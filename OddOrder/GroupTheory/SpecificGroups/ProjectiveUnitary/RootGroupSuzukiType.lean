/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.RootGroupStructure
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.Bruhat
import OddOrder.GroupTheory.SpecificGroups.Suzuki2Group.Basic

/-!
# The unitary root group as a Sylow subgroup and a Suzuki 2-group

Let `q = 2 ^ n`.  This file completes the concrete root-group calculation
used in the projective-unitary case of **Peterfalvi, Part II, Chapter I §3,
Proposition 1(c)** (pp. 105--106):

* the Hermitian root group has order `q³`, and its center is the fixed-field
  line of order `q`;
* the defining-field units act through the standard torus by
  `(a, b) |-> (c * a, c ^ 2 * b)`;
* for `1 < n`, this cyclic group acts regularly on the nonidentity
  involutions, giving an honest instance of **Appendix III, Definition 1**;
* the range of root translations has odd index in the standard unitary
  permutation group and is therefore a Sylow `2`-subgroup.

The last point supplies directly the standard-structure assertion cited by
Peterfalvi from Huppert, Kapitel II, Satz 10.12.  The construction proves only
the Appendix III Suzuki `2`-group condition and the order `q³`; it does not
assert type B, whose later use in Peterfalvi has an additional hypothesis.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

noncomputable section

open OddOrder.GroupTheory.Suzuki2Group

section /- Appendix III / Part II, Chapter I §3: exact center and order -/

namespace RootGroup

/-- The central square-one line is the full center of the Hermitian root
group. -/
theorem center_eq_centerLine (n : ℕ) (hn : 0 < n) :
    Subgroup.center (RootGroup n) = centerLine n := by
  apply le_antisymm
  · intro z hz
    obtain ⟨c, hc⟩ := exists_not_fixed_conjugation n hn
    have hcomm1 := (Subgroup.mem_center_iff.mp hz) (withFirst n 1)
    have hcommc := (Subgroup.mem_center_iff.mp hz) (withFirst n c)
    have hfixed : z.fst = star z.fst := by
      have h := congrArg RootGroup.snd hcomm1
      simp only [snd_mul, withFirst_fst, star_one, mul_one, one_mul] at h
      rw [add_comm (withFirst n 1).snd z.snd] at h
      exact (add_left_cancel h).symm
    by_contra hz0
    change z.fst ≠ 0 at hz0
    apply hc
    apply mul_left_cancel₀ hz0
    have h := congrArg RootGroup.snd hcommc
    simp only [snd_mul, withFirst_fst] at h
    rw [← hfixed] at h
    rw [add_comm (withFirst n c).snd z.snd] at h
    have hcprod : c * z.fst = z.fst * star c := add_left_cancel h
    calc
      z.fst * star c = c * z.fst := hcprod.symm
      _ = z.fst * c := mul_comm _ _
  · exact centerLine_le_center

/-- The center has exact order `q = 2 ^ n`. -/
theorem natCard_center (n : ℕ) (hn : 0 < n) :
    Nat.card (Subgroup.center (RootGroup n)) = 2 ^ n := by
  rw [center_eq_centerLine n hn, natCard_centerLine n hn]

/-- The center has the same cardinality as the defining field. -/
theorem natCard_center_eq_baseField (n : ℕ) (hn : 0 < n) :
    Nat.card (Subgroup.center (RootGroup n)) = Nat.card (BaseField n) := by
  rw [natCard_center n hn, natCard_baseField n hn]

/-- The root-group order `2 ^ (3 * n)` is exactly the field-theoretic
expression `q³`. -/
theorem natCard_eq_baseField_cube (n : ℕ) (hn : 0 < n) :
    Nat.card (RootGroup n) = Nat.card (BaseField n) ^ 3 := by
  rw [natCard n hn, natCard_baseField n hn, ← pow_mul]
  congr 1
  omega

end RootGroup

end

section /- Part II, Chapter I §3: the standard root subgroup -/

/-- Root translations in the standard unitary permutation group. -/
noncomputable def standardRootSubgroup (n : ℕ) :
    Subgroup (standardPermGroup n) :=
  (rootHom n).range

/-- Root coordinates identify with the range of root translations. -/
noncomputable def rootEquivStandardRoot (n : ℕ) :
    RootGroup n ≃* standardRootSubgroup n :=
  MonoidHom.ofInjective (rootHom_injective n)

/-- The standard root subgroup has exact order `2 ^ (3 * n)`. -/
theorem natCard_standardRootSubgroup (n : ℕ) (hn : 0 < n) :
    Nat.card (standardRootSubgroup n) = 2 ^ (3 * n) := by
  rw [← RootGroup.natCard n hn]
  exact (Nat.card_congr (rootEquivStandardRoot n).toEquiv).symm

/-- The standard root subgroup has exact order `q³`. -/
theorem natCard_standardRootSubgroup_eq_baseField_cube
    (n : ℕ) (hn : 0 < n) :
    Nat.card (standardRootSubgroup n) = Nat.card (BaseField n) ^ 3 := by
  calc
    Nat.card (standardRootSubgroup n) = Nat.card (RootGroup n) :=
      (Nat.card_congr (rootEquivStandardRoot n).toEquiv).symm
    _ = Nat.card (BaseField n) ^ 3 :=
      RootGroup.natCard_eq_baseField_cube n hn

end

section /- Appendix III, Definition 1: the regular cyclic torus -/

/-- Embed defining-field units into units of the quadratic extension. -/
def baseFieldUnitEmbedding (n : ℕ) :
    (BaseField n)ˣ →* (Field n)ˣ :=
  Units.map (algebraMap (BaseField n) (Field n)).toMonoidHom

@[simp]
theorem coe_baseFieldUnitEmbedding (n : ℕ) (c : (BaseField n)ˣ) :
    ((baseFieldUnitEmbedding n c : (Field n)ˣ) : Field n) =
      algebraMap (BaseField n) (Field n) (c : BaseField n) := rfl

/-- The defining-field multiplicative group acts through the unitary root
torus. -/
def baseTorusScaleHom (n : ℕ) :
    (BaseField n)ˣ →* MulAut (RootGroup n) :=
  (torusScaleHom n).comp (baseFieldUnitEmbedding n)

@[simp]
theorem baseTorusScaleHom_fst (n : ℕ) (c : (BaseField n)ˣ)
    (u : RootGroup n) :
    (baseTorusScaleHom n c u).fst =
      algebraMap (BaseField n) (Field n) c * u.fst := by
  rfl

@[simp]
theorem baseTorusScaleHom_snd (n : ℕ) (c : (BaseField n)ˣ)
    (u : RootGroup n) :
    (baseTorusScaleHom n c u).snd =
      algebraMap (BaseField n) (Field n) ((c : BaseField n) ^ 2) * u.snd := by
  change torusWeight (baseFieldUnitEmbedding n c) * u.snd = _
  simp [torusWeight, pow_two]

/-- The defining-field torus acts faithfully on the Hermitian root group. -/
theorem baseTorusScaleHom_injective (n : ℕ) :
    Function.Injective (baseTorusScaleHom n) := by
  intro c d h
  apply Units.ext
  apply (algebraMap (BaseField n) (Field n)).injective
  have h' := congrArg (fun a : MulAut (RootGroup n) =>
    (a (RootGroup.withFirst n 1)).fst) h
  simpa using h'

/-- The standard cyclic subgroup of automorphisms used in Appendix III,
Definition 1. -/
noncomputable def standardRootTorus (n : ℕ) :
    Subgroup (MulAut (RootGroup n)) :=
  (baseTorusScaleHom n).range

/-- The standard root torus is cyclic. -/
theorem standardRootTorus_isCyclic (n : ℕ) :
    IsCyclic ↥(standardRootTorus n) := by
  exact isCyclic_of_surjective
    (baseTorusScaleHom n).rangeRestrict
    (baseTorusScaleHom n).rangeRestrict_surjective

/-- The defining field is equivalent to the fixed field of quadratic
conjugation. -/
private noncomputable def fixedFieldEquiv (n : ℕ) (hn : 0 < n) :
    BaseField n ≃ {b : Field n // star b = b} :=
  Equiv.ofBijective
    (fun a : BaseField n =>
      ⟨algebraMap (BaseField n) (Field n) a, star_algebraMap n a⟩)
    ⟨by
      intro a b h
      apply (algebraMap (BaseField n) (Field n)).injective
      exact congrArg Subtype.val h,
    by
      intro b
      obtain ⟨a, ha⟩ :=
        (mem_range_algebraMap_iff_star_eq n hn b.1).2 b.2
      refine ⟨a, Subtype.ext ?_⟩
      exact ha⟩

@[simp]
private theorem fixedFieldEquiv_apply_val (n : ℕ) (hn : 0 < n)
    (a : BaseField n) :
    (fixedFieldEquiv n hn a : Field n) =
      algebraMap (BaseField n) (Field n) a := rfl

private theorem algebraMap_fixedFieldEquiv_symm
    (n : ℕ) (hn : 0 < n) (b : {b : Field n // star b = b}) :
    algebraMap (BaseField n) (Field n) ((fixedFieldEquiv n hn).symm b) = b := by
  exact congrArg Subtype.val ((fixedFieldEquiv n hn).apply_symm_apply b)

private theorem involution_fst_eq_zero {n : ℕ} {x : RootGroup n}
    (hx : x ∈ involutions (RootGroup n)) : x.fst = 0 :=
  (RootGroup.sq_eq_one_iff_fst_eq_zero x).1 hx.1

private theorem involution_snd_fixed {n : ℕ} {x : RootGroup n}
    (hx : x ∈ involutions (RootGroup n)) : star x.snd = x.snd := by
  have h := x.condition
  rw [involution_fst_eq_zero hx, zero_mul] at h
  exact (CharTwo.add_eq_zero.mp h).symm

private theorem involution_snd_ne_zero {n : ℕ} {x : RootGroup n}
    (hx : x ∈ involutions (RootGroup n)) : x.snd ≠ 0 := by
  intro h
  apply hx.2
  exact (RootGroup.eq_one_iff_snd_eq_zero x).2 h

/-- The standard defining-field torus acts regularly on the nonidentity
involutions of the Hermitian root group. -/
theorem standardRootTorus_actsRegularlyOnInvolutions
    (n : ℕ) (hn : 0 < n) :
    ActsRegularlyOnInvolutions (standardRootTorus n) := by
  intro x hx y hy
  let xb : {b : Field n // star b = b} :=
    ⟨x.snd, involution_snd_fixed hx⟩
  let yb : {b : Field n // star b = b} :=
    ⟨y.snd, involution_snd_fixed hy⟩
  let ax : BaseField n := (fixedFieldEquiv n hn).symm xb
  let ay : BaseField n := (fixedFieldEquiv n hn).symm yb
  have hax : algebraMap (BaseField n) (Field n) ax = x.snd := by
    simpa only [ax, xb] using algebraMap_fixedFieldEquiv_symm n hn xb
  have hay : algebraMap (BaseField n) (Field n) ay = y.snd := by
    simpa only [ay, yb] using algebraMap_fixedFieldEquiv_symm n hn yb
  have hax0 : ax ≠ 0 := by
    intro h
    apply involution_snd_ne_zero hx
    rw [← hax, h, map_zero]
  have hay0 : ay ≠ 0 := by
    intro h
    apply involution_snd_ne_zero hy
    rw [← hay, h, map_zero]
  let r : BaseField n :=
    (frobeniusEquiv (BaseField n) 2).symm (ay / ax)
  have hr_sq : r ^ 2 = ay / ax :=
    frobeniusEquiv_symm_pow_p (BaseField n) 2 (ay / ax)
  have hr0 : r ≠ 0 := by
    intro hr
    have hratio : ay / ax ≠ 0 := div_ne_zero hay0 hax0
    apply hratio
    rw [← hr_sq, hr, zero_pow (by decide : 2 ≠ 0)]
  let c : (BaseField n)ˣ := Units.mk0 r hr0
  let a : ↥(standardRootTorus n) :=
    ⟨baseTorusScaleHom n c, ⟨c, rfl⟩⟩
  have hr_mul : r ^ 2 * ax = ay := by
    rw [hr_sq, div_mul_cancel₀ ay hax0]
  refine ⟨a, ?_, ?_⟩
  · change baseTorusScaleHom n c x = y
    ext
    · simp only [baseTorusScaleHom_fst, involution_fst_eq_zero hx,
        involution_fst_eq_zero hy, mul_zero]
    · simp only [baseTorusScaleHom_snd]
      rw [← hax, ← hay, ← map_mul, show (c : BaseField n) = r from rfl,
        hr_mul]
  · intro b hb
    obtain ⟨d, hd⟩ := b.2
    have hsnd := congrArg RootGroup.snd hb
    change (b.1 x).snd = y.snd at hsnd
    rw [← hd] at hsnd
    simp only [baseTorusScaleHom_snd] at hsnd
    have hd_sq : (d : BaseField n) ^ 2 = r ^ 2 := by
      apply (algebraMap (BaseField n) (Field n)).injective
      apply mul_right_cancel₀
        ((map_ne_zero (algebraMap (BaseField n) (Field n))).2 hax0)
      calc
        algebraMap (BaseField n) (Field n) ((d : BaseField n) ^ 2) *
              algebraMap (BaseField n) (Field n) ax =
            algebraMap (BaseField n) (Field n) ((d : BaseField n) ^ 2) *
              x.snd := by rw [hax]
        _ = y.snd := hsnd
        _ = algebraMap (BaseField n) (Field n) ay := hay.symm
        _ = algebraMap (BaseField n) (Field n) (r ^ 2 * ax) := by rw [hr_mul]
        _ = algebraMap (BaseField n) (Field n) (r ^ 2) *
              algebraMap (BaseField n) (Field n) ax := by rw [map_mul]
    have hdr : (d : BaseField n) = r :=
      injective_pow_p (R := BaseField n) (p := 2) hd_sq
    have hdc : d = c := Units.ext hdr
    apply Subtype.ext
    change b.1 = a.1
    rw [← hd, hdc]

end

section /- Appendix III, Definition 1: the Suzuki 2-group package -/

private theorem exists_two_rootGroup_involutions (n : ℕ) (hn : 1 < n) :
    ∃ x y : RootGroup n, x ∈ involutions (RootGroup n) ∧
      y ∈ involutions (RootGroup n) ∧ x ≠ y := by
  have hn0 : 0 < n := by omega
  have hcard : 1 < Nat.card ((BaseField n)ˣ) := by
    rw [Nat.card_units, natCard_baseField n hn0]
    have hpow : 2 ^ 2 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at hpow ⊢
    omega
  letI : Nontrivial ((BaseField n)ˣ) :=
    Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨c, hc⟩ := exists_ne (1 : (BaseField n)ˣ)
  let x : RootGroup n := RootGroup.centralInvolution n
  let y : RootGroup n := baseTorusScaleHom n c x
  have hx : x ∈ involutions (RootGroup n) :=
    ⟨RootGroup.centralInvolution_sq n, RootGroup.centralInvolution_ne_one n⟩
  have hy_sq : y ^ 2 = 1 := by
    change (baseTorusScaleHom n c x) ^ 2 = 1
    rw [← map_pow, hx.1, map_one]
  have hy_ne : y ≠ 1 := by
    intro h
    apply hx.2
    apply (baseTorusScaleHom n c).injective
    simpa only [map_one] using h
  refine ⟨x, y, hx, ⟨hy_sq, hy_ne⟩, ?_⟩
  intro hxy
  apply hc
  apply Units.ext
  apply injective_pow_p (R := BaseField n) (p := 2)
  have hsnd := congrArg RootGroup.snd hxy
  dsimp only [x, y] at hsnd
  simp only [baseTorusScaleHom_snd,
    RootGroup.centralInvolution_snd] at hsnd
  apply (algebraMap (BaseField n) (Field n)).injective
  simpa only [Units.val_one, map_pow, map_one, one_pow, mul_one] using hsnd.symm

/-- **Peterfalvi Appendix III, Definition 1.**  For `q > 2`, the Hermitian
coordinate root group is an honest Suzuki `2`-group, witnessed by the cyclic
defining-field torus acting regularly on its involutions. -/
theorem RootGroup.isSuzuki2Group (n : ℕ) (hn : 1 < n) :
    IsSuzuki2Group (RootGroup n) := by
  have hn0 : 0 < n := by omega
  refine ⟨RootGroup.isPGroup n hn0, RootGroup.not_isMulCommutative n hn0,
    exists_two_rootGroup_involutions n hn, standardRootTorus n,
    standardRootTorus_isCyclic n,
    standardRootTorus_actsRegularlyOnInvolutions n hn0⟩

end

section /- Part II, Chapter I §3, Proposition 1(c): Sylow -/

/-- The odd cofactor in the order of the standard projective unitary group. -/
def standardRootOddCofactor (n : ℕ) : ℕ :=
  (2 ^ (3 * n) + 1) *
    ((2 ^ (2 * n) - 1) / (2 ^ n + 1).gcd 3)

private theorem unitaryTorusCofactor_odd (n : ℕ) (hn : 0 < n) :
    Odd ((2 ^ (2 * n) - 1) / (2 ^ n + 1).gcd 3) := by
  have hnumOdd : Odd (2 ^ (2 * n) - 1) :=
    Nat.Even.sub_odd (one_le_pow₀ one_le_two)
      (even_two.pow_of_ne_zero (by omega)) odd_one
  have hdenDvd : (2 ^ n + 1).gcd 3 ∣ 2 ^ (2 * n) - 1 := by
    apply dvd_trans (Nat.gcd_dvd_left (2 ^ n + 1) 3)
    have hpow : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by
      rw [show 2 * n = n * 2 by omega, pow_mul]
    rw [hpow]
    refine ⟨2 ^ n - 1, ?_⟩
    simpa using (Nat.sq_sub_sq (2 ^ n) 1)
  apply hnumOdd.of_dvd_nat
  exact ⟨(2 ^ n + 1).gcd 3, (Nat.div_mul_cancel hdenDvd).symm⟩

/-- The cofactor of the root-group order is odd. -/
theorem standardRootOddCofactor_odd (n : ℕ) (hn : 0 < n) :
    Odd (standardRootOddCofactor n) := by
  apply Odd.mul
  · exact (even_two.pow_of_ne_zero (by omega)).add_one
  · exact unitaryTorusCofactor_odd n hn

/-- The index of the standard root subgroup is the odd cofactor in the
standard unitary group order. -/
theorem standardRootSubgroup_index (n : ℕ) (hn : 0 < n) :
    (standardRootSubgroup n).index = standardRootOddCofactor n := by
  have hcard := (standardRootSubgroup n).card_mul_index
  rw [natCard_standardRootSubgroup n hn,
    natCard_standardPermGroup n hn] at hcard
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (by omega : 0 < 2) (3 * n))
  simpa [standardRootOddCofactor, mul_assoc] using hcard

/-- The standard root subgroup has odd index. -/
theorem standardRootSubgroup_index_odd (n : ℕ) (hn : 0 < n) :
    Odd (standardRootSubgroup n).index := by
  rw [standardRootSubgroup_index n hn]
  exact standardRootOddCofactor_odd n hn

/-- **Peterfalvi Part II, Chapter I §3, Proposition 1(c), unitary case.**
The range of root translations is a Sylow `2`-subgroup of the standard
projective unitary permutation group. -/
noncomputable def standardRootSylow (n : ℕ) (hn : 0 < n) :
    Sylow 2 (standardPermGroup n) :=
  ((RootGroup.isPGroup n hn).of_equiv (rootEquivStandardRoot n)).toSylow
    (by
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.mpr (standardRootSubgroup_index_odd n hn))

@[simp]
theorem coe_standardRootSylow (n : ℕ) (hn : 0 < n) :
    (standardRootSylow n hn : Subgroup (standardPermGroup n)) =
      standardRootSubgroup n := rfl

end

section /- Transport Appendix III structure to the subgroup carrier -/

private theorem isSuzuki2Group_of_mulEquiv
    {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (hP : IsSuzuki2Group P) : IsSuzuki2Group Q := by
  rcases hP with ⟨hPtwo, hPnoncomm, hPinv, A, hAcyc, hAreg⟩
  let autEquiv : MulAut P ≃* MulAut Q := MulAut.congr e
  let f : ↥A →* MulAut Q := autEquiv.toMonoidHom.comp A.subtype
  let B : Subgroup (MulAut Q) := f.range
  letI : IsCyclic ↥A := hAcyc
  have hQtwo : IsPGroup 2 Q := hPtwo.of_equiv e
  have hQnoncomm : ¬ IsMulCommutative Q := by
    intro hQcomm
    apply hPnoncomm
    rw [isMulCommutative_iff] at hQcomm ⊢
    intro x y
    apply e.injective
    simpa only [map_mul] using hQcomm (e x) (e y)
  have hQinv :
      ∃ x y : Q, x ∈ involutions Q ∧ y ∈ involutions Q ∧ x ≠ y := by
    obtain ⟨x, y, hx, hy, hxy⟩ := hPinv
    refine ⟨e x, e y, ?_, ?_, e.injective.ne hxy⟩
    · constructor
      · rw [← map_pow, hx.1, map_one]
      · intro h
        apply hx.2
        apply e.injective
        simpa only [map_one] using h
    · constructor
      · rw [← map_pow, hy.1, map_one]
      · intro h
        apply hy.2
        apply e.injective
        simpa only [map_one] using h
  have hBcyc : IsCyclic ↥B :=
    isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hBreg : ActsRegularlyOnInvolutions B := by
    intro x hx y hy
    have hxP : e.symm x ∈ involutions P := by
      constructor
      · apply e.injective
        simpa only [map_pow, map_one, e.apply_symm_apply] using hx.1
      · intro h
        apply hx.2
        apply e.symm.injective
        simpa only [map_one, e.symm_apply_apply] using h
    have hyP : e.symm y ∈ involutions P := by
      constructor
      · apply e.injective
        simpa only [map_pow, map_one, e.apply_symm_apply] using hy.1
      · intro h
        apply hy.2
        apply e.symm.injective
        simpa only [map_one, e.symm_apply_apply] using h
    obtain ⟨a, ha, hauniq⟩ := hAreg (e.symm x) hxP (e.symm y) hyP
    let b : ↥B := ⟨f a, ⟨a, rfl⟩⟩
    refine ⟨b, ?_, ?_⟩
    · change autEquiv a x = y
      change e ((a : MulAut P) (e.symm x)) = y
      rw [ha, e.apply_symm_apply]
    · intro c hc
      obtain ⟨d, hd⟩ := c.2
      have hdact : (d : MulAut P) (e.symm x) = e.symm y := by
        apply e.injective
        rw [e.apply_symm_apply]
        change autEquiv d x = y
        change (f d) x = y
        rw [hd]
        exact hc
      have hda : d = a := hauniq d hdact
      apply Subtype.ext
      rw [← hd, hda]
  exact ⟨hQtwo, hQnoncomm, hQinv, B, hBcyc, hBreg⟩

/-- The concrete Sylow root subgroup carries the same honest Appendix III
Suzuki `2`-group structure as its coordinate model. -/
theorem standardRootSubgroup_isSuzuki2Group (n : ℕ) (hn : 1 < n) :
    IsSuzuki2Group ↥(standardRootSubgroup n) :=
  isSuzuki2Group_of_mulEquiv (rootEquivStandardRoot n)
    (RootGroup.isSuzuki2Group n hn)

end

end

end OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
