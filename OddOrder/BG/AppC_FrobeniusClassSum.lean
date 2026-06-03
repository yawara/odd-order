/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Set.Card.Arithmetic
import OddOrder.BG.AppC_NormSet
import OddOrder.GroupTheory.RepresentationTheory.ClassSumAlgebra

/-!
# BG Appendix C: Frobenius Class-Sum Bridge

Bender--Glauberman Appendix C, Lemma C.2, pp. 145--152.

This file connects the finite-field pair set in `AppC_NormSet` to the conjugacy
class language used by the class-sum structure constants.  The finite-field leaf
keeps the concrete norm and semidirect-product setup; this file is the first
class-sum dependent layer for the `q >= 5` branch of Lemma C.2.
-/

namespace OddOrder.BG.AppC.NormSet

open OddOrder.RepresentationTheory

variable (p q : ℕ)

/-- The concrete Frobenius group `P ⋊ U` is finite; class-sum coefficients need
a `Fintype` instance.  `SemidirectProduct` is structurally just the product of
its left and right coordinates. -/
noncomputable instance normOneFrobeniusGroup_fintype [Fact p.Prime] :
    Fintype (normOneFrobeniusGroup p q) := by
  letI : Fintype (additiveFieldGroup p q) := Fintype.ofFinite _
  letI : Fintype (normOneUnits p q) := Fintype.ofFinite _
  exact Fintype.ofEquiv (additiveFieldGroup p q × normOneUnits p q)
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => (x.left, x.right)
      left_inv := by intro x; rfl
      right_inv := by intro x; ext <;> rfl }

/-- The conjugacy class in `H = P ⋊ U` of the additive-kernel element attached to
`s ∈ 𝔽_{p^q}`.  BG Lemma C.2 uses the class of a nonzero `s ∈ P`. -/
noncomputable def normOneClassAt [Fact p.Prime] (s : GaloisField p q) :
    ConjClasses (normOneFrobeniusGroup p q) :=
  ConjClasses.mk
    (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q)

/-- Every `U`-translate `u*s` lies in the conjugacy class of `s` inside
`H = P ⋊ U`.  This is the class-language form of `u s u⁻¹ = u*s`. -/
theorem normOneClassAt_mul_eq [Fact p.Prime] (s : GaloisField p q)
    (u : normOneUnits p q) :
    ConjClasses.mk
        (SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q) = normOneClassAt p q s := by
  unfold normOneClassAt
  apply Eq.symm
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  refine isConj_iff.mpr ⟨SemidirectProduct.inr u, ?_⟩
  simpa using normOneFrobenius_conj_inl p q u s

/-- Conjugating an additive-kernel point by an arbitrary element of
`H = P ⋊ U` only uses the `U`-coordinate.  The additive `P`-coordinate acts
trivially because `P` is abelian. -/
theorem normOneFrobenius_conj_inl_any [Fact p.Prime]
    (x : normOneFrobeniusGroup p q) (s : GaloisField p q) :
    x * SemidirectProduct.inl (Multiplicative.ofAdd s) * x⁻¹ =
      SemidirectProduct.inl
        (Multiplicative.ofAdd
          ((((x.right : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q) * s)) := by
  ext <;> simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.inv_left, SemidirectProduct.inv_right, normOneMulAction_apply]

/-- The conjugacy class of `s ∈ P` in `H = P ⋊ U` is exactly the `U`-orbit of
`s`.  This is the inverse direction to `normOneClassAt_mul_eq`. -/
theorem exists_normOne_mul_of_mem_normOneClass [Fact p.Prime] (s : GaloisField p q)
    {x : normOneFrobeniusGroup p q} (hx : ConjClasses.mk x = normOneClassAt p q s) :
    ∃ u : normOneUnits p q,
      x =
        SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) := by
  unfold normOneClassAt at hx
  have hconj : IsConj
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) x :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hx.symm
  rcases isConj_iff.mp hconj with ⟨g, hg⟩
  refine ⟨g.right, ?_⟩
  rw [← hg, normOneFrobenius_conj_inl_any]

/-- A nonzero additive-kernel conjugacy class in `H = P ⋊ U` has exactly one
point for each norm-one unit.  The bijection is `u ↦ inl (u*s)`, and `s ≠ 0`
makes it injective. -/
theorem normOneClassAt_carrier_ncard_eq_normOneUnits_card [Fact p.Prime]
    {s : GaloisField p q} (hs : s ≠ 0) :
    (normOneClassAt p q s).carrier.ncard = Nat.card (normOneUnits p q) := by
  classical
  rw [← Set.ncard_univ (α := normOneUnits p q)]
  symm
  refine Set.ncard_congr
    (fun u _ =>
      (SemidirectProduct.inl
        (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
          normOneFrobeniusGroup p q)) ?maps_to ?inj ?surj
  · intro u _
    exact ConjClasses.mem_carrier_iff_mk_eq.mpr (normOneClassAt_mul_eq p q s u)
  · intro u₁ u₂ _ _ h
    have hu_mul :
        (((u₁ : (GaloisField p q)ˣ) : GaloisField p q) * s) =
          (((u₂ : (GaloisField p q)ˣ) : GaloisField p q) * s) :=
      Multiplicative.ofAdd.injective (SemidirectProduct.inl_inj.mp h)
    exact Subtype.ext (Units.ext (mul_right_cancel₀ hs hu_mul))
  · intro x hx
    obtain ⟨u, rfl⟩ :=
      exists_normOne_mul_of_mem_normOneClass p q s
        (ConjClasses.mem_carrier_iff_mk_eq.mp hx)
    exact ⟨u, trivial, rfl⟩

/-- The product class `C_{2s}` has norm-one-unit size whenever `s ≠ 0` and
`2` is nonzero in the field.  This is the class-size factor needed after the
fixed-product fiber count. -/
theorem normOneClassAt_two_mul_carrier_ncard_eq_normOneUnits_card [Fact p.Prime]
    {s : GaloisField p q} (hs : s ≠ 0) (h2 : (2 : GaloisField p q) ≠ 0) :
    (normOneClassAt p q ((2 : GaloisField p q) * s)).carrier.ncard =
      Nat.card (normOneUnits p q) :=
  normOneClassAt_carrier_ncard_eq_normOneUnits_card p q (mul_ne_zero h2 hs)

/-- Fixed-product version of `IsClassPair`: the two entries lie in prescribed
classes and their product is the chosen representative `z`, not merely an
element conjugate to `z`.  This is the fiber counted by the finite-field pair
set before multiplying by the size of the product conjugacy class. -/
def IsFixedProductClassPair [Fact p.Prime]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    (z : normOneFrobeniusGroup p q)
    (r : normOneFrobeniusGroup p q × normOneFrobeniusGroup p q) : Prop :=
  ConjClasses.mk r.1 = Ci ∧ ConjClasses.mk r.2 = Cj ∧ r.1 * r.2 = z

/-- The set of fixed-product class pairs. -/
def fixedProductClassPairSet [Fact p.Prime]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    (z : normOneFrobeniusGroup p q) :
    Set (normOneFrobeniusGroup p q × normOneFrobeniusGroup p q) :=
  {r | IsFixedProductClassPair (p := p) (q := q) Ci Cj z r}

/-- Set version of the class-pair predicate, used to partition the full
class-sum pair count by exact product. -/
def classPairSet [Fact p.Prime]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    Set (normOneFrobeniusGroup p q × normOneFrobeniusGroup p q) :=
  {r | IsClassPair Ci Cj Cs r}

/-- The full class-pair set is the disjoint union of exact-product fibers over
the product conjugacy class.  This is the set-level form of the usual
`a_{ij}^s |C_s|` class-sum count. -/
theorem classPairSet_eq_iUnion_fixedProductClassPairSet [Fact p.Prime]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    classPairSet p q Ci Cj Cs =
      ⋃ z ∈ Cs.carrier, fixedProductClassPairSet (p := p) (q := q) Ci Cj z := by
  ext r
  constructor
  · intro hr
    refine Set.mem_iUnion.mpr ⟨r.1 * r.2, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
    · exact ConjClasses.mem_carrier_iff_mk_eq.mpr hr.2.2
    · exact ⟨hr.1, hr.2.1, rfl⟩
  · intro hr
    rcases Set.mem_iUnion.mp hr with ⟨z, hzmem⟩
    rcases Set.mem_iUnion.mp hzmem with ⟨hz, hfixed⟩
    exact ⟨hfixed.1, hfixed.2.1, by
      rw [hfixed.2.2]
      exact ConjClasses.mem_carrier_iff_mk_eq.mp hz⟩

/-- Cardinal form of `classPairSet_eq_iUnion_fixedProductClassPairSet`: the
full class-pair count is the finite sum of the fixed-product fiber sizes over
the product class. -/
theorem classPairSet_ncard_eq_finsum_fixedProductClassPairSet_ncard [Fact p.Prime]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    (classPairSet p q Ci Cj Cs).ncard =
      ∑ᶠ z ∈ Cs.carrier,
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
  classical
  have hdisj :
      Cs.carrier.PairwiseDisjoint
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj) := by
    intro z _ w _ hzw
    change Disjoint
      (fixedProductClassPairSet (p := p) (q := q) Ci Cj z)
      (fixedProductClassPairSet (p := p) (q := q) Ci Cj w)
    rw [Set.disjoint_left]
    intro r hz hw
    exact hzw (hz.2.2.symm.trans hw.2.2)
  rw [classPairSet_eq_iUnion_fixedProductClassPairSet]
  exact Set.Finite.ncard_biUnion (Set.toFinite _) (fun _ _ => Set.toFinite _) hdisj

/-- The set cardinality of `classPairSet` agrees with the existing class-sum
structure coefficient. -/
theorem classPairSet_ncard_eq_classSumCoeff [Fact p.Prime]
    [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    (classPairSet p q Ci Cj Cs).ncard = classSumCoeff Ci Cj Cs := by
  rw [← card_classPair (G := normOneFrobeniusGroup p q) Ci Cj Cs]
  rw [← Nat.card_coe_set_eq (classPairSet p q Ci Cj Cs)]
  rfl

/-- The class-sum structure coefficient is the sum of fixed-product fiber sizes
over the product class.  The later App C step shows these fibers have equal
cardinality in the concrete Frobenius group. -/
theorem classSumCoeff_eq_finsum_fixedProductClassPairSet_ncard [Fact p.Prime]
    [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    classSumCoeff Ci Cj Cs =
      ∑ᶠ z ∈ Cs.carrier,
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
  rw [← classPairSet_ncard_eq_classSumCoeff p q Ci Cj Cs]
  exact classPairSet_ncard_eq_finsum_fixedProductClassPairSet_ncard p q Ci Cj Cs

/-- Conjugation does not change the conjugacy-class label in the concrete
Frobenius group.  This local form avoids depending on private helpers from the
class-sum file. -/
theorem normOneFrobenius_mk_conj_eq [Fact p.Prime]
    (g x : normOneFrobeniusGroup p q) :
    ConjClasses.mk (g * x * g⁻¹) = ConjClasses.mk x := by
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g⁻¹, by group⟩)

/-- Fixed-product fibers over conjugate products have the same cardinality, by
conjugating both entries of a pair. -/
theorem fixedProductClassPairSet_ncard_eq_of_isConj [Fact p.Prime]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    {z w : normOneFrobeniusGroup p q} (hzw : IsConj z w) :
    (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard =
      (fixedProductClassPairSet (p := p) (q := q) Ci Cj w).ncard := by
  classical
  obtain ⟨g, hg⟩ := isConj_iff.mp hzw
  refine Set.ncard_congr
    (fun r _ => (g * r.1 * g⁻¹, g * r.2 * g⁻¹)) ?maps_to ?inj ?surj
  · intro r hr
    refine ⟨?_, ?_, ?_⟩
    · exact (normOneFrobenius_mk_conj_eq p q g r.1).trans hr.1
    · exact (normOneFrobenius_mk_conj_eq p q g r.2).trans hr.2.1
    · rw [show g * r.1 * g⁻¹ * (g * r.2 * g⁻¹) =
          g * (r.1 * r.2) * g⁻¹ by group, hr.2.2, hg]
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ _ _ hpair
    apply Prod.ext
    · have hx : g * x₁ * g⁻¹ = g * x₂ * g⁻¹ := by
        simpa using congrArg Prod.fst hpair
      have hx' : g⁻¹ * (g * x₁ * g⁻¹) * g = g⁻¹ * (g * x₂ * g⁻¹) * g := by
        rw [hx]
      simpa [mul_assoc] using hx'
    · have hy : g * y₁ * g⁻¹ = g * y₂ * g⁻¹ := by
        simpa using congrArg Prod.snd hpair
      have hy' : g⁻¹ * (g * y₁ * g⁻¹) * g = g⁻¹ * (g * y₂ * g⁻¹) * g := by
        rw [hy]
      simpa [mul_assoc] using hy'
  · intro r hr
    refine ⟨(g⁻¹ * r.1 * g, g⁻¹ * r.2 * g), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · exact (by
          simpa using (normOneFrobenius_mk_conj_eq p q g⁻¹ r.1).trans hr.1)
      · exact (by
          simpa using (normOneFrobenius_mk_conj_eq p q g⁻¹ r.2).trans hr.2.1)
      · have hback : g⁻¹ * w * g = z := by
          rw [← hg]
          group
        rw [show (g⁻¹ * r.1 * g) * (g⁻¹ * r.2 * g) =
            g⁻¹ * (r.1 * r.2) * g by group, hr.2.2, hback]
    · apply Prod.ext <;> group

/-- Summing fixed-product fiber sizes over one product conjugacy class multiplies
the representative fiber size by the class size. -/
theorem finsum_fixedProductClassPairSet_ncard_eq_carrier_ncard_mul [Fact p.Prime]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    (z : normOneFrobeniusGroup p q) :
    (∑ᶠ w ∈ (ConjClasses.mk z).carrier,
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj w).ncard) =
      (ConjClasses.mk z).carrier.ncard *
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
  classical
  let C := (ConjClasses.mk z).carrier
  have hCfin : C.Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hCfin]
  have hconst :
      ∀ w ∈ hCfin.toFinset,
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj w).ncard =
          (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
    intro w hw
    have hwC : w ∈ C := by
      simpa [C] using hw
    have hconj : IsConj z w :=
      ConjClasses.mk_eq_mk_iff_isConj.mp
        (ConjClasses.mem_carrier_iff_mk_eq.mp hwC).symm
    exact (fixedProductClassPairSet_ncard_eq_of_isConj p q Ci Cj hconj).symm
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul,
    Set.ncard_eq_toFinset_card _ hCfin]
  simp

/-- Class-sum pair counts factor as product-class size times one fixed-product
fiber.  This is the cardinal bridge from `classSumCoeff` to the finite-field
pair count used in App C. -/
theorem classSumCoeff_eq_carrier_ncard_mul_fixedProductClassPairSet_ncard [Fact p.Prime]
    [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    (z : normOneFrobeniusGroup p q) :
    classSumCoeff Ci Cj (ConjClasses.mk z) =
      (ConjClasses.mk z).carrier.ncard *
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
  rw [classSumCoeff_eq_finsum_fixedProductClassPairSet_ncard]
  exact finsum_fixedProductClassPairSet_ncard_eq_carrier_ncard_mul p q Ci Cj z

/-- A pair counted by `normOnePairSetAt s` gives a fixed-product class pair with
product exactly `inl (2*s)`. -/
theorem normOnePairSetAt_isFixedProductClassPair [Fact p.Prime]
    (s : GaloisField p q) {u v : normOneUnits p q}
    (h : (u, v) ∈ normOnePairSetAt p q s) :
    IsFixedProductClassPair (p := p) (q := q)
      (normOneClassAt p q s) (normOneClassAt p q s)
      (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
        normOneFrobeniusGroup p q)
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q),
        (SemidirectProduct.inl
          (Multiplicative.ofAdd (((v : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q)) := by
  refine ⟨normOneClassAt_mul_eq p q s u, normOneClassAt_mul_eq p q s v, ?_⟩
  exact (mem_normOnePairSetAt_iff_inl_mul_inl p q s u v).mp h

/-- Conversely, a fixed-product class pair over `C_s, C_s` with product
`inl (2*s)` comes from a pair of norm-one units satisfying the BG equation
`u*s + v*s = 2*s`. -/
theorem exists_normOnePairSetAt_of_isFixedProductClassPair [Fact p.Prime]
    (s : GaloisField p q) {x y : normOneFrobeniusGroup p q}
    (h : IsFixedProductClassPair (p := p) (q := q)
      (normOneClassAt p q s) (normOneClassAt p q s)
      (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
        normOneFrobeniusGroup p q) (x, y)) :
    ∃ u v : normOneUnits p q,
      (u, v) ∈ normOnePairSetAt p q s ∧
        x = SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) ∧
        y = SemidirectProduct.inl
          (Multiplicative.ofAdd (((v : (GaloisField p q)ˣ) : GaloisField p q) * s)) := by
  obtain ⟨u, hx⟩ := exists_normOne_mul_of_mem_normOneClass p q s h.1
  obtain ⟨v, hy⟩ := exists_normOne_mul_of_mem_normOneClass p q s h.2.1
  refine ⟨u, v, ?_, hx, hy⟩
  have hprod := h.2.2
  rw [hx, hy] at hprod
  exact (mem_normOnePairSetAt_iff_inl_mul_inl p q s u v).mpr hprod

/-- The finite-field pair count equals the cardinality of the fixed-product
class-pair fiber over `inl (2*s)`.  The hypothesis `s ≠ 0` makes the `U`-action
on `s` free, so the parametrization by `u, v ∈ U` is injective. -/
theorem normOnePairSetAt_ncard_eq_fixedProductClassPairSet_ncard [Fact p.Prime]
    {s : GaloisField p q} (hs : s ≠ 0) :
    (normOnePairSetAt p q s).ncard =
      (fixedProductClassPairSet (p := p) (q := q)
        (normOneClassAt p q s) (normOneClassAt p q s)
        (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
          normOneFrobeniusGroup p q)).ncard := by
  classical
  refine Set.ncard_congr
    (fun uv _ =>
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd (((uv.1 : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q),
        (SemidirectProduct.inl
          (Multiplicative.ofAdd (((uv.2 : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q))) ?maps_to ?inj ?surj
  · intro uv huv
    exact normOnePairSetAt_isFixedProductClassPair p q s huv
  · rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ _ _ hpair
    have hu_pair := congrArg Prod.fst hpair
    have hv_pair := congrArg Prod.snd hpair
    have hu_mul :
        (((u₁ : (GaloisField p q)ˣ) : GaloisField p q) * s) =
          (((u₂ : (GaloisField p q)ˣ) : GaloisField p q) * s) :=
      Multiplicative.ofAdd.injective (SemidirectProduct.inl_inj.mp hu_pair)
    have hv_mul :
        (((v₁ : (GaloisField p q)ˣ) : GaloisField p q) * s) =
          (((v₂ : (GaloisField p q)ˣ) : GaloisField p q) * s) :=
      Multiplicative.ofAdd.injective (SemidirectProduct.inl_inj.mp hv_pair)
    have hu : u₁ = u₂ :=
      Subtype.ext (Units.ext (mul_right_cancel₀ hs hu_mul))
    have hv : v₁ = v₂ :=
      Subtype.ext (Units.ext (mul_right_cancel₀ hs hv_mul))
    exact Prod.ext hu hv
  · intro r hr
    obtain ⟨u, v, huv, hx, hy⟩ :=
      exists_normOnePairSetAt_of_isFixedProductClassPair p q s hr
    refine ⟨(u, v), huv, ?_⟩
    exact Prod.ext hx.symm hy.symm

/-- For nonzero `s`, the class-sum coefficient for `C_s * C_s` landing in
`C_{2s}` is `|U|` times the finite-field fixed-product pair count. -/
theorem classSumCoeff_normOneClassAt_self_two_mul_eq_normOneUnits_card_mul_pairSetAt_ncard
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    {s : GaloisField p q} (hs : s ≠ 0) (h2 : (2 : GaloisField p q) ≠ 0) :
    classSumCoeff (normOneClassAt p q s) (normOneClassAt p q s)
        (normOneClassAt p q ((2 : GaloisField p q) * s)) =
      Nat.card (normOneUnits p q) * (normOnePairSetAt p q s).ncard := by
  classical
  change classSumCoeff (normOneClassAt p q s) (normOneClassAt p q s)
      (ConjClasses.mk
        (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
          normOneFrobeniusGroup p q)) =
    Nat.card (normOneUnits p q) * (normOnePairSetAt p q s).ncard
  rw [classSumCoeff_eq_carrier_ncard_mul_fixedProductClassPairSet_ncard]
  change (normOneClassAt p q ((2 : GaloisField p q) * s)).carrier.ncard *
      (fixedProductClassPairSet (p := p) (q := q)
        (normOneClassAt p q s) (normOneClassAt p q s)
        (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
          normOneFrobeniusGroup p q)).ncard =
    Nat.card (normOneUnits p q) * (normOnePairSetAt p q s).ncard
  rw [normOneClassAt_two_mul_carrier_ncard_eq_normOneUnits_card p q hs h2,
    ← normOnePairSetAt_ncard_eq_fixedProductClassPairSet_ncard p q hs]

/-- Same coefficient identity with the norm set `E` from BG Appendix C. -/
theorem classSumCoeff_normOneClassAt_self_two_mul_eq_normOneUnits_card_mul_normSetE_ncard
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hq : q ≠ 0) {s : GaloisField p q} (hs : s ≠ 0)
    (h2 : (2 : GaloisField p q) ≠ 0) :
    classSumCoeff (normOneClassAt p q s) (normOneClassAt p q s)
        (normOneClassAt p q ((2 : GaloisField p q) * s)) =
      Nat.card (normOneUnits p q) * (normSetE p q).ncard := by
  rw [classSumCoeff_normOneClassAt_self_two_mul_eq_normOneUnits_card_mul_pairSetAt_ncard
      p q hs h2, normOnePairSetAt_ncard_eq_normSetE_ncard p q hq hs]

/-- A pair counted by `normOnePairSetAt s` gives a class-pair counted by the
class-sum structure constants for the class of `s` and the class of `2*s` in
`H = P ⋊ U`.  This is the one-way bridge needed before proving that the
finite-field pair count is exactly the relevant class-sum coefficient. -/
theorem normOnePairSetAt_isClassPair [Fact p.Prime] (s : GaloisField p q)
    {u v : normOneUnits p q} (h : (u, v) ∈ normOnePairSetAt p q s) :
    IsClassPair (normOneClassAt p q s) (normOneClassAt p q s)
      (normOneClassAt p q ((2 : GaloisField p q) * s))
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q),
        (SemidirectProduct.inl
          (Multiplicative.ofAdd (((v : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact normOneClassAt_mul_eq p q s u
  · exact normOneClassAt_mul_eq p q s v
  · have hmul := (mem_normOnePairSetAt_iff_inl_mul_inl p q s u v).mp h
    rw [hmul]
    rfl

end OddOrder.BG.AppC.NormSet
