/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Assembly
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.XiLengthFromCard
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanDE

/-!
# Higman theorem (d): the actual two-summand split

T. Peterfalvi, Appendix III, Higman theorem (d), p. 141; G. Higman, *Suzuki
2-groups*, Lemma 12.

For a ξ-length-3 Suzuki 2-group `P`, the complementary invariant factors
`X, Y` of `higmanLemmaTwelve` project onto complementary invariant summands
of `P ⧸ Z(P)` of cardinality `|Z(P)|` each: since `Z(P) = Φ(P)`, the quotient
is elementary abelian, the images of the two factors are invariant under the
induced action, their cardinalities are `|X| / |Φ| = |Φ|` by the `A(n, θ)`
model count `|X| = |F|²`, and complementarity descends from
`X ⊓ Y = Φ(P)`, `X ⊔ Y = ⊤`.  This constructs Peterfalvi's
`OrderQModuleSplit` payload with `Z := Z(P)`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open scoped commutatorElement
open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups
open Module
open scoped Pointwise

noncomputable section

universe uP uF

/-! ## Cardinality of a quadratic central extension -/

/-- The twisted product is a product as a type. -/
theorem BilinearTwistedProduct.natCard_eq
    {R : Type*} {V : Type*} {W : Type*}
    [CommRing R] [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module R W] (B : LinearMap.BilinMap R V W) :
    Nat.card (BilinearTwistedProduct B) = Nat.card V * Nat.card W := by
  have e : BilinearTwistedProduct B ≃ V × W :=
    { toFun := fun x => (x.quotient, x.central)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun x => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod]

/-- **The order of a ξ-length-two type-A factor is `|Φ(P)|²`.** -/
theorem XiLengthTwoTypeAData.natCard_eq_sq
    {P : Type uP} [Group P] {S : Subgroup P}
    (data : XiLengthTwoTypeAData.{uP, uF} S)
    (hinvPhi : involutions P ⊆ frattini P)
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hPhiS : frattini P ≤ S) :
    Nat.card ↥S = Nat.card ↥(frattini P) ^ 2 := by
  letI := data.fieldF
  letI := data.finiteF
  letI := data.charTwoF
  letI : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2
  have h1 : Nat.card ↥S = Nat.card (TypeAModel data.phi) :=
    Nat.card_congr data.equivModel.toEquiv
  have h2 : Nat.card ↥(frattini P) = Nat.card data.F :=
    (Nat.card_congr
      (data.modelKernelEquivFrattini hinvPhi hEA hPhiS).toEquiv).symm
  rw [h1, h2, BilinearTwistedProduct.natCard_eq]
  have hF : Nat.card (Multiplicative data.F) = Nat.card data.F := rfl
  rw [pow_two]

/-! ## The elementary-abelian quotient -/

/-- **`P ⧸ Z(P)` is elementary abelian for a ξ-length-3 Suzuki 2-group**:
commutators and squares land in `Φ(P) = Z(P)`. -/
theorem quotient_center_isElementaryAbelian_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P] {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P, x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    OddOrder.GroupTheory.IsElementaryAbelian 2 (P ⧸ Subgroup.center P) := by
  have hZeq : Subgroup.center P = frattini P :=
    center_eq_frattini_of_xiLengthThree hP hncomm hmulti hxi hlen hprime
  have hAgemo := agemo_one_eq_frattini_of_xiLengthThree
    hP hncomm hmulti hxi hlen hprime
  constructor
  · intro xq yq
    refine QuotientGroup.induction_on xq fun x => ?_
    refine QuotientGroup.induction_on yq fun y => ?_
    show ((x * y : P) : P ⧸ Subgroup.center P) = ((y * x : P) : _)
    rw [QuotientGroup.eq]
    have hmem : ⁅y⁻¹, x⁻¹⁆ ∈ _root_.commutator P :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
        (Subgroup.mem_top _)
    have hcomm_le : _root_.commutator P ≤ Subgroup.center P := by
      rw [hZeq]
      exact OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP
    have heq : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact hcomm_le hmem
  · intro xq
    refine QuotientGroup.induction_on xq fun x => ?_
    show ((x : P ⧸ Subgroup.center P)) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hZeq, ← hAgemo]
    simpa using Agemo.mem_of_eq_pow (G := P) (p := 2) (n := 1) x

/-! ## The two-summand split -/

/-- **Peterfalvi Appendix III, Higman theorem (d), actual payload**: for a
ξ-length-3 Suzuki 2-group, `P ⧸ Z(P)` splits as two complementary invariant
summands of cardinality `|Z(P)|` — the images of the complementary type-A
factors. -/
theorem exists_orderQModuleSplit_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P] {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P, x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    Nonempty (OrderQModuleSplit Y.subtype (Subgroup.center P)
      (IsAInvariant.of_characteristic Y.subtype)) := by
  classical
  obtain ⟨factors⟩ :=
    xiLengthThreeTypeAFactorData_exists hP hncomm hmulti hxi hlen hprime
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hZeq : Subgroup.center P = frattini P :=
    center_eq_frattini_of_xiLengthThree hP hncomm hmulti hxi hlen hprime
  have hPhiNeBot : frattini P ≠ (⊥ : Subgroup P) := by
    intro hPhiBot
    have hcommBot : _root_.commutator P = ⊥ :=
      le_bot_iff.mp
        ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
          (le_of_eq hPhiBot))
    exact hncomm ((commutator_eq_bot_iff P).mp hcommBot)
  have hinvPhi : involutions P ⊆ frattini P :=
    involutions_subset_of_nontrivial_invariant hP Y hxi.transitive
      (IsAInvariant.of_characteristic Y.subtype) hPhiNeBot
  have hZinv : IsAInvariant Y.subtype (Subgroup.center P) :=
    IsAInvariant.of_characteristic Y.subtype
  -- invariance of the images under the induced action
  have hmapinv : ∀ {X : Subgroup P}, IsAInvariant Y.subtype X →
      IsAInvariant (IsAInvariant.quotientMulAutHom hZinv)
        (X.map (QuotientGroup.mk' (Subgroup.center P))) := by
    intro X hX a
    show (X.map (QuotientGroup.mk' (Subgroup.center P))).map
        (IsAInvariant.quotientMulAutHom hZinv a).toMonoidHom =
      X.map (QuotientGroup.mk' (Subgroup.center P))
    rw [Subgroup.map_map]
    have hcomp : (IsAInvariant.quotientMulAutHom hZinv a).toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center P))
        = (QuotientGroup.mk' (Subgroup.center P)).comp
          ((Y.subtype a : MulAut P)).toMonoidHom :=
      MonoidHom.ext fun g =>
        IsAInvariant.quotientMulAutHom_apply_mk' hZinv a g
    rw [hcomp, ← Subgroup.map_map]
    congr 1
    exact hX a
  -- cardinalities of the images
  have hZle_left : Subgroup.center P ≤ factors.left := by
    rw [hZeq]
    exact factors.frattini_lt_left.le
  have hZle_right : Subgroup.center P ≤ factors.right := by
    rw [hZeq]
    exact factors.frattini_lt_right.le
  have hcardZ : Nat.card ↥(Subgroup.center P) = Nat.card ↥(frattini P) := by
    rw [hZeq]
  have hcardMap : ∀ {X : Subgroup P}, Subgroup.center P ≤ X →
      Nat.card ↥X = Nat.card ↥(frattini P) ^ 2 →
      Nat.card ↥(X.map (QuotientGroup.mk' (Subgroup.center P))) =
        Nat.card ↥(Subgroup.center P) := by
    intro X hZX hcardX
    have hcomap : (X.map (QuotientGroup.mk' (Subgroup.center P))).comap
        (QuotientGroup.mk' (Subgroup.center P)) = X := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact sup_eq_left.mpr hZX
    have hcount :
        Nat.card ↥((X.map (QuotientGroup.mk' (Subgroup.center P))).comap
            (QuotientGroup.mk' (Subgroup.center P))) =
          Nat.card ↥(X.map (QuotientGroup.mk' (Subgroup.center P))) *
            Nat.card (QuotientGroup.mk' (Subgroup.center P)).ker :=
      Subgroup.card_comap_eq_card_mul_card_ker _
        (QuotientGroup.mk'_surjective (Subgroup.center P)) _
    rw [hcomap, hcardX] at hcount
    have hker : Nat.card (QuotientGroup.mk' (Subgroup.center P)).ker =
        Nat.card ↥(Subgroup.center P) := by
      rw [QuotientGroup.ker_mk']
    rw [hker, hcardZ] at hcount
    have hpos : 0 < Nat.card ↥(frattini P) := Nat.card_pos
    have hmul : Nat.card
          ↥(X.map (QuotientGroup.mk' (Subgroup.center P))) *
          Nat.card ↥(frattini P) =
        Nat.card ↥(frattini P) * Nat.card ↥(frattini P) := by
      rw [← hcount, pow_two]
    have hres := Nat.eq_of_mul_eq_mul_right hpos hmul
    rw [hres, hcardZ]
  -- complementarity of the images
  have hdisj : factors.left.map (QuotientGroup.mk' (Subgroup.center P)) ⊓
      factors.right.map (QuotientGroup.mk' (Subgroup.center P)) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw1, hw2⟩
    obtain ⟨x, hxX, rfl⟩ := hw1
    obtain ⟨y, hyY, hyx⟩ := hw2
    have hyxZ : y⁻¹ * x ∈ Subgroup.center P := by
      rw [← QuotientGroup.eq]
      exact hyx
    have hxY : x ∈ factors.right := by
      have : y * (y⁻¹ * x) ∈ factors.right :=
        Subgroup.mul_mem _ hyY (hZle_right hyxZ)
      simpa using this
    have hxZ : x ∈ Subgroup.center P := by
      rw [hZeq, ← factors.inf_eq_frattini]
      exact ⟨hxX, hxY⟩
    have hone : QuotientGroup.mk' (Subgroup.center P) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hxZ
    rw [hone]
    exact Subgroup.one_mem _
  have hsup : factors.left.map (QuotientGroup.mk' (Subgroup.center P)) ⊔
      factors.right.map (QuotientGroup.mk' (Subgroup.center P)) = ⊤ := by
    rw [← Subgroup.map_sup, factors.sup_eq_top]
    exact Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective (Subgroup.center P))
  exact ⟨{
    quotientEA := quotient_center_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
    left := factors.left.map (QuotientGroup.mk' (Subgroup.center P))
    right := factors.right.map (QuotientGroup.mk' (Subgroup.center P))
    leftInvariant := hmapinv factors.left_invariant
    rightInvariant := hmapinv factors.right_invariant
    leftCard := hcardMap hZle_left
      (factors.left_model.natCard_eq_sq hinvPhi hEA
        (hZeq ▸ hZle_left))
    rightCard := hcardMap hZle_right
      (factors.right_model.natCard_eq_sq hinvPhi hEA
        (hZeq ▸ hZle_right))
    complementary := isCompl_iff.mpr
      ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr hsup⟩ }⟩

/-! ## The packaged Higman payload from `|P| = q³` -/

/-- **The Higman payload for a Suzuki 2-group of order `q³`** (Peterfalvi
Appendix III, Theorem (a)/(d) for the cube case): the center coincides with
the Frattini subgroup and has exponent two, and `P ⧸ Z(P)` splits as two
complementary invariant summands of cardinality `|Z(P)|` each.  All three
conclusions are consequences of ξ-length three, which the order forces. -/
theorem center_payload_of_card_eq_cube
    {P : Type uP} [Group P] [Finite P]
    (hP : IsSuzuki2Group P)
    {K : Subgroup (MulAut P)} (hKcyc : IsCyclic ↥K)
    (hreg : ActsRegularlyOnInvolutions K)
    {n : ℕ} (hn : n ≠ 0)
    (hKcard : Nat.card ↥K = 2 ^ n - 1)
    (hcard : Nat.card P = (2 ^ n) ^ 3) :
    Subgroup.center P = frattini P ∧
    (∀ z ∈ Subgroup.center P, z ^ 2 = 1) ∧
    Nonempty (OrderQModuleSplit K.subtype (Subgroup.center P)
      (IsAInvariant.of_characteristic K.subtype)) := by
  obtain ⟨hP2, hncomm, hmulti, -⟩ := id hP
  have hxi : IsXiActor K := ⟨hKcyc, hreg.transitive⟩
  have hlen : HasXiLengthThree K.subtype :=
    hasXiLengthThree_of_card_eq_cube hP hKcyc hreg hn hKcard hcard
  obtain ⟨u₀, -, hu₀, -, -⟩ := id hmulti
  have hinvcard : (involutions P).ncard = Nat.card ↥K :=
    ncard_involutions_eq_card_of_regular hreg hu₀
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥K →
      p ∣ (involutions P).ncard := by
    intro p _ hp
    rwa [hinvcard]
  exact ⟨center_eq_frattini_of_xiLengthThree hP2 hncomm hmulti hxi hlen
      hprime,
    fun z hz => center_sq_eq_one_of_xiLengthThree hP2 hncomm hmulti hxi
      hlen hprime hz,
    exists_orderQModuleSplit_of_xiLengthThree hP2 hncomm hmulti hxi hlen
      hprime⟩

end

end OddOrder.Higman.Suzuki2Groups
