/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.QuotientTwoStep
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaEleven
import OddOrder.Higman.Suzuki2Groups.HigmanIdempotentAction

/-!
# Higman's Lemma 12: models for the ξ-length-two factors

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
pp. 89--90.

Higman extends the notation `A(n, φ)` to include the abelian case
`A(n, 1) = C₄ⁿ` immediately before Lemma 12. Peterfalvi's later
`TypeAData` deliberately describes only the noncommutative case and hence
requires `φ ≠ 1`. This leaf keeps those meanings distinct: the inclusive
`XiLengthTwoTypeAData` is the source-facing carrier for the two factors in
Lemma 12, while `TypeAData` maps into it by forgetting only nontriviality.

The restricted actor bridges below transfer cyclicity, involution
transitivity, and Higman's prime-support condition to an invariant factor.
Thus every noncommutative lifted factor is classified by Lemma 11.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups

universe uP uF

/-- Honest model data for a ξ-length-two Higman factor `A(n, φ)`.

Unlike Peterfalvi's noncommutative `TypeAData`, this source-facing carrier
allows `φ = 1`, which is Higman's abelian case `A(n, 1) = C₄ⁿ`. -/
structure XiLengthTwoTypeAData (P : Type uP) [Group P] where
  F : Type uF
  [fieldF : Field F]
  [finiteF : Finite F]
  [charTwoF : CharP F 2]
  parameter : ℕ
  parameter_pos : 0 < parameter
  card_field : Nat.card F = 2 ^ parameter
  phi : RingAut F
  phi_orderOf_odd : Odd (orderOf phi)
  equivModel : P ≃* TypeAModel phi

/-- A group has an inclusive ξ-length-two `A(n, φ)` model. -/
def IsXiLengthTwoTypeA (P : Type uP) [Group P] : Prop :=
  Nonempty (XiLengthTwoTypeAData.{uP, uF} P)

namespace XiLengthTwoTypeAData

/-- Forget only the nontriviality of `φ` from Peterfalvi's noncommutative
type-A data. -/
def ofTypeAData
    {P : Type uP} [Group P]
    (d : TypeAData.{uP, uF} P) :
    XiLengthTwoTypeAData.{uP, uF} P where
  F := d.F
  fieldF := d.fieldF
  finiteF := d.finiteF
  charTwoF := d.charTwoF
  parameter := d.parameter
  parameter_pos := d.parameter_pos
  card_field := d.card_field
  phi := d.phi
  phi_orderOf_odd := d.phi_orderOf_odd
  equivModel := d.equivModel

/-- Build inclusive `A(n, φ)` data from an actual central extension whose
square coordinate is `a ↦ a * φ(a)`. This is the source-faithful
`φ = 1` extension of `TypeAData.ofExtension`. -/
noncomputable def ofExtension
    {P : Type uP} [Group P]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    (parameter : ℕ) (parameter_pos : 0 < parameter)
    (card_field : Nat.card F = 2 ^ parameter)
    (phi : RingAut F)
    (phi_orderOf_odd : Odd (orderOf phi))
    (S : GroupExtension (Multiplicative F) P (Multiplicative F))
    (hcentral : S.inl.range ≤ Subgroup.center P)
    (hsq : ∀ x : P, x ^ 2 =
      S.inl (Multiplicative.ofAdd
        (typeAQuadraticMap phi (S.rightHom x).toAdd))) :
    XiLengthTwoTypeAData P := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let q := typeAQuadraticMap phi
  let basis := Module.finBasis (ZMod 2) F
  let extEquiv : S.Equiv (QuadraticExtension.extension q basis) := by
    apply GroupExtension.equivOfCommonSquareMap S
      (QuadraticExtension.extension q basis) hcentral
      (QuadraticExtension.range_inl_le_center q basis) q basis
    · exact hsq
    · intro x
      change x ^ 2 =
        (QuadraticExtension.extension q basis).inl
          (Multiplicative.ofAdd (q x.quotient))
      exact QuadraticExtension.sq_eq_inl_q q basis x
  exact
    { F := F
      parameter := parameter
      parameter_pos := parameter_pos
      card_field := card_field
      phi := phi
      phi_orderOf_odd := phi_orderOf_odd
      equivModel := extEquiv.toMulEquiv }

/-- Absorb a nonzero scalar in an `A(n, φ)` square formula into the kernel
coordinate, allowing `φ = 1`. -/
noncomputable def ofScaledSquareCoordinates
    {P : Type uP} [Group P]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    (parameter : ℕ) (parameter_pos : 0 < parameter)
    (card_field : Nat.card F = 2 ^ parameter)
    (phi : RingAut F)
    (phi_orderOf_odd : Odd (orderOf phi))
    (N : Subgroup P) [N.Normal]
    (left : Multiplicative F ≃* N)
    (right : P ⧸ N ≃* Multiplicative F)
    (hcentral : N ≤ Subgroup.center P)
    (epsilon : F) (hepsilon : epsilon ≠ 0)
    (hsq : ∀ x : P, x ^ 2 =
      left (Multiplicative.ofAdd
        (epsilon *
          ((right (QuotientGroup.mk' N x)).toAdd *
            phi (right (QuotientGroup.mk' N x)).toAdd)))) :
    XiLengthTwoTypeAData P := by
  let epsilonUnit : Fˣ := Units.mk0 epsilon hepsilon
  let scaleAdd : F ≃+ F :=
    (epsilonUnit.mulLeftLinearEquiv F F).toAddEquiv
  let scale : Multiplicative F ≃* Multiplicative F :=
    AddEquiv.toMultiplicative scaleAdd
  let left' : Multiplicative F ≃* N := scale.trans left
  let S : GroupExtension (Multiplicative F) P (Multiplicative F) :=
    GroupExtension.ofNormalSubgroupCoordinates N left' right
  apply ofExtension parameter parameter_pos card_field phi
    phi_orderOf_odd S
  · simpa only [S, GroupExtension.ofNormalSubgroupCoordinates_range_inl]
      using hcentral
  · intro x
    rw [hsq x]
    rfl

end XiLengthTwoTypeAData

/-- Every Peterfalvi type-A model is an inclusive Higman ξ-length-two
type-A model. -/
theorem isXiLengthTwoTypeA_of_isTypeA
    {P : Type uP} [Group P]
    (h : IsTypeA.{uP, uF} P) :
    IsXiLengthTwoTypeA.{uP, uF} P := by
  obtain ⟨d⟩ := h
  exact ⟨XiLengthTwoTypeAData.ofTypeAData d⟩

/-- The raw square equivalence for a homocyclic commutative group of
exponent four. The unreduced final-layer index keeps elaboration cheap. -/
noncomputable def homocyclicFourSquareEquivRaw
    {A ι : Type*} [CommGroup A] [Finite A]
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ 2)))) :
    (A ⧸ Agemo A 2 1) ≃* Agemo A 2 (2 - 1) :=
  actualQuotientEquivZeroLayer.trans
    (agemoSuccQuotientEquivLast ε (s := 0) (by omega))

/-- Squaring identifies the quotient by the squares with the subgroup of
squares in a homocyclic commutative group of exponent four. -/
noncomputable def homocyclicFourSquareEquiv
    {A ι : Type*} [CommGroup A] [Finite A]
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ 2)))) :
    (A ⧸ Agemo A 2 1) ≃* Agemo A 2 1 := by
  simpa only [Nat.reduceSub] using homocyclicFourSquareEquivRaw ε

@[simp] theorem homocyclicFourSquareEquiv_mk
    {A ι : Type*} [CommGroup A] [Finite A]
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ 2)))) (x : A) :
    ((homocyclicFourSquareEquiv ε (QuotientGroup.mk x) : Agemo A 2 1) : A) =
      x ^ 2 := by
  rfl

/-- A homocyclic commutative group of exponent four is Higman's inclusive
model A(n, 1), with actual finite-field square coordinates. -/
noncomputable def xiLengthTwoTypeAData_of_homocyclic_four
    {A : Type uP} {ι : Type*} [CommGroup A] [Finite A]
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ 2))))
    (hNtop : Agemo A 2 1 ≠ ⊤) :
    XiLengthTwoTypeAData.{uP, 0} A := by
  let N : Subgroup A := Agemo A 2 1
  letI : N.Normal := inferInstance
  letI : Nontrivial (A ⧸ N) :=
    QuotientGroup.nontrivial_iff.mpr (by simpa [N] using hNtop)
  let n := Module.finrank (ZMod 2) (Additive (A ⧸ N))
  have hn : 0 < n := Module.finrank_pos
  let F := GaloisField 2 n
  let coord : Additive (A ⧸ N) ≃ₗ[ZMod 2] F :=
    LinearEquiv.ofFinrankEq _ _ (by
      simpa [F, n] using (GaloisField.finrank 2 hn.ne').symm)
  let squareEquiv : (A ⧸ N) ≃* N := by
    simpa [N] using homocyclicFourSquareEquiv ε
  let kernelAdd : Additive N ≃+ F :=
    squareEquiv.toAdditive.symm.trans coord.toAddEquiv
  let quotientAdd : Additive (A ⧸ N) ≃+ F :=
    coord.toAddEquiv.trans (frobeniusEquiv F 2).symm.toAddEquiv
  let kernelMul : N ≃* Multiplicative F :=
    AddEquiv.toMultiplicativeRight kernelAdd
  let left : Multiplicative F ≃* N := kernelMul.symm
  let right : (A ⧸ N) ≃* Multiplicative F :=
    AddEquiv.toMultiplicativeRight quotientAdd
  refine XiLengthTwoTypeAData.ofScaledSquareCoordinates
    n hn (GaloisField.card 2 n hn.ne') (1 : RingAut F) (by simp)
    N left right ?_ (1 : F) one_ne_zero ?_
  · rw [CommGroup.center_eq_top]
    exact le_top
  · intro a
    simp only [one_mul]
    rw [← homocyclicFourSquareEquiv_mk ε a]
    apply congrArg Subtype.val
    apply kernelMul.injective
    simp only [kernelMul, left, MulEquiv.apply_symm_apply]
    apply Multiplicative.ofAdd.injective
    change coord
        (squareEquiv.toAdditive.symm
          (squareEquiv.toAdditive
            (Additive.ofMul (QuotientGroup.mk' N a)))) =
      (frobeniusEquiv F 2).symm
          (coord (Additive.ofMul (QuotientGroup.mk' N a))) *
        (frobeniusEquiv F 2).symm
          (coord (Additive.ofMul (QuotientGroup.mk' N a)))
    rw [squareEquiv.toAdditive.symm_apply_apply]
    rw [← pow_two, frobeniusEquiv_symm_pow_p]

/-- The faithful range of an invariant subgroup restriction is again a
cyclic actor transitive on that subgroup's involutions. -/
theorem restricted_range_isXiActor
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    (hxi : IsXiActor Y)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S) :
    IsXiActor hSinv.restrict.range := by
  refine ⟨?_, ?_⟩
  · letI : IsCyclic Y := hxi.cyclic
    exact isCyclic_of_surjective hSinv.restrict.rangeRestrict
      hSinv.restrict.rangeRestrict_surjective
  · intro x hx y hy
    have hxP : (x : P) ∈ involutions P := by
      refine ⟨congrArg Subtype.val hx.1, ?_⟩
      intro hx1
      exact hx.2 (Subtype.ext hx1)
    have hyP : (y : P) ∈ involutions P := by
      refine ⟨congrArg Subtype.val hy.1, ?_⟩
      intro hy1
      exact hy.2 (Subtype.ext hy1)
    obtain ⟨a, ha⟩ := hxi.transitive (x : P) hxP (y : P) hyP
    refine ⟨hSinv.restrict.rangeRestrict a, ?_⟩
    exact Subtype.ext ha

/-- If a subgroup contains every ambient involution, it has exactly the
same number of involutions as the ambient group. -/
theorem involutions_ncard_subgroup_eq_of_subset
    {P : Type uP} [Group P]
    (S : Subgroup P)
    (hinvS : involutions P ⊆ S) :
    (involutions S).ncard = (involutions P).ncard := by
  let f : ↑(involutions S) → ↑(involutions P) := fun x =>
    ⟨((x.1 : S) : P), by
      refine ⟨congrArg Subtype.val x.2.1, ?_⟩
      intro hx1
      exact x.2.2 (Subtype.ext hx1)⟩
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hxyP := congrArg
      (fun z : ↑(involutions P) => (z : P)) hxy
    simpa [f] using hxyP
  have hf_surjective : Function.Surjective f := by
    intro z
    let s : S := ⟨z.1, hinvS z.2⟩
    have hs : s ∈ involutions S := by
      refine ⟨?_, ?_⟩
      · apply Subtype.ext
        exact z.2.1
      · intro hs1
        apply z.2.2
        exact congrArg Subtype.val hs1
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Subtype.ext
    rfl
  calc
    (involutions S).ncard = Nat.card ↑(involutions S) :=
      (Nat.card_coe_set_eq (involutions S)).symm
    _ = Nat.card ↑(involutions P) :=
      Nat.card_congr (Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩)
    _ = (involutions P).ncard := Nat.card_coe_set_eq (involutions P)

/-- Two distinct ambient involutions give two distinct involutions in any
subgroup which contains every ambient involution. -/
theorem exists_distinct_involutions_subgroup_of_subset
    {P : Type uP} [Group P]
    {S : Subgroup P}
    (hinvS : involutions P ⊆ S)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y) :
    ∃ x y : S,
      x ∈ involutions S ∧ y ∈ involutions S ∧ x ≠ y := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hmulti
  let xs : S := ⟨x, hinvS hx⟩
  let ys : S := ⟨y, hinvS hy⟩
  refine ⟨xs, ys, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact Subtype.ext hx.1
    · intro hxs
      exact hx.2 (congrArg Subtype.val hxs)
  · refine ⟨?_, ?_⟩
    · exact Subtype.ext hy.1
    · intro hys
      exact hy.2 (congrArg Subtype.val hys)
  · intro hxys
    exact hxy (congrArg Subtype.val hxys)

/-- Higman's prime-support condition descends from the original actor to
the faithful range of its restriction. -/
theorem restricted_range_primeSupport
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hinvS : involutions P ⊆ S)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card hSinv.restrict.range →
      p ∣ (involutions S).ncard := by
  intro p hp hpRange
  rw [involutions_ncard_subgroup_eq_of_subset S hinvS]
  exact hprime p hp
    (hpRange.trans (Subgroup.card_range_dvd hSinv.restrict))

set_option maxHeartbeats 800000 in
-- The contradiction compares two Agemo layers through the invariant lattice.
/-- A commutative 2-group with xi-length two and more than one involution is
homocyclic of exponent four. This is Higman's abelian A(n, 1) branch. -/
theorem exists_homocyclic_four_of_commutative_xiLengthTwo
    {A : Type uP} [CommGroup A] [Finite A]
    {Y : Subgroup (MulAut A)}
    (hA : IsPGroup 2 A)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    (hmulti : ∃ x y : A,
      x ∈ involutions A ∧ y ∈ involutions A ∧ x ≠ y) :
    ∃ (ι : Type) (_ : Fintype ι),
      Nonempty (A ≃* (ι → Multiplicative (ZMod 4))) := by
  obtain ⟨ι, hι, e, he, ⟨ε⟩, hclass⟩ :=
    exists_homocyclic_and_invariant_eq_agemo
      hA Y.subtype hxi.transitive
  obtain ⟨M, hbotM, hMtop⟩ := hlen.exists_middle
  obtain ⟨s, hse, hM⟩ := hclass M.1 M.2.2
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    apply hMtop.ne
    apply Subtype.ext
    change M.1 = (⊤ : Subgroup A)
    simpa [agemo_zero_eq_top] using hM
  have hsne : s ≠ e := by
    intro hs
    subst s
    apply hbotM.ne'
    apply Subtype.ext
    change M.1 = (⊥ : Subgroup A)
    simpa [agemo_two_eq_bot_of_equiv_pi_zmod ε] using hM
  have he2 : 2 ≤ e := by omega
  have he_le : e ≤ 2 := by
    by_contra hnot
    have he3 : 3 ≤ e := by omega
    obtain ⟨x, _, hx, _, _⟩ := hmulti
    have hxlast : x ∈ Agemo A 2 (e - 1) :=
      (sq_eq_one_iff_mem_lastAgemoLayer ε he).mp hx.1
    have hxone : x ∈ Agemo A 2 1 :=
      (Agemo.anti (by omega : 1 ≤ e - 1)) hxlast
    have hxtwo : x ∈ Agemo A 2 2 :=
      (Agemo.anti (by omega : 2 ≤ e - 1)) hxlast
    have hOneNeBot : Agemo A 2 1 ≠ (⊥ : Subgroup A) := by
      intro hbot
      have := hxone
      rw [hbot] at this
      exact hx.2 (Subgroup.mem_bot.mp this)
    have hTwoNeBot : Agemo A 2 2 ≠ (⊥ : Subgroup A) := by
      intro hbot
      have := hxtwo
      rw [hbot] at this
      exact hx.2 (Subgroup.mem_bot.mp this)
    letI : Nontrivial (Agemo A 2 1) :=
      (Subgroup.nontrivial_iff_ne_bot (Agemo A 2 1)).mpr hOneNeBot
    letI : Nontrivial A :=
      (Agemo A 2 1).subtype_injective.nontrivial
    have hPhiNeTop : frattini A ≠ (⊤ : Subgroup A) := by
      obtain ⟨N, hN, _⟩ :=
        (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup A)).resolve_left
          bot_lt_top.ne
      exact fun htop => hN.1
        (le_antisymm le_top (htop ▸ frattini_le_coatom hN))
    have hOneNeTop : Agemo A 2 1 ≠ (⊤ : Subgroup A) := by
      rw [← NormalInvariantCover.frattini_eq_agemo_one hA]
      exact hPhiNeTop
    have hTwoNeTop : Agemo A 2 2 ≠ (⊤ : Subgroup A) := by
      intro htop
      apply hOneNeTop
      apply top_unique
      rw [← htop]
      exact Agemo.anti (by omega : 1 ≤ 2)
    let U : NormalInvariantSubgroup Y.subtype :=
      ⟨Agemo A 2 1, ⟨inferInstance,
        IsAInvariant.of_characteristic Y.subtype⟩⟩
    let V : NormalInvariantSubgroup Y.subtype :=
      ⟨Agemo A 2 2, ⟨inferInstance,
        IsAInvariant.of_characteristic Y.subtype⟩⟩
    have hUneBot : U ≠ normalInvariantBot Y.subtype := by
      intro h
      exact hOneNeBot (congrArg Subtype.val h)
    have hUneTop : U ≠ normalInvariantTop Y.subtype := by
      intro h
      exact hOneNeTop (congrArg Subtype.val h)
    have hVneBot : V ≠ normalInvariantBot Y.subtype := by
      intro h
      exact hTwoNeBot (congrArg Subtype.val h)
    have hVneTop : V ≠ normalInvariantTop Y.subtype := by
      intro h
      exact hTwoNeTop (congrArg Subtype.val h)
    have hUV : U = V :=
      hlen.eq_of_ne_bot_of_ne_top hA hxi.transitive
        hUneBot hUneTop hVneBot hVneTop
    have hOneTwo : Agemo A 2 1 = Agemo A 2 2 :=
      congrArg Subtype.val hUV
    let B := Agemo A 2 1
    letI : Nontrivial B :=
      (Subgroup.nontrivial_iff_ne_bot B).mpr hOneNeBot
    have hBFratNeTop : frattini B ≠ (⊤ : Subgroup B) := by
      obtain ⟨N, hN, _⟩ :=
        (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup B)).resolve_left
          bot_lt_top.ne
      exact fun htop => hN.1
        (le_antisymm le_top (htop ▸ frattini_le_coatom hN))
    apply hBFratNeTop
    rw [NormalInvariantCover.frattini_eq_agemo_one (hA.to_subgroup B)]
    rw [← agemo_succ_subgroupOf_eq_agemo_one (A := A) (p := 2) (s := 1)]
    exact Subgroup.subgroupOf_eq_top.mpr (by simpa [B] using hOneTwo.le)
  have heq : e = 2 := le_antisymm he_le he2
  subst e
  simpa using ⟨ι, ⟨hι⟩, ⟨ε⟩⟩

/-- A noncommutative proper invariant subgroup strictly above `Φ(P)` is
of Peterfalvi type A, by applying Higman's Lemma 11 to the faithful
restricted actor. -/
theorem isTypeA_invariant_subgroup_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P < S)
    (hStop : S < (⊤ : Subgroup P))
    (hncommS : ¬ IsMulCommutative S) :
    IsTypeA.{uP, 0} S := by
  have hSneBot : S ≠ (⊥ : Subgroup P) :=
    ne_of_gt (lt_of_le_of_lt bot_le hPhiS)
  have hinvS : involutions P ⊆ S :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hSinv hSneBot
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hxiS : IsXiActor hSinv.restrict.range :=
    restricted_range_isXiActor hxi hSinv
  have hlenS : HasXiLengthTwo hSinv.restrict.range.subtype :=
    restricted_range_hasXiLengthTwo_of_xiLengthThree
      hP hncomm hxi hlen hEA hSinv hPhiS hStop
  have hmultiS : ∃ x y : S,
      x ∈ involutions S ∧ y ∈ involutions S ∧ x ≠ y :=
    exists_distinct_involutions_subgroup_of_subset hinvS hmulti
  have hprimeS : ∀ p : ℕ, p.Prime →
      p ∣ Nat.card hSinv.restrict.range →
        p ∣ (involutions S).ncard :=
    restricted_range_primeSupport hSinv hinvS hprime
  exact higmanLemmaEleven (hP.to_subgroup S) hncommS hmultiS
    hxiS hlenS hprimeS

/-- The noncommutative branch of a lifted ξ-length-two factor has the
inclusive source-facing `A(n, φ)` model. -/
theorem isXiLengthTwoTypeA_invariant_subgroup_of_xiLengthThree_of_noncommutative
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P < S)
    (hStop : S < (⊤ : Subgroup P))
    (hncommS : ¬ IsMulCommutative S) :
    IsXiLengthTwoTypeA.{uP, 0} S :=
  isXiLengthTwoTypeA_of_isTypeA
    (isTypeA_invariant_subgroup_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime hSinv hPhiS hStop hncommS)

/-- The commutative branch of a lifted xi-length-two factor is Higman's
abelian model A(n, 1), not Peterfalvi's noncommutative TypeAData. -/
theorem isXiLengthTwoTypeA_invariant_subgroup_of_xiLengthThree_of_commutative
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P < S)
    (hStop : S < (⊤ : Subgroup P))
    (hcommS : IsMulCommutative S) :
    IsXiLengthTwoTypeA.{uP, 0} S := by
  letI : CommGroup S :=
    { (inferInstance : Group S) with mul_comm := hcommS.is_comm.comm }
  have hSneBot : S ≠ (⊥ : Subgroup P) :=
    ne_of_gt (lt_of_le_of_lt bot_le hPhiS)
  letI : Nontrivial S :=
    (Subgroup.nontrivial_iff_ne_bot S).mpr hSneBot
  have hinvS : involutions P ⊆ S :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hSinv hSneBot
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hxiS : IsXiActor hSinv.restrict.range :=
    restricted_range_isXiActor hxi hSinv
  have hlenS : HasXiLengthTwo hSinv.restrict.range.subtype :=
    restricted_range_hasXiLengthTwo_of_xiLengthThree
      hP hncomm hxi hlen hEA hSinv hPhiS hStop
  have hmultiS : ∃ x y : S,
      x ∈ involutions S ∧ y ∈ involutions S ∧ x ≠ y :=
    exists_distinct_involutions_subgroup_of_subset hinvS hmulti
  obtain ⟨ι, _, ⟨ε⟩⟩ :=
    exists_homocyclic_four_of_commutative_xiLengthTwo
      (hP.to_subgroup S) hxiS hlenS hmultiS
  have hFrattiniNeTop : frattini S ≠ (⊤ : Subgroup S) := by
    obtain ⟨M, hM, _⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup S)).resolve_left
        bot_lt_top.ne
    exact fun htop => hM.1
      (le_antisymm le_top (htop ▸ frattini_le_coatom hM))
  have hAgemoNeTop : Agemo S 2 1 ≠ (⊤ : Subgroup S) := by
    rw [← NormalInvariantCover.frattini_eq_agemo_one (hP.to_subgroup S)]
    exact hFrattiniNeTop
  have ε' : S ≃* (ι → Multiplicative (ZMod (2 ^ 2))) := by
    simpa using ε
  exact ⟨xiLengthTwoTypeAData_of_homocyclic_four ε' hAgemoNeTop⟩

/-- Every proper invariant factor strictly above the ambient Frattini
subgroup has Higman's inclusive A(n, phi) model. -/
theorem isXiLengthTwoTypeA_invariant_subgroup_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P < S)
    (hStop : S < (⊤ : Subgroup P)) :
    IsXiLengthTwoTypeA.{uP, 0} S := by
  by_cases hcommS : IsMulCommutative S
  · exact
      isXiLengthTwoTypeA_invariant_subgroup_of_xiLengthThree_of_commutative
        hP hncomm hmulti hxi hlen hprime hSinv hPhiS hStop hcommS
  · exact
      isXiLengthTwoTypeA_invariant_subgroup_of_xiLengthThree_of_noncommutative
        hP hncomm hmulti hxi hlen hprime hSinv hPhiS hStop hcommS

end OddOrder.Higman.Suzuki2Groups
