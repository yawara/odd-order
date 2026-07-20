/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanNormalCover
import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralGraded
import OddOrder.Higman.Suzuki2Groups.CenterInvolutions

/-!
# Higman's ξ-length-two reduction

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 11,
pp. 88--89.

The opening sentence of Lemma 11 says that, when the `ξ`-length is two, the
only `ξ`-composition series is

`P > Φ(P) > 1`.

Here `ξ` is represented by its faithful cyclic subgroup of `MulAut P`, and
`ξ`-composition terms are the actual normal actor-invariant subgroups from
`NormalInvariantSubgroup`.  Length two is expressed order-theoretically: a
two-step strict chain exists, while no three-step strict chain exists.  Thus
uniqueness of the middle term is a theorem, not part of the definition.

The transitivity hypothesis is deliberately weaker than regularity.  Higman's
original definition assumes a cyclic actor transitive on the involutions;
regularity is obtained later from the classification.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.Isaacs.Ch04

variable {P : Type*} [Group P]

/-- Higman's `ξ`: a faithful cyclic automorphism subgroup which is transitive
on the nonidentity involutions.  Faithfulness is built into the embedding in
`MulAut P`; regularity is not assumed. -/
structure IsXiActor (X : Subgroup (MulAut P)) : Prop where
  cyclic : IsCyclic ↥X
  transitive : ActsTransitivelyOnInvolutions X

variable {X : Type*} [Group X]

/-- The bottom term in the poset of normal actor-invariant subgroups. -/
def normalInvariantBot (act : X →* MulAut P) :
    NormalInvariantSubgroup act :=
  ⟨⊥, ⟨inferInstance, IsAInvariant.bot act⟩⟩

/-- The top term in the poset of normal actor-invariant subgroups. -/
def normalInvariantTop (act : X →* MulAut P) :
    NormalInvariantSubgroup act :=
  ⟨⊤, ⟨inferInstance, IsAInvariant.top act⟩⟩

/-- Intersection in the concrete poset of normal actor-invariant subgroups. -/
def normalInvariantInf (act : X →* MulAut P)
    (A B : NormalInvariantSubgroup act) : NormalInvariantSubgroup act := by
  letI : A.1.Normal := A.2.1
  letI : B.1.Normal := B.2.1
  exact ⟨A.1 ⊓ B.1, ⟨inferInstance, A.2.2.inf B.2.2⟩⟩

/-- The source-faithful meaning of `ξ`-length two.

There is a chain with two strict inclusions between the bottom and top normal
actor-invariant subgroups, and there is no chain with three strict inclusions.
This is the finite-poset content of composition length two, without choosing
or postulating the eventual Frattini middle term. -/
def HasXiLengthTwo (act : X →* MulAut P) : Prop :=
  ∃ M : NormalInvariantSubgroup act,
    normalInvariantBot act < M ∧
      M < normalInvariantTop act ∧
        ∀ A B C D : NormalInvariantSubgroup act,
          A < B → B < C → C < D → False

namespace HasXiLengthTwo

variable {act : X →* MulAut P}

theorem exists_middle (h : HasXiLengthTwo act) :
    ∃ M : NormalInvariantSubgroup act,
      normalInvariantBot act < M ∧ M < normalInvariantTop act := by
  rcases h with ⟨M, hbot, htop, _⟩
  exact ⟨M, hbot, htop⟩

theorem no_chain_of_length_three (h : HasXiLengthTwo act)
    {A B C D : NormalInvariantSubgroup act}
    (hAB : A < B) (hBC : B < C) (hCD : C < D) : False := by
  rcases h with ⟨_, _, _, hlong⟩
  exact hlong A B C D hAB hBC hCD

theorem bot_lt_of_ne_bot (_h : HasXiLengthTwo act)
    {A : NormalInvariantSubgroup act}
    (hA : A ≠ normalInvariantBot act) : normalInvariantBot act < A := by
  apply lt_of_le_of_ne
  · change (⊥ : Subgroup P) ≤ A.1
    exact bot_le
  · exact hA.symm

theorem lt_top_of_ne_top (_h : HasXiLengthTwo act)
    {A : NormalInvariantSubgroup act}
    (hA : A ≠ normalInvariantTop act) : A < normalInvariantTop act := by
  apply lt_of_le_of_ne
  · change A.1 ≤ (⊤ : Subgroup P)
    exact le_top
  · exact hA

/-- Every nontrivial proper term covers the bottom term. -/
theorem bot_covBy_of_ne_bot_of_ne_top (h : HasXiLengthTwo act)
    {A : NormalInvariantSubgroup act}
    (hAbot : A ≠ normalInvariantBot act)
    (hAtop : A ≠ normalInvariantTop act) :
    normalInvariantBot act ⋖ A := by
  have hlt := h.bot_lt_of_ne_bot hAbot
  by_contra hcov
  obtain ⟨B, hbotB, hBA⟩ := (not_covBy_iff hlt).mp hcov
  exact h.no_chain_of_length_three
    hbotB hBA (h.lt_top_of_ne_top hAtop)

/-- Every nontrivial proper term is covered by the top term. -/
theorem covBy_top_of_ne_bot_of_ne_top (h : HasXiLengthTwo act)
    {A : NormalInvariantSubgroup act}
    (hAbot : A ≠ normalInvariantBot act)
    (hAtop : A ≠ normalInvariantTop act) :
    A ⋖ normalInvariantTop act := by
  have hlt := h.lt_top_of_ne_top hAtop
  by_contra hcov
  obtain ⟨B, hAB, hBtop⟩ := (not_covBy_iff hlt).mp hcov
  exact h.no_chain_of_length_three
    (h.bot_lt_of_ne_bot hAbot) hAB hBtop

/-- A nontrivial proper term gives the full two-cover composition series. -/
theorem covers_of_ne_bot_of_ne_top (h : HasXiLengthTwo act)
    {A : NormalInvariantSubgroup act}
    (hAbot : A ≠ normalInvariantBot act)
    (hAtop : A ≠ normalInvariantTop act) :
    normalInvariantBot act ⋖ A ∧ A ⋖ normalInvariantTop act :=
  ⟨h.bot_covBy_of_ne_bot_of_ne_top hAbot hAtop,
    h.covBy_top_of_ne_bot_of_ne_top hAbot hAtop⟩

end HasXiLengthTwo

variable {Y : Subgroup (MulAut P)}

/-- Under transitivity on involutions, the middle term of a length-two
normal-invariant poset is unique.

Indeed, choose an involution in one nontrivial middle term.  Higman Lemma 2's
opening observation puts that involution in every other nontrivial invariant
term.  Their intersection is therefore nontrivial; since each middle term
covers the bottom, the intersection equals both. -/
theorem HasXiLengthTwo.eq_of_ne_bot_of_ne_top
    [Finite P] (hP : IsPGroup 2 P)
    (htrans : ActsTransitivelyOnInvolutions Y)
    (hlen : HasXiLengthTwo Y.subtype)
    {A B : NormalInvariantSubgroup Y.subtype}
    (hAbot : A ≠ normalInvariantBot Y.subtype)
    (hAtop : A ≠ normalInvariantTop Y.subtype)
    (hBbot : B ≠ normalInvariantBot Y.subtype)
    (hBtop : B ≠ normalInvariantTop Y.subtype) : A = B := by
  have hAval_ne : A.1 ≠ (⊥ : Subgroup P) := by
    intro hAval
    apply hAbot
    apply Subtype.ext
    exact hAval
  have hBval_ne : B.1 ≠ (⊥ : Subgroup P) := by
    intro hBval
    apply hBbot
    apply Subtype.ext
    exact hBval
  letI : Nontrivial A.1 :=
    (Subgroup.nontrivial_iff_ne_bot A.1).mpr hAval_ne
  have hA2 : IsPGroup 2 A.1 := hP.to_subgroup A.1
  have hcard_ne : Nat.card A.1 ≠ 1 :=
    ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  have htwo_dvd : 2 ∣ Nat.card A.1 :=
    hA2.card_eq_or_dvd.resolve_left hcard_ne
  obtain ⟨z, hzorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := A.1) 2 htwo_dvd
  have hz := orderOf_eq_prime_iff.mp hzorder
  have hzP : (z : P) ∈ involutions P := by
    refine ⟨congrArg Subtype.val hz.1, ?_⟩
    intro hz1
    exact hz.2 (Subtype.ext hz1)
  have hzB : (z : P) ∈ B.1 :=
    involutions_subset_of_nontrivial_invariant
      hP Y htrans B.2.2 hBval_ne hzP
  let C : NormalInvariantSubgroup Y.subtype :=
    normalInvariantInf Y.subtype A B
  have hzC : (z : P) ∈ C.1 := by
    exact ⟨z.2, hzB⟩
  have hCbot : C ≠ normalInvariantBot Y.subtype := by
    intro hC
    have hval := congrArg Subtype.val hC
    have hzbot := hzC
    change (z : P) ∈ C.1 at hzbot
    rw [hval] at hzbot
    exact hz.2 (Subtype.ext (Subgroup.mem_bot.mp hzbot))
  have hbotC : normalInvariantBot Y.subtype ≤ C := by
    change (⊥ : Subgroup P) ≤ C.1
    exact bot_le
  have hCA : C ≤ A := by
    change C.1 ≤ A.1
    exact inf_le_left
  have hCB : C ≤ B := by
    change C.1 ≤ B.1
    exact inf_le_right
  have hcovA := hlen.bot_covBy_of_ne_bot_of_ne_top hAbot hAtop
  have hcovB := hlen.bot_covBy_of_ne_bot_of_ne_top hBbot hBtop
  have hCAeq : C = A :=
    (hcovA.eq_or_eq hbotC hCA).resolve_left hCbot
  have hCBeq : C = B :=
    (hcovB.eq_or_eq hbotC hCB).resolve_left hCbot
  exact hCAeq.symm.trans hCBeq

/-! ## The sole middle term -/

/-- The Frattini subgroup as a concrete normal actor-invariant term. -/
def frattiniNormalInvariant (act : X →* MulAut P) :
    NormalInvariantSubgroup act :=
  ⟨frattini P, ⟨inferInstance, IsAInvariant.frattini act⟩⟩

/-- The derived subgroup as a concrete normal actor-invariant term. -/
def commutatorNormalInvariant (act : X →* MulAut P) :
    NormalInvariantSubgroup act :=
  ⟨_root_.commutator P, ⟨inferInstance, IsAInvariant.commutator_self act⟩⟩

/-- The center as a concrete normal actor-invariant term. -/
def centerNormalInvariant (act : X →* MulAut P) :
    NormalInvariantSubgroup act :=
  ⟨Subgroup.center P, ⟨inferInstance, IsAInvariant.center act⟩⟩

/-- In a nontrivial finite group the Frattini subgroup is proper. -/
private theorem frattini_ne_top_of_nontrivial
    [Finite P] [Nontrivial P] : frattini P ≠ ⊤ := by
  obtain ⟨M, hM, _⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup P)).resolve_left
      bot_lt_top.ne
  exact fun htop => hM.1
    (le_antisymm le_top (htop ▸ frattini_le_coatom hM))

/-- **Higman, Suzuki 2-groups, Lemma 11, opening reduction** (pp. 88--89):
for a nonabelian finite `2`-group of `ξ`-length two, the derived subgroup,
Frattini subgroup, and center are the same unique middle term. -/
theorem commutator_eq_frattini_and_frattini_eq_center
    [Finite P] (hP : IsPGroup 2 P) (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y) (hlen : HasXiLengthTwo Y.subtype) :
    _root_.commutator P = frattini P ∧
      frattini P = Subgroup.center P := by
  have hcomm_ne : _root_.commutator P ≠ (⊥ : Subgroup P) :=
    fun h => hncomm ((commutator_eq_bot_iff P).mp h)
  letI : Nontrivial (_root_.commutator P) :=
    (Subgroup.nontrivial_iff_ne_bot (_root_.commutator P)).mpr hcomm_ne
  letI : Nontrivial P :=
    (_root_.commutator P).subtype_injective.nontrivial
  have hPhi_ne_top : frattini P ≠ (⊤ : Subgroup P) :=
    frattini_ne_top_of_nontrivial
  have hcomm_le_Phi : _root_.commutator P ≤ frattini P :=
    OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP
  have hPhi_ne : frattini P ≠ (⊥ : Subgroup P) := by
    intro hPhi
    apply hcomm_ne
    exact le_bot_iff.mp (hcomm_le_Phi.trans_eq hPhi)
  have hcomm_ne_top : _root_.commutator P ≠ (⊤ : Subgroup P) := by
    intro hcomm
    apply hPhi_ne_top
    apply le_antisymm le_top
    rw [← hcomm]
    exact hcomm_le_Phi
  letI : Nontrivial ↥(Subgroup.center P) := hP.center_nontrivial
  have hcenter_ne : Subgroup.center P ≠ (⊥ : Subgroup P) :=
    (Subgroup.nontrivial_iff_ne_bot (Subgroup.center P)).mp inferInstance
  have hcenter_ne_top : Subgroup.center P ≠ (⊤ : Subgroup P) := by
    intro hcenter
    apply hncomm
    apply (commutator_eq_bot_iff P).mp
    exact (commutator_eq_bot_iff_center_eq_top (G := P)).mpr hcenter
  have hcomm_bot :
      commutatorNormalInvariant Y.subtype ≠ normalInvariantBot Y.subtype := by
    intro h
    exact hcomm_ne (congrArg Subtype.val h)
  have hcomm_top :
      commutatorNormalInvariant Y.subtype ≠ normalInvariantTop Y.subtype := by
    intro h
    exact hcomm_ne_top (congrArg Subtype.val h)
  have hPhi_bot :
      frattiniNormalInvariant Y.subtype ≠ normalInvariantBot Y.subtype := by
    intro h
    exact hPhi_ne (congrArg Subtype.val h)
  have hPhi_top :
      frattiniNormalInvariant Y.subtype ≠ normalInvariantTop Y.subtype := by
    intro h
    exact hPhi_ne_top (congrArg Subtype.val h)
  have hcenter_bot :
      centerNormalInvariant Y.subtype ≠ normalInvariantBot Y.subtype := by
    intro h
    exact hcenter_ne (congrArg Subtype.val h)
  have hcenter_top :
      centerNormalInvariant Y.subtype ≠ normalInvariantTop Y.subtype := by
    intro h
    exact hcenter_ne_top (congrArg Subtype.val h)
  have hcommPhi := hlen.eq_of_ne_bot_of_ne_top hP hxi.transitive
    hcomm_bot hcomm_top hPhi_bot hPhi_top
  have hPhiCenter := hlen.eq_of_ne_bot_of_ne_top hP hxi.transitive
    hPhi_bot hPhi_top hcenter_bot hcenter_top
  exact ⟨congrArg Subtype.val hcommPhi, congrArg Subtype.val hPhiCenter⟩

/-- The first Agemo subgroup is the same middle term.  The reverse inclusion
uses the general three-square identity `P' ≤ ℧¹(P)`. -/
theorem agemo_one_eq_frattini
    [Finite P] (hP : IsPGroup 2 P) (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y) (hlen : HasXiLengthTwo Y.subtype) :
    Agemo P 2 1 = frattini P := by
  have heq := commutator_eq_frattini_and_frattini_eq_center
    hP hncomm hxi hlen
  apply le_antisymm
  · rw [Agemo, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    simpa using IsPGroup.pow_mem_frattini hP x
  · rw [← heq.1]
    exact commutator_le_agemo_two_one P

/-- Every square lies in the center in the length-two case. -/
theorem square_mem_center
    [Finite P] (hP : IsPGroup 2 P) (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y) (hlen : HasXiLengthTwo Y.subtype) (x : P) :
    x ^ 2 ∈ Subgroup.center P := by
  have hx : x ^ 2 ∈ Agemo P 2 1 := by
    simpa using (Agemo.mem_of_eq_pow (G := P) (p := 2) (n := 1) x)
  rw [agemo_one_eq_frattini hP hncomm hxi hlen,
    (commutator_eq_frattini_and_frattini_eq_center
      hP hncomm hxi hlen).2] at hx
  exact hx

/-- A length-two group has nilpotency class at most two, expressed without a
choice of nilpotency-class convention. -/
theorem lowerCentralSeries_two_eq_bot
    [Finite P] (hP : IsPGroup 2 P) (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y) (hlen : HasXiLengthTwo Y.subtype) :
    (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥ := by
  have heq := commutator_eq_frattini_and_frattini_eq_center
    hP hncomm hxi hlen
  have hle : (⊤ : Subgroup P).lowerCentralSeries 1 ≤ Subgroup.center P := by
    rw [Subgroup.top_lowerCentralSeries_one, heq.1, heq.2]
  simpa using
    (Subgroup.lowerCentralSeries_succ_eq_bot (⊤ : Subgroup P) hle)

/-! ## Exponent two and the exact lower-central terms -/

/-- The first Agemo subgroup of the Frattini subgroup has trivial ambient
image.  If it were nontrivial, it would be another nontrivial proper normal
actor-invariant subgroup and hence, by uniqueness of the middle term, would
equal `Φ(P)`.  Injectivity of the subtype map would then make the Frattini
subgroup of the finite `2`-group `Φ(P)` equal to the whole group, impossible. -/
theorem frattini_agemo_one_map_eq_bot
    [Finite P] (hP : IsPGroup 2 P) (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y) (hlen : HasXiLengthTwo Y.subtype) :
    (Agemo ↥(frattini P) 2 1).map (frattini P).subtype = ⊥ := by
  have heq := commutator_eq_frattini_and_frattini_eq_center
    hP hncomm hxi hlen
  have hcomm_ne : _root_.commutator P ≠ (⊥ : Subgroup P) :=
    fun h => hncomm ((commutator_eq_bot_iff P).mp h)
  letI : Nontrivial (_root_.commutator P) :=
    (Subgroup.nontrivial_iff_ne_bot (_root_.commutator P)).mpr hcomm_ne
  letI : Nontrivial P :=
    (_root_.commutator P).subtype_injective.nontrivial
  have hPhi_ne : frattini P ≠ (⊥ : Subgroup P) := by
    rw [← heq.1]
    exact hcomm_ne
  letI : Nontrivial ↥(frattini P) :=
    (Subgroup.nontrivial_iff_ne_bot (frattini P)).mpr hPhi_ne
  have hPhi_ne_top : frattini P ≠ (⊤ : Subgroup P) :=
    frattini_ne_top_of_nontrivial
  letI : CommGroup ↥(frattini P) :=
    { (inferInstance : Group ↥(frattini P)) with
      mul_comm := fun x y => by
        apply Subtype.ext
        change (x : P) * (y : P) = (y : P) * (x : P)
        have hx : (x : P) ∈ Subgroup.center P := by
          rw [← heq.2]
          exact x.2
        exact (Subgroup.mem_center_iff.mp hx y).symm }
  let B : Subgroup P :=
    (Agemo ↥(frattini P) 2 1).map (frattini P).subtype
  obtain ⟨hBinv, hBnormal, hBPhi⟩ :=
    aInvariant_normal_map_of_characteristic
      (IsAInvariant.frattini Y.subtype) (Agemo ↥(frattini P) 2 1)
  by_contra hBne
  have hBne_top : B ≠ (⊤ : Subgroup P) := by
    intro hBtop
    apply hPhi_ne_top
    apply le_antisymm le_top
    rw [← hBtop]
    exact hBPhi
  let Bni : NormalInvariantSubgroup Y.subtype :=
    ⟨B, hBnormal, hBinv⟩
  have hBni_bot : Bni ≠ normalInvariantBot Y.subtype := by
    intro h
    apply hBne
    exact congrArg Subtype.val h
  have hBni_top : Bni ≠ normalInvariantTop Y.subtype := by
    intro h
    apply hBne_top
    exact congrArg Subtype.val h
  have hPhi_bot :
      frattiniNormalInvariant Y.subtype ≠ normalInvariantBot Y.subtype := by
    intro h
    exact hPhi_ne (congrArg Subtype.val h)
  have hPhi_top :
      frattiniNormalInvariant Y.subtype ≠ normalInvariantTop Y.subtype := by
    intro h
    exact hPhi_ne_top (congrArg Subtype.val h)
  have hB_eq_Phi : B = frattini P := congrArg Subtype.val
    (hlen.eq_of_ne_bot_of_ne_top hP hxi.transitive
      hBni_bot hBni_top hPhi_bot hPhi_top)
  have hmaps :
      (Agemo ↥(frattini P) 2 1).map (frattini P).subtype =
        (⊤ : Subgroup ↥(frattini P)).map (frattini P).subtype := by
    calc
      (Agemo ↥(frattini P) 2 1).map (frattini P).subtype = B := rfl
      _ = frattini P := hB_eq_Phi
      _ = (⊤ : Subgroup ↥(frattini P)).map (frattini P).subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hagemo_top : Agemo ↥(frattini P) 2 1 = ⊤ :=
    Subgroup.map_injective (frattini P).subtype_injective hmaps
  have hPhiP : IsPGroup 2 ↥(frattini P) := hP.to_subgroup (frattini P)
  have hagemo_le : Agemo ↥(frattini P) 2 1 ≤ frattini ↥(frattini P) := by
    rw [Agemo, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    simpa using IsPGroup.pow_mem_frattini hPhiP x
  have hfrattini_top : frattini ↥(frattini P) = ⊤ := by
    apply top_unique
    rw [← hagemo_top]
    exact hagemo_le
  have hbot_top : (⊥ : Subgroup ↥(frattini P)) = ⊤ := by
    apply frattini_nongenerating
    simp [hfrattini_top]
  exact (bot_ne_top : (⊥ : Subgroup ↥(frattini P)) ≠ ⊤) hbot_top

/-- The unique middle term `Φ(P)` is elementary abelian: every one of its
elements has square one. -/
theorem frattini_sq_eq_one
    [Finite P] (hP : IsPGroup 2 P) (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y) (hlen : HasXiLengthTwo Y.subtype)
    (z : frattini P) : z ^ 2 = 1 := by
  have hzAgemo : z ^ 2 ∈ Agemo ↥(frattini P) 2 1 := by
    simpa using
      (Agemo.mem_of_eq_pow (G := ↥(frattini P)) (p := 2) (n := 1) z)
  have hzmap : ((z ^ 2 : frattini P) : P) ∈
      (Agemo ↥(frattini P) 2 1).map (frattini P).subtype :=
    ⟨z ^ 2, hzAgemo, rfl⟩
  rw [frattini_agemo_one_map_eq_bot hP hncomm hxi hlen] at hzmap
  exact Subtype.ext (Subgroup.mem_bot.mp hzmap)

/-- The Frattini subgroup is exactly the identity together with the central
involutions. -/
theorem frattini_eq_involutionSubgroup
    [Finite P] (hP : IsPGroup 2 P) (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y) (hlen : HasXiLengthTwo Y.subtype) :
    frattini P = involutionSubgroup P := by
  have heq := commutator_eq_frattini_and_frattini_eq_center
    hP hncomm hxi hlen
  apply le_antisymm
  · intro z hz
    rw [involutionSubgroup, mem_omega1OfAbelian]
    refine ⟨?_, ?_⟩
    · rwa [← heq.2]
    · simpa using congrArg Subtype.val
        (frattini_sq_eq_one hP hncomm hxi hlen ⟨z, hz⟩)
  · intro z hz
    rw [heq.2]
    exact (mem_omega1OfAbelian.mp hz).1

/-- The first positive lower-central term is the unique middle term. -/
theorem lowerCentralTerm_one_eq_frattini
    [Finite P] (hP : IsPGroup 2 P) (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y) (hlen : HasXiLengthTwo Y.subtype) :
    lowerCentralTerm P 1 = frattini P := by
  rw [lowerCentralTerm, Subgroup.top_lowerCentralSeries_one,
    (commutator_eq_frattini_and_frattini_eq_center
      hP hncomm hxi hlen).1]

/-- The next lower-central term is trivial. -/
theorem lowerCentralTerm_two_eq_bot
    [Finite P] (hP : IsPGroup 2 P) (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y) (hlen : HasXiLengthTwo Y.subtype) :
    lowerCentralTerm P 2 = ⊥ := by
  simpa [lowerCentralTerm] using
    lowerCentralSeries_two_eq_bot hP hncomm hxi hlen

/-- Exact square-layer equality consumed by the lower-central square map. -/
theorem agemo_one_eq_lowerCentralTerm_one
    [Finite P] (hP : IsPGroup 2 P) (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y) (hlen : HasXiLengthTwo Y.subtype) :
    Agemo P 2 1 = lowerCentralTerm P 1 := by
  rw [agemo_one_eq_frattini hP hncomm hxi hlen,
    lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen]

end OddOrder.Higman.Suzuki2Groups
