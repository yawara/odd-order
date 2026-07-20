/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanXiLengthTwo
import OddOrder.Higman.Suzuki2Groups.HigmanMaximalNormalAbelian

/-!
# Higman's Lemma 12: the ξ-length-three reduction

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 12, pp. 89--92.

The opening of Lemma 12 assumes that the normal actor-invariant composition
length is three.  This leaf first records that hypothesis directly in the
poset of `NormalInvariantSubgroup`s: a chain with three strict inclusions
exists, while no chain with four strict inclusions exists.  The cover
relations in every such three-step chain are then derived rather than
included as data.

This leaf then identifies the lower term with the elementary-abelian
Frattini subgroup.  A subsequent leaf will split the two-step quotient.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP uX

variable {P : Type uP} [Group P]
variable {X : Type uX} [Group X]

/-- The source-faithful meaning of `ξ`-length three.

There is a chain with three strict inclusions between the bottom and top
normal actor-invariant subgroups, and there is no chain with four strict
inclusions. -/
def HasXiLengthThree (act : X →* MulAut P) : Prop :=
  ∃ A B : NormalInvariantSubgroup act,
    normalInvariantBot act < A ∧
      A < B ∧
        B < normalInvariantTop act ∧
          ∀ A B C D E : NormalInvariantSubgroup act,
            A < B → B < C → C < D → D < E → False

namespace HasXiLengthThree

variable {act : X →* MulAut P}

/-- A length-three action has a strict three-step chain. -/
theorem exists_chain (h : HasXiLengthThree act) :
    ∃ A B : NormalInvariantSubgroup act,
      normalInvariantBot act < A ∧
        A < B ∧ B < normalInvariantTop act := by
  rcases h with ⟨A, B, hbot, hAB, htop, _⟩
  exact ⟨A, B, hbot, hAB, htop⟩

/-- A length-three action has no chain with four strict inclusions. -/
theorem no_chain_of_length_four (h : HasXiLengthThree act)
    {A B C D E : NormalInvariantSubgroup act}
    (hAB : A < B) (hBC : B < C) (hCD : C < D) (hDE : D < E) :
    False := by
  rcases h with ⟨_, _, _, _, _, hlong⟩
  exact hlong A B C D E hAB hBC hCD hDE

/-- Every term distinct from the bottom lies strictly above it. -/
theorem bot_lt_of_ne_bot (_h : HasXiLengthThree act)
    {A : NormalInvariantSubgroup act}
    (hA : A ≠ normalInvariantBot act) : normalInvariantBot act < A := by
  apply lt_of_le_of_ne
  · change (⊥ : Subgroup P) ≤ A.1
    exact bot_le
  · exact hA.symm

/-- Every term distinct from the top lies strictly below it. -/
theorem lt_top_of_ne_top (_h : HasXiLengthThree act)
    {A : NormalInvariantSubgroup act}
    (hA : A ≠ normalInvariantTop act) : A < normalInvariantTop act := by
  apply lt_of_le_of_ne
  · change A.1 ≤ (⊤ : Subgroup P)
    exact le_top
  · exact hA

/-- Every strict three-step chain from bottom to top is a composition
series: all three inclusions are covers. -/
theorem covers_of_chain (h : HasXiLengthThree act)
    {A B : NormalInvariantSubgroup act}
    (hbot : normalInvariantBot act < A)
    (hAB : A < B)
    (htop : B < normalInvariantTop act) :
    normalInvariantBot act ⋖ A ∧
      A ⋖ B ∧ B ⋖ normalInvariantTop act := by
  have hbotCover : normalInvariantBot act ⋖ A := by
    by_contra hcov
    obtain ⟨C, hbotC, hCA⟩ := (not_covBy_iff hbot).mp hcov
    exact h.no_chain_of_length_four hbotC hCA hAB htop
  have hABCover : A ⋖ B := by
    by_contra hcov
    obtain ⟨C, hAC, hCB⟩ := (not_covBy_iff hAB).mp hcov
    exact h.no_chain_of_length_four hbot hAC hCB htop
  have htopCover : B ⋖ normalInvariantTop act := by
    by_contra hcov
    obtain ⟨C, hBC, hCtop⟩ := (not_covBy_iff htop).mp hcov
    exact h.no_chain_of_length_four hbot hAB hBC hCtop
  exact ⟨hbotCover, hABCover, htopCover⟩

/-- A length-three action admits an actual three-cover composition series. -/
theorem exists_composition_series (h : HasXiLengthThree act) :
    ∃ A B : NormalInvariantSubgroup act,
      normalInvariantBot act ⋖ A ∧
        A ⋖ B ∧ B ⋖ normalInvariantTop act := by
  obtain ⟨A, B, hbot, hAB, htop⟩ := h.exists_chain
  exact ⟨A, B, h.covers_of_chain hbot hAB htop⟩

/-- No proper lower interval contains three further strict steps. -/
theorem no_chain_of_length_three_below_proper
    (h : HasXiLengthThree act)
    {A B C D : NormalInvariantSubgroup act}
    (hAB : A < B) (hBC : B < C) (hCD : C < D)
    (hDtop : D < normalInvariantTop act) : False :=
  h.no_chain_of_length_four hAB hBC hCD hDtop

/-- No proper upper interval contains three preceding strict steps. -/
theorem no_chain_of_length_three_above_nonbottom
    (h : HasXiLengthThree act)
    {A B C D : NormalInvariantSubgroup act}
    (hbotA : normalInvariantBot act < A)
    (hAB : A < B) (hBC : B < C) (hCD : C < D) : False :=
  h.no_chain_of_length_four hbotA hAB hBC hCD

/-- Length three is incompatible with the length-two hypothesis on the same
normal actor-invariant poset. -/
theorem not_hasXiLengthTwo (h : HasXiLengthThree act) :
    ¬ HasXiLengthTwo act := by
  intro htwo
  obtain ⟨A, B, hbot, hAB, htop⟩ := h.exists_chain
  exact htwo.no_chain_of_length_three hbot hAB htop

end HasXiLengthThree

/-! ## The Frattini reduction -/

/-- **Higman Lemma 12 (p. 90), opening reduction.**

For a noncommutative finite `2`-group of `ξ`-length three, with Higman's
prime-supported cyclic actor, the Frattini subgroup is elementary abelian.
The prime-support input is precisely the standing normalization introduced
at the start of Higman §6: every prime dividing the chosen actor order also
divides the number `q - 1` of nonidentity involutions.

Lemma 9 first makes `Φ(P)` abelian.  If its own Frattini subgroup were
nontrivial, its ambient image would give two strict composition steps below
`Φ(P)`.  Length three would then force `P` to cover `Φ(P)`.  The cover
dichotomy and Lemmas 7--8 say respectively that `P` is abelian or that
`Φ(P)` has exponent two, contradicting that counter-assumption. -/
theorem frattini_isElementaryAbelian_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    OddOrder.GroupTheory.IsElementaryAbelian 2 ↥(frattini P) := by
  classical
  letI : Nontrivial P := by
    obtain ⟨x, y, _, _, hxy⟩ := hmulti
    exact ⟨⟨x, y, hxy⟩⟩
  have hinv : (involutions P).Nonempty := by
    obtain ⟨x, _, hx, _, _⟩ := hmulti
    exact ⟨x, hx⟩
  have hYodd : Odd (Nat.card Y) := by
    have hinvOdd := involutions_ncard_odd_of_isPGroup hP hinv
    exact Nat.not_even_iff_odd.mp fun hYeven =>
      hinvOdd.not_two_dvd_nat
        (hprime 2 Nat.prime_two (Even.two_dvd hYeven))
  have hPhiComm : IsMulCommutative (frattini P) :=
    frattini_isMulCommutative_of_transitive
      hP Y hxi.cyclic hxi.transitive hYodd hmulti hncomm
  have hPhiNeBot : frattini P ≠ ⊥ := by
    intro hPhiBot
    have hcommBot : _root_.commutator P = ⊥ :=
      le_bot_iff.mp ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        (le_of_eq hPhiBot))
    exact hncomm ((commutator_eq_bot_iff P).mp hcommBot)
  have hPhiNeTop : frattini P ≠ ⊤ := by
    obtain ⟨M, hM, _⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup P)).resolve_left
        bot_lt_top.ne
    exact fun htop => hM.1
      (le_antisymm le_top (htop ▸ frattini_le_coatom hM))
  letI : (frattini P).Normal := inferInstance
  letI : Nontrivial ↥(frattini P) :=
    (Subgroup.nontrivial_iff_ne_bot (frattini P)).mpr hPhiNeBot
  have hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  have htransPhi : ∀ x ∈ involutions ↥(frattini P),
      ∀ y ∈ involutions ↥(frattini P),
        ∃ g : Y, hPhiInv.restrict g x = y :=
    restricted_involutions_transitive Y.subtype hPhiInv (by
      intro x hx y hy
      obtain ⟨g, hg⟩ := hxi.transitive x hx y hy
      exact ⟨g, hg⟩)
  letI : CommGroup ↥(frattini P) :=
    { (inferInstance : Group ↥(frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  obtain ⟨ι, hι, _e, _he, _hε, classifyFull⟩ :=
    exists_homocyclic_and_invariant_eq_agemo
      (hP.to_subgroup (frattini P)) hPhiInv.restrict htransPhi
  letI : Fintype ι := hι
  have classify : ∀ U : Subgroup ↥(frattini P),
      IsAInvariant hPhiInv.restrict U →
        ∃ s : ℕ, U = Agemo ↥(frattini P) 2 s := by
    intro U hU
    obtain ⟨s, _hs, hsU⟩ := classifyFull U hU
    exact ⟨s, hsU⟩
  have hFratBot : frattini ↥(frattini P) = ⊥ := by
    by_contra hFratNeBot
    let B : Subgroup P :=
      NormalInvariantCover.ambientFrattini (frattini P)
    obtain ⟨hBInv, hBNormal, hBLe⟩ :=
      aInvariant_normal_map_of_characteristic
        hPhiInv (frattini ↥(frattini P))
    have hBNeBot : B ≠ ⊥ := by
      intro hBbot
      apply hFratNeBot
      apply (Subgroup.map_eq_bot_iff_of_injective
        (frattini ↥(frattini P)) (frattini P).subtype_injective).mp
      simpa [B, NormalInvariantCover.ambientFrattini] using hBbot
    have hFratNeTop : frattini ↥(frattini P) ≠ ⊤ := by
      obtain ⟨M, hM, _⟩ :=
        (IsCoatomic.eq_top_or_exists_le_coatom
          (⊥ : Subgroup ↥(frattini P))).resolve_left bot_lt_top.ne
      exact fun htop => hM.1
        (le_antisymm le_top (htop ▸ frattini_le_coatom hM))
    have hBNePhi : B ≠ frattini P := by
      intro hBPhi
      have hmaps :
          (frattini ↥(frattini P)).map (frattini P).subtype =
            (⊤ : Subgroup ↥(frattini P)).map (frattini P).subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
        simpa [B, NormalInvariantCover.ambientFrattini] using hBPhi
      exact hFratNeTop
        (Subgroup.map_injective (frattini P).subtype_injective hmaps)
    have hBltPhi : B < frattini P := lt_of_le_of_ne hBLe hBNePhi
    let b : NormalInvariantSubgroup Y.subtype :=
      ⟨B, ⟨hBNormal, hBInv⟩⟩
    let phi : NormalInvariantSubgroup Y.subtype :=
      ⟨frattini P, ⟨inferInstance, hPhiInv⟩⟩
    have hbotB : normalInvariantBot Y.subtype < b := by
      change (⊥ : Subgroup P) < B
      exact bot_lt_iff_ne_bot.mpr hBNeBot
    have hBPhi : b < phi := hBltPhi
    have hPhiTop : phi < normalInvariantTop Y.subtype := by
      change frattini P < (⊤ : Subgroup P)
      exact lt_top_iff_ne_top.mpr hPhiNeTop
    have hPhiCovTop : phi ⋖ normalInvariantTop Y.subtype :=
      (hlen.covers_of_chain hbotB hBPhi hPhiTop).2.2
    let hcover : NormalInvariantCover Y.subtype (frattini P) ⊤ :=
      { left := ⟨inferInstance, hPhiInv⟩
        right := ⟨inferInstance, IsAInvariant.top Y.subtype⟩
        covBy := by
          simpa [phi, normalInvariantTop] using hPhiCovTop }
    have hTopFrattini :
        NormalInvariantCover.ambientFrattini (⊤ : Subgroup P) =
          frattini P := by
      let e : (⊤ : Subgroup P) ≃* P := Subgroup.topEquiv
      have hfrattini :
          (frattini (⊤ : Subgroup P)).map e.toMonoidHom = frattini P := by
        apply le_antisymm
        · rw [Subgroup.map_le_iff_le_comap]
          exact frattini_le_comap_frattini_of_surjective e.surjective
        · have hback := frattini_le_comap_frattini_of_surjective
            (φ := e.symm.toMonoidHom) e.symm.surjective
          rwa [Subgroup.map_equiv_eq_comap_symm']
      have he : e.toMonoidHom = (⊤ : Subgroup P).subtype := by
        ext x
        rfl
      change (frattini (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype =
        frattini P
      rw [← he]
      exact hfrattini
    rcases hcover.commutator_map_eq_left_or_le_agemo_one
        hP classify hTopFrattini with hderived | hderived
    · have hExp : ∀ a : frattini P, a ^ 2 = 1 :=
        higmanLemmaEight_pow_two_eq_one_of_transitive
          hP Y hxi.cyclic hxi.transitive hYodd hmulti
            (frattini P) ⊤ hcover hPhiComm hderived
      have hEA : OddOrder.GroupTheory.IsElementaryAbelian 2 ↥(frattini P) :=
        ⟨hPhiComm.is_comm.comm, hExp⟩
      exact hFratNeBot
        ((OddOrder.BG.Ch1.S01.frattini_eq_bot_iff_isElementaryAbelian
          (hP.to_subgroup (frattini P))).mpr hEA)
    · have hTopComm : IsMulCommutative (⊤ : Subgroup P) :=
        higmanLemmaSeven_isMulCommutative_of_transitive
          hP Y hxi.cyclic hxi.transitive hmulti
            (frattini P) ⊤ hcover hPhiComm hTopFrattini hderived
      apply hncomm
      refine IsMulCommutative.of_comm fun x y => ?_
      exact congrArg Subtype.val
        (hTopComm.is_comm.comm
          (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup P))
          (⟨y, Subgroup.mem_top y⟩ : (⊤ : Subgroup P)))
  exact OddOrder.GroupTheory.IsPGroup.isElementaryAbelian_of_frattini_eq_bot
    (hP.to_subgroup (frattini P)) hFratBot

end OddOrder.Higman.Suzuki2Groups
