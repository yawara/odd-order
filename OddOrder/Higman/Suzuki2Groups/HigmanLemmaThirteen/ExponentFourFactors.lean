/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedLengths
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.LengthTwoModels
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Assembly

/-!
# Higman's Lemma 13: the exponent-four factors

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

This leaf begins the classification of the two restricted length-three
factors in the branch where `Φ(P)` has exponent four.  The first step is to
exclude an abelian factor.  A factor covered by the ambient top would then
be maximal normal invariant abelian, so Lemma 9 bounds its exponent by four;
the homocyclic Agemo classification is incompatible with restricted
`ξ`-length three at that exponent.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups

universe uA uP

/-- A commutative finite `2`-group of exponent at most four cannot have
`ξ`-length three under an actor transitive on involutions.

The homocyclic classification makes every invariant subgroup an Agemo
layer.  Since the second Agemo layer is trivial, every nontrivial proper
invariant subgroup is the first Agemo layer, contradicting the two distinct
middle terms required by `HasXiLengthThree`. -/
theorem not_hasXiLengthThree_of_isMulCommutative_of_pow_four
    {A : Type uA} [Group A] [Finite A]
    {Y : Subgroup (MulAut A)}
    (hA : IsPGroup 2 A)
    (htrans : ActsTransitivelyOnInvolutions Y)
    (hcomm : IsMulCommutative A)
    (hfour : ∀ a : A, a ^ 4 = 1) :
    ¬ HasXiLengthThree Y.subtype := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hcomm.is_comm.comm }
  intro hlen
  obtain ⟨ι, hι, e, _he, _hε, classify⟩ :=
    exists_homocyclic_and_invariant_eq_agemo
      hA Y.subtype htrans
  letI : Fintype ι := hι
  have hAgemoTwo : Agemo A 2 2 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := mem_agemo_iff_of_comm.mp hx
    simpa using hfour y
  have middle_index_eq_one :
      ∀ (K : NormalInvariantSubgroup Y.subtype),
        K ≠ normalInvariantBot Y.subtype →
        K ≠ normalInvariantTop Y.subtype →
        ∀ s : ℕ, K.1 = Agemo A 2 s → s = 1 := by
    intro K hKbot hKtop s hKs
    have hKvalNeBot : K.1 ≠ (⊥ : Subgroup A) := by
      intro h
      apply hKbot
      apply Subtype.ext
      exact h
    have hKvalNeTop : K.1 ≠ (⊤ : Subgroup A) := by
      intro h
      apply hKtop
      apply Subtype.ext
      exact h
    have hs0 : s ≠ 0 := by
      intro hs
      subst s
      apply hKvalNeTop
      simpa [agemo_zero_eq_top] using hKs
    have hslt : s < 2 := by
      by_contra hnot
      have htwo : 2 ≤ s := by omega
      apply hKvalNeBot
      rw [hKs, eq_bot_iff]
      exact (Agemo.anti htwo).trans (le_of_eq hAgemoTwo)
    omega
  obtain ⟨U, V, hbotU, hUV, hVtop⟩ := hlen.exists_chain
  obtain ⟨s, _hs, hUs⟩ := classify U.1 U.2.2
  obtain ⟨t, _ht, hVt⟩ := classify V.1 V.2.2
  have hs : s = 1 := middle_index_eq_one U hbotU.ne'
    (hUV.trans hVtop).ne s hUs
  have ht : t = 1 := middle_index_eq_one V (hbotU.trans hUV).ne'
    hVtop.ne t hVt
  apply hUV.ne
  apply Subtype.ext
  rw [hUs, hVt, hs, ht]

/-- A normal invariant restricted length-three subgroup covered by the
ambient top is noncommutative under Higman's standing hypotheses.

If it were commutative, the top cover would make it maximal among normal
actor-invariant abelian subgroups.  Lemma 9 would give exponent four, in
contradiction with the preceding Agemo-length obstruction. -/
theorem restricted_lengthThree_not_isMulCommutative_of_covBy_top
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hStop : NormalInvariantCover Y.subtype S ⊤)
    (hlenS : HasXiLengthThree hSinv.restrict.range.subtype) :
    ¬ IsMulCommutative S := by
  intro hcommS
  let hSmax : IsMaximalNormalInvariantAbelian Y.subtype S :=
    { isNormalInvariant := hStop.left
      isMulCommutative := hcommS
      maximal := by
        intro B hB hBcomm hSB
        rcases hStop.eq_left_or_eq_right hB hSB le_top with hBS | hBtop
        · exact hBS
        · exfalso
          apply hncomm
          refine IsMulCommutative.of_comm fun x y => ?_
          have hx : x ∈ B := by
            rw [hBtop]
            exact Subgroup.mem_top x
          have hy : y ∈ B := by
            rw [hBtop]
            exact Subgroup.mem_top y
          exact congrArg Subtype.val
            (hBcomm.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩) }
  have hinv : (involutions P).Nonempty := by
    obtain ⟨x, _, hx, _, _⟩ := hmulti
    exact ⟨x, hx⟩
  have hYodd : Odd (Nat.card Y) :=
    actor_card_odd_of_primeSupport hP hinv hprime
  have hSfour : ∀ s : S, s ^ 4 = 1 :=
    (higmanLemmaNine_of_transitive hP Y hxi.cyclic hxi.transitive
      hYodd hmulti hncomm S hSmax).1
  have hxiS : IsXiActor hSinv.restrict.range :=
    restricted_range_isXiActor hxi hSinv
  exact (not_hasXiLengthThree_of_isMulCommutative_of_pow_four
    (hP.to_subgroup S) hxiS.transitive hcommS hSfour) hlenS

/-- **Higman Lemma 13 (p. 92), initial classification of the two
exponent-four factors.**

The two complementary Frattini preimages are noncommutative Suzuki
`2`-groups of restricted `ξ`-length three, so Higman's Lemma 12 classifies
each as type B, C, or D.  The ambient meet and join data are retained for the
subsequent refinement to the source's type-B/type-C cases and its mixed
commutator contradiction. -/
theorem exists_two_classified_xiLengthThree_frattini_preimages_of_exponent_four
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    ∃ (X Z : Subgroup P)
        (hXinv : IsAInvariant Y.subtype X)
        (hZinv : IsAInvariant Y.subtype Z),
      X.Normal ∧ HasXiLengthThree hXinv.restrict.range.subtype ∧
        ¬ IsMulCommutative X ∧
        (IsTypeB.{uP, 0} X ∨ IsTypeC.{uP, 0} X ∨ IsTypeD.{uP, 0} X) ∧
        Z.Normal ∧ HasXiLengthThree hZinv.restrict.range.subtype ∧
        ¬ IsMulCommutative Z ∧
        (IsTypeB.{uP, 0} Z ∨ IsTypeC.{uP, 0} Z ∨ IsTypeD.{uP, 0} Z) ∧
        frattini P < X ∧ X < ⊤ ∧
        frattini P < Z ∧ Z < ⊤ ∧
        X ⊓ Z = frattini P ∧ X ⊔ Z = ⊤ := by
  obtain ⟨X, Z, hXinv, hZinv, hXnormal, hlenX,
      hZnormal, hlenZ, hPhiX, hXtop, hPhiZ, hZtop,
      hXZinf, hXZsup⟩ :=
    exists_two_xiLengthThree_frattini_preimages_of_exponent_four
      hP hncomm hmulti hxi hlen hprime hPhiComm hfour hexists
  let phiTerm := frattiniNormalInvariant Y.subtype
  let xTerm : NormalInvariantSubgroup Y.subtype :=
    ⟨X, ⟨hXnormal, hXinv⟩⟩
  let zTerm : NormalInvariantSubgroup Y.subtype :=
    ⟨Z, ⟨hZnormal, hZinv⟩⟩
  have hLower := frattiniSquare_composition_series_of_exponent_four
    hP hxi hPhiComm hfour hexists
  have hXcovers := hlen.covers_of_chain
    hLower.1.lt hLower.2.lt
      (show phiTerm < xTerm from hPhiX)
      (show xTerm < normalInvariantTop Y.subtype from hXtop)
  have hZcovers := hlen.covers_of_chain
    hLower.1.lt hLower.2.lt
      (show phiTerm < zTerm from hPhiZ)
      (show zTerm < normalInvariantTop Y.subtype from hZtop)
  let hXTopCover : NormalInvariantCover Y.subtype X ⊤ :=
    { left := xTerm.2
      right := (normalInvariantTop Y.subtype).2
      covBy := hXcovers.2.2.2 }
  let hZTopCover : NormalInvariantCover Y.subtype Z ⊤ :=
    { left := zTerm.2
      right := (normalInvariantTop Y.subtype).2
      covBy := hZcovers.2.2.2 }
  have hXncomm : ¬ IsMulCommutative X :=
    restricted_lengthThree_not_isMulCommutative_of_covBy_top
      hP hncomm hmulti hxi hprime hXinv hXTopCover hlenX
  have hZncomm : ¬ IsMulCommutative Z :=
    restricted_lengthThree_not_isMulCommutative_of_covBy_top
      hP hncomm hmulti hxi hprime hZinv hZTopCover hlenZ
  have classify :
      ∀ (S : Subgroup P) (hSinv : IsAInvariant Y.subtype S),
        frattini P < S →
        HasXiLengthThree hSinv.restrict.range.subtype →
        ¬ IsMulCommutative S →
        IsTypeB.{uP, 0} S ∨ IsTypeC.{uP, 0} S ∨ IsTypeD.{uP, 0} S := by
    intro S hSinv hPhiS hlenS hncommS
    have hSneBot : S ≠ (⊥ : Subgroup P) :=
      ne_of_gt (lt_of_le_of_lt bot_le hPhiS)
    have hinvS : involutions P ⊆ S :=
      involutions_subset_of_nontrivial_invariant
        hP Y hxi.transitive hSinv hSneBot
    have hxiS : IsXiActor hSinv.restrict.range :=
      restricted_range_isXiActor hxi hSinv
    have hmultiS : ∃ x y : S,
        x ∈ involutions S ∧ y ∈ involutions S ∧ x ≠ y :=
      exists_distinct_involutions_subgroup_of_subset hinvS hmulti
    have hprimeS : ∀ p : ℕ, p.Prime →
        p ∣ Nat.card hSinv.restrict.range →
          p ∣ (involutions S).ncard :=
      restricted_range_primeSupport hSinv hinvS hprime
    exact higmanLemmaTwelve (hP.to_subgroup S) hncommS hmultiS
      hxiS hlenS hprimeS
  have hXclass := classify X hXinv hPhiX hlenX hXncomm
  have hZclass := classify Z hZinv hPhiZ hlenZ hZncomm
  exact ⟨X, Z, hXinv, hZinv, hXnormal, hlenX, hXncomm, hXclass,
    hZnormal, hlenZ, hZncomm, hZclass, hPhiX, hXtop, hPhiZ, hZtop,
    hXZinf, hXZsup⟩

end OddOrder.Higman.Suzuki2Groups
