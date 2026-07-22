/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.LengthThreeReduction

/-!
# Higman's Lemma 13: the ξ-length-four reduction

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, pp. 92--93.

Higman's final lemma says that a Suzuki `2`-group has `ξ`-length at most
three.  Its two hard cases assume exact length four and split according as
the Frattini subgroup has exponent two or contains an element of order four.

This opening leaf records the exact-length-four poset interface and the
Frattini exponent split at source strength.  The length hypotheses are
stated in the concrete poset of normal actor-invariant subgroups, as in the
Lemma 11 and Lemma 12 developments.  The exponent split is derived from
Lemma 9's constructed maximal normal invariant abelian subgroup; it is not
supplied as new data.  The separate descent from an arbitrary longer chain
to an ambient-normal exact-length-four subgroup is not asserted here.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group

universe uP uX

variable {P : Type uP} [Group P]
variable {X : Type uX} [Group X]

/-- There is a chain of four strict inclusions in the normal
actor-invariant subgroup poset.  This is the negation target of Higman's
Lemma 13. -/
def HasXiLengthAtLeastFour (act : X →* MulAut P) : Prop :=
  ∃ A B C : NormalInvariantSubgroup act,
    normalInvariantBot act < A ∧
      A < B ∧
        B < C ∧ C < normalInvariantTop act

namespace HasXiLengthAtLeastFour

variable {act : X →* MulAut P}

/-- A chain witnessing `ξ`-length at least four. -/
theorem exists_chain (h : HasXiLengthAtLeastFour act) :
    ∃ A B C : NormalInvariantSubgroup act,
      normalInvariantBot act < A ∧
        A < B ∧ B < C ∧ C < normalInvariantTop act :=
  h

/-- A length-three action cannot contain a four-step chain. -/
theorem not_hasXiLengthThree (h : HasXiLengthAtLeastFour act) :
    ¬ HasXiLengthThree act := by
  intro hthree
  obtain ⟨A, B, C, hbot, hAB, hBC, htop⟩ := h.exists_chain
  exact hthree.no_chain_of_length_four hbot hAB hBC htop

/-- A length-two action cannot contain a four-step chain. -/
theorem not_hasXiLengthTwo (h : HasXiLengthAtLeastFour act) :
    ¬ HasXiLengthTwo act := by
  intro htwo
  obtain ⟨A, B, _, hbot, hAB, hBC, _⟩ := h.exists_chain
  exact htwo.no_chain_of_length_three hbot hAB hBC

end HasXiLengthAtLeastFour

/-- The source-faithful meaning of exact `ξ`-length four.

There is a chain with four strict inclusions between the bottom and top
normal actor-invariant subgroups, and there is no chain with five strict
inclusions. -/
def HasXiLengthFour (act : X →* MulAut P) : Prop :=
  HasXiLengthAtLeastFour act ∧
    ∀ A B C D E F : NormalInvariantSubgroup act,
      A < B → B < C → C < D → D < E → E < F → False

namespace HasXiLengthFour

variable {act : X →* MulAut P}

/-- Exact length four implies length at least four. -/
theorem atLeastFour (h : HasXiLengthFour act) :
    HasXiLengthAtLeastFour act :=
  h.1

/-- A length-four action has a strict four-step chain. -/
theorem exists_chain (h : HasXiLengthFour act) :
    ∃ A B C : NormalInvariantSubgroup act,
      normalInvariantBot act < A ∧
        A < B ∧ B < C ∧ C < normalInvariantTop act :=
  h.atLeastFour.exists_chain

/-- A length-four action has no chain with five strict inclusions. -/
theorem no_chain_of_length_five (h : HasXiLengthFour act)
    {A B C D E F : NormalInvariantSubgroup act}
    (hAB : A < B) (hBC : B < C) (hCD : C < D)
    (hDE : D < E) (hEF : E < F) : False :=
  h.2 A B C D E F hAB hBC hCD hDE hEF

/-- Every strict four-step chain from bottom to top is a composition
series: all four inclusions are covers. -/
theorem covers_of_chain (h : HasXiLengthFour act)
    {A B C : NormalInvariantSubgroup act}
    (hbot : normalInvariantBot act < A)
    (hAB : A < B) (hBC : B < C)
    (htop : C < normalInvariantTop act) :
    normalInvariantBot act ⋖ A ∧
      A ⋖ B ∧ B ⋖ C ∧ C ⋖ normalInvariantTop act := by
  have hbotCover : normalInvariantBot act ⋖ A := by
    by_contra hcov
    obtain ⟨D, hbotD, hDA⟩ := (not_covBy_iff hbot).mp hcov
    exact h.no_chain_of_length_five hbotD hDA hAB hBC htop
  have hABCover : A ⋖ B := by
    by_contra hcov
    obtain ⟨D, hAD, hDB⟩ := (not_covBy_iff hAB).mp hcov
    exact h.no_chain_of_length_five hbot hAD hDB hBC htop
  have hBCCover : B ⋖ C := by
    by_contra hcov
    obtain ⟨D, hBD, hDC⟩ := (not_covBy_iff hBC).mp hcov
    exact h.no_chain_of_length_five hbot hAB hBD hDC htop
  have htopCover : C ⋖ normalInvariantTop act := by
    by_contra hcov
    obtain ⟨D, hCD, hDtop⟩ := (not_covBy_iff htop).mp hcov
    exact h.no_chain_of_length_five hbot hAB hBC hCD hDtop
  exact ⟨hbotCover, hABCover, hBCCover, htopCover⟩

/-- A length-four action admits an actual four-cover composition series. -/
theorem exists_composition_series (h : HasXiLengthFour act) :
    ∃ A B C : NormalInvariantSubgroup act,
      normalInvariantBot act ⋖ A ∧
        A ⋖ B ∧ B ⋖ C ∧ C ⋖ normalInvariantTop act := by
  obtain ⟨A, B, C, hbot, hAB, hBC, htop⟩ := h.exists_chain
  exact ⟨A, B, C, h.covers_of_chain hbot hAB hBC htop⟩

/-- Exact lengths four and three are incompatible. -/
theorem not_hasXiLengthThree (h : HasXiLengthFour act) :
    ¬ HasXiLengthThree act :=
  h.atLeastFour.not_hasXiLengthThree

/-- Exact lengths four and two are incompatible. -/
theorem not_hasXiLengthTwo (h : HasXiLengthFour act) :
    ¬ HasXiLengthTwo act :=
  h.atLeastFour.not_hasXiLengthTwo

end HasXiLengthFour

/-! ## The Lemma 9 exponent split -/

/-- Higman's prime-support normalization forces the cyclic actor to have odd
order.  The proof uses only the existence of an involution, not a
`ξ`-length assumption. -/
theorem actor_card_odd_of_primeSupport
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hinv : (involutions P).Nonempty)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    Odd (Nat.card Y) := by
  have hinvOdd := involutions_ncard_odd_of_isPGroup hP hinv
  exact Nat.not_even_iff_odd.mp fun hYeven =>
    hinvOdd.not_two_dvd_nat
      (hprime 2 Nat.prime_two (Even.two_dvd hYeven))

/-- Under Higman's prime-support normalization, Lemma 9 makes the Frattini
subgroup commutative. -/
theorem frattini_isMulCommutative_of_primeSupport
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    IsMulCommutative (frattini P) := by
  have hinv : (involutions P).Nonempty := by
    obtain ⟨x, _, hx, _, _⟩ := hmulti
    exact ⟨x, hx⟩
  exact frattini_isMulCommutative_of_transitive
    hP Y hxi.cyclic hxi.transitive
      (actor_card_odd_of_primeSupport hP hinv hprime)
      hmulti hncomm

/-- **Higman Lemma 13 (p. 92), opening exponent reduction.**

Under the standing prime-supported `ξ`-actor assumptions, every element of
the Frattini subgroup has fourth power one.  This is inherited from the
maximal normal invariant abelian subgroup constructed for Lemma 9. -/
theorem frattini_pow_four_eq_one_of_primeSupport
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    ∀ z : frattini P, z ^ 4 = 1 := by
  have hinv : (involutions P).Nonempty := by
    obtain ⟨x, _, hx, _, _⟩ := hmulti
    exact ⟨x, hx⟩
  have hYodd : Odd (Nat.card Y) :=
    actor_card_odd_of_primeSupport hP hinv hprime
  obtain ⟨A, hAmax⟩ :=
    exists_maximalNormalInvariantAbelian Y.subtype
  obtain ⟨hA4, hPhiA⟩ :=
    higmanLemmaNine_of_transitive hP Y hxi.cyclic hxi.transitive
      hYodd hmulti hncomm A hAmax
  intro z
  apply Subtype.ext
  change (z : P) ^ 4 = 1
  exact congrArg Subtype.val (hA4 ⟨z, hPhiA z.property⟩)

/-- **Higman Lemma 13 (p. 92), Frattini case split.**

Either the Frattini subgroup has exponent two, or it contains an element
whose square is nontrivial and whose fourth power is one.  These are the two
cases treated on pp. 92--93. -/
theorem frattini_exponent_two_or_four_of_primeSupport
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    (∀ z : frattini P, z ^ 2 = 1) ∨
      ((∀ z : frattini P, z ^ 4 = 1) ∧
        ∃ z : frattini P, z ^ 2 ≠ 1) := by
  classical
  have hfour :=
    frattini_pow_four_eq_one_of_primeSupport
      hP hncomm hmulti hxi hprime
  by_cases htwo : ∀ z : frattini P, z ^ 2 = 1
  · exact Or.inl htwo
  · simp only [not_forall] at htwo
    obtain ⟨z, hz⟩ := htwo
    exact Or.inr ⟨hfour, z, hz⟩

end OddOrder.Higman.Suzuki2Groups
