/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaEleven.TypeAConclusion
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.Assembly
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.LengthBound

/-!
# Higman's classification of Suzuki 2-groups

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Theorem 1, pp. 79–82.

Higman's main theorem classifies every Suzuki `2`-group as one of the four
families `A`, `B`, `C`, or `D`.  Lemmas 11 and 12 classify the cases of
`ξ`-length two and three, respectively, while Lemma 13 excludes length at
least four.  A noncommutative finite `2`-group has the two-step normal
actor-invariant chain

`1 < Z(P) < P`,

so the existence or nonexistence of a three-step chain completes the
length dichotomy.  Higman closes the proof on p. 93 with “Thus Lemma 13 is
proved, and with it, the main theorem.”
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups

universe uP

/-- **Higman, Suzuki 2-groups, Theorem 1 (pp. 79–82; completed on p. 93).**

Every noncommutative finite `2`-group with more than one involution and a
cyclic automorphism group transitive on its involutions is isomorphic to a
group of type `A`, `B`, `C`, or `D`.

This is the source-facing form of Higman's main theorem: transitivity, not
regularity, is assumed.  The actor is first replaced by the prime-supported
cyclic actor used in Lemmas 11–13. -/
theorem higmanClassification
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (A : Subgroup (MulAut P))
    (hcyc : IsCyclic ↥A)
    (htrans : ActsTransitivelyOnInvolutions A) :
    IsTypeA.{uP, 0} P ∨ IsTypeB.{uP, 0} P ∨
      IsTypeC.{uP, 0} P ∨ IsTypeD.{uP, 0} P := by
  classical
  let : Nontrivial P := by
    obtain ⟨x, y, _, _, hxy⟩ := hmulti
    exact ⟨⟨x, y, hxy⟩⟩
  have hinv : (involutions P).Nonempty := by
    obtain ⟨x, _, hx, _, _⟩ := hmulti
    exact ⟨x, hx⟩
  obtain ⟨B, _hBA, hBcyc, hBtrans, _hcard, hprime⟩ :=
    exists_primeSupported_cyclic_actor A hcyc htrans hinv
  have hxi : IsXiActor B := ⟨hBcyc, hBtrans⟩
  have hnoFour : ¬ HasXiLengthAtLeastFour B.subtype :=
    higmanLemmaThirteen hP hncomm hmulti hxi hprime
  let centerTerm : NormalInvariantSubgroup B.subtype :=
    centerNormalInvariant B.subtype
  have hcenterNeBot : Subgroup.center P ≠ (⊥ : Subgroup P) := by
    let : Nontrivial ↥(Subgroup.center P) := hP.center_nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot (Subgroup.center P)).mp inferInstance
  have hcenterNeTop : Subgroup.center P ≠ (⊤ : Subgroup P) := by
    intro hcenter
    apply hncomm
    exact (Subgroup.center_eq_top_iff.mp hcenter)
  have hbotCenter :
      normalInvariantBot B.subtype < centerTerm := by
    change (⊥ : Subgroup P) < Subgroup.center P
    exact bot_lt_iff_ne_bot.mpr hcenterNeBot
  have hcenterTop :
      centerTerm < normalInvariantTop B.subtype := by
    change Subgroup.center P < (⊤ : Subgroup P)
    exact lt_top_iff_ne_top.mpr hcenterNeTop
  have hbotLe (U : NormalInvariantSubgroup B.subtype) :
      normalInvariantBot B.subtype ≤ U := by
    change (⊥ : Subgroup P) ≤ U.1
    exact bot_le
  have hleTop (U : NormalInvariantSubgroup B.subtype) :
      U ≤ normalInvariantTop B.subtype := by
    change U.1 ≤ (⊤ : Subgroup P)
    exact le_top
  by_cases hthree :
      ∃ U V : NormalInvariantSubgroup B.subtype,
        normalInvariantBot B.subtype < U ∧
          U < V ∧ V < normalInvariantTop B.subtype
  · obtain ⟨U, V, hbotU, hUV, hVtop⟩ := hthree
    have hlen : HasXiLengthThree B.subtype := by
      refine ⟨U, V, hbotU, hUV, hVtop, ?_⟩
      intro C D E F G hCD hDE hEF hFG
      apply hnoFour
      exact ⟨D, E, F, (hbotLe C).trans_lt hCD, hDE, hEF,
        hFG.trans_le (hleTop G)⟩
    exact Or.inr (higmanLemmaTwelve hP hncomm hmulti hxi hlen hprime)
  · have hlen : HasXiLengthTwo B.subtype := by
      refine ⟨centerTerm, hbotCenter, hcenterTop, ?_⟩
      intro C D E F hCD hDE hEF
      apply hthree
      exact ⟨D, E, (hbotLe C).trans_lt hCD, hDE,
        hEF.trans_le (hleTop F)⟩
    exact Or.inl (higmanLemmaEleven hP hncomm hmulti hxi hlen hprime)

/-- Higman's classification in the bundled compatibility form used by
Peterfalvi consumers.

`IsSuzuki2Group` packages a cyclic actor acting regularly on the
involutions.  Regularity supplies the transitivity required by the
source-facing theorem above. -/
theorem higmanClassification_of_isSuzuki2Group
    {P : Type uP} [Group P] [Finite P]
    (hP : IsSuzuki2Group P) :
    IsTypeA.{uP, 0} P ∨ IsTypeB.{uP, 0} P ∨
      IsTypeC.{uP, 0} P ∨ IsTypeD.{uP, 0} P := by
  obtain ⟨h2, hncomm, hmulti, A, hcyc, hregular⟩ := hP
  exact higmanClassification h2 hncomm hmulti A hcyc hregular.transitive

/-- **The two possible orders of a Suzuki `2`-group** (Higman's classification,
as Peterfalvi uses it in Part II, Ch. III §1: "`S` is non-abelian of order `q²`"
versus "of order `q³`", p. 117).

Every one of the four types is the quadratic extension of an anisotropic
quadratic map, so its elements of order dividing `2` are exactly the kernel of
the extension.  Type A has both coordinates equal to the field, giving
`|P| = |Ω₁(P)|²`; types B, C and D have a two-dimensional quotient coordinate,
giving `|P| = |Ω₁(P)|³`. -/
theorem natCard_eq_sq_or_cube_of_isSuzuki2Group
    {P : Type uP} [Group P] [Finite P] (hP : IsSuzuki2Group P) :
    Nat.card P = Nat.card {x : P // x ^ 2 = 1} ^ 2 ∨
      Nat.card P = Nat.card {x : P // x ^ 2 = 1} ^ 3 := by
  rcases higmanClassification_of_isSuzuki2Group hP with hA | hB | hC | hD
  · obtain ⟨data⟩ := hA
    obtain ⟨hcard, hsq⟩ := data.natCard_and_natCard_sq_eq_one
    exact Or.inl (by rw [hcard, hsq, sq])
  · obtain ⟨data⟩ := hB
    obtain ⟨hcard, hsq⟩ := data.natCard_and_natCard_sq_eq_one
    refine Or.inr ?_
    rw [hcard, hsq, Nat.card_prod]
    ring
  · obtain ⟨data⟩ := hC
    obtain ⟨hcard, hsq⟩ := data.natCard_and_natCard_sq_eq_one
    refine Or.inr ?_
    rw [hcard, hsq, Nat.card_prod]
    ring
  · obtain ⟨data⟩ := hD
    obtain ⟨hcard, hsq⟩ := data.natCard_and_natCard_sq_eq_one
    refine Or.inr ?_
    rw [hcard, hsq, Nat.card_prod]
    ring

end OddOrder.Higman.Suzuki2Groups
