/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedLengths

/-!
# Higman's Lemma 13: pairwise joins in the exponent-two branch

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

In the exponent-two branch the three lifted factors have `ξ`-length two.
Every pairwise join has one further composition step and is therefore a
`ξ`-length-three group to which Higman's Lemma 12 applies.

The no-long-chain direction requires care. A nontrivial normal invariant
subgroup of the restricted join contains every ambient involution. Since
`Φ(P)` has exponent two, its ambient image contains `Φ(P)` and hence the
ambient commutator subgroup. It is therefore ambient normal as well as
actor-invariant. A four-step restricted chain would consequently lift to a
five-step ambient chain, contradicting exact ambient `ξ`-length four.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

section /- Higman Lemma 13 (p. 93) -/

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

variable {P : Type uP} [Group P]

/-- **Higman Lemma 13 (p. 93), pairwise-join length.**

An invariant interval `⊥ < Φ(P) < R < S < ⊤` in an exponent-two
`ξ`-length-four group makes the restricted actor on `S` have exact
`ξ`-length three. -/
theorem restricted_range_hasXiLengthThree_of_two_step_exponent_two
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (htwo : ∀ z : frattini P, z ^ 2 = 1)
    {R S : Subgroup P}
    (hRinv : IsAInvariant Y.subtype R)
    (hSinv : IsAInvariant Y.subtype S)
    (hbotPhi : (⊥ : Subgroup P) < frattini P)
    (hPhiR : frattini P < R)
    (hRS : R < S)
    (hStop : S < (⊤ : Subgroup P)) :
    HasXiLengthThree hSinv.restrict.range.subtype := by
  let ract := hSinv.restrict.range.subtype
  let phiS : Subgroup S := (frattini P).subgroupOf S
  let rS : Subgroup S := R.subgroupOf S
  have hPhiS : frattini P ≤ S := hPhiR.le.trans hRS.le
  have hRleS : R ≤ S := hRS.le
  have hPhiMap : phiS.map S.subtype = frattini P :=
    Subgroup.map_subgroupOf_eq_of_le hPhiS
  have hRMap : rS.map S.subtype = R :=
    Subgroup.map_subgroupOf_eq_of_le hRleS
  have hPhiNormal : phiS.Normal :=
    (inferInstance : (frattini P).Normal).subgroupOf S
  have hRNormalAmbient : R.Normal :=
    Subgroup.Normal.of_commutator_le P
      ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        hPhiR.le)
  have hRNormal : rS.Normal := hRNormalAmbient.subgroupOf S
  have hPhiY : IsAInvariant hSinv.restrict phiS :=
    hSinv.subgroupOf (IsAInvariant.of_characteristic Y.subtype)
  have hRY : IsAInvariant hSinv.restrict rS :=
    hSinv.subgroupOf hRinv
  have hPhiRange : IsAInvariant ract phiS :=
    (isAInvariant_range_subtype_iff hSinv.restrict phiS).2 hPhiY
  have hRRange : IsAInvariant ract rS :=
    (isAInvariant_range_subtype_iff hSinv.restrict rS).2 hRY
  let phiTerm : NormalInvariantSubgroup ract :=
    ⟨phiS, ⟨hPhiNormal, hPhiRange⟩⟩
  let rTerm : NormalInvariantSubgroup ract :=
    ⟨rS, ⟨hRNormal, hRRange⟩⟩
  have hbotPhiTerm : normalInvariantBot ract < phiTerm := by
    change (⊥ : Subgroup S) < phiS
    rw [← Subgroup.map_lt_map_iff_of_injective S.subtype_injective]
    simpa [hPhiMap] using hbotPhi
  have hPhiRTerm : phiTerm < rTerm := by
    change phiS < rS
    rw [← Subgroup.map_lt_map_iff_of_injective S.subtype_injective]
    simpa [hPhiMap, hRMap] using hPhiR
  have hRTopTerm : rTerm < normalInvariantTop ract := by
    change rS < (⊤ : Subgroup S)
    rw [← Subgroup.map_lt_map_iff_of_injective S.subtype_injective]
    rw [hRMap]
    simpa [← MonoidHom.range_eq_map] using hRS
  refine ⟨phiTerm, rTerm, hbotPhiTerm, hPhiRTerm, hRTopTerm, ?_⟩
  intro A B C D E hAB hBC hCD hDE
  have hbotAle : normalInvariantBot ract ≤ A := by
    change (⊥ : Subgroup S) ≤ A.1
    exact bot_le
  have hbotB : normalInvariantBot ract < B :=
    lt_of_le_of_lt hbotAle hAB
  have hbotC : normalInvariantBot ract < C := hbotB.trans hBC
  have hbotD : normalInvariantBot ract < D := hbotC.trans hCD
  have hbotE : normalInvariantBot ract < E := hbotD.trans hDE
  have lift_nontrivial :
      ∀ K : NormalInvariantSubgroup ract,
        K ≠ normalInvariantBot ract →
          ∃ L : NormalInvariantSubgroup Y.subtype,
            L.1 = K.1.map S.subtype ∧ frattini P ≤ L.1 := by
    intro K hKne
    have hKvalNeBot : K.1 ≠ (⊥ : Subgroup S) := by
      intro hKbot
      apply hKne
      apply Subtype.ext
      exact hKbot
    have hKmapNeBot : K.1.map S.subtype ≠ (⊥ : Subgroup P) := by
      intro hKmap
      apply hKvalNeBot
      exact (Subgroup.map_eq_bot_iff_of_injective
        K.1 S.subtype_injective).mp hKmap
    have hKY : IsAInvariant hSinv.restrict K.1 :=
      (isAInvariant_range_subtype_iff hSinv.restrict K.1).1 K.2.2
    have hKmapInv : IsAInvariant Y.subtype (K.1.map S.subtype) :=
      aInvariant_map_subtype_of_restrict hSinv hKY
    have hinvK : involutions P ⊆ K.1.map S.subtype :=
      involutions_subset_of_nontrivial_invariant
        hP Y hxi.transitive hKmapInv hKmapNeBot
    have hPhiK : frattini P ≤ K.1.map S.subtype := by
      intro z hz
      by_cases hz1 : z = 1
      · exact hz1 ▸ (K.1.map S.subtype).one_mem
      · apply hinvK
        exact ⟨congrArg Subtype.val (htwo ⟨z, hz⟩), hz1⟩
    have hKmapNormal : (K.1.map S.subtype).Normal :=
      Subgroup.Normal.of_commutator_le P
        ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
          hPhiK)
    exact
      ⟨⟨K.1.map S.subtype, ⟨hKmapNormal, hKmapInv⟩⟩, rfl, hPhiK⟩
  obtain ⟨B', hB', _hPhiB'⟩ :=
    lift_nontrivial B hbotB.ne'
  obtain ⟨C', hC', _hPhiC'⟩ :=
    lift_nontrivial C hbotC.ne'
  obtain ⟨D', hD', _hPhiD'⟩ :=
    lift_nontrivial D hbotD.ne'
  obtain ⟨E', hE', _hPhiE'⟩ :=
    lift_nontrivial E hbotE.ne'
  have hbotB' : normalInvariantBot Y.subtype < B' := by
    change (⊥ : Subgroup P) < B'.1
    rw [hB']
    have hbotBsub : (⊥ : Subgroup S) < B.1 := hbotB
    simpa using
      (Subgroup.map_lt_map_iff_of_injective
        S.subtype_injective).2 hbotBsub
  have hB'C' : B' < C' := by
    change B'.1 < C'.1
    rw [hB', hC']
    exact (Subgroup.map_lt_map_iff_of_injective
      S.subtype_injective).2 hBC
  have hC'D' : C' < D' := by
    change C'.1 < D'.1
    rw [hC', hD']
    exact (Subgroup.map_lt_map_iff_of_injective
      S.subtype_injective).2 hCD
  have hD'E' : D' < E' := by
    change D'.1 < E'.1
    rw [hD', hE']
    exact (Subgroup.map_lt_map_iff_of_injective
      S.subtype_injective).2 hDE
  have hE'top : E' < normalInvariantTop Y.subtype := by
    change E'.1 < (⊤ : Subgroup P)
    apply lt_of_le_of_lt ?_ hStop
    rw [hE']
    exact Subgroup.map_subtype_le E.1
  exact hlen.no_chain_of_length_five
    hbotB' hB'C' hC'D' hD'E' hE'top

end

end OddOrder.Higman.Suzuki2Groups
