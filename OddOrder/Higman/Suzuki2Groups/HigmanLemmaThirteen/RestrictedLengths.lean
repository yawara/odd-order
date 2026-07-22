/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniPreimages

/-!
# Higman's Lemma 13: lengths of the lifted invariant factors

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, pp. 92–93.

This leaf determines the exact `ξ`-lengths of the normal invariant
subgroups lifted from the Frattini quotient.  The two Frattini-exponent
branches require different arguments; in particular, an exponent-four
restricted subgroup is not lifted to an ambient normal subgroup without a
separate proof.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

variable {P : Type uP} [Group P]

/-- In the exponent-two branch, a normal invariant Frattini cover has
restricted `ξ`-length two.

Every nontrivial normal invariant subgroup of the cover contains all
ambient involutions.  Since every element of `Φ(P)` is either `1` or an
involution, its image in `P` contains `Φ(P)` and is therefore ambient
normal.  The cover property then leaves only `Φ(P)` and the whole cover. -/
theorem restricted_range_hasXiLengthTwo_of_frattini_cover_exponent_two
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (htwo : ∀ z : frattini P, z ^ 2 = 1)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : NormalInvariantCover Y.subtype (frattini P) S) :
    HasXiLengthTwo hSinv.restrict.range.subtype := by
  let ract := hSinv.restrict.range.subtype
  have hPhiNeBot : frattini P ≠ (⊥ : Subgroup P) :=
    frattini_ne_bot_of_not_isMulCommutative hP hncomm
  let phiS : Subgroup S := (frattini P).subgroupOf S
  have hphiSNormal : phiS.Normal :=
    (inferInstance : (frattini P).Normal).subgroupOf S
  have hphiY : IsAInvariant hSinv.restrict phiS :=
    hSinv.subgroupOf (IsAInvariant.of_characteristic Y.subtype)
  have hphiRange : IsAInvariant ract phiS :=
    (isAInvariant_range_subtype_iff hSinv.restrict phiS).2 hphiY
  let phiTerm : NormalInvariantSubgroup ract :=
    ⟨phiS, ⟨hphiSNormal, hphiRange⟩⟩
  have hbotPhi : normalInvariantBot ract < phiTerm := by
    change (⊥ : Subgroup S) < phiS
    rw [← Subgroup.map_lt_map_iff_of_injective S.subtype_injective]
    simp only [Subgroup.map_bot]
    rw [show phiS.map S.subtype = frattini P by
      exact Subgroup.map_subgroupOf_eq_of_le hPhiS.le]
    exact bot_lt_iff_ne_bot.mpr hPhiNeBot
  have hPhiTop : phiTerm < normalInvariantTop ract := by
    change phiS < (⊤ : Subgroup S)
    rw [← Subgroup.map_lt_map_iff_of_injective S.subtype_injective]
    rw [show phiS.map S.subtype = frattini P by
      exact Subgroup.map_subgroupOf_eq_of_le hPhiS.le]
    simpa [← MonoidHom.range_eq_map] using hPhiS.lt
  refine ⟨phiTerm, hbotPhi, hPhiTop, ?_⟩
  intro A B C D hAB hBC hCD
  have hbotAle : normalInvariantBot ract ≤ A := by
    change (⊥ : Subgroup S) ≤ A.1
    exact bot_le
  have hbotB : normalInvariantBot ract < B :=
    lt_of_le_of_lt hbotAle hAB
  have hbotC : normalInvariantBot ract < C := hbotB.trans hBC
  have hbotD : normalInvariantBot ract < D := hbotC.trans hCD
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
    have hcommK : _root_.commutator P ≤ K.1.map S.subtype :=
      (OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        hPhiK
    have hKmapNormal : (K.1.map S.subtype).Normal := by
      apply (Subgroup.commutator_top_left_le_iff
        (H := K.1.map S.subtype)).mp
      exact (Subgroup.commutator_mono le_rfl le_top).trans hcommK
    exact ⟨⟨K.1.map S.subtype, ⟨hKmapNormal, hKmapInv⟩⟩,
      rfl, hPhiK⟩
  obtain ⟨B', hB', hPhiB'⟩ := lift_nontrivial B hbotB.ne'
  obtain ⟨C', hC', hPhiC'⟩ := lift_nontrivial C hbotC.ne'
  obtain ⟨D', hD', _hPhiD'⟩ := lift_nontrivial D hbotD.ne'
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
  have hC'S : C'.1 ≤ S := by
    rw [hC']
    exact Subgroup.map_subtype_le C.1
  have hD'S : D'.1 ≤ S := by
    rw [hD']
    exact Subgroup.map_subtype_le D.1
  rcases hPhiS.eq_left_or_eq_right C'.2 hPhiC' hC'S with
    hCphi | hCS
  · have hBphi : B'.1 < frattini P := by
      have h := hB'C'
      change B'.1 < C'.1 at h
      rwa [hCphi] at h
    exact (not_lt_of_ge hPhiB') hBphi
  · have hSD : S < D'.1 := by
      have h := hC'D'
      change C'.1 < D'.1 at h
      rwa [hCS] at h
    exact (not_lt_of_ge hD'S) hSD

end OddOrder.Higman.Suzuki2Groups
