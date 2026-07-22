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

/-- **Higman Lemma 13 (p. 93), exponent-two lifted factors.**

The three independent Frattini preimages all have restricted `ξ`-length
two.  Their pairwise intersections are `Φ(P)`, every pairwise join is
proper, and together they generate `P`. -/
theorem exists_three_xiLengthTwo_frattini_preimages_of_exponent_two
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    ∃ (X Z T : Subgroup P)
        (hXinv : IsAInvariant Y.subtype X)
        (hZinv : IsAInvariant Y.subtype Z)
        (hTinv : IsAInvariant Y.subtype T),
      X.Normal ∧ HasXiLengthTwo hXinv.restrict.range.subtype ∧
        Z.Normal ∧ HasXiLengthTwo hZinv.restrict.range.subtype ∧
        T.Normal ∧ HasXiLengthTwo hTinv.restrict.range.subtype ∧
        frattini P < X ∧ X < ⊤ ∧
        frattini P < Z ∧ Z < ⊤ ∧
        frattini P < T ∧ T < ⊤ ∧
        X ⊓ Z = frattini P ∧ X ⊓ T = frattini P ∧
        Z ⊓ T = frattini P ∧
        X ⊔ Z < ⊤ ∧ X ⊔ T < ⊤ ∧ Z ⊔ T < ⊤ ∧
          X ⊔ Z ⊔ T = ⊤ := by
  obtain ⟨X, Z, T, hXnormal, hXinv, hZnormal, hZinv,
      hTnormal, hTinv, hPhiX, hXtop, hPhiZ, hZtop, hPhiT, hTtop,
      _hXbot, _hZbot, _hTbot, hXZinf, hXTinf, hZTinf,
      hXZtop, hXTtop, hZTtop, _hXZ_Tinf, hXZ_Tsup⟩ :=
    exists_three_invariant_frattini_preimages_of_xiLengthFour_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
  letI : X.Normal := hXnormal
  letI : Z.Normal := hZnormal
  letI : T.Normal := hTnormal
  have left_lt_sup_of_inf_eq_frattini :
      ∀ {A B : Subgroup P}, frattini P < B →
        A ⊓ B = frattini P → A < A ⊔ B := by
    intro A B hPhiB hABinf
    apply lt_of_le_of_ne le_sup_left
    intro hEq
    have hBA : B ≤ A := by
      rw [hEq]
      exact le_sup_right
    have hBphi : B = frattini P := by
      calc
        B = A ⊓ B := (inf_eq_right.mpr hBA).symm
        _ = frattini P := hABinf
    exact hPhiB.ne hBphi.symm
  have hX_XZ : X < X ⊔ Z :=
    left_lt_sup_of_inf_eq_frattini hPhiZ hXZinf
  have hZ_XZ : Z < X ⊔ Z := by
    have h := left_lt_sup_of_inf_eq_frattini hPhiX (by
      simpa [inf_comm] using hXZinf)
    simpa [sup_comm] using h
  have hT_XT : T < X ⊔ T := by
    have h := left_lt_sup_of_inf_eq_frattini hPhiX (by
      simpa [inf_comm] using hXTinf)
    simpa [sup_comm] using h
  let phiTerm := frattiniNormalInvariant Y.subtype
  let xTerm : NormalInvariantSubgroup Y.subtype :=
    ⟨X, ⟨hXnormal, hXinv⟩⟩
  let zTerm : NormalInvariantSubgroup Y.subtype :=
    ⟨Z, ⟨hZnormal, hZinv⟩⟩
  let tTerm : NormalInvariantSubgroup Y.subtype :=
    ⟨T, ⟨hTnormal, hTinv⟩⟩
  let xzTerm : NormalInvariantSubgroup Y.subtype :=
    ⟨X ⊔ Z, ⟨inferInstance, hXinv.sup hZinv⟩⟩
  let xtTerm : NormalInvariantSubgroup Y.subtype :=
    ⟨X ⊔ T, ⟨inferInstance, hXinv.sup hTinv⟩⟩
  have hbotPhi : normalInvariantBot Y.subtype < phiTerm := by
    exact (normalInvariantBot_covBy_frattini_of_pow_two_eq_one
      hP hncomm hxi htwo).lt
  have hPhiXTerm : phiTerm < xTerm := hPhiX
  have hPhiZTerm : phiTerm < zTerm := hPhiZ
  have hPhiTTerm : phiTerm < tTerm := hPhiT
  have hX_XZTerm : xTerm < xzTerm := hX_XZ
  have hZ_XZTerm : zTerm < xzTerm := hZ_XZ
  have hT_XTTerm : tTerm < xtTerm := hT_XT
  have hXZtopTerm : xzTerm < normalInvariantTop Y.subtype := hXZtop
  have hXTtopTerm : xtTerm < normalInvariantTop Y.subtype := hXTtop
  have hXcovers := hlen.covers_of_chain
    hbotPhi hPhiXTerm hX_XZTerm hXZtopTerm
  have hZcovers := hlen.covers_of_chain
    hbotPhi hPhiZTerm hZ_XZTerm hXZtopTerm
  have hTcovers := hlen.covers_of_chain
    hbotPhi hPhiTTerm hT_XTTerm hXTtopTerm
  let hPhiXCover : NormalInvariantCover Y.subtype (frattini P) X :=
    { left := phiTerm.2
      right := xTerm.2
      covBy := hXcovers.2.1 }
  let hPhiZCover : NormalInvariantCover Y.subtype (frattini P) Z :=
    { left := phiTerm.2
      right := zTerm.2
      covBy := hZcovers.2.1 }
  let hPhiTCover : NormalInvariantCover Y.subtype (frattini P) T :=
    { left := phiTerm.2
      right := tTerm.2
      covBy := hTcovers.2.1 }
  have hlenX : HasXiLengthTwo hXinv.restrict.range.subtype :=
    restricted_range_hasXiLengthTwo_of_frattini_cover_exponent_two
      hP hncomm hxi htwo hXinv hPhiXCover
  have hlenZ : HasXiLengthTwo hZinv.restrict.range.subtype :=
    restricted_range_hasXiLengthTwo_of_frattini_cover_exponent_two
      hP hncomm hxi htwo hZinv hPhiZCover
  have hlenT : HasXiLengthTwo hTinv.restrict.range.subtype :=
    restricted_range_hasXiLengthTwo_of_frattini_cover_exponent_two
      hP hncomm hxi htwo hTinv hPhiTCover
  exact ⟨X, Z, T, hXinv, hZinv, hTinv, hXnormal, hlenX,
    hZnormal, hlenZ, hTnormal, hlenT,
    hPhiX, hXtop, hPhiZ, hZtop, hPhiT, hTtop,
    hXZinf, hXTinf, hZTinf, hXZtop, hXTtop, hZTtop, hXZ_Tsup⟩

end OddOrder.Higman.Suzuki2Groups
