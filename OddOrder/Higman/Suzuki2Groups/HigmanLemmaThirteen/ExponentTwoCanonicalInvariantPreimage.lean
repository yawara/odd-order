/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoInvariantPreimage

/-!
# Higman's Lemma 13: the canonical invariant Frattini preimage

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

The invariant-preimage endpoint constructs its new factor by pulling an
invariant subgroup `D ≤ P / Φ(P)` back along the quotient map.  This leaf
retains that canonical identification in the conclusion.  In particular,
the resulting subgroup maps onto exactly `D`, so later graph-subspace
arguments can recover the quotient subspace without losing witness data.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

section /- Higman Lemma 13 (p. 93) -/

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

variable {P : Type uP} [Group P]

/-- **Higman Lemma 13 (p. 93), canonical new invariant factor.**

Under the exponent-two length-four hypotheses, the pullback of a nonzero
invariant quotient subgroup `D` is an inclusive type-A factor with the
required Frattini intersection and proper join.  Unlike the earlier
existential endpoint, this statement records both that the witness is the
literal pullback of `D` and that its quotient image is exactly `D`. -/
theorem exists_canonical_typeA_frattini_preimage_of_invariant_quotient_pair_exponent_two
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
    (htwo : ∀ z : frattini P, z ^ 2 = 1)
    {W : Subgroup P}
    (hWinv : IsAInvariant Y.subtype W)
    (hPhiW : frattini P < W)
    {D : Subgroup (P ⧸ frattini P)}
    (hDinv : IsAInvariant
      (IsAInvariant.of_characteristic Y.subtype :
        IsAInvariant Y.subtype (frattini P)).quotientMulAutHom D)
    (hDbot : D ≠ ⊥)
    (hDWinf :
      D ⊓ W.map (QuotientGroup.mk' (frattini P)) = ⊥)
    (hDWtop :
      D ⊔ W.map (QuotientGroup.mk' (frattini P)) ≠ ⊤) :
    ∃ (U : Subgroup P) (hUinv : IsAInvariant Y.subtype U),
      U.Normal ∧
        frattini P < U ∧
        U ⊓ W = frattini P ∧
        U ⊔ W < ⊤ ∧
        HasXiLengthTwo hUinv.restrict.range.subtype ∧
        IsXiLengthTwoTypeA.{uP, 0} U ∧
        U = D.comap (QuotientGroup.mk' (frattini P)) ∧
        U.map (QuotientGroup.mk' (frattini P)) = D := by
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let q := QuotientGroup.mk' (frattini P)
  let U := D.comap q
  have hUinv : IsAInvariant Y.subtype U := by
    simpa [U, q] using hPhiInv.comap_quotient hDinv
  have hPhiU : frattini P < U := by
    have h := (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2
        (bot_lt_iff_ne_bot.mpr hDbot)
    simpa [U, q, QuotientGroup.ker_mk'] using h
  have hWcomap : (W.map q).comap q = W := by
    simp [q, QuotientGroup.comap_map_mk',
      sup_eq_right.mpr hPhiW.le]
  have hUWinf : U ⊓ W = frattini P := by
    calc
      U ⊓ W = D.comap q ⊓ (W.map q).comap q := by
        rw [hWcomap]
      _ = (D ⊓ W.map q).comap q :=
        (Subgroup.comap_inf D (W.map q) q).symm
      _ = (⊥ : Subgroup (P ⧸ frattini P)).comap q := by
        simpa [q] using congrArg (fun S => S.comap q) hDWinf
      _ = frattini P := by
        simp [q, QuotientGroup.ker_mk']
  have hUWcomap :
      U ⊔ W = (D ⊔ W.map q).comap q := by
    calc
      U ⊔ W = D.comap q ⊔ (W.map q).comap q := by
        rw [hWcomap]
      _ = (D ⊔ W.map q).comap q :=
        Subgroup.comap_sup_eq (f := q) D (W.map q)
          (QuotientGroup.mk'_surjective (frattini P))
  have hUWtop : U ⊔ W < (⊤ : Subgroup P) := by
    rw [hUWcomap]
    have h := (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2
        (lt_top_iff_ne_top.mpr hDWtop)
    simpa [q] using h
  have hUnormal : U.Normal :=
    Subgroup.Normal.of_commutator_le P
      ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        hPhiU.le)
  have hWnormal : W.Normal :=
    Subgroup.Normal.of_commutator_le P
      ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        hPhiW.le)
  have hUjoin : U < U ⊔ W := by
    apply lt_of_le_of_ne le_sup_left
    intro hEq
    have hWU : W ≤ U := by
      rw [hEq]
      exact le_sup_right
    have hWphi : W = frattini P := by
      calc
        W = U ⊓ W := (inf_eq_right.mpr hWU).symm
        _ = frattini P := hUWinf
    exact hPhiW.ne hWphi.symm
  let : U.Normal := hUnormal
  let : W.Normal := hWnormal
  let phiTerm := frattiniNormalInvariant Y.subtype
  let uTerm : NormalInvariantSubgroup Y.subtype :=
    ⟨U, ⟨hUnormal, hUinv⟩⟩
  let uwTerm : NormalInvariantSubgroup Y.subtype :=
    ⟨U ⊔ W, ⟨inferInstance, hUinv.sup hWinv⟩⟩
  have hbotPhi : normalInvariantBot Y.subtype < phiTerm :=
    (normalInvariantBot_covBy_frattini_of_pow_two_eq_one
      hP hncomm hxi htwo).lt
  have hPhiUTerm : phiTerm < uTerm := hPhiU
  have hUjoinTerm : uTerm < uwTerm := hUjoin
  have hJoinTopTerm : uwTerm < normalInvariantTop Y.subtype := hUWtop
  have hUcovers := hlen.covers_of_chain
    hbotPhi hPhiUTerm hUjoinTerm hJoinTopTerm
  let hPhiUCover : NormalInvariantCover Y.subtype (frattini P) U :=
    { left := phiTerm.2
      right := uTerm.2
      covBy := hUcovers.2.1 }
  have hlenU : HasXiLengthTwo hUinv.restrict.range.subtype :=
    restricted_range_hasXiLengthTwo_of_frattini_cover_exponent_two
      hP hncomm hxi htwo hUinv hPhiUCover
  have hmodelU : IsXiLengthTwoTypeA.{uP, 0} U :=
    isXiLengthTwoTypeA_invariant_subgroup
      hP hmulti hxi hprime hUinv hPhiU hlenU
  have hUcanonical :
      U = D.comap (QuotientGroup.mk' (frattini P)) := by
    rfl
  have hUmap :
      U.map (QuotientGroup.mk' (frattini P)) = D := by
    simpa [U, q] using
      Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective (frattini P)) D
  exact ⟨U, hUinv, hUnormal, hPhiU, hUWinf, hUWtop,
    hlenU, hmodelU, hUcanonical, hUmap⟩

end

end OddOrder.Higman.Suzuki2Groups
