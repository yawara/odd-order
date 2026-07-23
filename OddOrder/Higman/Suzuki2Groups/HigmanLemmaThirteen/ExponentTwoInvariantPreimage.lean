/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoFactorModels

/-!
# Higman's Lemma 13: a new invariant Frattini preimage

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

In the exponent-two branch, Higman constructs a new invariant summand of
`P / Φ(P)` which is independent from one of the original factors but does
not complement it: their sum is still proper.  This leaf isolates the
quotient-to-group step.  Pulling the new summand back gives an actual normal
invariant subgroup `U`; the ambient length-four chain then makes the
restricted action on `U` have length two, so the inclusive type-A
classification applies.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

section /- Higman Lemma 13 (p. 93) -/

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

variable {P : Type uP} [Group P]

/-- **Higman Lemma 13 (p. 93), new invariant factor.**

Let `D` be a nonzero invariant subgroup of the Frattini quotient.  If `D`
is independent from the image of an existing factor `W` and their sum is
proper, then the preimage of `D` is a normal invariant factor `U` satisfying
`U ∩ W = Φ(P)` and `U W < P`.  In the exponent-two length-four setting,
the restricted actor on `U` has exact `ξ`-length two and `U` has an honest
inclusive `A(n, φ)` model. -/
theorem exists_typeA_frattini_preimage_of_invariant_quotient_pair_exponent_two
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
    (hDWinf : D ⊓ W.map (QuotientGroup.mk' (frattini P)) = ⊥)
    (hDWtop : D ⊔ W.map (QuotientGroup.mk' (frattini P)) ≠ ⊤) :
    ∃ (U : Subgroup P) (hUinv : IsAInvariant Y.subtype U),
      U.Normal ∧
        frattini P < U ∧
        U ⊓ W = frattini P ∧
        U ⊔ W < ⊤ ∧
        HasXiLengthTwo hUinv.restrict.range.subtype ∧
        IsXiLengthTwoTypeA.{uP, 0} U := by
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
  letI : U.Normal := hUnormal
  letI : W.Normal := hWnormal
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
  exact ⟨U, hUinv, hUnormal, hPhiU, hUWinf, hUWtop, hlenU, hmodelU⟩

end

end OddOrder.Higman.Suzuki2Groups
