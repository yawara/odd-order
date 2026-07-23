/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedLengths

/-!
# Higman's Lemma 13: full geometry of the exponent-two preimages

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

The exponent-two Frattini-quotient decomposition lifts to three normal
actor-invariant subgroups of restricted `ξ`-length two.  Besides their
pairwise intersections and joins, this leaf retains the directness identity
`(X ⊔ Z) ⊓ T = Φ(P)` already supplied by the raw preimage construction.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

variable {P : Type uP} [Group P]

/-- **Higman Lemma 13 (p. 93), exponent-two lifted factors with full
preimage geometry.**

This is the full-geometry sibling of
`exists_three_xiLengthTwo_frattini_preimages_of_exponent_two`: it retains the
raw identity `(X ⊔ Z) ⊓ T = Φ(P)` for the same restricted-length witnesses. -/
theorem
    exists_three_xiLengthTwo_frattini_preimages_with_full_geometry_of_exponent_two
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
          (X ⊔ Z) ⊓ T = frattini P ∧
            X ⊔ Z ⊔ T = ⊤ := by
  obtain ⟨X, Z, T, hXnormal, hXinv, hZnormal, hZinv,
      hTnormal, hTinv, hPhiX, hXtop, hPhiZ, hZtop, hPhiT, hTtop,
      _hXbot, _hZbot, _hTbot, hXZinf, hXTinf, hZTinf,
      hXZtop, hXTtop, hZTtop, hXZ_Tinf, hXZ_Tsup⟩ :=
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
    hXZinf, hXTinf, hZTinf, hXZtop, hXTtop, hZTtop,
    hXZ_Tinf, hXZ_Tsup⟩

end OddOrder.Higman.Suzuki2Groups
