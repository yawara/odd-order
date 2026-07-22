/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.QuotientSummands
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.QuotientTwoStep

/-!
# Higman's Lemma 13: Frattini preimages of quotient summands

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, pp. 92–93.

The invariant summands of `P / Φ(P)` are pulled back to normal
actor-invariant subgroups of `P`.  In the exponent-four branch there are two
preimages whose intersection is `Φ(P)` and whose join is `P`.  In the
exponent-two branch there are three, with the corresponding successive
intersection and join identities.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

variable {P : Type uP} [Group P]

/-- Pull three complementary nonzero proper invariant summands of the
Frattini quotient back to invariant subgroups of the original group. -/
theorem frattiniPreimages_of_three_complementary_quotient_summands
    {Y : Subgroup (MulAut P)}
    {U V W : Subgroup (P ⧸ frattini P)}
    (hUinv : IsAInvariant
      (IsAInvariant.of_characteristic Y.subtype :
        IsAInvariant Y.subtype (frattini P)).quotientMulAutHom U)
    (hVinv : IsAInvariant
      (IsAInvariant.of_characteristic Y.subtype :
        IsAInvariant Y.subtype (frattini P)).quotientMulAutHom V)
    (hWinv : IsAInvariant
      (IsAInvariant.of_characteristic Y.subtype :
        IsAInvariant Y.subtype (frattini P)).quotientMulAutHom W)
    (hUbot : U ≠ ⊥) (hUtop : U ≠ ⊤)
    (hVbot : V ≠ ⊥) (hVtop : V ≠ ⊤)
    (hWbot : W ≠ ⊥) (hWtop : W ≠ ⊤)
    (hUVbot : U ⊓ V = ⊥)
    (hUVWbot : (U ⊔ V) ⊓ W = ⊥)
    (hUVWtop : U ⊔ V ⊔ W = ⊤) :
    ∃ X Z T : Subgroup P,
      IsAInvariant Y.subtype X ∧
        IsAInvariant Y.subtype Z ∧
        IsAInvariant Y.subtype T ∧
        frattini P < X ∧ X < ⊤ ∧
        frattini P < Z ∧ Z < ⊤ ∧
        frattini P < T ∧ T < ⊤ ∧
        X ≠ ⊥ ∧ Z ≠ ⊥ ∧ T ≠ ⊥ ∧
        X ⊓ Z = frattini P ∧
          (X ⊔ Z) ⊓ T = frattini P ∧
            X ⊔ Z ⊔ T = ⊤ := by
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let q := QuotientGroup.mk' (frattini P)
  let X := U.comap q
  let Z := V.comap q
  let T := W.comap q
  have hXinv : IsAInvariant Y.subtype X := by
    simpa [X, q] using hPhiInv.comap_quotient hUinv
  have hZinv : IsAInvariant Y.subtype Z := by
    simpa [Z, q] using hPhiInv.comap_quotient hVinv
  have hTinv : IsAInvariant Y.subtype T := by
    simpa [T, q] using hPhiInv.comap_quotient hWinv
  have hPhiX : frattini P < X := by
    have h := (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2
        (bot_lt_iff_ne_bot.mpr hUbot)
    simpa [X, q, QuotientGroup.ker_mk'] using h
  have hXtop : X < (⊤ : Subgroup P) := by
    have h := (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2
        (lt_top_iff_ne_top.mpr hUtop)
    simpa [X, q] using h
  have hPhiZ : frattini P < Z := by
    have h := (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2
        (bot_lt_iff_ne_bot.mpr hVbot)
    simpa [Z, q, QuotientGroup.ker_mk'] using h
  have hZtop : Z < (⊤ : Subgroup P) := by
    have h := (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2
        (lt_top_iff_ne_top.mpr hVtop)
    simpa [Z, q] using h
  have hPhiT : frattini P < T := by
    have h := (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2
        (bot_lt_iff_ne_bot.mpr hWbot)
    simpa [T, q, QuotientGroup.ker_mk'] using h
  have hTtop : T < (⊤ : Subgroup P) := by
    have h := (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2
        (lt_top_iff_ne_top.mpr hWtop)
    simpa [T, q] using h
  have hXZinf : X ⊓ Z = frattini P := by
    calc
      X ⊓ Z = (U ⊓ V).comap q := by
        exact (Subgroup.comap_inf U V q).symm
      _ = (⊥ : Subgroup (P ⧸ frattini P)).comap q := by
        rw [hUVbot]
      _ = frattini P := by simp [q, QuotientGroup.ker_mk']
  have hXZsup : X ⊔ Z = (U ⊔ V).comap q :=
    Subgroup.comap_sup_eq (f := q) U V
      (QuotientGroup.mk'_surjective (frattini P))
  have hXZ_Tinf : (X ⊔ Z) ⊓ T = frattini P := by
    calc
      (X ⊔ Z) ⊓ T = ((U ⊔ V) ⊓ W).comap q := by
        rw [hXZsup]
        exact (Subgroup.comap_inf (U ⊔ V) W q).symm
      _ = (⊥ : Subgroup (P ⧸ frattini P)).comap q := by
        rw [hUVWbot]
      _ = frattini P := by simp [q, QuotientGroup.ker_mk']
  have hXZ_Tsup : X ⊔ Z ⊔ T = (⊤ : Subgroup P) := by
    calc
      X ⊔ Z ⊔ T = ((U ⊔ V) ⊔ W).comap q := by
        rw [hXZsup]
        exact Subgroup.comap_sup_eq (f := q) (U ⊔ V) W
          (QuotientGroup.mk'_surjective (frattini P))
      _ = (⊤ : Subgroup (P ⧸ frattini P)).comap q := by
        rw [hUVWtop]
      _ = ⊤ := Subgroup.comap_top q
  exact ⟨X, Z, T, hXinv, hZinv, hTinv,
    hPhiX, hXtop, hPhiZ, hZtop, hPhiT, hTtop,
    ne_of_gt (lt_of_le_of_lt bot_le hPhiX),
    ne_of_gt (lt_of_le_of_lt bot_le hPhiZ),
    ne_of_gt (lt_of_le_of_lt bot_le hPhiT),
    hXZinf, hXZ_Tinf, hXZ_Tsup⟩

/-- **Higman Lemma 13 (p. 92), exponent-four Frattini preimages.**

The two quotient summands lift to proper normal actor-invariant subgroups
whose intersection is `Φ(P)` and whose join is all of `P`. -/
theorem exists_two_invariant_frattini_preimages_of_xiLengthFour_exponent_four
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
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    ∃ X Z : Subgroup P,
      X.Normal ∧ IsAInvariant Y.subtype X ∧
        Z.Normal ∧ IsAInvariant Y.subtype Z ∧
        frattini P < X ∧ X < ⊤ ∧
        frattini P < Z ∧ Z < ⊤ ∧
        X ≠ ⊥ ∧ Z ≠ ⊥ ∧
        X ⊓ Z = frattini P ∧ X ⊔ Z = ⊤ := by
  obtain ⟨U, W, hUinv, hWinv, hUbot, hUtop,
      hWbot, hWtop, hUWbot, hUWtop⟩ :=
    exists_two_invariant_quotient_summands_of_xiLengthFour_exponent_four
      hP hncomm hmulti hxi hlen hprime hPhiComm hfour hexists
  obtain ⟨X, Z, hXinv, hZinv, hPhiX, hXtop,
      hPhiZ, hZtop, hXbot, hZbot, hXZinf, hXZsup⟩ :=
    frattiniPreimages_of_complementary_invariant_quotient_summands
      hUinv hWinv hUbot hUtop hWbot hWtop hUWbot hUWtop
  have hXnormal : X.Normal :=
    Subgroup.Normal.of_commutator_le P
      ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        hPhiX.le)
  have hZnormal : Z.Normal :=
    Subgroup.Normal.of_commutator_le P
      ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        hPhiZ.le)
  exact ⟨X, Z, hXnormal, hXinv, hZnormal, hZinv,
    hPhiX, hXtop, hPhiZ, hZtop, hXbot, hZbot, hXZinf, hXZsup⟩

/-- **Higman Lemma 13 (p. 92), exponent-two Frattini preimages.**

The three quotient summands lift to proper normal actor-invariant subgroups
whose successive intersections are `Φ(P)` and whose join is all of `P`. -/
theorem exists_three_invariant_frattini_preimages_of_xiLengthFour_exponent_two
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
    ∃ X Z T : Subgroup P,
      X.Normal ∧ IsAInvariant Y.subtype X ∧
        Z.Normal ∧ IsAInvariant Y.subtype Z ∧
        T.Normal ∧ IsAInvariant Y.subtype T ∧
        frattini P < X ∧ X < ⊤ ∧
        frattini P < Z ∧ Z < ⊤ ∧
        frattini P < T ∧ T < ⊤ ∧
        X ≠ ⊥ ∧ Z ≠ ⊥ ∧ T ≠ ⊥ ∧
        X ⊓ Z = frattini P ∧
          (X ⊔ Z) ⊓ T = frattini P ∧
            X ⊔ Z ⊔ T = ⊤ := by
  obtain ⟨U, V, W, hUinv, hVinv, hWinv,
      hUbot, hUtop, hVbot, hVtop, hWbot, hWtop,
      hUVbot, hUVWbot, hUVWtop⟩ :=
    exists_three_invariant_quotient_summands_of_xiLengthFour_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
  obtain ⟨X, Z, T, hXinv, hZinv, hTinv,
      hPhiX, hXtop, hPhiZ, hZtop, hPhiT, hTtop,
      hXbot, hZbot, hTbot, hXZinf, hXZ_Tinf, hXZ_Tsup⟩ :=
    frattiniPreimages_of_three_complementary_quotient_summands
      hUinv hVinv hWinv hUbot hUtop hVbot hVtop hWbot hWtop
      hUVbot hUVWbot hUVWtop
  have hXnormal : X.Normal :=
    Subgroup.Normal.of_commutator_le P
      ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        hPhiX.le)
  have hZnormal : Z.Normal :=
    Subgroup.Normal.of_commutator_le P
      ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        hPhiZ.le)
  have hTnormal : T.Normal :=
    Subgroup.Normal.of_commutator_le P
      ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        hPhiT.le)
  exact ⟨X, Z, T, hXnormal, hXinv, hZnormal, hZinv,
    hTnormal, hTinv, hPhiX, hXtop, hPhiZ, hZtop, hPhiT, hTtop,
    hXbot, hZbot, hTbot, hXZinf, hXZ_Tinf, hXZ_Tsup⟩

end OddOrder.Higman.Suzuki2Groups
