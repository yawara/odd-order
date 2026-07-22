/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentFourJacobi
import OddOrder.GroupTheory.CommutatorSup

/-!
# Higman's Lemma 13: the final Frattini-square contradiction

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

If two restricted length-three factors generate `P`, their internal
commutators and squares lie in `Φ(P)²`.  Once the cross commutator also
lies there, `P / Φ(P)²` is elementary abelian.  Isaacs Lemma 4.5 then
forces `Φ(P) ≤ Φ(P)²`, contradicting the strict exponent-four Frattini
chain `Φ(P)² < Φ(P)`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open scoped commutatorElement IsMulCommutative
open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP


/-- Squares of elements of a restricted length-three factor land in the
common ambient `Φ(P)²`.

This is the power analogue of
`commutatorElement_mem_frattiniSquare_of_mem_restricted_lengthThree_factor_exponent_four`:
Isaacs Lemma 4.5 puts the square in `Φ(S)`, and the established restricted-factor
identification maps `Φ(S)` onto `Φ(P)²`. -/
theorem pow_two_mem_frattiniSquare_of_mem_restricted_lengthThree_factor_exponent_four
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : NormalInvariantCover Y.subtype (frattini P) S)
    (hlenS : HasXiLengthThree hSinv.restrict.range.subtype)
    (hncommS : ¬ IsMulCommutative S)
    {x : P} (hx : x ∈ S) :
    x ^ 2 ∈ frattiniSquare P := by
  have hPhiMap :=
    frattini_map_eq_frattiniSquare_of_restricted_lengthThree_exponent_four
      hP hmulti hxi hprime hPhiComm hexists hSinv hPhiS hlenS hncommS
  let xS : S := ⟨x, hx⟩
  have hpowS : xS ^ 2 ∈ frattini S :=
    OddOrder.Isaacs.Ch04.pow_p_mem_frattini_of_pgroup
      (hP.to_subgroup S) xS
  have hmap : S.subtype (xS ^ 2) ∈ (frattini S).map S.subtype :=
    Subgroup.mem_map_of_mem S.subtype hpowS
  rw [hPhiMap] at hmap
  rw [map_pow] at hmap
  exact hmap

/-- If two subgroups generate `P`, their internal and cross commutators
land in `Φ(P)²`, and their element squares land there, then
`P / Φ(P)²` is elementary abelian.

The power step is performed in the abelian quotient.  The kernel of its
squaring homomorphism contains the images of both factors; their join is
the full quotient, so every quotient element has square one. -/
private theorem frattiniSquare_quotient_isElementaryAbelian_of_two_factor_cover
    {P : Type uP} [Group P]
    [(frattiniSquare P).Normal]
    (X Z : Subgroup P)
    (hsup : X ⊔ Z = (⊤ : Subgroup P))
    (hXX : ⁅X, X⁆ ≤ frattiniSquare P)
    (hXZ : ⁅X, Z⁆ ≤ frattiniSquare P)
    (hZZ : ⁅Z, Z⁆ ≤ frattiniSquare P)
    (hXpow : ∀ x : P, x ∈ X → x ^ 2 ∈ frattiniSquare P)
    (hZpow : ∀ z : P, z ∈ Z → z ^ 2 ∈ frattiniSquare P) :
    IsElementaryAbelian 2 (P ⧸ frattiniSquare P) := by
  have hZX : ⁅Z, X⁆ ≤ frattiniSquare P := by
    simpa only [Subgroup.commutator_comm] using hXZ
  have hXsup : ⁅X, X ⊔ Z⁆ ≤ frattiniSquare P :=
    OddOrder.GroupTheory.commutator_sup_le_of_le hXX hXZ
  have hZsup : ⁅Z, X ⊔ Z⁆ ≤ frattiniSquare P :=
    OddOrder.GroupTheory.commutator_sup_le_of_le hZX hZZ
  have hsupComm : ⁅X ⊔ Z, X ⊔ Z⁆ ≤ frattiniSquare P := by
    apply OddOrder.GroupTheory.commutator_sup_le_of_le
    · simpa only [Subgroup.commutator_comm] using hXsup
    · simpa only [Subgroup.commutator_comm] using hZsup
  have hcomm : _root_.commutator P ≤ frattiniSquare P := by
    rw [_root_.commutator_def, ← hsup]
    exact hsupComm
  have hQcomm : ∀ a b : P ⧸ frattiniSquare P, a * b = b * a :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      hcomm).is_comm.comm
  letI : CommGroup (P ⧸ frattiniSquare P) :=
    { (inferInstance : Group (P ⧸ frattiniSquare P)) with
      mul_comm := hQcomm }
  let q := QuotientGroup.mk' (frattiniSquare P)
  have hXker : X.map q ≤
      (powMonoidHom 2 :
        (P ⧸ frattiniSquare P) →* (P ⧸ frattiniSquare P)).ker := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow]
    exact (QuotientGroup.eq_one_iff (x ^ 2)).2 (hXpow x hx)
  have hZker : Z.map q ≤
      (powMonoidHom 2 :
        (P ⧸ frattiniSquare P) →* (P ⧸ frattiniSquare P)).ker := by
    rintro _ ⟨z, hz, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow]
    exact (QuotientGroup.eq_one_iff (z ^ 2)).2 (hZpow z hz)
  have htopKer : (⊤ : Subgroup (P ⧸ frattiniSquare P)) ≤
      (powMonoidHom 2 :
        (P ⧸ frattiniSquare P) →* (P ⧸ frattiniSquare P)).ker := by
    rw [← Subgroup.map_top_of_surjective q
      (QuotientGroup.mk'_surjective (frattiniSquare P)),
      ← hsup, Subgroup.map_sup]
    exact sup_le hXker hZker
  refine ⟨hQcomm, ?_⟩
  intro a
  have ha := htopKer (show a ∈ (⊤ : Subgroup
    (P ⧸ frattiniSquare P)) from Subgroup.mem_top a)
  rwa [MonoidHom.mem_ker, powMonoidHom_apply] at ha

/-- The abstract final contradiction in Higman's exponent-four branch.

The hypotheses isolate exactly the output required from the factorwise and
cross-commutator calculations. -/
private theorem false_of_frattiniSquare_two_factor_cover
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (X Z : Subgroup P)
    (hsup : X ⊔ Z = (⊤ : Subgroup P))
    (hXX : ⁅X, X⁆ ≤ frattiniSquare P)
    (hXZ : ⁅X, Z⁆ ≤ frattiniSquare P)
    (hZZ : ⁅Z, Z⁆ ≤ frattiniSquare P)
    (hXpow : ∀ x : P, x ∈ X → x ^ 2 ∈ frattiniSquare P)
    (hZpow : ∀ z : P, z ∈ Z → z ^ 2 ∈ frattiniSquare P) :
    False := by
  letI : (frattiniSquare P).Normal :=
    (frattiniSquareNormalInvariant
      (MonoidHom.id (MulAut P))).2.1
  have hEA : IsElementaryAbelian 2 (P ⧸ frattiniSquare P) :=
    frattiniSquare_quotient_isElementaryAbelian_of_two_factor_cover
      X Z hsup hXX hXZ hZZ hXpow hZpow
  have hPhiSquare : frattini P ≤ frattiniSquare P :=
    OddOrder.Isaacs.Ch04.frattini_le_of_isElementaryAbelian_quotient_of_pgroup
      hP hEA
  exact (frattiniSquare_lt_frattini hPhiComm hfour hexists).2 hPhiSquare

/-- **Higman Lemma 13 (p. 92), factor-cover endpoint.**

For two restricted length-three factors covering `P`, the factorwise
commutator and power hypotheses are discharged by their common ambient
Frattini identification.  Therefore a cross-commutator inclusion in
`Φ(P)²` is impossible in the genuine exponent-four branch. -/
theorem false_of_restrictedFactor_covers_of_crossCommutator_le_frattiniSquare
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (X Z : Subgroup P)
    (hXinv : IsAInvariant Y.subtype X)
    (hPhiX : NormalInvariantCover Y.subtype (frattini P) X)
    (hlenX : HasXiLengthThree hXinv.restrict.range.subtype)
    (hncommX : ¬ IsMulCommutative X)
    (hZinv : IsAInvariant Y.subtype Z)
    (hPhiZ : NormalInvariantCover Y.subtype (frattini P) Z)
    (hlenZ : HasXiLengthThree hZinv.restrict.range.subtype)
    (hncommZ : ¬ IsMulCommutative Z)
    (hsup : X ⊔ Z = (⊤ : Subgroup P))
    (hXZ : ⁅X, Z⁆ ≤ frattiniSquare P) :
    False := by
  have hXX : ⁅X, X⁆ ≤ frattiniSquare P := by
    rw [Subgroup.commutator_le]
    intro x hx x' hx'
    exact
      commutatorElement_mem_frattiniSquare_of_mem_restricted_lengthThree_factor_exponent_four
        hP hmulti hxi hprime hPhiComm hexists
          hXinv hPhiX hlenX hncommX hx hx'
  have hZZ : ⁅Z, Z⁆ ≤ frattiniSquare P := by
    rw [Subgroup.commutator_le]
    intro z hz z' hz'
    exact
      commutatorElement_mem_frattiniSquare_of_mem_restricted_lengthThree_factor_exponent_four
        hP hmulti hxi hprime hPhiComm hexists
          hZinv hPhiZ hlenZ hncommZ hz hz'
  have hXpow : ∀ x : P, x ∈ X → x ^ 2 ∈ frattiniSquare P := by
    intro x hx
    exact
      pow_two_mem_frattiniSquare_of_mem_restricted_lengthThree_factor_exponent_four
        hP hmulti hxi hprime hPhiComm hexists
          hXinv hPhiX hlenX hncommX hx
  have hZpow : ∀ z : P, z ∈ Z → z ^ 2 ∈ frattiniSquare P := by
    intro z hz
    exact
      pow_two_mem_frattiniSquare_of_mem_restricted_lengthThree_factor_exponent_four
        hP hmulti hxi hprime hPhiComm hexists
          hZinv hPhiZ hlenZ hncommZ hz
  exact false_of_frattiniSquare_two_factor_cover
    hP hPhiComm hfour hexists X Z hsup hXX hXZ hZZ hXpow hZpow


end OddOrder.Higman.Suzuki2Groups
