/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S08_CaseBSeedGlue

/-!
# Peterfalvi (6.5): reduction to a non-abelian `p`-group — `(6.8)` application

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §6, (6.5).

The group-theoretic core of Peterfalvi (6.5)(b) — *a finite nilpotent group on whose abelianization a
finite group acts fixed-point-freely, with the `≤ 4|·|² + 1` index bound, is a `p`-group* — is
already formalized abstractly:
* `isPGroup_of_isFrobeniusGroup_of_card_le` (`S08_CoherenceCorePart1`) for the (6.8)(c1) Frobenius
  case (full fixed-point-free conjugation action), and
* `isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator` for the (6.8)(c2) certain-type case
  (fixed points in `⁅H,H⁆`).

Both take the **index bound** `hbound : |Abelianization H| ≤ 4|W₁|² + 1` as the single nontrivial
input; that bound is the contrapositive of Theorem (6.3) (`¬coherent S` + nilpotent + `S(⁅H,H⁆) = Y`
coherent ⟹ the bound), which is the remaining gate (via (6.2)).

This leaf supplies the two odd-order side conditions and wires the **(6.8)(c1) Frobenius** reduction
into the `SibleyDadeHypothesis` context, isolating `hbound` as the residual obligation.
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- Any natural dividing `|L|` is odd (since `|L|` is odd, Peterfalvi (6.4.a)). -/
theorem odd_of_dvd_card_L (hyp : SibleyDadeHypothesis G L H) {a : ℕ} (ha : a ∣ Nat.card ↥L) :
    Odd a := by
  rcases Nat.even_or_odd a with he | ho
  · obtain ⟨c, hc⟩ := ha
    exact absurd (hc ▸ he.mul_right c) (Nat.not_even_iff_odd.mpr hyp.card_L_odd)
  · exact ho

/-- `|W₁|` is odd. -/
theorem card_W1_odd (hyp : SibleyDadeHypothesis G L H) : Odd (Nat.card ↥hyp.W1) :=
  odd_of_dvd_card_L hyp (Subgroup.card_subgroup_dvd_card hyp.W1)

/-- `|H|` is odd. -/
theorem card_H_odd (hyp : SibleyDadeHypothesis G L H) : Odd (Nat.card ↥H) :=
  odd_of_dvd_card_L hyp (Subgroup.card_subgroup_dvd_card H)

/-- `|Abelianization H| = |H : ⁅H,H⁆|` is odd (it divides `|H|`, which divides the odd `|L|`). -/
theorem card_abelianization_H_odd (hyp : SibleyDadeHypothesis G L H) :
    Odd (Nat.card (Abelianization ↥H)) :=
  odd_of_dvd_card_L hyp
    ((Subgroup.card_quotient_dvd_card (commutator ↥H)).trans (Subgroup.card_subgroup_dvd_card H))

/-- **Peterfalvi (6.5)(b) reduction — (6.8)(c1) Frobenius case, in the Sibley context.**

When `L` is a Frobenius group with kernel `H` and complement `W₁` ((6.8)(c1), `hyp.cases.inl`), the
nilpotent kernel `H` is a `p`-group for some prime `p`, given the (6.2)/(6.3) index bound
`hbound : |Abelianization H| ≤ 4|W₁|² + 1`.  The odd-order side conditions are discharged from
`|L|` odd; the fixed-point-free `W₁`-action on `Abelianization H` is the Frobenius structure.

This wires `isPGroup_of_isFrobeniusGroup_of_card_le` into the capstone, isolating `hbound` (the
contrapositive of Theorem (6.3)) as the only residual obligation of the (6.8)(c1) `p`-group
reduction. -/
theorem exists_isPGroup_H_of_frobenius_of_card_le (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hbound : Nat.card (Abelianization ↥H) ≤ 4 * Nat.card ↥hyp.W1 ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p ↥H := by
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  exact isPGroup_of_isFrobeniusGroup_of_card_le hF (card_abelianization_H_odd hyp)
    (card_W1_odd hyp) hbound

/-- **Peterfalvi (6.5)(b) reduction — (6.8)(c2) certain-type case, in the Sibley context.**

In case (6.8)(c2) the complement `W₁` does *not* act fixed-point-freely on `H`, but the
`W₁`-conjugation fixed points lie in `⁅H,H⁆` (the certain-type centralizer condition `hfix`, phrased
via the explicit `L`-conjugation `w x w⁻¹ = x`).  Together with the Hall coprimality `hcop` and the
(6.2)/(6.3) index bound `hbound`, the nilpotent `H` is a `p`-group.

This wires `isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator` into the capstone via the
`W₁`-conjugation action, isolating `hfix` (the (4.6)/(6.4.c) fixed-point condition) and `hbound` (the
contrapositive of Theorem (6.3)) as the residual obligations of the (6.8)(c2) `p`-group reduction. -/
theorem exists_isPGroup_H_of_c2_of_card_le (hyp : SibleyDadeHypothesis G L H)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥hyp.W1))
    (hfix : ∀ w : ↥hyp.W1, w ≠ 1 → ∀ x : ↥H,
      (w : ↥L) * (x : ↥L) * (w : ↥L)⁻¹ = (x : ↥L) → x ∈ commutator ↥H)
    (hbound : Nat.card (Abelianization ↥H) ≤ 4 * Nat.card ↥hyp.W1 ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p ↥H := by
  letI : H.Normal := hyp.H_normal
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  -- the `W₁`-conjugation action on `H`.
  letI actH : MulDistribMulAction ↥hyp.W1 ↥H :=
    MulDistribMulAction.compHom H ((MulAut.conjNormal (H := H)).comp hyp.W1.subtype)
  have hsmulH : ∀ (a : ↥hyp.W1) (x : ↥H),
      ((a • x : ↥H) : ↥L) = (a : ↥L) * (x : ↥L) * (a : ↥L)⁻¹ := by
    intro a x
    have h1 : (a • x : ↥H) = (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a) x := by
      simp [MulDistribMulAction.toMulAut_apply]
    rw [h1]
    show ((MulAut.conjNormal (H := H) (hyp.W1.subtype a)) x : ↥L) = _
    rw [MulAut.conjNormal_apply]; rfl
  -- convert the explicit-conjugation `hfix` to the smul form the reduction lemma consumes.
  have hfix' : ∀ w : ↥hyp.W1, w ≠ 1 → ∀ x : ↥H, w • x = x → x ∈ commutator ↥H := by
    intro w hw x hwx
    refine hfix w hw x ?_
    have hb := hsmulH w x
    rw [hwx] at hb
    exact hb.symm
  exact isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator hcop.symm hfix'
    (card_abelianization_H_odd hyp) (card_W1_odd hyp) hbound

end OddOrder.Peterfalvi.S08
