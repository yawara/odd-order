/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.Basic
import OddOrder.Peterfalvi.Appendices.Suzuki.SylowTwo

/-!
# Peterfalvi Part II, Ch. III: the Feit–Sibley configuration

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III, §1, p. 115.

The proof of Theorem C observes, once `D` acts fixed-point-freely on `Q₁`
(`StructureOfH/Basic.lean`) and `Q` has trivial intersections in `G`, that
"the hypotheses of the Feit–Sibley Theorem, stated in Appendix IV, are
therefore satisfied".

This leaf supplies the remaining inputs of `FeitSibley.Hypothesis`:

* the conjugation action of `D` on the odd part `Q₁` (`conjQ1ByD`), which is
  Frobenius by Theorem C's step 1 and hence forces `(|Q₁|, |D|) = 1`;
* the ambient Sylow `2`-subgroup `S ≤ Q` of the book's `Q = S × Q₁`, together
  with the direct-product bookkeeping;
* `(|Q|, |D|) = 1`: an odd prime dividing `|Q|` divides the odd part `|Q₁|`,
  and `|D|` is odd, so the `2`-part is excluded as well.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.Isaacs.Ch06 (IsFrobeniusAction)

universe uG uΩ

namespace Hypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## The conjugation action of `D` on `Q₁` -/

/-- Conjugation by `D` on the odd part `Q₁` (`D ≤ H ≤ N_G(Q₁)`). -/
def conjQ1ByD : ↥hyp.D →* MulAut ↥hyp.Q1 where
  toFun k :=
    { toFun := fun x => ⟨(k : G) * x * (k : G)⁻¹,
        hyp.conj_mem_Q1_of_mem_H (hyp.D_le_H k.2) x.2⟩
      invFun := fun x => ⟨(k : G)⁻¹ * x * (k : G), by
        simpa using hyp.conj_mem_Q1_of_mem_H (inv_mem (hyp.D_le_H k.2)) x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by
        change (k : G) * ((x : G) * (y : G)) * (k : G)⁻¹ =
          ((k : G) * x * (k : G)⁻¹) * ((k : G) * y * (k : G)⁻¹)
        group) }
  map_one' := by
    ext x
    change ((1 : ↥hyp.D) : G) * (x : G) * ((1 : ↥hyp.D) : G)⁻¹ = (x : G)
    simp
  map_mul' k l := by
    ext x
    change (((k : G) * (l : G)) * (x : G) * (((k : G) * (l : G))⁻¹)) =
      (k : G) * ((l : G) * (x : G) * (l : G)⁻¹) * (k : G)⁻¹
    group

@[simp] lemma conjQ1ByD_apply_val (k : ↥hyp.D) (x : ↥hyp.Q1) :
    ((hyp.conjQ1ByD k x : ↥hyp.Q1) : G) = (k : G) * (x : G) * (k : G)⁻¹ := rfl

/-! ## The ambient Sylow `2`-subgroup `S` of `Q` -/

/-- The book's `S`: a Sylow `2`-subgroup of `Q`, as a subgroup of `G`.  Since `Q`
is nilpotent its Sylow `2`-subgroup is unique, so the choice is canonical. -/
noncomputable def sylowTwoOfQ : Subgroup G :=
  ((default : Sylow 2 ↥hyp.Q) : Subgroup ↥hyp.Q).map hyp.Q.subtype

lemma sylowTwoOfQ_le_Q : hyp.sylowTwoOfQ ≤ hyp.Q := by
  rintro x ⟨s, _, rfl⟩
  exact s.2

lemma card_sylowTwoOfQ :
    Nat.card ↥hyp.sylowTwoOfQ =
      Nat.card ↥((default : Sylow 2 ↥hyp.Q) : Subgroup ↥hyp.Q) :=
  (Nat.card_congr
    (Subgroup.equivMapOfInjective _ hyp.Q.subtype hyp.Q.subtype_injective).toEquiv).symm

/-- `|S| · |Q₁| = |Q|`: the book's internal direct decomposition `Q = S × Q₁`. -/
theorem card_sylowTwoOfQ_mul_card_Q1 :
    Nat.card ↥hyp.sylowTwoOfQ * Nat.card ↥hyp.Q1 = Nat.card ↥hyp.Q := by
  have h := Nat.card_congr
    (hyp.sylowTwoProdQ1MulEquiv (default : Sylow 2 ↥hyp.Q)).toEquiv
  rw [Nat.card_prod] at h
  rw [hyp.card_sylowTwoOfQ, hyp.card_Q1]
  exact h

/-- `S` is a `2`-group. -/
theorem isPGroup_sylowTwoOfQ : IsPGroup 2 ↥hyp.sylowTwoOfQ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_equiv (default : Sylow 2 ↥hyp.Q).isPGroup' ?_
  exact (Subgroup.equivMapOfInjective _ hyp.Q.subtype hyp.Q.subtype_injective)

/-- `|Q₁|` is odd: `Q₁` is the normal `2`-complement of `Q`. -/
theorem odd_card_Q1 : Odd (Nat.card ↥hyp.Q1) := by
  rw [hyp.card_Q1]
  rcases Nat.even_or_odd (Nat.card hyp.Q1Subgroup) with h | h
  · exact absurd h.two_dvd hyp.two_not_dvd_card_Q1Subgroup
  · exact h

end Hypothesis

namespace SecondCaseHypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (sc : SecondCaseHypothesis G Ω)

/-- **Theorem C, step 1, in Frobenius form**: the conjugation action of `D` on
`Q₁` is a Frobenius action. -/
theorem isFrobeniusAction_conjQ1ByD (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    letI : MulDistribMulAction ↥sc.toHypothesis.D ↥sc.toHypothesis.Q1 :=
      MulDistribMulAction.compHom _ sc.toHypothesis.conjQ1ByD
    IsFrobeniusAction ↥sc.toHypothesis.D ↥sc.toHypothesis.Q1 := by
  letI : MulDistribMulAction ↥sc.toHypothesis.D ↥sc.toHypothesis.Q1 :=
    MulDistribMulAction.compHom _ sc.toHypothesis.conjQ1ByD
  intro a ha n hn hfix
  refine hn (Subtype.ext ?_)
  refine sc.D_fixedPointFree_on_Q1 ind (a : G) a.2 (fun h => ha (Subtype.ext h)) (n : G) n.2 ?_
  exact congrArg (fun y : ↥sc.toHypothesis.Q1 => (y : G)) hfix

/-- `(|Q₁|, |D|) = 1`, from the Frobenius action of `D` on `Q₁`. -/
theorem coprime_card_Q1_D (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    Nat.Coprime (Nat.card ↥sc.toHypothesis.Q1) (Nat.card ↥sc.toHypothesis.D) := by
  classical
  letI : MulDistribMulAction ↥sc.toHypothesis.D ↥sc.toHypothesis.Q1 :=
    MulDistribMulAction.compHom _ sc.toHypothesis.conjQ1ByD
  haveI : Fintype ↥sc.toHypothesis.Q1 := Fintype.ofFinite _
  haveI : Fintype ↥sc.toHypothesis.D := Fintype.ofFinite _
  have h := (sc.isFrobeniusAction_conjQ1ByD ind).coprime_card
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

/-- **`(|Q|, |D|) = 1`**, the coprimality hypothesis of Appendix IV.

An odd prime dividing `|Q| = |S|·|Q₁|` divides `|Q₁|` (as `|S|` is a power of
`2`), and `(|Q₁|, |D|) = 1`; the prime `2` is excluded because `|D|` is odd. -/
theorem coprime_card_Q_D (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    Nat.Coprime (Nat.card ↥sc.toHypothesis.Q) (Nat.card ↥sc.toHypothesis.D) := by
  set hyp := sc.toHypothesis with hhyp
  by_contra hcop
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcop
  have hpQ : p ∣ Nat.card ↥hyp.Q := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpD : p ∣ Nat.card ↥hyp.D := hpdvd.trans (Nat.gcd_dvd_right _ _)
  -- `p ≠ 2`, since `|D|` is odd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hyp.D_odd) (even_iff_two_dvd.mpr hpD)
  -- `p ∣ |Q| = |S|·|Q₁|` with `|S|` a power of `2`, so `p ∣ |Q₁|`
  obtain ⟨n, hn⟩ := (hyp.isPGroup_sylowTwoOfQ).exists_card_eq
  have hpQ1 : p ∣ Nat.card ↥hyp.Q1 := by
    rw [← hyp.card_sylowTwoOfQ_mul_card_Q1, hn] at hpQ
    rcases (Nat.Prime.dvd_mul hp).mp hpQ with hS | hQ1
    · exact absurd (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two |>.mp
        (hp.dvd_of_dvd_pow hS)) hp2
    · exact hQ1
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes (sc.coprime_card_Q1_D ind) hpQ1 hpD)

end SecondCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
