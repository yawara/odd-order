/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_ImprimitiveUBound
import OddOrder.Peterfalvi.S11_SingleFactorCentralizer

/-!
# Peterfalvi (13.13): the odd part of the case-A block bound

For the imprimitive branch of Peterfalvi (9.7), the block-scalar ratio embedding gives
`u ∣ (p - 1)^(q - 1)`.  In the odd-order setting, `u` is odd while `p - 1` is even, so Euclid's
lemma removes the entire 2-primary factor and yields

`u ∣ ((p - 1) / 2)^(q - 1)`.

This is the structural divisibility input used in Peterfalvi (13.13) to determine the case-A
parameters.
-/

namespace OddOrder.Peterfalvi.S11

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.13), case-A odd-part divisibility.**  The imprimitive block action gives
`u ∣ (p - 1)^(q - 1)`; since `u` is odd, coprimality with `2^(q - 1)` removes that factor from
`(p - 1)^(q - 1) = 2^(q - 1) ((p - 1) / 2)^(q - 1)`. -/
theorem caseA_u_dvd_half_pred_pow [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseA : CliffordCaseAData chars) :
    chars.u ∣ ((chief.p - 1) / 2) ^ (data.q - 1) := by
  have hdiv := caseA_u_dvd_pred_pow chars caseA
  have heven : 2 ∣ chief.p - 1 :=
    even_iff_two_dvd.mp (chiefFactor_p_sub_one_even (chief := chief) hG)
  have hsplit : chief.p - 1 = 2 * ((chief.p - 1) / 2) :=
    (Nat.mul_div_cancel' heven).symm
  rw [hsplit, mul_pow] at hdiv
  have hcop : Nat.Coprime chars.u (2 ^ (data.q - 1)) :=
    (Nat.coprime_two_right.mpr (u_odd hG chars)).pow_right _
  exact hcop.dvd_of_dvd_mul_left hdiv

end OddOrder.Peterfalvi.S11

