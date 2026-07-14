/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_ImprimitiveUBound
import OddOrder.Peterfalvi.S11_SingleFactorCentralizer
import OddOrder.GroupTheory.RepresentationTheory.BlockScalarSylow

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

/-- **Peterfalvi (14.6), case-(9.7.a) Sylow noncyclicity.**  At the sharp (13.13) parameters
`q = 3` and `u = ((p - 1) / 2)²`, every Sylow `r`-subgroup of the faithful action image
`Ū = range(uActionHom)`, for `r ∣ (p - 1) / 2`, is noncyclic.

This is the direct §11 instantiation of the shared two-coordinate block-scalar theorem.  It
preserves the qualitative embedding from (9.7.a), rather than using only its cardinality
divisibility corollary. -/
theorem caseA_sylow_not_isCyclic_of_sharp_order [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseA : CliffordCaseAData chars)
    (hq : data.q = 3)
    (hu : chars.u = ((chief.p - 1) / 2) ^ 2)
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (chief.p - 1) / 2)
    (R : Sylow r ↥(MonoidHom.range (uActionHom data chief))) :
    ¬ IsCyclic ↥(R : Subgroup ↥(MonoidHom.range (uActionHom data chief))) := by
  obtain ⟨ψ, hψ⟩ := caseA_exists_blockScalarRatioEmbedding chars caseA
  have hqsub : data.q - 1 = 2 := by omega
  let e : Fin (data.q - 1) ≃ Fin 2 := finCongr hqsub
  let ψ2 : ↥(MonoidHom.range (uActionHom data chief)) →*
      (Fin 2 → (ZMod chief.p)ˣ) :=
    { toFun := fun u i => ψ u (e.symm i)
      map_one' := by ext i; simp
      map_mul' := fun x y => by ext i; simp }
  have hψ2 : Function.Injective ψ2 := by
    intro x y hxy
    apply hψ
    funext j
    have hij := congrFun hxy (e j)
    simpa only [ψ2, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.symm_apply_apply] using hij
  have hp2 : chief.p ≠ 2 := by
    intro hp2
    have heven := chiefFactor_p_sub_one_even (chief := chief) hG
    rw [hp2] at heven
    norm_num at heven
  have huCard :
      chars.u = Nat.card ↥(MonoidHom.range (uActionHom data chief)) :=
    chars.u_eq_card_quotient
  have hodd : Odd (Nat.card ↥(MonoidHom.range (uActionHom data chief))) := by
    rw [← huCard]
    exact u_odd hG chars
  have hcard :
      Nat.card ↥(MonoidHom.range (uActionHom data chief)) =
        ((chief.p - 1) / 2) ^ 2 := by
    rw [← huCard]
    exact hu
  exact OddOrder.RepresentationTheory.sylow_not_isCyclic_of_odd_blockScalarEmbedding
    chief.p_prime hp2 hodd ψ2 hψ2 hcard hr hrhalf R

/-- **Peterfalvi (14.6), case-(9.7.a) Sylow noncyclicity in `U`.**  Under the sharp
parameters, every Sylow `r`-subgroup of Peterfalvi's original `U`, for
`r ∣ (p - 1) / 2`, is noncyclic.

The action homomorphism is surjective onto its range.  Hence it sends a Sylow subgroup of `U`
to a Sylow subgroup of the faithful action image; a cyclic source would have cyclic image,
contradicting `caseA_sylow_not_isCyclic_of_sharp_order`.  Notice that no faithfulness assumption
on the original `U`-action is needed for this direction. -/
theorem caseA_sylow_U_not_isCyclic_of_sharp_order [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseA : CliffordCaseAData chars)
    (hq : data.q = 3)
    (hu : chars.u = ((chief.p - 1) / 2) ^ 2)
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (chief.p - 1) / 2)
    (R : Sylow r ↥data.U) :
    ¬ IsCyclic ↥(R : Subgroup ↥data.U) := by
  let e : ↥data.U ≃* ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    (Subgroup.subgroupOfEquivOfLe le_sup_left).symm
  let f : ↥data.U →* ↥(MonoidHom.range (uActionHom data chief)) :=
    (uActionHom data chief).rangeRestrict.comp e.toMonoidHom
  have hf : Function.Surjective f :=
    (uActionHom data chief).rangeRestrict_surjective.comp e.surjective
  letI : Fact r.Prime := ⟨hr⟩
  let Rbar : Sylow r ↥(MonoidHom.range (uActionHom data chief)) := R.mapSurjective hf
  have hRbar := caseA_sylow_not_isCyclic_of_sharp_order hG chars caseA hq hu
    hr hrhalf Rbar
  intro hR
  letI : IsCyclic ↥(R : Subgroup ↥data.U) := hR
  rw [show (Rbar : Subgroup ↥(MonoidHom.range (uActionHom data chief))) =
    (R : Subgroup ↥data.U).map f by rfl] at hRbar
  exact hRbar <|
    isCyclic_of_surjective _ (f.subgroupMap_surjective (R : Subgroup ↥data.U))

end OddOrder.Peterfalvi.S11
