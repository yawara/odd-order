/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.SylowDecomposition
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerNormalizer
import OddOrder.GroupTheory.PrimeComplementResidual

/-!
# Peterfalvi Part II, Ch. I §3: Proposition 1(c), centralizer residual

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, pp. 105–106.

This file contains the target-independent structural clauses of Proposition
1(c).  It proves that, once `C_Q(X)` is known to be a `2`-group, the
odd-order direct factor `Q₁` has trivial centralizer of `X`. It also proves
the source's center equality for the normal closure `⟨C_Q(X)^L⟩`; its
identification with `O^{2′}(L)` and quotient transport are packaged once
the induction target supplies the honest proof that `C_Q(X)` is a `2`-group.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open MulAction

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

section /- §3 Proposition 1(c) (pp. 105–106) -/

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c)**, first inference.
If `C_Q(X)` is a `2`-group, then `C_{Q₁}(X)=1`.  Here `Q₁` is the
actual normal `2`-complement constructed from the nilpotence of `Q`;
its odd order is coprime to the order of every subgroup of `C_Q(X)`. -/
theorem Q1_inf_centralizer_eq_bot_of_isPGroup (X : Subgroup G)
    (hCQ : IsPGroup 2
      ↥(hyp.Q ⊓ Subgroup.centralizer (X : Set G))) :
    hyp.Q1 ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  let C : Subgroup G := hyp.Q ⊓ Subgroup.centralizer (X : Set G)
  let A : Subgroup G := hyp.Q1 ⊓ Subgroup.centralizer (X : Set G)
  have hAC : A ≤ C := inf_le_inf hyp.Q1_le_Q le_rfl
  have hAp : IsPGroup 2 ↥A := by
    have hsub : IsPGroup 2 ↥(A.subgroupOf C) :=
      hCQ.to_subgroup (A.subgroupOf C)
    exact hsub.of_equiv (Subgroup.subgroupOfEquivOfLe hAC)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hAp
  have hAdvd : Nat.card A ∣ Nat.card hyp.Q1 :=
    Subgroup.card_dvd_of_le inf_le_left
  have hQ1odd : ¬ 2 ∣ Nat.card hyp.Q1 := by
    rw [hyp.card_Q1]
    exact hyp.two_not_dvd_card_Q1Subgroup
  have hnzero : n = 0 := by
    by_contra hn0
    apply hQ1odd
    apply (show 2 ∣ Nat.card A by
      rw [hn]
      exact dvd_pow_self 2 hn0).trans hAdvd
  apply Subgroup.card_eq_one.mp
  rw [hn, hnzero, pow_zero]

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c)**, structural core.
Put `L = C_G(X)` and `F₀ = ⟨C_Q(X)^L⟩`. Then the intersection of
the action kernel `ℕ(L)` with `F₀` is exactly `Z(F₀)`. This is the
classification-independent equality used in the source before `F₀` is
identified with `O^{2′}(L)` through the induction quotient. -/
theorem normalCore_subgroupOf_normalClosure_cQ_eq_center
    {X : Subgroup G} (hXV : X ≤ hyp.V) :
    let L : Subgroup G := Subgroup.centralizer (X : Set G)
    let H_L : Subgroup L := hyp.H.subgroupOf L
    let Q_L : Subgroup L := hyp.Q.subgroupOf L
    let F_L : Subgroup L := Subgroup.normalClosure (Q_L : Set L)
    H_L.normalCore.subgroupOf F_L = Subgroup.center F_L := by
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let H_L : Subgroup L := hyp.H.subgroupOf L
  let Q_L : Subgroup L := hyp.Q.subgroupOf L
  let D_L : Subgroup L := hyp.D.subgroupOf L
  let F_L : Subgroup L := Subgroup.normalClosure (Q_L : Set L)
  change H_L.normalCore.subgroupOf F_L = Subgroup.center F_L
  have hNcentral : H_L.normalCore ≤ Subgroup.centralizer (F_L : Set L) := by
    rw [Subgroup.le_centralizer_iff]
    apply Subgroup.normalClosure_le_normal
    apply Subgroup.le_centralizer_iff.mp
    rw [hyp.normalCore_cH_eq_centralizer_cQ hXV]
    exact inf_le_right
  apply le_antisymm
  · intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact hNcentral hz y y.2
  · intro z hz
    have hXD : X ≤ hyp.D := hXV.trans hyp.V_le_D
    have h3 : 3 ≤ (MulAction.fixedPoints X Ω).ncard :=
      hyp.three_le_ncard_fixedPoints_of_le_V hXV
    have hQcard : Nat.card Q_L = Nat.card ↥(hyp.Q ⊓ L) := by
      change Nat.card ↥(hyp.Q.subgroupOf L) = Nat.card ↥(hyp.Q ⊓ L)
      rw [← Subgroup.inf_subgroupOf_right hyp.Q L]
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (K := L) inf_le_right).toEquiv
    have hQeven : Even (Nat.card Q_L) := by
      rw [hQcard]
      exact hyp.even_card_cQ hXD h3
    have hQne : Q_L ≠ ⊥ := by
      intro hbot
      simp [hbot] at hQeven
    obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQne
    have hq1G : (((q : Q_L) : L) : G) ≠ 1 := fun h =>
      hq1 (Subtype.ext (Subtype.ext h))
    have hqF : (q : L) ∈ F_L := Subgroup.subset_normalClosure q.2
    let qF : F_L := ⟨q, hqF⟩
    have hqzF : qF * z = z * qF := Subgroup.mem_center_iff.mp hz qF
    have hqzL : (q : L) * (z : L) = (z : L) * q :=
      congrArg Subtype.val hqzF
    have hzH : ((z : L) : G) ∈ hyp.H := by
      apply hyp.centralizer_le_H_of_mem_Q q.2 hq1G
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hqzL.symm
    have htL : hyp.t ∈ L := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hyp.commute_t_of_mem_V (hXV hx)).eq
    let tL : L := ⟨hyp.t, htL⟩
    have hqconjF : tL * (q : L) * tL⁻¹ ∈ F_L :=
      (inferInstance : F_L.Normal).conj_mem q hqF tL
    let qconjF : F_L := ⟨tL * (q : L) * tL⁻¹, hqconjF⟩
    have hqconjzF : qconjF * z = z * qconjF :=
      Subgroup.mem_center_iff.mp hz qconjF
    have hqconjzL :
        (tL * (q : L) * tL⁻¹) * (z : L) =
          (z : L) * (tL * (q : L) * tL⁻¹) :=
      congrArg Subtype.val hqconjzF
    have hzconj_comm_q :
        (tL⁻¹ * (z : L) * tL) * (q : L) =
          (q : L) * (tL⁻¹ * (z : L) * tL) := by
      calc
        (tL⁻¹ * (z : L) * tL) * (q : L) =
            tL⁻¹ * ((z : L) * (tL * (q : L) * tL⁻¹)) * tL := by group
        _ = tL⁻¹ * ((tL * (q : L) * tL⁻¹) * (z : L)) * tL := by
          rw [hqconjzL]
        _ = (q : L) * (tL⁻¹ * (z : L) * tL) := by group
    have hzconjH : hyp.t⁻¹ * ((z : L) : G) * hyp.t ∈ hyp.H := by
      apply hyp.centralizer_le_H_of_mem_Q q.2 hq1G
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hzconj_comm_q
    have hzD : ((z : L) : G) ∈ hyp.D := by
      rw [hyp.mem_D_iff]
      exact ⟨hzH, hzconjH⟩
    have hzCQL : (z : L) ∈ Subgroup.centralizer (Q_L : Set L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q' hq'
      have hq'F : q' ∈ F_L := Subgroup.subset_normalClosure hq'
      have hcommF := Subgroup.mem_center_iff.mp hz (⟨q', hq'F⟩ : F_L)
      exact congrArg Subtype.val hcommF
    change (z : L) ∈ H_L.normalCore
    rw [hyp.normalCore_cH_eq_centralizer_cQ hXV]
    exact ⟨hzD, hzCQL⟩

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c)**, structure
equation inherited from §1 Proposition 4(b):
`|C_G(X)| = |C_Q(X)| |C_D(X)| (|C_Q(X)| + 1)`. -/
theorem card_centralizer_eq {X : Subgroup G} (hXV : X ≤ hyp.V) :
    let L : Subgroup G := Subgroup.centralizer (X : Set G)
    let Q_L : Subgroup L := hyp.Q.subgroupOf L
    let D_L : Subgroup L := hyp.D.subgroupOf L
    Nat.card L =
      Nat.card Q_L * Nat.card D_L * (Nat.card Q_L + 1) := by
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let H_L : Subgroup L := hyp.H.subgroupOf L
  let Q_L : Subgroup L := hyp.Q.subgroupOf L
  let D_L : Subgroup L := hyp.D.subgroupOf L
  let Λ : Type _ := ↥(fixedPoints X Ω)
  change Nat.card L =
    Nat.card Q_L * Nat.card D_L * (Nat.card Q_L + 1)
  have hXD : X ≤ hyp.D := hXV.trans hyp.V_le_D
  have hQcard : Nat.card Q_L = Nat.card ↥(hyp.Q ⊓ L) := by
    change Nat.card ↥(hyp.Q.subgroupOf L) = Nat.card ↥(hyp.Q ⊓ L)
    rw [← Subgroup.inf_subgroupOf_right hyp.Q L]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (K := L) inf_le_right).toEquiv
  have hDcard : Nat.card D_L = Nat.card ↥(hyp.D ⊓ L) := by
    change Nat.card ↥(hyp.D.subgroupOf L) = Nat.card ↥(hyp.D ⊓ L)
    rw [← Subgroup.inf_subgroupOf_right hyp.D L]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (K := L) inf_le_right).toEquiv
  have hHcard : Nat.card H_L = Nat.card ↥(hyp.H ⊓ L) := by
    change Nat.card ↥(hyp.H.subgroupOf L) = Nat.card ↥(hyp.H ⊓ L)
    rw [← Subgroup.inf_subgroupOf_right hyp.H L]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (K := L) inf_le_right).toEquiv
  have hcardH : Nat.card H_L = Nat.card Q_L * Nat.card D_L := by
    rw [hHcard, hQcard, hDcard]
    exact hyp.card_cH_eq hXD
  have hcardΛ : Nat.card Λ = Nat.card Q_L + 1 := by
    change Nat.card ↥(fixedPoints X Ω) = Nat.card Q_L + 1
    rw [Nat.card_coe_set_eq, hyp.ncard_fixedPoints hXD, hQcard]
  let a1 := hyp.centralizerHypothesisA1 hXV
  have h2 : IsMultiplyPretransitive L Λ 2 := a1.doubly_transitive
  have hpre : IsPretransitive L Λ :=
    isPretransitive_of_is_two_pretransitive
  have hidx : H_L.index = Nat.card Λ := by
    change a1.H.index = Nat.card Λ
    rw [a1.H_def]
    exact index_stabilizer_of_transitive L a1.basept
  have hmul : Nat.card H_L * H_L.index = Nat.card L :=
    H_L.card_mul_index
  rw [hcardH, hidx, hcardΛ] at hmul
  exact hmul.symm

/-- The A1 structure equation makes `C_Q(X)` contain a Sylow
`2`-subgroup of `C_G(X)`. -/
theorem exists_sylow_two_le_cQ {X : Subgroup G}
    (hXV : X ≤ hyp.V) :
    let L : Subgroup G := Subgroup.centralizer (X : Set G)
    let Q_L : Subgroup L := hyp.Q.subgroupOf L
    ∃ P : Sylow 2 L, (P : Subgroup L) ≤ Q_L := by
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let Q_L : Subgroup L := hyp.Q.subgroupOf L
  let D_L : Subgroup L := hyp.D.subgroupOf L
  change ∃ P : Sylow 2 L, (P : Subgroup L) ≤ Q_L
  have hXD : X ≤ hyp.D := hXV.trans hyp.V_le_D
  have h3 : 3 ≤ (fixedPoints X Ω).ncard :=
    hyp.three_le_ncard_fixedPoints_of_le_V hXV
  have hQcard : Nat.card Q_L = Nat.card ↥(hyp.Q ⊓ L) := by
    change Nat.card ↥(hyp.Q.subgroupOf L) = Nat.card ↥(hyp.Q ⊓ L)
    rw [← Subgroup.inf_subgroupOf_right hyp.Q L]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (K := L) inf_le_right).toEquiv
  have hDcard : Nat.card D_L = Nat.card ↥(hyp.D ⊓ L) := by
    change Nat.card ↥(hyp.D.subgroupOf L) = Nat.card ↥(hyp.D ⊓ L)
    rw [← Subgroup.inf_subgroupOf_right hyp.D L]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (K := L) inf_le_right).toEquiv
  have hQeven : Even (Nat.card Q_L) := by
    rw [hQcard]
    exact hyp.even_card_cQ hXD h3
  have hDodd : Odd (Nat.card D_L) := by
    rw [hDcard]
    exact hyp.D_odd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hQ0 : Nat.card Q_L ≠ 0 := Nat.card_pos.ne'
  have hodd : Odd (Nat.card D_L * (Nat.card Q_L + 1)) :=
    hDodd.mul (Even.add_one hQeven)
  have hm0 : Nat.card D_L * (Nat.card Q_L + 1) ≠ 0 :=
    fun h => by simp [h] at hodd
  have hfact : (Nat.card L).factorization 2 =
      (Nat.card Q_L).factorization 2 := by
    rw [hyp.card_centralizer_eq hXV, mul_assoc,
      Nat.factorization_mul hQ0 hm0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)), add_zero]
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 Q_L) := Sylow.nonempty
  have hcard : Nat.card ((P₀ : Subgroup Q_L).map Q_L.subtype) =
      2 ^ (Nat.card L).factorization 2 := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ Q_L.subtype
      Q_L.subtype_injective).toEquiv.symm, hfact]
    exact P₀.card_eq_multiplicity
  exact ⟨Sylow.ofCard _ hcard, by
    rw [Sylow.coe_ofCard]
    exact Subgroup.map_subtype_le _⟩

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c)**: once Lemma 1
shows that `C_Q(X)` is a `2`-group, the A1 structure equation makes it
a Sylow `2`-subgroup of `C_G(X)`. -/
theorem exists_sylow_two_eq_cQ_of_isPGroup
    {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hCQ : IsPGroup 2
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))) :
    ∃ P : Sylow 2 (Subgroup.centralizer (X : Set G)),
      (P : Subgroup (Subgroup.centralizer (X : Set G))) =
        hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)) := by
  obtain ⟨P, hP⟩ := hyp.exists_sylow_two_le_cQ hXV
  exact ⟨P, (P.is_maximal' hCQ hP).symm⟩

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c)**, residual transport.
If `C_Q(X)` is a Sylow `2`-subgroup of `L = C_G(X)`, then the preceding
center equality identifies the central quotient of `O^{2′}(L)` with
`O^{2′}(L / 𝒩(L))`. The Sylow hypothesis is the exact input still to be
supplied by the induction target; it is not stored in an opaque carrier. -/
noncomputable def centralizerResidualQuotientEquiv_of_sylow
    {X : Subgroup G} (hXV : X ≤ hyp.V)
    (P : Sylow 2 (Subgroup.centralizer (X : Set G)))
    (hP : (P : Subgroup (Subgroup.centralizer (X : Set G))) =
      hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) :
    let L : Subgroup G := Subgroup.centralizer (X : Set G)
    let H_L : Subgroup L := hyp.H.subgroupOf L
    ((Subgroup.primeComplementResidual 2 L) ⧸
        Subgroup.center (Subgroup.primeComplementResidual 2 L)) ≃*
      Subgroup.primeComplementResidual 2 (L ⧸ H_L.normalCore) := by
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let H_L : Subgroup L := hyp.H.subgroupOf L
  let Q_L : Subgroup L := hyp.Q.subgroupOf L
  change ((Subgroup.primeComplementResidual 2 L) ⧸
      Subgroup.center (Subgroup.primeComplementResidual 2 L)) ≃*
    Subgroup.primeComplementResidual 2 (L ⧸ H_L.normalCore)
  have hF : Subgroup.primeComplementResidual 2 L =
      Subgroup.normalClosure (Q_L : Set L) := by
    rw [Subgroup.primeComplementResidual_eq_normalClosure P, hP]
  apply Subgroup.primeComplementResidualQuotientEquiv H_L.normalCore
  rw [hF]
  exact hyp.normalCore_subgroupOf_normalClosure_cQ_eq_center hXV

/-- **Peterfalvi Part II, Ch. I §3 Proposition 1(c)**, residual
transport from the source input that `C_Q(X)` is a `2`-group.  The
Sylow witness and the identification
`O^{2′}(C_G(X)) = ⟨C_Q(X)^{C_G(X)}⟩` are constructed from A1 rather than
accepted as extra carrier fields. -/
noncomputable def centralizerResidualQuotientEquiv
    {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hCQ : IsPGroup 2
      ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))) :
    let L : Subgroup G := Subgroup.centralizer (X : Set G)
    let H_L : Subgroup L := hyp.H.subgroupOf L
    ((Subgroup.primeComplementResidual 2 L) ⧸
        Subgroup.center (Subgroup.primeComplementResidual 2 L)) ≃*
      Subgroup.primeComplementResidual 2 (L ⧸ H_L.normalCore) := by
  let hex := hyp.exists_sylow_two_eq_cQ_of_isPGroup hXV hCQ
  let P := Classical.choose hex
  have hP := Classical.choose_spec hex
  exact hyp.centralizerResidualQuotientEquiv_of_sylow hXV P hP
end

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
