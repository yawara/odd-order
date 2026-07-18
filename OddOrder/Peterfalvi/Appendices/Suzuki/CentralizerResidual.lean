/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.SylowDecomposition
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerNormalizer

/-!
# Peterfalvi Part II, Ch. I §3: Proposition 1(c), centralizer residual

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, pp. 105–106.

This file contains the target-independent structural clauses of Proposition
1(c).  It proves that, once `C_Q(X)` is known to be a `2`-group, the
odd-order direct factor `Q₁` has trivial centralizer of `X`. It also proves
the source's center equality for the normal closure `⟨C_Q(X)^L⟩`; its
identification with `O^{2′}(L)` belongs to the subsequent induction bridge.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

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
end

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
