/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerResidual

/-!
# Peterfalvi Part II, Ch. I §3: the centralizer quotient hypothesis

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, pp. 106–107.

In Proposition 1(c), Peterfalvi puts `L = C_G(X)`, divides the induced
action of `L` on `Ω_X` by its kernel `𝒩(L)`, and applies induction to this
faithful quotient action. This file constructs the actual quotient action,
transports all of (A1), proves (A2), and transports the elementary abelian
four-subgroup required by (A3). No abstract quotient carrier is posited.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open MulAction
open scoped Pointwise

/-! Generic quotient action by the exact kernel. -/

section /- quotient-action support for §3 Proposition 1(c) -/

variable {A Λ : Type*} [Group A] [MulAction A Λ]

/-- The permutation representation factored through a normal subgroup
contained in the action kernel. -/
def quotientPermHom (N : Subgroup A) [N.Normal]
    (hN : N ≤ (MulAction.toPermHom A Λ).ker) :
    A ⧸ N →* Equiv.Perm Λ :=
  QuotientGroup.lift N (MulAction.toPermHom A Λ) hN

/-- The action on the same point set, factored through `A/N`. -/
@[reducible] def quotientMulAction (N : Subgroup A) [N.Normal]
    (hN : N ≤ (MulAction.toPermHom A Λ).ker) :
    MulAction (A ⧸ N) Λ :=
  MulAction.compHom Λ (quotientPermHom N hN)

/-- The quotient action agrees with the old action on representatives. -/
theorem quotient_smul_mk (N : Subgroup A) [N.Normal]
    (hN : N ≤ (MulAction.toPermHom A Λ).ker) (a : A) (x : Λ) :
    letI := quotientMulAction N hN
    (QuotientGroup.mk' N a) • x = a • x := by
  rfl

/-- Factoring by the exact action kernel produces a faithful action. -/
theorem quotientFaithfulSMul (N : Subgroup A) [N.Normal]
    (hN : N = (MulAction.toPermHom A Λ).ker) :
    letI := quotientMulAction N hN.le
    FaithfulSMul (A ⧸ N) Λ := by
  letI := quotientMulAction N hN.le
  have hinj : Function.Injective (quotientPermHom N hN.le) :=
    (QuotientGroup.injective_lift_iff N
      (MulAction.toPermHom A Λ) hN.le).mpr hN
  refine ⟨?_⟩
  intro a b hab
  apply hinj
  ext x
  exact hab x

/-- Multiple transitivity descends along the quotient map because the point
set is unchanged and every old group element has a quotient image with the
same action. -/
theorem quotientIsMultiplyPretransitive (N : Subgroup A) [N.Normal]
    (hN : N ≤ (MulAction.toPermHom A Λ).ker) (n : ℕ)
    (htrans : IsMultiplyPretransitive A Λ n) :
    letI := quotientMulAction N hN
    IsMultiplyPretransitive (A ⧸ N) Λ n := by
  letI := quotientMulAction N hN
  rw [isMultiplyPretransitive_iff] at htrans ⊢
  intro x y
  obtain ⟨a, ha⟩ := htrans x y
  refine ⟨QuotientGroup.mk' N a, ?_⟩
  exact ha

/-- An elementary abelian four-subgroup survives quotienting by an odd-order
kernel.  This is the exact transport needed for source hypothesis (A3). -/
theorem quotientTwoRankGeTwo_of_odd_kernel [Finite A]
    (N : Subgroup A) [N.Normal] (hNodd : Odd (Nat.card N))
    (hA3 : ∃ E : Subgroup A,
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    ∃ Ebar : Subgroup (A ⧸ N),
      Nat.card Ebar = 4 ∧ ∀ x ∈ Ebar, x ^ 2 = 1 := by
  let π : A →* A ⧸ N := QuotientGroup.mk' N
  obtain ⟨E, hEcard, hEsq⟩ := hA3
  let Ebar : Subgroup (A ⧸ N) := E.map π
  let f : E → Ebar := fun e =>
    ⟨π e, ⟨e, e.2, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    have hab' : π (a : A) = π (b : A) := congrArg Subtype.val hab
    have hquot : π ((a : A) * (b : A)⁻¹) = 1 := by
      rw [map_mul, map_inv, hab', mul_inv_cancel]
    have hN : (a : A) * (b : A)⁻¹ ∈ N :=
      (QuotientGroup.eq_one_iff _).mp hquot
    have hE : (a : A) * (b : A)⁻¹ ∈ E :=
      E.mul_mem a.2 (E.inv_mem b.2)
    have hsq : ((a : A) * (b : A)⁻¹) ^ 2 = 1 :=
      hEsq _ hE
    have hone : (a : A) * (b : A)⁻¹ = 1 :=
      eq_one_of_sq_eq_one_of_odd_card hNodd hN hsq
    exact Subtype.ext (mul_inv_eq_one.mp hone)
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hxy
  refine ⟨Ebar, ?_, ?_⟩
  · rw [← hEcard]
    exact (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
  · intro x hx
    obtain ⟨e, he, rfl⟩ := hx
    rw [← map_pow, hEsq e he, map_one]

/-- Hypothesis (A1) descends along quotienting by the exact action kernel
provided the kernel lies in `D`. -/
noncomputable def HypothesisA1.quotientOfKernel [Finite A]
    (h : HypothesisA1 A Λ) (N : Subgroup A) [N.Normal]
    (hN : N = (MulAction.toPermHom A Λ).ker) (hND : N ≤ h.D) :
    letI := quotientMulAction N hN.le
    HypothesisA1 (A ⧸ N) Λ := by
  let π : A →* A ⧸ N := QuotientGroup.mk' N
  let Hbar : Subgroup (A ⧸ N) := h.H.map π
  let Qbar : Subgroup (A ⧸ N) := h.Q.map π
  let Dbar : Subgroup (A ⧸ N) := h.D.map π
  let tbar : A ⧸ N := π h.t
  letI := quotientMulAction N hN.le
  have hDleH : h.D ≤ h.H := by
    rw [h.D_def]
    exact inf_le_left
  have hNleH : N ≤ h.H := hND.trans hDleH
  have hkerH : π.ker ≤ h.H := by
    simpa only [π, QuotientGroup.ker_mk'] using hNleH
  have hkerD : π.ker ≤ h.D := by
    simpa only [π, QuotientGroup.ker_mk'] using hND
  have mem_H_of_mk_mem (a : A) (ha : π a ∈ Hbar) : a ∈ h.H := by
    have ha' : a ∈ Hbar.comap π := ha
    rw [show Hbar.comap π = h.H by
      exact Subgroup.comap_map_eq_self hkerH] at ha'
    exact ha'
  have mem_D_of_mk_mem (a : A) (ha : π a ∈ Dbar) : a ∈ h.D := by
    have ha' : a ∈ Dbar.comap π := ha
    rw [show Dbar.comap π = h.D by
      exact Subgroup.comap_map_eq_self hkerD] at ha'
    exact ha'
  refine
    { basept := h.basept
      doubly_transitive :=
        quotientIsMultiplyPretransitive N hN.le 2 h.doubly_transitive
      H := Hbar
      Q := Qbar
      D := Dbar
      H_def := ?_
      t := tbar
      t_sq := ?_
      t_ne_one := ?_
      t_not_mem_H := ?_
      D_def := ?_
      Q_le_H := ?_
      Q_normal_in_H := ?_
      Q_inf_D_eq_bot := ?_
      Q_mul_D_eq_H := ?_
      Q_even := ?_
      D_odd := ?_ }
  · ext y
    constructor
    · intro hy
      obtain ⟨a, haH, rfl⟩ := hy
      rw [mem_stabilizer_iff]
      change π a • h.basept = h.basept
      rw [quotient_smul_mk]
      rw [← mem_stabilizer_iff, ← h.H_def]
      exact haH
    · intro hy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N y
      rw [mem_stabilizer_iff] at hy
      have haFix : a • h.basept = h.basept := by
        simpa only [quotient_smul_mk] using hy
      refine ⟨a, ?_, rfl⟩
      rw [h.H_def]
      exact MulAction.mem_stabilizer_iff.mpr haFix
  · change π (h.t ^ 2) = 1
    rw [h.t_sq, map_one]
  · intro ht
    apply h.t_not_mem_H
    apply hNleH
    exact (QuotientGroup.eq_one_iff _).mp ht
  · intro ht
    apply h.t_not_mem_H
    exact mem_H_of_mk_mem h.t ht
  · ext y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N y
    constructor
    · intro ha
      have haD : a ∈ h.D := mem_D_of_mk_mem a ha
      rw [h.D_def, Subgroup.mem_inf] at haD
      obtain ⟨haH, hatH⟩ := haD
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hatH
      refine Subgroup.mem_inf.mpr ⟨⟨a, haH, rfl⟩, ?_⟩
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
      refine ⟨h.t⁻¹ * a * h.t, hatH, ?_⟩
      simp only [tbar, π, map_mul, map_inv]
    · intro ha
      obtain ⟨haHbar, hatHbar⟩ := Subgroup.mem_inf.mp ha
      have haH : a ∈ h.H := mem_H_of_mk_mem a haHbar
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hatHbar
      have hatH : h.t⁻¹ * a * h.t ∈ h.H := by
        apply mem_H_of_mk_mem
        simpa only [tbar, π, map_mul, map_inv] using hatHbar
      refine ⟨a, ?_, rfl⟩
      rw [h.D_def]
      refine ⟨haH, ?_⟩
      apply Subgroup.mem_map_equiv.mpr
      simpa only [MulAut.conj_symm_apply] using hatH
  · exact Subgroup.map_mono h.Q_le_H
  · intro a ha q hq
    obtain ⟨a0, ha0, rfl⟩ := ha
    obtain ⟨q0, hq0, rfl⟩ := hq
    refine ⟨a0 * q0 * a0⁻¹, h.Q_normal_in_H a0 ha0 q0 hq0, ?_⟩
    simp only [π, map_mul, map_inv]
  · rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    obtain ⟨hyQ, hyD⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨q, hqQ, rfl⟩ := hyQ
    have hqD : q ∈ h.D := mem_D_of_mk_mem q hyD
    have hqbot : q ∈ h.Q ⊓ h.D := ⟨hqQ, hqD⟩
    rw [h.Q_inf_D_eq_bot, Subgroup.mem_bot] at hqbot
    rw [hqbot, map_one]
  · apply Set.Subset.antisymm
    · rintro y ⟨qbar, hqbar, dbar, hdbar, rfl⟩
      obtain ⟨q, hq, rfl⟩ := hqbar
      obtain ⟨d, hd, rfl⟩ := hdbar
      refine ⟨q * d, h.H.mul_mem (h.Q_le_H hq) (hDleH hd), ?_⟩
      simp only [π, map_mul]
    · intro y hy
      obtain ⟨a, haH, rfl⟩ := hy
      have haProd : a ∈ (h.Q : Set A) * (h.D : Set A) := by
        rw [h.Q_mul_D_eq_H]
        exact haH
      obtain ⟨q, hq, d, hd, rfl⟩ := haProd
      exact ⟨π q, ⟨q, hq, rfl⟩, π d, ⟨d, hd, rfl⟩, by
        simp only [π, map_mul]⟩
  · let f : h.Q → Qbar := fun q =>
      ⟨π q, ⟨q, q.2, rfl⟩⟩
    have hf_inj : Function.Injective f := by
      intro q r hqr
      have hqr' : π (q : A) = π (r : A) := congrArg Subtype.val hqr
      have hquot : π ((q : A) * (r : A)⁻¹) = 1 := by
        rw [map_mul, map_inv, hqr', mul_inv_cancel]
      have hmemN : (q : A) * (r : A)⁻¹ ∈ N :=
        (QuotientGroup.eq_one_iff _).mp hquot
      have hmemD : (q : A) * (r : A)⁻¹ ∈ h.D := hND hmemN
      have hmemQ : (q : A) * (r : A)⁻¹ ∈ h.Q :=
        h.Q.mul_mem q.2 (h.Q.inv_mem r.2)
      have hbot : (q : A) * (r : A)⁻¹ ∈ h.Q ⊓ h.D :=
        ⟨hmemQ, hmemD⟩
      rw [h.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
      exact Subtype.ext (mul_inv_eq_one.mp hbot)
    have hf_surj : Function.Surjective f := by
      intro y
      obtain ⟨q, hq, hqy⟩ := y.2
      exact ⟨⟨q, hq⟩, Subtype.ext hqy⟩
    have hcard : Nat.card Qbar = Nat.card h.Q :=
      (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
    rw [hcard]
    exact h.Q_even
  · exact h.D_odd.of_dvd_nat (Subgroup.card_map_dvd h.D π)

/-- Add (A2) and (A3) to an already constructed (A1) carrier. -/
def HypothesisA1.toHypothesis [Finite A] (h : HypothesisA1 A Λ)
    (hfaithful : FaithfulSMul A Λ)
    (hA3 : ∃ E : Subgroup A,
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    Hypothesis A Λ where
  basept := h.basept
  doubly_transitive := h.doubly_transitive
  faithful := hfaithful
  H := h.H
  Q := h.Q
  D := h.D
  H_def := h.H_def
  t := h.t
  t_sq := h.t_sq
  t_ne_one := h.t_ne_one
  t_not_mem_H := h.t_not_mem_H
  D_def := h.D_def
  Q_le_H := h.Q_le_H
  Q_normal_in_H := h.Q_normal_in_H
  Q_inf_D_eq_bot := h.Q_inf_D_eq_bot
  Q_mul_D_eq_H := h.Q_mul_D_eq_H
  Q_even := h.Q_even
  D_odd := h.D_odd
  two_rank_ge_two := hA3

end

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

section /- §3, Proposition 1(c): faithful centralizer quotient (pp. 106–107) -/

variable {X : Subgroup G}

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(c)** — the honest quotient carrier
`L/𝒩(L)`. -/
abbrev centralizerActionQuotient (X : Subgroup G) : Type _ :=
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  L ⧸ (hyp.H.subgroupOf L).normalCore

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(c)** — the permutation
representation of `L/N` on `Ω_X`. -/
noncomputable def centralizerQuotientPermHom (hXV : X ≤ hyp.V) :
    centralizerActionQuotient hyp X →*
      Equiv.Perm ↥(MulAction.fixedPoints X Ω) := by
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let N : Subgroup L := (hyp.H.subgroupOf L).normalCore
  exact quotientPermHom N (hyp.normalCore_cH_eq_restrictedAction_ker hXV).le

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(c)** — the action of `L/N` on `Ω_X`,
obtained by factoring the restricted `L`-action through its exact kernel. -/
@[reducible] noncomputable def centralizerQuotientMulAction (hXV : X ≤ hyp.V) :
    MulAction (centralizerActionQuotient hyp X)
      ↥(MulAction.fixedPoints X Ω) := by
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let N : Subgroup L := (hyp.H.subgroupOf L).normalCore
  exact quotientMulAction N (hyp.normalCore_cH_eq_restrictedAction_ker hXV).le

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(c)** — the full source hypothesis
(A1) for the faithful centralizer quotient.
Its structural subgroups are the images of `C_H(X)`, `C_Q(X)`, and
`C_D(X)`; no opaque quotient carrier is needed. -/
noncomputable def centralizerQuotientHypothesisA1 (hXV : X ≤ hyp.V) :
    letI := hyp.centralizerQuotientMulAction hXV
    HypothesisA1 (centralizerActionQuotient hyp X)
      ↥(MulAction.fixedPoints X Ω) := by
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let N : Subgroup L := (hyp.H.subgroupOf L).normalCore
  let D_L : Subgroup L := hyp.D.subgroupOf L
  have hND : N ≤ D_L := by
    dsimp only [N, D_L, L]
    rw [hyp.normalCore_cH_eq_centralizer_cQ hXV]
    exact inf_le_left
  letI := hyp.centralizerQuotientMulAction hXV
  exact (hyp.centralizerHypothesisA1 hXV).quotientOfKernel N
    (hyp.normalCore_cH_eq_restrictedAction_ker hXV) hND

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(c)** — the factored centralizer
action is faithful, i.e. source hypothesis (A2) for `L/N`. -/
theorem centralizerQuotient_faithful (hXV : X ≤ hyp.V) :
    letI := hyp.centralizerQuotientMulAction hXV
    FaithfulSMul (centralizerActionQuotient hyp X)
      ↥(MulAction.fixedPoints X Ω) := by
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let N : Subgroup L := (hyp.H.subgroupOf L).normalCore
  letI := hyp.centralizerQuotientMulAction hXV
  exact quotientFaithfulSMul N
    (hyp.normalCore_cH_eq_restrictedAction_ker hXV)

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(c)** — the factored centralizer
action remains doubly transitive, i.e. the action part of source hypothesis (A1). -/
theorem centralizerQuotient_doublyTransitive (hXV : X ≤ hyp.V) :
    letI := hyp.centralizerQuotientMulAction hXV
    IsMultiplyPretransitive (centralizerActionQuotient hyp X)
      ↥(MulAction.fixedPoints X Ω) 2 := by
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let N : Subgroup L := (hyp.H.subgroupOf L).normalCore
  letI := hyp.centralizerQuotientMulAction hXV
  exact quotientIsMultiplyPretransitive N
    (hyp.normalCore_cH_eq_restrictedAction_ker hXV).le 2
    (hyp.centralizer_isMultiplyPretransitive_two hXV)

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(c)** — source hypothesis (A3)
descends from the centralizer to its faithful
quotient: the action kernel lies in the odd-order subgroup `D_L`, so it
cannot meet an elementary abelian four-subgroup nontrivially. -/
theorem centralizerQuotient_twoRankGeTwo (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    ∃ Ebar : Subgroup (centralizerActionQuotient hyp X),
      Nat.card Ebar = 4 ∧ ∀ x ∈ Ebar, x ^ 2 = 1 := by
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let N : Subgroup L := (hyp.H.subgroupOf L).normalCore
  let D_L : Subgroup L := hyp.D.subgroupOf L
  have hNleD : N ≤ D_L := by
    dsimp only [N, D_L, L]
    rw [hyp.normalCore_cH_eq_centralizer_cQ hXV]
    exact inf_le_left
  have hDodd : Odd (Nat.card D_L) :=
    (hyp.centralizerHypothesisA1 hXV).D_odd
  have hNodd : Odd (Nat.card N) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hNleD)
  exact quotientTwoRankGeTwo_of_odd_kernel N hNodd hA3

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(c)** — the complete honest
(A1)--(A3) carrier for `L/N`. The only mathematical
input beyond `X ≤ V` is exactly Proposition 1(c)'s hypothesis that
`L = C_G(X)` has 2-rank at least two. -/
noncomputable def centralizerQuotientHypothesis (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    letI := hyp.centralizerQuotientMulAction hXV
    Hypothesis (centralizerActionQuotient hyp X)
      ↥(MulAction.fixedPoints X Ω) := by
  letI := hyp.centralizerQuotientMulAction hXV
  exact (hyp.centralizerQuotientHypothesisA1 hXV).toHypothesis
    (hyp.centralizerQuotient_faithful hXV)
    (hyp.centralizerQuotient_twoRankGeTwo hXV hA3)

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(c)** — the faithful quotient is
strictly smaller than the ambient group when
`X ≠ 1`, as required to invoke the source induction hypothesis. -/
theorem card_centralizerActionQuotient_lt (hXV : X ≤ hyp.V)
    (hX : X ≠ ⊥) :
    Nat.card (centralizerActionQuotient hyp X) < Nat.card G := by
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let N : Subgroup L := (hyp.H.subgroupOf L).normalCore
  have hLlt : L < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hLtop
    have hXcenter : X ≤ Subgroup.center G := by
      exact (Subgroup.centralizer_eq_top_iff_subset.mp hLtop)
    letI : X.Normal := ⟨by
      intro n hn g
      have hcomm : g * n = n * g :=
        Subgroup.mem_center_iff.mp (hXcenter hn) g
      have heq : g * n * g⁻¹ = n := by
        rw [hcomm, mul_inv_cancel_right]
      rw [heq]
      exact hn⟩
    have hXH : X ≤ hyp.H :=
      hXV.trans hyp.V_le_D |>.trans hyp.D_le_H
    have hXcore : X ≤ hyp.H.normalCore :=
      Subgroup.normal_le_normalCore.mpr hXH
    have hXbot : X ≤ ⊥ := by
      rw [← hyp.normalCore_H_eq_bot]
      exact hXcore
    exact hX (eq_bot_iff.mpr hXbot)
  obtain ⟨g, -, hgL⟩ := SetLike.exists_of_lt hLlt
  have hLcard : Nat.card L < Nat.card G :=
    Finite.card_subtype_lt hgL
  exact (Nat.card_le_card_of_surjective
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)).trans_lt hLcard

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(c)** — on quotient representatives,
the factored action is definitionally
the old restricted centralizer action. -/
theorem centralizerQuotient_smul_mk (hXV : X ≤ hyp.V)
    (l : Subgroup.centralizer (X : Set G))
    (w : ↥(MulAction.fixedPoints X Ω)) :
    letI := hyp.centralizerQuotientMulAction hXV
    (QuotientGroup.mk'
        (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore l) • w =
      l • w := by
  rfl

end

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
