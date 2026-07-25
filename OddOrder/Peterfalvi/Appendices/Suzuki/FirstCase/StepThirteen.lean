/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepTwelveTransfer

/-!
# Peterfalvi Part II, Ch. II, step (13): `C_G(Z₁)` is a `3`-group — preliminaries

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (13), p. 113.

The centralizer identities feeding the step (13) counting
`|C_G(Z₁)| = |C_G(Z₁) ∩ C_G(s)|·|J|`:

* `C_G(st) ∩ C_G(s) = C_G(t) ∩ C_G(s)` (elementary: `t = s⁻¹·(st)`);
* `C_G(t) ∩ C_G(s) = V` — an element commuting with `s` fixes the base point
  (the fixed points of `s ∈ Q` off the base point would violate the
  regularity of `Q` on `Ω − {basept}`), and commuting with `t` it then also
  fixes `t • basept`, so it lies in `D`; conversely `V = C_D(t) = C_D(s)`
  (Ch. I Prop 5).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

include hyp in
/-- Commuting with `s` and `st` is the same as commuting with `s` and `t`
(elementary: `t = s⁻¹·(st)`). -/
lemma centralizer_mul_t_inf_eq_centralizer_t_inf :
    Subgroup.centralizer {hyp.distinguishedInvolution * hyp.t}
        ⊓ Subgroup.centralizer {hyp.distinguishedInvolution}
      = Subgroup.centralizer {hyp.t}
        ⊓ Subgroup.centralizer {hyp.distinguishedInvolution} := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hst, hs⟩
    refine ⟨?_, hs⟩
    have h1 : Commute x (hyp.distinguishedInvolution⁻¹
        * (hyp.distinguishedInvolution * hyp.t)) :=
      (Commute.inv_right hs).mul_right hst
    rwa [inv_mul_cancel_left] at h1
  · rintro ⟨ht, hs⟩
    exact ⟨(Commute.mul_right hs ht : _), hs⟩

include hyp in
/-- **Step (13) preliminary** (p. 113): `C_G(t) ∩ C_G(s) = V`.

`⊆`: an element `x` commuting with `s` maps the base point to an `s`-fixed
point; since `s` is an involution of `H` it lies in `Q`, which acts freely on
`Ω − {basept}`, so `x` fixes the base point.  Commuting with `t` as well, `x`
also fixes `t • basept`, hence `x ∈ D ⊓ C_G(t) = V`.  `⊇`: `V = C_D(t)` by
definition and `V = C_D(s)` by Ch. I Prop 5. -/
lemma centralizer_t_inf_centralizer_eq_V :
    Subgroup.centralizer {hyp.t}
        ⊓ Subgroup.centralizer {hyp.distinguishedInvolution} = hyp.V := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxt0, hxs0⟩ := Subgroup.mem_inf.mp hx
    have hxt : Commute x hyp.t := Subgroup.mem_centralizer_singleton_iff.mp hxt0
    have hxs : Commute x hyp.distinguishedInvolution :=
      Subgroup.mem_centralizer_singleton_iff.mp hxs0
    have hsH := hyp.distinguishedInvolution_mem_H
    have hsQ : hyp.distinguishedInvolution ∈ hyp.Q :=
      hyp.mem_Q_of_sq_eq_one_of_mem_H hsH hyp.distinguishedInvolution_sq
    -- `x` fixes the base point
    have hxbase : x • hyp.basept = hyp.basept := by
      by_contra hne
      obtain ⟨q, hq⟩ := hyp.qRegularEquiv.surjective ⟨x • hyp.basept, hne⟩
      have hqval : (q : G) • (hyp.t • hyp.basept) = x • hyp.basept :=
        congrArg Subtype.val hq
      have hsfix : hyp.distinguishedInvolution • (x • hyp.basept)
          = x • hyp.basept := by
        rw [← mul_smul, ← hxs.eq, mul_smul, hyp.smul_basept_eq_of_mem_H hsH]
      have hsq : (hyp.distinguishedInvolution * (q : G))
          • (hyp.t • hyp.basept) = x • hyp.basept := by
        rw [mul_smul, hqval, hsfix]
      have he : hyp.qRegularEquiv
          ⟨hyp.distinguishedInvolution * (q : G), hyp.Q.mul_mem hsQ q.2⟩
          = hyp.qRegularEquiv q := by
        rw [hq]
        exact Subtype.ext hsq
      have hval : hyp.distinguishedInvolution * (q : G) = (q : G) :=
        congrArg Subtype.val (hyp.qRegularEquiv.injective he)
      apply hyp.distinguishedInvolution_ne_one
      have h1 : hyp.distinguishedInvolution * (q : G) = 1 * (q : G) := by
        rw [one_mul]
        exact hval
      exact mul_right_cancel h1
    -- `x` fixes `t • basept` as well, so `x ∈ D`
    have hxtb : x • (hyp.t • hyp.basept) = hyp.t • hyp.basept := by
      rw [← mul_smul, hxt.eq, mul_smul, hxbase]
    have hxD : x ∈ hyp.D := by
      rw [hyp.D_eq_stabilizer_inf]
      exact ⟨mem_stabilizer_iff.mpr hxbase, mem_stabilizer_iff.mpr hxtb⟩
    exact Subgroup.mem_inf.mpr ⟨hxD, hxt0⟩
  · intro v hv
    refine Subgroup.mem_inf.mpr ⟨hv.2, ?_⟩
    exact (hyp.V_le_centralizer_distinguishedInvolution hv).2

include hyp in
/-- The two identities combined: `C_G(st) ∩ C_G(s) = V` (p. 113). -/
lemma centralizer_mul_t_inf_centralizer_eq_V :
    Subgroup.centralizer {hyp.distinguishedInvolution * hyp.t}
        ⊓ Subgroup.centralizer {hyp.distinguishedInvolution} = hyp.V := by
  rw [hyp.centralizer_mul_t_inf_eq_centralizer_t_inf,
    hyp.centralizer_t_inf_centralizer_eq_V]

include hyp in
/-- `st` is strongly real (it is the product of the two involutions `s`
and `t`). -/
lemma isStronglyReal_distinguishedInvolution_mul_t :
    IsStronglyReal (hyp.distinguishedInvolution * hyp.t) :=
  ⟨hyp.distinguishedInvolution,
    ⟨hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_ne_one⟩,
    hyp.t, ⟨hyp.t_sq, hyp.t_ne_one⟩, rfl⟩

include hyp in
/-- `s` inverts `st` (`s·(st)·s = ts = (st)⁻¹`), hence normalizes its
centralizer. -/
lemma conj_mem_centralizer_mul_t (x : G)
    (hx : x ∈ Subgroup.centralizer {hyp.distinguishedInvolution * hyp.t}) :
    hyp.distinguishedInvolution * x * hyp.distinguishedInvolution
      ∈ Subgroup.centralizer {hyp.distinguishedInvolution * hyp.t} := by
  set s := hyp.distinguishedInvolution with hs_def
  set c : G := s * hyp.t with hc_def
  have hs2 : s * s = 1 := by rw [← sq]; exact hyp.distinguishedInvolution_sq
  have ht2 : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  -- `s c s = c⁻¹`
  have hinv : s * c * s = c⁻¹ := by
    have hL : s * c * s = hyp.t * s := by
      rw [hc_def]
      calc s * (s * hyp.t) * s = (s * s) * hyp.t * s := by group
        _ = hyp.t * s := by rw [hs2, one_mul]
    have hR : c⁻¹ = hyp.t * s := by
      rw [hc_def, mul_inv_rev, inv_eq_of_mul_eq_one_right ht2,
        inv_eq_of_mul_eq_one_right hs2]
    rw [hL, hR]
  have hsc : s * c = c⁻¹ * s := by
    calc s * c = s * c * (s * s) := by rw [hs2, mul_one]
      _ = (s * c * s) * s := by group
      _ = c⁻¹ * s := by rw [hinv]
  have hsc' : s * c⁻¹ = c * s := by
    have h1 : s * c⁻¹ * s = c := by
      have h2 := congrArg (fun y : G => y⁻¹) hinv
      simp only [mul_inv_rev, inv_inv] at h2
      rw [inv_eq_of_mul_eq_one_right hs2, ← mul_assoc] at h2
      exact h2
    calc s * c⁻¹ = s * c⁻¹ * (s * s) := by rw [hs2, mul_one]
      _ = (s * c⁻¹ * s) * s := by group
      _ = c * s := by rw [h1]
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  have hxc : Commute x c := hx
  have hxci : x * c⁻¹ = c⁻¹ * x := hxc.inv_right.eq
  calc s * x * s * c = s * x * (s * c) := by group
    _ = s * x * (c⁻¹ * s) := by rw [hsc]
    _ = s * (x * c⁻¹) * s := by group
    _ = s * (c⁻¹ * x) * s := by rw [hxci]
    _ = (s * c⁻¹) * (x * s) := by group
    _ = (c * s) * (x * s) := by rw [hsc']
    _ = c * (s * x * s) := by group

include hyp in
/-- **Step (13), the counting identity** (p. 113):
`|C_G(st)| = |V| · |J|` where `J = {x ∈ C_G(st) | sxs = x⁻¹}`.

This is Ch. I §1, the Lemma (a), applied to the involution `s` acting on the
odd-order group `C_G(st)` (odd by Ch. I §3, Lemma 3, since `st` is strongly
real and not an involution), together with `C_G(st) ∩ C_G(s) = V`. -/
theorem card_centralizer_mul_t_eq
    (hst2 : (hyp.distinguishedInvolution * hyp.t) ^ 2 ≠ 1) :
    Nat.card ↥(Subgroup.centralizer
        ({hyp.distinguishedInvolution * hyp.t} : Set G))
      = Nat.card ↥hyp.V *
        (invertedBy (Subgroup.centralizer
          ({hyp.distinguishedInvolution * hyp.t} : Set G))
          hyp.distinguishedInvolution).ncard := by
  have hs2 : hyp.distinguishedInvolution * hyp.distinguishedInvolution = 1 := by
    rw [← sq]; exact hyp.distinguishedInvolution_sq
  have hodd : Odd (Nat.card ↥(Subgroup.centralizer
      ({hyp.distinguishedInvolution * hyp.t} : Set G))) :=
    hyp.centralizer_natCard_odd_of_stronglyReal
      hyp.isStronglyReal_distinguishedInvolution_mul_t hst2
  have hkey := card_eq_card_centralizer_mul_ncard_invertedBy
    (X := Subgroup.centralizer ({hyp.distinguishedInvolution * hyp.t} : Set G))
    hs2 hodd hyp.conj_mem_centralizer_mul_t
  rwa [hyp.centralizer_mul_t_inf_centralizer_eq_V] at hkey

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
