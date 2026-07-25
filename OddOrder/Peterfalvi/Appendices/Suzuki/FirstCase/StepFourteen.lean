/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepThirteen

/-!
# Peterfalvi Part II, Ch. II, step (14): the centre of `RΣ`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (14), p. 113.

In the notation of (11) (`R` the preimage of the near-field `F`, `T = [R, s]`,
`Σ = C_W(P)`, `Z₁ = ⟨st⟩`):

* `Z₁P ≤ Z(RΣ)`: `R` is abelian and contains both `Z₁` (by the "`Z₁ ⊂ T`"
  remark) and `P`; and `Σ` centralizes `P` by definition, while `Σ ≤ W ≤ V`
  centralizes both `s` (Ch. I Prop 5) and `t` (definition of `V`), hence `st`.
-/

set_option autoImplicit false

open scoped Pointwise

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)
  {F : Type uG} [NearFields.NearField F]
  (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.AffineNearFieldModel fc.rankOneQuotient F)

include fc in
/-- `Σ = C_W(P)` centralizes the distinguished involution `s`: `Σ ≤ W ≤ V` and
`V = C_D(s)` (Ch. I Prop 5). -/
lemma centralizer_W_le_centralizer_distinguishedInvolution :
    fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)
      ≤ Subgroup.centralizer
        ({fc.toHypothesis.distinguishedInvolution} : Set G) := by
  intro w hw
  have hwV : w ∈ fc.toHypothesis.V := fc.toHypothesis.W_le_V hw.1
  exact (fc.toHypothesis.V_le_centralizer_distinguishedInvolution hwV).2

include fc in
/-- `Σ` centralizes `st`: it centralizes `s` (above) and `t` (as `Σ ≤ V = C_D(t)`). -/
lemma centralizer_W_le_centralizer_distinguishedInvolution_mul_t :
    fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)
      ≤ Subgroup.centralizer
        ({fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t}
          : Set G) := by
  intro w hw
  have hws : Commute w fc.toHypothesis.distinguishedInvolution :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (fc.centralizer_W_le_centralizer_distinguishedInvolution hw)
  have hwt : Commute w fc.toHypothesis.t :=
    fc.toHypothesis.commute_t_of_mem_V (fc.toHypothesis.W_le_V hw.1)
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hws.mul_right hwt)

include model in
/-- **`Z₁P ≤ Z(RΣ)`** ((14), p. 113; the centre is taken inside `G`, i.e. as
`RΣ ⊓ C_G(RΣ)`).

`Z₁ ≤ T ≤ R` and `P ≤ R` with `R` abelian, so `Z₁P` centralizes `R`; and `Σ`
centralizes `P` by definition and `st` because `Σ ≤ V = C_D(s) = C_D(t)`. -/
theorem zpowers_mul_t_sup_P_le_center_sup
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) ⊔ fc.P
      ≤ (fc.invImageF model
            ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)))
        ⊓ Subgroup.centralizer
          (((fc.invImageF model
            ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)))
              : Subgroup G) : Set G) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  set R : Subgroup G := fc.invImageF model with hR_def
  set Sg : Subgroup G :=
    fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G) with hSg_def
  have hZ₁R : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ≤ R :=
    (fc.zpowers_distinguishedInvolution_mul_t_le_sInvertedT model ind hB2 hm).trans
      (fc.sInvertedT_spec model ind hB2 hm).1
  have hPR : fc.P ≤ R := fc.P_le_invImageF model
  have habR := fc.invImageF_mul_comm model ind hB2 hm
  -- both generators of `Z₁P` centralize `R` and `Σ`
  have hcent : ∀ z ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ⊔ fc.P, z ∈ Subgroup.centralizer ((R ⊔ Sg : Subgroup G) : Set G) := by
    intro z hz
    have hzR : z ∈ R := sup_le hZ₁R hPR hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    -- `x = r·σ` with `r ∈ R`, `σ ∈ Σ`
    have hx' : x ∈ ((R : Set G) * (Sg : Set G)) := by
      rw [← fc.coe_sup_invImageF_centralizer_W model]
      exact hx
    obtain ⟨r, hr, w, hw, rfl⟩ := hx'
    -- `z` commutes with `r` (both in the abelian `R`)
    have hzr : z * r = r * z := habR z hzR r hr
    -- `z` commutes with `w ∈ Σ`
    have hzw : z * w = w * z := by
      have hzcw : z ∈ Subgroup.centralizer (Sg : Set G) := by
        refine (sup_le ?_ ?_ : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t) ⊔ fc.P ≤ Subgroup.centralizer (Sg : Set G)) hz
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
          intro y hy
          exact Subgroup.mem_centralizer_singleton_iff.mp
            (fc.centralizer_W_le_centralizer_distinguishedInvolution_mul_t hy)
        · intro y hy
          rw [Subgroup.mem_centralizer_iff]
          intro c hc
          exact (Subgroup.mem_centralizer_iff.mp hc.2 y hy).symm
      exact (Subgroup.mem_centralizer_iff.mp hzcw w hw).symm
    calc r * w * z = r * (w * z) := by group
      _ = r * (z * w) := by rw [hzw]
      _ = (r * z) * w := by group
      _ = (z * r) * w := by rw [hzr]
      _ = z * (r * w) := by group
  refine le_inf ?_ (fun z hz => hcent z hz)
  exact sup_le (hZ₁R.trans le_sup_left) (hPR.trans le_sup_left)

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
