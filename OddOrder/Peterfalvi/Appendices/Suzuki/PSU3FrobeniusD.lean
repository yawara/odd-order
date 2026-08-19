/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3OrbitCount
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.TwoKSubgroups
import OddOrder.Isaacs.Ch06_FrobeniusActions.OddComplement

/-!
# Peterfalvi Part II, Ch. IV §2: `D` is a Frobenius complement

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §2, p. 129, in the proof of the Proposition:

> By [H], Kapitel V, Satz 8.15, the Sylow subgroups of `D` are cyclic.

That citation is Huppert's theorem on Frobenius complements, and the hypothesis it is
applied under is the Proposition's own: `D` acts without fixed points on `(Q/Q₀)^#`
(`Hypothesis.FreeD`).  Read on the central quotient `Q ⧸ Z(Q)` — which is `Q/Q₀` once
`Z(Q) = Q₀` — that says exactly that the conjugation action of `D` is a Frobenius action,
and Isaacs Cor 6.17 (`isZGroup_of_isFrobeniusAction_of_odd`) then gives the cyclicity,
`D` having odd order.

## Main results

* `Hypothesis.isFrobeniusAction_D_of_freeD` — §2's hypothesis *is* the statement that `D`
  acts as a Frobenius complement on `Q ⧸ Z(Q)`.
* `Hypothesis.isZGroup_D_of_freeD` — hence every Sylow subgroup of `D` is cyclic.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open OddOrder.Isaacs.Ch03 OddOrder.Isaacs.Ch06

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

include hyp

section /- Ch. IV §2: `D` is a Frobenius complement on `Q/Q₀` (p. 129) -/

/-- The conjugation action of `D` on `Q ⧸ Z(Q)`, as a `MulDistribMulAction`. -/
noncomputable instance conjQuotientDAction :
    MulDistribMulAction ↥hyp.D (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q) :=
  MulDistribMulAction.compHom _ (hyp.conjQuotientBy hyp.D_le_H)

/-- The action of `D` on `Q ⧸ Z(Q)` is conjugation, read on representatives. -/
theorem conjQuotientDAction_smul_mk (c : ↥hyp.D) (y : ↥hyp.Q) :
    (c • (y : ↥hyp.Q ⧸ Subgroup.center ↥hyp.Q))
      = ((⟨(c : G) * (y : G) * (c : G)⁻¹,
            hyp.Q_normal_in_H (c : G) (hyp.D_le_H c.2) (y : G) y.2⟩ : ↥hyp.Q)
          : ↥hyp.Q ⧸ Subgroup.center ↥hyp.Q) := by
  change (hyp.conjQuotientBy hyp.D_le_H c)
      (QuotientGroup.mk' (Subgroup.center ↥hyp.Q) y) = _
  rw [conjQuotientBy, IsAInvariant.quotientMulAutHom_apply_mk']
  rfl

/-- **§2's hypothesis is a Frobenius action** (Peterfalvi Part II, Ch. IV §2, p. 129).

`FreeD` says no non-trivial element of `D` fixes a non-trivial class of `Q/Q₀`; with
`Z(Q) = Q₀` the classes of `Q ⧸ Z(Q)` are those of `Q/Q₀`, so this is literally
`IsFrobeniusAction D (Q ⧸ Z(Q))`. -/
theorem isFrobeniusAction_D_of_freeD (hfree : hyp.FreeD)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q) :
    IsFrobeniusAction ↥hyp.D (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q) := by
  intro c hc u hu hfix
  refine hc ?_
  induction u using QuotientGroup.induction_on with
  | H x =>
    -- `u ≠ 1` says `x ∉ Q₀`
    have hmemZ : ∀ z : ↥hyp.Q,
        ((z : ↥hyp.Q ⧸ Subgroup.center ↥hyp.Q) = 1) ↔ (z : G) ∈ hyp.Q0 := by
      intro z
      rw [QuotientGroup.eq_one_iff, hZ]
      exact Subgroup.mem_subgroupOf
    have hxQ0 : (x : G) ∉ hyp.Q0 := fun hcon => hu ((hmemZ x).mpr hcon)
    -- the fixed-point equation, read in `G`
    rw [conjQuotientDAction_smul_mk hyp c x, QuotientGroup.eq, hZ,
      Subgroup.mem_subgroupOf] at hfix
    have hval : (x : G)⁻¹ * ((c : G) * (x : G) * (c : G)⁻¹) ∈ hyp.Q0 := by
      have hraw : (c : G) * ((x : G)⁻¹ * (c : G)⁻¹) * (x : G) ∈ hyp.Q0 := by
        simpa using hfix
      have hinv := hyp.Q0.inv_mem hraw
      have heq2 : ((c : G) * ((x : G)⁻¹ * (c : G)⁻¹) * (x : G))⁻¹
          = (x : G)⁻¹ * ((c : G) * (x : G) * (c : G)⁻¹) := by group
      rwa [heq2] at hinv
    have heq : ((c : G)⁻¹)⁻¹ * (x : G) * (c : G)⁻¹
        = (x : G) * ((x : G)⁻¹ * ((c : G) * (x : G) * (c : G)⁻¹)) := by
      rw [inv_inv]; group
    have hone : (c : G)⁻¹ = 1 := hfree x.2 hxQ0 (hyp.D.inv_mem c.2) hval heq
    exact Subtype.ext (by simpa using inv_eq_one.mp hone)

/-- **The Sylow subgroups of `D` are cyclic** (Peterfalvi Part II, Ch. IV §2, p. 129,
citing Huppert *Endliche Gruppen I*, Kapitel V, Satz 8.15).

`D` acts without fixed points on `(Q/Q₀)^#` and has odd order, so it is a Frobenius
complement of odd order — a `Z`-group by Isaacs Cor 6.17.  This is what the proof of §2's
Proposition uses to place the `p`-components of `h(ω) ζ⁻¹` inside `W`. -/
theorem isZGroup_D_of_freeD (hfree : hyp.FreeD)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    IsZGroup ↥hyp.D := by
  have : Nontrivial (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q) := by
    refine ⟨((⟨ω, hωQ⟩ : ↥hyp.Q) : ↥hyp.Q ⧸ Subgroup.center ↥hyp.Q), 1,
      fun hcon => hωQ0 ?_⟩
    rw [QuotientGroup.eq_one_iff, hZ, Subgroup.mem_subgroupOf] at hcon
    exact hcon
  exact isZGroup_of_isFrobeniusAction_of_odd (hyp.isFrobeniusAction_D_of_freeD hfree hZ)
    hyp.D_odd

end

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
