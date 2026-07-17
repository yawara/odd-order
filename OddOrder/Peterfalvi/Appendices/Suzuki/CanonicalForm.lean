/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.InvolutionClass

/-!
# Peterfalvi Part II, Ch. I §1: the canonical form (Prop 4)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §1, p. 101.

Proposition 4 of Ch. I §1:

* (a) every `g ∈ G - H` can be written in a unique way as `g = x t y` with
  `x ∈ H` and `y ∈ Q` — the *canonical form* of `g`;
* (b) there is a unique pair `(s, r)` with `tst = r⁻¹tr`, `s ∈ H ∩ I`,
  `r ∈ Q` — `s` is the *distinguished involution* of `Q` and
  `tst = r⁻¹tr` the *structure equation* of `G`.

Part (c) (the quotient `G/𝒩(G)` again satisfies (A1)) is deferred to a
later leaf.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open MulAction

open scoped Pointwise

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## Proposition 4 (a): the canonical form -/

/-- `H = DQ` as sets (from `H = QD` and normality of `Q` in `H`). -/
lemma D_mul_Q_eq_H :
    (hyp.D : Set G) * (hyp.Q : Set G) = (hyp.H : Set G) := by
  ext h
  constructor
  · rintro ⟨d, hd, q, hq, rfl⟩
    exact mul_mem (hyp.D_le_H hd) (hyp.Q_le_H hq)
  · intro hh
    have h2 : h ∈ (hyp.Q : Set G) * (hyp.D : Set G) := by
      rw [hyp.Q_mul_D_eq_H]
      exact hh
    obtain ⟨q, hq, d, hd, rfl⟩ := h2
    exact ⟨d, hd, d⁻¹ * q * d⁻¹⁻¹,
      hyp.Q_normal_in_H d⁻¹ (inv_mem (hyp.D_le_H hd)) q hq, by group⟩

/-- **Peterfalvi Part II, Ch. I Prop 4 (a)** (p. 101), existence — every
`g ∉ H` can be written `g = x t y` with `x ∈ H`, `y ∈ Q`
(`G - H = HtH = HtQ`). -/
lemma exists_canonicalForm {g : G} (hg : g ∉ hyp.H) :
    ∃ x ∈ hyp.H, ∃ y ∈ hyp.Q, g = x * hyp.t * y := by
  have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  -- `g ∈ HtH` via the dictionary
  have hgω : g • hyp.basept ≠ hyp.basept :=
    hyp.smul_basept_ne_of_not_mem_H hg
  have htω : hyp.t • hyp.basept ≠ hyp.basept :=
    hyp.smul_basept_ne_of_not_mem_H hyp.t_not_mem_H
  obtain ⟨h₁, hh₁, hsmul⟩ := hyp.exists_mem_H_smul_eq htω hgω
  have hfix : ((h₁ * hyp.t)⁻¹ * g) • hyp.basept = hyp.basept := by
    have h2 : (h₁ * hyp.t) • hyp.basept = g • hyp.basept := by
      rw [mul_smul, hsmul]
    calc ((h₁ * hyp.t)⁻¹ * g) • hyp.basept
        = (h₁ * hyp.t)⁻¹ • g • hyp.basept := by rw [mul_smul]
      _ = (h₁ * hyp.t)⁻¹ • (h₁ * hyp.t) • hyp.basept := by rw [h2]
      _ = hyp.basept := inv_smul_smul _ _
  have hh₂ : (h₁ * hyp.t)⁻¹ * g ∈ hyp.H :=
    hyp.H_def ▸ mem_stabilizer_iff.mpr hfix
  -- decompose the `H`-part as `d y` and slide `d` across `t`
  have hmem : (h₁ * hyp.t)⁻¹ * g ∈ (hyp.D : Set G) * (hyp.Q : Set G) := by
    rw [hyp.D_mul_Q_eq_H]
    exact hh₂
  obtain ⟨d, hd, y, hy, hdy⟩ := hmem
  have htdt : hyp.t * d * hyp.t ∈ hyp.D := by
    have h3 := hyp.t_conj_mem_D hd
    rwa [hyp.t_inv_eq] at h3
  refine ⟨h₁ * (hyp.t * d * hyp.t), mul_mem hh₁ (hyp.D_le_H htdt), y, hy, ?_⟩
  have hg2 : g = h₁ * hyp.t * (d * y) := by
    have h3 := congrArg (fun z : G => (h₁ * hyp.t) * z) hdy
    simpa [mul_assoc] using h3.symm
  rw [hg2]
  calc h₁ * hyp.t * (d * y) = h₁ * (hyp.t * d) * y := by group
    _ = h₁ * (hyp.t * d * (hyp.t * hyp.t)) * y := by rw [htt, mul_one]
    _ = h₁ * (hyp.t * d * hyp.t) * hyp.t * y := by group

/-- **Peterfalvi Part II, Ch. I Prop 4 (a)** (p. 101), uniqueness — the
canonical form `g = x t y` (`x ∈ H`, `y ∈ Q`) is unique
(`H^t ∩ Q ≤ D ∩ Q = 1`). -/
lemma canonicalForm_unique {x₁ y₁ x₂ y₂ : G} (hx₁ : x₁ ∈ hyp.H)
    (hy₁ : y₁ ∈ hyp.Q) (hx₂ : x₂ ∈ hyp.H) (hy₂ : y₂ ∈ hyp.Q)
    (heq : x₁ * hyp.t * y₁ = x₂ * hyp.t * y₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  -- `x₂⁻¹x₁ = t (y₂y₁⁻¹) t⁻¹`
  have h2 : x₂⁻¹ * x₁ = hyp.t * (y₂ * y₁⁻¹) * hyp.t⁻¹ := by
    have h4 : x₂⁻¹ * x₁ * hyp.t = hyp.t * (y₂ * y₁⁻¹) := by
      calc x₂⁻¹ * x₁ * hyp.t
          = x₂⁻¹ * (x₁ * hyp.t * y₁) * y₁⁻¹ := by group
        _ = x₂⁻¹ * (x₂ * hyp.t * y₂) * y₁⁻¹ := by rw [heq]
        _ = hyp.t * (y₂ * y₁⁻¹) := by group
    have h5 := congrArg (fun z : G => z * hyp.t⁻¹) h4
    simpa [mul_assoc] using h5
  -- hence `y₂y₁⁻¹ ∈ Q ∩ D = 1`
  have hzQ : y₂ * y₁⁻¹ ∈ hyp.Q := hyp.Q.mul_mem hy₂ (hyp.Q.inv_mem hy₁)
  have hzD : y₂ * y₁⁻¹ ∈ hyp.D := by
    rw [hyp.mem_D_iff]
    refine ⟨hyp.Q_le_H hzQ, ?_⟩
    rw [hyp.t_inv_eq] at h2 ⊢
    rw [← h2]
    exact mul_mem (inv_mem hx₂) hx₁
  have hbot : y₂ * y₁⁻¹ ∈ hyp.Q ⊓ hyp.D := ⟨hzQ, hzD⟩
  rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
  have hy : y₁ = y₂ := (mul_inv_eq_one.mp hbot).symm
  subst hy
  exact ⟨mul_right_cancel (mul_right_cancel heq), rfl⟩

/-- **Peterfalvi Part II, Ch. I Prop 4 (a)** (p. 101), packaged — the
canonical form as a unique-existence statement. -/
theorem existsUnique_canonicalForm {g : G} (hg : g ∉ hyp.H) :
    ∃! p : G × G, p.1 ∈ hyp.H ∧ p.2 ∈ hyp.Q ∧ g = p.1 * hyp.t * p.2 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hyp.exists_canonicalForm hg
  refine ⟨(x, y), ⟨hx, hy, hxy⟩, ?_⟩
  rintro ⟨x', y'⟩ ⟨hx', hy', hxy'⟩
  have h2 := hyp.canonicalForm_unique hx' hy' hx hy (hxy'.symm.trans hxy)
  exact Prod.ext h2.1 h2.2

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
