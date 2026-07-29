/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.OrderFiveOrbits

/-!
# `(SK) ∪ (SKtS)` is a subgroup

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §2, p. 118:

> **Proposition.** If case (b) of the proposition of §1 holds, then
> `(SK) ∪ (SKtS)` is a subgroup of `G`.
> **Proof.** It suffices to show that `tSt ⊆ SKtS`.

Here `S = Q` (Theorem C).  The book's reduction is exactly
`h(x) ∈ K` for all `x ∈ S#` (`tConjMiddle_mem_K`), and this file turns that into
the closure of `(SK) ∪ (SKtS)`.  The two rewrites that do the work are

* `t u k t = g(u) h(u) t f(u) k⁻¹` for `1 ≠ u ∈ Q` (`h(u) ∈ K` is the input), and
* `t f k⁻¹ q = k · t · (k f k⁻¹ q)`, because `t` inverts `K`.

## Main results

* `Hypothesis.orderFiveCarrier` — the set `(SK) ∪ (SKtS)`.
* `Hypothesis.orderFiveSubgroup` — it is a subgroup, given `h(x) ∈ K`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- The set `(SK) ∪ (SKtS)` of Peterfalvi Part II, Ch. III §2, p. 118, with
`S = Q`.

Despite the name it is the carrier of *both* cases of §3's opening paragraph:
in case (b) of the Proposition of §1 it is `typeASubgroup` (this section), and
in case (a), where `S = Q₀`, it is `⟨Q₀, K, t⟩` of Ch. I §3 Lemma 4
(`coe_orderThreeGeneratedSubgroup_eq_orderFiveCarrier`). -/
def orderFiveCarrier : Set G :=
  {g | ∃ q ∈ hyp.Q, ∃ k ∈ hyp.K, g = q * k} ∪
    {g | ∃ q ∈ hyp.Q, ∃ k ∈ hyp.K, ∃ q' ∈ hyp.Q, g = q * k * hyp.t * q'}

lemma mem_KSet_of_mem_K {k : G} (hk : k ∈ hyp.K) : k ∈ hyp.KSet := by
  rw [← hyp.coe_K]; exact hk

lemma conj_mem_Q_of_mem_K {k : G} (hk : k ∈ hyp.K) {q : G} (hq : q ∈ hyp.Q) :
    k * q * k⁻¹ ∈ hyp.Q :=
  hyp.Q_normal_in_H k (hyp.D_le_H (hyp.K_le_D hk)) q hq

lemma conj_inv_mem_Q_of_mem_K {k : G} (hk : k ∈ hyp.K) {q : G} (hq : q ∈ hyp.Q) :
    k⁻¹ * q * k ∈ hyp.Q := by
  have := hyp.conj_mem_Q_of_mem_K (hyp.K.inv_mem hk) hq
  rwa [inv_inv] at this

/-- **`(SK) ∪ (SKtS)` is a subgroup** (Peterfalvi Part II, Ch. III §2, p. 118),
given the Proposition's content `h(x) ∈ K` for `x ∈ S#`. -/
def orderFiveSubgroup
    (hK : ∀ x ∈ hyp.Q, x ≠ 1 → hyp.tConjMiddle x ∈ hyp.K) : Subgroup G where
  carrier := hyp.orderFiveCarrier
  one_mem' := Or.inl ⟨1, hyp.Q.one_mem, 1, hyp.K.one_mem, (one_mul 1).symm⟩
  inv_mem' := by
    rintro g (⟨q, hq, k, hk, rfl⟩ | ⟨q, hq, k, hk, q', hq', rfl⟩)
    · refine Or.inl ⟨k⁻¹ * q⁻¹ * k, hyp.conj_inv_mem_Q_of_mem_K hk (hyp.Q.inv_mem hq),
        k⁻¹, hyp.K.inv_mem hk, ?_⟩
      group
    · refine Or.inr ⟨q'⁻¹, hyp.Q.inv_mem hq', k, hk, q⁻¹, hyp.Q.inv_mem hq, ?_⟩
      have hkey : hyp.t * k⁻¹ = k * hyp.t :=
        (hyp.mul_t_eq_of_mem_KSet (hyp.mem_KSet_of_mem_K hk)).symm
      calc (q * k * hyp.t * q')⁻¹ = q'⁻¹ * (hyp.t * k⁻¹) * q⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hyp.t_inv_eq]; group
        _ = q'⁻¹ * (k * hyp.t) * q⁻¹ := by rw [hkey]
        _ = q'⁻¹ * k * hyp.t * q⁻¹ := by group
  mul_mem' := by
    have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
    have htkt : ∀ k ∈ hyp.K, hyp.t * k * hyp.t = k⁻¹ := fun k hk =>
      (hyp.mem_KSet_of_mem_K hk).2
    have htki : ∀ k ∈ hyp.K, hyp.t * k⁻¹ * hyp.t = k := fun k hk => by
      simpa using (hyp.inv_mem_KSet (hyp.mem_KSet_of_mem_K hk)).2
    -- pulling `t` past `k` on either side
    have htkinv : ∀ k ∈ hyp.K, hyp.t * k⁻¹ = k * hyp.t := fun k hk =>
      (hyp.mul_t_eq_of_mem_KSet (hyp.mem_KSet_of_mem_K hk)).symm
    have htk' : ∀ k ∈ hyp.K, hyp.t * k = k⁻¹ * hyp.t := fun k hk =>
      hyp.t_mul_eq_of_mem_KSet (hyp.mem_KSet_of_mem_K hk)
    rintro g₁ g₂ (⟨q₁, hq₁, k₁, hk₁, rfl⟩ | ⟨q₁, hq₁, k₁, hk₁, q₂, hq₂, rfl⟩)
      (⟨q₃, hq₃, k₂, hk₂, rfl⟩ | ⟨q₃, hq₃, k₂, hk₂, q₄, hq₄, rfl⟩)
    · -- `(SK)(SK)`
      refine Or.inl ⟨q₁ * (k₁ * q₃ * k₁⁻¹), hyp.Q.mul_mem hq₁
        (hyp.conj_mem_Q_of_mem_K hk₁ hq₃), k₁ * k₂, hyp.K.mul_mem hk₁ hk₂, by group⟩
    · -- `(SK)(SKtS)`
      refine Or.inr ⟨q₁ * (k₁ * q₃ * k₁⁻¹), hyp.Q.mul_mem hq₁
        (hyp.conj_mem_Q_of_mem_K hk₁ hq₃), k₁ * k₂, hyp.K.mul_mem hk₁ hk₂,
        q₄, hq₄, by group⟩
    · -- `(SKtS)(SK)`
      refine Or.inr ⟨q₁, hq₁, k₁ * k₂⁻¹, hyp.K.mul_mem hk₁ (hyp.K.inv_mem hk₂),
        k₂⁻¹ * (q₂ * q₃) * k₂,
        hyp.conj_inv_mem_Q_of_mem_K hk₂ (hyp.Q.mul_mem hq₂ hq₃), ?_⟩
      calc q₁ * k₁ * hyp.t * q₂ * (q₃ * k₂)
          = q₁ * k₁ * (hyp.t * (q₂ * q₃) * k₂) := by group
        _ = q₁ * k₁ * ((hyp.t * k₂) * (k₂⁻¹ * (q₂ * q₃) * k₂)) := by group
        _ = q₁ * k₁ * ((k₂⁻¹ * hyp.t) * (k₂⁻¹ * (q₂ * q₃) * k₂)) := by
            rw [htk' k₂ hk₂]
        _ = q₁ * (k₁ * k₂⁻¹) * hyp.t * (k₂⁻¹ * (q₂ * q₃) * k₂) := by group
    · -- `(SKtS)(SKtS)`
      by_cases hu : q₂ * q₃ = 1
      · refine Or.inl ⟨q₁ * ((k₁ * k₂⁻¹) * q₄ * (k₁ * k₂⁻¹)⁻¹),
          hyp.Q.mul_mem hq₁ (hyp.conj_mem_Q_of_mem_K
            (hyp.K.mul_mem hk₁ (hyp.K.inv_mem hk₂)) hq₄),
          k₁ * k₂⁻¹, hyp.K.mul_mem hk₁ (hyp.K.inv_mem hk₂), ?_⟩
        calc q₁ * k₁ * hyp.t * q₂ * (q₃ * k₂ * hyp.t * q₄)
            = q₁ * k₁ * (hyp.t * (q₂ * q₃) * k₂ * hyp.t) * q₄ := by group
          _ = q₁ * k₁ * (hyp.t * k₂ * hyp.t) * q₄ := by rw [hu]; group
          _ = q₁ * (k₁ * k₂⁻¹) * q₄ := by rw [htkt k₂ hk₂]; group
          _ = q₁ * ((k₁ * k₂⁻¹) * q₄ * (k₁ * k₂⁻¹)⁻¹) * (k₁ * k₂⁻¹) := by group
      · set u : G := q₂ * q₃ with hudef
        have huQ : u ∈ hyp.Q := hyp.Q.mul_mem hq₂ hq₃
        have hgu := hyp.tConjLeft_mem huQ hu
        have hfu := hyp.tConjRight_mem huQ hu
        have hhu := hK u huQ hu
        have hut := hyp.t_conj_eq huQ hu
        refine Or.inr ⟨q₁ * (k₁ * hyp.tConjLeft u * k₁⁻¹),
          hyp.Q.mul_mem hq₁ (hyp.conj_mem_Q_of_mem_K hk₁ hgu),
          k₁ * hyp.tConjMiddle u * k₂,
          hyp.K.mul_mem (hyp.K.mul_mem hk₁ hhu) hk₂,
          k₂ * hyp.tConjRight u * k₂⁻¹ * q₄,
          hyp.Q.mul_mem (hyp.conj_mem_Q_of_mem_K hk₂ hfu) hq₄, ?_⟩
        calc q₁ * k₁ * hyp.t * q₂ * (q₃ * k₂ * hyp.t * q₄)
            = q₁ * k₁ * (hyp.t * u * hyp.t) * (hyp.t * k₂ * hyp.t) * q₄ := by
              rw [hudef]
              calc q₁ * k₁ * hyp.t * q₂ * (q₃ * k₂ * hyp.t * q₄)
                  = q₁ * k₁ * (hyp.t * (q₂ * q₃) * (hyp.t * hyp.t) * k₂ * hyp.t)
                      * q₄ := by rw [htt]; group
                _ = q₁ * k₁ * (hyp.t * (q₂ * q₃) * hyp.t) *
                      (hyp.t * k₂ * hyp.t) * q₄ := by group
          _ = q₁ * k₁ * (hyp.tConjLeft u * hyp.tConjMiddle u * hyp.t *
                hyp.tConjRight u) * k₂⁻¹ * q₄ := by rw [← hut, htkt k₂ hk₂]
          _ = q₁ * (k₁ * hyp.tConjLeft u * k₁⁻¹) * (k₁ * hyp.tConjMiddle u) *
                (hyp.t * hyp.tConjRight u * k₂⁻¹) * q₄ := by group
          _ = q₁ * (k₁ * hyp.tConjLeft u * k₁⁻¹) * (k₁ * hyp.tConjMiddle u) *
                (hyp.t * k₂⁻¹ * (k₂ * hyp.tConjRight u * k₂⁻¹)) * q₄ := by group
          _ = q₁ * (k₁ * hyp.tConjLeft u * k₁⁻¹) * (k₁ * hyp.tConjMiddle u) *
                (k₂ * hyp.t * (k₂ * hyp.tConjRight u * k₂⁻¹)) * q₄ := by
              rw [htkinv k₂ hk₂]
          _ = q₁ * (k₁ * hyp.tConjLeft u * k₁⁻¹) * (k₁ * hyp.tConjMiddle u * k₂) *
                hyp.t * (k₂ * hyp.tConjRight u * k₂⁻¹ * q₄) := by group

@[simp] lemma coe_orderFiveSubgroup
    (hK : ∀ x ∈ hyp.Q, x ≠ 1 → hyp.tConjMiddle x ∈ hyp.K) :
    ((hyp.orderFiveSubgroup hK : Subgroup G) : Set G) = hyp.orderFiveCarrier := rfl

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
