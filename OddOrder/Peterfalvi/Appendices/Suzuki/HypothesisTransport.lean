/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.Basic

/-!
# Transporting the standing hypothesis along an isomorphism of actions

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §4, step (2) (p. 133).

Chapter IV §4 identifies `U/(P ∩ U)` with the standard `PSU(3, ℓ)` and then argues in the
model.  Two things have to cross that identification: the standing hypothesis itself, so
that §2/§3 can be run on either side, and the *universe*, because the concrete model lives
in `Type 0` while the ambient group of the induction lives wherever it lives — and
`TheoremAInductionBelow G Ω` quantifies over groups in `G`'s own universe.

`Hypothesis.ofMulEquiv` handles both: a group isomorphism together with an equivariant
bijection of the permuted sets carries (A1)–(A3) across, with no constraint relating the
universes of the source and target.

## Main results

* `Hypothesis.ofMulEquiv` — transport of the standing hypothesis along
  `e : A ≃* B` and an `e`-equivariant `f : Λ ≃ Λ'`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open MulAction
open scoped Pointwise

variable {A B : Type*} {Λ Λ' : Type*} [Group A] [Group B]
  [MulAction A Λ] [MulAction B Λ'] [Finite A] [Finite B]

/-- **Transport of the standing hypothesis along an isomorphism of actions.**

`e : A ≃* B` together with an `e`-equivariant bijection `f : Λ ≃ Λ'` carries every field
across: the subgroups by `Subgroup.map e`, the base point by `f`, and the distinguished
involution by `e`.  Injectivity of `e` is what keeps `Q ∩ D = 1`, `t ∉ H` and the two
order conditions intact. -/
noncomputable def ofMulEquiv (h : Hypothesis A Λ) (e : A ≃* B) (f : Λ ≃ Λ')
    (hf : ∀ (a : A) (l : Λ), f (a • l) = e a • f l) :
    Hypothesis B Λ' where
  basept := f h.basept
  doubly_transitive := by
    have hdt := h.doubly_transitive
    rw [isMultiplyPretransitive_iff] at hdt ⊢
    intro x y
    obtain ⟨a, ha⟩ := hdt (x.trans f.symm.toEmbedding) (y.trans f.symm.toEmbedding)
    refine ⟨e a, Function.Embedding.ext fun i => ?_⟩
    have hi := congrArg (fun z : Fin 2 ↪ Λ => f (z i)) ha
    simpa [hf] using hi
  faithful := ⟨by
    intro b₁ b₂ hb
    haveI := h.faithful
    have hA : ∀ l : Λ, e.symm b₁ • l = e.symm b₂ • l := by
      intro l
      apply f.injective
      rw [hf, hf, e.apply_symm_apply, e.apply_symm_apply]
      exact hb (f l)
    have hsymm : e.symm b₁ = e.symm b₂ := eq_of_smul_eq_smul hA
    have h2 := congrArg e hsymm
    rwa [e.apply_symm_apply, e.apply_symm_apply] at h2⟩
  H := h.H.map e.toMonoidHom
  Q := h.Q.map e.toMonoidHom
  D := h.D.map e.toMonoidHom
  H_def := by
    ext b
    rw [Subgroup.mem_map_equiv, h.H_def, mem_stabilizer_iff, mem_stabilizer_iff]
    constructor
    · intro hb
      have := congrArg f hb
      rwa [hf, e.apply_symm_apply] at this
    · intro hb
      apply f.injective
      rw [hf, e.apply_symm_apply]
      exact hb
  t := e h.t
  t_sq := by rw [← map_pow, h.t_sq, map_one]
  t_ne_one := by
    intro hcon
    exact h.t_ne_one (e.injective (by rw [hcon, map_one]))
  t_not_mem_H := by
    intro hcon
    rw [Subgroup.mem_map_equiv, e.symm_apply_apply] at hcon
    exact h.t_not_mem_H hcon
  D_def := by
    ext b
    have hmem : ∀ (K : Subgroup A) (y : B), y ∈ K.map e.toMonoidHom ↔ e.symm y ∈ K :=
      fun _ _ => Subgroup.mem_map_equiv
    rw [hmem, h.D_def, Subgroup.mem_inf, Subgroup.mem_inf, hmem,
      Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
      MulAut.conj_symm_apply, hmem]
    refine and_congr Iff.rfl ?_
    rw [show e.symm ((e h.t)⁻¹ * b * e h.t) = h.t⁻¹ * e.symm b * h.t from by
      simp only [map_mul, map_inv, e.symm_apply_apply]]
  Q_le_H := Subgroup.map_mono h.Q_le_H
  Q_normal_in_H := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨q, hq, rfl⟩
    exact ⟨a * q * a⁻¹, h.Q_normal_in_H a ha q hq, by simp⟩
  Q_inf_D_eq_bot := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨hQ, hD⟩ := Subgroup.mem_inf.mp hb
    rw [Subgroup.mem_map_equiv] at hQ hD
    have hbot : e.symm b ∈ h.Q ⊓ h.D := ⟨hQ, hD⟩
    rw [h.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
    rw [Subgroup.mem_bot, ← e.apply_symm_apply b, hbot, map_one]
  Q_mul_D_eq_H := by
    ext b
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, _, ⟨d, hd, rfl⟩, rfl⟩
      have hqd : q * d ∈ (h.H : Set A) := by
        rw [← h.Q_mul_D_eq_H]; exact ⟨q, hq, d, hd, rfl⟩
      exact ⟨q * d, hqd, by simp⟩
    · rintro ⟨a, ha, rfl⟩
      have hprod : a ∈ (h.Q : Set A) * (h.D : Set A) := by
        rw [h.Q_mul_D_eq_H]; exact ha
      obtain ⟨q, hq, d, hd, rfl⟩ := hprod
      exact ⟨e q, ⟨q, hq, rfl⟩, e d, ⟨d, hd, rfl⟩, by simp⟩
  Q_even := by
    rw [Nat.card_congr
      (Subgroup.equivMapOfInjective h.Q e.toMonoidHom e.injective).toEquiv.symm]
    exact h.Q_even
  D_odd := by
    rw [Nat.card_congr
      (Subgroup.equivMapOfInjective h.D e.toMonoidHom e.injective).toEquiv.symm]
    exact h.D_odd
  two_rank_ge_two := by
    obtain ⟨E, hE4, hEsq⟩ := h.two_rank_ge_two
    refine ⟨E.map e.toMonoidHom, ?_, ?_⟩
    · rwa [Nat.card_congr
        (Subgroup.equivMapOfInjective E e.toMonoidHom e.injective).toEquiv.symm]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hEsq x hx, map_one]

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
