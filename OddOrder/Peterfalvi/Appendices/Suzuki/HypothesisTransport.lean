/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.QStructure
import OddOrder.Peterfalvi.Appendices.Suzuki.DistinguishedInvolution

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
* `Hypothesis.ofMulEquivPullback` — the special case where only the group moves and the
  action is pulled back along the isomorphism.
* `Hypothesis.ofMulEquiv_V`, `Hypothesis.ofMulEquiv_KSet`,
  `Hypothesis.ofMulEquiv_W`, `Hypothesis.ofMulEquiv_Q0`,
  `Hypothesis.ofMulEquiv_distinguishedInvolution` — the *derived* data
  transport too.  `H`, `Q`, `D` and `t` are fields, so they cross by `rfl`; `V`, `K`,
  `W` and `Q₀` are defined from them and need these lemmas.
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

omit [Finite A] [Finite B] in
/-- An isomorphism carries centralizers to centralizers. -/
theorem map_centralizer_equiv (e : A ≃* B) (S : Set A) :
    (Subgroup.centralizer S).map e.toMonoidHom = Subgroup.centralizer (e '' S) := by
  ext b
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro hb _ ⟨a, ha, rfl⟩
    have := hb a ha
    have h2 := congrArg e this
    rwa [map_mul, map_mul, e.apply_symm_apply] at h2
  · intro hb a ha
    have := hb (e a) ⟨a, ha, rfl⟩
    have h2 := congrArg e.symm this
    rwa [map_mul, map_mul, e.symm_apply_apply] at h2

omit [Finite A] [Finite B] in
/-- An isomorphism commutes with intersections of subgroups. -/
theorem map_inf_equiv (e : A ≃* B) (K L : Subgroup A) :
    (K ⊓ L).map e.toMonoidHom = K.map e.toMonoidHom ⊓ L.map e.toMonoidHom := by
  ext b
  simp only [Subgroup.mem_map_equiv, Subgroup.mem_inf]

variable (h : Hypothesis A Λ) (e : A ≃* B) (f : Λ ≃ Λ')
  (hf : ∀ (a : A) (l : Λ), f (a • l) = e a • f l)

@[simp] theorem ofMulEquiv_H : (h.ofMulEquiv e f hf).H = h.H.map e.toMonoidHom := rfl

@[simp] theorem ofMulEquiv_Q : (h.ofMulEquiv e f hf).Q = h.Q.map e.toMonoidHom := rfl

@[simp] theorem ofMulEquiv_D : (h.ofMulEquiv e f hf).D = h.D.map e.toMonoidHom := rfl

@[simp] theorem ofMulEquiv_t : (h.ofMulEquiv e f hf).t = e h.t := rfl

/-- `V = C_D(t)` transports. -/
theorem ofMulEquiv_V : (h.ofMulEquiv e f hf).V = h.V.map e.toMonoidHom := by
  rw [Hypothesis.V, Hypothesis.V, map_inf_equiv, map_centralizer_equiv,
    Set.image_singleton]
  rfl

/-- `K = {x ∈ D | xᵗ = x⁻¹}` transports. -/
theorem ofMulEquiv_KSet : (h.ofMulEquiv e f hf).KSet = e '' h.KSet := by
  have ht : (h.ofMulEquiv e f hf).t = e h.t := rfl
  ext b
  constructor
  · rintro ⟨hD, hinv⟩
    rw [ht] at hinv
    refine ⟨e.symm b, ⟨?_, ?_⟩, e.apply_symm_apply b⟩
    · exact Subgroup.mem_map_equiv.mp hD
    · have h2 := congrArg e.symm hinv
      simpa only [map_mul, map_inv, e.symm_apply_apply] using h2
  · rintro ⟨a, ⟨haD, hainv⟩, rfl⟩
    refine ⟨Subgroup.mem_map_equiv.mpr (by rwa [e.symm_apply_apply]), ?_⟩
    rw [ht]
    have h2 := congrArg e hainv
    simpa only [map_mul, map_inv] using h2

/-- `W = C_V(K)` transports. -/
theorem ofMulEquiv_W : (h.ofMulEquiv e f hf).W = h.W.map e.toMonoidHom := by
  rw [Hypothesis.W, Hypothesis.W, map_inf_equiv, ofMulEquiv_V, map_centralizer_equiv,
    ofMulEquiv_KSet]

/-- `Q₀`, the involutions of `H` together with `1`, transports. -/
theorem ofMulEquiv_Q0 : (h.ofMulEquiv e f hf).Q0 = h.Q0.map e.toMonoidHom := by
  ext b
  rw [(h.ofMulEquiv e f hf).mem_Q0_iff, Subgroup.mem_map_equiv, h.mem_Q0_iff,
    ofMulEquiv_H, Subgroup.mem_map_equiv]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro hb
    have h2 := congrArg e.symm hb
    rwa [map_pow, map_one] at h2
  · intro hb
    have h2 := congrArg e hb
    rwa [map_pow, map_one, e.apply_symm_apply] at h2

/-- The distinguished involution transports.

`distinguishedInvolution` is a `Classical.choose`, so it cannot be computed through the
transport; instead `(e s, e r)` is checked against the defining conditions and uniqueness
(`eq_distinguishedPair_of_structure`) identifies it. -/
theorem ofMulEquiv_distinguishedInvolution :
    (h.ofMulEquiv e f hf).distinguishedInvolution = e h.distinguishedInvolution := by
  have ht : (h.ofMulEquiv e f hf).t = e h.t := rfl
  refine (((h.ofMulEquiv e f hf).eq_distinguishedPair_of_structure
    (s' := e h.distinguishedInvolution) (r' := e h.structureConjugator)
    (Subgroup.mem_map_of_mem _ h.distinguishedInvolution_mem_H) ?_ ?_
    (Subgroup.mem_map_of_mem _ h.distinguishedPair_spec.2.1) ?_).1).symm
  · rw [← map_pow, h.distinguishedInvolution_sq, map_one]
  · intro hcon
    exact h.distinguishedInvolution_ne_one (e.injective (by rw [hcon, map_one]))
  · rw [ht]
    simpa only [map_mul, map_inv] using congrArg e h.distinguishedPair_spec.2.2

/-- `|s t| = 3` transports. -/
theorem ofMulEquiv_orderOf_distinguishedInvolution_mul_t :
    orderOf ((h.ofMulEquiv e f hf).distinguishedInvolution * (h.ofMulEquiv e f hf).t)
      = orderOf (h.distinguishedInvolution * h.t) := by
  rw [ofMulEquiv_distinguishedInvolution, show (h.ofMulEquiv e f hf).t = e h.t from rfl,
    ← map_mul]
  exact orderOf_injective e.toMonoidHom e.injective _

/-- `V = W` transports. -/
theorem ofMulEquiv_V_eq_W (hVW : h.V = h.W) :
    (h.ofMulEquiv e f hf).V = (h.ofMulEquiv e f hf).W := by
  rw [ofMulEquiv_V, ofMulEquiv_W, hVW]

/-- `|Q₀|` transports. -/
theorem ofMulEquiv_natCard_Q0 :
    Nat.card ((h.ofMulEquiv e f hf).Q0) = Nat.card (h.Q0) := by
  rw [ofMulEquiv_Q0]
  exact (Nat.card_congr
    (Subgroup.equivMapOfInjective h.Q0 e.toMonoidHom e.injective).toEquiv).symm

/-- `|Q|` transports. -/
theorem ofMulEquiv_natCard_Q :
    Nat.card ((h.ofMulEquiv e f hf).Q) = Nat.card (h.Q) :=
  (Nat.card_congr
    (Subgroup.equivMapOfInjective h.Q e.toMonoidHom e.injective).toEquiv).symm

/-- A non-trivial element of `W` transports. -/
theorem ofMulEquiv_exists_ne_one_mem_W (hw : ∃ w ∈ h.W, w ≠ 1) :
    ∃ w ∈ (h.ofMulEquiv e f hf).W, w ≠ 1 := by
  obtain ⟨w, hwW, hw1⟩ := hw
  refine ⟨e w, ?_, ?_⟩
  · rw [ofMulEquiv_W]
    exact Subgroup.mem_map_of_mem _ hwW
  · intro hcon
    exact hw1 (e.injective (by rw [hcon, map_one]))

/-- **Transport along a group isomorphism alone**, pulling the action back along `e`.

This is the form Ch. IV §4 needs: the standard model's permutation action is carried to
`U/Z(U)` along `residualQuotientEquiv`, so that the ambient induction hypothesis — which
quantifies over groups in the *ambient* universe — becomes applicable to it.  The permuted
set does not move, only the group acting on it. -/
noncomputable def ofMulEquivPullback (h : Hypothesis A Λ) (e : A ≃* B) :
    letI := MulAction.compHom Λ e.symm.toMonoidHom
    Hypothesis B Λ := by
  letI := MulAction.compHom Λ e.symm.toMonoidHom
  refine h.ofMulEquiv e (Equiv.refl Λ) fun a l => ?_
  change a • l = (e.symm (e a)) • l
  rw [e.symm_apply_apply]

/-! ### The transported facts, for the pullback form

`ofMulEquivPullback` fixes its equivariance proof internally, so the general
`ofMulEquiv_*` lemmas cannot have that argument inferred at a use site; these restate
them with it discharged. -/

variable (hp : Hypothesis A Λ) (ep : A ≃* B)

theorem ofMulEquivPullback_V_eq_W (hVW : hp.V = hp.W) :
    letI := MulAction.compHom Λ ep.symm.toMonoidHom
    (hp.ofMulEquivPullback ep).V = (hp.ofMulEquivPullback ep).W := by
  letI := MulAction.compHom Λ ep.symm.toMonoidHom
  exact ofMulEquiv_V_eq_W _ _ _ _ hVW

theorem ofMulEquivPullback_natCard_Q0 :
    letI := MulAction.compHom Λ ep.symm.toMonoidHom
    Nat.card ((hp.ofMulEquivPullback ep).Q0) = Nat.card (hp.Q0) := by
  letI := MulAction.compHom Λ ep.symm.toMonoidHom
  exact ofMulEquiv_natCard_Q0 _ _ _ _

theorem ofMulEquivPullback_natCard_Q :
    letI := MulAction.compHom Λ ep.symm.toMonoidHom
    Nat.card ((hp.ofMulEquivPullback ep).Q) = Nat.card (hp.Q) := by
  letI := MulAction.compHom Λ ep.symm.toMonoidHom
  exact ofMulEquiv_natCard_Q _ _ _ _

theorem ofMulEquivPullback_orderOf_distinguishedInvolution_mul_t :
    letI := MulAction.compHom Λ ep.symm.toMonoidHom
    orderOf ((hp.ofMulEquivPullback ep).distinguishedInvolution *
        (hp.ofMulEquivPullback ep).t)
      = orderOf (hp.distinguishedInvolution * hp.t) := by
  letI := MulAction.compHom Λ ep.symm.toMonoidHom
  exact ofMulEquiv_orderOf_distinguishedInvolution_mul_t _ _ _ _

theorem ofMulEquivPullback_exists_ne_one_mem_W (hw : ∃ x ∈ hp.W, x ≠ 1) :
    letI := MulAction.compHom Λ ep.symm.toMonoidHom
    ∃ x ∈ (hp.ofMulEquivPullback ep).W, x ≠ 1 := by
  letI := MulAction.compHom Λ ep.symm.toMonoidHom
  exact ofMulEquiv_exists_ne_one_mem_W _ _ _ _ hw

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
