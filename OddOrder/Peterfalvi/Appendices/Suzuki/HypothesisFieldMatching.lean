/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.HypothesisTransport
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourSetup

/-!
# Which fields of the standing hypothesis are determined by which

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), Part II.

`Q₀`, `W` and the distinguished involution are not independent data: `Q₀ = {x ∈ H | x² = 1}`,
`W = D ⊓ C(Q₀)` (`W_eq_inf_centralizer_Q0`), and the distinguished pair is pinned by
uniqueness (`eq_distinguishedPair_of_structure`).  So an isomorphism matching `H` and `D`
matches `Q₀` and `W` — **with no reference to `t`** — and two hypotheses on one group with
the same `H`, `Q`, `D`, `t` have the same `Q₀`, `W` and `s`.

Ch. IV §4, step (2) (p. 133) uses both halves: the first to move `1 ≠ w ∈ W` between the
intrinsic and the transported standing hypotheses on `U/Z(U)`, the second to move facts
between that hypothesis and its relabelled-point-set twin.

## Main results

* `map_Q0_of_mulEquiv`, `map_W_of_mulEquiv`, `exists_ne_one_mem_W_of_mulEquiv`
* `Q0_eq_of_H_eq`, `W_eq_of_H_D_eq`, `distinguishedInvolution_eq_of_eq`
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

/-! ### `Q₀` and `W` are determined by `H` and `D`

`Q₀ = {x ∈ H | x² = 1}` and `W = D ⊓ C(Q₀)` (`W_eq_inf_centralizer_Q0`), so *any*
isomorphism matching `H` and `D` matches `Q₀` and `W` — **without any reference to `t`**.
That is what lets Ch. IV §4, step (2) move `1 ≠ w ∈ W` from the transported standing
hypothesis to the intrinsic one on `U/Z(U)`: the two are related by
`residualQuotientMulEquiv` followed by the conjugation of
`Setup.exists_conj_eq_triple`, and neither step needs the distinguished involution. -/

section EquivMatch

variable {L L' : Type*} [Group L] [Group L'] [Finite L] [Finite L']
  {Λ Λ' : Type*} [MulAction L Λ] [MulAction L' Λ']

/-- `Q₀` is determined by `H`. -/
theorem map_Q0_of_mulEquiv (h₁ : Hypothesis L Λ) (h₂ : Hypothesis L' Λ') (φ : L ≃* L')
    (hH : h₁.H.map φ.toMonoidHom = h₂.H) : h₁.Q0.map φ.toMonoidHom = h₂.Q0 := by
  ext y
  rw [Subgroup.mem_map_equiv, h₁.mem_Q0_iff, h₂.mem_Q0_iff, ← hH, Subgroup.mem_map_equiv]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro hy
    have hc := congrArg φ hy
    rwa [map_pow, map_one, MulEquiv.apply_symm_apply] at hc
  · intro hy
    have hc := congrArg φ.symm hy
    rwa [map_pow, map_one] at hc

/-- `W` is determined by `H` and `D` — **no `t`**. -/
theorem map_W_of_mulEquiv (h₁ : Hypothesis L Λ) (h₂ : Hypothesis L' Λ') (φ : L ≃* L')
    (hH : h₁.H.map φ.toMonoidHom = h₂.H) (hD : h₁.D.map φ.toMonoidHom = h₂.D) :
    h₁.W.map φ.toMonoidHom = h₂.W := by
  have himg : φ '' (h₁.Q0 : Set L) = (h₂.Q0 : Set L') := by
    rw [← map_Q0_of_mulEquiv h₁ h₂ φ hH]; rfl
  rw [h₁.W_eq_inf_centralizer_Q0, h₂.W_eq_inf_centralizer_Q0,
    Subgroup.map_inf _ _ φ.toMonoidHom φ.injective, hD,
    map_centralizer_equiv φ (h₁.Q0 : Set L), himg]

/-- `V` is determined by `D` and `t`. -/
theorem map_V_of_mulEquiv (h₁ : Hypothesis L Λ) (h₂ : Hypothesis L' Λ') (φ : L ≃* L')
    (hD : h₁.D.map φ.toMonoidHom = h₂.D) (ht : φ h₁.t = h₂.t) :
    h₁.V.map φ.toMonoidHom = h₂.V := by
  rw [Hypothesis.V, Hypothesis.V, Subgroup.map_inf _ _ φ.toMonoidHom φ.injective, hD,
    map_centralizer_equiv φ {h₁.t}, Set.image_singleton, ht]

/-- `K` is determined by `D` and `t`. -/
theorem map_K_of_mulEquiv (h₁ : Hypothesis L Λ) (h₂ : Hypothesis L' Λ') (φ : L ≃* L')
    (hD : h₁.D.map φ.toMonoidHom = h₂.D) (ht : φ h₁.t = h₂.t) :
    h₁.K.map φ.toMonoidHom = h₂.K := by
  have hset : (φ.toMonoidHom : L → L') '' h₁.KSet = h₂.KSet := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxD, hxinv⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hD]; exact Subgroup.mem_map_of_mem _ hxD
      · change h₂.t * φ x * h₂.t = (φ x)⁻¹
        rw [← ht, ← map_mul, ← map_mul, hxinv, map_inv]
    · rintro ⟨hyD, hyinv⟩
      refine ⟨φ.symm y, ⟨?_, ?_⟩, φ.apply_symm_apply y⟩
      · rw [← hD, Subgroup.mem_map_equiv] at hyD; exact hyD
      · apply φ.injective
        rw [map_mul, map_mul, map_inv, φ.apply_symm_apply, ht]
        exact hyinv
  rw [Hypothesis.K, Hypothesis.K, MonoidHom.map_closure, hset]

/-- A non-trivial element of `W` moves along the isomorphism. -/
theorem exists_ne_one_mem_W_of_mulEquiv (h₁ : Hypothesis L Λ) (h₂ : Hypothesis L' Λ')
    (φ : L ≃* L') (hH : h₁.H.map φ.toMonoidHom = h₂.H)
    (hD : h₁.D.map φ.toMonoidHom = h₂.D) (hw : ∃ w ∈ h₁.W, w ≠ 1) :
    ∃ w ∈ h₂.W, w ≠ 1 := by
  obtain ⟨w, hwW, hw1⟩ := hw
  refine ⟨φ w, ?_, ?_⟩
  · rw [← map_W_of_mulEquiv h₁ h₂ φ hH hD]
    exact Subgroup.mem_map_of_mem _ hwW
  · intro hc
    exact hw1 (φ.injective (by rw [hc, map_one]))

omit [Finite L] [Finite L'] in
/-- `C_Q(D) = 1` transports along an isomorphism matching `Q` and `D`. -/
theorem inf_centralizer_eq_bot_of_mulEquiv (φ : L ≃* L') {Q D : Subgroup L}
    {Q' D' : Subgroup L'} (hQ : Q.map φ.toMonoidHom = Q')
    (hD : D.map φ.toMonoidHom = D')
    (h : Q ⊓ Subgroup.centralizer (D : Set L) = ⊥) :
    Q' ⊓ Subgroup.centralizer (D' : Set L') = ⊥ := by
  have himg : φ '' (D : Set L) = (D' : Set L') := by rw [← hD]; rfl
  have := congrArg (fun K : Subgroup L => K.map φ.toMonoidHom) h
  simp only [Subgroup.map_bot] at this
  rw [Subgroup.map_inf _ _ φ.toMonoidHom φ.injective, hQ,
    map_centralizer_equiv φ (D : Set L), himg] at this
  exact this

end EquivMatch

section SameGroup

variable {L : Type*} [Group L] [Finite L] {Λ Λ' : Type*} [MulAction L Λ] [MulAction L Λ']

/-- `Q₀` depends only on `H`, not on the permuted set. -/
theorem Q0_eq_of_H_eq (h₁ : Hypothesis L Λ) (h₂ : Hypothesis L Λ') (hH : h₁.H = h₂.H) :
    h₁.Q0 = h₂.Q0 := by
  have h := map_Q0_of_mulEquiv h₁ h₂ (MulEquiv.refl L) (by simpa using hH)
  simpa using h

/-- `W` depends only on `H` and `D`, not on the permuted set. -/
theorem W_eq_of_H_D_eq (h₁ : Hypothesis L Λ) (h₂ : Hypothesis L Λ') (hH : h₁.H = h₂.H)
    (hD : h₁.D = h₂.D) : h₁.W = h₂.W := by
  have h := map_W_of_mulEquiv h₁ h₂ (MulEquiv.refl L) (by simpa using hH) (by simpa using hD)
  simpa using h

/-- The distinguished involution depends only on `H`, `Q` and `t`, not on the permuted
set: it is pinned by the uniqueness of the distinguished pair. -/
theorem distinguishedInvolution_eq_of_eq (h₁ : Hypothesis L Λ) (h₂ : Hypothesis L Λ')
    (hH : h₁.H = h₂.H) (hQ : h₁.Q = h₂.Q) (ht : h₁.t = h₂.t) :
    h₁.distinguishedInvolution = h₂.distinguishedInvolution :=
  (h₂.eq_distinguishedPair_of_structure (s' := h₁.distinguishedInvolution)
    (r' := h₁.structureConjugator) (hH ▸ h₁.distinguishedInvolution_mem_H)
    h₁.distinguishedInvolution_sq h₁.distinguishedInvolution_ne_one
    (hQ ▸ h₁.structureConjugator_mem_Q) (ht ▸ h₁.structure_equation)).1

end SameGroup

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
