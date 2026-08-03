/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.DefectGroup
import OddOrder.Algebra.MackeyFormula
import OddOrder.Algebra.Rosenberg

/-!
# The defect groups of an idempotent are conjugate

`DefectGroup` produces a defect group of a `G`-fixed element and shows it is a `p`-group.  For an
*idempotent* `b` whose corner in `A^G` is local — for `A = kG` and `b` a block idempotent this is
the primitivity of `b` in `Z(kG)` — the defect groups form a single `G`-conjugacy class.

The argument is Brauer's: `b = b · b` lies in `A^G_D · A^G_{D'}`, which Mackey's formula
(`exists_mul_eq_sum_relTraceIdeal_inf`) puts inside `∑_g A^G_{D ∩ ᵍD'}`; Rosenberg's lemma
(`exists_mem_of_sum_eq_of_local`) then puts `b` inside a *single* `A^G_{D ∩ ᵍD'}`.  Minimality of
`D` forces `D ∩ ᵍD' = D`, i.e. `D ≤ ᵍD'`, and minimality of `ᵍD'` — a defect group because the
trace ideals are permuted by conjugation — forces equality.

## Main results

* `OddOrder.GAlgebra.IsDefectGroup.conj` — a conjugate of a defect group is a defect group.
* `OddOrder.GAlgebra.exists_conj_eq_of_isDefectGroup` — the conjugacy, with locality of the
  corner supplied abstractly.
* `OddOrder.GAlgebra.exists_conj_eq_of_isDefectGroup_of_commute` — the form to use when `A^G` is
  commutative, where "non-unit in the corner" means "nilpotent".
-/

namespace OddOrder.GAlgebra

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {A : Type*} [Ring A] [MulSemiringAction G A]

section Conj

omit [Finite G] in
theorem smul_top_subgroup (c : G) : MulAut.conj c • (⊤ : Subgroup G) = ⊤ := by
  ext x
  simp

omit [Finite G] in
theorem smul_subgroup_lt_iff (φ : MulAut G) {S T : Subgroup G} : φ • S < φ • T ↔ S < T := by
  simp only [lt_iff_le_not_ge, Subgroup.pointwise_smul_le_pointwise_smul_iff]

/-- **A conjugate of a defect group is a defect group.**  The relative trace ideals are permuted
by conjugation (`smul_mem_relTraceIdeal_conj`) and `b` is `G`-fixed, so membership and minimality
both transport. -/
theorem IsDefectGroup.conj {b : A} (hbfix : ∀ g : G, g • b = b) {D : Subgroup G}
    (hD : IsDefectGroup b D) (c : G) : IsDefectGroup b (MulAut.conj c • D) where
  mem := by
    have := smul_mem_relTraceIdeal_conj hD.mem c
    rwa [hbfix c, smul_top_subgroup] at this
  minimal := by
    intro E hE hmem
    -- Pull `E` back by `c⁻¹`; it is then a proper subgroup of `D` containing `b` in its trace
    -- ideal, contradicting minimality of `D`.
    have hEmem : b ∈ relTraceIdeal (MulAut.conj c⁻¹ • E) (⊤ : Subgroup G) := by
      have := smul_mem_relTraceIdeal_conj hmem c⁻¹
      rwa [hbfix c⁻¹, smul_top_subgroup] at this
    refine hD.minimal _ ?_ hEmem
    have hinv : MulAut.conj c⁻¹ • (MulAut.conj c • D) = D := by
      rw [map_inv, inv_smul_smul]
    rw [← hinv, map_inv]
    exact (smul_subgroup_lt_iff _).mpr hE

end Conj

/-- **Brauer's theorem on defect groups**: they form a single `G`-conjugacy class.

The hypotheses `hNadd`, `hNb`, `hdich` say that the corner of `b` inside `A^G` is a local ring,
with `N` marking its non-units; see `exists_mem_of_sum_eq_of_local`. -/
theorem exists_conj_eq_of_isDefectGroup {b : A} (hbfix : ∀ g : G, g • b = b)
    (hb : IsIdempotentElem b) (hb0 : b ≠ 0)
    {N : A → Prop} (hNadd : ∀ x y, N x → N y → N (x + y)) (hNb : ¬ N b)
    (hdich : ∀ x : A, (∀ g : G, g • x = x) →
      N (b * x * b) ∨ ∃ u : A, (∀ g : G, g • u = u) ∧ u * (b * x * b) = b)
    {D D' : Subgroup G} (hD : IsDefectGroup b D) (hD' : IsDefectGroup b D') :
    ∃ g : G, D = MulAut.conj g • D' := by
  -- Mackey: `b = b · b` is a sum of elements of the ideals `A^G_{D ∩ ᵍD'}`.
  obtain ⟨s, c, hc, hbsum⟩ := exists_mul_eq_sum_relTraceIdeal_inf hD.mem hD'.mem
  rw [hb.eq] at hbsum
  -- Rosenberg: `b` already lies in one of them.
  obtain ⟨g, -, hmem⟩ := exists_mem_of_sum_eq_of_local (ι := G) (s := s)
    (I := fun g => relTraceIdeal (D ⊓ MulAut.conj g • D') (⊤ : Subgroup G)) (c := c)
    hb hb0 hNadd hNb (U := {x : A | ∀ g : G, g • x = x}) hbfix
    (fun _ u hu x hx => mem_relTraceIdeal_mul le_top hx fun w _ => hu w)
    (fun _ u hu x hx => mul_mem_relTraceIdeal le_top hx fun w _ => hu w)
    hc
    (fun i hi => by
      have hfix : ∀ g : G, g • c i = c i := fun g =>
        smul_of_mem_relTraceIdeal (hc i hi) (Subgroup.mem_top g)
      rcases hdich (c i) hfix with h | ⟨u, hu, hub⟩
      · exact Or.inl h
      · exact Or.inr ⟨u, hu, hub⟩)
    hbsum.symm
  -- Minimality of `D` turns `D ∩ ᵍD'` into `D`.
  have hDle : D ≤ MulAut.conj g • D' := by
    have hinf : D ⊓ MulAut.conj g • D' = D := by
      by_contra hne
      exact hD.minimal _ (lt_of_le_of_ne inf_le_left hne) hmem
    exact hinf ▸ inf_le_right
  -- Minimality of the (conjugate) defect group `ᵍD'` turns it into `D`.
  refine ⟨g, le_antisymm hDle ?_⟩
  by_contra hne
  exact (hD'.conj hbfix g).minimal D (lt_of_le_of_ne hDle fun h => hne (h ▸ le_refl _)) hD.mem

/-- **Brauer's theorem when `A^G` is commutative**, which is the case for `A = kG` acting by
conjugation, where `A^G = Z(kG)`.  There "non-unit in the corner of `b`" means "nilpotent", and
the dichotomy `hdich` is Fitting's lemma (`isNilpotent_or_exists_mul_eq`). -/
theorem exists_conj_eq_of_isDefectGroup_of_commute {b : A} (hbfix : ∀ g : G, g • b = b)
    (hb : IsIdempotentElem b) (hb0 : b ≠ 0)
    (hcomm : ∀ x y : A, (∀ g : G, g • x = x) → (∀ g : G, g • y = y) → Commute x y)
    (hdich : ∀ x : A, (∀ g : G, g • x = x) →
      IsNilpotent (b * x) ∨ ∃ u : A, (∀ g : G, g • u = u) ∧ u * (b * x) = b)
    {D D' : Subgroup G} (hD : IsDefectGroup b D) (hD' : IsDefectGroup b D') :
    ∃ g : G, D = MulAut.conj g • D' := by
  refine exists_conj_eq_of_isDefectGroup hbfix hb hb0
    (N := fun z => IsNilpotent z ∧ ∀ g : G, g • z = z)
    (fun x y hx hy => ⟨Commute.isNilpotent_add (hcomm x y hx.2 hy.2) hx.1 hy.1,
      fun g => by rw [smul_add, hx.2 g, hy.2 g]⟩)
    (fun h => not_isNilpotent_of_isIdempotentElem hb hb0 h.1) (fun x hx => ?_) hD hD'
  -- `b * x * b = b * x` because `b` and `x` are both `G`-fixed, hence commute.
  have hbx : b * x * b = b * x := by
    rw [mul_assoc, (hcomm x b hx hbfix).eq, ← mul_assoc, hb.eq]
  rw [hbx]
  rcases hdich x hx with h | ⟨u, hu, hub⟩
  · exact Or.inl ⟨h, fun g => by rw [smul_mul', hbfix g, hx g]⟩
  · exact Or.inr ⟨u, hu, hub⟩

end OddOrder.GAlgebra
