/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Coordinates of quadratic maps over `𝔽₂`

Over `ZMod 2` a quadratic map `Q : V → W` is determined by its values on a
basis of `V` together with its polar values on pairs of distinct basis
vectors: every vector is a `0`/`1`-combination of basis vectors, and
`QuadraticMap.map_sum` expands `Q` on such a sum in terms of exactly these
data.  Conversely, any assignment of such data is realized by a sum of the
elementary quadratic maps `v ↦ (cᵢ(v)·cⱼ(v)) • w` in the basis
coordinates.  Packaged as an `S`-linear equivalence with the coordinate
space `{p : ι × ι // p.1 ≤ p.2} → W`, this computes the dimension of the
space of `𝔽₂`-quadratic maps — the spanning input for Peterfalvi
Appendix III, Lemma 2(c) (issue 0148).

Main declarations:

* `coordMulCoord` — the elementary quadratic map `v ↦ (cᵢ(v)·cⱼ(v)) • w`;
* `eq_zero_of_forall_basis` / `ext_basis` — quadratic maps over `ZMod 2`
  agreeing on basis values and basis polars agree;
* `coordEquiv` — the coordinate `S`-linear equivalence
  `QuadraticMap (ZMod 2) V W ≃ₗ[S] ({p : ι × ι // p.1 ≤ p.2} → W)`.
-/

set_option autoImplicit false

namespace OddOrder.Algebra.CharTwoQuadratic

open QuadraticMap

variable {ι V W S : Type*} [AddCommGroup V] [AddCommGroup W]
  [Module (ZMod 2) V] [Module (ZMod 2) W]
  [Semiring S] [Module S W] [SMulCommClass S (ZMod 2) W]

variable (b : Module.Basis ι (ZMod 2) V)

/-! ### The elementary coordinate quadratic maps -/

/-- The elementary quadratic map `v ↦ (cᵢ(v)·cⱼ(v)) • w` attached to two
basis coordinates and a target vector. -/
noncomputable def coordMulCoord (i j : ι) (w : W) :
    QuadraticMap (ZMod 2) V W :=
  (LinearMap.toSpanSingleton (ZMod 2) W w).compQuadraticMap
    (QuadraticMap.linMulLin (b.coord i) (b.coord j))

@[simp] theorem coordMulCoord_apply (i j : ι) (w : W) (v : V) :
    coordMulCoord b i j w v = (b.coord i v * b.coord j v) • w :=
  rfl

private theorem coordMulCoord_add (i j : ι) (w w' : W) :
    coordMulCoord b i j (w + w') =
      coordMulCoord b i j w + coordMulCoord b i j w' := by
  ext v
  simp [smul_add]

private theorem coordMulCoord_smul (i j : ι) (s : S) (w : W) :
    coordMulCoord b i j (s • w) = s • coordMulCoord b i j w := by
  ext v
  simp only [coordMulCoord_apply, QuadraticMap.smul_apply]
  exact (smul_comm s (b.coord i v * b.coord j v) w).symm

/-- The polar form of an elementary coordinate map. -/
private theorem polar_coordMulCoord (i j : ι) (w : W) (x y : V) :
    polar (⇑(coordMulCoord b i j w)) x y =
      (b.coord i x * b.coord j y + b.coord i y * b.coord j x) • w := by
  simp only [QuadraticMap.polar, coordMulCoord_apply, map_add]
  rw [← sub_smul, ← sub_smul,
    show (b.coord i x + b.coord i y) * (b.coord j x + b.coord j y) -
        b.coord i x * b.coord j x - b.coord i y * b.coord j y =
        b.coord i x * b.coord j y + b.coord i y * b.coord j x from by ring]

/-! ### Determination on a basis -/

/-- Over `ZMod 2` every vector is the plain sum of the basis vectors in
the support of its coordinates. -/
theorem sum_repr_support_eq (v : V) :
    ∑ i ∈ (b.repr v).support, b i = v := by
  conv_rhs => rw [← b.linearCombination_repr v]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have h0 : (b.repr v) i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have h1 : (b.repr v) i = 1 := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) ((b.repr v) i) with h | h
    · exact absurd h h0
    · exact h
  rw [h1, one_smul]

/-- In a `ZMod 2`-module the polar form of a quadratic map vanishes on the
diagonal (`2`-torsion). -/
theorem polar_self_eq_zero (Q : QuadraticMap (ZMod 2) V W) (x : V) :
    polar (⇑Q) x x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, ← two_smul (ZMod 2),
    show (2 : ZMod 2) = 0 by decide, zero_smul]

/-- **Determination on a basis** (over `ZMod 2`): a quadratic map
vanishing on all basis vectors and all basis polars is zero. -/
theorem eq_zero_of_forall_basis {Q : QuadraticMap (ZMod 2) V W}
    (hval : ∀ i, Q (b i) = 0)
    (hpolar : ∀ i j, polar (⇑Q) (b i) (b j) = 0) :
    Q = 0 := by
  classical
  ext v
  rw [← sum_repr_support_eq b v, QuadraticMap.map_sum]
  have h1 : (∑ i ∈ (b.repr v).support, Q (b i)) = 0 :=
    Finset.sum_eq_zero fun i _ => hval i
  have h2 : (∑ ij ∈ (b.repr v).support.sym2 with ¬ ij.IsDiag,
      polarSym2 (⇑Q) (ij.map b)) = 0 := by
    refine Finset.sum_eq_zero fun ij _ => ?_
    induction ij with
    | _ i j =>
        rw [Sym2.map_mk, polarSym2_sym2Mk]
        exact hpolar i j
  rw [h1, h2, add_zero]
  rfl

/-- Two quadratic maps over `ZMod 2` agreeing on basis values and basis
polars agree. -/
theorem ext_basis {Q Q' : QuadraticMap (ZMod 2) V W}
    (hval : ∀ i, Q (b i) = Q' (b i))
    (hpolar : ∀ i j, polar (⇑Q) (b i) (b j) = polar (⇑Q') (b i) (b j)) :
    Q = Q' := by
  have hps : ∀ x y : V, polar (⇑(Q - Q')) x y =
      polar (⇑Q) x y - polar (⇑Q') x y := by
    intro x y
    simp only [QuadraticMap.polar, QuadraticMap.sub_apply]
    abel
  refine sub_eq_zero.mp (eq_zero_of_forall_basis b ?_ ?_)
  · intro i
    rw [QuadraticMap.sub_apply, hval, sub_self]
  · intro i j
    rw [hps, hpolar, sub_self]

/-! ### The coordinate equivalence -/

section CoordEquiv

variable [Fintype ι] [LinearOrder ι]

/-- Coordinate readout of a quadratic map: basis values on the diagonal,
basis polars off it. -/
noncomputable def toCoords :
    QuadraticMap (ZMod 2) V W →ₗ[S] ({p : ι × ι // p.1 ≤ p.2} → W) where
  toFun Q p := if p.1.1 = p.1.2 then Q (b p.1.1)
    else polar (⇑Q) (b p.1.1) (b p.1.2)
  map_add' Q Q' := by
    funext p
    by_cases hp : p.1.1 = p.1.2 <;>
      simp [hp, QuadraticMap.polar_add]
  map_smul' s Q := by
    funext p
    by_cases hp : p.1.1 = p.1.2 <;>
      simp [hp, QuadraticMap.polar_smul]

/-- Assembly of a quadratic map from coordinate data, as a sum of
elementary coordinate maps. -/
noncomputable def ofCoords :
    ({p : ι × ι // p.1 ≤ p.2} → W) →ₗ[S] QuadraticMap (ZMod 2) V W where
  toFun u := ∑ p : {p : ι × ι // p.1 ≤ p.2},
    coordMulCoord b p.1.1 p.1.2 (u p)
  map_add' u u' := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => coordMulCoord_add b _ _ _ _
  map_smul' s u := by
    rw [RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun p _ => coordMulCoord_smul b _ _ _ _

omit [Fintype ι] in
private theorem coord_basis (i l : ι) :
    b.coord i (b l) = if i = l then 1 else 0 := by
  classical
  rw [Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]
  rcases eq_or_ne i l with h | h
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun hh => h hh.symm), if_neg h]

private theorem ofCoords_basis_value (u : {p : ι × ι // p.1 ≤ p.2} → W)
    (l : ι) :
    ofCoords (S := S) b u (b l) = u ⟨(l, l), le_refl l⟩ := by
  change (∑ p : {p : ι × ι // p.1 ≤ p.2},
    coordMulCoord b p.1.1 p.1.2 (u p)) (b l) = _
  rw [QuadraticMap.sum_apply]
  rw [Finset.sum_eq_single (⟨(l, l), le_refl l⟩ : {p : ι × ι // p.1 ≤ p.2})]
  · simp
  · intro p _ hp
    rw [coordMulCoord_apply, coord_basis, coord_basis]
    rcases eq_or_ne p.1.1 l with h1 | h1
    · rcases eq_or_ne p.1.2 l with h2 | h2
      · exact absurd (Subtype.ext (Prod.ext h1 h2)) hp
      · rw [if_pos h1, if_neg h2, mul_zero, zero_smul]
    · rw [if_neg h1, zero_mul, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem polar_ofCoords_basis (u : {p : ι × ι // p.1 ≤ p.2} → W)
    {l m : ι} (hlm : l < m) :
    polar (⇑(ofCoords (S := S) b u)) (b l) (b m) =
      u ⟨(l, m), le_of_lt hlm⟩ := by
  change polar (⇑(∑ p : {p : ι × ι // p.1 ≤ p.2},
    coordMulCoord b p.1.1 p.1.2 (u p))) (b l) (b m) = _
  have hsum : ∀ x y : V, polar (⇑(∑ p : {p : ι × ι // p.1 ≤ p.2},
      coordMulCoord b p.1.1 p.1.2 (u p))) x y =
      ∑ p : {p : ι × ι // p.1 ≤ p.2},
        polar (⇑(coordMulCoord b p.1.1 p.1.2 (u p))) x y := by
    intro x y
    simp only [QuadraticMap.polar, QuadraticMap.sum_apply,
      Finset.sum_sub_distrib]
  rw [hsum]
  rw [Finset.sum_eq_single
    (⟨(l, m), le_of_lt hlm⟩ : {p : ι × ι // p.1 ≤ p.2})]
  · rw [polar_coordMulCoord]
    simp [ne_of_lt hlm, (ne_of_lt hlm).symm]
  · intro p _ hp
    rw [polar_coordMulCoord, coord_basis, coord_basis, coord_basis,
      coord_basis]
    rcases eq_or_ne p.1.1 l with h1 | h1
    · rcases eq_or_ne p.1.2 m with h2 | h2
      · exact absurd (Subtype.ext (Prod.ext h1 h2)) hp
      · have hne3 : ¬ p.1.1 = m := by
          rw [h1]
          exact ne_of_lt hlm
        rw [if_pos h1, if_neg h2, mul_zero, zero_add, if_neg hne3,
          zero_mul, zero_smul]
    · rw [if_neg h1, zero_mul, zero_add]
      rcases eq_or_ne p.1.1 m with h4 | h4
      · -- p.1.1 = m: then p.1.2 ≥ m > l, so coord p.1.2 (b l) = 0
        have h5 : ¬ p.1.2 = l := by
          intro h5
          have hle := p.2
          rw [h4, h5] at hle
          exact absurd hle (not_le.mpr hlm)
        rw [if_pos h4, if_neg h5, mul_zero, zero_smul]
      · rw [if_neg h4, zero_mul, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The coordinate equivalence for quadratic maps over `𝔽₂`**: a
quadratic map `V → W` corresponds to its basis values (diagonal
coordinates) and basis polars (strictly increasing coordinates). -/
noncomputable def coordEquiv :
    QuadraticMap (ZMod 2) V W ≃ₗ[S] ({p : ι × ι // p.1 ≤ p.2} → W) := by
  refine LinearEquiv.ofLinear (toCoords b) (ofCoords b) ?_ ?_
  · -- toCoords ∘ ofCoords = id
    refine LinearMap.ext fun u => funext fun p => ?_
    change toCoords (S := S) b (ofCoords (S := S) b u) p = u p
    obtain ⟨⟨l, m⟩, hlm⟩ := p
    rcases eq_or_lt_of_le hlm with heq | hlt
    · change (if l = m then ofCoords (S := S) b u (b l)
        else polar (⇑(ofCoords (S := S) b u)) (b l) (b m)) = _
      rw [if_pos heq, ofCoords_basis_value]
      exact congrArg u (Subtype.ext (Prod.ext rfl heq))
    · change (if l = m then ofCoords (S := S) b u (b l)
        else polar (⇑(ofCoords (S := S) b u)) (b l) (b m)) = _
      rw [if_neg (ne_of_lt hlt), polar_ofCoords_basis b u hlt]
  · -- ofCoords ∘ toCoords = id
    refine LinearMap.ext fun Q => ?_
    change ofCoords (S := S) b (toCoords (S := S) b Q) = Q
    refine ext_basis b ?_ ?_
    · intro l
      rw [ofCoords_basis_value]
      change (if l = l then Q (b l) else _) = Q (b l)
      rw [if_pos rfl]
    · intro i j
      rcases lt_trichotomy i j with h | h | h
      · rw [polar_ofCoords_basis b _ h]
        change (if i = j then _ else polar (⇑Q) (b i) (b j)) = _
        rw [if_neg (ne_of_lt h)]
      · subst h
        rw [polar_self_eq_zero, polar_self_eq_zero]
      · rw [QuadraticMap.polar_comm, QuadraticMap.polar_comm (⇑Q)]
        rw [polar_ofCoords_basis b _ h]
        change (if j = i then _ else polar (⇑Q) (b j) (b i)) = _
        rw [if_neg (ne_of_lt h)]

end CoordEquiv

end OddOrder.Algebra.CharTwoQuadratic
