/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Character
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryIrreducibles

/-!
# Orthogonality of the ordinary irreducible characters over the splitting field

Navarro's Theorem (2.13) — that `([θ,φ]⁰)` inverts the Cartan matrix — runs on the *second*
orthogonality relation for the ordinary characters.  Those characters live over the splitting
field `K` of the `p`-modular system, not over `ℂ`, so the repository's
`RepresentationTheory/ColumnOrthogonality` (which is stated over `ℂ` with complex conjugation)
does not apply and the relations have to be available over `K`.

This file proves the **first orthogonality relation**

`∑_{g ∈ G} χ_j(g) χ_i(g⁻¹) = |G| δ_{ij}`.

mathlib's `Representation.card_inv_mul_sum_char_mul_char_eq_finrank` turns the character sum into
the dimension of the space of intertwining maps, so everything reduces to computing that
dimension for two Wedderburn blocks.  Both computations are elementary here, because the blocks
are *full* matrix algebras over `K` — that is what the splitting hypothesis buys, and it is why no
algebraic closedness argument appears anywhere below:

* **off-diagonal**: `K[G] ≃ ∏_l M_{m_l}(K)` carries `Pi.single i 1` back to an element of `K[G]`
  acting as the identity on the `i`-th block and as zero on every other, so an intertwining map
  between different blocks vanishes;
* **diagonal**: a self-intertwining map commutes with every matrix of the block, and the matrix
  units `E_{b a₀}` pin it down to a scalar — Schur's lemma for the natural module of `M_n(K)`.

## Main results

* `OddOrder.RepresentationTheory.Modular.asAlgebraHom_wedderburnRepresentation` — the algebra map
  induced by the `i`-th block representation is the `i`-th block of `e`
* `OddOrder.RepresentationTheory.Modular.exists_asAlgebraHom_eq_id_eq_zero` — the central
  idempotent, pulled back to `K[G]`
* `OddOrder.RepresentationTheory.Modular.subsingleton_intertwiningMap_of_ne` — no nonzero
  intertwining maps between different blocks
* `OddOrder.RepresentationTheory.Modular.exists_eq_smul_id_of_intertwiningMap` — Schur for a
  block
* `OddOrder.RepresentationTheory.Modular.sum_character_mul_character_inv` — first orthogonality
-/

namespace OddOrder.RepresentationTheory.Modular

open Module Representation
open scoped Matrix

variable {K G : Type*} [Field K] [Group G] {ι' : Type*} {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

/-! ### The algebra map of a block representation -/

/-- **The algebra map induced by the `i`-th block representation is the `i`-th block of `e`.**
Both sides are algebra maps out of `K[G]` agreeing on the group elements. -/
theorem asAlgebraHom_wedderburnRepresentation (i : ι') :
    (wedderburnRepresentation e i).asAlgebraHom
      = (Matrix.toLinAlgEquiv' (n := m i) (R := K)).toAlgHom.comp
          ((Pi.evalAlgHom K (fun j => Matrix (m j) (m j) K) i).comp e.toAlgHom) := by
  refine MonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  rw [Representation.asAlgebraHom_single, one_smul]
  rfl

/-- **The `i`-th central idempotent, pulled back to `K[G]`**: it acts as the identity on the
`i`-th block and as zero on every other one. -/
theorem exists_asAlgebraHom_eq_id_eq_zero (i : ι') :
    ∃ a : MonoidAlgebra K G,
      (wedderburnRepresentation e i).asAlgebraHom a = LinearMap.id ∧
      ∀ j, j ≠ i → (wedderburnRepresentation e j).asAlgebraHom a = 0 := by
  classical
  refine ⟨e.symm (Pi.single i 1), ?_, fun j hj => ?_⟩
  · rw [asAlgebraHom_wedderburnRepresentation]
    simp
    rfl
  · rw [asAlgebraHom_wedderburnRepresentation]
    simp [Pi.single_eq_of_ne hj]

/-! ### Intertwining maps between different blocks -/

variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

omit [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] in
/-- An intertwining map commutes with the whole group algebra, not just with the group. -/
theorem map_asAlgebraHom_of_intertwiningMap {ρ : Representation K G V} {σ : Representation K G W}
    (f : IntertwiningMap ρ σ) (a : MonoidAlgebra K G) (v : V) :
    f.toLinearMap (ρ.asAlgebraHom a v) = σ.asAlgebraHom a (f.toLinearMap v) := by
  induction a using MonoidAlgebra.induction_on with
  | hM g =>
    rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of]
    exact congrFun (congrArg DFunLike.coe (f.isIntertwining' g)) v
  | hadd a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | hsmul c a ha => simp only [map_smul, LinearMap.smul_apply, ha]

/-- **There is no nonzero intertwining map between different Wedderburn blocks.**  The `i`-th
central idempotent acts as the identity upstairs and as zero downstairs. -/
theorem subsingleton_intertwiningMap_of_ne {i j : ι'} (h : i ≠ j) :
    Subsingleton
      (IntertwiningMap (wedderburnRepresentation e i) (wedderburnRepresentation e j)) := by
  obtain ⟨a, ha, ha'⟩ := exists_asAlgebraHom_eq_id_eq_zero e i
  have hzero : ∀ f : IntertwiningMap (wedderburnRepresentation e i)
      (wedderburnRepresentation e j), f.toLinearMap = 0 := by
    intro f
    refine LinearMap.ext fun v => ?_
    have hcomm := map_asAlgebraHom_of_intertwiningMap f a v
    rw [ha, ha' j (Ne.symm h)] at hcomm
    simpa using hcomm
  exact ⟨fun f f' => IntertwiningMap.ext ((hzero f).trans (hzero f').symm)⟩

/-! ### Endomorphisms of a block: Schur -/

/-- Every matrix of the `i`-th block is realised by an element of `K[G]`. -/
theorem exists_asAlgebraHom_eq_toLin (i : ι') (M : Matrix (m i) (m i) K) :
    ∃ a : MonoidAlgebra K G,
      (wedderburnRepresentation e i).asAlgebraHom a = Matrix.toLinAlgEquiv' M := by
  classical
  refine ⟨e.symm (Pi.single i M), ?_⟩
  rw [asAlgebraHom_wedderburnRepresentation]
  simp

/-- **A self-intertwining map of a block is a scalar.**  It commutes with every matrix of the
block, and the matrix units `E_{b a₀}` then force it to be multiplication by
`c = f(Pi.single a₀ 1) a₀` on every standard basis vector.

This is Schur's lemma for the natural module of `M_n(K)` — no algebraic closedness is needed,
because the block is already a *full* matrix algebra over `K`; that is exactly what the splitting
hypothesis on `K` buys. -/
theorem exists_eq_smul_id_of_intertwiningMap [∀ i, Nonempty (m i)] {i : ι'}
    (f : IntertwiningMap (wedderburnRepresentation e i) (wedderburnRepresentation e i)) :
    ∃ c : K, f = c • IntertwiningMap.id _ := by
  classical
  have hcomm : ∀ (M : Matrix (m i) (m i) K) (v : m i → K),
      f.toLinearMap (M *ᵥ v) = M *ᵥ f.toLinearMap v := by
    intro M v
    obtain ⟨a, ha⟩ := exists_asAlgebraHom_eq_toLin e i M
    have := map_asAlgebraHom_of_intertwiningMap f a v
    rwa [ha] at this
  set a₀ := Classical.arbitrary (m i) with ha₀
  refine ⟨f.toLinearMap (Pi.single a₀ 1) a₀, ?_⟩
  refine IntertwiningMap.ext ((Pi.basisFun K (m i)).ext fun b => ?_)
  have hb := hcomm (Matrix.single b a₀ 1) (Pi.single a₀ 1)
  rw [Matrix.single_mulVec_eq, Matrix.single_mulVec_eq] at hb
  simp only [Pi.single_eq_same, mul_one, one_smul, one_mul] at hb
  simp [hb]

/-- The space of self-intertwining maps of a block is one-dimensional. -/
theorem finrank_intertwiningMap_self [∀ i, Nonempty (m i)] (i : ι') :
    finrank K
      (IntertwiningMap (wedderburnRepresentation e i) (wedderburnRepresentation e i)) = 1 := by
  classical
  refine finrank_eq_one (IntertwiningMap.id _) ?_ fun w => ?_
  · intro hid
    have := congrArg (fun f : IntertwiningMap (wedderburnRepresentation e i)
      (wedderburnRepresentation e i) =>
        f.toLinearMap (Pi.single (Classical.arbitrary (m i)) (1 : K))) hid
    simp at this
  · obtain ⟨c, hc⟩ := exists_eq_smul_id_of_intertwiningMap e w
    exact ⟨c, hc.symm⟩

/-! ### First orthogonality -/

variable [Fintype G] [Invertible (Nat.card G : K)]

/-- **Off-diagonal first orthogonality over the splitting field.**  For different Wedderburn
blocks the character sum vanishes, because the space of intertwining maps does. -/
theorem sum_character_mul_character_inv_eq_zero {i j : ι'} (h : i ≠ j) :
    ∑ g : G, (wedderburnRepresentation e j).character g
      * (wedderburnRepresentation e i).character g⁻¹ = 0 := by
  haveI := subsingleton_intertwiningMap_of_ne e h
  have hfin := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (wedderburnRepresentation e i) (wedderburnRepresentation e j)
  rw [finrank_zero_of_subsingleton, Nat.cast_zero] at hfin
  have hinv : ((Nat.card G : K))⁻¹ ≠ 0 := by
    simpa using (isUnit_of_invertible (Nat.card G : K)).ne_zero
  exact (mul_eq_zero.mp hfin).resolve_left hinv

/-- **Diagonal first orthogonality over the splitting field.** -/
theorem sum_character_mul_character_inv_self [∀ i, Nonempty (m i)] (i : ι') :
    ∑ g : G, (wedderburnRepresentation e i).character g
      * (wedderburnRepresentation e i).character g⁻¹ = (Nat.card G : K) := by
  have hfin := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (wedderburnRepresentation e i) (wedderburnRepresentation e i)
  rw [finrank_intertwiningMap_self e i, Nat.cast_one] at hfin
  have hunit : IsUnit ((Nat.card G : K)) := isUnit_of_invertible _
  set S := ∑ g : G, (wedderburnRepresentation e i).character g
    * (wedderburnRepresentation e i).character g⁻¹ with hS
  calc S = (Nat.card G : K) * ((Nat.card G : K)⁻¹ * S) := by
          rw [← mul_assoc, mul_inv_cancel₀ hunit.ne_zero, one_mul]
    _ = (Nat.card G : K) * 1 := by rw [hfin]
    _ = (Nat.card G : K) := mul_one _

/-- **First orthogonality over the splitting field**, in one statement. -/
theorem sum_character_mul_character_inv [∀ i, Nonempty (m i)] [DecidableEq ι'] (i j : ι') :
    ∑ g : G, (wedderburnRepresentation e j).character g
        * (wedderburnRepresentation e i).character g⁻¹
      = if i = j then (Nat.card G : K) else 0 := by
  split
  · subst ‹i = j›
    exact sum_character_mul_character_inv_self e i
  · exact sum_character_mul_character_inv_eq_zero e ‹i ≠ j›

end OddOrder.RepresentationTheory.Modular
