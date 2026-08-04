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

This file proves the **off-diagonal first orthogonality**

`∑_{g ∈ G} χ_j(g) χ_i(g⁻¹) = 0`  for `i ≠ j`,

which is the part that needs no algebraic closedness at all.  The mechanism is the central
idempotent: `K[G] ≃ ∏_l M_{m_l}(K)` carries `Pi.single i 1` back to an element of `K[G]` that acts
as the identity on the `i`-th block and as zero on every other, so an intertwining map between
different blocks is forced to vanish.  mathlib's
`Representation.card_inv_mul_sum_char_mul_char_eq_finrank` then reads the character sum off the
dimension of the space of intertwining maps.

The diagonal case `i = j` needs `End` of a simple module to be `K`, i.e. Schur's lemma plus
algebraic closedness, and is not done here.

## Main results

* `OddOrder.RepresentationTheory.Modular.asAlgebraHom_wedderburnRepresentation` — the algebra map
  induced by the `i`-th block representation is the `i`-th block of `e`
* `OddOrder.RepresentationTheory.Modular.exists_asAlgebraHom_eq_id_eq_zero` — the central
  idempotent, pulled back to `K[G]`
* `OddOrder.RepresentationTheory.Modular.subsingleton_intertwiningMap_of_ne` — no nonzero
  intertwining maps between different blocks
* `OddOrder.RepresentationTheory.Modular.sum_character_mul_character_inv_eq_zero`
-/

namespace OddOrder.RepresentationTheory.Modular

open Module Representation

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

/-! ### Off-diagonal first orthogonality -/

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

end OddOrder.RepresentationTheory.Modular
