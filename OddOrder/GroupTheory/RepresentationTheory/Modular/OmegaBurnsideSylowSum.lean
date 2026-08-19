/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.OmegaBurnside
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryColumnOrthogonality
import OddOrder.GroupTheory.RepresentationTheory.SylowSumClassCoeff

/-!
# Navarro (4.23): cancelling `|K|` from the `Ω_{K,L}` formula

Navarro's proof of (4.23) compares two expressions for `|Ω_{K,L}|`, one of which carries a factor
`|K|`.  He divides it out in `ℚ`; here the division is done **inside the domain**, by combining

* `sum_class_coeff_sylowSum_mul`: `∑_{u ∈ K} (W · L̂)(u) = |Syl_p| · ∑_{x ∈ S} (K̂' · L̂)(x)`,
  where `W = ∑_{P ∈ Syl_p} P̂` is the central integral lift of `Ĝ_p`;
* `sum_class_coeff_of_mem_center`: the left side is `|K| · (W · L̂)(x_K)`;
* `ordCompl_mul_sum_sylow_coeff_classSum_mul` (= (4.19)): `|G|_{p'} ∑_{x ∈ S} (K̂' · L̂)(x)` is the
  character sum;
* `centralScalar_classSum_mul_character_one_out` (Burnside): `ω_χ(K̂') χ(1) = |K| χ(x_K⁻¹)`,
  which contributes the *same* factor `|K|` on the character side.

The common factor `|K|` — nonzero because a class is nonempty and the field has characteristic
zero — cancels, leaving

`|G|_{p'} · (W · L̂)(x_K) = |Syl_p| · ∑_χ χ(x_K⁻¹) ω_χ(L̂) · dim V_χ^S`.

Every coefficient here is a single value of `W · L̂`, so this is the identity that will be reduced
modulo the maximal ideal (where `|Syl_p| ≡ 1`) to give `R(z) = π(Ĝ_p z)`.

## Main results

* `OddOrder.RepresentationTheory.Modular.ordCompl_mul_coeff_sylowSum_mul`
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra OddOrder.GroupAlgebra OddOrder.GroupTheory.CenterClassSum

variable {K G : Type*} [Field K] [CharZero K] [Group G] [Fintype G]
  [DecidableEq (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι'] [Invertible (Nat.card G : K)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
variable {p : ℕ} [Fact p.Prime]

set_option maxHeartbeats 1000000 in
-- Burnside, the class-size bookkeeping and the Sylow reduction all run under the same
-- instance chains, so they are elaborated together.
set_option backward.isDefEq.respectTransparency false in
/-- **Navarro (4.23), with `|K|` cancelled inside the domain.**

`|G|_{p'} · (W · L̂)(x_K) = |Syl_p| · ∑_χ χ(x_K⁻¹) ω_χ(L̂) · dim V_χ^S`,

where `W = ∑_{P ∈ Syl_p(G)} P̂`.  Both the counting side and the character side of (4.19) carry a
factor `|K|`; it is removed here without ever leaving the ring of integers. -/
theorem ordCompl_mul_coeff_sylowSum_mul (S : Sylow p G) (C L : ConjClasses G) :
    ((ordCompl[p] (Nat.card G) : ℕ) : K)
        * ((∑ P : Sylow p G, subgroupSum K (P : Subgroup G)) * classSum L).coeff C.out
      = (Nat.card (Sylow p G) : K)
        * ∑ i : ι', (wedderburnRepresentation e i).character C.out⁻¹
            * MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum L)
            * (Module.finrank K (Representation.invariants
                ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : K) := by
  classical
  let := Fintype.ofFinite ↥(S : Subgroup G)
  have hmk : ConjClasses.mk C.out = C := by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  -- the class size, the factor being cancelled
  have hpos : 0 < OddOrder.RepresentationTheory.conjugacyClassSize C :=
    OddOrder.RepresentationTheory.conjugacyClassSize_pos C
  have hKne : (OddOrder.RepresentationTheory.conjugacyClassSize C : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr hpos.ne'
  refine mul_left_cancel₀ hKne ?_
  -- centrality of `W · L̂`
  have hWc : (∑ P : Sylow p G, subgroupSum K (P : Subgroup G))
      ∈ Subalgebra.center K (MonoidAlgebra K G) := sum_sylow_subgroupSum_mem_center
  have hLc : (classSum (k := K) L) ∈ Subalgebra.center K (MonoidAlgebra K G) :=
    classSum_mem_center _
  have hprod : ((∑ P : Sylow p G, subgroupSum K (P : Subgroup G)) * classSum L)
      ∈ Subalgebra.center K (MonoidAlgebra K G) := Subalgebra.mul_mem _ hWc hLc
  -- **Burnside on the inverse class**: the character side carries the *same* factor `|C|`
  have hburn : ∀ i : ι',
      MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum (ConjClasses.mk C.out⁻¹))
          * (wedderburnRepresentation e i).character 1
        = (OddOrder.RepresentationTheory.conjugacyClassSize C : K)
          * (wedderburnRepresentation e i).character C.out⁻¹ := by
    intro i
    rw [centralScalar_classSum_mul_character_one_out e i (ConjClasses.mk C.out⁻¹)]
    have hsize : OddOrder.RepresentationTheory.conjugacyClassSize (ConjClasses.mk C.out⁻¹)
        = OddOrder.RepresentationTheory.conjugacyClassSize C := by
      rw [OddOrder.RepresentationTheory.conjugacyClassSize_mk_inv, hmk]
    have hchar : (wedderburnRepresentation e i).character (ConjClasses.mk C.out⁻¹).out
        = (wedderburnRepresentation e i).character C.out⁻¹ := by
      refine character_eq_of_isConj _ ?_
      rw [← ConjClasses.mk_eq_mk_iff_isConj, ← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
    rw [hsize, hchar]
  -- left side: undo the class sum, then use the Sylow reduction and (4.19)
  calc (OddOrder.RepresentationTheory.conjugacyClassSize C : K)
        * (((ordCompl[p] (Nat.card G) : ℕ) : K)
          * ((∑ P : Sylow p G, subgroupSum K (P : Subgroup G)) * classSum L).coeff C.out)
      = ((ordCompl[p] (Nat.card G) : ℕ) : K)
          * ∑ u ∈ Finset.univ.filter (fun u : G => ConjClasses.mk u = C),
            ((∑ P : Sylow p G, subgroupSum K (P : Subgroup G)) * classSum L).coeff u := by
        rw [OddOrder.RepresentationTheory.sum_class_coeff_of_mem_center hprod C]; ring
    _ = (Nat.card (Sylow p G) : K)
          * (((ordCompl[p] (Nat.card G) : ℕ) : K)
            * ∑ x : ↥(S : Subgroup G),
                (classSum (k := K) (ConjClasses.mk C.out⁻¹) * classSum (k := K) L).coeff
                  (x : G)) := by
        rw [OddOrder.RepresentationTheory.sum_class_coeff_sylowSum_mul S C L]; ring
    _ = (Nat.card (Sylow p G) : K)
          * ∑ i : ι', MatrixModule.centralScalar e.toAlgHom.toRingHom i
                (classSum (ConjClasses.mk C.out⁻¹))
              * MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum L)
              * (wedderburnRepresentation e i).character 1
              * (Module.finrank K (Representation.invariants
                  ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : K) := by
        congr 1
        exact ordCompl_mul_sum_sylow_coeff_classSum_mul e S (ConjClasses.mk C.out⁻¹) L
    _ = (OddOrder.RepresentationTheory.conjugacyClassSize C : K)
          * ((Nat.card (Sylow p G) : K)
            * ∑ i : ι', (wedderburnRepresentation e i).character C.out⁻¹
                * MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum L)
                * (Module.finrank K (Representation.invariants
                    ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : K)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        linear_combination ((Nat.card (Sylow p G) : K)
          * MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum L)
          * (Module.finrank K (Representation.invariants
              ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : K)) * hburn i

end OddOrder.RepresentationTheory.Modular
