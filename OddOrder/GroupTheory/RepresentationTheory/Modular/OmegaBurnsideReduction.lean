/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.CentralScalarBridge
import OddOrder.GroupTheory.RepresentationTheory.Modular.CenterReduction
import OddOrder.GroupTheory.RepresentationTheory.Modular.OmegaBurnside

/-!
# Navarro (4.19) over the valuation ring

`ordCompl_mul_sum_sylow_coeff_classSum_mul` is an identity in the splitting field `K`, but every
term is the image of an element of `𝒪`:

* the coefficients of `K̂ · L̂'` are the structure constants, already defined over `𝒪`;
* `ω_χ(K̂)` is the lattice central character (`algebraMap_centralScalar_eq`);
* `χ(1)` and `dim V_χ^S` are natural numbers.

So the identity descends to `𝒪`, where it can be reduced modulo the maximal ideal.  Reducing and
grouping the sum over the blocks — the reduction of `ω_χ` is the block character, so it is
constant on each `Irr(B)` — gives Navarro (4.19) in the residue field.

## Main results

* `OddOrder.RepresentationTheory.Modular.ordCompl_mul_sum_sylow_coeff_classSum_mul_over` — the
  identity over `𝒪`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory.CenterClassSum

variable {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [Field K] [CharZero K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Invertible (Nat.card G : K)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι']
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)

set_option maxHeartbeats 1200000 in
-- Both central characters and the coefficient transport are unified at once.
/-- **Navarro (4.19) over `𝒪`.**  Every term of the `K`-identity is the image of an element of
`𝒪`, so the identity descends. -/
theorem ordCompl_mul_sum_sylow_coeff_classSum_mul_over {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    [Fintype ↥(S : Subgroup G)] (C D : ConjClasses G) :
    ((ordCompl[p] (Nat.card G) : ℕ) : 𝒪)
        * ∑ x : ↥(S : Subgroup G), (classSum (k := 𝒪) C * classSum (k := 𝒪) D).coeff (x : G)
      = ∑ i : ι',
          centralScalar K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
              (exists_smul_id_of_commute_wedderburnLattice e i)
              ⟨classSum (k := 𝒪) C, classSum_mem_center C⟩
            * centralScalar K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
              (exists_smul_id_of_commute_wedderburnLattice e i)
              ⟨classSum (k := 𝒪) D, classSum_mem_center D⟩
            * (Fintype.card (m i) : 𝒪)
            * (Module.finrank K (Representation.invariants
                ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : 𝒪) := by
  classical
  refine FaithfulSMul.algebraMap_injective 𝒪 K ?_
  rw [map_mul, map_natCast, map_sum, map_sum]
  have hcoeff : ∀ x : ↥(S : Subgroup G),
      algebraMap 𝒪 K ((classSum (k := 𝒪) C * classSum (k := 𝒪) D).coeff (x : G))
        = (classSum (k := K) C * classSum (k := K) D).coeff (x : G) := by
    intro x
    have hprod : MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K)
        (classSum (k := 𝒪) C * classSum (k := 𝒪) D)
        = classSum (k := K) C * classSum (k := K) D := by
      rw [map_mul, mapRingHom_classSum, mapRingHom_classSum]
    rw [← MonoidAlgebra.coeff_mapRingHom, hprod]
  rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hcoeff x,
    ordCompl_mul_sum_sylow_coeff_classSum_mul e S C D]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, map_mul, map_natCast, map_natCast,
    algebraMap_centralScalar_eq e i ⟨classSum (k := 𝒪) C, classSum_mem_center C⟩,
    algebraMap_centralScalar_eq e i ⟨classSum (k := 𝒪) D, classSum_mem_center D⟩,
    mapRingHom_classSum, mapRingHom_classSum]
  congr 2
  rw [Representation.char_one, Module.finrank_fintype_fun_eq_card]

end OddOrder.RepresentationTheory.Modular
