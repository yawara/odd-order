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
* `OddOrder.RepresentationTheory.Modular.residue_ordCompl_mul_sum_sylow_coeff` — its reduction,
  grouped by blocks
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

/-! ### The reduction, grouped by blocks -/

section Reduction

variable [HenselianLocalRing 𝒪] {p : ℕ} [IsPModularSystem p 𝒪] [Fintype (ConjClasses G)]
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    MatrixModule.blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

set_option maxHeartbeats 1600000 in
-- The block characters and the two central characters are unified at once.
omit [IsPModularSystem p 𝒪] in
open scoped Classical in
/-- **Navarro (4.19) in the residue field.**  Reducing the `𝒪`-identity and collecting the sum
over the fibres of `blockOfIrr` — the reduction of `ω_χ` is the block character, hence constant on
each `Irr(B)` — gives

`|G|_{p'}* · |Ω_{K,L}|* = ∑_B λ_B(K̂) λ_B(L̂') ∑_{χ ∈ Irr(B)} χ(1) · dim V_χ^S`. -/
theorem residue_ordCompl_mul_sum_sylow_coeff [Fact p.Prime]
    [Fintype (MatrixModule.Block πG hπG hlinG)] (S : Sylow p G)
    [Fintype ↥(S : Subgroup G)] (C D : ConjClasses G) :
    residue 𝒪 ((ordCompl[p] (Nat.card G) : ℕ) : 𝒪)
        * ∑ x : ↥(S : Subgroup G),
          residue 𝒪 ((classSum (k := 𝒪) C * classSum (k := 𝒪) D).coeff (x : G))
      = ∑ B : MatrixModule.Block πG hπG hlinG,
          MatrixModule.blockCharacter πG hπG hlinG B
              ⟨classSum (k := ResidueField 𝒪) C, classSum_mem_center C⟩
            * MatrixModule.blockCharacter πG hπG hlinG B
              ⟨classSum (k := ResidueField 𝒪) D, classSum_mem_center D⟩
            * ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
              (Fintype.card (m i) : ResidueField 𝒪)
                * (Module.finrank K (Representation.invariants
                    ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) :
                  ResidueField 𝒪) := by
  classical
  have hbase := congrArg (residue 𝒪)
    (ordCompl_mul_sum_sylow_coeff_classSum_mul_over e S C D)
  rw [map_mul, map_sum, map_sum] at hbase
  rw [hbase]
  -- each summand is the block character of `χ_i`'s block
  have hterm : ∀ i : ι', residue 𝒪
      (centralScalar K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
          (exists_smul_id_of_commute_wedderburnLattice e i)
          ⟨classSum (k := 𝒪) C, classSum_mem_center C⟩
        * centralScalar K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
          (exists_smul_id_of_commute_wedderburnLattice e i)
          ⟨classSum (k := 𝒪) D, classSum_mem_center D⟩
        * (Fintype.card (m i) : 𝒪)
        * (Module.finrank K (Representation.invariants
            ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : 𝒪))
      = MatrixModule.blockCharacter πG hπG hlinG (blockOfIrr e hπG hlinG hnilG i)
            ⟨classSum (k := ResidueField 𝒪) C, classSum_mem_center C⟩
          * MatrixModule.blockCharacter πG hπG hlinG (blockOfIrr e hπG hlinG hnilG i)
            ⟨classSum (k := ResidueField 𝒪) D, classSum_mem_center D⟩
          * ((Fintype.card (m i) : ResidueField 𝒪)
            * (Module.finrank K (Representation.invariants
                ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) :
              ResidueField 𝒪)) := by
    intro i
    have hC : residue 𝒪 (centralScalar K
        ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
        (exists_smul_id_of_commute_wedderburnLattice e i)
        ⟨classSum (k := 𝒪) C, classSum_mem_center C⟩)
        = MatrixModule.blockCharacter πG hπG hlinG (blockOfIrr e hπG hlinG hnilG i)
          ⟨classSum (k := ResidueField 𝒪) C, classSum_mem_center C⟩ :=
      (blockCharacter_blockOfLattice_mapRingHom K _
        (exists_smul_id_of_commute_wedderburnLattice e i) residue_surjective πG hπG hlinG hnilG
        ⟨classSum (k := 𝒪) C, classSum_mem_center C⟩
        (z' := ⟨classSum (k := ResidueField 𝒪) C, classSum_mem_center C⟩)
        (mapRingHom_classSum (residue 𝒪) C)).symm
    have hD : residue 𝒪 (centralScalar K
        ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
        (exists_smul_id_of_commute_wedderburnLattice e i)
        ⟨classSum (k := 𝒪) D, classSum_mem_center D⟩)
        = MatrixModule.blockCharacter πG hπG hlinG (blockOfIrr e hπG hlinG hnilG i)
          ⟨classSum (k := ResidueField 𝒪) D, classSum_mem_center D⟩ :=
      (blockCharacter_blockOfLattice_mapRingHom K _
        (exists_smul_id_of_commute_wedderburnLattice e i) residue_surjective πG hπG hlinG hnilG
        ⟨classSum (k := 𝒪) D, classSum_mem_center D⟩
        (z' := ⟨classSum (k := ResidueField 𝒪) D, classSum_mem_center D⟩)
        (mapRingHom_classSum (residue 𝒪) D)).symm
    rw [map_mul, map_mul, map_mul, map_natCast, map_natCast, hC, hD]
    ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i]
  rw [← Finset.sum_fiberwise Finset.univ (blockOfIrr e hπG hlinG hnilG) fun i =>
    MatrixModule.blockCharacter πG hπG hlinG (blockOfIrr e hπG hlinG hnilG i)
        ⟨classSum (k := ResidueField 𝒪) C, classSum_mem_center C⟩
      * MatrixModule.blockCharacter πG hπG hlinG (blockOfIrr e hπG hlinG hnilG i)
        ⟨classSum (k := ResidueField 𝒪) D, classSum_mem_center D⟩
      * ((Fintype.card (m i) : ResidueField 𝒪)
        * (Module.finrank K (Representation.invariants
            ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) :
          ResidueField 𝒪))]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

end Reduction

end OddOrder.RepresentationTheory.Modular
