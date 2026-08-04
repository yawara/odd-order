/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.CartanMatrix
import OddOrder.GroupTheory.RepresentationTheory.Modular.OmegaBurnsideReduction
import OddOrder.GroupTheory.RepresentationTheory.Modular.OmegaBurnsideSylowSum

/-!
# Navarro (4.23) over the valuation ring, and its reduction

`ordCompl_mul_coeff_sylowSum_mul` is the `|K|`-free identity

`|G|_{p'} · (W · L̂)(x_K) = |Syl_p| · ∑_χ χ(x_K⁻¹) ω_χ(L̂) · dim V_χ^S`,

an identity in the splitting field `K` all of whose terms are images of elements of `𝒪`:
the coefficients of `W · L̂` are integers, `χ(x_K⁻¹)` is the trace of a lattice
(`ordinaryCharacter`), `ω_χ(L̂)` is the lattice central character, and `dim V_χ^S` is a natural
number.  So it descends, and can be reduced.

On reduction `|Syl_p|` becomes `1` (`card_sylow_modEq_one`), `W` becomes `Ĝ_p`
(`pElementSum_eq_sum_sylow`) and the sum over `Irr(G)` groups into the sum over blocks:

`|G|_{p'}* · (Ĝ_p · L̂)*(x_K) = ∑_B λ_B(L̂) · ∑_{χ ∈ Irr(B)} (χ(x_K⁻¹) · dim V_χ^S)*`.

This is the `x_K`-coefficient of Navarro's (4.23) `π(Ĝ_p z) = R(z)`, up to the page-93 evaluation
of the inner sum.

## Main results

* `OddOrder.RepresentationTheory.Modular.ordCompl_mul_coeff_sylowSum_mul_over`
* `OddOrder.RepresentationTheory.Modular.residue_ordCompl_mul_coeff_pElementSum_mul`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupAlgebra OddOrder.GroupTheory.CenterClassSum

variable {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [Field K] [CharZero K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Invertible (Nat.card G : K)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι']
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)

set_option maxHeartbeats 1200000 in
-- The coefficient transport, the lattice character and the central character are unified at once.
/-- **Navarro (4.23) over `𝒪`.**  Every term of `ordCompl_mul_coeff_sylowSum_mul` is the image of
an element of the valuation ring, so the identity descends. -/
theorem ordCompl_mul_coeff_sylowSum_mul_over [HenselianLocalRing 𝒪] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (C L : ConjClasses G) :
    ((ordCompl[p] (Nat.card G) : ℕ) : 𝒪)
        * ((∑ P : Sylow p G, subgroupSum 𝒪 (P : Subgroup G)) * classSum L).coeff C.out
      = (Nat.card (Sylow p G) : 𝒪)
        * ∑ i : ι', ordinaryCharacter (𝒪 := 𝒪) e i C.out⁻¹
            * centralScalar K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
              (exists_smul_id_of_commute_wedderburnLattice e i)
              ⟨classSum (k := 𝒪) L, classSum_mem_center L⟩
            * (Module.finrank K (Representation.invariants
                ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : 𝒪) := by
  classical
  refine FaithfulSMul.algebraMap_injective 𝒪 K ?_
  rw [map_mul, map_mul, map_natCast, map_natCast, map_sum]
  -- the coefficient of `W · L̂` is transported by the coefficient change
  have hcoeff : algebraMap 𝒪 K
      (((∑ P : Sylow p G, subgroupSum 𝒪 (P : Subgroup G)) * classSum L).coeff C.out)
      = ((∑ P : Sylow p G, subgroupSum K (P : Subgroup G)) * classSum L).coeff C.out := by
    have hprod : MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K)
        ((∑ P : Sylow p G, subgroupSum 𝒪 (P : Subgroup G)) * classSum L)
        = (∑ P : Sylow p G, subgroupSum K (P : Subgroup G)) * classSum L := by
      rw [map_mul, map_sum, mapRingHom_classSum]
      exact congrArg (· * _) (Finset.sum_congr rfl fun P _ => mapRingHom_subgroupSum _ _)
    rw [← MonoidAlgebra.coeff_mapRingHom, hprod]
  rw [hcoeff, ordCompl_mul_coeff_sylowSum_mul e S C L]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, map_mul, map_natCast, algebraMap_ordinaryCharacter,
    algebraMap_centralScalar_eq e i ⟨classSum (k := 𝒪) L, classSum_mem_center L⟩,
    mapRingHom_classSum]
  rfl

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
-- The Sylow count, the coefficient transport and the block characters are unified at once.
open scoped Classical in
/-- **Navarro (4.23) in the residue field.**  Reducing `ordCompl_mul_coeff_sylowSum_mul_over`
turns `|Syl_p|` into `1` (Sylow's third theorem) and `W` into `Ĝ_p` (Navarro (4.22)), and the sum
over `Irr(G)` groups into a sum over the blocks:

`|G|_{p'}* · (Ĝ_p · L̂)*(x_K) = ∑_B λ_B(L̂) · ∑_{χ ∈ Irr(B)} (χ(x_K⁻¹) · dim V_χ^S)*`.

The left side is the `x_K`-coefficient of `π(Ĝ_p L̂)`; the right side becomes the coefficient of
Navarro's `R(L̂) = ∑_B λ_B(L̂) e_B` once the inner sum is evaluated (page 93). -/
theorem residue_ordCompl_mul_coeff_pElementSum_mul [Fact p.Prime]
    [Fintype (MatrixModule.Block πG hπG hlinG)] (S : Sylow p G) (C L : ConjClasses G) :
    residue 𝒪 ((ordCompl[p] (Nat.card G) : ℕ) : 𝒪)
        * (pElementSum p (ResidueField 𝒪) (G := G) * classSum L).coeff C.out
      = ∑ B : MatrixModule.Block πG hπG hlinG,
          MatrixModule.blockCharacter πG hπG hlinG B
              ⟨classSum (k := ResidueField 𝒪) L, classSum_mem_center L⟩
            * ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
                residue 𝒪 (ordinaryCharacter (𝒪 := 𝒪) e i C.out⁻¹)
                  * (Module.finrank K (Representation.invariants
                      ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) :
                    ResidueField 𝒪) := by
  classical
  have hbase := congrArg (residue 𝒪) (ordCompl_mul_coeff_sylowSum_mul_over e S C L)
  rw [map_mul, map_mul, map_sum] at hbase
  -- Sylow's third theorem: `|Syl_p| ≡ 1 (mod p)`
  have hsyl : residue 𝒪 ((Nat.card (Sylow p G) : ℕ) : 𝒪) = 1 := by
    rw [map_natCast]
    have h := card_sylow_modEq_one p G
    simpa using (CharP.natCast_eq_natCast (ResidueField 𝒪) p).mpr h
  -- Navarro (4.22): `W` reduces to `Ĝ_p`
  have hcoeff : residue 𝒪
      (((∑ P : Sylow p G, subgroupSum 𝒪 (P : Subgroup G)) * classSum L).coeff C.out)
      = (pElementSum p (ResidueField 𝒪) (G := G) * classSum L).coeff C.out := by
    rw [pElementSum_eq_sum_sylow]
    have hprod : MonoidAlgebra.mapRingHom G (residue 𝒪)
        ((∑ P : Sylow p G, subgroupSum 𝒪 (P : Subgroup G)) * classSum L)
        = (∑ P : Sylow p G, subgroupSum (ResidueField 𝒪) (P : Subgroup G)) * classSum L := by
      rw [map_mul, map_sum, mapRingHom_classSum]
      exact congrArg (· * _) (Finset.sum_congr rfl fun P _ => mapRingHom_subgroupSum _ _)
    rw [← MonoidAlgebra.coeff_mapRingHom, hprod]
  rw [hsyl, one_mul, hcoeff] at hbase
  rw [hbase]
  -- each summand is the block character of `χ_i`'s block times the integral data
  have hterm : ∀ i : ι', residue 𝒪
      (ordinaryCharacter (𝒪 := 𝒪) e i C.out⁻¹
        * centralScalar K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
          (exists_smul_id_of_commute_wedderburnLattice e i)
          ⟨classSum (k := 𝒪) L, classSum_mem_center L⟩
        * (Module.finrank K (Representation.invariants
            ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : 𝒪))
      = MatrixModule.blockCharacter πG hπG hlinG (blockOfIrr e hπG hlinG hnilG i)
            ⟨classSum (k := ResidueField 𝒪) L, classSum_mem_center L⟩
          * (residue 𝒪 (ordinaryCharacter (𝒪 := 𝒪) e i C.out⁻¹)
            * (Module.finrank K (Representation.invariants
                ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) :
              ResidueField 𝒪)) := by
    intro i
    have hL : residue 𝒪 (centralScalar K
        ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
        (exists_smul_id_of_commute_wedderburnLattice e i)
        ⟨classSum (k := 𝒪) L, classSum_mem_center L⟩)
        = MatrixModule.blockCharacter πG hπG hlinG (blockOfIrr e hπG hlinG hnilG i)
          ⟨classSum (k := ResidueField 𝒪) L, classSum_mem_center L⟩ :=
      (blockCharacter_blockOfLattice_mapRingHom K _
        (exists_smul_id_of_commute_wedderburnLattice e i) residue_surjective πG hπG hlinG hnilG
        ⟨classSum (k := 𝒪) L, classSum_mem_center L⟩
        (z' := ⟨classSum (k := ResidueField 𝒪) L, classSum_mem_center L⟩)
        (mapRingHom_classSum (residue 𝒪) L)).symm
    rw [map_mul, map_mul, map_natCast, hL]
    ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i]
  rw [← Finset.sum_fiberwise Finset.univ (blockOfIrr e hπG hlinG hnilG) fun i =>
    MatrixModule.blockCharacter πG hπG hlinG (blockOfIrr e hπG hlinG hnilG i)
        ⟨classSum (k := ResidueField 𝒪) L, classSum_mem_center L⟩
      * (residue 𝒪 (ordinaryCharacter (𝒪 := 𝒪) e i C.out⁻¹)
        * (Module.finrank K (Representation.invariants
            ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) :
          ResidueField 𝒪))]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

end Reduction

end OddOrder.RepresentationTheory.Modular
