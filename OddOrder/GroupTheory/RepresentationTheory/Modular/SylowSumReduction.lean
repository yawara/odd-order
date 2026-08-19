/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockSumOverPSubgroup
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockIdempotentOrdinary
import OddOrder.GroupTheory.RepresentationTheory.Modular.CartanMatrix
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryIdempotent
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
* `OddOrder.RepresentationTheory.Modular.sum_block_character_mul_finrank_invariants` — the
  page-93 evaluation of the inner sum
* `OddOrder.RepresentationTheory.Modular.ordCompl_mul_coeff_blockIdempotentLift` — the same over
  `𝒪`, in terms of a lift of the block idempotent
* `OddOrder.RepresentationTheory.Modular.coeff_pElementSum_mul_classSum` — **Navarro (4.23)**,
  in coefficient form
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

set_option maxHeartbeats 800000 in
-- The Sylow cardinality, the invariants count and the idempotent coefficients are unified at once.
omit [IsPModularSystem p 𝒪] in
open scoped Classical in
/-- **Navarro (4.19), page 93, evaluated.**  Summing the block's characters over a Sylow
`p`-subgroup collapses to the identity term (`sum_pSubgroup_sum_block_character`), and the inner
sums are the multiplicities of the trivial character:

`∑_{χ ∈ Irr(B)} χ(y⁻¹) · dim V_χ^S = |G|_{p'} · (∑_{χ ∈ Irr(B)} e_χ)(y)`.

The right-hand side is `|G|_{p'}` times the `y`-coefficient of the *lift* of the block idempotent
(`mapRingHom_blockIdempotent_eq_sum`), so this is exactly the factor of `|G|_{p'}` that cancels
against the one on the counting side of (4.23). -/
theorem sum_block_character_mul_finrank_invariants [Fact p.Prime] (S : Sylow p G)
    (B : MatrixModule.Block πG hπG hlinG) (y : G)
    (hweak : ∀ x : ↥(S : Subgroup G), (x : G) ≠ 1 →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character y⁻¹
          * (wedderburnRepresentation e i).character (x : G) = 0) :
    ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character y⁻¹
          * (Module.finrank K (Representation.invariants
              ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : K)
      = ((ordCompl[p] (Nat.card G) : ℕ) : K)
        * (∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
            ordinaryIdempotent e i).coeff y := by
  classical
  let := Fintype.ofFinite ↥(S : Subgroup G)
  have hcard : Fintype.card ↥(S : Subgroup G) = ordProj[p] (Nat.card G) := by
    rw [← Nat.card_eq_fintype_card]; exact S.card_eq_multiplicity
  have hne : ((ordProj[p] (Nat.card G) : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ (Fact.out (p := p.Prime)).pos.ne')
  refine mul_left_cancel₀ hne ?_
  -- the inner sum over `S` is `|S|` times the multiplicity of the trivial character
  have hinner : ∀ i : ι', ∑ x : ↥(S : Subgroup G),
      (wedderburnRepresentation e i).character (x : G)
      = (Fintype.card ↥(S : Subgroup G) : K)
        * (Module.finrank K (Representation.invariants
            ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : K) := by
    intro i
    rw [← OddOrder.RepresentationTheory.sum_character_eq_card_mul_finrank_invariants]
    exact Finset.sum_congr rfl fun x _ => rfl
  -- `|G|` splits, and the coefficient of `∑ e_χ` is the character sum
  have hcoeff : (∑ i ∈ Finset.univ.filter
      (fun i => blockOfIrr e hπG hlinG hnilG i = B), ordinaryIdempotent e i).coeff y
      = ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        ⅟(Nat.card G : K) * (wedderburnRepresentation e i).character 1
          * (wedderburnRepresentation e i).character y⁻¹ := by
    rw [MonoidAlgebra.coeff_finsetSum]
    exact Finset.sum_congr rfl fun i _ => coeff_ordinaryIdempotent e i y
  have hinv : ((ordProj[p] (Nat.card G) : ℕ) : K) * ((ordCompl[p] (Nat.card G) : ℕ) : K)
      * ⅟(Nat.card G : K) = 1 := by
    rw [← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self, mul_invOf_self]
  calc ((ordProj[p] (Nat.card G) : ℕ) : K)
        * ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
          (wedderburnRepresentation e i).character y⁻¹
            * (Module.finrank K (Representation.invariants
                ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : K)
      = ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
          (wedderburnRepresentation e i).character y⁻¹
            * ∑ x : ↥(S : Subgroup G), (wedderburnRepresentation e i).character (x : G) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hinner i, hcard]; ring
    _ = ∑ x : ↥(S : Subgroup G),
          ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
            (wedderburnRepresentation e i).character y⁻¹
              * (wedderburnRepresentation e i).character (x : G) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
          (wedderburnRepresentation e i).character y⁻¹
            * (wedderburnRepresentation e i).character 1 :=
        sum_pSubgroup_sum_block_character e hπG hlinG hnilG (S : Subgroup G) B y hweak
    _ = ((ordProj[p] (Nat.card G) : ℕ) : K)
          * (((ordCompl[p] (Nat.card G) : ℕ) : K)
            * (∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
                ordinaryIdempotent e i).coeff y) := by
        rw [hcoeff, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        linear_combination (-((wedderburnRepresentation e i).character 1
          * (wedderburnRepresentation e i).character y⁻¹)) * hinv

set_option maxHeartbeats 800000 in
-- The descent and the identification of the idempotent lift run under the same instance chains.
omit [IsPModularSystem p 𝒪] in
open scoped Classical in
/-- **The page-93 evaluation over `𝒪`.**  With `f` an idempotent of `Z(𝒪G)` lifting the block
idempotent `e_B`, `mapRingHom_blockIdempotent_eq_sum` identifies its image in `K[G]` with
`∑_{χ ∈ Irr(B)} e_χ`, so the previous lemma reads

`∑_{χ ∈ Irr(B)} χ(y⁻¹) · dim V_χ^S = |G|_{p'} · f(y)`

as an identity in the valuation ring. -/
theorem ordCompl_mul_coeff_blockIdempotentLift [Fact p.Prime] (S : Sylow p G)
    {B : MatrixModule.Block πG hπG hlinG} {f : Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)}
    (hidem : IsIdempotentElem f)
    {f' : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)}
    (hf : MonoidAlgebra.mapRingHom G (residue 𝒪) (f : MonoidAlgebra 𝒪 G)
      = (f' : MonoidAlgebra (ResidueField 𝒪) G))
    (hB : MatrixModule.blockCharacterPi πG hπG hlinG f' = Pi.single B 1) (y : G)
    (hweak : ∀ x : ↥(S : Subgroup G), (x : G) ≠ 1 →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character y⁻¹
          * (wedderburnRepresentation e i).character (x : G) = 0) :
    ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        ordinaryCharacter (𝒪 := 𝒪) e i y⁻¹
          * (Module.finrank K (Representation.invariants
              ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : 𝒪)
      = ((ordCompl[p] (Nat.card G) : ℕ) : 𝒪) * (f : MonoidAlgebra 𝒪 G).coeff y := by
  refine FaithfulSMul.algebraMap_injective 𝒪 K ?_
  have hterm : ∀ i : ι', algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) e i y⁻¹
        * (Module.finrank K (Representation.invariants
            ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : 𝒪))
      = (wedderburnRepresentation e i).character y⁻¹
        * (Module.finrank K (Representation.invariants
            ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : K) := by
    intro i
    rw [map_mul, map_natCast, algebraMap_ordinaryCharacter]
    rfl
  rw [map_sum, map_mul, map_natCast,
    Finset.sum_congr rfl fun i (_ : i ∈ _) => hterm i,
    sum_block_character_mul_finrank_invariants e hπG hlinG hnilG S B y hweak]
  refine congrArg _ ?_
  rw [← MonoidAlgebra.coeff_mapRingHom,
    mapRingHom_blockIdempotent_eq_sum (K := K) e hπG hlinG hnilG hidem hf hB]


set_option maxHeartbeats 1200000 in
-- The two halves of (4.23) and the cancellation run under the same instance chains.
open scoped Classical in
/-- **Navarro (4.23), coefficient form.**  For a class `C` on which weak block orthogonality
applies (in particular any `p`-regular class) and any class sum `L̂`,

`(Ĝ_p · L̂)(x_C) = ∑_B λ_B(L̂) · e_B(x_C)`,

i.e. the `x_C`-coefficient of `π(Ĝ_p L̂)` equals that of `R(L̂) = ∑_B λ_B(L̂) e_B`.

Both sides of `residue_ordCompl_mul_coeff_pElementSum_mul` carry the factor `|G|_{p'}*` — the
counting side by construction, the character side by the page-93 evaluation — and `p ∤ |G|_{p'}`,
so it cancels. -/
theorem coeff_pElementSum_mul_classSum [Fact p.Prime]
    [Fintype (MatrixModule.Block πG hπG hlinG)] (S : Sylow p G) (C L : ConjClasses G)
    {F : MatrixModule.Block πG hπG hlinG → Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)}
    {F' : MatrixModule.Block πG hπG hlinG →
      Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)}
    (hidem : ∀ B, IsIdempotentElem (F B))
    (hf : ∀ B, MonoidAlgebra.mapRingHom G (residue 𝒪) ((F B : MonoidAlgebra 𝒪 G))
      = ((F' B : MonoidAlgebra (ResidueField 𝒪) G)))
    (hB : ∀ B, MatrixModule.blockCharacterPi πG hπG hlinG (F' B) = Pi.single B 1)
    (hweak : ∀ B : MatrixModule.Block πG hπG hlinG, ∀ x : ↥(S : Subgroup G), (x : G) ≠ 1 →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character C.out⁻¹
          * (wedderburnRepresentation e i).character (x : G) = 0) :
    (pElementSum p (ResidueField 𝒪) (G := G) * classSum L).coeff C.out
      = ∑ B : MatrixModule.Block πG hπG hlinG,
          MatrixModule.blockCharacter πG hπG hlinG B
              ⟨classSum (k := ResidueField 𝒪) L, classSum_mem_center L⟩
            * ((F' B : MonoidAlgebra (ResidueField 𝒪) G)).coeff C.out := by
  classical
  -- `p ∤ |G|_{p'}`, so the common factor is invertible in the residue field
  have hne : residue 𝒪 ((ordCompl[p] (Nat.card G) : ℕ) : 𝒪) ≠ 0 := by
    rw [map_natCast]
    refine fun h => Nat.not_dvd_ordCompl (Fact.out (p := p.Prime)) (Nat.card_pos (α := G)).ne' ?_
    exact (CharP.cast_eq_zero_iff (ResidueField 𝒪) p _).mp h
  refine mul_left_cancel₀ hne ?_
  rw [residue_ordCompl_mul_coeff_pElementSum_mul e hπG hlinG hnilG S C L, Finset.mul_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  -- page 93, reduced: the inner sum is `|G|_{p'}*` times the block idempotent's coefficient
  have h93 := congrArg (residue 𝒪)
    (ordCompl_mul_coeff_blockIdempotentLift e hπG hlinG hnilG S (hidem B) (hf B) (hB B) C.out
      (hweak B))
  rw [map_sum, map_mul, map_natCast] at h93
  have hFcoeff : residue 𝒪 ((F B : MonoidAlgebra 𝒪 G).coeff C.out)
      = ((F' B : MonoidAlgebra (ResidueField 𝒪) G)).coeff C.out := by
    rw [← MonoidAlgebra.coeff_mapRingHom, hf B]
  rw [hFcoeff] at h93
  rw [Finset.sum_congr rfl fun i (_ : i ∈ _) => (map_mul (residue 𝒪) _ _).trans
    (congrArg _ (map_natCast (residue 𝒪) _))] at h93
  rw [h93, map_natCast]
  ring

end Reduction

end OddOrder.RepresentationTheory.Modular
