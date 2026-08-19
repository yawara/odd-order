/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.SubgroupSumWedderburn
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockKernel
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlockKernel

/-!
# Navarro (6.13): the Cartan matrix of the principal block

Let `G = N·P` with `N ⊴ G` of order prime to `p` and `P` a `p`-subgroup — the shape of a group
with a normal `p`-complement.  Then `Irr(B_0)` is exactly the set of ordinary irreducibles killed
by `N`:

`(∀ n ∈ N, ρ_i(n) = 1) ↔ χ_i ∈ Irr(B_0)`.

* (⟸) the central character of `B_0` is the augmentation, so `λ_{B_0}(N̂*) = |N|* ≠ 0`, and a
  block on which `N̂` acts invertibly kills `N`;
* (⟹) then `λ_{B(χ_i)}(N̂*) = |N|* ≠ 0`, so `B(χ_i)` kills `N`, hence — since `G = N·P` — kills
  all of `G`; and there is only one block doing that.

Feeding this into `card_mul_sum_sq_eq_card` (the two trace computations) gives Navarro's

`∑_{χ ∈ Irr(B_0)} χ(1)² = |G| / |N| = |G|_p`,

i.e. the Cartan matrix of `B_0` is the `1 × 1` matrix `(|G|_p)`.

## Main results

* `OddOrder.RepresentationTheory.Modular.forall_eq_one_iff_blockOfIrr_eq_principalBlock`
* `OddOrder.RepresentationTheory.Modular.card_mul_sum_sq_principalBlock` — the Cartan value
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupAlgebra OddOrder.GroupTheory
open OddOrder.MatrixModule

variable {p : ℕ} [Fact p.Prime] {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)]
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
  {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

/-! ### The ordinary side: `N̂` acts invertibly exactly when `N` is killed -/

-- `Fintype G` is what makes `subgroupSum` (which needs `Finite G`) elaborate in the statement;
-- the section fixes it, so it cannot be replaced by `Finite` here.
set_option linter.unusedFintypeInType false in
omit [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] in
/-- The `i`-th ordinary irreducible kills `N` exactly when `N̂` acts invertibly on it. -/
theorem centralScalar_subgroupSum_ne_zero_iff [CharZero K] {N : Subgroup G} (hN : N.Normal)
    (i : ι') :
    MatrixModule.centralScalar e.toAlgHom.toRingHom i (subgroupSum K N) ≠ 0
      ↔ ∀ n ∈ N, wedderburnRepresentation e i n = 1 := by
  constructor
  · intro hne n hn
    have h1 : e (MonoidAlgebra.single n (1 : K)) i = 1 :=
      pi_single_eq_one_of_isUnit_centralScalar e.toAlgHom.toRingHom i e.surjective hN
        (isUnit_iff_ne_zero.mpr hne) hn
    change Matrix.toLinAlgEquiv' (e (MonoidAlgebra.single n (1 : K)) i) = 1
    rw [h1, map_one]
  · intro hker
    have hsum : ((Pi.evalAlgHom K _ i).comp e.toAlgHom) (subgroupSum K N)
        = (Nat.card ↥N : ℕ) • (1 : Matrix (m i) (m i) K) := by
      refine map_subgroupSum_of_forall_map_single_eq_one _ fun n hn => ?_
      have := hker n hn
      apply (Matrix.toLinAlgEquiv' (R := K) (n := m i)).injective
      rw [map_one]
      exact this
    have hval : MatrixModule.centralScalar e.toAlgHom.toRingHom i (subgroupSum K N)
        = ((Nat.card ↥N : ℕ) : K) := by
      rw [MatrixModule.centralScalar]
      change (e (subgroupSum K N) i) _ _ = _
      rw [show e (subgroupSum K N) i = (Nat.card ↥N : ℕ) • (1 : Matrix (m i) (m i) K) from hsum]
      simp
    rw [hval]
    exact_mod_cast Nat.cast_ne_zero.mpr Nat.card_pos.ne'

/-! ### The bridge to the principal block -/

set_option maxHeartbeats 1600000 in
-- Both central characters (ordinary lattice and residue field) are in play at once.
omit [IsPModularSystem p 𝒪] in
/-- **`Irr(B_0)` is exactly the set of ordinary irreducibles killed by `N`.** -/
theorem forall_eq_one_iff_blockOfIrr_eq_principalBlock [CharP (ResidueField 𝒪) p]
    {N P : Subgroup G} (hN : N.Normal) (hNp : ¬ p ∣ Nat.card ↥N) (hP : IsPGroup p ↥P)
    (hsup : N ⊔ P = ⊤) (i : ι') :
    (∀ n ∈ N, wedderburnRepresentation e i n = 1)
      ↔ blockOfIrr e hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG := by
  classical
  have := hN
  set zN' : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G) :=
    ⟨subgroupSum (ResidueField 𝒪) N, subgroupSum_mem_center hN⟩ with hzN'
  have hcard : ((Nat.card ↥N : ℕ) : ResidueField 𝒪) ≠ 0 := fun h =>
    hNp ((CharP.cast_eq_zero_iff (ResidueField 𝒪) p _).mp h)
  constructor
  · -- `N` killed ⟹ the block of `χ_i` kills `G`, and only `B_0` does that
    intro hker
    have hlam : blockCharacter πG hπG hlinG (blockOfIrr e hπG hlinG hnilG i) zN'
        = ((Nat.card ↥N : ℕ) : ResidueField 𝒪) :=
      blockCharacter_subgroupSum e hπG hlinG hnilG rfl hN hker
    obtain ⟨j, hj⟩ := Quotient.exists_rep (blockOfIrr e hπG hlinG hnilG i)
    obtain ⟨j₀, hj₀⟩ := Quotient.exists_rep (principalBlock πG hπG hlinG hnilG)
    have hjscal : MatrixModule.centralScalar πG j (subgroupSum (ResidueField 𝒪) N)
        = ((Nat.card ↥N : ℕ) : ResidueField 𝒪) := by
      rw [show MatrixModule.centralScalar πG j (subgroupSum (ResidueField 𝒪) N)
          = MatrixModule.centralCharacterAlg πG j hπG hlinG zN' from rfl,
        ← blockCharacter_mk πG hπG hlinG j, hj, hlam]
    have hjN : ∀ u ∈ N, πG (MonoidAlgebra.single u (1 : ResidueField 𝒪)) j = 1 := fun u hu =>
      pi_single_eq_one_of_isUnit_centralScalar πG j hπG hN
        (isUnit_iff_ne_zero.mpr (by rw [hjscal]; exact hcard)) hu
    have hjG : ∀ g : G, πG (MonoidAlgebra.single g (1 : ResidueField 𝒪)) j = 1 := by
      intro g
      apply (Matrix.toLinAlgEquiv' (R := ResidueField 𝒪) (n := nnG j)).injective
      rw [map_one]
      refine blockRepresentation_eq_one_of_sup_eq_top πG hπG hlinG hP hsup j (fun u hu => ?_) g
      change Matrix.toLinAlgEquiv' (πG (MonoidAlgebra.single u (1 : ResidueField 𝒪)) j) = 1
      rw [hjN u hu, map_one]
    have hj₀G : ∀ g : G, πG (MonoidAlgebra.single g (1 : ResidueField 𝒪)) j₀ = 1 := fun g =>
      pi_single_eq_one_principalBlock_of_sup_eq_top πG hπG hlinG hnilG hNp hP hsup hj₀ g
    have : j = j₀ := eq_of_forall_pi_single_eq_one πG hπG hlinG hjG hj₀G
    rw [← hj, this, hj₀]
  · -- `χ_i ∈ Irr(B_0)` ⟹ `λ_{B_0}(N̂*) = |N|* ≠ 0`, and that forces `N` to be killed
    intro hiB
    refine forall_eq_one_of_residue_centralScalar_ne_zero (𝒪 := 𝒪) e hN i ?_
    have hbridge := blockCharacter_blockOfLattice_mapRingHom K
      ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
      (exists_smul_id_of_commute_wedderburnLattice e i) residue_surjective πG hπG hlinG hnilG
      ⟨subgroupSum 𝒪 N, subgroupSum_mem_center hN⟩ (z' := zN')
      (mapRingHom_subgroupSum _ N)
    rw [show blockOfLattice K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
        (exists_smul_id_of_commute_wedderburnLattice e i) residue_surjective πG hπG hlinG hnilG
        = blockOfIrr e hπG hlinG hnilG i from rfl, hiB,
      blockCharacter_principalBlock_subgroupSum πG hπG hlinG hnilG hN] at hbridge
    rw [← hbridge]
    exact hcard

set_option maxHeartbeats 1600000 in
-- Rewriting the filter needs the equivalence above under all its instance chains.
open scoped Classical in
/-- **Navarro (6.13): the Cartan matrix of the principal block is `(|G|_p)`.**

`|N| · ∑_{χ ∈ Irr(B_0)} χ(1)² = |G|`, so with `N` a normal `p`-complement the sum is `|G|_p`. -/
theorem card_mul_sum_sq_principalBlock [Fintype ι'] [CharP (ResidueField 𝒪) p]
    {N P : Subgroup G} (hN : N.Normal) (hNp : ¬ p ∣ Nat.card ↥N) (hP : IsPGroup p ↥P)
    (hsup : N ⊔ P = ⊤) :
    ((Nat.card ↥N : ℕ) : K)
        * ∑ i ∈ Finset.univ.filter
            (fun i => blockOfIrr e hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG),
          (Fintype.card (m i) : K) ^ 2
      = ((Nat.card G : ℕ) : K) := by
  classical
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  rw [← card_mul_sum_sq_eq_card e hN]
  congr 2
  refine Finset.filter_congr fun i _ => ?_
  rw [centralScalar_subgroupSum_ne_zero_iff e hN i,
    forall_eq_one_iff_blockOfIrr_eq_principalBlock e hπG hlinG hnilG hN hNp hP hsup i]

end OddOrder.RepresentationTheory.Modular
