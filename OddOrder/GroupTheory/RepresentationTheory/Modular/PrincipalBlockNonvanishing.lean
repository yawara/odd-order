/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.AugmentationIdeal
import OddOrder.GroupTheory.PRegularElementCount
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockIdempotentOrdinary
import OddOrder.GroupTheory.RepresentationTheory.Modular.PRegularSumBlock
import OddOrder.GroupTheory.RepresentationTheory.SumCharacterInvariants

/-!
# A character of the principal block does not vanish on all `p`-singular elements

If `p` divides `|G|` and `χ ∈ Irr(B_0)`, then `χ(x) ≠ 0` for at least one `p`-singular `x`.

This is what Brauer's proof of Theorem (7.2) needs: if the generalised decomposition number
`d^t_{χ 1}` vanished, `χ` would vanish on every `2`-singular element, and Navarro's (3.18)
would make `B_0` a block of defect `0` — contradicting that the defect groups of the principal
block are the Sylow subgroups.

The route taken here is shorter than Navarro's (3.18)(d) ⟹ (e), which needs the integrality of
`e_χ` and Theorem (3.9).  Only `Ĝ⁰` is used:

* `ω_χ(Ĝ⁰) · χ(1) = ∑_{g ∈ G⁰} χ(g)` (`centralScalar_pRegularSum_mul_character_one`), and if `χ`
  vanishes on the `p`-singular elements the right side is `∑_{g ∈ G} χ(g) = |G| · dim V^G`;
* `ω_χ(Ĝ⁰)` is a **unit of `𝒪`**, because its residue is the block character
  `λ_{B_0}(Ĝ⁰) = |G⁰|*` and `p ∤ |G⁰|` (`not_dvd_card_isPRegular`).

If `dim V^G = 0` the first identity reads `unit · χ(1) = 0`, which is absurd.  If `dim V^G ≠ 0`
then the representation is trivial (`forall_apply_eq_of_invariants_ne_bot`), so `χ` is nowhere
zero — and Cauchy supplies a `p`-singular element.

## Main results

* `OddOrder.RepresentationTheory.Modular.forall_apply_eq_of_invariants_ne_bot` — a Wedderburn
  block with a nonzero invariant vector is the trivial representation
* `OddOrder.RepresentationTheory.Modular.not_dvd_card_of_character_eq_zero_of_pSingular`
* `OddOrder.RepresentationTheory.Modular.exists_not_isPRegular_character_ne_zero`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra MatrixModule OddOrder.GroupAlgebra OddOrder.GroupTheory

/-! ### A Wedderburn block with an invariant vector is trivial -/

section Invariants

variable {K G : Type*} [Field K] [Group G] {ι' : Type*} {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K) (i : ι')

/-- **On an invariant vector the whole `i`-th matrix block acts through the augmentation.**
Both sides are `K`-linear in `a` and agree on the group elements. -/
theorem mulVec_eq_augmentation_smul {v : m i → K}
    (hv : ∀ g : G, wedderburnRepresentation e i g v = v) (a : MonoidAlgebra K G) :
    (e a i).mulVec v = OddOrder.Algebra.augmentation K G a • v := by
  induction a using MonoidAlgebra.induction_on with
  | hM g =>
    rw [OddOrder.Algebra.augmentation_of, one_smul, MonoidAlgebra.of_apply]
    exact hv g
  | hadd x y hx hy =>
    rw [map_add, Pi.add_apply, Matrix.add_mulVec, hx, hy, map_add, add_smul]
  | hsmul r x hx =>
    rw [map_smul, Pi.smul_apply, Matrix.smul_mulVec, hx, map_smul, smul_smul,
      smul_eq_mul]

/-- **A Wedderburn block with a nonzero invariant vector is the trivial representation.**

The matrices `e a i` act on an invariant `v` by the scalar `ε(a)`, and `e` is onto the `i`-th
factor; taking `M` with a single nonzero column shows that `v` spans, so `G` fixes everything. -/
theorem forall_apply_eq_of_invariants_ne_bot
    (hbot : Representation.invariants (wedderburnRepresentation e i) ≠ ⊥)
    (g : G) (w : m i → K) : wedderburnRepresentation e i g w = w := by
  classical
  obtain ⟨v, hvmem, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hv : ∀ g : G, wedderburnRepresentation e i g v = v := fun g =>
    (Representation.mem_invariants _ _).mp hvmem g
  obtain ⟨j, hj⟩ : ∃ j : m i, v j ≠ 0 := Function.ne_iff.mp hv0
  -- `v` spans: the matrix whose `j`-th column is `w` sends `v` to `(v j) • w`
  have hspan : ∀ w : m i → K, w ∈ Submodule.span K {v} := by
    intro w
    set M : Matrix (m i) (m i) K := Matrix.of fun l j' => if j' = j then w l else 0 with hM
    have hMv : M.mulVec v = v j • w := by
      funext l
      rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl fun j' (_ : j' ∈ Finset.univ) =>
        show M l j' * v j' = if j' = j then w l * v j' else 0 by
          rw [hM]; split <;> simp_all]
      rw [Finset.sum_ite_eq' Finset.univ j fun j' => w l * v j', if_pos (Finset.mem_univ _)]
      ring
    obtain ⟨a, ha⟩ : ∃ a : MonoidAlgebra K G, e a i = M :=
      ⟨e.symm (Pi.single i M), by rw [AlgEquiv.apply_symm_apply, Pi.single_eq_same]⟩
    have hmem : v j • w ∈ Submodule.span K {v} := by
      rw [← hMv, ← ha, mulVec_eq_augmentation_smul e i hv a]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    have := Submodule.smul_mem _ (v j)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at this
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan w)
  rw [← hc, map_smul, hv g]

end Invariants

/-! ### The principal block -/

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [CharZero K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] [Invertible (Nat.card G : K)]
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

set_option maxHeartbeats 1600000 in
-- The lattice and the Wedderburn central characters are both in play, as in (4.19).
omit [CharZero K] [Invertible (Nat.card G : K)] in
open scoped Classical in
/-- **`ω_{χ_i}(Ĝ⁰)` is a unit of `𝒪` for `χ_i ∈ Irr(B_0)`.**  Its residue is the block character
`λ_{B_0}(Ĝ⁰) = |G⁰|*`, and `p ∤ |G⁰|`. -/
theorem isUnit_centralScalar_pRegularSum_of_blockOfIrr_principal [Fact p.Prime] (i : ι')
    (hi : blockOfIrr e hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG) :
    IsUnit (centralScalar K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
      (exists_smul_id_of_commute_wedderburnLattice e i)
      ⟨pRegularSum p 𝒪, pRegularSum_mem_center⟩) := by
  classical
  rw [isUnit_iff_residue_ne_zero]
  rw [← blockCharacter_blockOfLattice_mapRingHom K _
    (exists_smul_id_of_commute_wedderburnLattice e i) residue_surjective πG hπG hlinG hnilG
    (z := ⟨pRegularSum p 𝒪, pRegularSum_mem_center⟩)
    (z' := ⟨pRegularSum p (ResidueField 𝒪), pRegularSum_mem_center⟩)
    (by exact mapRingHom_pRegularSum (residue 𝒪))]
  rw [show blockOfLattice K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
      (exists_smul_id_of_commute_wedderburnLattice e i) residue_surjective πG hπG hlinG hnilG
      = principalBlock πG hπG hlinG hnilG from hi,
    blockCharacter_principalBlock_pRegularSum πG hπG hlinG hnilG p]
  rw [OddOrder.GroupTheory.card_filter_isPRegular]
  intro h
  exact not_dvd_card_isPRegular (G := G) (Fact.out (p := p.Prime))
    ((CharP.cast_eq_zero_iff (ResidueField 𝒪) p _).mp h)

set_option maxHeartbeats 1600000 in
-- Same instance chains.
omit [Invertible (Nat.card G : K)] in
open scoped Classical in
/-- **A character of the principal block cannot vanish on every `p`-singular element** when
`p ∣ |G|` (Navarro (3.18) in the form Theorem (7.2) uses it). -/
theorem not_dvd_card_of_character_eq_zero_of_pSingular [Fact p.Prime] (i : ι')
    (hi : blockOfIrr e hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG)
    (hvan : ∀ x : G, ¬ IsPRegular p x → (wedderburnRepresentation e i).character x = 0) :
    ¬ p ∣ Nat.card G := by
  classical
  intro hdvd
  -- the `p`-regular sum picks up the whole character sum
  have hsum : ∑ g ∈ Finset.univ.filter (fun g : G => IsPRegular p g),
        (wedderburnRepresentation e i).character g
      = ∑ g : G, (wedderburnRepresentation e i).character g := by
    refine Finset.sum_subset
      (Finset.filter_subset (fun g : G => IsPRegular p g) Finset.univ) fun g _ hg => ?_
    exact hvan g fun hreg => hg (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreg⟩)
  have htotal : ∑ g : G, (wedderburnRepresentation e i).character g
      = (Fintype.card G : K)
        * (Module.finrank K (Representation.invariants (wedderburnRepresentation e i)) : K) :=
    OddOrder.RepresentationTheory.sum_character_eq_card_mul_finrank_invariants _
  have hchar1 : (wedderburnRepresentation e i).character (1 : G) = (Fintype.card (m i) : K) := by
    rw [Representation.char_one, Module.finrank_fintype_fun_eq_card]
  have hcard1 : ((Fintype.card (m i) : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- the central character of `Ĝ⁰` is a unit
  have hunit := isUnit_centralScalar_pRegularSum_of_blockOfIrr_principal (𝒪 := 𝒪) (p := p)
    e hπG hlinG hnilG i hi
  have hbridge : algebraMap 𝒪 K (centralScalar K
        ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
        (exists_smul_id_of_commute_wedderburnLattice e i)
        ⟨pRegularSum p 𝒪, pRegularSum_mem_center⟩)
      = MatrixModule.centralScalar e.toAlgHom.toRingHom i (pRegularSum p K) := by
    rw [algebraMap_centralScalar_eq e i ⟨pRegularSum p 𝒪, pRegularSum_mem_center⟩]
    exact congrArg _ (mapRingHom_pRegularSum (algebraMap 𝒪 K))
  have hne : MatrixModule.centralScalar e.toAlgHom.toRingHom i (pRegularSum p K) ≠ 0 := by
    rw [← hbridge]
    intro h
    exact hunit.ne_zero (FaithfulSMul.algebraMap_injective 𝒪 K (by rw [h, map_zero]))
  -- Burnside: `ω(Ĝ⁰) · χ(1) = ∑_{g ∈ G⁰} χ(g)`
  have hburn := centralScalar_pRegularSum_mul_character_one e i p
  rw [hsum, htotal] at hburn
  -- the invariants cannot be trivial
  have hinv : Representation.invariants (wedderburnRepresentation e i) ≠ ⊥ := by
    intro hzero
    rw [hzero, finrank_bot, Nat.cast_zero, mul_zero] at hburn
    rcases mul_eq_zero.mp hburn with h | h
    · exact hne h
    · rw [hchar1] at h
      exact hcard1 h
  -- so the representation is trivial, hence nowhere zero; Cauchy gives a `p`-singular element
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := G) p
    (by rwa [← Nat.card_eq_fintype_card])
  have hxsing : ¬ IsPRegular p x := by rw [IsPRegular, not_not, hx]
  have hgg : (wedderburnRepresentation e i) x = (wedderburnRepresentation e i) 1 := by
    refine LinearMap.ext fun w => ?_
    rw [forall_apply_eq_of_invariants_ne_bot e i hinv x w, map_one]
    rfl
  have hchar : (wedderburnRepresentation e i).character x
      = (wedderburnRepresentation e i).character 1 := by
    rw [Representation.character, Representation.character, hgg]
  rw [hvan x hxsing, hchar1] at hchar
  exact hcard1 hchar.symm

set_option maxHeartbeats 1600000 in
-- Same instance chains.
omit [Invertible (Nat.card G : K)] in
open scoped Classical in
/-- The contrapositive form: for `p ∣ |G|` a character of the principal block is nonzero at some
`p`-singular element. -/
theorem exists_not_isPRegular_character_ne_zero [Fact p.Prime] (i : ι')
    (hi : blockOfIrr e hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG)
    (hdvd : p ∣ Nat.card G) :
    ∃ x : G, ¬ IsPRegular p x ∧ (wedderburnRepresentation e i).character x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact not_dvd_card_of_character_eq_zero_of_pSingular e hπG hlinG hnilG i hi hcon hdvd

end OddOrder.RepresentationTheory.Modular
