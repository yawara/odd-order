/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlock
import OddOrder.GroupTheory.RepresentationTheory.Modular.SecondMainBlockOfIrr

/-!
# The support of `d^x_{χ ·}` seen through `C_G(x) ↠ C_G(x)/N`

Navarro's display on p. 141 expands `χ(x u)` in a basic set of the principal block of
`C_G(x)/⟨x⟩`.  The basic set only expresses `φ_μ` for `μ ∈ IBr(B_0(C_G(x)/⟨x⟩))`
(`sum_basicDecompositionNumber_eq_character_of_support`), so the expansion needs the column
`d^x_{χ ·}` to vanish off that set.

That is what this file provides.  For `χ ∈ Irr(B_0(G))` the second main theorem
(`generalizedDecompositionNumber_eq_zero_of_blockOfIrr_ne`) kills `d^x_{χμ}` unless the block of
`μ` induces `B_0(G)`, and the converse third main theorem (`hconv`) makes that block
`B_0(C_G(x))`; Navarro (7.6) (`mk_eq_principalBlock_quotientPi_of_mem`, supplied here as `hbij`)
then moves it to `B_0(C_G(x)/N)`.

## Main results

* `OddOrder.RepresentationTheory.Modular.generalizedDecompositionNumber_eq_zero_of_quotient_ne`

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (5.8), (6.?), (7.6), p. 141.
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsIntegrallyClosed 𝒪]
  [IsAlgClosed (FractionRing 𝒪)]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)]
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ιG : Type*} {nnG : ιG → Type*} [∀ i, Fintype (nnG i)] [∀ i, DecidableEq (nnG i)]
  [Finite ιG] [∀ i, Nonempty (nnG i)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [Finite ι'] [∀ i, Nonempty (m i)]
variable {κ : Type*} {mG : κ → Type*} [∀ i, Fintype (mG i)] [∀ i, DecidableEq (mG i)]
  [Finite κ] [∀ i, Nonempty (mG i)]

set_option maxHeartbeats 1000000 in
-- The second main theorem it specialises carries the whole block chain.
omit [Finite κ] in
/-- **The column `d^x_{χ ·}` is supported on `IBr(B_0(C_G(x)/N))`** for `χ ∈ Irr(B_0(G))`.

Three inputs compose: the second main theorem kills `d^x_{χμ}` unless `μ`'s block induces the
block of `χ`; the converse third main theorem `hconv` identifies that block as `B_0(C_G(x))` when
`χ ∈ Irr(B_0(G))`; and Navarro (7.6), passed in as `hbij`, moves `B_0(C_G(x))` to
`B_0(C_G(x)/N)`. -/
theorem generalizedDecompositionNumber_eq_zero_of_quotient_ne (hp : p.Prime)
    {x : G} (hx : IsPElement p x) [Fintype ↥(centralizerOf x)]
    (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
    (eG : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (mG i) (mG i) K)
    {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
    (hπG : Function.Surjective πG)
    (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
    {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
      ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
      π (c • a) = c • π a)
    (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
    (hnilH : ∀ z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
      blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
    (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
      blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
    {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
    {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
    (hconv : ∀ b : Block π hπ hlin,
      inducedBlockOfCentralizer x π hπ hlin πG hπG hlinG hnilG hp hx b
        = principalBlock πG hπG hlinG hnilG → b = principalBlock π hπ hlin hnilH)
    {P : ι → Prop} (hbij : ∀ ν : ι,
      Quotient.mk (blockSetoid π hπ hlin) ν = principalBlock π hπ hlin hnilH → P ν)
    {i : κ} (hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG)
    {μ : ι} (hμ : ¬ P μ) :
    generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
        ((wedderburnRepresentation eG i).character)
        (fun _ _ hgh => character_eq_of_isConj _ hgh) μ = 0 := by
  refine generalizedDecompositionNumber_eq_zero_of_blockOfIrr_ne hp hx e eG hπG hlinG hπ hlin
    hkerJ hnilH hnilG hω hω' hζ hζk hζK ?_
  rw [hi]
  exact fun hc => hμ (hbij μ (hconv _ hc))

end OddOrder.RepresentationTheory.Modular
