/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockIdempotentLift
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockOfLattice
import OddOrder.GroupTheory.RepresentationTheory.Modular.InducedBlockCentralizer
import OddOrder.GroupTheory.RepresentationTheory.Modular.InducedBlockWitness
import OddOrder.GroupTheory.RepresentationTheory.Modular.SecondMainTheorem

/-!
# Navarro (5.2) in block language

`SecondMainTheorem.generalizedDecompositionNumber_eq_zero` asks for the witness `w` of (5.6) and
for the block idempotents in their three incarnations.  All of that is determined by the block
data itself: (5.6) (`exists_inducedBlock_witness`) produces `w` from
`b^G = B`, and the reduction `centerReduce` produces the incarnations of `f_b` over `K` and over
the residue field.

So the statement of the second main theorem takes the shape it has in the textbook: `B ∈ Bl(G)`,
`b ∈ Bl(C_G(x))` with `b^G = B`, and a character annihilated by `f_B`.

Once the annihilation hypothesis is itself read off from the block of `χ` — Navarro (3.13.a),
`apply_eq_zero_of_blockOfLattice_ne` — the statement becomes Navarro (5.8): the generalized
decomposition numbers of `χ ∈ Irr(B)` are supported on the blocks of `C_G(x)` inducing `B`.

## Main results

* `OddOrder.RepresentationTheory.Modular.generalizedDecompositionNumber_eq_zero_of_inducedBlock`
* `OddOrder.RepresentationTheory.Modular.generalizedDecompositionNumber_eq_zero_of_blockOfLattice`
  — Navarro (5.8)
* `..._eq_zero_of_inducedBlockOfCentralizer_ne` — Navarro (5.8), with the block idempotents
  produced rather than assumed
* `..._sum_generalizedDecompositionNumber_inducedBlockOfCentralizer` — Navarro (5.8) as the
  textbook states it, as a sum over the blocks inducing the block of `χ`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule
open OddOrder.GroupTheory.CenterClassSum (inducedCentralCharacter)
open OddOrder.GroupAlgebra (inclusionHom)
open scoped TensorProduct

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module 𝒪 V]
  [IsScalarTower 𝒪 K V]
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ιG : Type*} {nnG : ιG → Type*} [∀ i, Fintype (nnG i)] [∀ i, DecidableEq (nnG i)]
  [Finite ιG] [∀ i, Nonempty (nnG i)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [Finite ι'] [∀ i, Nonempty (m i)]

set_option maxHeartbeats 1000000 in
-- Two splittings, two block index sets and the three incarnations of `f_b`; unifying those
-- instance chains is what costs the heartbeats.
omit [Finite ιG] [Module 𝒪 V] [IsScalarTower 𝒪 K V] in
/-- **Brauer's second main theorem in block language, Navarro (5.2).**  Let `x` be a `p`-element,
`H = C_G(x)`, `B` a block of `G` and `b` a block of `H` with `b^G = B`.  If the block idempotent
`f_B` annihilates the module affording `χ` — this is `χ ∉ Irr(B)` — then `d^x_{χφ} = 0` for every
`φ ∈ IBr(b)`.

Compared with `generalizedDecompositionNumber_eq_zero` the witness of (5.6) and the reductions of
`f_b` are no longer asked for: they are produced from `b^G = B` and from `f_b` itself. -/
theorem generalizedDecompositionNumber_eq_zero_of_inducedBlock (hp : p.Prime) {x : G}
    (hx : IsPElement p x) [Fintype ↥(centralizerOf x)]
    -- the ordinary splitting of `K[H]` and the modular splittings of `kG` and `kH`
    (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
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
    [DecidableEq (Block πG hπG hlinG)] [DecidableEq (Block π hπ hlin)]
    {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
    {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
    (σ : Representation K G V)
    -- the two blocks and their idempotents
    {B : Block πG hπG hlinG} {b : Block π hπ hlin}
    {fB : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))} (hfB : IsIdempotentElem fB)
    (hfBc : blockCharacterPi πG hπG hlinG (centerReduce (residue 𝒪) fB) = Pi.single B 1)
    {fb : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 ↥(centralizerOf x)))}
    (hfb : IsIdempotentElem fb)
    (hfbc : blockCharacterPi π hπ hlin (centerReduce (residue 𝒪) fb) = Pi.single b 1)
    -- `b^G = B`
    (hbG : (blockCharacter πG hπG hlinG B).toLinearMap
      = inducedCentralCharacter (centralizerOf x) (blockCharacter π hπ hlin b).toLinearMap)
    -- `χ ∉ Irr(B)`
    (hσB : σ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K)
      (fB : MonoidAlgebra 𝒪 G)) = 0)
    -- `φ_j ∈ IBr(b)`
    {j : ι} (hjb : Quotient.mk (blockSetoid π hπ hlin) j = b) :
    generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
        (fun g => LinearMap.trace K V (σ g))
        (fun _ _ hgh => character_eq_of_isConj σ hgh) j = 0 := by
  classical
  haveI : Fintype (ConjClasses ↥(centralizerOf x)) := Fintype.ofFinite _
  obtain ⟨w, hwa, hwb, hwc, hwd⟩ := exists_inducedBlock_witness (centralizerOf x) (residue 𝒪)
    πG hπG hlinG π hπ hlin residue_surjective (ker_residue) hnilH hfB hfBc hfb hfbc hbG
  refine generalizedDecompositionNumber_eq_zero hp hx e hπ hlin hkerJ hω hω' hζ hζk hζK σ
    (f𝒪 := fb) (fK := centerReduce (algebraMap 𝒪 K) fb) (fk := centerReduce (residue 𝒪) fb)
    hfb rfl rfl (congrArg Subtype.val hfB)
    (fun a => (Subalgebra.mem_center_iff.mp fB.2 a).symm) hσB hwa hwb hwc hwd ?_
  rw [show centralCharacterAlg π j hπ hlin (centerReduce (residue 𝒪) fb)
      = blockCharacterPi π hπ hlin (centerReduce (residue 𝒪) fb)
        (Quotient.mk (blockSetoid π hπ hlin) j) from rfl,
    hfbc, hjb, Pi.single_eq_same]

/-! ### Navarro (5.8) -/

set_option maxHeartbeats 1000000 in
-- As above, plus the block of `χ` and its lattice.
/-- **Navarro (5.8).**  Let `x` be a `p`-element and `H = C_G(x)`.  If the block of `χ` is not the
block induced by `b ∈ Bl(H)`, then `d^x_{χφ} = 0` for every `φ ∈ IBr(b)`.  Equivalently: the
generalized decomposition numbers of `χ ∈ Irr(B)` are supported on `⋃_{b^G = B} IBr(b)`.

This is `generalizedDecompositionNumber_eq_zero_of_inducedBlock` with the annihilation hypothesis
replaced by block membership, via Navarro (3.13.a) (`apply_eq_zero_of_blockOfLattice_ne`) and the
fact that a lattice spans (`asAlgebraHom_eq_zero_of_latticeRepresentation`). -/
theorem generalizedDecompositionNumber_eq_zero_of_blockOfLattice (hp : p.Prime) {x : G}
    (hx : IsPElement p x) [Fintype ↥(centralizerOf x)]
    (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
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
    [DecidableEq (Block πG hπG hlinG)] [DecidableEq (Block π hπ hlin)]
    (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
      blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
    {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
    {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
    -- the representation affording `χ` and an invariant lattice in it
    (σ : Representation K G V) {L : Submodule 𝒪 V} [L.IsLattice K] [Nontrivial ↥L]
    (hLinv : ∀ (g : G), ∀ v ∈ L, σ g v ∈ L)
    (hEnd : ∀ E : Module.End K (K ⊗[𝒪] ↥L),
      (∀ a : MonoidAlgebra 𝒪 G, E * LinearMap.baseChange K
          ((latticeRepresentation σ hLinv).asAlgebraHom a)
        = LinearMap.baseChange K ((latticeRepresentation σ hLinv).asAlgebraHom a) * E) →
      ∃ c : K, E = c • LinearMap.id)
    -- the two blocks and their idempotents
    {B : Block πG hπG hlinG} {b : Block π hπ hlin}
    {fB : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))} (hfB : IsIdempotentElem fB)
    (hfBc : blockCharacterPi πG hπG hlinG (centerReduce (residue 𝒪) fB) = Pi.single B 1)
    {fb : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 ↥(centralizerOf x)))}
    (hfb : IsIdempotentElem fb)
    (hfbc : blockCharacterPi π hπ hlin (centerReduce (residue 𝒪) fb) = Pi.single b 1)
    (hbG : (blockCharacter πG hπG hlinG B).toLinearMap
      = inducedCentralCharacter (centralizerOf x) (blockCharacter π hπ hlin b).toLinearMap)
    -- `χ ∉ Irr(B)`: the block of `χ` is not `b^G`
    (hne : blockOfLattice K ((latticeRepresentation σ hLinv).asAlgebraHom) hEnd
      residue_surjective πG hπG hlinG hnilG ≠ B)
    {j : ι} (hjb : Quotient.mk (blockSetoid π hπ hlin) j = b) :
    generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
        (fun g => LinearMap.trace K V (σ g))
        (fun _ _ hgh => character_eq_of_isConj σ hgh) j = 0 := by
  classical
  refine generalizedDecompositionNumber_eq_zero_of_inducedBlock hp hx e hπG hlinG hπ hlin hkerJ
    hnilH hω hω' hζ hζk hζK σ hfB hfBc hfb hfbc hbG ?_ hjb
  exact asAlgebraHom_eq_zero_of_latticeRepresentation σ hLinv
    (apply_eq_zero_of_blockOfLattice_ne K _ hEnd residue_surjective πG hπG hlinG hnilG
      ker_residue hfB rfl hfBc hne)

/-! ### Navarro (5.8), with nothing left to supply -/

set_option maxHeartbeats 1000000 in
-- As above, plus the induced block and the two lifted block idempotents.
/-- **Navarro (5.8).**  For a `p`-element `x`, every block `b` of `C_G(x)` induces a block `b^G` of
`G` (`inducedBlockOfCentralizer`, Brauer's theorem for `P = ⟨x⟩`), and the block idempotents
`f_b ∈ Z(𝒪 C_G(x))`, `f_{b^G} ∈ Z(𝒪G)` exist (`exists_isIdempotentElem_blockCharacterPi_eq_single`).
So the only hypothesis left is the one that carries the content: `b^G` is not the block of `χ`.

Together with (5.1) this says that the generalized decomposition numbers of `χ ∈ Irr(B)` are
supported on `⋃_{b^G = B} IBr(b)`. -/
theorem generalizedDecompositionNumber_eq_zero_of_inducedBlockOfCentralizer_ne (hp : p.Prime)
    {x : G} (hx : IsPElement p x) [Fintype ↥(centralizerOf x)]
    (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
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
    (σ : Representation K G V) {L : Submodule 𝒪 V} [L.IsLattice K] [Nontrivial ↥L]
    (hLinv : ∀ (g : G), ∀ v ∈ L, σ g v ∈ L)
    (hEnd : ∀ E : Module.End K (K ⊗[𝒪] ↥L),
      (∀ a : MonoidAlgebra 𝒪 G, E * LinearMap.baseChange K
          ((latticeRepresentation σ hLinv).asAlgebraHom a)
        = LinearMap.baseChange K ((latticeRepresentation σ hLinv).asAlgebraHom a) * E) →
      ∃ c : K, E = c • LinearMap.id)
    -- the block of `φ_j` does not induce the block of `χ`
    {j : ι}
    (hj : inducedBlockOfCentralizer x π hπ hlin πG hπG hlinG hnilG hp hx
          (Quotient.mk (blockSetoid π hπ hlin) j)
        ≠ blockOfLattice K ((latticeRepresentation σ hLinv).asAlgebraHom) hEnd
            residue_surjective πG hπG hlinG hnilG) :
    generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
        (fun g => LinearMap.trace K V (σ g))
        (fun _ _ hgh => character_eq_of_isConj σ hgh) j = 0 := by
  classical
  obtain ⟨fb, hfbi, hfbcc⟩ := exists_isIdempotentElem_blockCharacterPi_eq_single π hπ hlin hnilH
    (Quotient.mk (blockSetoid π hπ hlin) j)
  obtain ⟨fB, hfBi, hfBcc⟩ := exists_isIdempotentElem_blockCharacterPi_eq_single πG hπG hlinG
    hnilG (inducedBlockOfCentralizer x π hπ hlin πG hπG hlinG hnilG hp hx
      (Quotient.mk (blockSetoid π hπ hlin) j))
  exact generalizedDecompositionNumber_eq_zero_of_blockOfLattice hp hx e hπG hlinG hπ hlin hkerJ
    hnilH hnilG hω hω' hζ hζk hζK σ hLinv hEnd hfBi hfBcc hfbi hfbcc
    (blockCharacter_toLinearMap_inducedBlockOfCentralizer x π hπ hlin πG hπG hlinG hnilG hp hx _)
    hj.symm rfl

set_option maxHeartbeats 1000000 in
-- As above.
open scoped Classical in
/-- **Navarro (5.8), as the textbook states it.**  For `y ∈ C_G(x)` a `p'`-element,

`χ(xy) = ∑ d^x_{χμ} μ(y)`,  the sum over `μ ∈ IBr(b)` for the blocks `b` of `C_G(x)` inducing the
block of `χ`.

This is (5.1) — which expands `χ(xy)` over all of `IBr(C_G(x))` — with the terms outside those
blocks deleted by `generalizedDecompositionNumber_eq_zero_of_inducedBlockOfCentralizer_ne`. -/
theorem sum_generalizedDecompositionNumber_inducedBlockOfCentralizer (hp : p.Prime)
    {x : G} (hx : IsPElement p x) [Fintype ↥(centralizerOf x)]
    (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
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
    (σ : Representation K G V) {L : Submodule 𝒪 V} [L.IsLattice K] [Nontrivial ↥L]
    (hLinv : ∀ (g : G), ∀ v ∈ L, σ g v ∈ L)
    (hEnd : ∀ E : Module.End K (K ⊗[𝒪] ↥L),
      (∀ a : MonoidAlgebra 𝒪 G, E * LinearMap.baseChange K
          ((latticeRepresentation σ hLinv).asAlgebraHom a)
        = LinearMap.baseChange K ((latticeRepresentation σ hLinv).asAlgebraHom a) * E) →
      ∃ c : K, E = c • LinearMap.id)
    {y : ↥(centralizerOf x)} (hy : IsPRegular p y) :
    ∑ φ ∈ Finset.univ.filter (fun φ : ι =>
        inducedBlockOfCentralizer x π hπ hlin πG hπG hlinG hnilG hp hx
            (Quotient.mk (blockSetoid π hπ hlin) φ)
          = blockOfLattice K ((latticeRepresentation σ hLinv).asAlgebraHom) hEnd
              residue_surjective πG hπG hlinG hnilG),
      generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
          (fun g => LinearMap.trace K V (σ g))
          (fun _ _ hgh => character_eq_of_isConj σ hgh) φ
        * algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ y)
      = LinearMap.trace K V (σ (x * (y : G))) := by
  rw [Finset.sum_filter_of_ne fun φ _ hne => ?_]
  · exact sum_generalizedDecompositionNumber x hp hω' hπ hlin hkerJ _ _ hy
  · by_contra hcon
    exact hne (by
      rw [generalizedDecompositionNumber_eq_zero_of_inducedBlockOfCentralizer_ne hp hx e hπG hlinG
        hπ hlin hkerJ hnilH hnilG hω hω' hζ hζk hζK σ hLinv hEnd hcon, zero_mul])

end OddOrder.RepresentationTheory.Modular
