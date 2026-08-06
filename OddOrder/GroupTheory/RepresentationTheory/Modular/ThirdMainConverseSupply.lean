/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockPartVanishingSupply
import OddOrder.GroupTheory.RepresentationTheory.Modular.KulshammerThirdMain
import OddOrder.GroupTheory.RepresentationTheory.Modular.PRegularSumVanishing
import OddOrder.GroupTheory.RepresentationTheory.Modular.SecondMainPrincipalBlock

/-!
# The converse of the third main theorem, with all of Külshammer's side conditions discharged

`eq_principalBlock_of_inducedBlockOfCentralizer_eq` — a block `b` of `C_G(x)` with `b^G = B_0(G)`
is `b_0(C_G(x))` — carries three hypotheses about a *chosen* family of block idempotents on each
of the two groups, and Külshammer's formula behind it carries block orthogonality (`hweak`) and
the vanishing of the non-principal block characters on `Ĝ⁰` (`hvanish`).  This file discharges all
of them, leaving the statement that the involution chain actually consumes as its `hconv`.

Three groups take part, and each needs its own modular datum:

| group | role |
|---|---|
| `G` | the principal block `B_0(G)` |
| `H = C_G(x)` | the block `b` being identified |
| `C = C_G(⟨x⟩)` | the intermediate group both comparisons factor through |

`H` and `C` are equal as subgroups (`centralizer_zpowers_eq_centralizerOf`) but not as types, and
that equality is never used: `coeff_principalBlock_eq_of_mem_centralizer` compares `G` with `C`
and `H` with `C` and cancels the `C` side, so no datum has to be transported along it.

The `C`-side datum is free over a coefficient ring with algebraically closed residue field
(`GroupAlgebra.exists_modularDatum`), as are the Sylow subgroups, the ordinary splittings and the
block-idempotent families; `hroot`/`hroot'` supply the roots of unity, in the shape
`PadicComplexSystem` provides for `𝓞_ℂ_[p]`.

## Main results

* `OddOrder.RepresentationTheory.Modular.eq_principalBlock_of_inducedBlockOfCentralizer_eq_of_roots`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsIntegrallyClosed 𝒪]
  [IsAlgClosed (FractionRing 𝒪)] [IsAlgClosed (ResidueField 𝒪)]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K] [IsAlgClosed K] [CharZero K]
  [Fact p.Prime]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] [Invertible (Nat.card G : K)] {x : G}
  [Fintype ↥(centralizerOf x)] [DecidableEq (ConjClasses ↥(centralizerOf x))]
  [Fintype (ConjClasses ↥(centralizerOf x))] [Invertible (Nat.card ↥(centralizerOf x) : K)]
-- `Irr(G)` and `Bl(G)`
variable {ι'G : Type*} {mG : ι'G → Type*} [∀ i, Fintype (mG i)] [∀ i, DecidableEq (mG i)]
  [∀ i, Nonempty (mG i)] [Fintype ι'G]
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
-- `Irr(C_G(x))` and `Bl(C_G(x))`
variable {ι'H : Type*} {mH : ι'H → Type*} [∀ i, Fintype (mH i)] [∀ i, DecidableEq (mH i)]
  [∀ i, Nonempty (mH i)] [Fintype ι'H]
variable {ιH : Type*} [Finite ιH] {nnH : ιH → Type*} [∀ j, Fintype (nnH j)]
  [∀ j, DecidableEq (nnH j)] [∀ j, Nonempty (nnH j)]

set_option maxHeartbeats 1600000 in
-- Three modular data are assembled in one term, and Külshammer's formula on each pair of them is
-- elaborated against the full coefficient-ring chain.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open scoped Classical in
/-- **The converse of Brauer's third main theorem at a `p`-element, self-contained.**

A block `b` of `C_G(x)` with `b^G = B_0(G)` is the principal block of `C_G(x)`, with no hypothesis
left about block idempotents, Sylow subgroups, roots of unity or the datum of `C_G(⟨x⟩)`.

This is the `hconv` of `PrincipalBlockInvolution`. -/
theorem eq_principalBlock_of_inducedBlockOfCentralizer_eq_of_roots (hp : p.Prime)
    (hx : IsPElement p x)
    (hroot : ∀ n : ℕ, ¬ p ∣ n → n ≠ 0 → ∃ ζ : 𝒪, IsPrimitiveRoot ζ n)
    (hroot' : ∀ n : ℕ, ¬ p ∣ n → n ≠ 0 → ∃ ζ : ResidueField 𝒪, IsPrimitiveRoot ζ n)
    {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
    (eG : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (mG i) (mG i) K)
    (eH : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ i, Matrix (mH i) (mH i) K)
    {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
    (hπG : Function.Surjective πG)
    (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
    (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
      blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
    (hkerJG : RingHom.ker πG = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
    {πH : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
      ∀ j, Matrix (nnH j) (nnH j) (ResidueField 𝒪)}
    (hπH : Function.Surjective πH)
    (hlinH : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
      πH (c • a) = c • πH a)
    (hnilH : ∀ z : Subalgebra.center (ResidueField 𝒪)
        (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
      blockCharacterPi πH hπH hlinH z = 0 → IsNilpotent z)
    (hkerJH : RingHom.ker πH
      = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
    (b : Block πH hπH hlinH)
    (hind : inducedBlockOfCentralizer x πH hπH hlinH πG hπG hlinG hnilG hp hx b
      = principalBlock πG hπG hlinG hnilG) :
    b = principalBlock πH hπH hlinH hnilH := by
  classical
  haveI : Fintype ιG := Fintype.ofFinite _
  haveI : Fintype ιH := Fintype.ofFinite _
  haveI : Fintype (Block πG hπG hlinG) := Fintype.ofFinite _
  haveI : Fintype (Block πH hπH hlinH) := Fintype.ofFinite _
  have hQ : IsPGroup p ↥(Subgroup.zpowers x) := isPGroup_zpowers_of_isPElement hx
  have hQH : Subgroup.zpowers x ≤ centralizerOf x := zpowers_le_centralizerOf x
  have hCH : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ centralizerOf x :=
    centralizer_zpowers_le_centralizerOf x
  -- the intermediate group `C = C_G(⟨x⟩)` and its instances
  haveI : Fintype ↥(Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) :=
    Fintype.ofFinite _
  haveI : Invertible
      (Nat.card ↥(Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : NeZero
      (Nat.card ↥(Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) : K) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  -- the ordinary splitting of `K[C]`
  obtain ⟨nC, dC, hdC, ⟨eC⟩⟩ := exists_algEquiv_pi_matrix_monoidAlgebra K
    ↥(Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G))
  haveI : ∀ i, NeZero (dC i) := hdC
  haveI : ∀ i, Nonempty (Fin (dC i)) := fun i => ⟨0⟩
  -- the modular datum of `C`
  obtain ⟨ιC, hιC, nnC, hnnC, hdecC, hneC, πC, hπC, hlinC, hkerJC, hnilC⟩ :=
    GroupAlgebra.exists_modularDatum (ResidueField 𝒪)
      ↥(Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G))
  letI := hιC
  letI := hnnC
  letI := hdecC
  letI := hneC
  haveI : Fintype ιC := Fintype.ofFinite _
  haveI : Fintype (Block πC hπC hlinC) := Fintype.ofFinite _
  -- roots of unity for the three groups
  obtain ⟨ωG, hωG⟩ := hroot (pRegularExponent p G) (not_dvd_pRegularExponent hp)
    pRegularExponent_pos.ne'
  obtain ⟨ω'G, hω'G⟩ := hroot' (pRegularExponent p G) (not_dvd_pRegularExponent hp)
    pRegularExponent_pos.ne'
  obtain ⟨ωH, hωH⟩ := hroot (pRegularExponent p ↥(centralizerOf x)) (not_dvd_pRegularExponent hp)
    pRegularExponent_pos.ne'
  obtain ⟨ω'H, hω'H⟩ := hroot' (pRegularExponent p ↥(centralizerOf x))
    (not_dvd_pRegularExponent hp) pRegularExponent_pos.ne'
  obtain ⟨ωC, hωC⟩ := hroot
    (pRegularExponent p ↥(Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)))
    (not_dvd_pRegularExponent hp) pRegularExponent_pos.ne'
  obtain ⟨ω'C, hω'C⟩ := hroot'
    (pRegularExponent p ↥(Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)))
    (not_dvd_pRegularExponent hp) pRegularExponent_pos.ne'
  -- Sylow subgroups and block-idempotent families
  obtain ⟨SG⟩ : Nonempty (Sylow p G) := inferInstance
  obtain ⟨SH⟩ : Nonempty (Sylow p ↥(centralizerOf x)) := inferInstance
  obtain ⟨SC⟩ : Nonempty
      (Sylow p ↥(Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G))) :=
    inferInstance
  obtain ⟨F, F', hidem, hf, hB⟩ := exists_blockIdempotentFamily πG hπG hlinG hnilG
  obtain ⟨FH, F'H, hidemH, hfH, hBH⟩ := exists_blockIdempotentFamily πH hπH hlinH hnilH
  obtain ⟨FC, FC', hidemC, hfC, hBC⟩ := exists_blockIdempotentFamily πC hπC hlinC hnilC
  -- block orthogonality against a nontrivial element of a Sylow `p`-subgroup
  have hweak : ∀ g : ↥(Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)),
      IsPRegular p (g : G) → ∀ B : Block πG hπG hlinG, ∀ y : ↥(SG : Subgroup G), (y : G) ≠ 1 →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr eG hπG hlinG hnilG i = B),
        (wedderburnRepresentation eG i).character (g : G)⁻¹
          * (wedderburnRepresentation eG i).character (y : G) = 0 := by
    intro g hg B y hy1
    exact sum_character_blockOfIrr_eq_zero_of_isPRegular_of_roots hp hg
      (isPElement_of_mem_of_isPGroup SG.isPGroup' y.2) hy1 hroot hroot' eG hπG hlinG hnilG
      hζ hζk hζK B
  have hweakH : ∀ g : ↥(Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)),
      IsPRegular p (g : G) → ∀ B : Block πH hπH hlinH,
      ∀ y : ↥(SH : Subgroup ↥(centralizerOf x)), (y : ↥(centralizerOf x)) ≠ 1 →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr eH hπH hlinH hnilH i = B),
        (wedderburnRepresentation eH i).character (⟨(g : G), hCH g.2⟩ : ↥(centralizerOf x))⁻¹
          * (wedderburnRepresentation eH i).character (y : ↥(centralizerOf x)) = 0 := by
    intro g hg B y hy1
    exact sum_character_blockOfIrr_eq_zero_of_isPRegular_of_roots hp
      ((isPRegular_coe_iff (H := centralizerOf x)
        (y := (⟨(g : G), hCH g.2⟩ : ↥(centralizerOf x)))).mp hg)
      (isPElement_of_mem_of_isPGroup SH.isPGroup' y.2) hy1 hroot hroot' eH hπH hlinH hnilH
      hζ hζk hζK B
  have hweakC : ∀ g : ↥(Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)),
      IsPRegular p (g : G) → ∀ B : Block πC hπC hlinC,
      ∀ y : ↥(SC : Subgroup ↥(Subgroup.centralizer
          ((Subgroup.zpowers x : Subgroup G) : Set G))),
        (y : ↥(Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G))) ≠ 1 →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr eC hπC hlinC hnilC i = B),
        (wedderburnRepresentation eC i).character g⁻¹
          * (wedderburnRepresentation eC i).character
              (y : ↥(Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G))) = 0 := by
    intro g hg B y hy1
    exact sum_character_blockOfIrr_eq_zero_of_isPRegular_of_roots hp
      ((isPRegular_coe_iff (H := Subgroup.centralizer
        ((Subgroup.zpowers x : Subgroup G) : Set G)) (y := g)).mp hg)
      (isPElement_of_mem_of_isPGroup SC.isPGroup' y.2) hy1
      hroot hroot' eC hπC hlinC hnilC hζ hζk hζK B
  -- the non-principal block characters vanish on `Ĝ⁰`
  have hvanish := blockCharacter_pRegularSum_eq_zero_of_ne_principalBlock hp hωG hω'G hπG hlinG
    hkerJG hnilG eG
  have hvanishH := blockCharacter_pRegularSum_eq_zero_of_ne_principalBlock hp hωH hω'H hπH hlinH
    hkerJH hnilH eH
  have hvanishC := blockCharacter_pRegularSum_eq_zero_of_ne_principalBlock hp hωC hω'C hπC hlinC
    hkerJC hnilC eC
  -- the two comparisons through `C`, and their composite
  have hGC := coeff_principalBlock_eq_centralizer_forall eG hπG hlinG hnilG eC hπC hlinC hnilC
    hp hQ SG SC hωG hω'G hkerJG hωC hω'C hkerJC hidem hf hB hweak hvanish hidemC hfC hBC
    hweakC hvanishC
  have hHC := coeff_principalBlock_eq_centralizer_intermediate_forall eH hπH hlinH hnilH eC hπC
    hlinC hnilC hp hQ hQH hCH SH SC hωH hω'H hkerJH hωC hω'C hkerJC hidemH hfH hBH hweakH
    hvanishH hidemC hfC hBC hweakC hvanishC
  have hcoeff := coeff_principalBlock_eq_of_mem_centralizer hπG hlinG hnilG hπH hlinH hnilH
    hπC hlinC hnilC hCH hGC hHC
  exact eq_principalBlock_of_inducedBlockOfCentralizer_eq πH hπH hlinH hnilH πG hπG hlinG hnilG
    hp hx hB hBH hcoeff b hind

end OddOrder.RepresentationTheory.Modular
