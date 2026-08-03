/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockRepresentation
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerCharacter

/-!
# The irreducible Brauer characters `IBr(G)`

A splitting datum `π : kG ↠ ∏_{j ∈ ι} M_{n_j}(k)` with `k = ResidueField 𝒪` presents the simple
`kG`-modules as the blocks (`Algebra/PiMatrixSimpleModules`), each carrying a representation
(`Modular/BlockRepresentation`).  Their Brauer characters, taken at the exponent
`|G|_{p'} = pRegularExponent p G`, are the **irreducible Brauer characters** of `G`.

For an algebraically closed `k` such a datum exists with `#ι = #{p`-regular classes of `G}`
(`Modular/BrauerCount`), which is Brauer's theorem `|IBr(G)| = #{p`-regular classes`}`.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.irreducibleBrauerCharacter`

## Main results

* `irreducibleBrauerCharacter_conj` — they are class functions
* `irreducibleBrauerCharacter_one` — the value at `1` is the size of the block
* `residue_irreducibleBrauerCharacter` — reduction is the modular trace of the block
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
variable (π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪))

/-- **The irreducible Brauer characters of `G`** attached to a splitting datum: the Brauer
character of the `i`-th block, at the exponent `|G|_{p'}`. -/
noncomputable def irreducibleBrauerCharacter (i : ι) (g : G) : 𝒪 :=
  brauerCharacter (𝒪 := 𝒪) (pRegularExponent p G) (blockRepresentation π i) g

omit [IsPModularSystem p 𝒪] [Finite G] in
/-- **Irreducible Brauer characters are class functions.** -/
theorem irreducibleBrauerCharacter_conj (i : ι) (g h : G) :
    irreducibleBrauerCharacter (p := p) π i (h * g * h⁻¹)
      = irreducibleBrauerCharacter (p := p) π i g :=
  brauerCharacter_conj _ g h

/-- **The degree of an irreducible Brauer character** is the size of its block. -/
theorem irreducibleBrauerCharacter_one (hp : p.Prime) (i : ι) :
    irreducibleBrauerCharacter (p := p) π i 1 = (Fintype.card (nn i) : 𝒪) := by
  rw [irreducibleBrauerCharacter,
    brauerCharacter_pRegularExponent_one (ρ := blockRepresentation π i) hp,
    Module.finrank_fintype_fun_eq_card]

/-- **Reduction of an irreducible Brauer character at a `p`-regular element is the trace of the
block.**  This is the sense in which `IBr(G)` records the modular representation theory. -/
theorem residue_irreducibleBrauerCharacter (hp : p.Prime)
    {ω : ResidueField 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G)) (i : ι)
    {g : G} (hg : IsPRegular p g) :
    residue 𝒪 (irreducibleBrauerCharacter (p := p) π i g)
      = Matrix.trace (π (single g 1) i) := by
  rw [irreducibleBrauerCharacter,
    residue_brauerCharacter_of_isPRegular (ρ := blockRepresentation π i) hp hω hg]
  simp only [blockRepresentation, LinearMap.trace_eq_matrix_trace (ResidueField 𝒪)
    (Pi.basisFun (ResidueField 𝒪) (nn i))]
  congr 1
  exact LinearMap.toMatrix'_toLin' _

end OddOrder.RepresentationTheory.Modular
