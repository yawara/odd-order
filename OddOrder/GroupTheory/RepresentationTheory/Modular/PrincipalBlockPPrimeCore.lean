/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.SecondMainPrincipalBlock

/-!
# Navarro (7.7): `χ(u v) = χ(u)` for `v` in the `p'`-core of `C_G(u)`

**Navarro, *Characters and Blocks of Finite Groups*, Theorem (7.7)** (p. 145): let `u ∈ G` be a
`p`-element, `v ∈ O_{p'}(C_G(u))`, and `B_0` the principal block of `G`.  Then

`χ(u v) = χ(u)` for every `χ ∈ Irr(B_0)`.

This is the last piece of modular representation theory that Glauberman's `Z*`-theorem needs
(issue 0186); it is the only result of Chapter 7 that Brauer–Suzuki (issues 0147 / 9506) did not
already require.

The argument is Navarro's.  Writing the defining expansion of the generalized decomposition
numbers at the `p`-element `u`,

`χ(u w) = ∑_{μ ∈ IBr(C_G(u))} d^u_{χ μ} μ(w)`   for `p`-regular `w ∈ C_G(u)`,

two facts collapse it.  The **second main theorem** together with the **converse of the third
main theorem** kills every `μ` outside the principal block `b_0` of `C_G(u)`
(`generalizedDecompositionNumber_eq_zero_of_ne_principalBlock`, the `hconv` hypothesis of the
ambient section).  And on the surviving `μ ∈ IBr(b_0)`, Navarro (6.10) identifies
`O_{p'}(C_G(u)) = ker(b_0)`, so (6.11)/(6.12) give `μ(v) = μ(1)`.  Evaluating the expansion at
`w = v` and at `w = 1` therefore gives the same number.

Note what is *not* assumed: the specialisation
`SecondMainPrincipalBlock.character_mul_eq_generalizedDecompositionNumber` needs `C_G(u)` to have
a normal `p`-complement, which collapses the sum to its single term `φ_0`; Brauer–Suzuki only
ever used it in that form.  Here the sum stays a sum.

## Main results

* `OddOrder.RepresentationTheory.Modular`
  `.generalizedDecompositionNumber_eq_zero_of_ne_principalBlock` — the second main theorem in the
  form `d^u_{χ μ} = 0` for `μ` outside `b_0(C_G(u))`
* `OddOrder.RepresentationTheory.Modular.character_mul_eq_character_of_brauerCharacter_eq` —
  Navarro (7.7), with the hypothesis `v ∈ O_{p'}(C_G(u))` presented as
  "every Brauer character of `b_0` takes the same value at `v` as at `1`"
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule
open OddOrder.RepresentationTheory

section SeventySeven

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsIntegrallyClosed 𝒪]
  [IsAlgClosed (FractionRing 𝒪)]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
  [Fact p.Prime] [CharP (ResidueField 𝒪) p]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] {x : G} [Fintype ↥(centralizerOf x)]
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable {m : ι → Type*}
variable {ι' : Type*} {m' : ι' → Type*} [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)]
  [Finite ι'] [∀ i, Nonempty (m' i)]
variable {κ : Type*} {mG : κ → Type*} [∀ i, Fintype (mG i)] [∀ i, DecidableEq (mG i)]
  [Finite κ] [∀ i, Nonempty (mG i)]
variable {ιG : Type*} {nnG : ιG → Type*} [∀ i, Fintype (nnG i)] [∀ i, DecidableEq (nnG i)]
  [Finite ιG] [∀ i, Nonempty (nnG i)]
variable (hp : p.Prime) (hx : IsPElement p x)
  {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
  (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ i, Matrix (m' i) (m' i) K)
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
  (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
  {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
  (hconv : ∀ b : Block π hπ hlin,
    inducedBlockOfCentralizer x π hπ hlin πG hπG hlinG hnilG hp hx b
      = principalBlock πG hπG hlinG hnilG → b = principalBlock π hπ hlin hnil)

omit [Finite κ] [Fact p.Prime] in
include hp hx hω e hπG hlinG hkerJ hnil hζ hζk hζK hconv in
/-- **The `p`-section of `x` only sees the principal block of `C_G(x)`.**  If
`χ_i ∈ Irr(B_0(G))` and the block of `μ` is not `b_0(C_G(x))`, then `d^x_{χ_i μ} = 0`.

Second main theorem: a nonzero `d^x_{χ_i μ}` forces the block of `μ` to induce `B_0(G)`; the
converse third main theorem (`hconv`) then makes that block `b_0(C_G(x))`.

This is `SecondMainPrincipalBlock.generalizedDecompositionNumber_eq_zero_of_ne_principal`
without the normal-`p`-complement hypothesis, which that statement only needs in order to name
the surviving column `φ_0`. -/
theorem generalizedDecompositionNumber_eq_zero_of_ne_principalBlock {i : κ}
    (hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG)
    {μ : ι} (hμ : Quotient.mk (blockSetoid π hπ hlin) μ ≠ principalBlock π hπ hlin hnil) :
    generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
        ((wedderburnRepresentation eG i).character)
        (fun _ _ hgh => character_eq_of_isConj _ hgh) μ = 0 := by
  refine generalizedDecompositionNumber_eq_zero_of_blockOfIrr_ne hp hx e eG hπG hlinG hπ hlin
    hkerJ hnil hnilG hω hω' hζ hζk hζK ?_
  rw [hi]
  exact fun hc => hμ (hconv _ hc)

-- `Fintype ι` indexes the sum that the proof runs over; the statement only mentions it through
-- the expansion, so the linter sees it as proof-only.
set_option linter.unusedFintypeInType false in
omit [Finite κ] [Fact p.Prime] in
include hp hx hω e hπG hlinG hkerJ hnil hζ hζk hζK hω' hconv in
/-- **Navarro (7.7)**: `χ(x v) = χ(x)` for `χ ∈ Irr(B_0(G))`, once every irreducible Brauer
character of the principal block of `C_G(x)` takes the same value at `v` as at `1`.

Evaluate the defining expansion `χ(x w) = ∑_μ d^x_{χ μ} μ(w)` at `w = v` and at `w = 1`: term by
term the two agree, because outside the principal block of `C_G(x)` the coefficient `d^x_{χ μ}`
vanishes, and inside it the Brauer character values agree by hypothesis.

The hypothesis is what `v ∈ O_{p'}(C_G(x))` gives, through Navarro (6.10)
(`O_{p'}(C) = ker(b_0)`) and (6.11)/(6.12) (`ker(b_0)` acts trivially in every
`μ ∈ IBr(b_0)`). -/
theorem character_mul_eq_character_of_brauerCharacter_eq {i : κ}
    (hi : blockOfIrr eG hπG hlinG hnilG i = principalBlock πG hπG hlinG hnilG)
    {v : ↥(centralizerOf x)} (hv : IsPRegular p v)
    (hval : ∀ μ : ι, Quotient.mk (blockSetoid π hπ hlin) μ = principalBlock π hπ hlin hnil →
      irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ v
        = irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ 1) :
    (wedderburnRepresentation eG i).character (x * (v : G))
      = (wedderburnRepresentation eG i).character x := by
  classical
  -- the defining expansion of the generalized decomposition numbers, at any `p`-regular `y`
  have hsum : ∀ {y : ↥(centralizerOf x)}, IsPRegular p y →
      ∑ μ, generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
            ((wedderburnRepresentation eG i).character)
            (fun _ _ hgh => character_eq_of_isConj _ hgh) μ *
          algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ y)
        = (wedderburnRepresentation eG i).character (x * (y : G)) :=
    fun hy => sum_generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
      ((wedderburnRepresentation eG i).character)
      (fun _ _ hgh => character_eq_of_isConj _ hgh) hy
  -- rewrite the right-hand side as the same expansion at `y = 1` (`x` itself is never rewritten:
  -- it occurs in `centralizerOf x`, so `rw` on it would not be type correct)
  have hone : (wedderburnRepresentation eG i).character x
      = (wedderburnRepresentation eG i).character (x * ((1 : ↥(centralizerOf x)) : G)) := by
    rw [OneMemClass.coe_one, mul_one]
  rw [hone, ← hsum hv, ← hsum (isPRegular_one hp)]
  refine Finset.sum_congr rfl fun μ _ => ?_
  by_cases hμ : Quotient.mk (blockSetoid π hπ hlin) μ = principalBlock π hπ hlin hnil
  · rw [hval μ hμ]
  · rw [generalizedDecompositionNumber_eq_zero_of_ne_principalBlock hp hx hω e eG hπG hlinG hπ
      hlin hkerJ hnil hnilG hω' hζ hζk hζK hconv hi hμ, zero_mul, zero_mul]

end SeventySeven

end OddOrder.RepresentationTheory.Modular
