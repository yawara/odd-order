/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.GroupAlgebraBlocks
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockPartVanishing
import OddOrder.GroupTheory.RepresentationTheory.Modular.PPrimeSubgroupRestriction

/-!
# Discharging the `hweak` hypothesis of Külshammer's formula

Külshammer's route to the converse of the third main theorem carries block orthogonality
(Navarro (5.11)) as a hypothesis, in the shape

`∀ B, ∀ x ∈ S, x ≠ 1, ∑_{χ ∈ Irr(B)} χ(g⁻¹) χ(x) = 0`  (`g` `p`-regular, `S` a Sylow `p`-subgroup).

`sum_character_blockOfIrr_eq_zero_of_isPRegular` proves exactly that, but it asks for a full
modular datum on `C_G(x_p)` — a splitting `π` of `k[C_G(x_p)]` with `ker π = J`, its nilpotence
witness, the ordinary Wedderburn splitting of `K[C_G(x_p)]`, and primitive roots of unity of order
`exp_{p'}(C_G(x_p))` upstairs and downstairs.  Since `x` ranges over a Sylow subgroup, that is a
different centraliser for every `x`, so the hypothesis cannot be discharged one group at a time.

Over a coefficient ring whose residue field is algebraically closed all of it is free:
`GroupAlgebra.exists_modularDatum` produces the modular splitting for *any* finite group, the
ordinary splitting comes from `IsAlgClosed K` by Maschke, and the two roots of unity are supplied
by the two hypotheses `hroot`/`hroot'` — the shape `PadicComplexSystem` provides for `𝓞_ℂ_[p]`.

## Main results

* `OddOrder.RepresentationTheory.Modular.sum_character_blockOfIrr_eq_zero_of_isPRegular_of_roots`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsIntegrallyClosed 𝒪]
  [IsAlgClosed (FractionRing 𝒪)] [IsAlgClosed (ResidueField 𝒪)]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K] [IsAlgClosed K] [CharZero K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] [Invertible (Nat.card G : K)]
-- `Irr(G)`, through the Wedderburn splitting of `KG`
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι']
-- `Bl(G)`
variable {ιG : Type*} {nnG : ιG → Type*} [∀ i, Fintype (nnG i)] [∀ i, DecidableEq (nnG i)]
  [Finite ιG] [∀ i, Nonempty (nnG i)]

open scoped Classical in
/-- **Navarro (5.11) against a nontrivial `p`-element, with the centraliser datum supplied.**

This is `sum_character_blockOfIrr_eq_zero_of_isPRegular` with its six `C_G(x_p)`-hypotheses
discharged: the modular splitting from `GroupAlgebra.exists_modularDatum` (the residue field is
algebraically closed), the ordinary splitting from Maschke over the algebraically closed `K`, and
the two roots of unity from `hroot`/`hroot'` at `n = exp_{p'}(C_G(x_p))`, which is prime to `p`
(`not_dvd_pRegularExponent`).

It is the form Külshammer's `hweak` consumes, where `x` runs over a Sylow `p`-subgroup and so no
single centraliser datum could be fixed in advance. -/
theorem sum_character_blockOfIrr_eq_zero_of_isPRegular_of_roots (hp : p.Prime) {g x : G}
    (hg : IsPRegular p g) (hx : IsPElement p x) (hx1 : x ≠ 1)
    (hroot : ∀ n : ℕ, ¬ p ∣ n → n ≠ 0 → ∃ ζ : 𝒪, IsPrimitiveRoot ζ n)
    (hroot' : ∀ n : ℕ, ¬ p ∣ n → n ≠ 0 → ∃ ζ : ResidueField 𝒪, IsPrimitiveRoot ζ n)
    (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
    {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
    (hπG : Function.Surjective πG)
    (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
    (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
      blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
    {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
    (B : Block πG hπG hlinG) :
    ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character g⁻¹
          * (wedderburnRepresentation e i).character x = 0 := by
  classical
  have : Fintype ↥(centralizerOf (pPart p x)) := Fintype.ofFinite _
  have : NeZero (Nat.card ↥(centralizerOf (pPart p x)) : K) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨nH, dH, hdH, ⟨eH⟩⟩ :=
    exists_algEquiv_pi_matrix_monoidAlgebra K ↥(centralizerOf (pPart p x))
  have : ∀ i, NeZero (dH i) := hdH
  have : ∀ i, Nonempty (Fin (dH i)) := fun i => ⟨0⟩
  obtain ⟨ιH, hιH, nnH, hnnH, hdecH, hneH, π, hπ, hlin, hkerJ, hnilH⟩ :=
    GroupAlgebra.exists_modularDatum (ResidueField 𝒪) ↥(centralizerOf (pPart p x))
  -- `letI`, not `haveI`: `Fintype`/`DecidableEq` are data, and the target lemma's instance
  -- arguments have to stay definitionally the ones `exists_modularDatum` returned.
  let := hιH
  let := hnnH
  let := hdecH
  let := hneH
  obtain ⟨ω, hω⟩ := hroot (pRegularExponent p ↥(centralizerOf (pPart p x)))
    (not_dvd_pRegularExponent hp) pRegularExponent_pos.ne'
  obtain ⟨ω', hω'⟩ := hroot' (pRegularExponent p ↥(centralizerOf (pPart p x)))
    (not_dvd_pRegularExponent hp) pRegularExponent_pos.ne'
  exact sum_character_blockOfIrr_eq_zero_of_isPRegular hp hg hx hx1 e eH hπG hlinG hnilG
    hπ hlin hkerJ hnilH hω hω' hζ hζk hζK B

end OddOrder.RepresentationTheory.Modular
