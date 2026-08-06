/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.BrauerSuzukiQ8.Reduction
import OddOrder.GroupTheory.CentralInvolutionNormalComplement
import OddOrder.GroupTheory.RepresentationTheory.Modular.AnalysisAtInvolution
import OddOrder.GroupTheory.RepresentationTheory.Modular.InvolutionColumnExpansion
import OddOrder.GroupTheory.RepresentationTheory.Modular.PadicComplexDatum

/-!
# Brauer–Suzuki, the `Q₈` case: the character-theoretic core (Navarro pp. 139–146)

`q8_exists_proper_normal` is the whole content of the `Q₈` branch: the involution of a proper
quaternion Sylow `2`-subgroup lies in a proper normal subgroup.  Navarro obtains it as the kernel
of a nontrivial character of the principal block, through the "analysis at `y`" and the "analysis
at `t`" of pp. 140–145.

The character-theoretic engine is `exists_proper_normal_of_columns`; every one of its hypotheses
has a supplier in `GroupTheory/RepresentationTheory/Modular/`, and this file is where they are
instantiated for the `Q₈` configuration (issue 9506).

## Main results

* `OddOrder.GroupTheory.q8_exists_proper_normal`
-/

open OddOrder.Isaacs.Ch03

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- **Navarro pp. 139–146, the character-theoretic core** (issue 9506, `sorry`): when the
quaternion Sylow `2`-subgroup is proper, its involution lies in a proper normal subgroup.

This is Navarro's "our objective is to find a nontrivial character in the principal block of `G`
which contains `t` in its kernel" — the kernel of such a character is the proper normal subgroup.
The proof occupies the eight pages pp. 139–146: a unique `G`-class of elements of order `4`
(fusion control plus `Aut(Q₈) = Sym(4)`), then the "analysis at `y`" and "analysis at `t`" with
the principal-block basic set of Navarro (7.3)/(7.4), for which the integral change-of-basis
matrix `intBasicSetMatrix` (issue 9508, closed) is the prerequisite. -/
theorem q8_exists_proper_normal (hO : oPiCore {p | p ≠ 2} G = ⊥) (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) (hTG : (T : Subgroup G) ≠ ⊤)
    {z : G} (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ z ∈ N := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype G := Fintype.ofFinite G
  -- the datum of `G` over `𝓞_ℂ_[2]`
  obtain ⟨ι'G, _, mG, _, _, _, eG, ιG, _, nnG, _, _, _, πG, hπG, hlinG, ωG, ω'G,
    hkerJG, hnilG, hωG, hω'G⟩ :=
    OddOrder.RepresentationTheory.Modular.exists_datum_padicComplex 2 G
  -- the centraliser of the involution, and its datum
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  haveI : Finite ↥C := Subtype.finite
  obtain ⟨ι'C, _, mC, _, _, _, eC, ιC, _, nnC, _, _, _, πC, hπC, hlinC, ωC, ω'C,
    hkerJC, hnilC, hωC, hω'C⟩ :=
    OddOrder.RepresentationTheory.Modular.exists_datum_padicComplex 2 ↥C
  -- the central subgroup `⟨z⟩ ⊴ C_G(z)` and the quotient `Q = C_G(z)/⟨z⟩`
  have hzC : z ∈ C := Subgroup.mem_centralizer_iff.mpr fun w hw => by
    rw [Set.mem_singleton_iff] at hw; subst hw; rfl
  set Nz : Subgroup ↥C := Subgroup.zpowers (⟨z, hzC⟩ : ↥C) with hNz
  haveI : Nz.Normal := zpowers_self_normal_centralizer z hzC
  have hNzcard : Nat.card ↥Nz = 2 := by
    rw [hNz, Nat.card_zpowers,
      ← orderOf_injective C.subtype (Subgroup.subtype_injective _) (⟨z, hzC⟩ : ↥C)]
    exact hz
  have hNzP : IsPGroup 2 ↥Nz := IsPGroup.of_card (n := 1) (by rw [hNzcard, pow_one])
  haveI : Finite (↥C ⧸ Nz) := Quotient.finite _
  -- the ordinary splitting of `Q`; its *modular* splitting must be `quotientPi` of that of `C`,
  -- so that `IBr(Q)` and `IBr(C)` share their index type (Navarro (7.6))
  obtain ⟨ι'Q, _, mQ, _, _, _, eQ, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    OddOrder.RepresentationTheory.Modular.exists_datum_padicComplex 2 (↥C ⧸ Nz)
  obtain ⟨ϖ, hϖ⟩ :=
    OddOrder.RepresentationTheory.Modular.exists_isPrimitiveRoot_pRegularExponent 2 (↥C ⧸ Nz)
  obtain ⟨ϖ', hϖ'⟩ :=
    OddOrder.RepresentationTheory.Modular.exists_isPrimitiveRoot_residueField_pRegularExponent 2
      (↥C ⧸ Nz)
  have hkerJQ := OddOrder.RepresentationTheory.Modular.ker_quotientPi πC hπC hlinC hNzP hkerJC
  have hnilQ := fun w hw =>
    OddOrder.GroupAlgebra.isNilpotent_of_blockCharacterPi_eq_zero
      (OddOrder.RepresentationTheory.Modular.quotientPi πC hπC hlinC hNzP).toRingHom
      (OddOrder.RepresentationTheory.Modular.quotientPi_surjective πC hπC hlinC hNzP)
      (OddOrder.RepresentationTheory.Modular.quotientPi_smul πC hπC hlinC hNzP) hkerJQ w hw
  sorry

end OddOrder.GroupTheory
