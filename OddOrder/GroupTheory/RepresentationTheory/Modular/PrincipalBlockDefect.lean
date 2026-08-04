/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.GroupAlgebraDefectGroup
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockHeight
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockIdempotentLift
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlock

/-!
# The principal block has full defect

`d(B_0) = ν(|G|)`: a defect group of the principal block is a Sylow `p`-subgroup.

`BlockHeight` proves this for any `G`-fixed idempotent of `𝒪[G]` whose augmentation survives
reduction to the residue field.  The principal block idempotent is such an element: it is central
(so `G`-fixed), idempotent, and its reduction `e_{B_0}` satisfies
`ε(e_{B_0}) = λ_{B_0}(e_{B_0}) = 1` because the central character of `B_0` *is* the augmentation
(`blockCharacter_principalBlock`).  Since the augmentation commutes with the reduction of
coefficients (`augmentation_mapRingHom`), the residue of `ε_𝒪(f_{B_0})` is `1 ≠ 0`.

Consequently `1_G`, of degree `1`, has height zero in `B_0`: the height inequality
`p^{ν(|G|) - d(B_0)} ∣ χ(1)` of `BlockHeight` is an equality for it.

## Main results

* `OddOrder.RepresentationTheory.Modular.defect_eq_factorization_of_blockCharacterPi_principal` —
  full defect, for any lift of the principal block idempotent
* `OddOrder.RepresentationTheory.Modular.exists_isIdempotentElem_defect_principalBlock` — such a
  lift exists, so the hypothesis is not vacuous
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.MatrixModule
open OddOrder.GroupTheory.CenterSimplesOrbit (aug aug_apply)

open scoped OddOrder.Conjugation

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
variable {G : Type*} [Group G] [Finite G]
variable {ι : Type*} [Finite ι] {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [∀ i, Nonempty (nn i)]
variable (π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪))
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
/-- **`d(B_0) = ν(|G|)`.**  A lift `f` of the principal block idempotent has full defect: its
augmentation reduces to `λ_{B_0}(e_{B_0}) = 1`, so `BlockHeight`'s criterion applies. -/
theorem defect_eq_factorization_of_blockCharacterPi_principal
    [DecidableEq (Block π hπ hlin)]
    {f : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))} (hf : IsIdempotentElem f)
    (hval : blockCharacterPi π hπ hlin (OddOrder.centerReduce (residue 𝒪) f)
      = Pi.single (principalBlock π hπ hlin hnil) 1)
    (hfix : ∀ g : G, g • (f : MonoidAlgebra 𝒪 G) = (f : MonoidAlgebra 𝒪 G)) :
    GAlgebra.defect p hfix = (Nat.card G).factorization p := by
  have hfc : IsIdempotentElem (f : MonoidAlgebra 𝒪 G) := by
    have h := congrArg Subtype.val hf
    simpa [IsIdempotentElem] using h
  refine defect_eq_factorization_of_residue_augmentation_ne_zero hfix hfc ?_
  have hres : residue 𝒪 (OddOrder.Algebra.augmentation 𝒪 G (f : MonoidAlgebra 𝒪 G))
      = aug (OddOrder.centerReduce (residue 𝒪) f) := by
    rw [aug_apply, OddOrder.coe_centerReduce, OddOrder.centerReduceHom_apply,
      OddOrder.Algebra.augmentation_mapRingHom]
  rw [hres, ← blockCharacter_principalBlock π hπ hlin hnil, ← blockCharacterPi_apply, hval,
    Pi.single_eq_same]
  exact one_ne_zero

/-- **A lift of the principal block idempotent exists**, so the hypothesis of
`defect_eq_factorization_of_blockCharacterPi_principal` is satisfiable: the principal block really
does have full defect. -/
theorem exists_isIdempotentElem_defect_principalBlock [DecidableEq (Block π hπ hlin)] :
    ∃ (f : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)))
      (hfix : ∀ g : G, g • (f : MonoidAlgebra 𝒪 G) = (f : MonoidAlgebra 𝒪 G)),
      IsIdempotentElem f ∧
        blockCharacterPi π hπ hlin (OddOrder.centerReduce (residue 𝒪) f)
          = Pi.single (principalBlock π hπ hlin hnil) 1 ∧
        GAlgebra.defect p hfix = (Nat.card G).factorization p := by
  obtain ⟨f, hf, hval⟩ :=
    exists_isIdempotentElem_blockCharacterPi_eq_single π hπ hlin hnil
      (principalBlock π hπ hlin hnil)
  refine ⟨f, OddOrder.GroupAlgebra.mem_center_iff_forall_smul_eq.mp f.2, hf, hval, ?_⟩
  exact defect_eq_factorization_of_blockCharacterPi_principal π hπ hlin hnil hf hval _

end OddOrder.RepresentationTheory.Modular
