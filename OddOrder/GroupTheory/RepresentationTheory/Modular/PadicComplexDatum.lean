/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.GroupAlgebraBlocks
import OddOrder.GroupTheory.RepresentationTheory.Modular.PadicComplexSystem

/-!
# The complete datum of a finite group over `𝓞_ℂ_[p]`

The block machinery asks each group for four independent pieces of data:

* the **ordinary splitting** `e : ℂ_[p][H] ≃ₐ ∏ M_{m_i}(ℂ_[p])`, which indexes `Irr(H)`;
* the **modular splitting** `π : k[H] ↠ ∏ M_{n_j}(k)` with `ker π = J(k[H])` and the nilpotence
  condition, which indexes `IBr(H)` and defines the blocks;
* a primitive `|H|_{p'}`-th root of unity `ω` in `𝓞_ℂ_[p]`, and
* its companion `ω'` in the residue field.

Over `𝓞_ℂ_[p]` all four are **free for every finite group**, with no hypothesis to discharge:
`ℂ_[p]` is algebraically closed of characteristic `0` (Maschke plus Wedderburn–Artin), the residue
field `𝔽̄_p` is algebraically closed (`exists_modularDatum`), and `p` does not divide `|H|_{p'}`.

That is exactly what the Brauer–Suzuki chain needs, where the datum is required for four different
groups at once — `G`, `C_G(t)`, `C_G(y)` and `C_G(t)/⟨t⟩` — and no single one of them can be fixed
in advance.  It is also the `CLAUDE.md` doneness criterion for the carrier: the datum is
*constructed*, not posited.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_datum_padicComplex`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Every finite group has a complete datum over `𝓞_ℂ_[p]`.**

The ordinary splitting comes from `exists_algEquiv_pi_matrix_padicComplex`, the modular one from
`GroupAlgebra.exists_modularDatum` (the residue field is algebraically closed), and the two roots
of unity from `exists_isPrimitiveRoot_pRegularExponent` and its residue companion. -/
theorem exists_datum_padicComplex (H : Type*) [Group H] [Finite H] :
    ∃ (ι' : Type) (_ : Fintype ι') (m : ι' → Type) (_ : ∀ i, Fintype (m i))
      (_ : ∀ i, DecidableEq (m i)) (_ : ∀ i, Nonempty (m i))
      (_e : MonoidAlgebra ℂ_[p] H ≃ₐ[ℂ_[p]] ∀ i, Matrix (m i) (m i) ℂ_[p])
      (ι : Type) (_ : Fintype ι) (nn : ι → Type) (_ : ∀ j, Fintype (nn j))
      (_ : ∀ j, DecidableEq (nn j)) (_ : ∀ j, Nonempty (nn j))
      (π : MonoidAlgebra (ResidueField 𝓞_ℂ_[p]) H →+*
        ∀ j, Matrix (nn j) (nn j) (ResidueField 𝓞_ℂ_[p]))
      (hπ : Function.Surjective π)
      (hlin : ∀ (c : ResidueField 𝓞_ℂ_[p]) (a : MonoidAlgebra (ResidueField 𝓞_ℂ_[p]) H),
        π (c • a) = c • π a)
      (_ω : 𝓞_ℂ_[p]) (_ω' : ResidueField 𝓞_ℂ_[p]),
      RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝓞_ℂ_[p]) H) ∧
      (∀ z : Subalgebra.center (ResidueField 𝓞_ℂ_[p]) (MonoidAlgebra (ResidueField 𝓞_ℂ_[p]) H),
        OddOrder.MatrixModule.blockCharacterPi π hπ hlin z = 0 → IsNilpotent z) ∧
      IsPrimitiveRoot _ω (pRegularExponent p H) ∧
      IsPrimitiveRoot _ω' (pRegularExponent p H) := by
  classical
  obtain ⟨n, d, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_padicComplex p H
  have : ∀ i, NeZero (d i) := hd
  have : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨0⟩
  obtain ⟨ι, hιfin, nn, hnnfin, hnndec, hnnne, π, hπ, hlin, hkerJ, hnil⟩ :=
    OddOrder.GroupAlgebra.exists_modularDatum (ResidueField 𝓞_ℂ_[p]) H
  obtain ⟨ω, hω⟩ := exists_isPrimitiveRoot_pRegularExponent p H
  obtain ⟨ω', hω'⟩ := exists_isPrimitiveRoot_residueField_pRegularExponent p H
  exact ⟨Fin n, inferInstance, fun i => Fin (d i), inferInstance, inferInstance, inferInstance,
    e, ι, hιfin, nn, hnnfin, hnndec, hnnne, π, hπ, hlin, ω, ω', hkerJ, hnil, hω, hω'⟩

end OddOrder.RepresentationTheory.Modular
