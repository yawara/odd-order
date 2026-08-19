/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.AnisotropicNormForm
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.RootGroupTwistedCoordinates
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.TwistedProductComparison

/-!
# An anisotropic twisted product over `𝐅_{q²}` is the unitary root group

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3 (4), pp. 130–131.

The Proposition of Chapter III §3 presents `Q` as `BilinearTwistedProduct φ`, where
`φ` is an anisotropic cocycle on a field `E` of order `q²` with values in its subfield
`F` of order `q`, semilinear in the sense `φ (a x) (b y) = a b^θ φ x y`.  Chapter IV
§3 (3) shows `θ = 1`, so `φ` is `F`-bilinear.  Chapter IV §3 (4) is stated in the
unitary coordinates of `PSU(3, q)` — that is, in `RootGroup q`.

This file supplies the bridge.  Three facts combine:

* an anisotropic `F`-bilinear cocycle has the Hermitian norm as diagonal, after an
  `F`-linear change of variable
  (`OddOrder.FiniteField.exists_addEquiv_norm_of_anisotropic`);
* two finite fields of the same order are isomorphic
  (`FiniteField.ringEquivOfCardEq`), and a ring isomorphism matches the fixed
  subfields of the `q`-power Frobenius;
* a twisted product depends on its cocycle only through the diagonal
  (`BilinearTwistedProduct.nonempty_mulEquiv_of_diag`), and the root group is the
  twisted product of the corrected Hermitian cocycle (`toTwistedProduct`).

## Main results

* `ProjectiveUnitary.frobFixedAddEquiv` — the fixed subfields correspond under a ring
  isomorphism.
* `ProjectiveUnitary.nonempty_mulEquiv_rootGroup_of_anisotropic` — the bridge.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

open OddOrder.FiniteField
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups

section FixedSubfieldTransport

variable {E E' : Type*} [_root_.Field E] [Finite E] [CharP E 2]
  [_root_.Field E'] [Finite E'] [CharP E' 2] (m : ℕ)

/-- A ring isomorphism carries the fixed subfield of the `q`-power Frobenius into the
corresponding one: `x^q = x` is preserved. -/
theorem map_mem_frobFixedSubfield_of_ringEquiv (σ : E ≃+* E') {x : E}
    (hx : x ∈ frobFixedSubfield E 2 m) : σ x ∈ frobFixedSubfield E' 2 m := by
  rw [mem_frobFixedSubfield] at hx ⊢
  rw [← map_pow, hx]

/-- **The fixed subfields correspond under a ring isomorphism.**  Only the additive
structure is needed downstream, which is what the central coordinate of a twisted
product sees. -/
noncomputable def frobFixedAddEquiv (σ : E ≃+* E') :
    ↥(frobFixedSubfield E 2 m) ≃+ ↥(frobFixedSubfield E' 2 m) where
  toFun z := ⟨σ z, map_mem_frobFixedSubfield_of_ringEquiv m σ z.2⟩
  invFun z := ⟨σ.symm z, map_mem_frobFixedSubfield_of_ringEquiv m σ.symm z.2⟩
  left_inv _ := Subtype.ext (σ.symm_apply_apply _)
  right_inv _ := Subtype.ext (σ.apply_symm_apply _)
  map_add' _ _ := Subtype.ext (map_add σ _ _)

@[simp] theorem frobFixedAddEquiv_coe (σ : E ≃+* E')
    (z : ↥(frobFixedSubfield E 2 m)) :
    ((frobFixedAddEquiv m σ z : ↥(frobFixedSubfield E' 2 m)) : E') = σ (z : E) :=
  rfl

end FixedSubfieldTransport

/-- **An anisotropic `F`-bilinear twisted product over a field of order `q²` is the
unitary root group** (Peterfalvi Part II, Ch. IV §3 (4), pp. 130–131).

This is the translation between the two coordinate systems of Chapter IV: the model
`S₁` of Chapter III §3 on the left, and the unipotent group of `PSU(3, q)` — the
group of pairs `(a, b)` with `b + b̄ = a ā` — on the right.

The hypothesis `hsemi` is the `θ = 1` form of the semilinearity delivered by the
Proposition of Chapter III §3, and `θ = 1` is Chapter IV §3 (3). -/
theorem nonempty_mulEquiv_rootGroup_of_anisotropic {E : Type*} [_root_.Field E] [Finite E]
    [CharP E 2] [Algebra (ZMod 2) E] {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (φ : LinearMap.BilinMap (ZMod 2) E ↥(frobFixedSubfield E 2 n))
    (hsemi : ∀ a ∈ frobFixedSubfield E 2 n, ∀ b ∈ frobFixedSubfield E 2 n, ∀ x y : E,
      ((φ (a * x) (b * y) : ↥(frobFixedSubfield E 2 n)) : E)
        = a * b * ((φ x y : ↥(frobFixedSubfield E 2 n)) : E))
    (haniso : ∀ x : E, x ≠ 0 → φ x x ≠ 0) :
    Nonempty (BilinearTwistedProduct φ ≃* RootGroup n) := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have : Fintype (Field n) := Fintype.ofFinite (Field n)
  -- the change of variable making the diagonal the Hermitian norm
  obtain ⟨f₀, -, hf₀⟩ :=
    exists_addEquiv_norm_of_anisotropic n hn.ne' hcard φ hsemi haniso
  -- the identification of `E` with the standard field of order `q²`
  have hcards : Fintype.card E = Fintype.card (Field n) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, natCard_field n hn,
      ← pow_mul]
    congr 1
    omega
  set σ : E ≃+* Field n := FiniteField.ringEquivOfCardEq hcards with hσ
  -- the corrected Hermitian cocycle on the target
  have hcardF : Nat.card (Field n) = (2 ^ n) ^ 2 := by
    rw [natCard_field n hn, ← pow_mul]
    congr 1
    omega
  obtain ⟨u, hu⟩ := exists_frobTrace_eq_one (E := Field n) n hn.ne' hcardF
  -- the two diagonals correspond
  have hdiag : ∀ x : E,
      rootBilin hn hu ((f₀.trans σ.toAddEquiv) x) ((f₀.trans σ.toAddEquiv) x)
        = frobFixedAddEquiv n σ (φ x x) := by
    intro x
    refine Subtype.ext ?_
    rw [rootBilin_diag_coe hn hu, frobFixedAddEquiv_coe]
    change σ (f₀ x) * star (σ (f₀ x)) = σ ((φ x x : ↥(frobFixedSubfield E 2 n)) : E)
    rw [star_eq_conjugation, conjugation_apply n hn, ← map_pow, ← map_mul, ← hf₀ x]
  exact (BilinearTwistedProduct.nonempty_mulEquiv_of_diag
    (f₀.trans σ.toAddEquiv) (frobFixedAddEquiv n σ) hdiag).map
      fun e => e.trans (toTwistedProduct hn hu).symm

end OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
