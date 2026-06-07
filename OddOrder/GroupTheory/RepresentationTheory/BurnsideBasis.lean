/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.ExtraspecialFaithful

/-!
# The Burnside basis of `End_F V` (BG (2.11))

`OddOrder.GroupTheory.RepresentationTheory` shared module exposing the **Burnside basis** used in
Bender–Glauberman (2.11): for a faithful irreducible representation `ρ` of a finite group `P` of
nilpotency class `≤ 2` over an algebraically closed field with `char ∤ |P|`, the images
`{ρ(out c) : c ∈ P/Z(P)}` of a transversal of the central cosets form a **basis** of `End_F V`.

The two halves are already established in `ExtraspecialFaithful.lean`/`AbsolutelyIrreducible.lean`
(buried inside the dimension count `sq_finrank_eq_card_quotient_center`):

* **spanning** — `span_range_quotient_out_eq_top` (Burnside: `{ρ g}` spans, and each `ρ g` is a
  central-character multiple of `ρ(out ⟦g⟧)`);
* **linear independence** — the trace-form Gram matrix `[χ(out c · (out c')⁻¹)] = (dim V)·I` is
  nonsingular because `(dim V : F) ≠ 0` (`finrank_cast_ne_zero`).

Here we lift the independence to a standalone lemma and package both into
`burnsideBasis : Basis (P ⧸ Z(P)) F (End_F V)`.  This is the carrier for the `H`-module structure
of `E(P)` (the keystone `dim E₀ = dim E_m + 1` of BG Thm 2.5).
-/

namespace OddOrder.RepresentationTheory

open Representation Module

variable {F : Type*} [Field F] [IsAlgClosed F]
variable {P : Type*} [Group P] {V : Type*} [AddCommGroup V] [Module F V]

/-- **Linear independence of the central-coset images** (BG (2.11), independence half). The family
`c ↦ ρ(out c)` indexed by `P/Z(P)` is `F`-linearly independent in `End_F V`: pairing
`A ↦ trace(A · ρ(out c')⁻¹)` against it gives the diagonal Gram matrix `χ(out c · (out c')⁻¹) =
δ_{c c'} · (dim V)`, nonsingular since `(dim V : F) ≠ 0`. (This is the `hindep` step previously
buried inside `card_quotient_center_le_sq_finrank`.) -/
theorem linearIndependent_representation_quotientOut [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P) :
    LinearIndependent F (fun c : P ⧸ Subgroup.center P => ρ (Quotient.out c)) := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  haveI : Fintype (P ⧸ Subgroup.center P) := Fintype.ofFinite _
  have hco : ∀ c : P ⧸ Subgroup.center P, (↑(Quotient.out c) : P ⧸ Subgroup.center P) = c :=
    fun c => Quotient.out_eq' c
  have hmem : ∀ c c' : P ⧸ Subgroup.center P,
      Quotient.out c * (Quotient.out c')⁻¹ ∈ Subgroup.center P ↔ c = c' := by
    intro c c'
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hco, hco]
    exact mul_inv_eq_one
  have hTval : ∀ c c' : P ⧸ Subgroup.center P,
      LinearMap.trace F V (ρ (Quotient.out c) * ρ ((Quotient.out c')⁻¹))
        = if c = c' then (Module.finrank F V : F) else 0 := by
    intro c c'
    rw [← map_mul]
    change ρ.character _ = _
    by_cases h : c = c'
    · subst h; rw [if_pos rfl, mul_inv_cancel, char_one]
    · rw [if_neg h]
      exact character_eq_zero_of_notMem_center ρ hf hcl ((hmem c c').not.mpr h)
  rw [Fintype.linearIndependent_iff]
  intro coef hcoef j
  have happ : LinearMap.trace F V
        ((∑ i, coef i • ρ (Quotient.out i)) * ρ ((Quotient.out j)⁻¹))
      = ∑ i, coef i • LinearMap.trace F V (ρ (Quotient.out i) * ρ ((Quotient.out j)⁻¹)) := by
    rw [Finset.sum_mul, map_sum]
    simp only [smul_mul_assoc, map_smul]
  rw [hcoef, zero_mul, map_zero] at happ
  simp only [hTval, smul_ite, smul_zero] at happ
  rw [Finset.sum_ite_eq' Finset.univ j] at happ
  simp only [Finset.mem_univ, if_true, smul_eq_mul] at happ
  exact (mul_eq_zero.mp happ.symm).resolve_right (finrank_cast_ne_zero ρ hf hcl)

/-- **The Burnside basis** (BG (2.11)): for a faithful irreducible representation of a finite group
`P` of nilpotency class `≤ 2` over an algebraically closed field with `char ∤ |P|`, the images
`{ρ(out c) : c ∈ P/Z(P)}` form a basis of `End_F V`. Independence is
`linearIndependent_representation_quotientOut`; spanning is `span_range_quotient_out_eq_top`. -/
noncomputable def burnsideBasis [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P) :
    Basis (P ⧸ Subgroup.center P) F (Module.End F V) :=
  Basis.mk (linearIndependent_representation_quotientOut ρ hf hcl)
    (span_range_quotient_out_eq_top ρ).ge

@[simp]
theorem burnsideBasis_apply [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P)
    (c : P ⧸ Subgroup.center P) :
    burnsideBasis ρ hf hcl c = ρ (Quotient.out c) :=
  Basis.mk_apply _ _ c

end OddOrder.RepresentationTheory
