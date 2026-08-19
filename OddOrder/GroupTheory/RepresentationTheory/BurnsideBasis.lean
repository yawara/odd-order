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

/-- **Linear independence of central-coset images, for any section** (BG (2.11), independence half).
For any section `t` of `P ↠ P/Z(P)` (`⟦t c⟧ = c`), the family `c ↦ ρ(t c)` is `F`-linearly
independent in `End_F V`: pairing `A ↦ trace(A · ρ(t c')⁻¹)` gives the diagonal Gram matrix
`χ(t c · (t c')⁻¹) = δ_{c c'} · (dim V)`, nonsingular since `(dim V : F) ≠ 0`. -/
theorem linearIndependent_representation_section [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P)
    (t : P ⧸ Subgroup.center P → P) (ht : ∀ c, (↑(t c) : P ⧸ Subgroup.center P) = c) :
    LinearIndependent F (fun c : P ⧸ Subgroup.center P => ρ (t c)) := by
  classical
  have : Fintype P := Fintype.ofFinite P
  have : Fintype (P ⧸ Subgroup.center P) := Fintype.ofFinite _
  have hmem : ∀ c c' : P ⧸ Subgroup.center P,
      t c * (t c')⁻¹ ∈ Subgroup.center P ↔ c = c' := by
    intro c c'
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ht, ht]
    exact mul_inv_eq_one
  have hTval : ∀ c c' : P ⧸ Subgroup.center P,
      LinearMap.trace F V (ρ (t c) * ρ ((t c')⁻¹))
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
        ((∑ i, coef i • ρ (t i)) * ρ ((t j)⁻¹))
      = ∑ i, coef i • LinearMap.trace F V (ρ (t i) * ρ ((t j)⁻¹)) := by
    rw [Finset.sum_mul, map_sum]
    simp only [smul_mul_assoc, map_smul]
  rw [hcoef, zero_mul, map_zero] at happ
  simp only [hTval, smul_ite, smul_zero] at happ
  rw [Finset.sum_ite_eq' Finset.univ j] at happ
  simp only [Finset.mem_univ, if_true, smul_eq_mul] at happ
  exact (mul_eq_zero.mp happ.symm).resolve_right (finrank_cast_ne_zero ρ hf hcl)

/-- **Spanning of central-coset images, for any section** (BG (2.11), Burnside spanning half). For
any section `t` of `P ↠ P/Z(P)`, the images `{ρ(t c)}` span `End_F V`: by Burnside `{ρ g}` spans,
and each `ρ g` is the central-character multiple `s · ρ(t ⟦g⟧)`. -/
theorem span_range_section_eq_top [FiniteDimensional F V] (ρ : Representation F P V)
    [ρ.IsIrreducible] (t : P ⧸ Subgroup.center P → P)
    (ht : ∀ c, (↑(t c) : P ⧸ Subgroup.center P) = c) :
    Submodule.span F (Set.range fun c : P ⧸ Subgroup.center P => ρ (t c)) = ⊤ := by
  set v : (P ⧸ Subgroup.center P) → Module.End F V := fun c => ρ (t c) with hv
  have hmem_span : ∀ g : P, ρ g ∈ Submodule.span F (Set.range v) := by
    intro g
    have hz : g * (t (↑g : P ⧸ Subgroup.center P))⁻¹ ∈ Subgroup.center P := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ht]
      exact mul_inv_cancel _
    obtain ⟨s, hs⟩ := center_isScalar ρ hz
    have hgeq : g = g * (t (↑g : P ⧸ Subgroup.center P))⁻¹ * t (↑g : P ⧸ Subgroup.center P) := by
      group
    rw [hgeq, map_mul, hs, ← Module.End.one_eq_id, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ s (Submodule.subset_span (Set.mem_range_self _))
  have hsub : ∀ r : MonoidAlgebra F P, ρ.asAlgebraHom r ∈ Submodule.span F (Set.range v) := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | of g => rw [asAlgebraHom_of]; exact hmem_span g
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro A _
  obtain ⟨r, rfl⟩ := asAlgebraHom_surjective_of_isAlgClosed ρ A
  exact hsub r

/-- **The Burnside basis, for any section** (BG (2.11)): for a faithful irreducible representation
of a finite group `P` of nilpotency class `≤ 2` over an algebraically closed field
(`char ∤ |P|`), and any section `t` of `P ↠ P/Z(P)`, the images `{ρ(t c) : c ∈ P/Z(P)}` form a
basis of `End_F V`.
(With a `φ`-equivariant section, the conjugation action on this basis is a *pure permutation* —
the input to the BG (2.11) `F[H]`-module structure.) -/
noncomputable def burnsideBasisOfSection [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P)
    (t : P ⧸ Subgroup.center P → P) (ht : ∀ c, (↑(t c) : P ⧸ Subgroup.center P) = c) :
    Basis (P ⧸ Subgroup.center P) F (Module.End F V) :=
  Basis.mk (linearIndependent_representation_section ρ hf hcl t ht)
    (span_range_section_eq_top ρ t ht).ge

@[simp]
theorem burnsideBasisOfSection_apply [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P)
    (t : P ⧸ Subgroup.center P → P) (ht : ∀ c, (↑(t c) : P ⧸ Subgroup.center P) = c)
    (c : P ⧸ Subgroup.center P) :
    burnsideBasisOfSection ρ hf hcl t ht c = ρ (t c) :=
  Basis.mk_apply _ _ c

/-- **Linear independence of the `Quotient.out` central-coset images** (BG (2.11)). Special case of
`linearIndependent_representation_section` at the canonical section `Quotient.out`. -/
theorem linearIndependent_representation_quotientOut [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P) :
    LinearIndependent F (fun c : P ⧸ Subgroup.center P => ρ (Quotient.out c)) :=
  linearIndependent_representation_section ρ hf hcl Quotient.out (fun c => Quotient.out_eq' c)

/-- **The Burnside basis** (BG (2.11)) at the canonical section `Quotient.out`. -/
noncomputable def burnsideBasis [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P) :
    Basis (P ⧸ Subgroup.center P) F (Module.End F V) :=
  burnsideBasisOfSection ρ hf hcl Quotient.out (fun c => Quotient.out_eq' c)

@[simp]
theorem burnsideBasis_apply [FiniteDimensional F V] [Finite P]
    [Invertible (Nat.card P : F)] (ρ : Representation F P V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hcl : commutator P ≤ Subgroup.center P)
    (c : P ⧸ Subgroup.center P) :
    burnsideBasis ρ hf hcl c = ρ (Quotient.out c) :=
  burnsideBasisOfSection_apply ρ hf hcl Quotient.out _ c

end OddOrder.RepresentationTheory
