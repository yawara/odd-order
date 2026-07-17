/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import OddOrder.GroupTheory.RepresentationTheory.CyclicExtension
import OddOrder.GroupTheory.RepresentationTheory.ZIrr

/-!
# Extension of an invariant irreducible character along a cyclic quotient

**Isaacs, _Character Theory of Finite Groups_ (Academic Press, 1976), Theorem 11.22 (cyclic
case, direct construction)**: let `H ⊴ K` with `K/H` cyclic, and let `θ ∈ Irr(H)` be
`K`-invariant.  Then `θ` extends to an irreducible character `χ ∈ Irr(K)` with
`Res_H χ = θ`.

This file is the **`ℂ` / character-level layer**.  The construction itself — Schur's lemma,
the normalized conjugation unit and the extension representation — lives in
`CyclicExtension.lean` and is carried out over an **arbitrary algebraically closed field**
(Bender-Glauberman Prop 2.2(b), no characteristic hypothesis).  The only genuinely
`ℂ`-specific step is the *first* one:

* **step 1 over `ℂ`** (`nonempty_equiv_conjRep_of_character_eq`): equality of characters
  `θ^g = θ` is upgraded to an equivalence of representations `ρ ≅ ρ^g` by **character
  orthogonality**, which needs `|H|` invertible in the field.  Bender-Glauberman avoid this
  by taking `M ≅ M^x` as a hypothesis instead — see
  `exists_extension_of_nonempty_equiv_conjRep`.

Given that upgrade, steps 2-4 are the generic ones re-exported from `CyclicExtension.lean`.

This file is the **(G1) extension** brick of the constructive Clifford correspondence
(issue 9002): Peterfalvi (1.7)(b) needs each `θ ∈ Irr(H)` with abelian inertia quotient
`I(θ)/H` to extend to its inertia group, which follows by iterating the cyclic case along a
composition series of `I(θ)/H` (the coprime/canonical-extension refinement, Isaacs 6.28/8.16,
handles the invariance propagation; see `RepresentationDeterminant`).

## Main results

* `OddOrder.RepresentationTheory.nonempty_equiv_conjRep_of_character_eq` — equal characters
  make `ρ ≅ ρ^g` over `ℂ` (step 1).
* `OddOrder.RepresentationTheory.exists_conjugation_unit` — the intertwining unit, as an
  equation in `(Module.End ℂ V)ˣ`.
* `OddOrder.RepresentationTheory.exists_normalized_conjugation_unit` — the normalized unit.
* `OddOrder.RepresentationTheory.IsIrreducibleCharacter.exists_extension_of_conjBy_eq` —
  **Isaacs 11.22** at the character level.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Academic Press 1976, Theorem 11.22.
* Bender, Glauberman, *Local Analysis for the Odd Order Theorem*, Proposition 2.2(b) (the
  characteristic-free core, in `CyclicExtension.lean`).
* Peterfalvi §3 (1.7); Coq PFsection1 `cfInd_central_Inertia`.
-/

namespace OddOrder.RepresentationTheory

variable {K : Type*} [Group K] {H : Subgroup K} [hH : H.Normal]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-! ### Step 1 over `ℂ`: character orthogonality gives the intertwining unit -/

section Intertwiner

variable [FiniteDimensional ℂ V]

/-- **Equal characters give an equivalence with the conjugate** (step 1 of Isaacs 11.22).
If the conjugate representation `ρ^g` has the same character as the irreducible `ρ` — i.e.
the character of `ρ` is `g`-invariant — then `ρ ≅ ρ^g` as representations of `H`.  This is
character orthogonality: `⟨χ, χ⟩ = 1 ≠ 0` forces the `if Nonempty (Equiv _ _)` branch.

This is the one step that genuinely needs `|H|` invertible in the field; Bender-Glauberman
Prop 2.2(b) assumes `ρ ≅ ρ^g` outright and so avoids it entirely. -/
theorem nonempty_equiv_conjRep_of_character_eq [Finite ↥H] [Invertible (Nat.card ↥H : ℂ)]
    (ρ : Representation ℂ ↥H V) [Representation.IsIrreducible ρ] (g : K)
    (hinv : (conjRep ρ g).character = ρ.character) :
    Nonempty (ρ.Equiv (conjRep ρ g)) := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI := isIrreducible_conjRep ρ g
  have h1 : (Nat.card ↥H : ℂ)⁻¹ * ∑ h : ↥H, ρ.character h * ρ.character h⁻¹ = 1 := by
    rw [Representation.char_orthonormal, if_pos ⟨Representation.Equiv.refl _⟩]
  have key := Representation.char_orthonormal (conjRep ρ g) ρ
  rw [hinv, h1] at key
  by_contra hc
  rw [if_neg hc] at key
  exact one_ne_zero key

/-- **The conjugation unit** (step 1, unit form).  For an irreducible `ρ` whose character is
`g`-invariant, there is a unit `P` of the endomorphism ring with
`P · ρ(h) = ρ(g h g⁻¹) · P` for all `h ∈ H` — stated as an equation between units, with
`ρ(h)` packaged as `ρ.asGroupHom h`.

The `ℂ` specialization of `exists_conjugation_unit_of_nonempty_equiv`, with the equivalence
supplied by `nonempty_equiv_conjRep_of_character_eq`. -/
theorem exists_conjugation_unit [Finite ↥H] [Invertible (Nat.card ↥H : ℂ)]
    (ρ : Representation ℂ ↥H V) [Representation.IsIrreducible ρ] (g : K)
    (hinv : (conjRep ρ g).character = ρ.character) :
    ∃ P : (Module.End ℂ V)ˣ, ∀ h : ↥H,
      P * ρ.asGroupHom h
        = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P :=
  exists_conjugation_unit_of_nonempty_equiv ρ g
    (nonempty_equiv_conjRep_of_character_eq ρ g hinv)

end Intertwiner

/-! ### The normalized conjugation unit over `ℂ` -/

section Normalization

variable [FiniteDimensional ℂ V]

/-- **The normalized conjugation unit over `ℂ`** (steps 2-3 of Isaacs 11.22), from
`g`-invariance of the *character*.  Over `ℂ` the hypothesis `|H|` invertible is automatic, so
character invariance alone suffices; the construction itself is the characteristic-free
`exists_normalized_conjugation_unit_of_nonempty_equiv`. -/
theorem exists_normalized_conjugation_unit [Finite K]
    (ρ : Representation ℂ ↥H V) [Representation.IsIrreducible ρ] (g : K)
    (hinv : (conjRep ρ g).character = ρ.character) :
    ∃ P : (Module.End ℂ V)ˣ,
      (∀ h : ↥H, P * ρ.asGroupHom h
        = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P) ∧
      ∀ (t : ℤ) (ht : g ^ t ∈ H), P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩ := by
  haveI : Invertible (Nat.card ↥H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact exists_normalized_conjugation_unit_of_nonempty_equiv ρ g
    (nonempty_equiv_conjRep_of_character_eq ρ g hinv)

end Normalization

/-! ### The character-level extension theorem -/

section CharacterLevel

/-- **Extension along a cyclic quotient — Isaacs, _Character Theory_, Theorem 11.22 (cyclic
case).**  Let `H ⊴ K` with `K` finite and the image of `g : K` generating `K/H`, and let `θ`
be an irreducible character of `H` fixed by `g`-conjugation (equivalently, `K`-invariant,
since `H ≤ I_K(θ)` always).  Then `θ` **extends** to `K`: there is an irreducible character
`χ` of `K` with `Res_H χ = θ`.

This is the (G1) cyclic building block of the constructive Clifford correspondence
(Peterfalvi (1.7)(b), issue 9002); the abelian inertia quotient case follows by iterating
along a composition series.

The representation-level, characteristic-free analogue over any algebraically closed field is
`exists_extension_of_nonempty_equiv_conjRep` (BG Prop 2.2(b)). -/
theorem IsIrreducibleCharacter.exists_extension_of_conjBy_eq [Finite K]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ) {g : K}
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    (hinv : ClassFunction.conjBy g θ = θ) :
    ∃ χ : ClassFunction K ℂ, IsIrreducibleCharacter χ ∧
      ClassFunction.restrict H χ = θ := by
  obtain ⟨V, _, _, _, ρ, hρirr, hchar⟩ := hθ
  haveI := hρirr
  -- the conjugate representation has the same character, by invariance of `θ`
  have hinv' : (conjRep ρ g).character = ρ.character := by
    funext h
    rw [conjRep_character,
      ← congrFun hchar (ClassFunction.conjByMulEquiv (G := K) (H := H) g h),
      ← congrFun hchar h]
    exact congrFun (congrArg (fun f : ClassFunction ↥H ℂ => (f : ↥H → ℂ)) hinv) h
  obtain ⟨P, hP, hPt⟩ := exists_normalized_conjugation_unit ρ g hinv'
  refine ⟨repCharacterClassFunction (cyclicExtension ρ g P hP hPt hgen),
    ⟨V, inferInstance, inferInstance, inferInstance, cyclicExtension ρ g P hP hPt hgen,
      isIrreducible_cyclicExtension hP hPt hgen, rfl⟩, ?_⟩
  ext h
  rw [ClassFunction.restrict_apply]
  have h3 : cyclicExtension ρ g P hP hPt hgen ((h : K)) = ρ h :=
    DFunLike.congr_fun (cyclicExtension_comp_subtype hP hPt hgen) h
  have h4 : (cyclicExtension ρ g P hP hPt hgen).character (h : K) = ρ.character h :=
    congrArg (LinearMap.trace ℂ V) h3
  change (cyclicExtension ρ g P hP hPt hgen).character (h : K) = _
  rw [h4, ← congrFun hchar h]

end CharacterLevel

end OddOrder.RepresentationTheory
