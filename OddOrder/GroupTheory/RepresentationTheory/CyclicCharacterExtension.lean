/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible
import OddOrder.GroupTheory.RepresentationTheory.Inertia
import OddOrder.GroupTheory.RepresentationTheory.ZIrr

/-!
# Extension of an invariant irreducible character along a cyclic quotient

**Isaacs, _Character Theory of Finite Groups_ (Academic Press, 1976), Theorem 11.22 (cyclic
case, direct construction)**: let `H ⊴ K` with `K/H` cyclic, and let `θ ∈ Irr(H)` be
`K`-invariant.  Then `θ` extends to an irreducible character `χ ∈ Irr(K)` with
`Res_H χ = θ`.

The construction is the classical one, avoiding cohomology.  Fix `g : K` whose image
generates `K/H`, and a representation `ρ` affording `θ`.

1. *(intertwiner)* Invariance `θ^g = θ` says the conjugate representation
   `ρ^g = ρ ∘ (h ↦ g h g⁻¹)` has the same character as `ρ`; both are irreducible, so by
   character orthogonality they are equivalent: there is a unit `P` with
   `P ρ(h) P⁻¹ = ρ(g h g⁻¹)`.
2. *(Schur)* For `m` with `g ^ m ∈ H`, the unit `ρ(g^m)⁻¹ P^m` commutes with every `ρ(h)`,
   hence is a scalar `c ≠ 0` by Schur's lemma.
3. *(normalization)* Replacing `P` by `ζ • P` where `ζ^m = c⁻¹` (possible over `ℂ`) gives a
   unit with `P^t = ρ(g^t)` for **every** `t : ℤ` with `g^t ∈ H`.
4. *(extension)* `ρ̃(g^i h) := P^i ρ(h)` is then a well-defined irreducible representation
   of `K` restricting to `ρ` on `H`; its character extends `θ`.

This file is the **(G1) extension** brick of the constructive Clifford correspondence
(issue 9002): Peterfalvi (1.7)(b) needs each `θ ∈ Irr(H)` with abelian inertia quotient
`I(θ)/H` to extend to its inertia group, which follows by iterating the cyclic case along a
composition series of `I(θ)/H` (the coprime/canonical-extension refinement, Isaacs 6.28/8.16,
handles the invariance propagation; see `RepresentationDeterminant`).

## Main results

* `OddOrder.RepresentationTheory.conjRep` — the conjugate representation
  `ρ^g(h) = ρ(g h g⁻¹)` of a normal subgroup's representation.
* `OddOrder.RepresentationTheory.Representation.isIrreducible_of_isIrreducible_comp` —
  irreducibility ascends from any precomposition `σ ∘ f` to `σ`.
* `OddOrder.RepresentationTheory.nonempty_equiv_conjRep_of_character_eq` — equal characters
  make `ρ ≅ ρ^g` (step 1).
* `OddOrder.RepresentationTheory.exists_conjugation_unit` — the intertwining unit, as an
  equation in `(Module.End ℂ V)ˣ`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Academic Press 1976, Theorem 11.22.
* Peterfalvi §3 (1.7); Coq PFsection1 `cfInd_central_Inertia`.
-/

namespace OddOrder.RepresentationTheory

variable {K : Type*} [Group K] {H : Subgroup K} [hH : H.Normal]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-! ### The conjugate representation -/

section ConjRep

/-- The **conjugate representation** `ρ^g` of a representation `ρ` of a normal subgroup
`H ⊴ K` by an ambient element `g : K`: it acts by `(ρ^g)(h) = ρ(g h g⁻¹)`.  Its character
is Peterfalvi's conjugate character `θ^g` (`ClassFunction.conjBy`). -/
def conjRep (ρ : Representation ℂ ↥H V) (g : K) : Representation ℂ ↥H V :=
  ρ.comp (ClassFunction.conjByMulEquiv (G := K) (H := H) g).toMonoidHom

@[simp] theorem conjRep_apply (ρ : Representation ℂ ↥H V) (g : K) (h : ↥H) :
    conjRep ρ g h = ρ (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) :=
  rfl

/-- The character of the conjugate representation is the conjugate of the character. -/
theorem conjRep_character (ρ : Representation ℂ ↥H V) (g : K) (h : ↥H) :
    (conjRep ρ g).character h
      = ρ.character (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) :=
  rfl

/-- **Irreducibility ascends along any precomposition.**  If `σ ∘ f` is irreducible for
*some* homomorphism `f : H' →* G'`, then `σ` is irreducible: a `σ`-invariant submodule is in
particular `σ ∘ f`-invariant.  (No surjectivity of `f` is needed, in contrast to the
descent direction `isIrreducible_comp_of_surjective`.) -/
theorem Representation.isIrreducible_of_isIrreducible_comp
    {G' H' : Type*} [Group G'] [Group H'] {f : H' →* G'}
    (σ : Representation ℂ G' V) (hσ : Representation.IsIrreducible (σ.comp f)) :
    Representation.IsIrreducible σ := by
  have h1 : IsSimpleOrder (Subrepresentation (σ.comp f)) := hσ
  haveI := h1.toNontrivial
  -- restrict the invariance condition of a `σ`-subrepresentation to the image of `f`
  let ι : Subrepresentation σ → Subrepresentation (σ.comp f) := fun R =>
    { toSubmodule := R.toSubmodule
      apply_mem_toSubmodule := fun h _v hv => R.apply_mem_toSubmodule (f h) hv }
  have hbotS : (⊥ : Subrepresentation σ).toSubmodule = ⊥ := rfl
  have htopS : (⊤ : Subrepresentation σ).toSubmodule = ⊤ := rfl
  have hbotC : (⊥ : Subrepresentation (σ.comp f)).toSubmodule = ⊥ := rfl
  have htopC : (⊤ : Subrepresentation (σ.comp f)).toSubmodule = ⊤ := rfl
  -- `⊥ ≠ ⊤` in `Submodule ℂ V`, read off from the simple order on `Subrepresentation (σ.comp f)`.
  have hVne : (⊥ : Submodule ℂ V) ≠ ⊤ := fun h2 =>
    bot_ne_top (α := Subrepresentation (σ.comp f))
      (Subrepresentation.toSubmodule_injective (by rw [hbotC, htopC]; exact h2))
  haveI hnt : Nontrivial (Subrepresentation σ) :=
    ⟨⟨⊥, ⊤, fun hbt => hVne (by rw [← hbotS, hbt, htopS])⟩⟩
  exact ⟨fun S => by
    rcases h1.eq_bot_or_eq_top (ι S) with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective
        ((congrArg Subrepresentation.toSubmodule h).trans hbotC))
    · exact Or.inr (Subrepresentation.toSubmodule_injective
        ((congrArg Subrepresentation.toSubmodule h).trans htopC))⟩

/-- The conjugate of an irreducible representation is irreducible: `ρ = (ρ^g) ∘ (conj g⁻¹)`,
so irreducibility of `ρ` ascends to `ρ^g` by `isIrreducible_of_isIrreducible_comp`. -/
theorem isIrreducible_conjRep (ρ : Representation ℂ ↥H V) [Representation.IsIrreducible ρ]
    (g : K) : Representation.IsIrreducible (conjRep ρ g) := by
  have hcomp : (conjRep ρ g).comp
      (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹).toMonoidHom = ρ := by
    refine MonoidHom.ext fun h => ?_
    calc ((conjRep ρ g).comp
          (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹).toMonoidHom) h
        = ρ ((ClassFunction.conjByMulEquiv (G := K) (H := H) g)
            ((ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹) h)) := rfl
      _ = ρ h := by rw [ClassFunction.conjByMulEquiv_mul, mul_inv_cancel,
            ClassFunction.conjByMulEquiv_one]
  exact Representation.isIrreducible_of_isIrreducible_comp (conjRep ρ g)
    (hcomp ▸ ‹Representation.IsIrreducible ρ›)

end ConjRep

/-! ### Step 1: the intertwining unit of an invariant irreducible representation -/

section Intertwiner

variable [FiniteDimensional ℂ V]

/-- **Equal characters give an equivalence with the conjugate** (step 1 of Isaacs 11.22).
If the conjugate representation `ρ^g` has the same character as the irreducible `ρ` — i.e.
the character of `ρ` is `g`-invariant — then `ρ ≅ ρ^g` as representations of `H`.  This is
character orthogonality: `⟨χ, χ⟩ = 1 ≠ 0` forces the `if Nonempty (Equiv _ _)` branch. -/
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
`ρ(h)` packaged as `ρ.asGroupHom h`. -/
theorem exists_conjugation_unit [Finite ↥H] [Invertible (Nat.card ↥H : ℂ)]
    (ρ : Representation ℂ ↥H V) [Representation.IsIrreducible ρ] (g : K)
    (hinv : (conjRep ρ g).character = ρ.character) :
    ∃ P : (Module.End ℂ V)ˣ, ∀ h : ↥H,
      P * ρ.asGroupHom h
        = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P := by
  obtain ⟨φ⟩ := nonempty_equiv_conjRep_of_character_eq ρ g hinv
  refine ⟨⟨φ.toLinearMap, φ.toLinearEquiv.symm.toLinearMap,
    LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩, fun h => ?_⟩
  · rw [Module.End.mul_apply]
    exact φ.toLinearEquiv.apply_symm_apply v
  · rw [Module.End.mul_apply]
    exact φ.toLinearEquiv.symm_apply_apply v
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    change φ.toLinearMap * (ρ.asGroupHom h : Module.End ℂ V)
      = (ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h)
          : Module.End ℂ V) * φ.toLinearMap
    rw [Representation.asGroupHom_apply, Representation.asGroupHom_apply,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact φ.isIntertwining' h

end Intertwiner

/-! ### Steps 2–3: Schur's lemma and the normalized conjugation unit -/

section Normalization

variable [FiniteDimensional ℂ V]

/-- **Schur's lemma, commutant form.**  An endomorphism commuting with every `ρ x` of an
irreducible complex representation is a scalar multiple of the identity. -/
theorem exists_smul_id_of_forall_mul_comm {G' : Type*} [Group G']
    (ρ : Representation ℂ G' V) [Representation.IsIrreducible ρ]
    (T : Module.End ℂ V) (hT : ∀ x : G', ρ x * T = T * ρ x) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  have hT' : ∀ (x : G') (v : V), T (ρ x v) = ρ x (T v) := fun x v => by
    have h1 := LinearMap.congr_fun (hT x) v
    simpa only [Module.End.mul_apply] using h1.symm
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective (T.intertwiningMap_of_isIntertwiningMap ρ ρ hT')
  refine ⟨c, ?_⟩
  have hL : T = (algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c).toLinearMap := by
    rw [hc]
    rfl
  rw [hL, Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.toLinearMap_smul]
  congr 1

variable {ρ : Representation ℂ ↥H V} {g : K} {P : (Module.End ℂ V)ˣ}

omit [FiniteDimensional ℂ V] in
/-- The inverse of a conjugation unit conjugates in the opposite direction:
`P⁻¹ · ρ(h) = ρ(g⁻¹ h g) · P⁻¹`. -/
theorem conjugation_unit_inv_comm
    (hP : ∀ h : ↥H, P * ρ.asGroupHom h
      = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P) (h : ↥H) :
    P⁻¹ * ρ.asGroupHom h
      = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h) * P⁻¹ := by
  have key := hP (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h)
  rw [ClassFunction.conjByMulEquiv_mul, mul_inv_cancel,
    ClassFunction.conjByMulEquiv_one] at key
  calc P⁻¹ * ρ.asGroupHom h
      = P⁻¹ * (ρ.asGroupHom h * P) * P⁻¹ := by group
    _ = P⁻¹ * (P * ρ.asGroupHom
          (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h)) * P⁻¹ := by rw [← key]
    _ = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h) * P⁻¹ := by
        group

omit [FiniteDimensional ℂ V] in
/-- **Iterated conjugation** (toward step 2).  A conjugation unit for `g` conjugates by `g^i`
after taking the `i`-th power: `P^i · ρ(h) = ρ(g^i h g^{-i}) · P^i` for every `i : ℤ`. -/
theorem conjugation_unit_zpow_comm
    (hP : ∀ h : ↥H, P * ρ.asGroupHom h
      = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P) :
    ∀ (i : ℤ) (h : ↥H), P ^ i * ρ.asGroupHom h
      = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) (g ^ i) h) * P ^ i := by
  intro i
  induction i using Int.induction_on with
  | zero =>
    intro h
    rw [zpow_zero P, zpow_zero g, ClassFunction.conjByMulEquiv_one, one_mul, mul_one]
  | succ i ih =>
    intro h
    rw [zpow_add_one P (i : ℤ), zpow_add_one g (i : ℤ)]
    calc P ^ (i : ℤ) * P * ρ.asGroupHom h
        = P ^ (i : ℤ) * (P * ρ.asGroupHom h) := by group
      _ = P ^ (i : ℤ) * (ρ.asGroupHom
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P) := by rw [hP h]
      _ = P ^ (i : ℤ) * ρ.asGroupHom
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P := by group
      _ = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) (g ^ (i : ℤ))
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g h)) * P ^ (i : ℤ) * P := by
          rw [ih (ClassFunction.conjByMulEquiv (G := K) (H := H) g h)]
      _ = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) (g ^ (i : ℤ) * g) h)
            * (P ^ (i : ℤ) * P) := by rw [ClassFunction.conjByMulEquiv_mul]; group
  | pred i ih =>
    intro h
    rw [zpow_sub_one P (-(i : ℤ)), zpow_sub_one g (-(i : ℤ))]
    calc P ^ (-(i : ℤ)) * P⁻¹ * ρ.asGroupHom h
        = P ^ (-(i : ℤ)) * (P⁻¹ * ρ.asGroupHom h) := by group
      _ = P ^ (-(i : ℤ)) * (ρ.asGroupHom
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h) * P⁻¹) := by
          rw [conjugation_unit_inv_comm hP h]
      _ = P ^ (-(i : ℤ)) * ρ.asGroupHom
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h) * P⁻¹ := by group
      _ = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) (g ^ (-(i : ℤ)))
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h))
            * P ^ (-(i : ℤ)) * P⁻¹ := by
          rw [ih (ClassFunction.conjByMulEquiv (G := K) (H := H) g⁻¹ h)]
      _ = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H)
            (g ^ (-(i : ℤ)) * g⁻¹) h) * (P ^ (-(i : ℤ)) * P⁻¹) := by
          rw [ClassFunction.conjByMulEquiv_mul]; group

/-- **The normalized conjugation unit** (steps 2–3 of Isaacs 11.22).  For an irreducible `ρ`
whose character is `g`-invariant, there is a unit `P` that

* conjugates `ρ(h)` to `ρ(g h g⁻¹)`: `P · ρ(h) = ρ(g h g⁻¹) · P`, and
* satisfies `P ^ t = ρ(g ^ t)` for **every** `t : ℤ` with `g ^ t ∈ H`.

The intertwiner of `exists_conjugation_unit` satisfies the second condition only up to a
scalar (Schur's lemma applied to `ρ(g^m)⁻¹ P^m`, where `m` is the order of `gH` in `K/H`);
rescaling by an `m`-th root of that scalar — available over `ℂ` — repairs it, first at
`t = m` and then for all multiples of `m`, i.e. for all valid `t`. -/
theorem exists_normalized_conjugation_unit [Finite K]
    (ρ : Representation ℂ ↥H V) [Representation.IsIrreducible ρ] (g : K)
    (hinv : (conjRep ρ g).character = ρ.character) :
    ∃ P : (Module.End ℂ V)ˣ,
      (∀ h : ↥H, P * ρ.asGroupHom h
        = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P) ∧
      ∀ (t : ℤ) (ht : g ^ t ∈ H), P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩ := by
  haveI : Invertible (Nat.card ↥H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨P₀, hP₀⟩ := exists_conjugation_unit ρ g hinv
  -- the order `m` of `gH` in `K/H`; `{t : ℤ | g^t ∈ H} = mℤ`
  set m : ℕ := orderOf (QuotientGroup.mk' H g) with hm
  have hm0 : 0 < m := orderOf_pos _
  have hgm : g ^ m ∈ H := by
    have h1 : (QuotientGroup.mk' H) (g ^ m) = 1 := by
      rw [map_pow]
      exact pow_orderOf_eq_one _
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hdvd : ∀ t : ℤ, g ^ t ∈ H → (m : ℤ) ∣ t := by
    intro t ht
    rw [hm, orderOf_dvd_iff_zpow_eq_one, ← map_zpow, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ht
  -- `T := ρ(g^m)⁻¹ · P₀^m` commutes with the image of `ρ` …
  set R : (Module.End ℂ V)ˣ := ρ.asGroupHom ⟨g ^ m, hgm⟩ with hR
  have hTcomm : ∀ h : ↥H,
      ρ h * ((R⁻¹ * P₀ ^ (m : ℤ) : (Module.End ℂ V)ˣ) : Module.End ℂ V)
      = ((R⁻¹ * P₀ ^ (m : ℤ) : (Module.End ℂ V)ˣ) : Module.End ℂ V) * ρ h := by
    intro h
    have h2 : ClassFunction.conjByMulEquiv (G := K) (H := H) (g ^ (m : ℤ)) h
        = ⟨g ^ m, hgm⟩ * h * (⟨g ^ m, hgm⟩ : ↥H)⁻¹ := by
      apply Subtype.ext
      rw [ClassFunction.conjByMulEquiv_apply, zpow_natCast]
      rfl
    have h1 := conjugation_unit_zpow_comm hP₀ (m : ℤ) h
    rw [h2, map_mul, map_mul, map_inv, ← hR] at h1
    -- h1 : P₀^m * ρ(h) = (R · ρ(h) · R⁻¹) · P₀^m; rearrange to the commutant form
    have hu : ρ.asGroupHom h * (R⁻¹ * P₀ ^ (m : ℤ))
        = (R⁻¹ * P₀ ^ (m : ℤ)) * ρ.asGroupHom h := by
      calc ρ.asGroupHom h * (R⁻¹ * P₀ ^ (m : ℤ))
          = R⁻¹ * (R * ρ.asGroupHom h * R⁻¹ * P₀ ^ (m : ℤ)) := by group
        _ = R⁻¹ * (P₀ ^ (m : ℤ) * ρ.asGroupHom h) := by rw [← h1]
        _ = (R⁻¹ * P₀ ^ (m : ℤ)) * ρ.asGroupHom h := by group
    have := congrArg Units.val hu
    simpa only [Units.val_mul, Representation.asGroupHom_apply] using this
  -- … hence is a nonzero scalar `c` by Schur
  obtain ⟨c, hc⟩ := exists_smul_id_of_forall_mul_comm ρ _ hTcomm
  haveI : Nontrivial V := by
    haveI h1 : Nontrivial (Subrepresentation ρ) := IsSimpleOrder.toNontrivial
    have h2 : Nontrivial (Submodule ℂ V) :=
      (Subrepresentation.toSubmodule_injective (ρ := ρ)).nontrivial
    exact (Submodule.nontrivial_iff ℂ).mp h2
  haveI : Nontrivial (Module.End ℂ V) := ⟨1, 0, fun h1 => by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (by simpa using LinearMap.congr_fun h1 v)⟩
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact Units.ne_zero (R⁻¹ * P₀ ^ (m : ℤ)) hc
  -- an `m`-th root `z` of `c⁻¹` rescales `P₀` into the normalized unit
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (c⁻¹) hm0
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm0.ne'] at hz
    exact inv_ne_zero hc0 hz.symm
  -- scalar units are central in `(Module.End ℂ V)ˣ`
  set U : ℂˣ →* (Module.End ℂ V)ˣ :=
    Units.map (algebraMap ℂ (Module.End ℂ V)).toMonoidHom with hUdef
  have hUval : ∀ w : ℂˣ,
      ((U w : (Module.End ℂ V)ˣ) : Module.End ℂ V) = algebraMap ℂ _ (w : ℂ) := fun _ => rfl
  have hUcentral : ∀ (w : ℂˣ) (x : (Module.End ℂ V)ˣ), U w * x = x * U w := fun w x =>
    Units.ext (by
      rw [Units.val_mul, Units.val_mul, hUval]
      exact Algebra.commutes (w : ℂ) (x : Module.End ℂ V))
  refine ⟨U (Units.mk0 z hz0) * P₀, fun h => ?_, ?_⟩
  · -- the intertwining property survives the scalar twist
    calc U (Units.mk0 z hz0) * P₀ * ρ.asGroupHom h
        = U (Units.mk0 z hz0) * (P₀ * ρ.asGroupHom h) := by group
      _ = U (Units.mk0 z hz0) * (ρ.asGroupHom
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P₀) := by rw [hP₀ h]
      _ = U (Units.mk0 z hz0) * ρ.asGroupHom
            (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P₀ := by group
      _ = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h)
            * U (Units.mk0 z hz0) * P₀ := by rw [hUcentral]
      _ = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h)
            * (U (Units.mk0 z hz0) * P₀) := by group
  · -- normalization: `P^t = ρ(g^t)` whenever `g^t ∈ H`
    intro t ht
    obtain ⟨s, rfl⟩ := hdvd t ht
    -- at `t = m`: `P₀^m = R · (c-scalar)`, and the `z`-twist cancels the scalar
    have hT : R⁻¹ * P₀ ^ (m : ℤ) = U (Units.mk0 c hc0) := Units.ext (by
      rw [hUval, hc]
      exact (Module.algebraMap_end_eq_smul_id ℂ ℂ V c).symm)
    have hP₀m : P₀ ^ (m : ℤ) = R * U (Units.mk0 c hc0) := by
      rw [← hT]
      group
    have hUm : U (Units.mk0 z hz0) ^ (m : ℤ) * U (Units.mk0 c hc0) = 1 := by
      rw [← map_zpow, ← map_mul]
      have h3 : Units.mk0 z hz0 ^ (m : ℤ) * Units.mk0 c hc0 = 1 := Units.ext (by
        rw [Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
        change z ^ m * c = 1
        rw [hz, inv_mul_cancel₀ hc0])
      rw [h3, map_one]
    have hmove : U (Units.mk0 z hz0) ^ (m : ℤ) * (R * U (Units.mk0 c hc0))
        = R * (U (Units.mk0 z hz0) ^ (m : ℤ) * U (Units.mk0 c hc0)) := by
      rw [← map_zpow, ← mul_assoc, hUcentral _ R, mul_assoc]
    calc (U (Units.mk0 z hz0) * P₀) ^ ((m : ℤ) * s)
        = ((U (Units.mk0 z hz0) * P₀) ^ (m : ℤ)) ^ s := by rw [zpow_mul]
      _ = (U (Units.mk0 z hz0) ^ (m : ℤ) * P₀ ^ (m : ℤ)) ^ s := by
          rw [Commute.mul_zpow (hUcentral (Units.mk0 z hz0) P₀)]
      _ = (U (Units.mk0 z hz0) ^ (m : ℤ) * (R * U (Units.mk0 c hc0))) ^ s := by rw [hP₀m]
      _ = (R * (U (Units.mk0 z hz0) ^ (m : ℤ) * U (Units.mk0 c hc0))) ^ s := by rw [hmove]
      _ = R ^ s := by rw [hUm, mul_one]
      _ = ρ.asGroupHom ((⟨g ^ m, hgm⟩ : ↥H) ^ s) := by rw [hR, ← map_zpow]
      _ = ρ.asGroupHom ⟨g ^ ((m : ℤ) * s), ht⟩ := by
          congr 1
          apply Subtype.ext
          rw [SubgroupClass.coe_zpow]
          change ((g ^ m : K)) ^ s = g ^ ((m : ℤ) * s)
          rw [← zpow_natCast g m, ← zpow_mul]

end Normalization

end OddOrder.RepresentationTheory
