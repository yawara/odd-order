/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Index
import OddOrder.GroupTheory.RepresentationTheory.CharacterConjugate
import OddOrder.GroupTheory.RepresentationTheory.ZIrr

/-!
# Schur's center bound: `χ(1)² ≤ |G : Z|`

This module formalizes **Isaacs, _Character Theory of Finite Groups_ (Academic Press, 1976),
Corollary 2.30**: if `χ` is an irreducible character of a finite group `G` and `Z` is a subgroup
of the center `Z(G)`, then `χ(1)² ≤ |G : Z|`.

The argument is the standard one.  By Schur's lemma over `ℂ`, every central element acts as a
scalar, so for `z ∈ Z` the matrix `ρ z` is `c • id` and hence `|χ(z)|² = χ(z)·χ(z⁻¹) = χ(1)²`
(the scalars at `z` and `z⁻¹` are inverse to each other).  Summing over `Z` and bounding by the
full sum over `G` (each summand `χ(g)·χ(g⁻¹) = ‖χ(g)‖² ≥ 0`), the first orthogonality relation
`∑_{g∈G} χ(g)·χ(g⁻¹) = |G|` gives `χ(1)²·|Z| ≤ |G| = |G:Z|·|Z|`, whence `χ(1)² ≤ |G:Z|`.

## Main results

* `OddOrder.RepresentationTheory.finrank_sq_le_index` — for an irreducible finite-dimensional
  complex representation `ρ` of `G` and `Z ≤ Z(G)`, `(finrank ℂ V)² ≤ Z.index`.
  Here `finrank ℂ V = χ(1)`.

## Usage (Peterfalvi)

Peterfalvi invokes [Is] Cor 2.30 repeatedly: §3 (1.8) (`Z = D`, `G = C`), §8 (6.6)/(6.8.3)
(`Z = Z(K)`, `Z = Z(H)`), and §9 (Feit–Sibley).  All applications take the form
`χ(1)² ≤ |C : Z|` for an irreducible `χ` whose kernel contains a subgroup mapping `Z` into the
center of the relevant quotient.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Academic Press 1976, Corollary 2.30.
* Peterfalvi §1 (1.8); §6 (6.6)–(6.8); §9.
-/

namespace OddOrder.RepresentationTheory

open scoped ComplexOrder
open Module Representation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **Schur's lemma over `ℂ`.** A central element of `G` acts on an irreducible representation as
a scalar: for `g ∈ Z(G)` there is `c : ℂ` with `ρ g = c • LinearMap.id`. -/
theorem exists_central_scalar (ρ : Representation ℂ G V) [IsIrreducible ρ]
    {g : G} (hg : g ∈ Subgroup.center G) :
    ∃ c : ℂ, ρ g = c • LinearMap.id := by
  have hgc : g ∈ Submonoid.center G :=
    Submonoid.mem_center_iff.mpr (Subgroup.mem_center_iff.mp hg)
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 (IntertwiningMap.centralMul ρ g hgc)
  refine ⟨c, ?_⟩
  have hlin := congrArg IntertwiningMap.toLinearMap hc
  rw [IntertwiningMap.algebraMap_apply, IntertwiningMap.toLinearMap_smul,
    show (1 : IntertwiningMap ρ ρ).toLinearMap = LinearMap.id from rfl] at hlin
  exact hlin.symm

/-- For a central element `z`, the product `χ(z)·χ(z⁻¹)` equals `χ(1)² = (finrank ℂ V)²`.

`ρ z = c • id` and `ρ z⁻¹ = c' • id` with `c·c' = 1` (since `ρ z · ρ z⁻¹ = id`), so
`χ(z)·χ(z⁻¹) = (n·c)(n·c') = n²`. -/
theorem char_mul_char_inv_of_mem_center_complex [Finite G] (ρ : Representation ℂ G V) [IsIrreducible ρ]
    {z : G} (hz : z ∈ Subgroup.center G) :
    ρ.character z * ρ.character z⁻¹ = (finrank ℂ V : ℂ) ^ 2 := by
  obtain ⟨c, hc⟩ := exists_central_scalar ρ hz
  obtain ⟨c', hc'⟩ := exists_central_scalar ρ (Subgroup.inv_mem _ hz)
  -- `V` is nontrivial because `ρ` is irreducible (`Subrepresentation ρ` is a simple, hence
  -- nontrivial, order, and `toSubmodule` is injective into `Submodule ℂ V`).
  haveI : Nontrivial V := by
    haveI h1 : Nontrivial (Subrepresentation ρ) := IsSimpleOrder.toNontrivial
    have h2 : Nontrivial (Submodule ℂ V) :=
      (Subrepresentation.toSubmodule_injective (ρ := ρ)).nontrivial
    exact (Submodule.nontrivial_iff ℂ).mp h2
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  -- `c * c' = 1` from `ρ z ∘ ρ z⁻¹ = ρ 1 = id` evaluated at `v`.
  have hmul : ρ z (ρ z⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hc, hc'] at hmul
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul] at hmul
  have hcc' : c * c' = 1 :=
    smul_left_injective ℂ hv (by change (c * c') • v = (1 : ℂ) • v; rw [hmul, one_smul])
  -- character values: `χ(z) = n·c`, `χ(z⁻¹) = n·c'`.
  have hchz : ρ.character z = (finrank ℂ V : ℂ) * c := by
    rw [Representation.character, hc, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]
  have hchz' : ρ.character z⁻¹ = (finrank ℂ V : ℂ) * c' := by
    rw [Representation.character, hc', map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]
  rw [hchz, hchz']
  ring_nf
  rw [mul_assoc, hcc', mul_one]

/-- The product `χ(g)·χ(g⁻¹)` is the squared norm of `χ(g)`, as a complex number.
This is `χ(g) · conj(χ(g))` via `character_inv`. -/
theorem char_mul_char_inv_eq_normSq [Finite G] (ρ : Representation ℂ G V) (g : G) :
    ρ.character g * ρ.character g⁻¹ = (Complex.normSq (ρ.character g) : ℂ) := by
  rw [character_inv ρ g, Complex.star_def, Complex.mul_conj]

/-- For a central `z`, the real number `‖χ(z)‖²` equals `χ(1)² = (finrank ℂ V)²`. -/
theorem normSq_char_of_mem_center [Finite G] (ρ : Representation ℂ G V) [IsIrreducible ρ]
    {z : G} (hz : z ∈ Subgroup.center G) :
    Complex.normSq (ρ.character z) = (finrank ℂ V : ℝ) ^ 2 := by
  have h := char_mul_char_inv_of_mem_center_complex ρ hz
  rw [char_mul_char_inv_eq_normSq] at h
  have : (Complex.normSq (ρ.character z) : ℂ) = (((finrank ℂ V : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [h]; push_cast; ring
  exact_mod_cast this

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- The full first-orthogonality sum: `∑_{g∈G} ‖χ(g)‖² = |G|` (as a real number).

This is `char_orthonormal` for `ρ = ρ`, repackaged with real squared norms. -/
theorem sum_normSq_char_eq_card (ρ : Representation ℂ G V) [IsIrreducible ρ] :
    ∑ g : G, Complex.normSq (ρ.character g) = (Nat.card G : ℝ) := by
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    have := ‹Invertible (Nat.card G : ℂ)›
    exact Invertible.ne_zero _
  -- `char_orthonormal` (ρ = ρ): `(|G|)⁻¹ * ∑ χ g · χ g⁻¹ = 1`.
  have horth := ρ.char_orthonormal (σ := ρ)
  rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at horth
  -- so `∑ χ g · χ g⁻¹ = |G|`
  have hsumC : ∑ g : G, ρ.character g * ρ.character g⁻¹ = (Nat.card G : ℂ) := by
    have h : (Nat.card G : ℂ) * ((Nat.card G : ℂ)⁻¹ *
        ∑ g : G, ρ.character g * ρ.character g⁻¹) = (Nat.card G : ℂ) * 1 := by
      rw [horth]
    rwa [← mul_assoc, mul_inv_cancel₀ hcard, one_mul, mul_one] at h
  -- rewrite each summand as the squared norm
  have hcast : (↑(∑ g : G, Complex.normSq (ρ.character g)) : ℂ) = (Nat.card G : ℂ) := by
    push_cast
    rw [← hsumC]
    exact Finset.sum_congr rfl fun g _ => (char_mul_char_inv_eq_normSq ρ g).symm
  exact_mod_cast hcast

set_option linter.unusedFintypeInType false in
/-- **Isaacs, Character Theory of Finite Groups, Corollary 2.30.**

Let `ρ` be a finite-dimensional irreducible complex representation of a finite group `G`, with
character `χ` (so `χ(1) = finrank ℂ V`).  If `Z` is a subgroup of the center `Z(G)`, then
`χ(1)² ≤ |G : Z|`.

`[Fintype G]` is used in the proof (summation over `G` and over the subgroup `Z`) even though it
does not appear in the statement type. -/
theorem finrank_sq_le_index (ρ : Representation ℂ G V) [IsIrreducible ρ]
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) :
    finrank ℂ V ^ 2 ≤ Z.index := by
  classical
  set n := finrank ℂ V with hn
  set s : Finset G := (Z : Set G).toFinset with hs
  have hcard_s : s.card = Nat.card Z := by
    rw [hs, Set.toFinset_card, Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.refl _)
  -- partial sum over `Z` equals `n² · |Z|`
  have hZsum : ∑ z ∈ s, Complex.normSq (ρ.character z) = (n : ℝ) ^ 2 * (Nat.card Z : ℝ) := by
    have hmem : ∀ z ∈ s, z ∈ Subgroup.center G := by
      intro z hz
      exact hZ (by simpa [hs, Set.mem_toFinset] using hz)
    rw [Finset.sum_congr rfl (fun z hz => normSq_char_of_mem_center ρ (hmem z hz)),
      Finset.sum_const, nsmul_eq_mul, mul_comm, hcard_s]
  -- `s ⊆ univ` and the summands are nonneg, so partial ≤ full = |G|
  have hle : ∑ z ∈ s, Complex.normSq (ρ.character z) ≤ (Nat.card G : ℝ) := by
    rw [← sum_normSq_char_eq_card ρ]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun g _ _ => Complex.normSq_nonneg _)
  rw [hZsum] at hle
  -- so `n² · |Z| ≤ |G|` in ℝ; push to ℕ.
  have hleN : n ^ 2 * Nat.card Z ≤ Nat.card G := by
    have hR : ((n ^ 2 * Nat.card Z : ℕ) : ℝ) ≤ ((Nat.card G : ℕ) : ℝ) := by
      push_cast
      exact hle
    exact_mod_cast hR
  -- `|G| = |G:Z| · |Z|`, cancel `|Z| > 0`.
  have hcardZ : 0 < Nat.card Z := Nat.card_pos
  rw [← Z.index_mul_card] at hleN
  exact Nat.le_of_mul_le_mul_right hleN hcardZ

set_option linter.unusedFintypeInType false in
/-- **Isaacs Corollary 2.30, character form.**  For an irreducible character `φ` of a finite
group `G` and a subgroup `Z` of the center, the degree `φ(1)` is a natural number `d` with
`d² ≤ |G : Z|`.

This is the form invoked in Peterfalvi (§1 (1.8), §6 (6.6)–(6.8), §9): `φ(1)² ≤ |C : Z|`.  The
degree `φ(1)` is returned as an explicit natural `d` together with the witness `φ(1) = d`. -/
theorem IsIrreducibleCharacter.exists_degree_sq_le_index {φ : ClassFunction G ℂ}
    (hφ : IsIrreducibleCharacter φ) (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) :
    ∃ d : ℕ, (φ : G → ℂ) 1 = (d : ℂ) ∧ d ^ 2 ≤ Z.index := by
  obtain ⟨W, _, _, _, ρ, hρ, hcoe⟩ := hφ
  haveI : Representation.IsIrreducible ρ := hρ
  refine ⟨finrank ℂ W, ?_, finrank_sq_le_index ρ Z hZ⟩
  rw [congrFun hcoe 1, ρ.char_one]

/-! ### Central restriction ([Is] Lemma 2.27) -/

section CentralRestriction

/-- Any representation of a group on the one-dimensional space `ℂ` is irreducible:
the only `ℂ`-submodules of `ℂ` are `⊥` and `⊤`. -/
theorem isIrreducible_complex_rep {H : Type*} [Group H] (ρ : Representation ℂ H ℂ) :
    ρ.IsIrreducible := by
  have hsub : ∀ S : Submodule ℂ ℂ, S = ⊥ ∨ S = ⊤ := by
    intro S
    by_cases hbot : S = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      rw [Submodule.eq_top_iff']
      intro y
      have hy : y = (y / x) • x := by
        rw [smul_eq_mul]
        field_simp
      rw [hy]
      exact S.smul_mem _ hx
  refine { toNontrivial := ?_, eq_bot_or_eq_top := fun S' => ?_ }
  · refine ⟨⊥, ⊤, fun h => ?_⟩
    have hbt : (⊥ : Submodule ℂ ℂ) = ⊤ := congrArg Subrepresentation.toSubmodule h
    have h1 : (1 : ℂ) ∈ (⊥ : Submodule ℂ ℂ) := by rw [hbt]; trivial
    exact one_ne_zero ((Submodule.mem_bot ℂ).mp h1)
  · rcases hsub S'.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

/-- **Isaacs, Character Theory of Finite Groups, Lemma 2.27 (central restriction).**

Let `χ` be an irreducible (complex) character of `G` and let `Z ≤ Z(G)`.  There is a
**linear** character `φ` of `Z` — an irreducible character with `φ(1) = 1` — such that
`Res_Z χ = χ(1) • φ`; pointwise, `χ(z) = φ(z) · χ(1)` for all `z ∈ Z`.

By Schur's lemma each central `z` acts on a witnessing irreducible representation as a
scalar `φ(z)`, and the scalars form the linear character.  This is the decomposition behind
Peterfalvi (6.8.2.3): `Res^H_Z θ = a·φ` with `a = θ(1)`, `φ ∈ Irr Z`, and `φ ≠ 1_Z`
whenever `Z ⊄ ker θ` (which follows from the pointwise formula since `χ(1) ≠ 0`). -/
theorem IsIrreducibleCharacter.exists_central_linear_restriction
    {G : Type*} [Group G] {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ)
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) :
    ∃ φ : ClassFunction (↥Z) ℂ, IsIrreducibleCharacter φ ∧ φ 1 = 1 ∧
      ClassFunction.restrict Z χ = χ 1 • φ ∧
      ∀ z : ↥Z, χ (z : G) = φ z * χ 1 := by
  classical
  obtain ⟨W, _, _, _, ρ, hirr, hchar⟩ := hχ
  haveI : Representation.IsIrreducible ρ := hirr
  haveI := nontrivial_of_isIrreducible ρ
  -- the central scalar function from Schur's lemma
  choose c hc using fun z : ↥Z => exists_central_scalar ρ (hZ z.2)
  have huniq : ∀ {c₁ c₂ : ℂ}, (c₁ • LinearMap.id : W →ₗ[ℂ] W) = c₂ • LinearMap.id →
      c₁ = c₂ := by
    intro c₁ c₂ h
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have happ := congrArg (fun f : W →ₗ[ℂ] W => f w) h
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at happ
    exact smul_left_injective ℂ hw happ
  have hcmul : ∀ z₁ z₂ : ↥Z, c (z₁ * z₂) = c z₁ * c z₂ := by
    intro z₁ z₂
    apply huniq
    rw [← hc (z₁ * z₂), show ((z₁ * z₂ : ↥Z) : G) = (z₁ : G) * (z₂ : G) from rfl,
      map_mul, hc z₁, hc z₂]
    ext w
    simp [Module.End.mul_apply, smul_smul, mul_comm]
  have hcone : c 1 = 1 := by
    apply huniq
    rw [← hc 1, show ((1 : ↥Z) : G) = 1 from rfl, map_one]
    ext w
    simp [Module.End.one_apply]
  -- character values: `χ(z) = c z · χ(1)`
  have hχ1 : χ 1 = (finrank ℂ W : ℂ) := by
    rw [show χ 1 = (χ : G → ℂ) 1 from rfl, congrFun hchar 1, ρ.char_one]
  have hval : ∀ z : ↥Z, χ (z : G) = c z * χ 1 := by
    intro z
    rw [show χ (z : G) = (χ : G → ℂ) (z : G) from rfl, congrFun hchar (z : G), hχ1]
    change LinearMap.trace ℂ W (ρ (z : G)) = _
    rw [hc z, map_smul, LinearMap.trace_id]
    simp [smul_eq_mul]
  -- elements of `Z` are central, so any function on `Z` is a class function
  have hcomm : ∀ z₁ z₂ : ↥Z, z₂ * z₁ * z₂⁻¹ = z₁ := by
    intro z₁ z₂
    apply Subtype.ext
    change (z₂ : G) * (z₁ : G) * (z₂ : G)⁻¹ = (z₁ : G)
    rw [(Subgroup.mem_center_iff.mp (hZ z₂.2) (z₁ : G)).symm]
    group
  refine ⟨⟨fun z => c z, fun z₁ z₂ => by rw [hcomm]⟩, ?_, hcone, ?_, fun z => hval z⟩
  · -- the witnessing one-dimensional representation `z ↦ c z • id`
    refine ⟨ℂ, inferInstance, inferInstance, inferInstance,
      { toFun := fun z => c z • LinearMap.id
        map_one' := by
          rw [hcone]
          ext
          simp [Module.End.one_apply]
        map_mul' := fun z₁ z₂ => by
          rw [hcmul]
          ext
          simp [Module.End.mul_apply, smul_smul, mul_comm] },
      isIrreducible_complex_rep _, ?_⟩
    funext z
    change c z = LinearMap.trace ℂ ℂ (c z • LinearMap.id)
    rw [map_smul, LinearMap.trace_id]
    simp
  · -- `Res_Z χ = χ(1) • φ`
    ext z
    rw [ClassFunction.restrict_apply, hval z, ClassFunction.smul_apply]
    change c z * χ 1 = χ 1 * c z
    ring

end CentralRestriction

end OddOrder.RepresentationTheory
