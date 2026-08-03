/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.DirectSum.LinearMap
import OddOrder.Algebra.EigenspaceDecomposition
import OddOrder.GroupTheory.PRegularElement
import OddOrder.GroupTheory.RepresentationTheory.Modular.SplittingSystem

/-!
# Brauer characters

Let `𝒪` be a `p`-modular system with residue field `k`, splitting for `n`, and let `V` be a
finite-dimensional `k`-representation of a group `G`.  For an element `g` acting with
`ρ g ^ n = 1` — in the application, a `p`-regular element of order dividing `n` — the operator
`ρ g` is diagonalisable with eigenvalues among the `n`-th roots of unity of `k`
(`EigenspaceDecomposition`).  The **Brauer character** replaces each eigenvalue by its unique
lift to `𝒪` and adds them up with multiplicity:

`φ_V(g) = ∑_{ζ ∈ μ_n(k)} dim_k V_ζ · ζ̂`.

Unlike the naive trace in characteristic `p`, this lands in characteristic `0` and so can be
compared with ordinary characters.  The two facts that pin the definition down are
`brauerCharacter_one` (`φ_V(1) = dim_k V`) and `residue_brauerCharacter`
(`φ_V(g) reduces to the ordinary trace of ρ g`); the latter says the Brauer character is a
genuine lift of the Brauer-trace, not an unrelated formula.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.rootLift` — the unique `n`-th root of unity of `𝒪`
  over a given one of `k`, as a total function
* `OddOrder.RepresentationTheory.Modular.brauerCharacter`

## Main results

* `rootLift_unique`, `rootLift_one` — the lift is characterised by its residue
* `brauerCharacter_one` — the value at `1` is the dimension
* `brauerCharacter_conj` — Brauer characters are class functions
* `residue_brauerCharacter` — reduction is the ordinary trace
* `brauerCharacter_quotient_add_subrepresentation` — additivity in short exact sequences
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Polynomial Module.End

/-! ### Lifting roots of unity as a total function -/

section RootLift

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]

open Classical in
/-- The `n`-th root of unity of `𝒪` lying over a given element of the residue field (and `0`
when there is none).  On `μ_n(k)` — the only place it is used — this is the inverse of the
isomorphism `rootsOfUnityEquivResidue`, packaged as a total function so that it can be applied
inside sums over a `Finset` of the residue field. -/
noncomputable def rootLift (n : ℕ) (c : ResidueField 𝒪) : 𝒪 :=
  if h : ∃ a : 𝒪, a ^ n = 1 ∧ residue 𝒪 a = c then h.choose else 0

variable {n : ℕ} (hn : ¬ p ∣ n) (hn0 : n ≠ 0)
include hn hn0

/-- On an `n`-th root of unity of the residue field, `rootLift` is an `n`-th root of unity of
`𝒪` with the prescribed residue. -/
theorem rootLift_spec {c : ResidueField 𝒪} (hc : c ^ n = 1) :
    (rootLift (𝒪 := 𝒪) n c) ^ n = 1 ∧ residue 𝒪 (rootLift (𝒪 := 𝒪) n c) = c := by
  classical
  have hex : ∃ a : 𝒪, a ^ n = 1 ∧ residue 𝒪 a = c :=
    exists_pow_eq_one_residue_eq (isUnit_natCast_of_not_dvd (p := p) hn) hn0 hc
  rw [rootLift, dif_pos hex]
  exact hex.choose_spec

theorem rootLift_pow_eq_one {c : ResidueField 𝒪} (hc : c ^ n = 1) :
    (rootLift (𝒪 := 𝒪) n c) ^ n = 1 := (rootLift_spec hn hn0 hc).1

theorem residue_rootLift {c : ResidueField 𝒪} (hc : c ^ n = 1) :
    residue 𝒪 (rootLift (𝒪 := 𝒪) n c) = c := (rootLift_spec hn hn0 hc).2

/-- **`rootLift` is *the* lift**: any `n`-th root of unity of `𝒪` is recovered from its
residue.  This is uniqueness in `RootsOfUnityLift`. -/
theorem rootLift_unique {a : 𝒪} (ha : a ^ n = 1) : rootLift n (residue 𝒪 a) = a := by
  have hres : (residue 𝒪 a) ^ n = 1 := by rw [← map_pow, ha, map_one]
  obtain ⟨h1, h2⟩ := rootLift_spec (p := p) hn hn0 hres
  exact eq_of_pow_eq_one_of_sub_mem (isUnit_natCast_of_not_dvd (p := p) hn) h1 ha
    ((residue_eq_zero_iff _).mp (by rw [map_sub, h2, sub_self]))

theorem rootLift_one : rootLift (𝒪 := 𝒪) n 1 = 1 := by
  have h := rootLift_unique (p := p) hn hn0 (a := (1 : 𝒪)) (one_pow n)
  rwa [map_one] at h

end RootLift

/-! ### The Brauer character -/

section BrauerCharacter

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ResidueField 𝒪) V]

/-- The **Brauer character** of a `k`-representation at an element: the eigenvalues of `ρ g`,
lifted from the residue field `k` to `𝒪`, added up with multiplicity.  It is the right notion
only when `ρ g ^ n = 1`; otherwise the eigenvalues are not `n`-th roots of unity and the sum
below misses part of `V`. -/
noncomputable def brauerCharacter (n : ℕ) (ρ : Representation (ResidueField 𝒪) G V) (g : G) :
    𝒪 :=
  ∑ ζ ∈ nthRootsFinset n (1 : ResidueField 𝒪),
    Module.finrank (ResidueField 𝒪) (Module.End.eigenspace (ρ g) ζ) • rootLift n ζ

variable {n : ℕ} (ρ : Representation (ResidueField 𝒪) G V)

/-- **Brauer characters are class functions.**  Conjugating `ρ g` by the invertible operator
`ρ h` carries eigenspaces to eigenspaces, so every multiplicity is unchanged. -/
theorem brauerCharacter_conj (g h : G) :
    brauerCharacter (𝒪 := 𝒪) n ρ (h * g * h⁻¹) = brauerCharacter (𝒪 := 𝒪) n ρ g := by
  have hinv : ∀ v : V, (ρ h⁻¹) ((ρ h) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have hinv' : ∀ v : V, (ρ h) ((ρ h⁻¹) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hconj : ∀ v : V, (ρ (h * g * h⁻¹)) ((ρ h) v) = (ρ h) ((ρ g) v) := fun v => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hinv]
  let e : V ≃ₗ[ResidueField 𝒪] V :=
    { ρ h with invFun := ρ h⁻¹, left_inv := hinv, right_inv := hinv' }
  refine Finset.sum_congr rfl fun ζ _ => ?_
  congr 1
  have hmap : Submodule.map (e : V →ₗ[ResidueField 𝒪] V) (Module.End.eigenspace (ρ g) ζ)
      = Module.End.eigenspace (ρ (h * g * h⁻¹)) ζ := by
    refine le_antisymm ?_ fun w hw => ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    · rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, mem_eigenspace_iff] at hv
      rw [mem_eigenspace_iff]
      change (ρ (h * g * h⁻¹)) ((ρ h) v) = ζ • (ρ h) v
      rw [hconj, hv, map_smul]
    · rw [mem_eigenspace_iff] at hw
      rw [SetLike.mem_coe, mem_eigenspace_iff]
      change (ρ g) ((ρ h⁻¹) w) = ζ • (ρ h⁻¹) w
      have key : (ρ h) ((ρ g) ((ρ h⁻¹) w)) = ζ • w := by
        rw [← hconj ((ρ h⁻¹) w), hinv' w]; exact hw
      have h2 := congrArg (fun x : V => (ρ h⁻¹) x) key
      simp only [hinv, map_smul] at h2
      exact h2
  rw [← hmap, LinearEquiv.finrank_map_eq]

variable (hn : ¬ p ∣ n) (hn0 : 0 < n)
include hn hn0

omit [IsPModularSystem p 𝒪] hn in
/-- **Brauer characters are additive in short exact sequences.**  For a `G`-invariant subspace
`W ≤ V`, the Brauer character of `V` is the sum of those of `V ⧸ W` and of `W`.

This is what makes a Brauer character depend only on the composition factors of the module, and
hence what makes the decomposition matrix well defined.  The proof is the eigenvalue-by-
eigenvalue dimension count `finrank_eigenspace_eq_quotient_add`. -/
theorem brauerCharacter_quotient_add_subrepresentation [FiniteDimensional (ResidueField 𝒪) V]
    (W : Submodule (ResidueField 𝒪) V) (hW : ∀ g : G, W ≤ W.comap (ρ g))
    {ω : ResidueField 𝒪} (hω : IsPrimitiveRoot ω n) {g : G} (hg : (ρ g) ^ n = 1) :
    brauerCharacter (𝒪 := 𝒪) n ρ g
      = brauerCharacter (𝒪 := 𝒪) n (ρ.quotient W hW) g
        + brauerCharacter (𝒪 := 𝒪) n (ρ.subrepresentation W hW) g := by
  classical
  rw [brauerCharacter, brauerCharacter, brauerCharacter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ζ hζ => ?_
  rw [OddOrder.finrank_eigenspace_eq_quotient_add (hW g) hn0 hω hg hζ, add_nsmul]
  rfl


/-- **The Brauer character at the identity is the dimension.** -/
theorem brauerCharacter_one :
    brauerCharacter (𝒪 := 𝒪) n ρ 1 = (Module.finrank (ResidueField 𝒪) V : 𝒪) := by
  classical
  have hρ : ρ 1 = 1 := map_one ρ
  have hother : ∀ ζ ∈ nthRootsFinset n (1 : ResidueField 𝒪), ζ ≠ 1 →
      Module.finrank (ResidueField 𝒪) (Module.End.eigenspace (ρ (1 : G)) ζ) • rootLift n ζ
        = 0 := by
    intro ζ _ hζ
    have hbot : Module.End.eigenspace (ρ (1 : G)) ζ = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
      rw [mem_eigenspace_iff, hρ] at hv
      have hzero : (1 - ζ) • v = 0 := by
        rw [sub_smul, one_smul, ← hv]
        simp
      rcases smul_eq_zero.mp hzero with hc | hc
      · exact absurd (by linear_combination -hc : ζ = 1) hζ
      · exact hc
    rw [hbot, finrank_bot, zero_smul]
  rw [brauerCharacter,
    Finset.sum_eq_single (1 : ResidueField 𝒪) hother
      (fun hc => absurd (one_mem_nthRootsFinset hn0) hc)]
  have htop : Module.End.eigenspace (ρ (1 : G)) 1 = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun v => ?_
    rw [mem_eigenspace_iff, hρ, one_smul]
    rfl
  rw [htop, finrank_top, rootLift_one hn hn0.ne', nsmul_eq_mul, mul_one]

/-- **The Brauer character is a lift of the ordinary trace.**  Reducing `φ_V(g)` modulo the
maximal ideal of `𝒪` returns the trace of `ρ g` computed in characteristic `p`.

This is what makes the definition the right one: the Brauer character carries exactly the
information of the modular trace, but recorded in characteristic `0` where it can be compared
with ordinary characters. -/
theorem residue_brauerCharacter [FiniteDimensional (ResidueField 𝒪) V]
    {ω : ResidueField 𝒪} (hω : IsPrimitiveRoot ω n) {g : G} (hg : (ρ g) ^ n = 1) :
    residue 𝒪 (brauerCharacter (𝒪 := 𝒪) n ρ g)
      = LinearMap.trace (ResidueField 𝒪) V (ρ g) := by
  classical
  -- Reduction turns each lifted eigenvalue back into the eigenvalue.
  have hres : residue 𝒪 (brauerCharacter (𝒪 := 𝒪) n ρ g)
      = ∑ ζ ∈ nthRootsFinset n (1 : ResidueField 𝒪),
          Module.finrank (ResidueField 𝒪) (Module.End.eigenspace (ρ g) ζ) • ζ := by
    rw [brauerCharacter, map_sum]
    refine Finset.sum_congr rfl fun ζ hζ => ?_
    rw [map_nsmul, residue_rootLift hn hn0.ne' ((mem_nthRootsFinset hn0 _).mp hζ)]
  -- The trace splits over the eigenspace decomposition, and on each piece it is `dim · ζ`.
  have hmaps : ∀ ζ : nthRootsFinset n (1 : ResidueField 𝒪),
      Set.MapsTo (ρ g) (Module.End.eigenspace (ρ g) (ζ : ResidueField 𝒪))
        (Module.End.eigenspace (ρ g) (ζ : ResidueField 𝒪)) := by
    intro ζ v hv
    rw [SetLike.mem_coe, mem_eigenspace_iff] at hv ⊢
    rw [hv, map_smul, hv]
  have hrestrict : ∀ ζ : nthRootsFinset n (1 : ResidueField 𝒪),
      LinearMap.trace (ResidueField 𝒪) _ ((ρ g).restrict (hmaps ζ))
        = Module.finrank (ResidueField 𝒪)
            (Module.End.eigenspace (ρ g) (ζ : ResidueField 𝒪)) • (ζ : ResidueField 𝒪) := by
    intro ζ
    have hid : (ρ g).restrict (hmaps ζ) = (ζ : ResidueField 𝒪) • LinearMap.id := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      have hv := v.2
      rw [mem_eigenspace_iff] at hv
      simpa [LinearMap.restrict_apply] using hv
    rw [hid, map_smul, LinearMap.trace_id, smul_eq_mul, nsmul_eq_mul]
    exact mul_comm _ _
  rw [hres, LinearMap.trace_eq_sum_trace_restrict
    (isInternal_eigenspace_of_pow hn0 hω hg) hmaps]
  simp only [hrestrict, Finset.univ_eq_attach]
  exact (Finset.sum_attach (nthRootsFinset n (1 : ResidueField 𝒪))
    (fun ζ => Module.finrank (ResidueField 𝒪) (Module.End.eigenspace (ρ g) ζ) • ζ)).symm

end BrauerCharacter

/-! ### `p`-regular elements of a finite group

Brauer characters of a finite group `G` are taken at the exponent `n = |G|_{p'}`
(`pRegularExponent`): every `p`-regular element has order dividing it, so no hypothesis on
`ρ g` has to be carried around. -/

section PRegular

open OddOrder.GroupTheory

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ResidueField 𝒪) V]
variable (ρ : Representation (ResidueField 𝒪) G V)

omit [IsPModularSystem p 𝒪] [Finite G] in
/-- A `p`-regular element acts with `ρ g ^ |G|_{p'} = 1`, so its eigenvalues are `|G|_{p'}`-th
roots of unity — exactly the hypothesis the Brauer character needs. -/
theorem rep_pow_pRegularExponent_eq_one (hp : p.Prime) {g : G} (hg : IsPRegular p g) :
    (ρ g) ^ pRegularExponent p G = 1 := by
  rw [← map_pow, pow_pRegularExponent_eq_one hp hg, map_one]

/-- **Reduction of the Brauer character at a `p`-regular element is the ordinary trace.**
Unlike `residue_brauerCharacter` this carries no hypothesis on `ρ g`: `p`-regularity of `g`
supplies it. -/
theorem residue_brauerCharacter_of_isPRegular [FiniteDimensional (ResidueField 𝒪) V]
    (hp : p.Prime) {ω : ResidueField 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {g : G} (hg : IsPRegular p g) :
    residue 𝒪 (brauerCharacter (𝒪 := 𝒪) (pRegularExponent p G) ρ g)
      = LinearMap.trace (ResidueField 𝒪) V (ρ g) :=
  residue_brauerCharacter (hn := not_dvd_pRegularExponent hp) (hn0 := pRegularExponent_pos)
    (ρ := ρ) (hω := hω) (hg := rep_pow_pRegularExponent_eq_one ρ hp hg)

/-- The Brauer character of a finite group at the identity is the dimension. -/
theorem brauerCharacter_pRegularExponent_one (hp : p.Prime) :
    brauerCharacter (𝒪 := 𝒪) (pRegularExponent p G) ρ 1
      = (Module.finrank (ResidueField 𝒪) V : 𝒪) :=
  brauerCharacter_one (hn := not_dvd_pRegularExponent hp) (hn0 := pRegularExponent_pos) (ρ := ρ)

end PRegular

end OddOrder.RepresentationTheory.Modular
