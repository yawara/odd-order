/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OddOrder.GroupTheory.RepresentationTheory.Modular.LatticeEigenspaces

/-!
# Reduction of an `𝒪`-lattice modulo the maximal ideal

The decomposition map compares an `𝒪`-lattice `L` with its reduction `k ⊗[𝒪] L`, where
`k = ResidueField 𝒪`.  This file sets that comparison up:

* an endomorphism of finite order stays of finite order after reduction
  (`Module.End.baseChangeHom` is an algebra map);
* the reduction of a `ζ`-eigen-submodule lands inside the `ζ̄`-eigenspace of the reduced
  operator.

Together with `LatticeEigenspaces` — where the trace over `𝒪` is already written in
Brauer-character shape, and reduction is a bijection `μ_n(𝒪) → μ_n(k)` — what remains for the
decomposition-map identity is that these containments are equalities on dimensions.

## Main results

* `OddOrder.RepresentationTheory.Modular.baseChange_pow_eq_one`
* `OddOrder.RepresentationTheory.Modular.baseChange_eigenspace_le`
* `OddOrder.RepresentationTheory.Modular.finrank_baseChange_eigenspace`
* `OddOrder.RepresentationTheory.Modular.trace_eq_sum_finrank_baseChange_eigenspace` — the
  decomposition-map identity at the level of operators
* `OddOrder.RepresentationTheory.Modular.reduction` and
  `OddOrder.RepresentationTheory.Modular.trace_eq_brauerCharacter_reduction` — the same
  identity for representations
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Polynomial TensorProduct

variable {𝒪 : Type*} [CommRing 𝒪]
variable {L : Type*} [AddCommGroup L] [Module 𝒪 L]

/-- Reduction preserves the order of an endomorphism: base change is an algebra map. -/
theorem baseChange_pow_eq_one [IsLocalRing 𝒪] {A : Module.End 𝒪 L} {n : ℕ} (hA : A ^ n = 1) :
    (A.baseChange (ResidueField 𝒪)) ^ n = 1 := by
  have h := congrArg (Module.End.baseChangeHom 𝒪 (ResidueField 𝒪) L) hA
  rwa [map_pow, map_one] at h

/-- **The reduction of an eigen-submodule lands in the eigenspace of the reduced operator.**
An eigenvector for `ζ` upstairs reduces to an eigenvector for the residue of `ζ`. -/
theorem baseChange_eigenspace_le [IsLocalRing 𝒪] (A : Module.End 𝒪 L) (ζ : 𝒪) :
    (Module.End.eigenspace A ζ).baseChange (ResidueField 𝒪)
      ≤ Module.End.eigenspace (A.baseChange (ResidueField 𝒪)) (residue 𝒪 ζ) := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
  have hv' : A v = ζ • v := Module.End.mem_eigenspace_iff.mp hv
  change (A.baseChange (ResidueField 𝒪)) ((1 : ResidueField 𝒪) ⊗ₜ[𝒪] v)
    = residue 𝒪 ζ • ((1 : ResidueField 𝒪) ⊗ₜ[𝒪] v)
  rw [LinearMap.baseChange_tmul, hv', TensorProduct.tmul_smul,
    ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]

/-- The reduction of a free eigen-submodule has the same dimension as its rank. -/
theorem finrank_baseChange_eigenspace [IsLocalRing 𝒪] (A : Module.End 𝒪 L) (ζ : 𝒪)
    [Module.Free 𝒪 (Module.End.eigenspace A ζ)] [Module.Finite 𝒪 (Module.End.eigenspace A ζ)] :
    Module.finrank (ResidueField 𝒪) (ResidueField 𝒪 ⊗[𝒪] (Module.End.eigenspace A ζ))
      = Module.finrank 𝒪 (Module.End.eigenspace A ζ) :=
  Module.finrank_baseChange

/-! ### Two counting helpers -/

section Counting

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The dimension of a finite supremum of subspaces is at most the sum of the dimensions.  With
the reverse inequality supplied by a spanning argument this pins each summand down. -/
theorem finrank_biSup_le_sum {ι : Type*} (t : Finset ι) (q : ι → Submodule K W) :
    Module.finrank K ↥(⨆ i ∈ t, q i) ≤ ∑ i ∈ t, Module.finrank K (q i) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    have hins : (⨆ i ∈ insert a t, q i) = q a ⊔ ⨆ i ∈ t, q i := by
      simp only [Finset.mem_insert, iSup_or, iSup_sup_eq, iSup_iSup_eq_left]
    rw [Finset.sum_insert ha, hins]
    refine le_trans ?_ (Nat.add_le_add_left ih _)
    have h := Submodule.finrank_sup_add_finrank_inf_eq (q a) (⨆ i ∈ t, q i)
    omega

end Counting

/-! ### Base change and suprema -/

section BaseChangeSup

variable (k : Type*) [Field k] [Algebra 𝒪 k]

/-- Base change of a supremum of submodules is contained in the supremum of the base changes. -/
theorem baseChange_iSup_le {ι : Sort*} (N : ι → Submodule 𝒪 L) :
    (⨆ i, N i).baseChange k ≤ ⨆ i, (N i).baseChange k := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  induction hv using Submodule.iSup_induction' with
  | mem i x hx =>
    exact Submodule.mem_iSup_of_mem i (Submodule.tmul_mem_baseChange_of_mem 1 hx)
  | zero => simp
  | add x y _ _ hx hy =>
    have : (TensorProduct.mk 𝒪 k L 1) (x + y)
        = (TensorProduct.mk 𝒪 k L 1) x + (TensorProduct.mk 𝒪 k L 1) y := map_add _ _ _
    rw [SetLike.mem_coe] at hx hy ⊢
    rw [this]
    exact Submodule.add_mem _ hx hy

/-- If a family of submodules spans, so do their base changes. -/
theorem iSup_baseChange_eq_top {ι : Sort*} {N : ι → Submodule 𝒪 L} (hN : ⨆ i, N i = ⊤) :
    ⨆ i, (N i).baseChange k = ⊤ :=
  eq_top_iff.mpr (by
    rw [← Submodule.baseChange_top (A := k) (M := L), ← hN]
    exact baseChange_iSup_le k N)

/-- The `Finset`-indexed form of `iSup_baseChange_eq_top`. -/
theorem iSup_baseChange_biSup_eq_top {ι : Type*} (t : Finset ι) (N : ι → Submodule 𝒪 L)
    (hN : (⨆ i ∈ t, N i) = ⊤) : (⨆ i ∈ t, (N i).baseChange k) = ⊤ :=
  eq_top_iff.mpr <| by
    rw [← Submodule.baseChange_top (A := k) (M := L), ← hN]
    exact le_trans (baseChange_iSup_le k _)
      (iSup_mono fun i => baseChange_iSup_le k _)

end BaseChangeSup

/-! ### The decomposition-map identity

Two squeezes turn the containments above into equalities of dimensions, without invoking
Nakayama or the splitting criterion: for each root of unity the reduction of the
eigen-submodule has the *same* dimension as the rank upstairs, and it exhausts the eigenspace
downstairs. -/

section Decomposition

variable {p : ℕ} [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsDomain 𝒪]
  [ValuationRing 𝒪]
variable [Module.Free 𝒪 L] [Module.Finite 𝒪 L]
variable {n : ℕ} (hn : ¬ p ∣ n) (hn0 : 0 < n) {ω : 𝒪} (hω : IsPrimitiveRoot ω n)
include hn hn0 hω

omit [IsDomain 𝒪] [ValuationRing 𝒪] [Module.Free 𝒪 L]
  [Module.Finite 𝒪 L] hn0 in
/-- A primitive `n`-th root of unity of `𝒪` stays primitive in the residue field, for `p ∤ n`:
a smaller power that becomes `1` downstairs was already `1` upstairs, by separatedness. -/
theorem isPrimitiveRoot_residue : IsPrimitiveRoot (residue 𝒪 ω) n := by
  refine ⟨by rw [← map_pow, hω.pow_eq_one, map_one], fun l hl => ?_⟩
  refine hω.dvd_of_pow_eq_one l ?_
  refine eq_of_pow_eq_one_of_sub_mem (isUnit_natCast_of_not_dvd (p := p) hn)
    (by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]) (one_pow n) ?_
  refine (residue_eq_zero_iff _).mp ?_
  rw [map_sub, map_one, map_pow, hl, sub_self]

variable {A : Module.End 𝒪 L} (hA : A ^ n = 1)
include hA

/-- **Reduction does not lose dimension**: the base change of a `ζ`-eigen-submodule has
dimension equal to its rank, and fills the whole `ζ̄`-eigenspace of the reduced operator. -/
theorem finrank_eigenspace_baseChange {ζ : 𝒪} (hζ : ζ ∈ nthRootsFinset n (1 : 𝒪)) :
    Module.finrank (ResidueField 𝒪)
        (Module.End.eigenspace (A.baseChange (ResidueField 𝒪)) (residue 𝒪 ζ))
      = Module.finrank 𝒪 (Module.End.eigenspace A ζ) := by
  classical
  set k := ResidueField 𝒪
  set s := nthRootsFinset n (1 : 𝒪) with hs
  -- squeeze 1: the base changes of the eigen-submodules have the right dimensions
  have hbc_le : ∀ η ∈ s, Module.finrank k ((Module.End.eigenspace A η).baseChange k)
      ≤ Module.finrank 𝒪 (Module.End.eigenspace A η) := by
    intro η hη
    haveI := free_eigenspace_of_pow (p := p) hn hn0 hω hA hη
    haveI := finite_eigenspace_of_pow (p := p) hn hn0 hω hA hη
    rw [Submodule.baseChange, ← Module.finrank_baseChange (R := k) (S := 𝒪)
      (M' := Module.End.eigenspace A η)]
    exact LinearMap.finrank_range_le _
  have htop : (⨆ η ∈ s, (Module.End.eigenspace A η).baseChange k) = ⊤ :=
    iSup_baseChange_biSup_eq_top k s _
      (iSup_eigenspace_eq_top_of_pow (p := p) hn hn0 hω hA)
  have hDsum : Module.finrank k (k ⊗[𝒪] L)
      ≤ ∑ η ∈ s, Module.finrank k ((Module.End.eigenspace A η).baseChange k) := by
    calc Module.finrank k (k ⊗[𝒪] L)
        = Module.finrank k ↥(⨆ η ∈ s, (Module.End.eigenspace A η).baseChange k) := by
          rw [htop, finrank_top]
      _ ≤ _ := finrank_biSup_le_sum s _
  have hrank : ∑ η ∈ s, Module.finrank 𝒪 (Module.End.eigenspace A η) = Module.finrank 𝒪 L :=
    sum_finrank_eigenspace_of_pow (p := p) hn hn0 hω hA
  have hbc_eq : ∀ η ∈ s, Module.finrank k ((Module.End.eigenspace A η).baseChange k)
      = Module.finrank 𝒪 (Module.End.eigenspace A η) := by
    refine (Finset.sum_eq_sum_iff_of_le hbc_le).mp
      (le_antisymm (Finset.sum_le_sum hbc_le) ?_)
    rw [hrank, ← Module.finrank_baseChange (R := k) (S := 𝒪) (M' := L)]
    exact hDsum
  -- squeeze 2: those base changes exhaust the eigenspaces downstairs
  have hle : ∀ η ∈ s, Module.finrank 𝒪 (Module.End.eigenspace A η)
      ≤ Module.finrank k (Module.End.eigenspace (A.baseChange k) (residue 𝒪 η)) := by
    intro η hη
    rw [← hbc_eq η hη]
    exact Submodule.finrank_mono (baseChange_eigenspace_le A η)
  refine ((Finset.sum_eq_sum_iff_of_le hle).mp ?_ ζ hζ).symm
  rw [hrank, sum_nthRootsFinset_residue hn hn0
    (fun c => Module.finrank k (Module.End.eigenspace (A.baseChange k) c)),
    OddOrder.sum_finrank_eigenspace_of_pow hn0 (isPrimitiveRoot_residue hn hω)
      (baseChange_pow_eq_one hA),
    Module.finrank_baseChange]

/-- **The decomposition-map identity at the level of operators.**  The trace of a finite-order
lattice endomorphism is the Brauer-character expression of its reduction. -/
theorem trace_eq_sum_finrank_baseChange_eigenspace :
    LinearMap.trace 𝒪 L A
      = ∑ ζ ∈ nthRootsFinset n (1 : 𝒪),
          Module.finrank (ResidueField 𝒪)
            (Module.End.eigenspace (A.baseChange (ResidueField 𝒪)) (residue 𝒪 ζ)) • ζ := by
  rw [trace_eq_sum_finrank_smul_of_pow (p := p) hn hn0 hω hA]
  exact Finset.sum_congr rfl fun ζ hζ => by rw [finrank_eigenspace_baseChange hn hn0 hω hA hζ]

end Decomposition

/-! ### The decomposition map, in representation form -/

section Representation

variable {G : Type*} [Group G]

/-- **The reduction of an `𝒪`-representation** modulo the maximal ideal: base change along
`𝒪 → k`.  It is a homomorphism because `Module.End.baseChangeHom` is an algebra map. -/
noncomputable def reduction [IsLocalRing 𝒪] (ρ : Representation 𝒪 G L) :
    Representation (ResidueField 𝒪) G (ResidueField 𝒪 ⊗[𝒪] L) :=
  MonoidHom.comp (Module.End.baseChangeHom 𝒪 (ResidueField 𝒪) L).toRingHom.toMonoidHom ρ

@[simp]
theorem reduction_apply [IsLocalRing 𝒪] (ρ : Representation 𝒪 G L) (g : G) :
    reduction ρ g = (ρ g).baseChange (ResidueField 𝒪) := rfl

/-- **Reduction is compatible with the whole group-algebra action**, not just with group
elements: the `k[G]`-action on the reduction is the base change of the `𝒪[G]`-action, along the
coefficient reduction `𝒪[G] → k[G]`.

This is what carries the central character down.  If `z ∈ Z(𝒪G)` acts on `L` by `ω(z)`, then
`z̄` acts on the reduction by `residue (ω z) = λ(z̄)` — so every constituent of the reduction has
the centre acting by the same character, which is Navarro (3.3). -/
theorem asAlgebraHom_reduction_mapRingHom [IsLocalRing 𝒪] (ρ : Representation 𝒪 G L)
    (x : MonoidAlgebra 𝒪 G) :
    (reduction ρ).asAlgebraHom (MonoidAlgebra.mapRingHom G (residue 𝒪) x)
      = LinearMap.baseChange (ResidueField 𝒪) (ρ.asAlgebraHom x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g r =>
    rw [MonoidAlgebra.mapRingHom_single, Representation.asAlgebraHom_single,
      Representation.asAlgebraHom_single, LinearMap.baseChange_smul, reduction_apply,
      ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]

/-- A `p`-regular element of a finite group satisfies the finite-order hypothesis at the
canonical exponent `|G|_{p'}`. -/
theorem rep_pow_pRegularExponent_eq_one' {p : ℕ} [Finite G] (ρ : Representation 𝒪 G L)
    (hp : p.Prime) {g : G} (hg : OddOrder.GroupTheory.IsPRegular p g) :
    (ρ g) ^ OddOrder.GroupTheory.pRegularExponent p G = 1 := by
  rw [← map_pow, OddOrder.GroupTheory.pow_pRegularExponent_eq_one hp hg, map_one]

variable {p : ℕ} [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsDomain 𝒪]
  [ValuationRing 𝒪] [Module.Free 𝒪 L] [Module.Finite 𝒪 L]
variable {n : ℕ} (hn : ¬ p ∣ n) (hn0 : 0 < n) {ω : 𝒪} (hω : IsPrimitiveRoot ω n)
  (ρ : Representation 𝒪 G L)
include hn hn0 hω

/-- **The decomposition map.**  The ordinary character of an `𝒪`-lattice representation — the
trace over `𝒪`, which is the character of the associated representation over the fraction
field — agrees with the Brauer character of its reduction.

This is the identity `χ = ∑_φ d_{χφ} φ` before the reduction is broken into composition
factors; the breaking up is `brauerCharacter_quotient_add_subrepresentation`. -/
theorem trace_eq_brauerCharacter_reduction {g : G} (hg : (ρ g) ^ n = 1) :
    LinearMap.trace 𝒪 L (ρ g) = brauerCharacter (𝒪 := 𝒪) n (reduction ρ) g := by
  rw [brauerCharacter_eq_sum_nthRootsFinset hn hn0,
    trace_eq_sum_finrank_baseChange_eigenspace hn hn0 hω hg]
  exact Finset.sum_congr rfl fun ζ _ => by rw [reduction_apply]

end Representation

end OddOrder.RepresentationTheory.Modular
