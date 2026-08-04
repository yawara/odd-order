/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BlockOfSimpleModule
import OddOrder.Algebra.TraceIsCompl
import OddOrder.GroupTheory.MaschkeComplement
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockRepresentation
import OddOrder.GroupTheory.RepresentationTheory.Modular.MinimalSubrepresentation

/-!
# Every ordinary character decomposes into irreducible ones

The characteristic-zero counterpart of `BrauerDecomposition`.  A splitting `π : KG → ∏ M_{n_i}(K)`
whose kernel is the Jacobson radical — for `K` of characteristic `0` that radical is `0`, so `π`
is a Wedderburn isomorphism and the index set is `Irr(G)` — makes every finite-dimensional
representation's character a non-negative integer combination of the `n_i`-dimensional ones.

The induction is on dimension, exactly as on the modular side, but with one simplification: since
`|G|` is invertible, Maschke gives an **invariant complement** of the minimal invariant subspace
(`exists_isCompl_invariant`), so the trace splits by
`trace_eq_add_trace_restrict_of_isCompl` and no trace additivity along a short exact sequence is
needed.

As on the modular side the induction also delivers **block-diagonality**: a constituent that
actually occurs has the same central character as the whole representation, whenever the centre
acts by a scalar.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_ordinaryCharacter_eq` — a simple representation
  is one of the `n_i`-dimensional ones
* `OddOrder.RepresentationTheory.Modular.exists_ordinary_decomposition_of_finrank_le`
* `OddOrder.RepresentationTheory.Modular.exists_ordinary_decomposition`
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra

variable {K G : Type*} [Field K] [Group G] {ι : Type*} {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]

/-! ### A simple representation is one of the blocks -/

section Simple

variable {V : Type*} [AddCommGroup V] [Module K V]

set_option linter.unusedFintypeInType false in
/-- **A simple representation has one of the irreducible ordinary characters**, and its central
character is read off at the *same* index — the pairing that makes block-diagonality work. -/
theorem exists_ordinaryCharacter_eq (ρ : Representation K G V)
    [IsSimpleModule (MonoidAlgebra K G) ρ.asModule]
    {π : MonoidAlgebra K G →+* ∀ j, Matrix (nn j) (nn j) K} (hπ : Function.Surjective π)
    (hlin : ∀ (c : K) (a : MonoidAlgebra K G), π (c • a) = c • π a)
    (hker : RingHom.ker π ≤ Module.annihilator (MonoidAlgebra K G) ρ.asModule) :
    ∃ i : ι, (∀ g : G, LinearMap.trace K V (ρ g)
        = LinearMap.trace K (nn i → K) (blockRepresentation π i g)) ∧
      ∀ {z : Subalgebra.center K (MonoidAlgebra K G)} {c : K},
        (∀ m : ρ.asModule, (z : MonoidAlgebra K G) • m
          = (algebraMap K (MonoidAlgebra K G) c) • m) →
        c = MatrixModule.centralCharacterAlg π i hπ hlin z := by
  obtain ⟨i, ⟨e⟩⟩ := MatrixModule.exists_linearEquiv_blockModule (nn := nn) hπ hker
  letI := MatrixModule.blockModule nn π i
  haveI := MatrixModule.isScalarTower_blockModule (nn := nn) hlin i
  refine ⟨i, fun g => ?_, fun {z c} hzc => ?_⟩
  · set f : V ≃ₗ[K] (nn i → K) :=
      (ρ.asModuleEquiv.symm).trans (e.restrictScalars K) with hf
    have hint : ∀ (g : G) (v : V), f ((ρ g) v) = (blockRepresentation π i g) (f v) := by
      intro g v
      have h1 : ρ.asModuleEquiv.symm ((ρ g) v)
          = (single g (1 : K)) • ρ.asModuleEquiv.symm v :=
        Representation.asModuleEquiv_symm_map_rho ρ g v
      simp only [hf, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, h1]
      rw [e.map_smul]
      rfl
    have hconj : blockRepresentation π i g = f.conj (ρ g) := by
      refine LinearMap.ext fun v => ?_
      have hv := hint g (f.symm v)
      rw [LinearEquiv.apply_symm_apply] at hv
      simpa [LinearEquiv.conj_apply] using hv.symm
    rw [hconj, LinearMap.trace_conj']
  · refine MatrixModule.eq_centralCharacterAlg_of_forall_smul_eq π i hπ hlin fun v => ?_
    have hv := congrArg e (hzc (e.symm v))
    rw [map_smul, map_smul, e.apply_symm_apply] at hv
    rw [hv, algebraMap_smul]

end Simple

/-! ### The decomposition -/

section Decomposition

variable [Finite G] [NeZero (Nat.card G : K)]
variable {π : MonoidAlgebra K G →+* ∀ j, Matrix (nn j) (nn j) K} (hπ : Function.Surjective π)
  (hlin : ∀ (c : K) (a : MonoidAlgebra K G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra K G))
include hπ hlin hkerJ

/-- **Every ordinary character is a non-negative integer combination of the irreducible ones**,
together with block-diagonality. -/
theorem exists_ordinary_decomposition_of_finrank_le (m : ℕ) :
    ∀ {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (ρ : Representation K G V),
      Module.finrank K V ≤ m →
      ∃ d : ι → ℕ, (∀ g : G, LinearMap.trace K V (ρ g)
          = ∑ i, (d i : K) * LinearMap.trace K (nn i → K) (blockRepresentation π i g)) ∧
        ∀ (i : ι) {z : Subalgebra.center K (MonoidAlgebra K G)} {c : K}, d i ≠ 0 →
          ρ.asAlgebraHom (z : MonoidAlgebra K G) = c • LinearMap.id →
          c = MatrixModule.centralCharacterAlg π i hπ hlin z := by
  classical
  induction m with
  | zero =>
    intro V _ _ _ ρ hm
    haveI : Subsingleton V := Module.finrank_zero_iff.mp (Nat.le_zero.mp hm)
    refine ⟨0, fun g => ?_, ?_⟩
    · rw [show ρ g = 0 from Subsingleton.elim _ _, map_zero]
      simp
    · intro i z c hi _
      exact absurd rfl hi
  | succ m ih =>
    intro V _ _ _ ρ hm
    rcases subsingleton_or_nontrivial V with _ | _
    · refine ⟨0, fun g => ?_, ?_⟩
      · rw [show ρ g = 0 from Subsingleton.elim _ _, map_zero]
        simp
      · intro i z c hi _
        exact absurd rfl hi
    obtain ⟨W, hWinv, hWne, hWmin⟩ := exists_minimal_invariant ρ
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWne
    haveI := isSimpleModule_subrepresentation_of_minimal ρ hWinv hWne hWmin
    obtain ⟨i, hi, hic⟩ := exists_ordinaryCharacter_eq (nn := nn)
      (ρ.subrepresentation W hWinv) hπ hlin
      (hkerJ ▸ IsSemisimpleModule.jacobson_le_annihilator _ _)
    obtain ⟨W', hW'inv, hcompl⟩ :=
      OddOrder.GroupTheory.exists_isCompl_invariant ρ W fun g _ hv => hWinv g hv
    have hW'le : ∀ g : G, W' ≤ W'.comap (ρ g) := fun g _ hv => hW'inv g hv
    have hrank : Module.finrank K W + Module.finrank K W' = Module.finrank K V :=
      Submodule.finrank_add_eq_of_isCompl hcompl
    have hWpos : 0 < Module.finrank K W := Module.finrank_pos
    obtain ⟨d, hd, hdc⟩ := ih (ρ.subrepresentation W' hW'le) (by omega)
    refine ⟨d + Pi.single i 1, fun g => ?_, ?_⟩
    · have h1 : LinearMap.trace K W ((ρ g).restrict (fun _ hv => hWinv g hv))
          = LinearMap.trace K (nn i → K) (blockRepresentation π i g) := hi g
      have h2 : LinearMap.trace K W' ((ρ g).restrict (fun _ hv => hW'inv g hv))
          = ∑ j, (d j : K) * LinearMap.trace K (nn j → K) (blockRepresentation π j g) := hd g
      rw [trace_eq_add_trace_restrict_of_isCompl hcompl (fun _ hv => hWinv g hv)
        (fun _ hv => hW'inv g hv), h1, h2]
      have hsingle : ∑ j, (((Pi.single i 1 : ι → ℕ) j : ℕ) : K) *
          LinearMap.trace K (nn j → K) (blockRepresentation π j g)
          = LinearMap.trace K (nn i → K) (blockRepresentation π i g) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [Pi.single_eq_of_ne hb]
        · intro hmem
          exact absurd (Finset.mem_univ i) hmem
      simp only [Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib, hsingle]
      exact add_comm _ _
    · intro j z c hj hz
      rcases Nat.eq_zero_or_pos (d j) with hdj | hdj
      · have hji : j = i := by
          by_contra hne
          rw [Pi.add_apply, hdj, Pi.single_eq_of_ne hne] at hj
          exact hj rfl
        subst hji
        refine hic fun mm => ?_
        apply (ρ.subrepresentation W hWinv).asModuleEquiv.injective
        rw [Representation.asModuleEquiv_map_smul, Representation.asModuleEquiv_map_smul,
          subrepresentation_asAlgebraHom_eq_smul ρ hWinv hz, AlgHom.commutes]
        simp
      · refine hdc j hdj.ne' (LinearMap.ext fun v => ?_)
        exact subrepresentation_asAlgebraHom_eq_smul ρ hW'le hz v

/-- **The decomposition of an ordinary character into irreducible ones.** -/
theorem exists_ordinary_decomposition {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : Representation K G V) :
    ∃ d : ι → ℕ, (∀ g : G, LinearMap.trace K V (ρ g)
        = ∑ i, (d i : K) * LinearMap.trace K (nn i → K) (blockRepresentation π i g)) ∧
      ∀ (i : ι) {z : Subalgebra.center K (MonoidAlgebra K G)} {c : K}, d i ≠ 0 →
        ρ.asAlgebraHom (z : MonoidAlgebra K G) = c • LinearMap.id →
        c = MatrixModule.centralCharacterAlg π i hπ hlin z :=
  exists_ordinary_decomposition_of_finrank_le hπ hlin hkerJ _ ρ le_rfl

end Decomposition

end OddOrder.RepresentationTheory.Modular
