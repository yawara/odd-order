/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Module.Lattice
import Mathlib.LinearAlgebra.Trace
import OddOrder.Algebra.ValuationRingFreeModule
import OddOrder.GroupTheory.RepresentationTheory.Modular.InvariantLattice

/-!
# Ordinary representations and their invariant lattices

The decomposition matrix compares an ordinary representation of `G` — over the fraction field `K`
of the coefficient ring `𝒪` — with the reduction modulo `𝔪` of a `G`-invariant `𝒪`-lattice inside
it.  `InvariantLattice` produces the lattice; this file turns it into a `Representation 𝒪 G L` and
identifies its character with the ordinary one:

`algebraMap 𝒪 K (tr_𝒪 L (ρ_L g)) = tr_K V (ρ g)`.

That identity is what makes the decomposition numbers a function of the *ordinary character*
rather than of the chosen lattice, so that `D` is a matrix indexed by `Irr(G)`.

The proof is a basis comparison: mathlib's `Module.Basis.extendOfIsLattice` turns an `𝒪`-basis of
a lattice into a `K`-basis of the ambient space, and `repr_extendOfIsLattice` below says the
coordinates of a lattice vector are unchanged (up to `algebraMap`).  Both traces are then the
trace of the *same* matrix, read in `𝒪` and in `K`.

Everything is over a valuation ring rather than a PID, because the splitting `p`-modular system
`𝓞_ℂ_[p]` is not Noetherian; `ValuationRingFreeModule` supplies the freeness of the lattice that
mathlib's `Submodule.IsLattice.free` gets from the PID structure theorem.

## Main results

* `OddOrder.RepresentationTheory.Modular.Submodule.IsLattice.free_of_valuationRing` — lattices
  are free
* `OddOrder.RepresentationTheory.Modular.repr_extendOfIsLattice` — coordinates are unchanged
* `OddOrder.RepresentationTheory.Modular.latticeRepresentation` — the restriction of `ρ` to a
  `G`-stable lattice
* `OddOrder.RepresentationTheory.Modular.algebraMap_trace_latticeRepresentation` — the character
  of the lattice representation is the ordinary character
* `OddOrder.RepresentationTheory.Modular.exists_isLattice_invariant` — a `G`-invariant lattice
  always exists
-/

namespace OddOrder.RepresentationTheory.Modular

open Module

variable {𝒪 K V : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪] [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] [AddCommGroup V] [Module K V] [Module 𝒪 V] [IsScalarTower 𝒪 K V]

/-- **A lattice over a valuation ring is free.**  This is mathlib's `Submodule.IsLattice.free`,
which needs a principal ideal domain, over a valuation ring instead. -/
instance Submodule.IsLattice.free_of_valuationRing (M : Submodule 𝒪 V) [M.IsLattice K] :
    Module.Free 𝒪 M :=
  have := Module.IsTorsionFree.trans_faithfulSMul 𝒪 K V
  free_of_isTorsionFree

/-! ### Coordinates in an extended basis -/

omit [IsDomain 𝒪] [ValuationRing 𝒪] in
/-- **A lattice vector has the same coordinates upstairs and downstairs.**  The `K`-basis of `V`
extending an `𝒪`-basis `b` of the lattice reads off, on a vector of the lattice, exactly the
`𝒪`-coordinates of `b`.

Both sides are `𝒪`-linear in `x` and agree on `b i`, so `Module.Basis.ext` finishes. -/
theorem repr_extendOfIsLattice {κ : Type*} {L : Submodule 𝒪 V} [L.IsLattice K]
    (b : Basis κ 𝒪 L) (x : L) (k : κ) :
    (b.extendOfIsLattice K).repr (x : V) k = algebraMap 𝒪 K (b.repr x k) := by
  classical
  set F : L →ₗ[𝒪] K :=
    { toFun := fun y => (b.extendOfIsLattice K).repr (y : V) k
      map_add' := fun y z => by rw [Submodule.coe_add, map_add, Finsupp.add_apply]
      map_smul' := fun c y => by
        have hc : ((c • y : L) : V) = algebraMap 𝒪 K c • (y : V) := by
          rw [Submodule.coe_smul, algebraMap_smul]
        rw [hc, map_smul, Finsupp.smul_apply, RingHom.id_apply, smul_eq_mul,
          Algebra.smul_def] } with hF
  have hFb : ∀ i, F (b i) = algebraMap 𝒪 K (b.repr (b i) k) := by
    intro i
    have h1 : ((b i : L) : V) = (b.extendOfIsLattice K) i :=
      (Module.Basis.extendOfIsLattice_apply K b i).symm
    rw [hF]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, h1, Module.Basis.repr_self, Module.Basis.repr_self,
      Finsupp.single_apply]
    split <;> simp
  have hFeq : F = (Algebra.linearMap 𝒪 K).comp ((Finsupp.lapply k).comp b.repr.toLinearMap) :=
    b.ext fun i => by simpa using hFb i
  exact congrArg (fun f : L →ₗ[𝒪] K => f x) hFeq

/-! ### The representation on an invariant lattice -/

variable {G : Type*} [Group G]

/-- **The restriction of an ordinary representation to a `G`-stable lattice.** -/
def latticeRepresentation (ρ : Representation K G V) {L : Submodule 𝒪 V}
    (hL : ∀ (g : G), ∀ v ∈ L, ρ g v ∈ L) : Representation 𝒪 G L where
  toFun g := ((ρ g).restrictScalars 𝒪).restrict (hL g)
  map_one' := LinearMap.ext fun v => Subtype.ext (by simp [LinearMap.restrict_apply])
  map_mul' g h := LinearMap.ext fun v => Subtype.ext (by simp [LinearMap.restrict_apply])

omit [IsDomain 𝒪] [ValuationRing 𝒪] [IsFractionRing 𝒪 K] in
@[simp]
theorem coe_latticeRepresentation_apply (ρ : Representation K G V) {L : Submodule 𝒪 V}
    (hL : ∀ (g : G), ∀ v ∈ L, ρ g v ∈ L) (g : G) (v : L) :
    ((latticeRepresentation ρ hL g v : L) : V) = ρ g v := rfl

/-! ### The character of the lattice representation is the ordinary character -/

/-- **The ordinary character is the trace of the lattice representation.**  Reading both traces in
the basis `b` of the lattice and the basis of `V` it extends, they are the trace of one matrix,
seen in `𝒪` and in `K`.

This is what makes the decomposition numbers depend on the ordinary character alone: two lattices
in the same representation have the same trace function, hence the same decomposition. -/
theorem algebraMap_trace_latticeRepresentation (ρ : Representation K G V) {L : Submodule 𝒪 V}
    [L.IsLattice K] (hL : ∀ (g : G), ∀ v ∈ L, ρ g v ∈ L) (g : G) :
    algebraMap 𝒪 K (LinearMap.trace 𝒪 L (latticeRepresentation ρ hL g))
      = LinearMap.trace K V (ρ g) := by
  classical
  set b := Module.Free.chooseBasis 𝒪 L with hb
  set b' := b.extendOfIsLattice K with hb'
  haveI : Module.Finite K V := Module.Finite.of_basis b'
  rw [LinearMap.trace_eq_matrix_trace 𝒪 b, LinearMap.trace_eq_matrix_trace K b',
    Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rw [hb', Module.Basis.extendOfIsLattice_apply K b i, ← coe_latticeRepresentation_apply ρ hL g,
    ← hb']
  exact (repr_extendOfIsLattice b _ i).symm

/-! ### Existence -/

omit [IsDomain 𝒪] [ValuationRing 𝒪] [IsFractionRing 𝒪 K] in
/-- Every finite-dimensional `K`-vector space contains an `𝒪`-lattice: the `𝒪`-span of a
`K`-basis. -/
theorem exists_isLattice [FiniteDimensional K V] : ∃ L : Submodule 𝒪 V, L.IsLattice K := by
  classical
  set c := Module.Free.chooseBasis K V with hc
  refine ⟨Submodule.span 𝒪 (Set.range c), ⟨Submodule.fg_span (Set.finite_range c), ?_⟩⟩
  rw [Submodule.span_span_of_tower 𝒪 K]
  exact c.span_eq

omit [IsDomain 𝒪] [ValuationRing 𝒪] [IsFractionRing 𝒪 K] in
/-- The average of a lattice over a finite group is again a lattice: it contains the original one
and is still finitely generated. -/
theorem isLattice_averagedLattice [Finite G] (ρ : Representation K G V) (L₀ : Submodule 𝒪 V)
    [L₀.IsLattice K] : (averagedLattice ρ L₀).IsLattice K :=
  Submodule.IsLattice.of_le_of_isLattice_of_fg K (le_averagedLattice ρ L₀)
    (fg_averagedLattice ρ Submodule.IsLattice.fg)

omit [IsDomain 𝒪] [ValuationRing 𝒪] [IsFractionRing 𝒪 K] in
/-- **Every ordinary representation of a finite group has a `G`-invariant lattice.**  This is what
lets the decomposition map be applied to every element of `Irr(G)`. -/
theorem exists_isLattice_invariant [Finite G] [FiniteDimensional K V] (ρ : Representation K G V) :
    ∃ L : Submodule 𝒪 V, L.IsLattice K ∧ ∀ (g : G), ∀ v ∈ L, ρ g v ∈ L := by
  obtain ⟨L₀, hL₀⟩ := exists_isLattice (𝒪 := 𝒪) (K := K) (V := V)
  haveI := hL₀
  exact ⟨averagedLattice ρ L₀, isLattice_averagedLattice ρ L₀,
    fun h _ hv => mem_averagedLattice_of_mem ρ L₀ h hv⟩

end OddOrder.RepresentationTheory.Modular
