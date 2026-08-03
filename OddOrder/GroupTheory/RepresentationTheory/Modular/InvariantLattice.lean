/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# `G`-invariant lattices in a representation over the fraction field

The decomposition map compares an ordinary representation, over the field of fractions `K` of
the coefficient ring `𝒪`, with the reduction of an `𝒪`-lattice inside it.  For that comparison
to apply to *every* ordinary representation one needs a `G`-invariant lattice, and for a finite
group there always is one: take any lattice and average it over the group,

`L = ⨆ g ∈ G, g · L₀`.

The sum is finite, so `L` is still finitely generated, it still spans, and it is visibly
`G`-stable.  (Nothing here needs `𝒪` to be a discrete valuation ring, or even a domain: only
finiteness of `G`.)

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_invariant_lattice`
-/

namespace OddOrder.RepresentationTheory.Modular

variable {𝒪 K G V : Type*} [CommRing 𝒪] [Field K] [Algebra 𝒪 K] [Group G]
  [AddCommGroup V] [Module K V] [Module 𝒪 V] [IsScalarTower 𝒪 K V]

/-- The average of a lattice over the group: the supremum of its translates. -/
def averagedLattice (ρ : Representation K G V) (L₀ : Submodule 𝒪 V) : Submodule 𝒪 V :=
  ⨆ g : G, L₀.map ((ρ g).restrictScalars 𝒪)

theorem le_averagedLattice (ρ : Representation K G V) (L₀ : Submodule 𝒪 V) :
    L₀ ≤ averagedLattice ρ L₀ := fun v hv =>
  Submodule.mem_iSup_of_mem 1 ⟨v, hv, by simp⟩

theorem fg_averagedLattice [Finite G] (ρ : Representation K G V) {L₀ : Submodule 𝒪 V}
    (h : L₀.FG) : (averagedLattice ρ L₀).FG :=
  Submodule.fg_iSup _ fun _ => h.map _

/-- **The averaged lattice is `G`-stable.** -/
theorem mem_averagedLattice_of_mem (ρ : Representation K G V) (L₀ : Submodule 𝒪 V) (h : G)
    {v : V} (hv : v ∈ averagedLattice ρ L₀) : ρ h v ∈ averagedLattice ρ L₀ := by
  induction hv using Submodule.iSup_induction' with
  | mem g x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    refine Submodule.mem_iSup_of_mem (h * g) ⟨w, hw, ?_⟩
    simp [map_mul]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- **Every representation of a finite group over `K` contains a `G`-invariant `𝒪`-lattice.**
Averaging keeps finite generation (the sum is finite) and can only enlarge the span. -/
theorem exists_invariant_lattice [Finite G] (ρ : Representation K G V) (L₀ : Submodule 𝒪 V)
    (hfg : L₀.FG) :
    ∃ L : Submodule 𝒪 V, L.FG ∧ L₀ ≤ L ∧ ∀ (h : G), ∀ v ∈ L, ρ h v ∈ L :=
  ⟨averagedLattice ρ L₀, fg_averagedLattice ρ hfg, le_averagedLattice ρ L₀,
    fun h _ hv => mem_averagedLattice_of_mem ρ L₀ h hv⟩

/-- If the starting lattice spans `V` over `K`, so does the averaged one. -/
theorem span_averagedLattice_eq_top (ρ : Representation K G V) {L₀ : Submodule 𝒪 V}
    (h : Submodule.span K (L₀ : Set V) = ⊤) :
    Submodule.span K ((averagedLattice ρ L₀ : Submodule 𝒪 V) : Set V) = ⊤ :=
  eq_top_iff.mpr (h ▸ Submodule.span_mono (le_averagedLattice ρ L₀))

end OddOrder.RepresentationTheory.Modular
