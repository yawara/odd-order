/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import OddOrder.Algebra.PiMatrixSimpleModules
import OddOrder.GroupTheory.RepresentationTheory.PGroupFixedVector

/-!
# A normal `p`-subgroup acts trivially on every simple module

**Navarro (2.32)**.  If `char k = p` and `N ⊴ G` is a `p`-subgroup, then `N` lies in the kernel of
every irreducible `k`-representation of `G`; in particular `O_p(G)` acts trivially on every simple
`kG`-module.

The simple modules are taken in the form the block theory of this development uses them: the
column spaces `nn i → k` of a surjection `π : kG ↠ ∏_j M_{n_j}(k)`
(`OddOrder.MatrixModule.blockModule`, `OddOrder.MatrixModule.isSimpleModule_blockModule`).  So the
conclusion reads `π (single u 1) i = 1` for `u ∈ N`.

The proof is the textbook one.  The fixed space `V^N` is nonzero because a `p`-group acting on a
nonzero vector space in characteristic `p` has a nonzero fixed vector — that is
`IsPGroup.invariants_ne_bot`, already available in this repository from BG §2 — and `V^N` is a
`kG`-submodule because `N` is normal.  Simplicity then forces `V^N = V`.

This feeds Navarro (4.7) (`K̂ ∈ J(Z(kG))` whenever `K ∩ C_G(O_p(G)) = ∅`) and through it the
Brauer correspondence (4.14).

## Main definitions

* `OddOrder.GroupAlgebra.blockRepresentation` — the `i`-th block as a representation of `G`

## Main results

* `OddOrder.GroupAlgebra.blockRepresentation_eq_one_of_mem_normal_pSubgroup`
* `OddOrder.GroupAlgebra.pi_single_eq_one_of_mem_normal_pSubgroup`
-/

namespace OddOrder.GroupAlgebra

open Matrix MonoidAlgebra OddOrder.MatrixModule

variable {k ι G : Type*} [Field k] [Group G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
variable (π : MonoidAlgebra k G →+* ∀ j, Matrix (nn j) (nn j) k)

/-- **The `i`-th block as a representation of `G`.**  A splitting `π : kG → ∏_j M_{n_j}(k)` turns
the column space `nn i → k` into a `kG`-module (`OddOrder.MatrixModule.blockModule`); restricting
the action to the group elements is the representation recorded here. -/
noncomputable def blockRepresentation (i : ι) : Representation k G (nn i → k) where
  toFun g := Matrix.toLinAlgEquiv' (π (single g (1 : k)) i)
  map_one' := by
    change Matrix.toLinAlgEquiv' (π (single (1 : G) (1 : k)) i) = 1
    rw [← MonoidAlgebra.one_def, map_one, Pi.one_apply, map_one]
  map_mul' g h := by
    change Matrix.toLinAlgEquiv' (π (single (g * h) (1 : k)) i) = _
    have hsplit : (single (g * h) (1 : k) : MonoidAlgebra k G) = single g 1 * single h 1 := by
      rw [single_mul_single, one_mul]
    rw [hsplit, map_mul, Pi.mul_apply, map_mul]

@[simp]
theorem blockRepresentation_apply (i : ι) (g : G) (v : nn i → k) :
    blockRepresentation π i g v = π (single g (1 : k)) i *ᵥ v :=
  Matrix.toLinAlgEquiv'_apply _ _

/-- The representation is the restriction of the module action to the group elements. -/
theorem blockRepresentation_eq_smul (i : ι) (g : G) (v : nn i → k) :
    letI := blockModule nn π i
    blockRepresentation π i g v = (single g (1 : k) : MonoidAlgebra k G) • v :=
  Matrix.toLinAlgEquiv'_apply _ _

variable [∀ i, Nonempty (nn i)] [Finite G]

/-- **Navarro (2.32).**  A normal `p`-subgroup acts trivially on every simple `kG`-module when
`char k = p`. -/
theorem blockRepresentation_eq_one_of_mem_normal_pSubgroup {p : ℕ} [Fact p.Prime] [CharP k p]
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a)
    {N : Subgroup G} [hNnorm : N.Normal] (hN : IsPGroup p ↥N) (i : ι) {u : G} (hu : u ∈ N) :
    blockRepresentation π i u = 1 := by
  classical
  letI := blockModule nn π i
  haveI := isScalarTower_blockModule hlin i
  haveI hsimple : IsSimpleModule (MonoidAlgebra k G) (nn i → k) :=
    isSimpleModule_blockModule hπ i
  set ρ : Representation k G (nn i → k) := blockRepresentation π i with hρ
  set W : Submodule k (nn i → k) :=
    Representation.invariants (ρ.comp N.subtype : Representation k ↥N (nn i → k)) with hWdef
  have hmemW : ∀ v : nn i → k, v ∈ W ↔ ∀ n : G, n ∈ N → ρ n v = v := by
    intro v
    rw [hWdef, Representation.mem_invariants]
    exact ⟨fun h n hn => h ⟨n, hn⟩, fun h n => h n n.2⟩
  -- The fixed space is nonzero: a `p`-group in characteristic `p` fixes a nonzero vector.
  have hWne : W ≠ ⊥ := hN.invariants_ne_bot _ top_ne_bot
  -- The fixed space is a `kG`-submodule, because `N` is normal.
  have hstable : ∀ (a : MonoidAlgebra k G) {v : nn i → k}, v ∈ W → a • v ∈ W := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | hM g =>
      intro v hv
      have hgv : (of k G g : MonoidAlgebra k G) • v = ρ g v :=
        (blockRepresentation_eq_smul π i g v).symm
      rw [hgv, hmemW]
      intro n hn
      have hconj : g⁻¹ * n * g ∈ N := by
        simpa using hNnorm.conj_mem n hn g⁻¹
      have hrw : n * g = g * (g⁻¹ * n * g) := by group
      calc ρ n (ρ g v) = ρ (n * g) v := by rw [← Module.End.mul_apply, ← map_mul]
        _ = ρ g (ρ (g⁻¹ * n * g) v) := by rw [hrw, map_mul, Module.End.mul_apply]
        _ = ρ g v := by rw [(hmemW v).mp hv _ hconj]
    | hadd x y hx hy =>
      intro v hv
      rw [add_smul]
      exact W.add_mem (hx hv) (hy hv)
    | hsmul c x hx =>
      intro v hv
      rw [smul_assoc]
      exact W.smul_mem c (hx hv)
  let W' : Submodule (MonoidAlgebra k G) (nn i → k) :=
    { carrier := (W : Set (nn i → k))
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun a _ hv => hstable a hv }
  -- Simplicity: a nonzero submodule is everything.
  have hW'top : W' = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top W' with h | h
    · refine absurd ?_ hWne
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hvW' : v ∈ W' := hv
      rw [h] at hvW'
      simpa using hvW'
    · exact h
  have hfix : ∀ v : nn i → k, ρ u v = v := by
    intro v
    have hvW' : v ∈ W' := by rw [hW'top]; exact Submodule.mem_top
    exact (hmemW v).mp hvW' u hu
  exact LinearMap.ext fun v => by rw [Module.End.one_apply]; exact hfix v

/-- **A simple module on which `N` acts trivially and whose remaining quotient is a `p`-group is
the trivial module.**

If `N ≤ G` acts trivially on a simple `kG`-module and `G = N·P` for a `p`-subgroup `P`, then all
of `G` acts trivially.  The point is that the `P`-fixed space is automatically `G`-fixed — writing
`g = n x` gives `g · w = n · (x · w) = n · w = w` — so it is a nonzero submodule and simplicity
finishes.

Passing to `G/N` and invoking `blockRepresentation_eq_one_of_mem_normal_pSubgroup` there would say
the same thing; keeping everything inside `G` avoids transporting the splitting `π` along the
quotient map.  This is what turns "`G` has a normal `p`-complement" into "`IBr(B₀)` is trivial" in
Navarro (6.13). -/
theorem blockRepresentation_eq_one_of_sup_eq_top {p : ℕ} [Fact p.Prime] [CharP k p]
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a)
    {N P : Subgroup G} [N.Normal] (hP : IsPGroup p ↥P) (hsup : N ⊔ P = ⊤)
    (i : ι) (hNtriv : ∀ u ∈ N, blockRepresentation π i u = 1) (g : G) :
    blockRepresentation π i g = 1 := by
  classical
  letI := blockModule nn π i
  haveI := isScalarTower_blockModule hlin i
  haveI hsimple : IsSimpleModule (MonoidAlgebra k G) (nn i → k) :=
    isSimpleModule_blockModule hπ i
  set ρ : Representation k G (nn i → k) := blockRepresentation π i with hρ
  -- every element of `G` is `n * x` with `n ∈ N`, `x ∈ P`
  have hdecomp : ∀ y : G, ∃ n ∈ N, ∃ x ∈ P, y = n * x := by
    intro y
    have hy : y ∈ (↑(N ⊔ P) : Set G) := by rw [hsup]; trivial
    rw [Subgroup.normal_mul] at hy
    obtain ⟨n, hn, x, hx, hnx⟩ := hy
    exact ⟨n, hn, x, hx, hnx.symm⟩
  -- the `P`-fixed vectors are already `G`-fixed
  have hfix : ∀ v : nn i → k, (∀ x : P, ρ (x : G) v = v) → ∀ y : G, ρ y v = v := by
    intro v hv y
    obtain ⟨n, hn, x, hx, rfl⟩ := hdecomp y
    rw [map_mul, Module.End.mul_apply, hv ⟨x, hx⟩, hNtriv n hn, Module.End.one_apply]
  -- so `V^G` is nonzero
  set W : Submodule k (nn i → k) := ρ.invariants with hWdef
  have hWne : W ≠ ⊥ := by
    intro hbot
    refine hP.invariants_ne_bot (ρ.comp P.subtype : Representation k ↥P (nn i → k)) top_ne_bot ?_
    rw [Submodule.eq_bot_iff]
    intro v hv
    have : v ∈ W := (Representation.mem_invariants ρ v).mpr
      (hfix v fun x => (Representation.mem_invariants _ v).mp hv x)
    rw [hbot] at this
    simpa using this
  -- and it is a `kG`-submodule, hence everything
  have hstable : ∀ (a : MonoidAlgebra k G) {v : nn i → k}, v ∈ W → a • v ∈ W := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | hM y =>
      intro v hv
      have hyv : (of k G y : MonoidAlgebra k G) • v = ρ y v :=
        (blockRepresentation_eq_smul π i y v).symm
      rw [hyv]
      exact (Representation.mem_invariants ρ _).mpr fun z => by
        rw [← Module.End.mul_apply, ← map_mul]
        simp only [(Representation.mem_invariants ρ v).mp hv]
    | hadd u w hu hw => intro v hv; rw [add_smul]; exact W.add_mem (hu hv) (hw hv)
    | hsmul c u hu => intro v hv; rw [smul_assoc]; exact W.smul_mem c (hu hv)
  let W' : Submodule (MonoidAlgebra k G) (nn i → k) :=
    { carrier := (W : Set (nn i → k))
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun a _ hv => hstable a hv }
  have hW'top : W' = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top W' with h | h
    · refine absurd ?_ hWne
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hvW' : v ∈ W' := hv
      rw [h] at hvW'
      simpa using hvW'
    · exact h
  refine LinearMap.ext fun v => ?_
  have hvW' : v ∈ W' := by rw [hW'top]; exact Submodule.mem_top
  rw [Module.End.one_apply]
  exact (Representation.mem_invariants ρ v).mp hvW' g

/-- **Navarro (2.32)**, matrix form: for `u` in a normal `p`-subgroup the operator
`π (single u 1) i` is the identity matrix. -/
theorem pi_single_eq_one_of_mem_normal_pSubgroup {p : ℕ} [Fact p.Prime] [CharP k p]
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a)
    {N : Subgroup G} [N.Normal] (hN : IsPGroup p ↥N) (i : ι) {u : G} (hu : u ∈ N) :
    π (single u (1 : k)) i = 1 := by
  apply (Matrix.toLinAlgEquiv' (R := k) (n := nn i)).injective
  rw [map_one]
  exact blockRepresentation_eq_one_of_mem_normal_pSubgroup π hπ hlin hN i hu

end OddOrder.GroupAlgebra
