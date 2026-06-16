/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Wielandt's fixed-point formula — the module-level counting (Peterfalvi (9.1))

This file builds the elementary-abelian (= vector-space) core of **Peterfalvi (9.1)**
(Wielandt's fixed-point formula).  The eventual target, assembled in
`OddOrder.GroupTheory.CoprimeAction`, is

`|C_H(UE)|^{|E|} · |H| = |C_H(E)|^{|E|} · |C_H(U)|`

for a Frobenius group `L = U ⋊ E` acting coprimely on a finite solvable group `H`.

The proof reduces, through a chief series of `H`, to a dimension identity on each
elementary-abelian chief factor `V` (an `𝔽_p[L]`-module with `p ∤ |L|`):

`|E| · dim V^L + dim V = |E| · dim V^E + dim V^U`.            (⋆)

See `notes/peterfalvi/s11_wielandt_91_design.md` for the full route.  This file collects
the linear-algebra facts; `S03b_Lemma33` already supplies the *qualitative* Wielandt
lemma (kernel acts trivially), but the present *counting* needs Maschke + Brauer's
permutation lemma instead of the averaging-operator trace.

## Main results (this file, growing bottom-up)

* `finrank_invariants_add_finrank_ker_averageMap`: the coprime decomposition
  `V = V^G ⊕ [V,G]` at the level of dimensions, `dim V^G + dim [V,G] = dim V`.
-/

namespace OddOrder.GroupTheory.WielandtCounting

open Module Representation

variable {k : Type*} [Field k] {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- **Coprime decomposition, dimension form.**  When `|G|` is invertible in `k`, the averaging
map `averageMap ρ` is a projection onto the invariants `V^G`, so `V = V^G ⊕ [V,G]` with
`[V,G] = ker (averageMap ρ)`.  Taking dimensions:
`dim V^G + dim [V,G] = dim V`. -/
theorem finrank_invariants_add_finrank_ker_averageMap
    (ρ : Representation k G V) [Fintype G] [Invertible (Fintype.card G : k)]
    [FiniteDimensional k V] :
    finrank k ρ.invariants + finrank k (LinearMap.ker ρ.averageMap) = finrank k V := by
  have hrange : LinearMap.range ρ.averageMap = ρ.invariants := (isProj_averageMap ρ).range
  rw [← hrange, LinearMap.finrank_range_add_finrank_ker]

end OddOrder.GroupTheory.WielandtCounting
