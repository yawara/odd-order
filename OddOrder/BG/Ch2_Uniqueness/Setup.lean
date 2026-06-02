/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.SetTheory.Cardinal.Finite
import OddOrder.GroupTheory.MaximalSubgroup

/-!
# The fixed minimal counterexample `G` (BG §7)

Bender–Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994), §7
(mmd L2133): *"We now assume that the main theorem is false. Henceforth … we let `G`
denote a fixed counterexample of minimal order. Of course `G` is a nonabelian simple group."*

This is the ambient hypothesis under which all of Chapters II–IV (BG §7–§16) operate. It is
bundled as a `structure` (the same pattern as `OddOrder.Peterfalvi.…Hypothesis`) so that every
downstream theorem threads a single named hypothesis `hG : IsMinimalSimpleOdd G` rather than a
drifting collection of `variable`s; converting to/from the unbundled (mathlib / eval-submission)
form is a one-line wrapper in either direction.

`IsMinimalSimpleOdd` is **not** a restatement of the Odd Order Theorem; it is the *negation
setup* (assume a counterexample exists). The actual theorem
`Odd (Nat.card G) → IsSolvable G` is obtained by deriving `False` from `IsMinimalSimpleOdd G`
via the whole §7–§16 + Appendix C contradiction, not by unwrapping this structure.

## Main definition

* `IsMinimalSimpleOdd G`: `G` is finite of odd order, simple, non-solvable, and every proper
  subgroup is solvable (the working form of "minimal counterexample of odd order").

## References

* Bender, Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994), §7.
-/

namespace OddOrder.BG

/-- **BG fixed counterexample `G`** (§7, mmd L2133): the working hypotheses of a *minimal
counterexample of odd order* to the Odd Order Theorem. `G` is finite of odd order, simple,
non-solvable (a genuine counterexample, hence nonabelian simple), and — by minimality of the
order — every proper subgroup of `G` is solvable.

All of BG Chapters II–IV (§7–§16) are stated under `(hG : IsMinimalSimpleOdd G)`. -/
structure IsMinimalSimpleOdd (G : Type*) [Group G] [Finite G] : Prop where
  /-- `|G|` is odd. -/
  odd : Odd (Nat.card G)
  /-- `G` is simple. -/
  simple : IsSimpleGroup G
  /-- `G` is not solvable (it is a counterexample). Together with `simple` this is "`G` is a
  nonabelian simple group" (BG: "Of course `G` is a nonabelian simple group"). -/
  notSolvable : ¬ IsSolvable G
  /-- Minimality of the counterexample: every proper subgroup of `G` is solvable. -/
  properSolvable : ∀ M : Subgroup G, M < ⊤ → IsSolvable M

namespace IsMinimalSimpleOdd

variable {G : Type*} [Group G] [Finite G]

/-- A minimal simple counterexample is nontrivial (it is simple, hence has `> 1` element). -/
theorem nontrivial (hG : IsMinimalSimpleOdd G) : Nontrivial G :=
  have : IsSimpleGroup G := hG.simple
  inferInstance

/-- Every proper subgroup of a minimal counterexample is solvable. -/
theorem solvable_of_lt_top (hG : IsMinimalSimpleOdd G) (M : Subgroup G) (hM : M < ⊤) :
    IsSolvable M :=
  hG.properSolvable M hM

/-- Every maximal subgroup of a minimal counterexample is solvable. -/
theorem solvable_of_isCoatom (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : IsCoatom M) :
    IsSolvable M :=
  hG.solvable_of_lt_top M hM.lt_top

/-- The `ℳ`-membership form of `solvable_of_isCoatom`. -/
theorem solvable_of_mem_maximalSubgroups (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ OddOrder.GroupTheory.maximalSubgroups G) :
    IsSolvable M :=
  hG.solvable_of_isCoatom (OddOrder.GroupTheory.mem_maximalSubgroups.mp hM)

end IsMinimalSimpleOdd

end OddOrder.BG
