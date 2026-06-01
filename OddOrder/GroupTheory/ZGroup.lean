/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow

/-!
# Z-groups (every Sylow subgroup cyclic)

`OddOrder.GroupTheory` shared module: a **Z-group** is a finite group all of whose Sylow
subgroups are cyclic. Bender–Glauberman use this in §10 (Lemma 10.4(b)) and elsewhere.

## Main definitions

* `IsZGroup G`: every Sylow `p`-subgroup of `G` (for every prime `p`) is cyclic.

## References

* Bender, Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994), §10.
-/

namespace OddOrder.GroupTheory

/-- **Z-group**: a group all of whose Sylow subgroups are cyclic. -/
def IsZGroup (G : Type*) [Group G] : Prop :=
  ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic ↥(P : Subgroup G)

end OddOrder.GroupTheory
