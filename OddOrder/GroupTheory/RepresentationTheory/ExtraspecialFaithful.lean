/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.FDRep
import OddOrder.GroupTheory.IsExtraspecial

/-!
# Faithful representations of extraspecial `p`-groups (BG §2 Thm 2.5 scaffold)

`OddOrder.GroupTheory.RepresentationTheory` shared module: scaffold for
**Bender-Glauberman §2 Thm 2.5** infrastructure on faithful complex
representations of extraspecial `p`-groups.

## Status

* Skeleton only.  See issue **#34** for the full implementation plan.

## BG ↔ mathlib mapping

* **BG Thm 2.5** — every faithful absolutely irreducible representation of an
  extraspecial `p`-group `E` of order `p^{1+2n}` has dimension exactly `p^n`.
  The proof routes through Clifford's theorem applied to the center `Z(E)`
  (already available in `OddOrder.RepresentationTheory.Clifford` modulo the
  sorry on `clifford_decomposition`, see issue #26).
* The bridging data is the `OddOrder.GroupTheory.IsExtraspecial` predicate
  already in the repo.
-/

namespace OddOrder.RepresentationTheory

end OddOrder.RepresentationTheory
