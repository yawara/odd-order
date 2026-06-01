/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Main

/-!
# Subgroup constructions realized in the ambient group

Shared low-level `OddOrder.GroupTheory` module for two constructions that BG
(Chapters II–IV) and Peterfalvi (Sections 10–16) both need, realized as
subgroups of the *ambient* group `G` rather than of the subgroup `H`:

* `derivedInG H` — the derived subgroup `H'` of `H`, mapped back into `G`.
* `opiCoreInG π H` — the `pi`-core `O_π(H)` of `H`, mapped back into `G`.

These were originally duplicated as `BG.Ch2.S07.{derivedInG, opiCoreInG}` and as
`GroupTheory.{derivedInAmbient, piCoreIn, pCoreIn, pPrimeCoreIn}`; this file is
the single canonical home (issue 0052). It sits low in the import graph (only
`Isaacs.Ch03`) so every consumer can import it cheaply.
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-- **`H'` in `G`**: the derived subgroup `commutator ↥H` of a subgroup `H`,
mapped back into the ambient group `G` via `H.subtype`. -/
def derivedInG (H : Subgroup G) : Subgroup G :=
  (commutator ↥H).map H.subtype

/-- **`O_π(H)` in `G`**: the `π`-core of the subgroup `H` (largest normal
`π`-subgroup of `↥H`), mapped back into the ambient group `G` via `H.subtype`.
`opiCoreInG {p} H = O_p(H)` and `opiCoreInG {p}ᶜ H = O_{p'}(H)`, both in `G`. -/
def opiCoreInG (π : Set ℕ) (H : Subgroup G) : Subgroup G :=
  (Ch03.oPiCore π ↥H).map H.subtype

end OddOrder.GroupTheory
