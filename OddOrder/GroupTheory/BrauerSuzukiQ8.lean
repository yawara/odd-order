/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module -- shake: keep-all

public import OddOrder.GroupTheory.BrauerSuzukiQ8.CharacterCore
public import OddOrder.GroupTheory.BrauerSuzukiQ8.Induction
public import OddOrder.GroupTheory.BrauerSuzukiQ8.Reduction
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Positivity.Finset

/-!
# Brauer–Suzuki: the `Q₈` case (Navarro, *Characters and Blocks*, pp. 139–146)

Pure re-export hub.  The content lives in

* `BrauerSuzukiQ8/Reduction.lean` — the group-theoretic reduction of p. 139
* `BrauerSuzukiQ8/CharacterCore.lean` — `q8_exists_proper_normal`, the modular character theory
* `BrauerSuzukiQ8/Induction.lean` — the induction on `|G|` and the final statements
-/
