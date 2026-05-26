/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.FDRep
import Mathlib.GroupTheory.OrderOfElement

/-!
# Two-dimensional representations of odd-order groups (BG §2 Thm 2.6 scaffold)

`OddOrder.GroupTheory.RepresentationTheory` shared module: scaffold for
**Bender-Glauberman §2 Thm 2.6** infrastructure on two-dimensional
representations of finite groups of odd order.

## Status

* Skeleton only.  See issue **#35** for the full implementation plan.

## BG ↔ mathlib mapping

* **BG Thm 2.6** — a finite group of odd order has no faithful
  two-dimensional complex representation.  The proof uses the determinant
  homomorphism to reduce to the `SL(2, ℂ)` situation, then BG Thm 2.5
  (extraspecial faithful, issue #34) plus parity arguments.
* The companion result (used as a stepping stone in BG §3) bounds the
  dimension of any non-trivial faithful complex representation of an
  odd-order group from below.
-/

namespace OddOrder.RepresentationTheory

end OddOrder.RepresentationTheory
