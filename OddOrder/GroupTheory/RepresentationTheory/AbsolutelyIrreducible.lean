/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.FDRep
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Absolutely irreducible representations (BG §2 Prop 2.1 scaffold)

`OddOrder.GroupTheory.RepresentationTheory` shared module: scaffold for
**Bender-Glauberman §2 Prop 2.1** infrastructure on absolutely irreducible
representations.  A representation `ρ : G →* (V →ₗ[k] V)` is **absolutely
irreducible** if its scalar extension to the algebraic closure `k̄` remains
irreducible.

## Status

* Skeleton only.  See issue **#33** for the full implementation plan.
* Designed to mirror mathlib `Mathlib.RepresentationTheory.Irreducible` once
  the absolute version is added upstream.

## BG ↔ mathlib mapping

* **BG Prop 2.1(a)** — over an algebraically closed field of characteristic
  not dividing `|G|`, every irreducible representation is absolutely
  irreducible.  In mathlib this is the content of
  `Mathlib.RepresentationTheory.FinGroupCharZero` together with the
  `Mathlib.RepresentationTheory.Irreducible` API.
* **BG Prop 2.1(b)–(d)** — character-theoretic criterion + tensor product
  with the algebraic closure.
-/

namespace OddOrder.RepresentationTheory

end OddOrder.RepresentationTheory
