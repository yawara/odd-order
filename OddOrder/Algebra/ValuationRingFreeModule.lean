/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Module

/-!
# Finite torsion-free modules over a valuation ring are free

Over a principal ideal domain this is the structure theorem for finitely generated modules, and
mathlib has it (`Module.free_of_finite_type_torsion_free'`).  Over a valuation ring — which need
not be Noetherian — it is instead a two-step consequence of two mathlib results:

* a valuation ring is **Bézout**, and over a Bézout domain flatness is exactly torsion-freeness
  (`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`);
* a valuation ring is **local**, and over a local ring a finite flat module is free
  (`Module.free_of_flat_of_isLocalRing`).

The reason this matters here is the splitting `p`-modular system `𝓞_ℂ_[p]`
(`Modular/PadicComplexSystem`): its value group is divisible, so it is not a discrete valuation
ring and not Noetherian, and every appeal to "submodules of free modules over a PID are free" in
the modular theory has to be replaced by the above.

The case the modular theory actually uses is a `G`-invariant lattice inside an ordinary
representation (`Modular/LatticeRepresentation`), which is free and therefore has a rank and a
trace.

## Main results

* `OddOrder.free_of_isTorsionFree` — finite + torsion-free ⟹ free
-/

namespace OddOrder

/-- **A finitely generated torsion-free module over a valuation ring is free.**  Bézout turns
torsion-freeness into flatness and locality turns finite flatness into freeness. -/
theorem free_of_isTorsionFree {R M : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.IsTorsionFree R M] :
    Module.Free R M :=
  have : Module.Flat R M := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  Module.free_of_flat_of_isLocalRing

end OddOrder
