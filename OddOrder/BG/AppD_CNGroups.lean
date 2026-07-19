/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppD_CNGroups.Basic
import OddOrder.BG.AppD_CNGroups.MaximalSylowIntersection
import OddOrder.BG.AppD_CNGroups.SylowTI

/-!
# BG Appendix D: CN-Groups of Odd Order

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix D, pp. 153--156.

Appendix D is a guide to the Feit--Hall--Thompson CN-theorem proof.  It is not part of the main
BG-to-Peterfalvi proof path, but it records two reusable local-analysis consequences for a
**minimal simple** CN-group of odd order.  Both are now proved.

This file is a pure re-export hub; the content lives in the leaves:

* `OddOrder.BG.AppD_CNGroups.Basic` — `IsCNGroup`, the standing hypothesis
  `MinimalSimpleCNHypothesis`, and its elementary consequences (CN passes to subgroups,
  `O_p(G) = 1`, `G' = G`).
* `OddOrder.BG.AppD_CNGroups.MaximalSylowIntersection` — the local analysis: with
  `N = N_G(Z(L(P)))`, the subgroup `N` is a 3-step group with respect to `p` and every Sylow
  `p`-subgroup `R ≠ P` satisfies `P ∩ R ≤ O_p(N)`.  This is BG's display (D.2).
* `OddOrder.BG.AppD_CNGroups.SylowTI` — **Lemma D.1** (`sylow_eq_of_nontrivial_inter`) and
  **Lemma D.2** (`sylow_le_commutator_normalizer`).

⚠ Do **not** discharge the Appendix D lemmas vacuously from `feitThompson`.  The CN-theorem is an
*input* to Feit--Thompson (BG p. 153: it "is actually needed in **FT**, although not for the part
covered by this book"), so deriving Appendix D from `feitThompson` would invert the mathematical
dependency order and produce contentless declarations.
-/
