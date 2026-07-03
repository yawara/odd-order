/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S09_FrobeniusHypothesis76
import OddOrder.Peterfalvi.S08_CoherenceTheorems

/-!
# Peterfalvi (6.8) coherence for a Frobenius family — wiring the Sibley datum

The (6.8) coherence capstone `S08.sibleySetup_is_coherent` (sorry-free) produces the coherent
extension `ν` (an `IsCoherent`) for the induced family `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` from a
`S08.SibleyDadeHypothesis`.  Its Frobenius case (c1) is the intended Peterfalvi (7.10) producer.  This
leaf wires the `FrobeniusFamily` (7.10) hypothesis to a `SibleyDadeHypothesis`, unlocking `ν` for the
(7.8.b)/(7.9) character estimates of `card_G0_lower_bound` (issue 0044).

Foundational coordinate lemma first: the Sibley kernel `(H_i).subgroupOf L_i : Subgroup ↥L_i` has
`sharpImage` equal to `(H_i)^# = sharp (H_i)`, matching the `of_isTISubset` Dade support.
-/

namespace OddOrder.Peterfalvi.S09

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **The Sibley kernel's sharp image is the Frobenius kernel's sharp set.**  For the `i`-th member,
`sharpImage ((H_i).subgroupOf L_i) = (H_i)^#`: since `H_i ≤ L_i`, mapping `(H_i).subgroupOf L_i` back
through `L_i.subtype` recovers `H_i`, and `sharpImage`/`sharp` both remove the identity.  This aligns
the `SibleyDadeHypothesis` support coordinate (a subgroup of `↥L_i`) with the `of_isTISubset` /
`hypothesis71` support `sharp (H_i)` (a subset of `G`). -/
lemma sharpImage_subgroupOf_eq (F : FrobeniusFamily G k) (i : Fin k) :
    OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))
      = OddOrder.Peterfalvi.S04.sharp (F.H i : Set G) := by
  have hmap : Subgroup.map (F.L i).subtype ((F.H i).subgroupOf (F.L i)) = F.H i := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (F.kernel_le i)]
  rw [OddOrder.Peterfalvi.S08.sharpImage, hmap]
  rfl

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
