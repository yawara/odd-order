/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.Basic

/-!
# A central Sylow subgroup gives a normal `p`-complement

If a Sylow `p`-subgroup `P` of `G` lies in `Z(G)`, then `C_G(P) = G`, so
`N_G(P) ≤ C_G(P)` and Burnside's transfer theorem
(`hasNormalPComplement_of_sylow_normalizer_le_centralizer`) applies.

The case Brauer–Suzuki uses is `G = C_G(x)` with `⟨x⟩` a Sylow `p`-subgroup of it: `x` is central
in its own centraliser, so its powers are too.  Navarro's proof of the Brauer–Suzuki theorem
invokes this for an element `y` of order `4` of a quaternion Sylow `2`-subgroup — the Sylow
`2`-subgroups of `C_G(y)` cannot have order `8`, because a quaternion group of order `8` has no
central element of order `4`, so `⟨y⟩` is one of them.

## Main results

* `OddOrder.GroupTheory.hasNormalPComplement_of_sylow_le_center`
* `OddOrder.GroupTheory.hasNormalPComplement_centralizer_of_sylow_zpowers`
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs.Ch05 (HasNormalPComplement)

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- **A central Sylow `p`-subgroup gives a normal `p`-complement.**  `C_G(P) = G` because `P` is
central, so Burnside's transfer theorem applies with no further hypothesis. -/
theorem hasNormalPComplement_of_sylow_le_center (P : Sylow p G)
    (hP : (P : Subgroup G) ≤ Subgroup.center G) : HasNormalPComplement p G := by
  refine OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer P ?_
  intro g _
  exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
    ((Subgroup.mem_center_iff.mp (hP hh)) g).symm

/-! ### Unpacking a normal `p`-complement

`HasNormalPComplement p G` says `G = N ⋊ P` for every Sylow `p`-subgroup `P`.  The block theory
consumes that in the form "`p ∤ |N|` and `G/N` is a `p`-group"; both are read off the complement
relation, since `[G : P] = |N|` and `[G : N] = |P|`. -/

/-- **A complement to a Sylow `p`-subgroup has order prime to `p`** — it is `[G : P]`. -/
theorem not_dvd_card_of_isComplement' {N : Subgroup G} (P : Sylow p G)
    (hcomp : Subgroup.IsComplement' N (P : Subgroup G)) : ¬ p ∣ Nat.card ↥N := by
  rw [← hcomp.index_eq_card]
  exact P.not_dvd_index

/-- **The quotient by a normal complement is a `p`-group** — it has the order of `P`. -/
theorem isPGroup_quotient_of_isComplement' {N : Subgroup G} [N.Normal] (P : Sylow p G)
    (hcomp : Subgroup.IsComplement' N (P : Subgroup G)) : IsPGroup p (G ⧸ N) := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  refine IsPGroup.of_card (n := n) ?_
  rw [← Subgroup.index_eq_card, hcomp.symm.index_eq_card, hn]

omit [Finite G] [Fact p.Prime] in
/-- **`⟨x⟩` is central in `C_G(x)`.** -/
theorem zpowers_self_le_center_centralizer (x : G)
    (hx : x ∈ Subgroup.centralizer ({x} : Set G)) :
    Subgroup.zpowers (⟨x, hx⟩ : ↥(Subgroup.centralizer ({x} : Set G)))
      ≤ Subgroup.center ↥(Subgroup.centralizer ({x} : Set G)) := by
  rw [Subgroup.zpowers_le]
  refine Subgroup.mem_center_iff.mpr fun h => ?_
  refine Subtype.ext ?_
  push_cast
  exact ((Subgroup.mem_centralizer_iff.mp h.2) x rfl).symm

/-- **`C_G(x)` has a normal `p`-complement when `⟨x⟩` is one of its Sylow `p`-subgroups.** -/
theorem hasNormalPComplement_centralizer_of_sylow_zpowers (x : G)
    (hx : x ∈ Subgroup.centralizer ({x} : Set G))
    (S : Sylow p ↥(Subgroup.centralizer ({x} : Set G)))
    (hS : (S : Subgroup ↥(Subgroup.centralizer ({x} : Set G)))
      = Subgroup.zpowers (⟨x, hx⟩ : ↥(Subgroup.centralizer ({x} : Set G)))) :
    HasNormalPComplement p ↥(Subgroup.centralizer ({x} : Set G)) := by
  refine hasNormalPComplement_of_sylow_le_center S ?_
  rw [hS]
  exact zpowers_self_le_center_centralizer x hx

end OddOrder.GroupTheory
