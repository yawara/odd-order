/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow

/-!
# The Sylow subgroups containing a given `p`-subgroup

**Navarro (4.22), first part**: for a `p`-subgroup `Q ≤ G` the number of Sylow `p`-subgroups
containing `Q` is `≡ 1 (mod p)`.

`Q` acts on `Syl_p(G)` by conjugation and — for a `p`-subgroup — the fixed points are exactly the
Sylow subgroups *containing* `Q` (`IsPGroup.sylow_mem_fixedPoints_iff`), so this is Sylow's third
theorem plus the orbit count for a `p`-group.

Külshammer's expression `Ĝ_p = ∑_{P ∈ Syl_p(G)} P̂` for the sum of the `p`-elements in
characteristic `p` is the case `Q = ⟨x⟩`: the coefficient of a `p`-element `x` on the right is the
number of Sylow subgroups containing it.

## Main results

* `OddOrder.GroupTheory.card_sylow_containing_modEq_one`
-/

namespace OddOrder.GroupTheory

open MulAction

open scoped Pointwise

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- **Every `p`-element is conjugate into any prescribed Sylow `p`-subgroup.**  It lies in *some*
Sylow `p`-subgroup (`IsPGroup.exists_le_sylow`), and the Sylow `p`-subgroups are conjugate. -/
theorem exists_conj_mem_sylow {x : G} (hx : IsPGroup p (Subgroup.zpowers x)) (P : Sylow p G) :
    ∃ g : G, g * x * g⁻¹ ∈ (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hcoe : (P : Subgroup G) = MulAut.conj g • (Q : Subgroup G) := by rw [← hg]; rfl
  refine ⟨g, ?_⟩
  rw [hcoe, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    show (MulAut.conj g)⁻¹ • (g * x * g⁻¹) = x by
      rw [← map_inv MulAut.conj g]
      change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      group]
  exact hQ (Subgroup.mem_zpowers x)

/-- **Navarro (4.22).**  The number of Sylow `p`-subgroups containing a given `p`-subgroup is
`≡ 1 (mod p)`. -/
theorem card_sylow_containing_modEq_one {Q : Subgroup G} (hQ : IsPGroup p ↥Q) :
    Nat.card {P : Sylow p G // Q ≤ (P : Subgroup G)} ≡ 1 [MOD p] := by
  classical
  have hfix : {P : Sylow p G // Q ≤ (P : Subgroup G)} ≃ fixedPoints ↥Q (Sylow p G) :=
    Equiv.subtypeEquivRight fun P => (hQ.sylow_mem_fixedPoints_iff (Q := P)).symm
  calc Nat.card {P : Sylow p G // Q ≤ (P : Subgroup G)}
      = Nat.card (fixedPoints ↥Q (Sylow p G)) := Nat.card_congr hfix
    _ ≡ Nat.card (Sylow p G) [MOD p] := (hQ.card_modEq_card_fixedPoints _).symm
    _ ≡ 1 [MOD p] := card_sylow_modEq_one p G

/-- The number of Sylow `p`-subgroups containing a fixed `p`-element is `≡ 1 (mod p)`. -/
theorem card_sylow_mem_modEq_one {x : G} (hx : IsPGroup p (Subgroup.zpowers x)) :
    Nat.card {P : Sylow p G // x ∈ (P : Subgroup G)} ≡ 1 [MOD p] := by
  have hequiv : {P : Sylow p G // x ∈ (P : Subgroup G)}
      ≃ {P : Sylow p G // Subgroup.zpowers x ≤ (P : Subgroup G)} :=
    Equiv.subtypeEquivRight fun P => by
      rw [Subgroup.zpowers_le]
  rw [Nat.card_congr hequiv]
  exact card_sylow_containing_modEq_one hx

end OddOrder.GroupTheory
