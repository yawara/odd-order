/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.LayerRestriction
import OddOrder.Isaacs.Ch09_MoreSubnormality.PResidual

/-!
# Isaacs Ch. 9 — §9C: Thompson–Wielandt (Theorems 9.23/9.24), p. 283–284

まず `core_H(D)` (相対 normalCore = `D` に含まれ `H` に normal な最大部分群) の infra を
用意する. Theorem 9.24 の statement (`M = core_H(D)`, `N = core_K(D)`, `E = M∩N`,
`U = core_H(E)`, `V = core_K(E)`) と proof で使う.

- `relCore H D` (= `core_H(D)`): `((D.subgroupOf H).normalCore).map H.subtype`.
- `relCore_le` (`≤ D`), `relCore_le_left` (`≤ H`),
  `le_normalizer_relCore` (`H ≤ N_G(core_H(D))`, すなわち `core_H(D)` は `H` に normal),
  `le_relCore` (最大性: `N ≤ D`, `N ≤ H`, `H ≤ N_G(N)` ⇒ `N ≤ core_H(D)`).
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

variable {G : Type*} [Group G]

section /- 9C: relative core `core_H(D)` -/

/-- **`core_H(D)`** (相対 normalCore): `D` に含まれ `H` に normal な最大の部分群.
`↥H` 内の `normalCore` を `H.subtype` で押し出す. -/
def relCore (H D : Subgroup G) : Subgroup G :=
  ((D.subgroupOf H).normalCore).map H.subtype

theorem relCore_le_left (H D : Subgroup G) : relCore H D ≤ H :=
  Subgroup.map_subtype_le _

theorem relCore_le (H D : Subgroup G) : relCore H D ≤ D :=
  (Subgroup.map_mono (Subgroup.normalCore_le _)).trans
    (by rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left)

/-- `core_H(D)` は `H` に normal (`H ≤ N_G(core_H(D))`). -/
theorem le_normalizer_relCore (H D : Subgroup G) :
    H ≤ Subgroup.normalizer (relCore H D : Set G) :=
  le_normalizer_map_subtype_of_normal (Subgroup.normalCore_normal _)

/-- `core_H(D)` の最大性: `N ≤ D`, `N ≤ H`, `N` が `H` に normal (`H ≤ N_G(N)`) なら
`N ≤ core_H(D)`. -/
theorem le_relCore {H D N : Subgroup G} (hND : N ≤ D) (hNH : N ≤ H)
    (hNnorm : H ≤ Subgroup.normalizer (N : Set G)) : N ≤ relCore H D := by
  haveI : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hNnorm
  have h1 : N.subgroupOf H ≤ (D.subgroupOf H).normalCore :=
    Subgroup.normal_le_normalCore.mpr (Subgroup.comap_mono hND)
  calc N = (N.subgroupOf H).map H.subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNH]
    _ ≤ relCore H D := Subgroup.map_mono h1

end

section /- 9C: Theorem 9.24 の仮説と N_G 補題 -/

/-- Thm 9.24 の仮説: `D` の非自明部分群は `H` または `K` を真に含むどの部分群にも
normal でない (`N ◁ L` を `L ≤ N_G(N)` で表す). -/
def NoNormalInSupergroup (H K D : Subgroup G) : Prop :=
  ∀ L : Subgroup G, H < L ∨ K < L →
    ∀ N : Subgroup G, N ≠ ⊥ → N ≤ D → ¬ (L ≤ Subgroup.normalizer (N : Set G))

/-- 仮説から: `N ≤ D` が nonidentity で `H` に normal (`H ≤ N_G(N)`) なら `N_G(N) = H`
(さもなくば `N_G(N) ⊋ H` が仮説に反する). -/
theorem normalizer_eq_left_of_noNormal {H K D : Subgroup G}
    (hyp : NoNormalInSupergroup H K D) {N : Subgroup G} (hN : N ≠ ⊥) (hND : N ≤ D)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup.normalizer (N : Set G) = H := by
  refine le_antisymm ?_ hHN
  by_contra hle
  exact hyp (Subgroup.normalizer (N : Set G))
    (Or.inl (lt_of_le_of_ne hHN fun heq => hle heq.ge)) N hN hND le_rfl

/-- 仮説から (K 版): `N ≤ D` が nonidentity で `K` に normal なら `N_G(N) = K`. -/
theorem normalizer_eq_right_of_noNormal {H K D : Subgroup G}
    (hyp : NoNormalInSupergroup H K D) {N : Subgroup G} (hN : N ≠ ⊥) (hND : N ≤ D)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup.normalizer (N : Set G) = K := by
  refine le_antisymm ?_ hKN
  by_contra hle
  exact hyp (Subgroup.normalizer (N : Set G))
    (Or.inr (lt_of_le_of_ne hKN fun heq => hle heq.ge)) N hN hND le_rfl

end

end OddOrder.Isaacs.Ch09
