/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

/-!
# Isaacs Problems 8A (pp. 235–236) — 剰余類と軌道

**Problems 8A.14 / 8A.15**。推移作用の軌道を剰余類空間 `G ⧸ H` から数える。

## Main results

- `cosetToOrbit`, `card_orbits_le_index`, `two_mul_card_orbits_le_index` —
  **Problem 8A.14** (後半込み): `G` 推移的で `[G:H] = m` なら
  `H` の軌道は高々 `m` 個 (`gH ↦ ⟦g⁻¹ • α⟧` が `G ⧸ H` からの全射)。
  `H` が点安定化群を含まなければファイバーが常に 2 元以上なので `≤ m / 2`。
- `doubleCoset_transitive_iff` — **Problem 8A.15**: `G` の `H`-剰余類への作用が
  2-transitive ⟺ 二重剰余類が `H` とその外のちょうど 2 つ (= `H × H` の両側作用が
  `G` 上 2 軌道)。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

section /- Problems 8A (pp. 235-236) -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-! ### Problem 8A.14 — 部分群の軌道数は指数以下 -/

/-- **Isaacs Problem 8A.14** (p. 236) 前半: `G` が `Ω` に推移的で `[G : H] = m` なら,
`H` の `Ω` 上の軌道は高々 `m` 個。

`gH ↦ ⟦g⁻¹ • α⟧` が `G ⧸ H` から `H`-軌道の集合への**全射**になる:
`b = a h` (`h ∈ H`) なら `b⁻¹ • α = h⁻¹ • (a⁻¹ • α)` で同じ `H`-軌道, また `G` の推移性から
任意の `ω = g • α` は `g⁻¹H` の像。 -/
def cosetToOrbit (H : Subgroup G) (α : Ω) :
    G ⧸ H → MulAction.orbitRel.Quotient H Ω :=
  Quotient.lift (fun g : G => (Quotient.mk'' ((g : G)⁻¹ • α) :
      MulAction.orbitRel.Quotient H Ω)) (by
    intro a b hab
    have hmem : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    refine Quotient.sound' (MulAction.orbitRel_apply.mpr ⟨⟨a⁻¹ * b, hmem⟩, ?_⟩)
    change ((a⁻¹ * b : G)) • ((b : G)⁻¹ • α) = (a : G)⁻¹ • α
    rw [← mul_smul]
    group)

@[simp] lemma cosetToOrbit_mk (H : Subgroup G) (α : Ω) (g : G) :
    cosetToOrbit H α (Quotient.mk'' g) = Quotient.mk'' ((g : G)⁻¹ • α) := rfl

lemma cosetToOrbit_surjective [IsPretransitive G Ω] (H : Subgroup G) (α : Ω) :
    Function.Surjective (cosetToOrbit H α) := by
  refine Quotient.ind' fun ω => ?_
  obtain ⟨g, hg⟩ := exists_smul_eq G α ω
  refine ⟨Quotient.mk'' g⁻¹, ?_⟩
  change (Quotient.mk'' ((g⁻¹ : G)⁻¹ • α) : MulAction.orbitRel.Quotient H Ω)
    = Quotient.mk'' ω
  rw [inv_inv, hg]

theorem card_orbits_le_index [Finite G] [Finite Ω] [IsPretransitive G Ω]
    (H : Subgroup G) (α : Ω) :
    Nat.card (MulAction.orbitRel.Quotient H Ω) ≤ H.index := by
  classical
  rw [Subgroup.index_eq_card]
  exact Nat.card_le_card_of_surjective _ (cosetToOrbit_surjective H α)

/-- 8A.14 後半の核: `H` が点安定化群 `G_{a⁻¹ • α}` を含まないなら, `aH` と同じ
`H`-軌道を与える別の剰余類 `bH ≠ aH` がある。

`u ∈ a⁻¹ G_α a ∖ H` を取り `b := a u⁻¹` とすると `bH ≠ aH` で
`b⁻¹ • α = u a⁻¹ • α = a⁻¹ • α`。 -/
theorem exists_ne_coset_same_orbit {H : Subgroup G} {α : Ω} (a : G)
    (hns : ¬ (∀ g ∈ MulAction.stabilizer G ((a : G)⁻¹ • α), g ∈ H)) :
    ∃ b : G, (b : G)⁻¹ • α = (a : G)⁻¹ • α ∧ a⁻¹ * b ∉ H := by
  simp only [not_forall] at hns
  obtain ⟨u, hu, huH⟩ := hns
  refine ⟨a * u⁻¹, ?_, ?_⟩
  · rw [mul_inv_rev, inv_inv, mul_smul]
    exact MulAction.mem_stabilizer_iff.mp hu
  · intro hc
    exact huH (by simpa using H.inv_mem hc)

/-- **Isaacs Problem 8A.14** (p. 236) 後半: `H` がどの点安定化群も含まないなら,
`H` の `Ω` 上の軌道は高々 `m/2` 個 (`2 · 軌道数 ≤ [G:H]`)。

全射 `cosetToOrbit` のファイバーが常に 2 元以上 (`exists_ne_coset_same_orbit`) なので,
`|G ⧸ H| = ∑_o |fiber o| ≥ 2 · 軌道数`。 -/
theorem two_mul_card_orbits_le_index [Finite G] [Finite Ω] [IsPretransitive G Ω]
    (H : Subgroup G) (α : Ω) (hns : ∀ ω : Ω, ¬ (MulAction.stabilizer G ω ≤ H)) :
    2 * Nat.card (MulAction.orbitRel.Quotient H Ω) ≤ H.index := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient H Ω) := Fintype.ofFinite _
  have hfib : ∀ o : MulAction.orbitRel.Quotient H Ω,
      2 ≤ (Finset.univ.filter fun c => cosetToOrbit H α c = o).card := by
    intro o
    obtain ⟨c, hc⟩ := cosetToOrbit_surjective H α o
    induction c using Quotient.ind' with
    | _ a =>
      obtain ⟨b, hbα, hbH⟩ := exists_ne_coset_same_orbit (H := H) a (hns ((a : G)⁻¹ • α))
      refine Finset.one_lt_card.mpr ⟨Quotient.mk'' a, by simp [hc], Quotient.mk'' b, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, cosetToOrbit_mk, hbα]
        exact hc
      · exact fun hab => hbH (QuotientGroup.leftRel_apply.mp (Quotient.exact' hab))
  calc 2 * Nat.card (MulAction.orbitRel.Quotient H Ω)
      = ∑ _o : MulAction.orbitRel.Quotient H Ω, 2 := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card,
          mul_comm]
    _ ≤ ∑ o : MulAction.orbitRel.Quotient H Ω,
          (Finset.univ.filter fun c => cosetToOrbit H α c = o).card :=
        Finset.sum_le_sum fun o _ => hfib o
    _ = Fintype.card (G ⧸ H) :=
        (Finset.card_eq_sum_card_fiberwise fun c _ => Finset.mem_univ _).symm
    _ = H.index := by rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]

/-! ### Problem 8A.15 — 剰余類への 2-transitivity と二重剰余類 -/

/-- **Isaacs Problem 8A.15** (p. 236): `G` の `H`-剰余類への作用が 2-transitive ⟺
`H × H` の両側作用 `g · (x,y) = x⁻¹ g y` が `G` 上ちょうど 2 軌道をもつ。

`H × H`-軌道は**二重剰余類** `H g H` そのもので, そのひとつは `H` 自身。よって
「ちょうど 2 軌道」= 「`H` の外がひとつの二重剰余類」であり, これが本補題の左辺。
右辺は「点安定化群 `G_{1·H} = H` が `(G ⧸ H) ∖ {H}` に推移的」= 2-transitivity。 -/
theorem doubleCoset_transitive_iff (H : Subgroup G) :
    (∀ a b : G, a ∉ H → b ∉ H → ∃ x ∈ H, ∃ y ∈ H, x * a * y = b) ↔
      (∀ a b : G, (a : G ⧸ H) ≠ ((1 : G) : G ⧸ H) → (b : G ⧸ H) ≠ ((1 : G) : G ⧸ H) →
        ∃ h ∈ H, h • (a : G ⧸ H) = (b : G ⧸ H)) := by
  have hone : ∀ a : G, ((a : G ⧸ H) = ((1 : G) : G ⧸ H)) ↔ a ∈ H := by
    intro a
    rw [QuotientGroup.eq, mul_one, H.inv_mem_iff]
  constructor
  · intro h a b ha hb
    obtain ⟨x, hx, y, hy, hxy⟩ := h a b (fun hc => ha ((hone a).mpr hc))
      (fun hc => hb ((hone b).mpr hc))
    refine ⟨x, hx, ?_⟩
    rw [show x • (a : G ⧸ H) = ((x * a : G) : G ⧸ H) from rfl, QuotientGroup.eq]
    have hy' : (x * a)⁻¹ * b = y := by rw [← hxy]; group
    rw [hy']
    exact hy
  · intro h a b ha hb
    obtain ⟨x, hx, hxa⟩ := h a b (fun hc => ha ((hone a).mp hc)) (fun hc => hb ((hone b).mp hc))
    rw [show x • (a : G ⧸ H) = ((x * a : G) : G ⧸ H) from rfl, QuotientGroup.eq] at hxa
    exact ⟨x, hx, (x * a)⁻¹ * b, hxa, by group⟩

end

end OddOrder.Isaacs.Ch08
