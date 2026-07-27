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
# Isaacs Problems 8A (pp. 235–236) — 剰余類・指数と軌道

**Problems 8A.14 / 8A.15 / 8A.16**。推移作用の軌道を剰余類空間 `G ⧸ H` と
相対指数から数える。

## Main results

- `cosetToOrbit`, `card_orbits_le_index`, `two_mul_card_orbits_le_index` —
  **Problem 8A.14** (後半込み): `G` 推移的で `[G:H] = m` なら
  `H` の軌道は高々 `m` 個 (`gH ↦ ⟦g⁻¹ • α⟧` が `G ⧸ H` からの全射)。
  `H` が点安定化群を含まなければファイバーが常に 2 元以上なので `≤ m / 2`。
- `doubleCoset_transitive_iff` — **Problem 8A.15**: `G` の `H`-剰余類への作用が
  2-transitive ⟺ 二重剰余類が `H` とその外のちょうど 2 つ (= `H × H` の両側作用が
  `G` 上 2 軌道)。
- `stabilizer_subgroupOf`, `relIndex_stabilizer_eq_ncard_orbit`,
  `relIndex_stabilizer_eq_index`, `sub_one_dvd_ncard_orbit_mul_index`,
  `two_transitive_of_coprime_index` — **Problem 8A.16**: `G` が 2-transitive で
  `H ≤ G` が推移的, `[G : H]` が `n - 1` と互いに素なら `H` も 2-transitive。
  核心は `[G_α : H ⊓ G_α] = [G : H]` と相対指数の二通りの分解から出る
  `(n - 1) ∣ |Δ| · [G : H]` (`Δ` は `H ⊓ G_α`-軌道)。
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

/-! ### Problem 8A.16 — 指数が `n - 1` と互いに素な推移的部分群 -/

section CoprimeIndex

/-- 部分群 `K ≤ G` の制限作用による安定化群は, `G` の安定化群の `subgroupOf`。 -/
lemma stabilizer_subgroupOf (K : Subgroup G) (x : Ω) :
    (MulAction.stabilizer G x).subgroupOf K = MulAction.stabilizer ↥K x := by
  ext k
  exact Iff.rfl

/-- **軌道の大きさは相対指数**: 部分群 `K` の下での `x` の軌道は `[K : K ⊓ G_x]` 個の点をもつ。 -/
lemma relIndex_stabilizer_eq_ncard_orbit (K : Subgroup G) (x : Ω) :
    (MulAction.stabilizer G x).relIndex K = (MulAction.orbit ↥K x).ncard := by
  rw [Subgroup.relIndex, stabilizer_subgroupOf, MulAction.index_stabilizer]

/-- `G` も `H ≤ G` も `Ω` に推移的なら **`[G_α : H ⊓ G_α] = [G : H]`**。

`|G| = |G_α| n` と `|H| = |H ⊓ G_α| n` から従う指数の等式で, 二通りの
`[G : H ⊓ G_α]` の分解 (`H` を経由 / `G_α` を経由) を突き合わせて得る。 -/
lemma relIndex_stabilizer_eq_index [Finite Ω] [IsPretransitive G Ω] {H : Subgroup G}
    [IsPretransitive ↥H Ω] (α : Ω) :
    H.relIndex (MulAction.stabilizer G α) = H.index := by
  haveI : Nonempty Ω := ⟨α⟩
  have hn : 0 < Nat.card Ω := Nat.card_pos
  have e1 : (MulAction.stabilizer G α).relIndex H * H.index
      = (H ⊓ MulAction.stabilizer G α).index := by
    rw [← Subgroup.inf_relIndex_left]
    exact Subgroup.relIndex_mul_index inf_le_left
  have e2 : H.relIndex (MulAction.stabilizer G α) * (MulAction.stabilizer G α).index
      = (H ⊓ MulAction.stabilizer G α).index := by
    rw [← Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_mul_index inf_le_right
  rw [Subgroup.relIndex, stabilizer_subgroupOf, MulAction.index_stabilizer_of_transitive] at e1
  rw [MulAction.index_stabilizer_of_transitive] at e2
  exact Nat.eq_of_mul_eq_mul_right hn (e2.trans (e1.symm.trans (mul_comm _ _)))

/-- **8A.16 の数え上げの核心**: `G` が 2-transitive, `H ≤ G` が推移的なら,
`δ ≠ α` の `H ⊓ G_α`-軌道 `Δ` は `(n - 1) ∣ |Δ| · [G : H]` を満たす。

`S = G_δ`, `T = G_α`, `Hα = H ⊓ T` として `[Hα : S ⊓ Hα] · [T : Hα]`
`= [T : S ⊓ Hα] = [S ⊓ T : S ⊓ Hα] · [T : S ⊓ T]` を `Subgroup.relIndex_mul_relIndex`
で二通りに分解する。左端が `|Δ|`, `[T : Hα] = [G : H]`, 右端の `[T : S ⊓ T]` が
`G_α` の `Ω ∖ {α}` 上の軌道 = `n - 1`。 -/
lemma sub_one_dvd_ncard_orbit_mul_index [Finite Ω] [IsPretransitive G Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : G, g • a = c ∧ g • b = d)
    {H : Subgroup G} [IsPretransitive ↥H Ω] {α δ : Ω} (hδ : δ ≠ α) :
    Nat.card Ω - 1 ∣
      (MulAction.orbit ↥(H ⊓ MulAction.stabilizer G α) δ).ncard * H.index := by
  classical
  -- `G_α` の `δ` 上の軌道はちょうど `Ω ∖ {α}`。
  have horb : MulAction.orbit ↥(MulAction.stabilizer G α) δ = ({α}ᶜ : Set Ω) := by
    ext ε
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨t, ht⟩ hcon
      refine hδ (MulAction.injective (t : G) ?_)
      change (t : G) • δ = (t : G) • α
      rw [show (t : G) • α = α from t.2, show (t : G) • δ = ε from ht, hcon]
    · intro hε
      obtain ⟨g, hgα, hgδ⟩ := h2 α δ α ε hδ.symm (Ne.symm hε)
      exact ⟨⟨g, hgα⟩, hgδ⟩
  have hcompl : ({α}ᶜ : Set Ω).ncard = Nat.card Ω - 1 := by
    have := Set.ncard_add_ncard_compl ({α} : Set Ω)
    rw [Set.ncard_singleton] at this
    omega
  -- 相対指数の二通りの分解。
  have c1 : (MulAction.stabilizer G δ ⊓ (H ⊓ MulAction.stabilizer G α)).relIndex
        (H ⊓ MulAction.stabilizer G α)
      * (H ⊓ MulAction.stabilizer G α).relIndex (MulAction.stabilizer G α)
      = (MulAction.stabilizer G δ ⊓ (H ⊓ MulAction.stabilizer G α)).relIndex
        (MulAction.stabilizer G α) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right inf_le_right
  have c2 : (MulAction.stabilizer G δ ⊓ (H ⊓ MulAction.stabilizer G α)).relIndex
        (MulAction.stabilizer G δ ⊓ MulAction.stabilizer G α)
      * (MulAction.stabilizer G δ ⊓ MulAction.stabilizer G α).relIndex
        (MulAction.stabilizer G α)
      = (MulAction.stabilizer G δ ⊓ (H ⊓ MulAction.stabilizer G α)).relIndex
        (MulAction.stabilizer G α) :=
    Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_inf_left _ inf_le_right) inf_le_right
  rw [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right,
    relIndex_stabilizer_eq_ncard_orbit, relIndex_stabilizer_eq_index] at c1
  rw [Subgroup.inf_relIndex_right, relIndex_stabilizer_eq_ncard_orbit, horb, hcompl] at c2
  exact ⟨_, (c1.trans c2.symm).trans (mul_comm _ _)⟩

/-- **Isaacs Problem 8A.16** (p. 236) 🎉: `G` が `Ω` (`|Ω| = n`) に 2-transitive で,
`H ≤ G` が推移的かつ `[G : H]` が `n - 1` と互いに素なら, **`H` も 2-transitive**。

`Δ` を `δ ≠ α` の `H ⊓ G_α`-軌道とすると `(n - 1) ∣ |Δ| · [G : H]`
(`sub_one_dvd_ncard_orbit_mul_index`) なので, 互いに素性から `(n - 1) ∣ |Δ|`。
`Δ ⊆ Ω ∖ {α}` かつ `Δ ≠ ∅` だから `|Δ| = n - 1`, すなわち `H ⊓ G_α` は
`Ω ∖ {α}` に推移的。`H` の推移性と合わせて 2-transitivity になる。 -/
theorem two_transitive_of_coprime_index [Finite Ω] [IsPretransitive G Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : G, g • a = c ∧ g • b = d)
    {H : Subgroup G} [IsPretransitive ↥H Ω]
    (hcop : Nat.Coprime (Nat.card Ω - 1) H.index) :
    ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ h : ↥H, h • a = c ∧ h • b = d := by
  classical
  -- 核心: `H ⊓ G_α` は `Ω ∖ {α}` に推移的。
  have key : ∀ α δ ε : Ω, δ ≠ α → ε ≠ α →
      ∃ k : G, k ∈ H ⊓ MulAction.stabilizer G α ∧ k • δ = ε := by
    intro α δ ε hδ hε
    have hcompl : ({α}ᶜ : Set Ω).ncard = Nat.card Ω - 1 := by
      have := Set.ncard_add_ncard_compl ({α} : Set Ω)
      rw [Set.ncard_singleton] at this
      omega
    have hsub : MulAction.orbit ↥(H ⊓ MulAction.stabilizer G α) δ ⊆ ({α}ᶜ : Set Ω) := by
      intro ε' hmem hcon
      rw [Set.mem_singleton_iff] at hcon
      obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp hmem
      refine hδ (MulAction.injective (k : G) ?_)
      change (k : G) • δ = (k : G) • α
      rw [show (k : G) • α = α from k.2.2, show (k : G) • δ = ε' from hk, hcon]
    have hdvd : Nat.card Ω - 1 ∣
        (MulAction.orbit ↥(H ⊓ MulAction.stabilizer G α) δ).ncard :=
      hcop.dvd_of_dvd_mul_right (sub_one_dvd_ncard_orbit_mul_index h2 hδ)
    have hpos : 0 < (MulAction.orbit ↥(H ⊓ MulAction.stabilizer G α) δ).ncard :=
      Set.ncard_pos (Set.toFinite _) |>.mpr ⟨δ, MulAction.mem_orbit_self δ⟩
    have hle : (MulAction.orbit ↥(H ⊓ MulAction.stabilizer G α) δ).ncard
        ≤ Nat.card Ω - 1 :=
      hcompl ▸ Set.ncard_le_ncard hsub (Set.toFinite _)
    have hcard : (MulAction.orbit ↥(H ⊓ MulAction.stabilizer G α) δ).ncard
        = Nat.card Ω - 1 :=
      le_antisymm hle (Nat.le_of_dvd hpos hdvd)
    have heq : MulAction.orbit ↥(H ⊓ MulAction.stabilizer G α) δ = ({α}ᶜ : Set Ω) :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hcompl, hcard]) (Set.toFinite _)
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp
      (show ε ∈ MulAction.orbit ↥(H ⊓ MulAction.stabilizer G α) δ from heq ▸ hε)
    exact ⟨(k : G), k.2, hk⟩
  intro a b c d hab hcd
  obtain ⟨h₁, hh₁⟩ := MulAction.exists_smul_eq (↥H) a c
  have hne : (h₁ : G) • b ≠ c := by
    intro hc
    refine hab (MulAction.injective (h₁ : G) ?_)
    change (h₁ : G) • a = (h₁ : G) • b
    rw [hc]
    exact hh₁
  obtain ⟨k, hkmem, hk⟩ := key c ((h₁ : G) • b) d hne hcd.symm
  refine ⟨⟨k, hkmem.1⟩ * h₁, ?_, ?_⟩
  · rw [mul_smul, hh₁]
    exact MulAction.mem_stabilizer_iff.mp hkmem.2
  · rw [mul_smul]
    exact hk

end CoprimeIndex

end

end OddOrder.Isaacs.Ch08
