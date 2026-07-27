/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch08_PermutationGroups.RegularNormal

/-!
# Isaacs, Finite Group Theory — Problems 8A (pp. 235–236)

Isaacs §8A の章末演習。「regular 部分群」は `RegularNormal.lean` の流儀に合わせ
**軌道写像 `smulBase N α : ↥N → Ω` が全単射**であることとして扱う (Thm 8.5)。
半正則 (semiregular) は同じく**軌道写像が単射**、同値に `N ⊓ G_α = ⊥`
(`injective_smulBase_iff_disjoint_stabilizer`)。

## Main results

- `smul_eq_self_of_mem_centralizer`, `centralizer_inf_stabilizer_eq_bot`,
  `bijective_smulBase_top_of_comm` — **Problem 8A.2**: transitive な `H ≤ G` の
  中心化群 `C_G(H)` は半正則。帰結として可換 transitive な置換群は regular。
- `smul_orbit_eq_orbit_smul`, `card_orbit_eq_of_normal` — **Problem 8A.8**:
  transitive な `G` の正規部分群 `N` について `G` は `N`-軌道を推移的に置換し,
  したがって `N` は half-transitive (すべての `N`-軌道が同じ濃度)。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

section /- Problems 8A (pp. 235-236) -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-! ### Problem 8A.2 — 中心化群は半正則 -/

/-- **Isaacs Problem 8A.2** (p. 235) の核心: `H ≤ G` が `Ω` に推移的なら, `C_G(H)` の元は
1 点を固定するだけで全点を固定する。

`β = h • α` (`h ∈ H`) と書き, `c` が `h` と可換なことから
`c • β = c • h • α = h • c • α = h • α = β`。 -/
theorem smul_eq_self_of_mem_centralizer {H : Subgroup G} [IsPretransitive H Ω]
    {c : G} (hc : c ∈ Subgroup.centralizer (H : Set G)) {α : Ω} (hα : c • α = α) (β : Ω) :
    c • β = β := by
  obtain ⟨h, rfl⟩ := exists_smul_eq H α β
  rw [subgroup_smul_def, ← mul_smul,
    ← Subgroup.mem_centralizer_iff.mp hc (h : G) h.2, mul_smul, hα]

/-- **Isaacs Problem 8A.2** (p. 235), 前半: `H ≤ G` が `Ω` に推移的なら `C_G(H)` は
**半正則** — どの点安定化群とも自明にしか交わらない。

置換群 (= 忠実な作用) であることが要る: `smul_eq_self_of_mem_centralizer` は
「全点を固定する」までしか言わず, そこから `c = 1` を出すのに忠実性を使う。 -/
theorem centralizer_inf_stabilizer_eq_bot [FaithfulSMul G Ω] {H : Subgroup G}
    [IsPretransitive H Ω] (α : Ω) :
    Subgroup.centralizer (H : Set G) ⊓ stabilizer G α = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨hc, hα⟩
  rw [Subgroup.mem_bot]
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun β => ?_
  rw [one_smul]
  exact smul_eq_self_of_mem_centralizer hc (mem_stabilizer_iff.mp hα) β

/-- **Isaacs Problem 8A.2** (p. 235), 後半: **可換な推移的置換群は regular**。

可換なので `G = C_G(G)` が半正則 (前半), 推移性と合わせて軌道写像は全単射。 -/
theorem bijective_smulBase_top_of_comm [FaithfulSMul G Ω] [IsPretransitive G Ω]
    (hcomm : ∀ x y : G, x * y = y * x) (α : Ω) :
    Function.Bijective (smulBase (⊤ : Subgroup G) α) := by
  haveI : IsPretransitive (⊤ : Subgroup G) Ω := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨g, hg⟩ := exists_smul_eq G x y
    exact ⟨⟨g, Subgroup.mem_top g⟩, hg⟩
  rw [bijective_smulBase_iff]
  refine ⟨inferInstance, ?_⟩
  have hcentral : (⊤ : Subgroup G) ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) :=
    fun x _ => Subgroup.mem_centralizer_iff.mpr fun y _ => hcomm y x
  refine le_antisymm (le_trans (inf_le_inf_right _ hcentral) ?_) bot_le
  exact le_of_eq (centralizer_inf_stabilizer_eq_bot (H := (⊤ : Subgroup G)) α)

/-! ### Problem 8A.8 — 正規部分群の軌道は推移的に置換される -/

/-- **Isaacs Problem 8A.8** (p. 235): `N ⊴ G` のとき `g` は `N`-軌道を `N`-軌道へ写す:
`g • orbit N α = orbit N (g • α)`。

`N` が正規なので `g * n = (g n g⁻¹) * g` と書き換えられる。 -/
theorem smul_orbit_eq_orbit_smul {N : Subgroup G} [N.Normal] (g : G) (α : Ω) :
    g • orbit N α = orbit N (g • α) := by
  ext x
  constructor
  · rintro ⟨-, ⟨n, rfl⟩, rfl⟩
    refine ⟨⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem ‹N.Normal› (n : G) n.2 g⟩, ?_⟩
    simp only [subgroup_smul_def, ← mul_smul]
    group
  · rintro ⟨n, rfl⟩
    refine ⟨(g⁻¹ * (n : G) * g) • α, ⟨⟨g⁻¹ * (n : G) * g, ?_⟩, rfl⟩, ?_⟩
    · simpa using Subgroup.Normal.conj_mem ‹N.Normal› (n : G) n.2 g⁻¹
    · simp only [subgroup_smul_def, ← mul_smul]
      group

/-- **Isaacs Problem 8A.8** (p. 235) の帰結: `G` が推移的で `N ⊴ G` なら `N` は
**half-transitive** — すべての `N`-軌道が同じ濃度をもつ。

`G` の推移性で `β = g • α` と書き, `g • orbit N α = orbit N β` が全単射を与える。 -/
theorem card_orbit_eq_of_normal [IsPretransitive G Ω] {N : Subgroup G} [N.Normal] (α β : Ω) :
    Nat.card (orbit N α) = Nat.card (orbit N β) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G α β
  rw [← smul_orbit_eq_orbit_smul g α]
  exact Nat.card_congr ((Equiv.Set.image (fun x : Ω => g • x) (orbit N α)
    (MulAction.injective g)).trans (Equiv.setCongr Set.image_smul))

end

end OddOrder.Isaacs.Ch08
