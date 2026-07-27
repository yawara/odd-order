/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Problems

/-!
# Isaacs Problems 8A (pp. 235–236) — 置換指標のべき乗平均

**Problems 8A.12 / 8A.13**。Burnside の軌道数公式を積作用 `Ω × Ω`, `Ω × Ω × Ω` に
適用して, 置換指標 `χ(g) = |Fix(g)|` の 2 乗・3 乗の平均を軌道数に翻訳する。

## Main results

- `card_fixedBy_prod`, `sum_sq_card_fixedBy`, `card_orbits_prod_eq_two_iff`,
  `sum_sq_card_fixedBy_eq_two_mul_iff` — **Problem 8A.12**: 推移的な `G` について
  `G` が 2-transitive ⟺ 置換指標の 2 乗の平均が 2。
- `card_fixedBy_prod_three`, `sum_cube_card_fixedBy` — **Problem 8A.13** の骨格:
  置換指標の 3 乗和は `Ω³` 上の軌道数 × `|G|`。
- `cube_orbit_diag`, `cube_orbit_pattern_xxz` / `_xzx` / `_zxx`,
  `cube_orbit_pattern_distinct` — **Problem 8A.13**: `Ω³` の 5 つの一致パターンが
  (2-transitive / 3-transitive の下で) それぞれ単一軌道であること。
- `cube_orbit_ne_of_fst_snd` / `_fst_thd` / `_snd_thd` — 一致パターンは軌道不変量
  なので, 上の 5 つの代表元は互いに別軌道。
- `card_orbits_cube_eq_five_iff`, `sum_cube_card_fixedBy_eq_five_mul_iff` —
  **Problem 8A.13**: 2-transitive な `G` と `|Ω| ≥ 3` について
  `G` が 3-transitive ⟺ 置換指標の 3 乗の平均が **5**。すなわち求める `m` は **5**
  (3 点の一致パターン `xxx` / `xxz` / `xzx` / `zxx` / 全相異)。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

section /- Problems 8A (pp. 235-236) -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-! ### Problem 8A.12 — 置換指標の 2 乗平均 -/

/-- 積作用の固定点集合は各成分の固定点集合の積。 -/
def fixedByProdEquiv {A B : Type*} [MulAction G A] [MulAction G B] (g : G) :
    (MulAction.fixedBy (A × B) g) ≃ (MulAction.fixedBy A g) × (MulAction.fixedBy B g) where
  toFun p := (⟨p.1.1, congrArg Prod.fst p.2⟩, ⟨p.1.2, congrArg Prod.snd p.2⟩)
  invFun q := ⟨(q.1.1, q.2.1), Prod.ext q.1.2 q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- 置換指標の 2 乗は積作用 `Ω × Ω` の置換指標。 -/
theorem card_fixedBy_prod (g : G) :
    Nat.card (MulAction.fixedBy (Ω × Ω) g) = Nat.card (MulAction.fixedBy Ω g) ^ 2 := by
  rw [Nat.card_congr (fixedByProdEquiv (A := Ω) (B := Ω) g), Nat.card_prod, sq]

/-- 置換指標の 3 乗は `Ω × Ω × Ω` の置換指標。 -/
theorem card_fixedBy_prod_three (g : G) :
    Nat.card (MulAction.fixedBy (Ω × Ω × Ω) g) = Nat.card (MulAction.fixedBy Ω g) ^ 3 := by
  rw [Nat.card_congr (fixedByProdEquiv (A := Ω) (B := Ω × Ω) g), Nat.card_prod,
    card_fixedBy_prod]
  ring

/-- **Isaacs Problem 8A.12** (p. 236) の骨格: **置換指標 `χ` の 2 乗和は
`Ω × Ω` 上の軌道数 × `|G|`**。したがって `χ(g)²` の平均値は `Ω × Ω` 上の軌道数に等しい。

`χ²` は積作用の置換指標 (`card_fixedBy_prod`) なので, Burnside の補題
(`Ch01.sum_card_fixedBy_nat`) をそのまま `Ω × Ω` に適用すればよい。あとは
「`G` が 2-transitive ⟺ `Ω × Ω` の軌道がちょうど 2 個 (対角線とその外)」を見ればよい。 -/
theorem sum_sq_card_fixedBy [Fintype G] [Finite Ω] :
    ∑ g : G, Nat.card (MulAction.fixedBy Ω g) ^ 2
      = Nat.card (MulAction.orbitRel.Quotient G (Ω × Ω)) * Nat.card G := by
  rw [← OddOrder.Isaacs.Ch01.sum_card_fixedBy_nat (M := G) (β := Ω × Ω)]
  exact (Finset.sum_congr rfl fun g _ => card_fixedBy_prod g).symm

/-- **Isaacs Problem 8A.13** (p. 236) の骨格: 置換指標の 3 乗和は `Ω × Ω × Ω` 上の
軌道数 × `|G|`。

`G` が 3-transitive のとき `Ω³` の軌道は **5 個** — 3 点の一致パターン
(`xxx` / `xxy` / `xyx` / `yxx` / 全相異) がちょうど軌道に対応する (退化 4 パターンは
2-transitivity だけで各 1 軌道)。したがって求める `m` は **5**。 -/
theorem sum_cube_card_fixedBy [Fintype G] [Finite Ω] :
    ∑ g : G, Nat.card (MulAction.fixedBy Ω g) ^ 3
      = Nat.card (MulAction.orbitRel.Quotient G (Ω × Ω × Ω)) * Nat.card G := by
  rw [← OddOrder.Isaacs.Ch01.sum_card_fixedBy_nat (M := G) (β := Ω × Ω × Ω)]
  exact (Finset.sum_congr rfl fun g _ => card_fixedBy_prod_three g).symm

/-! #### `Ω³` の 5 つの一致パターン (8A.13) -/

section CubeOrbits

/-- 推移性: 対角線の点 `(x,x,x)` はすべて同一軌道。 -/
lemma cube_orbit_diag [IsPretransitive G Ω] (α x : Ω) :
    (Quotient.mk'' (x, x, x) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      = Quotient.mk'' (α, α, α) := by
  obtain ⟨g, hg⟩ := exists_smul_eq G α x
  exact Quotient.sound' (MulAction.orbitRel_apply.mpr ⟨g, by simp [hg]⟩)

/-- 2-transitivity: パターン `(x,x,z)` (`x ≠ z`) はすべて同一軌道。 -/
lemma cube_orbit_pattern_xxz
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : G, g • a = c ∧ g • b = d)
    {α β : Ω} (hαβ : α ≠ β) {x z : Ω} (hxz : x ≠ z) :
    (Quotient.mk'' (x, x, z) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      = Quotient.mk'' (α, α, β) := by
  obtain ⟨g, hg1, hg2⟩ := h2 α β x z hαβ hxz
  exact Quotient.sound' (MulAction.orbitRel_apply.mpr ⟨g, by simp [hg1, hg2]⟩)

/-- 2-transitivity: パターン `(x,z,x)` (`x ≠ z`) はすべて同一軌道。 -/
lemma cube_orbit_pattern_xzx
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : G, g • a = c ∧ g • b = d)
    {α β : Ω} (hαβ : α ≠ β) {x z : Ω} (hxz : x ≠ z) :
    (Quotient.mk'' (x, z, x) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      = Quotient.mk'' (α, β, α) := by
  obtain ⟨g, hg1, hg2⟩ := h2 α β x z hαβ hxz
  exact Quotient.sound' (MulAction.orbitRel_apply.mpr ⟨g, by simp [hg1, hg2]⟩)

/-- 2-transitivity: パターン `(z,x,x)` (`x ≠ z`) はすべて同一軌道。 -/
lemma cube_orbit_pattern_zxx
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : G, g • a = c ∧ g • b = d)
    {α β : Ω} (hαβ : α ≠ β) {x z : Ω} (hxz : x ≠ z) :
    (Quotient.mk'' (z, x, x) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      = Quotient.mk'' (β, α, α) := by
  obtain ⟨g, hg1, hg2⟩ := h2 α β x z hαβ hxz
  exact Quotient.sound' (MulAction.orbitRel_apply.mpr ⟨g, by simp [hg1, hg2]⟩)

/-- 3-transitivity: 相異なる 3 点の三つ組はすべて同一軌道。 -/
lemma cube_orbit_pattern_distinct
    (h3 : ∀ a b c x y z : Ω, a ≠ b → a ≠ c → b ≠ c → x ≠ y → x ≠ z → y ≠ z →
      ∃ g : G, g • a = x ∧ g • b = y ∧ g • c = z)
    {α β γ : Ω} (h1 : α ≠ β) (h2' : α ≠ γ) (h3' : β ≠ γ)
    {x y z : Ω} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (Quotient.mk'' (x, y, z) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      = Quotient.mk'' (α, β, γ) := by
  obtain ⟨g, hg1, hg2, hg3⟩ := h3 α β γ x y z h1 h2' h3' hxy hxz hyz
  exact Quotient.sound'
    (MulAction.orbitRel_apply.mpr ⟨g, by simp [hg1, hg2, hg3]⟩)

/-! 一致パターンは軌道不変量 — 以下の 3 本で 5 つの代表元が互いに別軌道だと分かる。 -/

/-- 第 1・第 2 成分の一致は軌道不変。 -/
lemma cube_orbit_ne_of_fst_snd {p q : Ω × Ω × Ω} (hp : p.1 = p.2.1) (hq : q.1 ≠ q.2.1) :
    (Quotient.mk'' p : MulAction.orbitRel.Quotient G (Ω × Ω × Ω)) ≠ Quotient.mk'' q := by
  intro hc
  rw [Quotient.eq''] at hc
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp hc
  have hg' : g • q = p := hg
  refine hq (MulAction.injective g ?_)
  change g • q.1 = g • q.2.1
  rw [show g • q.1 = p.1 from congrArg Prod.fst hg',
    show g • q.2.1 = p.2.1 from congrArg (fun r => (Prod.snd r).1) hg', hp]

/-- 第 1・第 3 成分の一致は軌道不変。 -/
lemma cube_orbit_ne_of_fst_thd {p q : Ω × Ω × Ω} (hp : p.1 = p.2.2) (hq : q.1 ≠ q.2.2) :
    (Quotient.mk'' p : MulAction.orbitRel.Quotient G (Ω × Ω × Ω)) ≠ Quotient.mk'' q := by
  intro hc
  rw [Quotient.eq''] at hc
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp hc
  have hg' : g • q = p := hg
  refine hq (MulAction.injective g ?_)
  change g • q.1 = g • q.2.2
  rw [show g • q.1 = p.1 from congrArg Prod.fst hg',
    show g • q.2.2 = p.2.2 from congrArg (fun r => (Prod.snd r).2) hg', hp]

/-- 第 2・第 3 成分の一致は軌道不変。 -/
lemma cube_orbit_ne_of_snd_thd {p q : Ω × Ω × Ω} (hp : p.2.1 = p.2.2) (hq : q.2.1 ≠ q.2.2) :
    (Quotient.mk'' p : MulAction.orbitRel.Quotient G (Ω × Ω × Ω)) ≠ Quotient.mk'' q := by
  intro hc
  rw [Quotient.eq''] at hc
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp hc
  have hg' : g • q = p := hg
  refine hq (MulAction.injective g ?_)
  change g • q.2.1 = g • q.2.2
  rw [show g • q.2.1 = p.2.1 from congrArg (fun r => (Prod.snd r).1) hg',
    show g • q.2.2 = p.2.2 from congrArg (fun r => (Prod.snd r).2) hg', hp]

end CubeOrbits

/-- **Isaacs Problem 8A.12** (p. 236) の組合せ部分: 推移的な `G` について
**`Ω × Ω` の `G`-軌道がちょうど 2 個 ⟺ `G` は 2-transitive**。

軌道は「対角線」と「対角線の外」の 2 つ。対角線の類には対角線上の点しか入らないので,
2-transitivity は「対角線外がひとつの軌道」と同値。 -/
theorem card_orbits_prod_eq_two_iff [IsPretransitive G Ω] [Nontrivial Ω] :
    Nat.card (MulAction.orbitRel.Quotient G (Ω × Ω)) = 2 ↔
      ∀ β₁ β₂ γ₁ γ₂ : Ω, β₁ ≠ β₂ → γ₁ ≠ γ₂ → ∃ g : G, g • β₁ = γ₁ ∧ g • β₂ = γ₂ := by
  classical
  obtain ⟨α, β, hαβ⟩ := exists_pair_ne Ω
  have hdiag : ∀ x y : Ω, (Quotient.mk'' (x, y) : MulAction.orbitRel.Quotient G (Ω × Ω))
      = Quotient.mk'' (α, α) → x = y := by
    intro x y h
    rw [Quotient.eq''] at h
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp h
    have hg' : g • ((α : Ω), (α : Ω)) = (x, y) := hg
    exact (congrArg Prod.fst hg').symm.trans (congrArg Prod.snd hg')
  have hmk : ∀ p q : Ω × Ω, (∃ g : G, g • p = q) →
      (Quotient.mk'' q : MulAction.orbitRel.Quotient G (Ω × Ω)) = Quotient.mk'' p := by
    intro p q hpq
    rw [Quotient.eq'']
    exact MulAction.orbitRel_apply.mpr hpq
  constructor
  · -- 2 軌道 ⟹ 2-transitive
    intro hcard β₁ β₂ γ₁ γ₂ hβ hγ
    obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.mp hcard
    have hmem : ∀ q : MulAction.orbitRel.Quotient G (Ω × Ω), q = x ∨ q = y := fun q => by
      have hq : q ∈ ({x, y} : Set _) := huniv ▸ Set.mem_univ q
      simpa using hq
    have hoff : ∀ (b₁ b₂ : Ω), b₁ ≠ b₂ →
        (Quotient.mk'' (b₁, b₂) : MulAction.orbitRel.Quotient G (Ω × Ω))
          ≠ Quotient.mk'' (α, α) := fun b₁ b₂ hb hc => hb (hdiag b₁ b₂ hc)
    have hsame : (Quotient.mk'' (γ₁, γ₂) : MulAction.orbitRel.Quotient G (Ω × Ω))
        = Quotient.mk'' (β₁, β₂) := by
      rcases hmem (Quotient.mk'' (α, α)) with hα | hα <;>
        rcases hmem (Quotient.mk'' (β₁, β₂)) with hβ' | hβ' <;>
        rcases hmem (Quotient.mk'' (γ₁, γ₂)) with hγ' | hγ' <;>
        first
          | (exact hγ'.trans hβ'.symm)
          | (exact absurd (hβ'.trans hα.symm) (hoff β₁ β₂ hβ))
          | (exact absurd (hγ'.trans hα.symm) (hoff γ₁ γ₂ hγ))
    rw [Quotient.eq''] at hsame
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp hsame
    have hg' : g • (β₁, β₂) = (γ₁, γ₂) := hg
    exact ⟨g, congrArg Prod.fst hg', congrArg Prod.snd hg'⟩
  · -- 2-transitive ⟹ 2 軌道
    intro h2
    refine Nat.card_eq_two_iff.mpr ⟨Quotient.mk'' (α, α), Quotient.mk'' (α, β),
      fun hc => hαβ (hdiag α β hc.symm), Set.eq_univ_iff_forall.mpr ?_⟩
    refine Quotient.ind' fun p => ?_
    rcases eq_or_ne p.1 p.2 with hp | hp
    · obtain ⟨g, hg⟩ := exists_smul_eq G α p.1
      exact Set.mem_insert_iff.mpr (Or.inl (hmk (α, α) p ⟨g, Prod.ext hg (hg.trans hp)⟩))
    · obtain ⟨g, hg1, hg2⟩ := h2 α β p.1 p.2 hαβ hp
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr
        (hmk (α, β) p ⟨g, Prod.ext hg1 hg2⟩)))

/-- **Isaacs Problem 8A.12** (p. 236) 🎉: 推移的な `G` について
**`G` が 2-transitive ⟺ 置換指標 `χ` の 2 乗の平均値が 2**
(`∑_{g} χ(g)² = 2 |G|`)。

`χ²` は積作用 `Ω × Ω` の置換指標なので, Burnside より `∑ χ² = (Ω×Ω の軌道数)·|G|`。
軌道数が 2 であることが 2-transitivity と同値 (`card_orbits_prod_eq_two_iff`)。 -/
theorem sum_sq_card_fixedBy_eq_two_mul_iff [Fintype G] [Finite Ω] [IsPretransitive G Ω]
    [Nontrivial Ω] :
    (∑ g : G, Nat.card (MulAction.fixedBy Ω g) ^ 2) = 2 * Nat.card G ↔
      ∀ β₁ β₂ γ₁ γ₂ : Ω, β₁ ≠ β₂ → γ₁ ≠ γ₂ → ∃ g : G, g • β₁ = γ₁ ∧ g • β₂ = γ₂ := by
  rw [sum_sq_card_fixedBy, ← card_orbits_prod_eq_two_iff]
  exact ⟨fun h => Nat.eq_of_mul_eq_mul_right Nat.card_pos h, fun h => by rw [h]⟩

/-! #### `Ω³` の軌道数はちょうど 5 (8A.13 の答 `m = 5`) -/

/-- **Isaacs Problem 8A.13** (p. 236) の組合せ部分: 2-transitive な `G` と 3 点以上の `Ω`
について **`Ω³` の `G`-軌道がちょうど 5 個 ⟺ `G` は 3-transitive**。

`Ω³` の点は 3 成分の一致パターン `xxx` / `xxz` / `xzx` / `zxx` / 全相異 の 5 種に分かれ,
一致パターンは軌道不変量なので (`cube_orbit_ne_of_fst_snd` 等) 異なるパターンは異なる軌道。
退化した 4 パターンは 2-transitivity だけで各々ひとつの軌道になる
(`cube_orbit_diag`, `cube_orbit_pattern_xxz` / `_xzx` / `_zxx`) ので, 5 軌道であることの
実質的な内容は「全相異のパターンがひとつの軌道」= 3-transitivity に尽きる。

⚠ `|Ω| ≥ 3` は必須: `|Ω| = 2` なら全相異の三つ組が存在せず軌道数は 4 になる。 -/
theorem card_orbits_cube_eq_five_iff [IsPretransitive G Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : G, g • a = c ∧ g • b = d)
    {α β γ : Ω} (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) :
    Nat.card (MulAction.orbitRel.Quotient G (Ω × Ω × Ω)) = 5 ↔
      ∀ a b c x y z : Ω, a ≠ b → a ≠ c → b ≠ c → x ≠ y → x ≠ z → y ≠ z →
        ∃ g : G, g • a = x ∧ g • b = y ∧ g • c = z := by
  classical
  -- 5 つの代表元は互いに別軌道 (10 通りすべて一致パターンで区別できる)。
  have h01 : (Quotient.mk'' (α, α, α) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      ≠ Quotient.mk'' (α, α, β) := cube_orbit_ne_of_snd_thd rfl hαβ
  have h02 : (Quotient.mk'' (α, α, α) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      ≠ Quotient.mk'' (α, β, α) := cube_orbit_ne_of_fst_snd rfl hαβ
  have h03 : (Quotient.mk'' (α, α, α) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      ≠ Quotient.mk'' (β, α, α) := cube_orbit_ne_of_fst_snd rfl hαβ.symm
  have h04 : (Quotient.mk'' (α, α, α) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      ≠ Quotient.mk'' (α, β, γ) := cube_orbit_ne_of_fst_snd rfl hαβ
  have h12 : (Quotient.mk'' (α, α, β) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      ≠ Quotient.mk'' (α, β, α) := cube_orbit_ne_of_fst_snd rfl hαβ
  have h13 : (Quotient.mk'' (α, α, β) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      ≠ Quotient.mk'' (β, α, α) := cube_orbit_ne_of_fst_snd rfl hαβ.symm
  have h14 : (Quotient.mk'' (α, α, β) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      ≠ Quotient.mk'' (α, β, γ) := cube_orbit_ne_of_fst_snd rfl hαβ
  have h23 : (Quotient.mk'' (α, β, α) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      ≠ Quotient.mk'' (β, α, α) := cube_orbit_ne_of_fst_thd rfl hαβ.symm
  have h24 : (Quotient.mk'' (α, β, α) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      ≠ Quotient.mk'' (α, β, γ) := cube_orbit_ne_of_fst_thd rfl hαγ
  have h34 : (Quotient.mk'' (β, α, α) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
      ≠ Quotient.mk'' (α, β, γ) := cube_orbit_ne_of_snd_thd rfl hβγ
  have hncard : ({Quotient.mk'' (α, α, α), Quotient.mk'' (α, α, β), Quotient.mk'' (α, β, α),
      Quotient.mk'' (β, α, α), Quotient.mk'' (α, β, γ)} :
      Set (MulAction.orbitRel.Quotient G (Ω × Ω × Ω))).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [h01, h02, h03, h04]),
      Set.ncard_insert_of_notMem (by simp [h12, h13, h14]),
      Set.ncard_insert_of_notMem (by simp [h23, h24]),
      Set.ncard_insert_of_notMem (by simp [h34]), Set.ncard_singleton]
  constructor
  · -- 5 軌道 ⟹ 3-transitive: 5 つの代表元が全体を尽くすので, 全相異の三つ組は
    -- 退化パターンのどの代表元とも別軌道 ⟹ 第 5 の軌道にしか行けない。
    intro hcard a b c x y z hab hac hbc hxy hxz hyz
    haveI : Finite (MulAction.orbitRel.Quotient G (Ω × Ω × Ω)) :=
      Nat.finite_of_card_ne_zero (by omega)
    have huniv : ({Quotient.mk'' (α, α, α), Quotient.mk'' (α, α, β), Quotient.mk'' (α, β, α),
        Quotient.mk'' (β, α, α), Quotient.mk'' (α, β, γ)} :
        Set (MulAction.orbitRel.Quotient G (Ω × Ω × Ω))) = Set.univ :=
      Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
        (by rw [Set.ncard_univ, hcard, hncard]) Set.finite_univ
    have hlast : ∀ u v w : Ω, u ≠ v → u ≠ w → v ≠ w →
        (Quotient.mk'' (u, v, w) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
          = Quotient.mk'' (α, β, γ) := by
      intro u v w huv huw hvw
      have hmem : (Quotient.mk'' (u, v, w) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
          ∈ ({Quotient.mk'' (α, α, α), Quotient.mk'' (α, α, β), Quotient.mk'' (α, β, α),
            Quotient.mk'' (β, α, α), Quotient.mk'' (α, β, γ)} :
            Set (MulAction.orbitRel.Quotient G (Ω × Ω × Ω))) := huniv ▸ Set.mem_univ _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h | h | h
      · exact absurd h.symm (cube_orbit_ne_of_fst_snd rfl huv)
      · exact absurd h.symm (cube_orbit_ne_of_fst_snd rfl huv)
      · exact absurd h.symm (cube_orbit_ne_of_fst_thd rfl huw)
      · exact absurd h.symm (cube_orbit_ne_of_snd_thd rfl hvw)
      · exact h
    have hsame : (Quotient.mk'' (x, y, z) : MulAction.orbitRel.Quotient G (Ω × Ω × Ω))
        = Quotient.mk'' (a, b, c) :=
      (hlast x y z hxy hxz hyz).trans (hlast a b c hab hac hbc).symm
    rw [Quotient.eq''] at hsame
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp hsame
    have hg' : g • ((a, b, c) : Ω × Ω × Ω) = (x, y, z) := hg
    exact ⟨g, congrArg Prod.fst hg', congrArg (fun r => (Prod.snd r).1) hg',
      congrArg (fun r => (Prod.snd r).2) hg'⟩
  · -- 3-transitive ⟹ 5 軌道: 5 つの代表元が全体を尽くす。
    intro h3
    have huniv : (Set.univ : Set (MulAction.orbitRel.Quotient G (Ω × Ω × Ω)))
        = {Quotient.mk'' (α, α, α), Quotient.mk'' (α, α, β), Quotient.mk'' (α, β, α),
          Quotient.mk'' (β, α, α), Quotient.mk'' (α, β, γ)} := by
      refine (Set.eq_univ_iff_forall.mpr ?_).symm
      refine Quotient.ind' fun p => ?_
      obtain ⟨x, y, z⟩ := p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases eq_or_ne x y with hxy | hxy
      · subst hxy
        rcases eq_or_ne x z with hxz | hxz
        · subst hxz
          exact Or.inl (cube_orbit_diag α x)
        · exact Or.inr (Or.inl (cube_orbit_pattern_xxz h2 hαβ hxz))
      · rcases eq_or_ne x z with hxz | hxz
        · subst hxz
          exact Or.inr (Or.inr (Or.inl (cube_orbit_pattern_xzx h2 hαβ hxy)))
        · rcases eq_or_ne y z with hyz | hyz
          · subst hyz
            exact Or.inr (Or.inr (Or.inr (Or.inl
              (cube_orbit_pattern_zxx h2 hαβ hxy.symm))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr
              (cube_orbit_pattern_distinct h3 hαβ hαγ hβγ hxy hxz hyz))))
    rw [← Set.ncard_univ, huniv]
    exact hncard

/-- **Isaacs Problem 8A.13** (p. 236) 🎉: 2-transitive な `G` と `|Ω| ≥ 3` について
**`G` が 3-transitive ⟺ 置換指標 `χ` の 3 乗の平均値が 5** (`∑_{g} χ(g)³ = 5 |G|`)。
すなわち求める正整数は **`m = 5`**。

`χ³` は積作用 `Ω × Ω × Ω` の置換指標なので, Burnside より `∑ χ³ = (Ω³ の軌道数)·|G|`;
軌道数が 5 であることが 3-transitivity と同値 (`card_orbits_cube_eq_five_iff`)。 -/
theorem sum_cube_card_fixedBy_eq_five_mul_iff [Fintype G] [Finite Ω] [IsPretransitive G Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : G, g • a = c ∧ g • b = d)
    (hΩ : 2 < Nat.card Ω) :
    (∑ g : G, Nat.card (MulAction.fixedBy Ω g) ^ 3) = 5 * Nat.card G ↔
      ∀ a b c x y z : Ω, a ≠ b → a ≠ c → b ≠ c → x ≠ y → x ≠ z → y ≠ z →
        ∃ g : G, g • a = x ∧ g • b = y ∧ g • c = z := by
  classical
  have := Fintype.ofFinite Ω
  obtain ⟨α, β, γ, hαβ, hαγ, hβγ⟩ :=
    Fintype.two_lt_card_iff (α := Ω) |>.mp (by rwa [← Nat.card_eq_fintype_card])
  rw [sum_cube_card_fixedBy, ← card_orbits_cube_eq_five_iff h2 hαβ hαγ hβγ]
  exact ⟨fun h => Nat.eq_of_mul_eq_mul_right Nat.card_pos h, fun h => by rw [h]⟩

end

end OddOrder.Isaacs.Ch08
