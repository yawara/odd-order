/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Basic
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.PointStabilizers
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.RegularRepresentations

/-!
# Isaacs Problems 8A (pp. 235–236) — 可解な多重推移群

**Problem 8A.10**: 可解な 4-transitive 置換群の次数は 4 で, したがって `S₄` に同型。

## Main results

- `card_le_four_of_three_transitive_on_nonidentity`,
  `card_le_four_of_regular_normal_of_stabilizer_three_transitive` —
  **Problem 8A.10 の核心**: 自己同型群が `N ∖ {1}` に 3-transitive なら `|N| ≤ 4`;
  `N` が regular normal で `G_α` が `Ω ∖ {α}` に 3-transitive なら `|N| ≤ 4`。
- `card_eq_four_of_isSolvable_of_stabilizer_three_transitive`,
  `nonempty_mulEquiv_perm_fin_four_of_four_transitive` — **Problem 8A.10**:
  可解な 4-transitive 置換群の次数は 4 で, したがって `S₄` に同型。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

section /- Problems 8A (pp. 235-236) -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-! ### Problem 8A.10 — 可解 4-transitive 群 -/

/-- **8A.10 の核心**: 群 `N` に自己同型として作用する `A` が非単位元の集合 `N ∖ {1}` に
**3-transitive** なら `|N| ≤ 4`。

自己同型は積を保つので, `x`, `y` を固定する元は `xy` も固定する。`|N| ≥ 5` なら
`1, x, y, xy` と異なる `w` が取れ, 3-transitivity で `(x, y, xy) ↦ (x, y, w)` を実現する
自己同型があるはずだが, それは `xy ↦ xy ≠ w` を強いる — 矛盾。

`N` が elementary abelian であることは不要 (積を保つことだけを使う)。 -/
theorem card_le_four_of_three_transitive_on_nonidentity
    {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]
    (h3 : ∀ x y z x' y' z' : N, x ≠ 1 → y ≠ 1 → z ≠ 1 → x' ≠ 1 → y' ≠ 1 → z' ≠ 1 →
      x ≠ y → x ≠ z → y ≠ z → x' ≠ y' → x' ≠ z' → y' ≠ z' →
      ∃ a : A, a • x = x' ∧ a • y = y' ∧ a • z = z') :
    Nat.card N ≤ 4 := by
  classical
  by_contra hcard
  have h5 : 5 ≤ Nat.card N := Nat.lt_of_not_le hcard
  have : Finite N := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite N
  -- 濃度が `Nat.card N` 未満の `Finset` の外に元が取れる
  have hout : ∀ s : Finset N, s.card < Nat.card N → ∃ z : N, z ∉ s := by
    intro s hs
    by_contra hc
    rw [Finset.eq_univ_iff_forall.mpr (not_exists_not.mp hc), Finset.card_univ,
      ← Nat.card_eq_fintype_card] at hs
    exact lt_irrefl _ hs
  -- `x ≠ 1`
  obtain ⟨x, hx⟩ := hout {1} (by simp only [Finset.card_singleton]; omega)
  simp only [Finset.mem_singleton] at hx
  -- `y ∉ {1, x, x⁻¹}` — これで `x * y ∉ {1, x, y}`
  obtain ⟨y, hy⟩ := hout {1, x, x⁻¹} (lt_of_le_of_lt (Finset.card_insert_le _ _) (by
    refine lt_of_le_of_lt (Nat.succ_le_succ (Finset.card_insert_le _ _)) ?_
    simp only [Finset.card_singleton]
    omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨hy1, hyx, hyxinv⟩ := hy
  have hxy1 : x * y ≠ 1 := fun hc => hyxinv (inv_eq_of_mul_eq_one_right hc).symm
  have hxyx : x * y ≠ x := fun hc => hy1 (by simpa using congrArg (x⁻¹ * ·) hc)
  have hxyy : x * y ≠ y := fun hc => hx (by simpa using congrArg (· * y⁻¹) hc)
  -- `w ∉ {1, x, y, x * y}`
  obtain ⟨w, hw⟩ := hout {1, x, y, x * y} (by
    refine lt_of_le_of_lt (Finset.card_insert_le _ _) ?_
    refine lt_of_le_of_lt (Nat.succ_le_succ (Finset.card_insert_le _ _)) ?_
    refine lt_of_le_of_lt (Nat.succ_le_succ (Nat.succ_le_succ (Finset.card_insert_le _ _))) ?_
    simp only [Finset.card_singleton]
    omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  obtain ⟨hw1, hwx, hwy, hwxy⟩ := hw
  -- 3-transitivity: `(x, y, x*y) ↦ (x, y, w)`
  obtain ⟨a, hax, hay, haxy⟩ := h3 x y (x * y) x y w hx hy1 hxy1 hx hy1 hw1
    (Ne.symm hyx) (Ne.symm hxyx) (Ne.symm hxyy) (Ne.symm hyx) (Ne.symm hwx) (Ne.symm hwy)
  exact hwxy (by rw [← haxy, smul_mul', hax, hay])

/-- **8A.10 の step 5**: `N` が regular normal で点安定化群 `G_α` が `Ω ∖ {α}` に
3-transitive なら, `|N| ≤ 4`。

Thm 8.5 の第 3 主張 (共役作用と点作用の置換同型) を軌道写像 `n ↦ n • α` で直接使う:
`g • α = α` のとき `(g n g⁻¹) • α = g • (n • α)` なので, `Ω ∖ {α}` 上の 3-transitivity は
`N ∖ {1}` 上の**自己同型による** 3-transitivity に翻訳され,
`card_le_four_of_three_transitive_on_nonidentity` が使える。 -/
theorem card_le_four_of_regular_normal_of_stabilizer_three_transitive
    {N : Subgroup G} [N.Normal] {α : Ω} (hreg : Function.Bijective (smulBase N α))
    (h3 : ∀ β₁ β₂ β₃ γ₁ γ₂ γ₃ : Ω, β₁ ≠ α → β₂ ≠ α → β₃ ≠ α → γ₁ ≠ α → γ₂ ≠ α → γ₃ ≠ α →
      β₁ ≠ β₂ → β₁ ≠ β₃ → β₂ ≠ β₃ → γ₁ ≠ γ₂ → γ₁ ≠ γ₃ → γ₂ ≠ γ₃ →
      ∃ g : G, g • α = α ∧ g • β₁ = γ₁ ∧ g • β₂ = γ₂ ∧ g • β₃ = γ₃) :
    Nat.card ↥N ≤ 4 := by
  refine card_le_four_of_three_transitive_on_nonidentity (A := MulAut ↥N) ?_
  intro x y z x' y' z' hx hy hz hx' hy' hz' hxy hxz hyz hxy' hxz' hyz'
  -- 非単位元は `α` と異なる点へ, 相異なる元は相異なる点へ移る
  have hne : ∀ n : ↥N, n ≠ 1 → (n : G) • α ≠ α := fun n hn hc =>
    hn (hreg.1 (show smulBase N α n = smulBase N α 1 by simpa [smulBase] using hc))
  have hinj : ∀ m n : ↥N, (m : G) • α = (n : G) • α → m = n := fun m n hc =>
    hreg.1 (by simpa [smulBase] using hc)
  obtain ⟨g, hgα, hg1, hg2, hg3⟩ :=
    h3 ((x : G) • α) ((y : G) • α) ((z : G) • α) ((x' : G) • α) ((y' : G) • α) ((z' : G) • α)
      (hne x hx) (hne y hy) (hne z hz) (hne x' hx') (hne y' hy') (hne z' hz')
      (fun hc => hxy (hinj _ _ hc)) (fun hc => hxz (hinj _ _ hc)) (fun hc => hyz (hinj _ _ hc))
      (fun hc => hxy' (hinj _ _ hc)) (fun hc => hxz' (hinj _ _ hc)) (fun hc => hyz' (hinj _ _ hc))
  -- `g` による共役が求める自己同型
  have hginv : g⁻¹ • α = α := by rw [inv_smul_eq_iff, hgα]
  have key : ∀ (n n' : ↥N), g • ((n : G) • α) = (n' : G) • α →
      (MulAut.conjNormal (H := N) g) • n = n' := by
    intro n n' hc
    refine hinj _ _ ?_
    rw [MulAut.smul_def, MulAut.conjNormal_apply]
    calc (g * (n : G) * g⁻¹) • α = g • ((n : G) • (g⁻¹ • α)) := by
          simp only [← mul_smul, mul_assoc]
      _ = (n' : G) • α := by rw [hginv, hc]
  exact ⟨MulAut.conjNormal (H := N) g, key x x' hg1, key y y' hg2, key z z' hg3⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Isaacs Problem 8A.10** (p. 236) の主内容: **可解な 4-transitive 置換群の次数は 4**。

書籍 hint どおり極小正規部分群 `N` を取る。`N` は忠実性から非自明に作用するので **8A.9**
で推移的, `G` 可解ゆえ **Isaacs Thm 3.11** で可換 (実は elementary abelian), 可換 + 推移的
+ 忠実で **8A.2** より `C_G(N) ⊓ G_α = ⊥`, `N ≤ C_G(N)` だから `N` は **regular**。
`G_α` は `Ω ∖ {α}` に 3-transitive なので
`card_le_four_of_regular_normal_of_stabilizer_three_transitive` で `|N| ≤ 4`,
regular ゆえ `|Ω| = |N| ≤ 4`。

4-transitivity は「推移的 + `G_α` が `Ω ∖ {α}` に 3-transitive」の形で仮定する
(`h2` は 2-transitivity 部分, `h3` は 3-transitivity 部分)。 -/
theorem card_eq_four_of_isSolvable_of_stabilizer_three_transitive [Finite G] [Group.IsSolvable G]
    [FaithfulSMul G Ω] [IsPretransitive G Ω] {α : Ω} (hΩ4 : 4 ≤ Nat.card Ω)
    (h2 : ∀ α' β γ : Ω, β ≠ α' → γ ≠ α' → ∃ g : G, g • α' = α' ∧ g • β = γ)
    (h3 : ∀ β₁ β₂ β₃ γ₁ γ₂ γ₃ : Ω, β₁ ≠ α → β₂ ≠ α → β₃ ≠ α → γ₁ ≠ α → γ₂ ≠ α → γ₃ ≠ α →
      β₁ ≠ β₂ → β₁ ≠ β₃ → β₂ ≠ β₃ → γ₁ ≠ γ₂ → γ₁ ≠ γ₃ → γ₂ ≠ γ₃ →
      ∃ g : G, g • α = α ∧ g • β₁ = γ₁ ∧ g • β₂ = γ₂ ∧ g • β₃ = γ₃) :
    Nat.card Ω = 4 := by
  classical
  -- `Ω` は 2 点以上, したがって `G` は非自明
  have hΩfin : Finite Ω := Nat.finite_of_card_ne_zero (by omega)
  have hΩnt : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨β, hβ⟩ := exists_ne α
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq G α β
  have hGnt : Nontrivial G := ⟨g₀, 1, fun hc => hβ (by rw [← hg₀, hc, one_smul])⟩
  -- 極小正規部分群 `N`
  obtain ⟨N, hNmin, -⟩ :=
    OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
  have hNnormal : N.Normal := hNmin.1
  have hNnt : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNmin.2.1
  -- `N` は非自明に作用する (忠実性)
  obtain ⟨n, hn1⟩ := exists_ne (1 : ↥N)
  have hnact : ∃ x : Ω, (n : G) • x ≠ x := by
    by_contra hc
    exact hn1 (Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (α := Ω)
      fun x => by rw [OneMemClass.coe_one, one_smul]; exact not_exists_not.mp hc x))
  obtain ⟨x, hx⟩ := hnact
  -- 8A.9: `N` は推移的
  have hNtrans : IsPretransitive ↥N Ω := isPretransitive_of_normal_of_two_transitive h2 hx
  -- Thm 3.11: `N` は可換
  have habel := OddOrder.Isaacs.Ch03.minimal_normal_isAbelian_of_isSolvable hNmin
  have hNcent : N ≤ Subgroup.centralizer (N : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => habel b hb a ha
  -- 8A.2: `N` は regular
  have hbot : N ⊓ stabilizer G α = ⊥ :=
    le_antisymm (le_trans (inf_le_inf_right _ hNcent)
      (le_of_eq (centralizer_inf_stabilizer_eq_bot (H := N) α))) bot_le
  have hbij : Function.Bijective (smulBase N α) :=
    (bijective_smulBase_iff N α).mpr ⟨hNtrans, hbot⟩
  -- 核心補題で `|N| ≤ 4`, regular ゆえ `|Ω| = |N|`
  have hcardN := card_le_four_of_regular_normal_of_stabilizer_three_transitive hbij h3
  have hcardΩ : Nat.card Ω = Nat.card ↥N :=
    (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  omega

/-- 型の同値 `e : α ≃ β` に沿った対称群の同型 (mathlib の `Equiv.permCongr` の乗法版)。 -/
def permCongrMulEquiv {α β : Type*} (e : α ≃ β) : Equiv.Perm α ≃* Equiv.Perm β where
  toFun p := (e.symm.trans p).trans e
  invFun q := (e.trans q).trans e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
  map_mul' _ _ := by ext; simp

/-- **Isaacs Problem 8A.10** (p. 236) 🎉: **可解な 4-transitive 置換群は `S₄` に同型**。

次数が 4 であること (`card_eq_four_of_isSolvable_of_stabilizer_three_transitive`) を認めれば,
`MulAction.toPermHom` が単射 (忠実) かつ全射 (4 点の任意の並べ替えは 4-transitivity で
実現できる) なので `G ≃* Sym(Ω) ≃* S₄`。

4-transitivity は「単射な 4-tuple どうしを移す元がある」形 (`h4`) で仮定する。 -/
theorem nonempty_mulEquiv_perm_fin_four_of_four_transitive [FaithfulSMul G Ω]
    (hcard : Nat.card Ω = 4)
    (h4 : ∀ b c : Fin 4 → Ω, Function.Injective b → Function.Injective c →
      ∃ g : G, ∀ i, g • b i = c i) :
    Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  have : Finite Ω := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨e⟩ : Nonempty (Fin 4 ≃ Ω) := Finite.card_eq.mp (by simp [hcard])
  have hbij : Function.Bijective (MulAction.toPermHom G Ω) := by
    refine ⟨MulAction.toPerm_injective, fun σ => ?_⟩
    obtain ⟨g, hg⟩ := h4 (fun i => e i) (fun i => σ (e i)) e.injective
      (σ.injective.comp e.injective)
    refine ⟨g, Equiv.ext fun x => ?_⟩
    have hx : x = e (e.symm x) := (e.apply_symm_apply x).symm
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, hx, hg (e.symm x)]
  exact ⟨(MulEquiv.ofBijective _ hbij).trans (permCongrMulEquiv e.symm)⟩

end

end OddOrder.Isaacs.Ch08
