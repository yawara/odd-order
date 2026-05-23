/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import OddOrder.GroupTheory.ElementaryAbelian

/-!
# Thompson Subgroup `J(P)`

`OddOrder.GroupTheory` shared module: Thompson subgroup `J(P)` の定義と基本性質.

Isaacs, *Finite Group Theory* (2008), Chapter 7 (pp. 201-202) の中核 def.
mathlib v4.29.1 に未収載 (`Thompson` 名はゼロ件). Ch.7, BG App.A, BG App.B (Puig 代替),
BG §6, §8, §9 (Uniqueness Theorem) で繰り返し使われる shared concept として独立 module 化.

## Main definitions

* `Subgroup.maxElemAbelianIn P p`: 部分群 `P` 内の `p`-elementary abelian 部分群のうち
  最大位数のものの集合 (Isaacs L3727 の `E(P)`).
* `Subgroup.thompsonJ P p`: Thompson subgroup `J(P) = ⟨E(P)⟩`
  (Isaacs L3727, Aschbacher §32, BG L5586 の記法).

## Design notes

* Isaacs の `J(P)` は **largest order** の elementary abelian (Aschbacher 系). Thompson
  原版は **largest rank** (元の Thompson 1968) で、両者は P が abelian non-elementary
  のとき異なりうる. 本 module は Isaacs/Aschbacher 版を採用.
* `p` は引数で取る (`P ∈ Syl_p(G)` 文脈で外側固定が自然).
* `[Finite G]` は def 段階では不要だが, 主要結果 (Thm 7.2 等) では必須.

## Forward references

* `Subgroup.thompsonJ_le`: `J(P) ≤ P`.
* **Isaacs Thm 7.2** (`thompsonJ_eq_of_le_of_le`): `J(P) ≤ Q ≤ P ⇒ J(Q) = J(P)`.
  特に `J(P)` は `Q` 内 characteristic.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- `[Finite G]` のとき, `Subgroup G` 自体も有限. `Subgroup G ↪ Set G` 経由. -/
instance instFiniteSubgroupOfFinite [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

/-- The trivial subgroup `⊥` is `p`-elementary abelian for any `p`. -/
theorem bot_isElementaryAbelian (p : ℕ) :
    (⊥ : Subgroup G).IsElementaryAbelian p := by
  refine ⟨?_, ?_⟩
  · intro x y
    exact Subsingleton.elim _ _
  · intro x
    have hx : x = 1 := Subsingleton.elim x 1
    rw [hx, one_pow]

/-- **Maximum-order elementary abelian subgroups of `P`** (Isaacs Ch.7 L3727 の `E(P)`).

`E(P) = {E ≤ P | E は p-elementary abelian で, 任意の elem-ab subgroup F ≤ P について
|F| ≤ |E|}`. -/
def maxElemAbelianIn (P : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {E | E ≤ P ∧ E.IsElementaryAbelian p ∧
       ∀ F : Subgroup G, F ≤ P → F.IsElementaryAbelian p → Nat.card F ≤ Nat.card E}

/-- **Thompson subgroup** `J(P) = ⟨E(P)⟩` (Isaacs Ch.7 def, p.201).

`P` 内の最大位数 elementary abelian 部分群すべての (Subgroup G 内での) 上限. -/
def thompsonJ (P : Subgroup G) (p : ℕ) : Subgroup G :=
  ⨆ E ∈ maxElemAbelianIn P p, E

/-- `J(P) ≤ P`: Thompson subgroup は `P` の部分群. -/
theorem thompsonJ_le (P : Subgroup G) (p : ℕ) : thompsonJ P p ≤ P := by
  refine iSup_le fun E => iSup_le fun hE => ?_
  exact hE.1

/-- `E ∈ maxElemAbelianIn P p` の生成元は `J(P)` に含まれる. -/
theorem le_thompsonJ_of_mem_maxElemAbelianIn {P E : Subgroup G} {p : ℕ}
    (hE : E ∈ maxElemAbelianIn P p) : E ≤ thompsonJ P p :=
  le_iSup_of_le E (le_iSup_of_le hE le_rfl)

/-- `maxElemAbelianIn` の単調性 (片方向): max-order subgroup の "最大値" は
`P` を縮める方向と整合しない一般論はないが, **「`J(P) ≤ Q ≤ P` ⇒ Q 内 max は P 内 max
と一致」** という Isaacs Thm 7.2 の核となる性質を別途 `thompsonJ_eq_of_le_of_le` で示す. -/
theorem mem_maxElemAbelianIn_of_le {P Q E : Subgroup G} {p : ℕ}
    (hQP : Q ≤ P) (hE : E ∈ maxElemAbelianIn Q p) :
    E.IsElementaryAbelian p ∧ E ≤ P :=
  ⟨hE.2.1, hE.1.trans hQP⟩

/-- `[Finite G]` のもとで `maxElemAbelianIn P p` は非空 (`⊥` が常に元). -/
theorem maxElemAbelianIn_nonempty [Finite G] (P : Subgroup G) (p : ℕ) :
    (maxElemAbelianIn P p).Nonempty := by
  -- S = {F ≤ P | F elem ab} は有限・非空 (⊥ ∈ S).
  have hUniv : (Set.univ : Set (Subgroup G)).Finite := Set.finite_univ
  have hS_fin : {F : Subgroup G | F ≤ P ∧ F.IsElementaryAbelian p}.Finite :=
    hUniv.subset (fun _ _ => Set.mem_univ _)
  have hS_ne : {F : Subgroup G | F ≤ P ∧ F.IsElementaryAbelian p}.Nonempty :=
    ⟨⊥, bot_le, bot_isElementaryAbelian p⟩
  -- 最大位数の元 E を取得.
  obtain ⟨E, hE_S, hE_max⟩ :=
    Set.exists_max_image
      {F : Subgroup G | F ≤ P ∧ F.IsElementaryAbelian p}
      (fun F => Nat.card F) hS_fin hS_ne
  refine ⟨E, hE_S.1, hE_S.2, ?_⟩
  intro F hF_P hF_el
  exact hE_max F ⟨hF_P, hF_el⟩

/-- **Isaacs Thm 7.2** (J(P) は Q 内でも変わらない).

`J(P) ≤ Q ≤ P` のとき `J(Q) = J(P)`. 系として **`J(P)` は `Q` 内 characteristic**
(`J(Q)` は Q 内 characteristic で自動的に従う性質, 別途).

証明: `maxElemAbelianIn Q p = maxElemAbelianIn P p` を示す.
- `Q ⊆ P` 側: `E ∈ maxElemAbelianIn P p` ⇒ `E ≤ J(P) ≤ Q`, `Q` 内でも max (任意の
  `F ≤ Q ≤ P` elem ab で `|F| ≤ |E|`).
- `P ⊆ Q` 側: `E₀ ∈ maxElemAbelianIn P p` を fix し `E₀ ≤ Q`. `E ∈ maxElemAbelianIn Q p`
  なら `|E₀| ≤ |E|` (E max in Q) かつ `|E| ≤ |E₀|` (E ≤ P, E₀ max in P) で位数一致.
  位数一致から `E` も `P` 内 max. -/
theorem thompsonJ_eq_of_le_of_le [Finite G] {P Q : Subgroup G} {p : ℕ}
    (hJQ : thompsonJ P p ≤ Q) (hQP : Q ≤ P) :
    thompsonJ Q p = thompsonJ P p := by
  apply le_antisymm
  · -- J(Q) ≤ J(P)
    refine iSup_le fun E => iSup_le fun hE_Q => ?_
    -- E max in Q.  E ∈ maxElemAbelianIn P p を示す.
    obtain ⟨E₀, hE₀_P, hE₀_el, hE₀_max⟩ := maxElemAbelianIn_nonempty P p
    have hE₀_le_J : E₀ ≤ thompsonJ P p :=
      le_thompsonJ_of_mem_maxElemAbelianIn ⟨hE₀_P, hE₀_el, hE₀_max⟩
    have hE₀_Q : E₀ ≤ Q := hE₀_le_J.trans hJQ
    have hcard_E₀_le_E : Nat.card E₀ ≤ Nat.card E := hE_Q.2.2 E₀ hE₀_Q hE₀_el
    have hE_P : E ≤ P := hE_Q.1.trans hQP
    have hcard_E_le_E₀ : Nat.card E ≤ Nat.card E₀ := hE₀_max E hE_P hE_Q.2.1
    have hcard_eq : Nat.card E = Nat.card E₀ := le_antisymm hcard_E_le_E₀ hcard_E₀_le_E
    apply le_thompsonJ_of_mem_maxElemAbelianIn
    refine ⟨hE_P, hE_Q.2.1, ?_⟩
    intro F hF_P hF_el
    calc Nat.card F
        ≤ Nat.card E₀ := hE₀_max F hF_P hF_el
      _ = Nat.card E := hcard_eq.symm
  · -- J(P) ≤ J(Q)
    refine iSup_le fun E => iSup_le fun hE_P => ?_
    have hE_le_J : E ≤ thompsonJ P p :=
      le_thompsonJ_of_mem_maxElemAbelianIn hE_P
    have hE_Q : E ≤ Q := hE_le_J.trans hJQ
    apply le_thompsonJ_of_mem_maxElemAbelianIn
    refine ⟨hE_Q, hE_P.2.1, ?_⟩
    intro F hF_Q hF_el
    exact hE_P.2.2 F (hF_Q.trans hQP) hF_el

end Subgroup
