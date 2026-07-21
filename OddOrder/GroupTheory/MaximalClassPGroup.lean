/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh02
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroups

/-!
# Maximal-class p-group 理論: 2-step centralizer 条件と degree of commutativity の同値

BG App.E (issue 9402) の clean Lemma。maximal class p-群 `S` の理論 (Blackburn 1958;
Leedham-Green–McKay, *The Structure of Groups of Prime Power Order*, Ch. 3) では、
uniserial 鎖 `γᵢ(S)` に対し

* **degree of commutativity ≥ 1** (`dc(S) ≥ 1`): `⁅γᵢ, γⱼ⁆ ≤ γ_{i+j+1}` (weight bound
  `⁅γᵢ, γⱼ⁆ ≤ γ_{i+j}` の 1 段改善)、
* **non-exceptional**: 2-step centralizer `Cᵢ = C_S(γᵢ/γ_{i+2})` が全て一致

が同値になることが標準事実 (n ≥ 5)。本 leaf はこの同値の**片方向が完全に一般の交換子計算で
成り立つ**ことを形式化する: 任意の群 `G` と正規部分群 `T` の鎖
`H a = iterCommutator T ⊤ a` (`H 0 = T`, `H (a+1) = ⁅H a, ⊤⁆`) について

> `(∀ a, ⁅H a, T⁆ ≤ H (a+2))` (2-step 条件) `⟺` `(∀ a b, ⁅H a, H b⁆ ≤ H (a+b+2))` (dc 形)。

非自明方向は Isaacs Cor 4.10 (three-subgroups mod `N`,
`commutator_commutator_le_of_rotate`) による `b` 帰納で、Isaacs Thm 4.11
(`commutator_lowerCentralSeries_le`) と同じ骨格。maximal class 仮定は**不要**
(1 次元性を使う Lie 環版と違い、部分群の `≤` 形は一般に成立する)。

## 消費側

BG corrected Prop E.4 / (E.23) の追加仮説 `hdc` は 2-step 形
(`OddOrder/BG/AppE_BetaSupply.lean` `scale_iterCommutator_of_two_step`、
`AppE_PropE4.lean`)。本同値により `hdc` は dc 形と交換可能 — BG の印刷版 E.4 が
偽であること (Lazard 群 `Q₆` 反例、`AppE_FiliformRefutation.lean` /
`notes/bg/appE_e4_counterexample_2026_07_21.md`) の「欠けた仮説」の 2 表現が一致する。

将来の maximal class p-群 API (`IsExceptional` 述語等) はこの leaf に置く。
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs.Ch04

variable {G : Type*} [Group G] {T : Subgroup G}

/-- **2-step centralizer 条件 ⟹ degree of commutativity ≥ 1** (一般の交換子計算).

`H a = iterCommutator T ⊤ a` の鎖について、2-step 条件 `⁅H a, T⁆ ≤ H (a+2)` (∀a) から
full additivity `⁅H a, H b⁆ ≤ H (a+b+2)` (∀a b) が従う。`b` についての帰納
(`a` は generalize): base `b = 0` は 2-step 条件そのもの、step は three-subgroups
mod `H (a+b+3)` (Isaacs Cor 4.10) — `⁅⁅⊤, H a⁆, H b⁆` は帰納法の仮定の `a+1` 例化、
`⁅⁅H a, H b⁆, ⊤⁆` は帰納法の仮定 + 単調性で押さえる。

maximal class p-群論では `T = C_S(Ω₁(Z₂(S)))`, `H a = γ_{a+1}(S)` で、これが
「non-exceptional ⟹ dc ≥ 1」の片方向 (Leedham-Green–McKay Ch. 3)。 -/
theorem commutator_iterCommutator_le_of_two_step [T.Normal]
    (hdc : ∀ a : ℕ, ⁅iterCommutator T (⊤ : Subgroup G) a, T⁆ ≤
      iterCommutator T (⊤ : Subgroup G) (a + 2)) :
    ∀ a b : ℕ,
      ⁅iterCommutator T (⊤ : Subgroup G) a, iterCommutator T (⊤ : Subgroup G) b⁆ ≤
        iterCommutator T (⊤ : Subgroup G) (a + b + 2) := by
  intro a b
  induction b generalizing a with
  | zero => simpa using hdc a
  | succ b ih =>
    haveI : (iterCommutator T (⊤ : Subgroup G) (a + b + 3)).Normal :=
      iterCommutator_normal _
    -- three-subgroups mod `H (a+b+3)` で回した形: `⁅⁅H b, ⊤⁆, H a⁆ ≤ H (a+b+3)`.
    have key : ⁅⁅iterCommutator T (⊤ : Subgroup G) b, (⊤ : Subgroup G)⁆,
        iterCommutator T (⊤ : Subgroup G) a⁆ ≤
        iterCommutator T (⊤ : Subgroup G) (a + b + 3) := by
      refine commutator_commutator_le_of_rotate ?_ ?_
      · -- `⁅⁅⊤, H a⁆, H b⁆ = ⁅H (a+1), H b⁆ ≤ H (a+b+3)`: 帰納法の仮定の `a+1` 例化.
        have h_top : ⁅(⊤ : Subgroup G), iterCommutator T (⊤ : Subgroup G) a⁆ =
            iterCommutator T (⊤ : Subgroup G) (a + 1) := by
          rw [Subgroup.commutator_comm]; rfl
        rw [h_top]
        have h := ih (a + 1)
        rwa [show a + 1 + b + 2 = a + b + 3 by omega] at h
      · -- `⁅⁅H a, H b⁆, ⊤⁆ ≤ ⁅H (a+b+2), ⊤⁆ = H (a+b+3)`: 帰納法の仮定 + 単調性.
        exact le_trans (Subgroup.commutator_mono (ih a) le_rfl) le_rfl
    rw [show a + (b + 1) + 2 = a + b + 3 by omega, Subgroup.commutator_comm]
    exact key

/-- **2-step centralizer 条件 ⟺ degree of commutativity ≥ 1** (同値形)。

逆方向は `T = H 0` の例化で自明。BG corrected E.4 の追加仮説 `hdc` (2-step 形、
`AppE_BetaSupply.lean`) と Blackburn の `dc(S) ≥ 1` が同じ条件であることの機械検証。 -/
theorem two_step_iff_commutator_iterCommutator_le [T.Normal] :
    (∀ a : ℕ, ⁅iterCommutator T (⊤ : Subgroup G) a, T⁆ ≤
      iterCommutator T (⊤ : Subgroup G) (a + 2)) ↔
    (∀ a b : ℕ,
      ⁅iterCommutator T (⊤ : Subgroup G) a, iterCommutator T (⊤ : Subgroup G) b⁆ ≤
        iterCommutator T (⊤ : Subgroup G) (a + b + 2)) := by
  constructor
  · exact commutator_iterCommutator_le_of_two_step
  · intro hfull a
    simpa using hfull a 0

end OddOrder.GroupTheory
