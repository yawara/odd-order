/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Elementary Abelian Groups

`OddOrder.GroupTheory` shared module: 'elementary abelian p-group' の概念.

mathlib v4.29.1 にはこの概念 ("G abelian かつ ∀ x, x^p = 1") が無いため, 本リポジトリの
Ch.3 (Isaacs Thm 3.11), Ch.6 (6.9/6.15), Ch.7 (J(P) 定義) 共通の shared concept として
独立 module に切り出す. BG App.A, App.B (Puig L(S)) も将来再利用する.

## Main definitions

* `OddOrder.GroupTheory.IsElementaryAbelian p G`: 群 `G` が `p`-elementary abelian.
* `Subgroup.IsElementaryAbelian H p`: 部分群 `H ≤ G` が `p`-elementary abelian
  (whole-group form を `↥H` に適用; dot-notation friendly).

## Design notes

* `p` prime 仮定は def 段階では入れない (mathlib 慣用). 主結果記述時に `[Fact p.Prime]` 付与.
* def 形式は **(commute) ∧ (∀ x, x^p = 1)** を採用 (Ch.3 既存実装と整合). 別形式
  `IsPGroup p G ∧ Monoid.exponent G ∣ p` への bridge は将来追加可.
* 将来 mathlib upstream 視野で `OddOrder/Mathlib/ElementaryAbelian.lean` 候補.
-/

namespace OddOrder.GroupTheory

/-- **Elementary Abelian p-Group** (type-level): `G` is `p`-elementary abelian iff
`G` is abelian and `∀ x : G, x ^ p = 1`. -/
def IsElementaryAbelian (p : ℕ) (G : Type*) [Group G] : Prop :=
  (∀ x y : G, x * y = y * x) ∧ (∀ x : G, x ^ p = 1)

namespace IsElementaryAbelian

variable {p : ℕ} {G : Type*} [Group G]

/-- Commutativity projection. -/
theorem comm (h : IsElementaryAbelian p G) (x y : G) : x * y = y * x := h.1 x y

/-- `p`-th power projection. -/
theorem pow_eq_one (h : IsElementaryAbelian p G) (x : G) : x ^ p = 1 := h.2 x

end IsElementaryAbelian

end OddOrder.GroupTheory

namespace Subgroup

variable {G : Type*} [Group G]

/-- **Subgroup is Elementary Abelian**: subgroup `H ≤ G` is `p`-elementary abelian iff
the subtype `↥H` is `p`-elementary abelian as a group. -/
def IsElementaryAbelian (H : Subgroup G) (p : ℕ) : Prop :=
  OddOrder.GroupTheory.IsElementaryAbelian p ↥H

end Subgroup
