/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.OmegaSubgroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Critical subgroups (Gorenstein Thm 5.3.11 / 5.3.13)

`OddOrder.GroupTheory` shared module: Thompson の **critical subgroup**.

**BG Theorem 1.13** (J. G. Thompson, `references/bg/local-analysis.mmd:461`) の土台.
BG は証明本体を **Gorenstein "Finite Groups" Thm 5.3.11 (critical の存在) + 5.3.13
(`Ω₁(C)` の性質)** に委譲する. Isaacs に対応定理は無い (3 調査で確認) ため,
CLAUDE.md が定める「`G, Thm` 引用で Isaacs が欠く場合のみ Gorenstein 原文参照」ケース.
原典: `references/gorenstein/finite-groups.mmd` L3878-3945. 設計: `notes/bg/thm113_design.md`.

## Main definitions

* `IsCritical C`: `C ≤ G` が critical (Gorenstein 5.3.11 の (i)(ii)(iii)):
  characteristic, `cl(C) ≤ 2`, `[G,C] ≤ Z(C)`, `C_G(C) = Z(C)`.

## Main results (段階実装, `notes/bg/thm113_design.md` の S1-S8)

* `IsCritical.*`: 射影 (本ファイル).
* (予定 S1-S2) `isCritical_exists`: Gorenstein 5.3.11 存在定理.
* (予定 S6) `IsCritical.omega1_exponent`: 5.3.13 = `Ω₁(C)` exponent `p` (odd).
* (予定 S3-S7) faithful `p'`-action, `C_{Aut G}(Ω₁ C)` が `p`-群.

## Implementation notes

predicate `IsCritical : Subgroup G → Prop` を採用 (mathlib 互換, no-wrapper 方針).
`G` 自身が `p`-群の文脈で `C ≤ G` を critical と呼ぶ (Gorenstein の `P = G = ⊤`).
Gorenstein の (i) は `C/Z(C)` elementary abelian も含むが, それは (i-a)+commutator
から導出可能なので def には入れず補題で与える.
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **Gorenstein "Finite Groups" Thm 5.3.11** の条件を満たす部分群 `C ≤ G` =
`G` の **critical subgroup**:

* (char) `C` は `G` で characteristic;
* (i) `cl(C) ≤ 2`, すなわち `⁅C, C⁆ ≤ Z(C)`;
* (ii) `[G, C] ≤ Z(C)` (ambient `G` 側で, `Z(C)` は `C.subtype` 像);
* (iii) `C_G(C) = Z(C)` (self-centralizing).

Gorenstein の (i) に含まれる `C/Z(C)` elementary abelian は導出可能なので
def には入れない. -/
def IsCritical (C : Subgroup G) : Prop :=
  C.Characteristic
    ∧ _root_.commutator ↥C ≤ Subgroup.center ↥C
    ∧ ⁅(⊤ : Subgroup G), C⁆ ≤ (Subgroup.center ↥C).map C.subtype
    ∧ Subgroup.centralizer (C : Set G) = (Subgroup.center ↥C).map C.subtype

namespace IsCritical

variable {C : Subgroup G}

/-- critical ⇒ `C` characteristic. -/
theorem characteristic (hC : IsCritical C) : C.Characteristic := hC.1

/-- critical ⇒ `cl(C) ≤ 2` (`⁅C, C⁆ ≤ Z(C)`). -/
theorem commutator_le_center (hC : IsCritical C) :
    _root_.commutator ↥C ≤ Subgroup.center ↥C := hC.2.1

/-- critical ⇒ `[G, C] ≤ Z(C)` (ambient `G`). -/
theorem commutator_top_le_center (hC : IsCritical C) :
    ⁅(⊤ : Subgroup G), C⁆ ≤ (Subgroup.center ↥C).map C.subtype := hC.2.2.1

/-- critical ⇒ `C_G(C) = Z(C)` (self-centralizing). -/
theorem centralizer_eq (hC : IsCritical C) :
    Subgroup.centralizer (C : Set G) = (Subgroup.center ↥C).map C.subtype := hC.2.2.2

end IsCritical

end OddOrder.GroupTheory
