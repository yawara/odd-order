/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.Layer
import OddOrder.Isaacs.Ch01_Sylow.Basic

/-!
# Isaacs Ch. 9 — §9A: generalized Fitting subgroup F*(G) と Thm 9.8 / Cor 9.9 (p. 275)

- `genFitting G` = **generalized Fitting subgroup** `F*(G) = F(G) E(G)` (書籍 p. 275,
  `fitting G ⊔ layer G`). 両因子 normal ゆえ `F*(G) ◁ G`.
- **Theorem 9.8** (Bender, `centralizer_genFitting_le_genFitting`): 任意の有限群で
  `C_G(F*(G)) ≤ F*(G)`.
- **Corollary 9.9** (`fitting_le_genFitting`, `genFitting_eq_fitting_iff`):
  `F*(G) ⊇ F(G)`, かつ等号 ⟺ `F(G) ⊇ C_G(F(G))`.

## 実装ノート

Cor 9.9 の `←` (`F ⊇ C(F) ⇒ F* = F`) は Thm 9.7(c) のみに依る: `F(G)` solvable normal
なので `[E(G), F(G)] = 1`, ゆえ `E(G) ⊆ C_G(F(G)) ⊆ F(G)`, `F* = F(G) E(G) = F(G)`.
`→` は Thm 9.8 (`F* ⊇ C(F*)`) を要する.
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup QuotientGroup

open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 9A: generalized Fitting subgroup (p. 275) -/

/-- **Generalized Fitting subgroup** `F*(G) = F(G) E(G)` (Isaacs p. 275). -/
def genFitting (G : Type*) [Group G] : Subgroup G :=
  Ch01.fitting G ⊔ layer G

/-- `F(G) ≤ F*(G)` (Cor 9.9 の自明な包含). -/
theorem fitting_le_genFitting : Ch01.fitting G ≤ genFitting G := le_sup_left

/-- `E(G) ≤ F*(G)`. -/
theorem layer_le_genFitting : layer G ≤ genFitting G := le_sup_right

/-- **F\*(G) は `G` で正規** (両因子 normal). -/
instance genFitting.normal [Finite G] : (genFitting G).Normal := by
  rw [genFitting]
  infer_instance

end

section /- 9A: Corollary 9.9 の `←` 方向 (Thm 9.7(c) 依存) -/

/-- **Isaacs Cor 9.9 (`←`)**: `F(G) ⊇ C_G(F(G))` なら `F*(G) = F(G)`.
`F(G)` は solvable normal なので Thm 9.7(c) で `[E(G), F(G)] = 1`, よって
`E(G) ≤ C_G(F(G)) ≤ F(G)`, `F* = F(G) ⊔ E(G) = F(G)`. -/
theorem genFitting_eq_fitting_of_centralizer_fitting_le [Finite G]
    (h : Subgroup.centralizer (Ch01.fitting G : Set G) ≤ Ch01.fitting G) :
    genFitting G = Ch01.fitting G := by
  refine le_antisymm ?_ fitting_le_genFitting
  rw [genFitting, sup_le_iff]
  refine ⟨le_rfl, ?_⟩
  -- E(G) ≤ C_G(F(G)) ≤ F(G)
  haveI : IsSolvable ↥(Ch01.fitting G) := by
    haveI := Ch01.fitting.isNilpotent (G := G)
    exact IsNilpotent.to_isSolvable
  have hcomm : ⁅layer G, Ch01.fitting G⁆ = ⊥ :=
    commutator_layer_eq_bot_of_normal_isSolvable inferInstance
  have hle : layer G ≤ Subgroup.centralizer (Ch01.fitting G : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  exact hle.trans h

end

end OddOrder.Isaacs.Ch09
