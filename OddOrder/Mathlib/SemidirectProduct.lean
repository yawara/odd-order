/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.PGroup

/-!
# Generic helpers for `SemidirectProduct`

mathlib v4.29.1 `SemidirectProduct` モジュールに対する補足. 順次 upstream 視野.

## 主結果

* `IsPGroup.semidirectProduct`: `N`, `G` 双方が p-group ⇒ `N ⋊[φ] G` も p-group.
  Isaacs Lem 4.32 (P p-group acts on G p-group ⇒ [G,P] < G + C_G(P) > 1) で
  `Γ = G ⋊ P` が p-group ⇒ 冪零という議論の核.
-/

/-- **半直積の Finite instance**. `SemidirectProduct.equivProd` 経由. -/
instance SemidirectProduct.finite {N G : Type*} [Group N] [Group G] [Finite N] [Finite G]
    {φ : G →* MulAut N} : Finite (N ⋊[φ] G) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

/-- **p-group の半直積は p-group**: `N`, `G` 共に p-group なら `N ⋊[φ] G` も p-group.

`SemidirectProduct.card` (`|N ⋊ G| = |N| · |G|`) + `IsPGroup.iff_card` で
`|N| = p^a`, `|G| = p^b` ⇒ `|N ⋊ G| = p^{a+b}`. -/
theorem IsPGroup.semidirectProduct
    {N G : Type*} [Group N] [Group G] [Finite N] [Finite G]
    {p : ℕ} [Fact p.Prime] {φ : G →* MulAut N}
    (hN : IsPGroup p N) (hG : IsPGroup p G) :
    IsPGroup p (N ⋊[φ] G) := by
  rw [IsPGroup.iff_card]
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hN
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hG
  refine ⟨a + b, ?_⟩
  rw [SemidirectProduct.card, ha, hb, pow_add]
