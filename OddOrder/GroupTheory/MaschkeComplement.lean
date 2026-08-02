/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Maschke: invariant complements of subrepresentations

mathlib は Maschke を `MonoidAlgebra.Submodule.exists_isCompl`
(`Submodule k[G] V` の補元) の形で持っている。本 leaf はそれを **表現の言葉**に翻訳する:

`ρ : Representation k Q V` と `Q`-不変な部分加群 `W` に対し, `Q`-不変な補元 `W'` がある
(`|Q|` が `k` の標数で可逆, すなわち `NeZero (Nat.card Q : k)` のとき)。

`Subrepresentation ρ ≃o Submodule k[Q] ρ.asModule`
(`Subrepresentation.subrepresentationSubmoduleOrderIso`) を経由するだけ。

Isaacs Problem 10B.2 (`E ◁ G` 基本可換, `p ∤ |G : C_G(E)|` ⟹ `E ≤ Soc(G)`) で使う。

## Main results

* `OddOrder.GroupTheory.exists_isCompl_invariant`
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

/-- **Maschke, 表現版**: `Nat.card Q` が `k` で可逆なら, `Q`-不変な部分加群には
`Q`-不変な補元がある. -/
theorem exists_isCompl_invariant {k Q V : Type*} [Field k] [Group Q] [Finite Q]
    [NeZero (Nat.card Q : k)] [AddCommGroup V] [Module k V]
    (ρ : Representation k Q V) (W : Submodule k V)
    (hW : ∀ g : Q, ∀ ⦃v : V⦄, v ∈ W → ρ g v ∈ W) :
    ∃ W' : Submodule k V, (∀ g : Q, ∀ ⦃v : V⦄, v ∈ W' → ρ g v ∈ W') ∧ IsCompl W W' := by
  classical
  set σ : Subrepresentation ρ := ⟨W, hW⟩ with hσ
  obtain ⟨N, hN⟩ := MonoidAlgebra.Submodule.exists_isCompl
    (Subrepresentation.subrepresentationSubmoduleOrderIso σ)
  set τ : Subrepresentation ρ :=
    Subrepresentation.subrepresentationSubmoduleOrderIso.symm N with hτ
  have hcompl : IsCompl σ τ := by
    rw [hτ]
    exact (Subrepresentation.subrepresentationSubmoduleOrderIso.symm).isCompl
      (by simpa using hN)
  refine ⟨τ.toSubmodule, τ.apply_mem_toSubmodule, ?_⟩
  constructor
  · rw [disjoint_iff]
    have := hcompl.disjoint
    rw [disjoint_iff] at this
    exact congrArg Subrepresentation.toSubmodule this
  · rw [codisjoint_iff]
    have := hcompl.codisjoint
    rw [codisjoint_iff] at this
    exact congrArg Subrepresentation.toSubmodule this

end OddOrder.GroupTheory
