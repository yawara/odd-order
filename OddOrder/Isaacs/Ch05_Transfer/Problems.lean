/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer

/-!
# Isaacs Chapter 5 — Problems 5A (transfer の基本)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 5A (書籍 pp. 152-153)。

mathlib の transfer は `MonoidHom.transfer (ϕ : H →* A) : G →* A` (`A` は可換群) で,
Isaacs の `v : G → H/H'` は `A = H/H'`, `ϕ = 自然な射影` の場合にあたる。

* **5A.1** `transfer_id_eq_pow_index_of_commGroup` — `G` 可換, `|G : H| = n` なら
  `G → H` の transfer は `g ↦ g ^ n`。
-/

namespace OddOrder.Isaacs.Ch05

open MonoidHom

section /- Problems 5A (pp. 152-153) -/

/-- **Isaacs Problem 5A.1**: `G` が可換で `H ≤ G` の指数が `n` なら, `G` から `H` への
transfer は `g ↦ g ^ n`。

可換なので `transfer_eq_pow` の仮説 `g₀⁻¹ g^k g₀ = g^k` は自明に成り立つ。 -/
theorem transfer_id_eq_pow_index_of_commGroup {G : Type*} [CommGroup G] {H : Subgroup G}
    [H.FiniteIndex] (g : G) :
    transfer (MonoidHom.id H) g = ⟨g ^ H.index, transfer_eq_pow_aux g
      (fun k g₀ _ => by rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul])⟩ :=
  transfer_eq_pow (MonoidHom.id H) g
    (fun k g₀ _ => by rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul])

/-- **Isaacs Problem 5A.1** (値の形): `G` 可換なら transfer の値は `g ^ |G : H|`。 -/
theorem coe_transfer_id_of_commGroup {G : Type*} [CommGroup G] {H : Subgroup G}
    [H.FiniteIndex] (g : G) :
    ((transfer (MonoidHom.id H) g : H) : G) = g ^ H.index := by
  rw [transfer_id_eq_pow_index_of_commGroup]

end

end OddOrder.Isaacs.Ch05
