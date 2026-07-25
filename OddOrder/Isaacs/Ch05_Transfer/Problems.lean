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
* **5A.4(a)** `transfer_eq_pow_index_of_le_center` — `H ≤ Z(G)`, `|G : H| = n` なら
  transfer は `g ↦ ϕ ⟨g ^ n⟩` (`ϕ : ↥H →* A` は任意)。Isaacs の `v : G → H/H'` は
  `A = H/H'` の場合で, `H ≤ Z(G)` なら `H` は可換ゆえ `H' = 1`, `H/H' ≅ H` なので
  「`v(h) = h ^ n`」がそのまま読める。
  ⚠ 余域を `↥H` に取った版は `CommGroup ↥H` を statement 内 `letI` で供給する必要があり,
  その instance の `toGroup` が `Subgroup.toGroup` と構文的に一致しないため
  `MonoidHom.id ↥H` の型が合わない (diamond)。一般 `ϕ` 版で十分なので採らない。
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

/-- **Isaacs Problem 5A.4(a)** (一般の余域版): `H ≤ Z(G)` で `|G : H| = n` なら, 任意の
`ϕ : ↥H →* A` (`A` 可換) について transfer は `g ↦ ϕ ⟨g ^ n⟩`。

`transfer_eq_pow` の仮説は `g₀⁻¹ g^k g₀ ∈ H ≤ Z(G)` が中心的で `g₀` と可換なことから従う
(mathlib `transfer_center_eq_pow` と同じ議論を `H ≤ Z(G)` に一般化したもの)。 -/
theorem transfer_eq_pow_index_of_le_center {G A : Type*} [Group G] [CommGroup A]
    {H : Subgroup G} [H.FiniteIndex] (hH : H ≤ Subgroup.center G) (ϕ : H →* A) (g : G) :
    transfer ϕ g = ϕ ⟨g ^ H.index, transfer_eq_pow_aux g
      (fun k g₀ hk => by rw [← mul_right_inj, ← (hH hk).comm, mul_inv_cancel_right])⟩ :=
  transfer_eq_pow ϕ g
    (fun k g₀ hk => by rw [← mul_right_inj, ← (hH hk).comm, mul_inv_cancel_right])

end

end OddOrder.Isaacs.Ch05
