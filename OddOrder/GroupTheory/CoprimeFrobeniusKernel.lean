/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

/-!
# Stability helpers for the coprime Frobenius kernel argument (Peterfalvi (9.1) corollary (i))

Peterfalvi (9.1) corollary (i) states that for a coprime action of a Frobenius group `L = U ⋊ E`
on a finite solvable group `H`, `C_H(E) = 1 ⟹ U` centralizes `H`.  The proof is a strong induction
on `|H|`: take a minimal `φ(L)`-invariant normal subgroup `N` (elementary abelian), show `U` is
trivial on `N` (BG Lemma 3.3, since `C_N(E) = 0`) and on `H/N` (induction, `C_{H/N}(E) = 1` by the
coprime fixed-point lift Isaacs Cor 3.28), then conclude `U` is trivial on `H` by the **stability**
step proved here.

The stability step is purely group-theoretic: an automorphism `α` of `H` that fixes `N` pointwise
and is trivial modulo `N` (`h⁻¹ * α h ∈ N` for all `h`) satisfies `α^k h = h * (h⁻¹ * α h)^k`; when
`N` has exponent dividing `p` this forces `α^p = 1`, and combined with `α` having order prime to `p`
(the coprime hypothesis) gives `α = 1`.

This file holds only the elementary stability lemmas; the full corollary (i) assembles them with the
chief-series / BG 3.3 machinery in `OddOrder.GroupTheory.CoprimeAction`.
-/

namespace OddOrder.GroupTheory.CoprimeFrobeniusKernel

variable {H : Type*} [Group H]

/-- **Iterate formula for a mod-`N`-trivial automorphism.**  If `α : MulAut H` fixes the subgroup
`N` pointwise and `h⁻¹ * α h ∈ N` for every `h` (i.e. `α` is trivial on `H/N`), then iterating `α`
multiplies the "displacement" `h⁻¹ * α h ∈ N`:  `(α^k) h = h * (h⁻¹ * α h)^k`.

The cross terms vanish because each displacement lies in `N`, which `α` fixes pointwise. -/
theorem mulAut_iterate_apply (α : MulAut H) {N : Subgroup H}
    (hfix : ∀ n ∈ N, α n = n) (hmod : ∀ h : H, h⁻¹ * α h ∈ N) :
    ∀ (k : ℕ) (h : H), (α ^ k) h = h * (h⁻¹ * α h) ^ k := by
  intro k
  induction k with
  | zero => intro h; simp
  | succ k ih =>
    intro h
    have key : α h = h * (h⁻¹ * α h) := by group
    calc (α ^ (k + 1)) h = α ((α ^ k) h) := by rw [pow_succ']; rfl
      _ = α (h * (h⁻¹ * α h) ^ k) := by rw [ih]
      _ = α h * (α (h⁻¹ * α h)) ^ k := by rw [map_mul, map_pow]
      _ = α h * (h⁻¹ * α h) ^ k := by rw [hfix _ (hmod h)]
      _ = h * (h⁻¹ * α h) ^ (k + 1) := by rw [pow_succ', ← mul_assoc, ← key]

/-- **`p`-power triviality (stability group has exponent `p`).**  If `α : MulAut H` fixes `N`
pointwise, is trivial modulo `N`, and every element of `N` satisfies `n^p = 1` (e.g. `N` elementary
abelian of exponent `p`), then `α^p = 1`. -/
theorem mulAut_pow_eq_one_of_exponent (α : MulAut H) {N : Subgroup H} {p : ℕ}
    (hfix : ∀ n ∈ N, α n = n) (hmod : ∀ h : H, h⁻¹ * α h ∈ N)
    (hexp : ∀ n ∈ N, n ^ p = 1) :
    α ^ p = 1 := by
  refine MulEquiv.ext (fun h => ?_)
  change (α ^ p) h = h
  rw [mulAut_iterate_apply α hfix hmod p h, hexp _ (hmod h), mul_one]

/-- **Stability ⟹ triviality under a coprime order.**  If `α` is `p`-power-trivial (fixes `N`
pointwise, trivial mod `N`, `N` of exponent dividing `p`) and additionally `α^m = 1` for some `m`
coprime to `p`, then `α = 1`.  (In corollary (i), `m = orderOf (φ u)` divides `|U|`, coprime to the
chief-factor prime `p`.) -/
theorem mulAut_eq_one_of_exponent_of_coprime (α : MulAut H) {N : Subgroup H} {p m : ℕ}
    (hfix : ∀ n ∈ N, α n = n) (hmod : ∀ h : H, h⁻¹ * α h ∈ N)
    (hexp : ∀ n ∈ N, n ^ p = 1) (hm : α ^ m = 1) (hcop : Nat.Coprime p m) :
    α = 1 := by
  have hp : α ^ p = 1 := mulAut_pow_eq_one_of_exponent α hfix hmod hexp
  -- `orderOf α` divides both `p` and `m`, which are coprime, so `orderOf α = 1`.
  have hdp : orderOf α ∣ p := orderOf_dvd_of_pow_eq_one hp
  have hdm : orderOf α ∣ m := orderOf_dvd_of_pow_eq_one hm
  have hgcd : Nat.gcd p m = 1 := hcop
  have hd1 : orderOf α ∣ 1 := hgcd ▸ Nat.dvd_gcd hdp hdm
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)

end OddOrder.GroupTheory.CoprimeFrobeniusKernel
