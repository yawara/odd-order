/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finite.Prod
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.GroupTheory.Coset.Card

/-!
# The imprimitive order bound: `|U| ≤ (p − 1)^(q−1)`

The σ-theory foundation of Peterfalvi (9.7)(a) (the *non-Galois* branch of `typeP_Galois`, issue
9000): when the abelian complement `U` acts on the Frobenius kernel quotient `Hbar ≅ 𝔽_p^q` (`q`
prime) **reducibly**, `Hbar` decomposes into `q` one-dimensional blocks `H1^w` (`|H1| = p`) permuted
cyclically by `W₁`.  Writing `a := |U : C_U(H1)|` for the order of the scalar action on a block
(`a ∣ p − 1`, since `U/C_U(H1) ↪ 𝔽_p^×`), the map `x ↦ (block-scalar_i(x)/block-scalar_1(x))_i`
embeds `Ū` injectively into `ℤ_a^{q−1}` (the `−1` normalizing by block `1`), whence

  `u = |Ū| ≤ a^{q−1} ≤ (p − 1)^{q−1}`.

This file supplies the **generic arithmetic engine** — an injective map into a `(q−1)`-fold product
of an `a`-element type bounds the source by `a^{q−1}`, and `a ≤ p − 1` lifts it to `(p−1)^{q−1}`.
The structural inputs (the block decomposition and the injectivity of the ratio embedding) are the
imprimitive `𝔽_p`-module content, supplied by the caller (the Pf (9.7)(a) assembly); combined with
`(p−1)^{q−1} ≤ (p^q−1)/(p−1)` this yields the non-Galois half of `basic_structure.u_bound`.
-/

namespace OddOrder.RepresentationTheory

/-- **Embedding card bound**: an injective map from `U` into the `n`-fold function type `Fin n → M`
(`M` finite) bounds `|U|` by `|M|^n`.  General `Nat.card` fact; the arithmetic core of the
imprimitive order bound (with `M = ℤ_a`, `n = q − 1`). -/
theorem card_le_pow_of_injective_to_pi {U M : Type*} [Finite M] {n : ℕ}
    {f : U → (Fin n → M)} (hf : Function.Injective f) :
    Nat.card U ≤ Nat.card M ^ n := by
  have h1 : Nat.card U ≤ Nat.card (Fin n → M) := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card (Fin n → M) = Nat.card M ^ n := by
    simp [Nat.card_pi]
  rwa [h2] at h1

/-- **Imprimitive order bound** (Peterfalvi (9.7)(a) / (13.2.c) non-Galois branch): if `U` embeds
injectively into `Fin (q−1) → A` with `|A| = a` and `a ≤ p − 1`, then `|U| ≤ (p−1)^{q−1}`.

Assembles `card_le_pow_of_injective_to_pi` (`|U| ≤ a^{q−1}`) with the monotonicity `a ≤ p − 1`
(`Nat.pow_le_pow_left`).  The caller supplies the ratio embedding `Ū ↪ ℤ_a^{q−1}` and `a ∣ p − 1`
(hence `a ≤ p − 1`) from the imprimitive block structure; the downstream bridge
`(p−1)^{q−1} ≤ (p^q−1)/(p−1)` then gives `u ≤ (p^q−1)/(p−1)`. -/
theorem card_le_pow_sub_one_of_injective_imprimitive
    {U A : Type*} [Finite A] {p q a : ℕ}
    (hcardA : Nat.card A = a) (ha : a ≤ p - 1)
    {f : U → (Fin (q - 1) → A)} (hf : Function.Injective f) :
    Nat.card U ≤ (p - 1) ^ (q - 1) := by
  have hb : Nat.card U ≤ a ^ (q - 1) := by
    have := card_le_pow_of_injective_to_pi hf
    rwa [hcardA] at this
  exact hb.trans (Nat.pow_le_pow_left ha _)

/-- **The block-scalar ratio homomorphism** in Peterfalvi (9.7.a):
`x ↦ (φ_{i+1}(x) / φ_0(x))_i`.

Normalizing all scalar coordinates by the zeroth one removes the common-scalar diagonal and leaves
`n` coordinates from an `n + 1` block system.  The target is a group because scalar values lie
in the commutative group `A`. -/
def blockScalarRatioHom {Ubar A : Type*} [Group Ubar] [CommGroup A] {n : ℕ}
    (φ : Fin (n + 1) → (Ubar →* A)) : Ubar →* (Fin n → A) where
  toFun x i := φ i.succ x / φ 0 x
  map_one' := by
    ext i
    simp
  map_mul' x y := by
    ext i
    simp only [Pi.mul_apply, map_mul, div_eq_mul_inv, mul_inv_rev]
    ac_rfl

/-- **Injectivity of the block-scalar ratio homomorphism.**  If an element whose scalar values are
constant on all `n + 1` blocks is necessarily trivial, then the normalized ratio homomorphism is
injective.  This is the qualitative form of the (9.7.a) product embedding; unlike its cardinality
corollaries below, it can be restricted to Sylow subgroups by downstream consumers. -/
theorem blockScalarRatioHom_injective {Ubar A : Type*} [Group Ubar] [CommGroup A] {n : ℕ}
    (φ : Fin (n + 1) → (Ubar →* A))
    (hconst : ∀ x : Ubar, (∀ i : Fin (n + 1), φ i x = φ 0 x) → x = 1) :
    Function.Injective (blockScalarRatioHom φ) := by
  intro x y hxy
  have hxy' : ∀ i : Fin n, φ i.succ x / φ 0 x = φ i.succ y / φ 0 y :=
    fun i => congrFun hxy i
  have hz : x * y⁻¹ = 1 := by
    apply hconst
    refine Fin.cases rfl (fun j => ?_)
    have h : φ j.succ x * φ 0 y = φ j.succ y * φ 0 x :=
      (div_eq_div_iff_mul_eq_mul).mp (hxy' j)
    change φ j.succ (x * y⁻¹) = φ 0 (x * y⁻¹)
    rw [map_mul, map_mul, map_inv, map_inv, ← div_eq_mul_inv, ← div_eq_mul_inv,
      div_eq_div_iff_mul_eq_mul, mul_comm (φ 0 x)]
    exact h
  exact mul_inv_eq_one.mp hz

/-- **Ratio-embedding order divisibility**: under the block-scalar hypotheses of
`card_le_pow_of_block_scalars`, the order of `Ubar` divides `|A|^n`.

The ratio map is a group homomorphism
`x ↦ (φ_{i+1}(x) / φ_0(x))_i : Ubar →* (Fin n → A)`.  The `hconst` hypothesis makes it
injective, so Lagrange gives the divisibility of finite group orders.  Unlike the cardinality-only
bound below, this form retains prime-factor information; Peterfalvi (13.13) uses it to remove the
2-primary part of `(p - 1)^(q - 1)` for an odd-order source group. -/
theorem card_dvd_pow_of_block_scalars {Ubar A : Type*} [CommGroup Ubar] [Finite Ubar]
    [CommGroup A] [Finite A]
    {n : ℕ} (φ : Fin (n + 1) → (Ubar →* A))
    (hconst : ∀ x : Ubar, (∀ i : Fin (n + 1), φ i x = φ 0 x) → x = 1) :
    Nat.card Ubar ∣ Nat.card A ^ n := by
  simpa [Nat.card_pi] using
    Subgroup.card_dvd_of_injective (blockScalarRatioHom φ)
      (blockScalarRatioHom_injective φ hconst)

/-- **Ratio embedding from block scalars** (the injectivity core of Peterfalvi (9.7)(a)'s `psi`,
`PFsection9.v:442`): given a finite commutative group `Ū` with `q = n+1` scalar characters
`φ : Fin (n+1) → (Ū →* A)` (the action of `Ū` on the `n+1` imprimitivity blocks, each `𝔽_p`-line, so
`A = 𝔽_p^×`) such that **no nonidentity element acts by a single scalar on every block**
(`hconst`), the ratio map `x ↦ (φ_{i+1}(x)·φ_0(x)⁻¹)_i : Ū → (Fin n → A)` is injective, whence

  `|Ū| ≤ |A|^n`.

The `−1` (`n = q − 1` free coordinates) comes from normalizing by block `0`.  With `|A| = a ∣ p − 1`
this is `u ≤ a^{q−1} ≤ (p−1)^{q−1}` (`card_le_cyclotomicQuotient_of_injective_imprimitive`).  The
caller supplies the block scalars `φ` and `hconst` from the imprimitive `𝔽_p`-module decomposition
(the `W₁`-permuted blocks). -/
theorem card_le_pow_of_block_scalars {Ubar A : Type*} [CommGroup Ubar] [Finite Ubar]
    [CommGroup A] [Finite A]
    {n : ℕ} (φ : Fin (n + 1) → (Ubar →* A))
    (hconst : ∀ x : Ubar, (∀ i : Fin (n + 1), φ i x = φ 0 x) → x = 1) :
    Nat.card Ubar ≤ Nat.card A ^ n := by
  calc Nat.card Ubar
      ≤ Nat.card (Fin n → A) := Nat.card_le_card_of_injective _
        (blockScalarRatioHom_injective φ hconst)
    _ = Nat.card A ^ n := by simp [Nat.card_pi]

/-- **Non-Galois → cyclotomic-quotient bridge**: `(p − 1)^{q−1} ≤ (p^q − 1)/(p − 1)`.

`(p−1)^{q−1}·(p−1) = (p−1)^q < p^q`, so `(p−1)^q ≤ p^q − 1`; division by `p − 1`
gives the claim.
Pure `ℕ` arithmetic, `sorry`-free.  Lifts the non-Galois bound `u ≤ (p−1)^{q−1}` to the uniform
`u ≤ (p^q − 1)/(p − 1)` matching the Galois branch (`SingerLineBound`). -/
theorem pow_sub_one_le_cyclotomicQuotient {p q : ℕ} (hp : 2 ≤ p) (hq : 1 ≤ q) :
    (p - 1) ^ (q - 1) ≤ (p ^ q - 1) / (p - 1) := by
  have hp1 : 0 < p - 1 := by omega
  rw [Nat.le_div_iff_mul_le hp1]
  have hpow : (p - 1) ^ (q - 1) * (p - 1) = (p - 1) ^ q := by
    rw [← pow_succ]; congr 1; omega
  rw [hpow]
  have hlt : (p - 1) ^ q < p ^ q := Nat.pow_lt_pow_left (by omega) (by omega)
  have hpq1 : 1 ≤ p ^ q := Nat.one_le_pow _ _ (by omega)
  omega

/-- **Imprimitive order bound, cyclotomic-quotient form** (Peterfalvi (13.2.c) non-Galois half):
under the hypotheses of `card_le_pow_sub_one_of_injective_imprimitive` and `2 ≤ p`, `1 ≤ q`,

  `|U| ≤ (p^q − 1)/(p − 1)`,

matching the Galois branch's conclusion so the two combine into `basic_structure.u_bound`.  Chains
`card_le_pow_sub_one_of_injective_imprimitive` (`≤ (p−1)^{q−1}`) with the bridge
`pow_sub_one_le_cyclotomicQuotient`. -/
theorem card_le_cyclotomicQuotient_of_injective_imprimitive
    {U A : Type*} [Finite A] {p q a : ℕ} (hp : 2 ≤ p) (hq : 1 ≤ q)
    (hcardA : Nat.card A = a) (ha : a ≤ p - 1)
    {f : U → (Fin (q - 1) → A)} (hf : Function.Injective f) :
    Nat.card U ≤ (p ^ q - 1) / (p - 1) :=
  (card_le_pow_sub_one_of_injective_imprimitive hcardA ha hf).trans
    (pow_sub_one_le_cyclotomicQuotient hp hq)

end OddOrder.RepresentationTheory
