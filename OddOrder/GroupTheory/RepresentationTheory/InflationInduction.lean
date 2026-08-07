/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.InflationCharacter
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
import OddOrder.GroupTheory.RepresentationTheory.InducedTransport

/-!
# Inflation ∘ induction: the P-inflation norm bridge

Generic representation-theory infrastructure connecting an induced character on `G` with the
induced character on a quotient `G ⧸ N`, used for Peterfalvi (13.18.b)'s identification
`Ind_{PW₁}^S 1_{PW₁} = γ = Ind_{W̄₁}^{S̄} 1` (with `S̄ = S/P`).

## Main results

* `OddOrder.RepresentationTheory.inner_compHom_mk'_eq` — **P1, inflation isometry.**  The
  class-function inner product is preserved by pullback along the quotient map `mk' N`:
  `⟨φ ∘ mk', ψ ∘ mk'⟩_G = ⟨φ, ψ⟩_{G⧸N}` (the fibers of `mk'` all have card `|N|`, and the
  `⅟|G|·|N| = ⅟|G⧸N|` normalization cancels).  Generalizes the MulEquiv version
  `inner_compHom_of_mulEquiv` (`InducedTransport.lean`) to a genuine quotient.
* `OddOrder.RepresentationTheory.induce_one_eq_compHom_induce_one_of_le` — **P2, trivial-character
  induction–inflation commute.**  For `N ⊴ G`, `N ≤ A`, `Ind_A^G 1_A = (Ind_{A/N}^{G/N} 1) ∘ mk'`.
  Both sides are permutation characters; equality is pointwise via `induce_one_apply`
  (the filter-count `{x : x⁻¹gx ∈ A}` is the `mk'`-preimage of `{xq : xq⁻¹ḡxq ∈ A/N}`,
  `|N|`-to-`1`).

These package the "(1.6.b)" identification Peterfalvi uses in (13.18.a,b): together with
`norm_induce_one_frobenius` on the Frobenius quotient `S̄`, they give
`‖Ind_{PW₁}^S 1‖² = (u−1)/q + 1`.
-/

namespace OddOrder.RepresentationTheory


variable {G : Type*} [Group G]

open scoped Classical in
/-- **Fiber cardinality of the quotient map.**  The number of `g : G` mapping to a fixed coset
`q : G ⧸ N` under `QuotientGroup.mk` equals `|N|` (every fiber is a coset of `N`,
`QuotientGroup.card_preimage_mk` with a singleton). -/
theorem card_filter_mk_eq {N : Subgroup G} [Fintype G] (q : G ⧸ N) :
    (Finset.univ.filter (fun g : G => (QuotientGroup.mk g : G ⧸ N) = q)).card = Nat.card ↥N := by
  have hcard : (Finset.univ.filter (fun g : G => (QuotientGroup.mk g : G ⧸ N) = q)).card
      = Nat.card ↥((QuotientGroup.mk : G → G ⧸ N) ⁻¹' ({q} : Set (G ⧸ N))) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine congrArg Finset.card ?_
    ext g
    simp [Set.mem_preimage]
  rw [hcard, QuotientGroup.card_preimage_mk N ({q} : Set (G ⧸ N))]
  simp

open scoped Classical in
/-- **P1 — inflation isometry for the quotient map.**  Pullback along `mk' N` preserves the
class-function inner product: `⟨compHom (mk' N) φ, compHom (mk' N) ψ⟩_G = ⟨φ, ψ⟩_{G⧸N}`.

Every fiber of `QuotientGroup.mk` has cardinality `|N|` (`card_filter_mk_eq`), so the
unscaled inner sum over `G` is `|N|` times the one over `G ⧸ N`; the normalizations
`⅟|G|` and `⅟|G⧸N|` differ by exactly that factor (`Nat.card G = Nat.card (G⧸N) · Nat.card N`). -/
theorem inner_compHom_mk'_eq {N : Subgroup G} [N.Normal] [Fintype G] [Fintype (G ⧸ N)]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card (G ⧸ N) : ℂ)]
    (φ ψ : ClassFunction (G ⧸ N) ℂ) :
    ClassFunction.inner (ClassFunction.compHom (QuotientGroup.mk' N) φ)
        (ClassFunction.compHom (QuotientGroup.mk' N) ψ) = ClassFunction.inner φ ψ := by
  have hfib : ∀ q : G ⧸ N,
      (Finset.univ.filter (fun g : G => (QuotientGroup.mk g : G ⧸ N) = q)).card = Nat.card ↥N :=
    fun q => card_filter_mk_eq q
  -- Unscaled inner sum over `G` is `|N|` times the one over `G ⧸ N`.
  have key : (∑ g : G, (ClassFunction.compHom (QuotientGroup.mk' N) φ) g *
        star ((ClassFunction.compHom (QuotientGroup.mk' N) ψ) g))
      = (Nat.card ↥N : ℂ) * ∑ q : G ⧸ N, φ q * star (ψ q) := by
    simp only [ClassFunction.compHom_apply, QuotientGroup.mk'_apply]
    rw [← Finset.sum_fiberwise' (Finset.univ) (fun g : G => (QuotientGroup.mk g : G ⧸ N))
      (fun q => φ q * star (ψ q)), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hfib q]
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.inner_eq_inv_card_mul_innerSum,
    ClassFunction.innerSum, ClassFunction.innerSum, key, ← mul_assoc]
  -- `⅟|G| · |N| = ⅟|G⧸N|`.
  have hcardG : (Nat.card G : ℂ) = (Nat.card (G ⧸ N) : ℂ) * (Nat.card ↥N : ℂ) := by
    rw [← Nat.cast_mul, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hne2 : (Nat.card ↥N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  congr 1
  rw [invOf_eq_inv, invOf_eq_inv, hcardG, mul_inv, mul_assoc, inv_mul_cancel₀ hne2, mul_one]

open scoped Classical in
/-- **Permutation-character value of the induced trivial character.**  `Ind_H^G 1_H` at `g` is
`⅟|H|` times the number of conjugators `x` sending `g` into `H` (the trivial character contributes
`1` on each such `x`).  (Generic; the same fact as `S15_SAndT_Setup.induce_one_apply`, reproven
upstream so the P-inflation bridge below can cite it.) -/
private theorem induceTriv_apply {H : Subgroup G} [Fintype G] [Invertible (Nat.card ↥H : ℂ)]
    (g : G) :
    ClassFunction.induce H (trivialClassFunction ↥H) g
      = ⅟(Nat.card ↥H : ℂ) *
        ((Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ H)).card : ℂ) := by
  rw [ClassFunction.induce_apply_eq_sum_filter]
  congr 1
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ))
      (fun x hx => by
        rw [ClassFunction.induceTerm_of_mem (trivialClassFunction ↥H) (Finset.mem_filter.mp hx).2]
        rfl),
    Finset.sum_const, nsmul_eq_mul, mul_one]

open scoped Classical in
/-- **Peterfalvi (1.6)(b)** (book p. 7): *induction commutes with inflation along a normal subgroup
contained in the kernel.*

Let `N ⊴ G` with `N ≤ H`, let `θ₁` be a class function on `H/N = H.map (mk' N)`, and let `θ` be the
class function on `H` it inflates to -- i.e. `θ(x) = θ₁(xN)` for all `x ∈ H` (`hinfl`).  Then

`Ind_H^G θ = (Ind_{H/N}^{G/N} θ₁) ∘ mk'`.

This is the book's statement: there `θ ∈ Irr(H)` is given with `N ⊆ Ker θ`, `θ₁` is *defined* by
`θ₁(xN) = θ(x)`, and `χ` -- the character of `G/N` with `χ(xN) = (Ind_H^G θ)(x)`, which exists by
(1.6)(a) -- is shown to equal `Ind_{H/N}^{G/N} θ₁`.  Saying "`χ` inflates to `Ind_H^G θ`" is the
same as the displayed equation, and stating it that way avoids having to construct `χ` (the
equation determines it, `mk'` being surjective).  Neither irreducibility of `θ` nor `N ⊆ Ker θ` is
needed beyond what `hinfl` already says: `hinfl` *is* the assertion that `θ` factors through `H/N`,
which for a character is exactly `N ⊆ Ker θ`.

*Proof* (the book's).  Both sides vanish off `H` resp. `H/N`, and the conjugator condition
`x⁻¹gx ∈ H` transports along `mk` (`N ≤ H`), so the two induction sums have matching terms:
`induceTerm H θ x g = induceTerm (H/N) θ₁ (mk x) (mk g)`.  Summing over `G` rather than `G/N`
overcounts by the constant fiber size `|N|` (`card_filter_mk_eq`), which the normalization
`⅟|H| = ⅟(|N|·|H/N|)` absorbs. -/
theorem induce_eq_compHom_induce_of_inflation {N H : Subgroup G} [N.Normal] (hNH : N ≤ H)
    [Fintype G] [Fintype (G ⧸ N)] [Invertible (Nat.card ↥H : ℂ)]
    [Invertible (Nat.card ↥(H.map (QuotientGroup.mk' N)) : ℂ)]
    (θ : ClassFunction ↥H ℂ) (θ₁ : ClassFunction ↥(H.map (QuotientGroup.mk' N)) ℂ)
    (hinfl : ∀ (x : G) (hx : x ∈ H),
      θ ⟨x, hx⟩ = θ₁ ⟨QuotientGroup.mk x, Subgroup.mem_map_of_mem _ hx⟩) :
    ClassFunction.induce H θ
      = ClassFunction.compHom (QuotientGroup.mk' N)
          (ClassFunction.induce (H.map (QuotientGroup.mk' N)) θ₁) := by
  classical
  -- Membership bridge: `mk y ∈ H/N ↔ y ∈ H` (uses `N ≤ H`).
  have hmem : ∀ y : G, (QuotientGroup.mk y : G ⧸ N) ∈ H.map (QuotientGroup.mk' N) ↔ y ∈ H := by
    intro y
    rw [← QuotientGroup.mk'_apply, ← Subgroup.mem_comap, Subgroup.comap_map_eq,
      QuotientGroup.ker_mk', sup_eq_left.mpr hNH]
  -- `|H| = |N| · |H/N|`: `H` is the `mk`-preimage of `H/N`, whose fibers all have size `|N|`.
  have hcardH : (Nat.card ↥H : ℂ)
      = (Nat.card ↥N : ℂ) * (Nat.card ↥(H.map (QuotientGroup.mk' N)) : ℂ) := by
    have hset : ((QuotientGroup.mk : G → G ⧸ N) ⁻¹'
        (H.map (QuotientGroup.mk' N) : Set (G ⧸ N))) = (H : Set G) := by
      ext y
      rw [Set.mem_preimage, SetLike.mem_coe, SetLike.mem_coe, hmem y]
    have h := QuotientGroup.card_preimage_mk N (H.map (QuotientGroup.mk' N) : Set (G ⧸ N))
    rw [hset, SetLike.coe_sort_coe, SetLike.coe_sort_coe] at h
    exact_mod_cast h
  have hneN : (Nat.card ↥N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  ext g
  -- Termwise match, the heart of the proof.
  have hterm : ∀ x : G, ClassFunction.induceTerm H θ x g
      = ClassFunction.induceTerm (H.map (QuotientGroup.mk' N)) θ₁
          (QuotientGroup.mk x) (QuotientGroup.mk g) := by
    intro x
    have hconj : ((QuotientGroup.mk x : G ⧸ N)⁻¹ * QuotientGroup.mk g * QuotientGroup.mk x)
        = (QuotientGroup.mk (x⁻¹ * g * x) : G ⧸ N) := by
      simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    by_cases hx : x⁻¹ * g * x ∈ H
    · rw [ClassFunction.induceTerm_of_mem θ hx,
        ClassFunction.induceTerm_of_mem θ₁ (by rw [hconj]; exact (hmem _).mpr hx)]
      rw [hinfl (x⁻¹ * g * x) hx]
      congr 1
    · rw [ClassFunction.induceTerm_of_not_mem θ hx,
        ClassFunction.induceTerm_of_not_mem θ₁ (by rw [hconj]; exact fun h => hx ((hmem _).mp h))]
  -- Sum over `G` = `|N|` × sum over `G ⧸ N` (constant fiber size).
  have hsum : (∑ x : G, ClassFunction.induceTerm (H.map (QuotientGroup.mk' N)) θ₁
        (QuotientGroup.mk x) (QuotientGroup.mk g))
      = (Nat.card ↥N : ℂ) * ∑ q : G ⧸ N,
          ClassFunction.induceTerm (H.map (QuotientGroup.mk' N)) θ₁ q (QuotientGroup.mk g) := by
    rw [← Finset.sum_fiberwise' (Finset.univ) (fun x : G => (QuotientGroup.mk x : G ⧸ N))
      (fun q => ClassFunction.induceTerm (H.map (QuotientGroup.mk' N)) θ₁ q
        (QuotientGroup.mk g)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, card_filter_mk_eq q]
  rw [ClassFunction.compHom_apply, QuotientGroup.mk'_apply, ClassFunction.induce_apply,
    ClassFunction.induce_apply, Finset.sum_congr rfl (fun x _ => hterm x), hsum, ← mul_assoc]
  -- `⅟|H| · |N| = ⅟|H/N|`.
  congr 1
  rw [invOf_eq_inv, invOf_eq_inv, hcardH, mul_inv, mul_comm ((Nat.card ↥N : ℂ))⁻¹,
    mul_assoc, inv_mul_cancel₀ hneN, mul_one]

open scoped Classical in
/-- **P2 — trivial-character induction–inflation commute**: the `θ = 1` case of Peterfalvi (1.6)(b)
(`induce_eq_compHom_induce_of_inflation`).  For a normal
subgroup `N ⊴ G` contained in `A ≤ G`, the induced trivial character of `A` is the inflation of the
induced trivial character of the quotient subgroup `A/N = A.map (mk' N) ≤ G ⧸ N`:
`Ind_A^G 1_A = (Ind_{A/N}^{G/N} 1) ∘ mk'`.

Both are permutation characters.  Pointwise at `g` (`induceTriv_apply`): the conjugator sets
`{x : x⁻¹gx ∈ A}` and `{xq : xq⁻¹ḡxq ∈ A/N}` correspond under `mk` (`x⁻¹gx ∈ A ↔ mk(x⁻¹gx) ∈ A/N`,
using `N ≤ A`), with every fiber of `mk` of size `|N|`; the `⅟|A| = ⅟(|N|·|A/N|)` normalization
absorbs the `|N|` fiber factor. -/
theorem induce_one_eq_compHom_induce_one_of_le {N A : Subgroup G} [N.Normal] (hNA : N ≤ A)
    [Fintype G] [Fintype (G ⧸ N)] [Invertible (Nat.card ↥A : ℂ)]
    [Invertible (Nat.card ↥(A.map (QuotientGroup.mk' N)) : ℂ)] :
    ClassFunction.induce A (trivialClassFunction ↥A)
      = ClassFunction.compHom (QuotientGroup.mk' N)
          (ClassFunction.induce (A.map (QuotientGroup.mk' N))
            (trivialClassFunction ↥(A.map (QuotientGroup.mk' N)))) :=
  induce_eq_compHom_induce_of_inflation hNA (trivialClassFunction ↥A)
    (trivialClassFunction ↥(A.map (QuotientGroup.mk' N))) (fun _ _ => rfl)

open scoped Classical in
/-- **P3 — inflated class functions are orthogonal to irreducibles not killing `N`.**  For `N ⊴ G`,
any class function `φ` of `G ⧸ N` inflates to something orthogonal to every irreducible character
`ψ` of `G` whose kernel does **not** contain `N`: `⟨φ ∘ mk', ψ⟩_G = 0`.

Peterfalvi's "(13.18.b) `Ind_{PW₁}^S 1 ⊥ μ_{0j}` because `P ⊄ ker μ_{0j}`": expand `φ` in the
`Irr(G ⧸ N)` basis (`sum_inner_irreducibleCharacter_smul`); each `compHom (mk' N) χ̄` is the
irreducible `inflate N χ̄` with `N ⊆ ker` (`subset_characterKernel_inflate`), so it differs from `ψ`
(which has `N ⊄ ker`) and is orthogonal to it (`irreducibleCharacter_inner_eq_ite`). -/
theorem inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker {N : Subgroup G} [N.Normal]
    [Fintype G] [Finite (G ⧸ N)] [Finite (IrreducibleCharacter (G ⧸ N))]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card (G ⧸ N) : ℂ)]
    (φ : ClassFunction (G ⧸ N) ℂ) (ψ : IrreducibleCharacter G)
    (hψ : ¬ ((N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction G ℂ))) :
    ClassFunction.inner (ClassFunction.compHom (QuotientGroup.mk' N) φ)
        (ψ : ClassFunction G ℂ) = 0 := by
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  haveI : Fintype (IrreducibleCharacter (G ⧸ N)) := Fintype.ofFinite _
  have compHom_sum : ∀ (s : Finset (IrreducibleCharacter (G ⧸ N)))
      (a : IrreducibleCharacter (G ⧸ N) → ℂ),
      ClassFunction.compHom (QuotientGroup.mk' N)
          (∑ χ ∈ s, a χ • (χ : ClassFunction (G ⧸ N) ℂ))
        = ∑ χ ∈ s, a χ •
            ClassFunction.compHom (QuotientGroup.mk' N) (χ : ClassFunction (G ⧸ N) ℂ) := by
    intro s a
    induction s using Finset.induction with
    | empty => simp [ClassFunction.compHom_zero]
    | @insert χ s hχ ih =>
        rw [Finset.sum_insert hχ, ClassFunction.compHom_add, ClassFunction.compHom_smul, ih,
          Finset.sum_insert hχ]
  conv_lhs => rw [← sum_inner_irreducibleCharacter_smul φ, compHom_sum]
  rw [inner_sum_left]
  refine Finset.sum_eq_zero (fun χ _ => ?_)
  have hne : inflate N χ ≠ ψ := fun heq =>
    hψ (heq ▸ subset_characterKernel_inflate N χ)
  rw [ClassFunction.inner_smul_left, ← inflate_coe N χ, irreducibleCharacter_inner_eq_ite,
    if_neg hne, mul_zero]

end OddOrder.RepresentationTheory
