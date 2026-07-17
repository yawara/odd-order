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

open scoped Classical

variable {G : Type*} [Group G]

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

/-- **P2 — trivial-character induction–inflation commute** (Peterfalvi "(1.6.b)").  For a normal
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
            (trivialClassFunction ↥(A.map (QuotientGroup.mk' N)))) := by
  -- Membership bridge: `mk' y ∈ A/N ↔ y ∈ A` (`N ≤ A`).
  have hmem : ∀ y : G, (QuotientGroup.mk' N y ∈ A.map (QuotientGroup.mk' N)) ↔ y ∈ A := by
    intro y
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNA]
  -- `|A| = |N| · |A/N|`: `A` is the `mk`-preimage of `A/N`, whose fibers all have size `|N|`.
  have hcardA : (Nat.card ↥A : ℂ)
      = (Nat.card ↥N : ℂ) * (Nat.card ↥(A.map (QuotientGroup.mk' N)) : ℂ) := by
    have hset : ((QuotientGroup.mk : G → G ⧸ N) ⁻¹'
        (A.map (QuotientGroup.mk' N) : Set (G ⧸ N))) = (A : Set G) := by
      ext y
      rw [Set.mem_preimage, SetLike.mem_coe, SetLike.mem_coe, ← QuotientGroup.mk'_apply, hmem y]
    have h := QuotientGroup.card_preimage_mk N (A.map (QuotientGroup.mk' N) : Set (G ⧸ N))
    rw [hset, SetLike.coe_sort_coe, SetLike.coe_sort_coe] at h
    exact_mod_cast h
  have hneN : (Nat.card ↥N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  ext g
  -- Conjugator condition transports along `mk`.
  have hPQ : ∀ x : G, (x⁻¹ * g * x ∈ A) ↔
      ((QuotientGroup.mk x : G ⧸ N)⁻¹ * (QuotientGroup.mk g) * (QuotientGroup.mk x)
        ∈ A.map (QuotientGroup.mk' N)) := by
    intro x
    rw [← hmem (x⁻¹ * g * x)]
    simp only [QuotientGroup.mk'_apply, map_mul, map_inv]
  rw [ClassFunction.compHom_apply, induceTriv_apply (H := A),
    induceTriv_apply (H := A.map (QuotientGroup.mk' N)), QuotientGroup.mk'_apply]
  -- Fiberwise count: `#{x : x⁻¹gx∈A} = |N| · #{xq : xq⁻¹ḡxq∈A/N}`.
  have hmapsto : ∀ x ∈ Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ A),
      (QuotientGroup.mk x : G ⧸ N) ∈ Finset.univ.filter
        (fun xq : G ⧸ N => xq⁻¹ * (QuotientGroup.mk g) * xq ∈ A.map (QuotientGroup.mk' N)) :=
    fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hPQ x).mp (Finset.mem_filter.mp hx).2⟩
  have hper : ∀ xq ∈ Finset.univ.filter
        (fun xq : G ⧸ N => xq⁻¹ * (QuotientGroup.mk g) * xq ∈ A.map (QuotientGroup.mk' N)),
      ((Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ A)).filter
          (fun a => (QuotientGroup.mk a : G ⧸ N) = xq)).card = Nat.card ↥N := by
    intro xq hxq
    have hQ : xq⁻¹ * (QuotientGroup.mk g) * xq ∈ A.map (QuotientGroup.mk' N) :=
      (Finset.mem_filter.mp hxq).2
    have hfeq : (Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ A)).filter
          (fun a => (QuotientGroup.mk a : G ⧸ N) = xq)
        = Finset.univ.filter (fun a : G => (QuotientGroup.mk a : G ⧸ N) = xq) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro a _
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨(hPQ a).mpr ?_, h⟩
        rw [h]; exact hQ
    rw [hfeq]
    exact card_filter_mk_eq xq
  have hcount : (Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ A)).card
      = Nat.card ↥N * (Finset.univ.filter
          (fun xq : G ⧸ N => xq⁻¹ * (QuotientGroup.mk g) * xq
            ∈ A.map (QuotientGroup.mk' N))).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmapsto, Finset.sum_congr rfl hper, Finset.sum_const,
      smul_eq_mul, mul_comm]
  rw [hcount]
  push_cast
  -- `⅟|A| · (|N| · c) = ⅟|A/N| · c`.
  rw [← mul_assoc]
  congr 1
  rw [invOf_eq_inv, invOf_eq_inv, hcardA, mul_inv, mul_comm ((Nat.card ↥N : ℂ))⁻¹,
    mul_assoc, inv_mul_cancel₀ hneN, mul_one]

/-- **P3 — inflated class functions are orthogonal to irreducibles not killing `N`.**  For `N ⊴ G`,
any class function `φ` of `G ⧸ N` inflates to something orthogonal to every irreducible character
`ψ` of `G` whose kernel does **not** contain `N`: `⟨φ ∘ mk', ψ⟩_G = 0`.

Peterfalvi's "(13.18.b) `Ind_{PW₁}^S 1 ⊥ μ_{0j}` because `P ⊄ ker μ_{0j}`": expand `φ` in the
`Irr(G ⧸ N)` basis (`sum_inner_irreducibleCharacter_smul`); each `compHom (mk' N) χ̄` is the
irreducible `inflate N χ̄` with `N ⊆ ker` (`subset_characterKernel_inflate`), so it differs from `ψ`
(which has `N ⊄ ker`) and is orthogonal to it (`irreducibleCharacter_inner_eq_ite`). -/
theorem inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker {N : Subgroup G} [N.Normal]
    [Fintype G] [Fintype (G ⧸ N)] [Fintype (IrreducibleCharacter (G ⧸ N))]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card (G ⧸ N) : ℂ)]
    (φ : ClassFunction (G ⧸ N) ℂ) (ψ : IrreducibleCharacter G)
    (hψ : ¬ ((N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction G ℂ))) :
    ClassFunction.inner (ClassFunction.compHom (QuotientGroup.mk' N) φ)
        (ψ : ClassFunction G ℂ) = 0 := by
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
