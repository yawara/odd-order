/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup

/-!
# Transport of Frobenius groups across isomorphisms

A group isomorphism `e : G ≃* H` carries the whole Frobenius structure of `G = N ⋊ A`
(`IsFrobeniusGroup G N A`) onto its image: `IsFrobeniusGroup H (N.map e) (A.map e)`, with kernel
`e(N)` and complement `e(A)`.  Every defining datum transports:

* normality (`Subgroup.map` of a normal subgroup along a *surjective* hom is normal),
* the complement relation `N ⊓ A = ⊥`, `N ⊔ A = ⊤` (both preserved by the order-isomorphism
  `Subgroup.mapEquiv` induced by `e`),
* nontriviality of kernel/complement (an isomorphism sends `⊥` to `⊥`), and
* the conjugation-Frobenius condition `a·n·a⁻¹ ≠ n` (a group homomorphism intertwines products
  and inverses, so it transports pointwise).

This is the group-level analogue of the *action*-level `IsFrobeniusAction.quotient` (Isaacs Cor 6.2,
`FrobeniusActionTI.lean`); the two are complementary — the action version descends the conjugation
action of `A` on `N` to a quotient `N/M` (`M ≤ N`), whereas this version transports the entire
Frobenius *group* along an ambient isomorphism.

## Motivation (Peterfalvi (14.9), the `calT1` inertia)

In (14.9) the type-`P` group `T` has `T' = QV = Q ⋊ V` with a Frobenius subgroup `V ⋊ W₂ ≤ T`
(kernel `V`, complement `W₂`; `S15.isMulCommutative_V`).  The quotient `T/Q` is Frobenius with
kernel `QV/Q ≅ V` and complement `W₂Q/Q ≅ W₂` — but *not* because one "quotients a Frobenius group
by a subgroup of its kernel" (`Q ⊄ V`, and that operation is false in general without coprimality).
Rather, the composite `V ⋊ W₂ ↪ T ↠ T/Q` is an **isomorphism onto its image**
(as `(V ⊔ W₂) ⊓ Q = ⊥`), so the Frobenius structure of `V ⋊ W₂` *transports* onto `T/Q` by
`isFrobeniusGroup_map_equiv` below.  Feeding the resulting quotient-Frobenius group to
`inertia_eq_of_frobeniusGroup` (via the inertia/inflation-commutation bridge, the companion brick)
yields `I_T(inflate_Q θ) = QV` for nonprincipal `θ ∈ Irr(QV/Q)`, the sole genuinely-missing input to
the `|calT1| = (|V|−1)/p` count.

## Main results

* `OddOrder.Isaacs.Ch06.isFrobeniusGroup_map_equiv` — `IsFrobeniusGroup G N A` transports along
  `e : G ≃* H` to `IsFrobeniusGroup H (N.map e) (A.map e)`.
* `OddOrder.Isaacs.Ch06.IsFrobeniusGroup.mapEquiv` — the same, as dot-notation on
  `IsFrobeniusGroup`.
-/

namespace OddOrder.Isaacs.Ch06

variable {G H : Type*} [Group G] [Group H]

/-- **Frobenius groups transport across isomorphisms.**  If `G = N ⋊ A` is a Frobenius group
(`IsFrobeniusGroup G N A`) and `e : G ≃* H` is a group isomorphism, then `H = e(N) ⋊ e(A)` is a
Frobenius group with kernel `e(N)` and complement `e(A)`.

Each Frobenius datum is carried along `e`: normality of `e(N)` (image of a normal subgroup under a
surjective hom), the complement relation (`e` is a bounded-lattice isomorphism on subgroups, so it
preserves `⊓ = ⊥` and `⊔ = ⊤`), the nontriviality of the two parts (an isomorphism sends `⊥` to
`⊥`), and the conjugation-Frobenius condition (transported pointwise using that `e` is a
homomorphism: `e a · e n · (e a)⁻¹ = e (a n a⁻¹)`). -/
theorem isFrobeniusGroup_map_equiv {N A : Subgroup G} (h : IsFrobeniusGroup G N A) (e : G ≃* H) :
    IsFrobeniusGroup H (N.map e.toMonoidHom) (A.map e.toMonoidHom) := by
  haveI := h.isNormal
  refine ⟨?isNormal, ?isComplement, ?ne_bot_kernel, ?ne_bot_complement, ?conj⟩
  case isNormal =>
    -- image of a normal subgroup under the *surjective* `e`.
    exact h.isNormal.map e.toMonoidHom e.surjective
  case isComplement =>
    -- `e(N)` and `e(A)` are complements: disjoint image + product-is-top.
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · -- `e(N) ⊓ e(A) = ⊥`, from `N ⊓ A = ⊥` via `map_inf` (`e` injective).
      rw [disjoint_iff, ← Subgroup.map_inf _ _ e.toMonoidHom e.injective,
        disjoint_iff.mp h.isComplement.disjoint, Subgroup.map_bot]
    · -- `e(N) * e(A) = ⊤` (as sets), from `N ⊔ A = ⊤` via `map_sup` + `e` surjective.
      have hsup : N.map e.toMonoidHom ⊔ A.map e.toMonoidHom = ⊤ := by
        rw [← Subgroup.map_sup, h.isComplement.sup_eq_top, ← MonoidHom.range_eq_map,
          MonoidHom.range_eq_top.mpr e.surjective]
      haveI : (N.map e.toMonoidHom).Normal := h.isNormal.map e.toMonoidHom e.surjective
      have hmul := Subgroup.normal_mul (N.map e.toMonoidHom) (A.map e.toMonoidHom)
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  case ne_bot_kernel =>
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
    exact h.ne_bot_kernel
  case ne_bot_complement =>
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
    exact h.ne_bot_complement
  case conj =>
    -- transport `a·n·a⁻¹ ≠ n` pointwise: preimages under `e` witness a violation upstream.
    intro a haA ha n hnN hn hfix
    -- `a = e a₀`, `n = e n₀` with `a₀ ∈ A`, `n₀ ∈ N`.
    obtain ⟨a₀, ha₀A, rfl⟩ := Subgroup.mem_map.mp haA
    obtain ⟨n₀, hn₀N, rfl⟩ := Subgroup.mem_map.mp hnN
    have ha₀ : a₀ ≠ 1 := fun h1 => ha (by rw [h1, map_one])
    have hn₀ : n₀ ≠ 1 := fun h1 => hn (by rw [h1, map_one])
    -- `e (a₀ n₀ a₀⁻¹) = e n₀` ⇒ `a₀ n₀ a₀⁻¹ = n₀` (injectivity), contradicting Frobenius on `G`.
    apply h.conj_frobenius a₀ ha₀A ha₀ n₀ hn₀N hn₀
    apply e.injective
    rw [map_mul, map_mul, map_inv]
    exact hfix

/-- **Frobenius groups transport across isomorphisms** (dot-notation form of
`isFrobeniusGroup_map_equiv`): `h.mapEquiv e : IsFrobeniusGroup H (e(N)) (e(A))`. -/
theorem IsFrobeniusGroup.mapEquiv {N A : Subgroup G} (h : IsFrobeniusGroup G N A) (e : G ≃* H) :
    IsFrobeniusGroup H (N.map e.toMonoidHom) (A.map e.toMonoidHom) :=
  isFrobeniusGroup_map_equiv h e

end OddOrder.Isaacs.Ch06
