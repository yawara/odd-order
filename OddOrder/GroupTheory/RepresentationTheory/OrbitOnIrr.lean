/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible

/-!
# Cardinality of an irreducibly-induced family (the `G/H`-orbit count)

For a normal subgroup `H ⊴ G` and a *conjugation-invariant* finite family `T ⊆ Irr H`, the map
`θ ↦ Ind_H^G θ` partitions `T` into fibres, each an entire `G`-conjugation orbit of size
`[G : I_G(θ)]` (`card_filter_induce_eq_index_inertia`).  When every member induces *irreducibly*
— equivalently, has inertia `I_G(θ) = H` — every fibre has the **same** size `[G : H]`, so the
image `{Ind_H^G θ | θ ∈ T} ⊆ Irr G` has cardinality `|T| / [G : H]`:

`|image (Ind)| · [G : H] = |T|`   (`card_image_induce_mul_index_eq`).

This is the general "orbit count" behind Peterfalvi's induced-family sizes `size (seqIndD …) =
(|source| − 1) / e` — the count that the degree-square identity `sum_div_normSq_induce_image_eq`
(same file, `InducedIrreducible`) leaves implicit.  It is the *cardinality* analogue of that
degree-sum: instead of `∑ χ(1)²`, it counts `|image|`, using the single hypothesis that each
source induces irreducibly (`I_G(θ) = H`).

## Main results

* `card_image_induce_mul_index_eq` — `|T.image (Ind)| · [G:H] = |T|` for a conjugation-invariant
  `T ⊆ Irr H` whose members all have inertia `H`.
* `card_image_induce_eq_div` — the division form `|T.image (Ind)| = |T| / [G:H]`.

## References

* Peterfalvi, *Character Theory for the Odd Order Theorem*, §14 (14.9): the `calT1` family count
  `size calT1 = (v − 1) / p` (Coq `PFsection14.v` `FTtypeP_min_typeII`, lines 836–845, via
  `size_irr_subseq_seqInd`/`card_imset_Ind_irr`).
-/

namespace OddOrder.RepresentationTheory

open ClassFunction

variable {G : Type*} [Group G] {H : Subgroup G} [hH : H.Normal]
variable [Fintype G] [Fintype ↥H] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
/-- **The irreducibly-induced image has cardinality `|T| / [G:H]`** (multiplied-out form).

For a conjugation-invariant Finset `T ⊆ Irr H` (`H ⊴ G`) whose every member `θ` has inertia
`I_G(θ) = H` — i.e. `Ind_H^G θ` is irreducible — the induction map `θ ↦ Ind_H^G θ` is `[G:H]`-to-one
onto its image, so `|image| · [G:H] = |T|`.

`Finset.card_eq_sum_card_image` writes `|T|` as the sum over the image of the fibre cardinalities,
and each fibre `{θ ∈ T | Ind θ = χ}` — being the `G`-conjugation orbit of any preimage `θ₀`
(`card_filter_induce_eq_index_inertia`) — has size `[G : I_G(θ₀)] = [G : H]` by the inertia
hypothesis.  A constant summand over the image then collapses to `|image| · [G:H]`. -/
theorem card_image_induce_mul_index_eq
    (T : Finset (IrreducibleCharacter H))
    (hT : ∀ θ ∈ T, ∀ g : G, IrreducibleCharacter.conjBy (G := G) (H := H) g θ ∈ T)
    (hinertia : ∀ θ ∈ T, IrreducibleCharacter.inertia (G := G) (H := H) θ = H) :
    (T.image (fun θ => induce H θ.toClassFunction)).card * H.index = T.card := by
  classical
  -- `|T| = ∑_{χ ∈ image} |fibre over χ|`, each fibre `= [G:H]`.
  rw [Finset.card_eq_sum_card_image (fun θ => induce H θ.toClassFunction) T]
  rw [Finset.sum_congr rfl (fun χ hχ => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
  -- Fibre cardinality = `[G:H]` via `card_filter_induce_eq_index_inertia` + inertia = `H`.
  obtain ⟨θ₀, hθ₀T, hθ₀eq⟩ := Finset.mem_image.mp hχ
  have hfib : {a ∈ T | induce H a.toClassFunction = χ}
      = T.filter (fun θ => induce H θ.toClassFunction = induce H θ₀.toClassFunction) := by
    apply Finset.filter_congr
    intro θ _
    rw [hθ₀eq]
  rw [hfib, card_filter_induce_eq_index_inertia T hT θ₀ hθ₀T, hinertia θ₀ hθ₀T]

open scoped Classical in
/-- **The irreducibly-induced image has cardinality `|T| / [G:H]`** (division form).  Immediate
from `card_image_induce_mul_index_eq` and `[G:H] > 0`. -/
theorem card_image_induce_eq_div
    (T : Finset (IrreducibleCharacter H))
    (hT : ∀ θ ∈ T, ∀ g : G, IrreducibleCharacter.conjBy (G := G) (H := H) g θ ∈ T)
    (hinertia : ∀ θ ∈ T, IrreducibleCharacter.inertia (G := G) (H := H) θ = H) :
    (T.image (fun θ => induce H θ.toClassFunction)).card = T.card / H.index := by
  have hidx : 0 < H.index := Nat.pos_of_ne_zero fun h0 => by
    have hmc := H.index_mul_card
    rw [h0, zero_mul] at hmc
    exact (Nat.card_pos (α := G)).ne' hmc.symm
  rw [← card_image_induce_mul_index_eq T hT hinertia, Nat.mul_div_cancel _ hidx]

end OddOrder.RepresentationTheory
