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
omit [Fintype ↥H] in
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
  haveI : Fintype ↥H := Fintype.ofFinite _
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
omit [Fintype ↥H] in
/-- **The irreducibly-induced image has cardinality `|T| / [G:H]`** (division form).  Immediate
from `card_image_induce_mul_index_eq` and `[G:H] > 0`. -/
theorem card_image_induce_eq_div
    (T : Finset (IrreducibleCharacter H))
    (hT : ∀ θ ∈ T, ∀ g : G, IrreducibleCharacter.conjBy (G := G) (H := H) g θ ∈ T)
    (hinertia : ∀ θ ∈ T, IrreducibleCharacter.inertia (G := G) (H := H) θ = H) :
    (T.image (fun θ => induce H θ.toClassFunction)).card = T.card / H.index := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hidx : 0 < H.index := Nat.pos_of_ne_zero fun h0 => by
    have hmc := H.index_mul_card
    rw [h0, zero_mul] at hmc
    exact (Nat.card_pos (α := G)).ne' hmc.symm
  rw [← card_image_induce_mul_index_eq T hT hinertia, Nat.mul_div_cancel _ hidx]

open scoped Classical in
omit [Fintype ↥H] in
/-- **The irreducibly-induced image has cardinality at least `|T| / [G:H]`** (lower-bound form; no
conjugation-invariance of `T` needed).  For *any* Finset `T ⊆ Irr H` (`H ⊴ G`) whose every member
`θ` has inertia `I_G(θ) = H`, each induction fibre `{θ ∈ T | Ind θ = Ind θ₀}` embeds into the
`G`-conjugation orbit of `θ₀` (`induce_eq_induce_iff_conj`), whose size is `[G:I_G(θ₀)] = [G:H]`; so
`|T| ≤ |image|·[G:H]`, giving `|T| / [G:H] ≤ |image|`.

Unlike `card_image_induce_eq_div`, this drops the `hT` conjugation-closure hypothesis: a lower bound
suffices for the Peterfalvi (9.8.d) family count `|𝒵| ≥ |T|/a`, and dropping `hT` lets the family be
merely inertia-pinned (each member induces irreducibly) rather than a full conjugation-closed set —
sidestepping the `def_Itheta` conjugation-descent entirely. -/
theorem card_image_induce_ge_div
    (T : Finset (IrreducibleCharacter H))
    (hinertia : ∀ θ ∈ T, IrreducibleCharacter.inertia (G := G) (H := H) θ = H) :
    T.card / H.index ≤ (T.image (fun θ => induce H θ.toClassFunction)).card := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hidx : 0 < H.index := Nat.pos_of_ne_zero fun h0 => by
    have hmc := H.index_mul_card
    rw [h0, zero_mul] at hmc
    exact (Nat.card_pos (α := G)).ne' hmc.symm
  -- `|T| = ∑_{χ ∈ image} |fibre_χ| ≤ |image|·[G:H]` (each fibre embeds in a `[G:H]`-orbit).
  have hle : T.card
      ≤ (T.image (fun θ => induce H θ.toClassFunction)).card * H.index := by
    rw [Finset.card_eq_sum_card_image (fun θ => induce H θ.toClassFunction) T]
    calc ∑ χ ∈ T.image (fun θ => induce H θ.toClassFunction),
            (T.filter fun θ => induce H θ.toClassFunction = χ).card
        ≤ ∑ _χ ∈ T.image (fun θ => induce H θ.toClassFunction), H.index := by
          refine Finset.sum_le_sum fun χ hχ => ?_
          obtain ⟨θ₀, hθ₀T, hθ₀eq⟩ := Finset.mem_image.mp hχ
          -- the fibre over `χ` embeds into `conjByOrbit θ₀`, of size `[G:I(θ₀)] = [G:H]`.
          have hO : (IrreducibleCharacter.conjByOrbit (G := G) (H := H) θ₀).Finite := by
            unfold IrreducibleCharacter.conjByOrbit; exact Set.finite_range _
          have hFsub : (T.filter fun θ => induce H θ.toClassFunction = χ) ⊆ hO.toFinset := by
            intro θ hθ
            rw [Finset.mem_filter] at hθ
            rw [Set.Finite.mem_toFinset, IrreducibleCharacter.mem_conjByOrbit]
            have h2 : induce H θ.toClassFunction = induce H θ₀.toClassFunction :=
              hθ.2.trans hθ₀eq.symm
            obtain ⟨g, hg⟩ := (induce_eq_induce_iff_conj θ θ₀).mp h2
            exact ⟨g⁻¹, by rw [← hg, ← IrreducibleCharacter.conjBy_mul]; simp⟩
          calc (T.filter fun θ => induce H θ.toClassFunction = χ).card
              ≤ hO.toFinset.card := Finset.card_le_card hFsub
            _ = (IrreducibleCharacter.conjByOrbit (G := G) (H := H) θ₀).ncard :=
                (Set.ncard_eq_toFinset_card _ hO).symm
            _ = Nat.card (IrreducibleCharacter.conjByOrbit (G := G) (H := H) θ₀) :=
                (Nat.card_coe_set_eq _).symm
            _ = (IrreducibleCharacter.inertia (G := G) (H := H) θ₀).index :=
                card_conjByOrbit_eq_index_inertia θ₀
            _ = H.index := by rw [hinertia θ₀ hθ₀T]
      _ = (T.image (fun θ => induce H θ.toClassFunction)).card * H.index := by
          rw [Finset.sum_const, smul_eq_mul]
  -- `|T| ≤ |image|·[G:H]` ⟹ `|T|/[G:H] ≤ |image|`.
  calc T.card / H.index
      ≤ ((T.image (fun θ => induce H θ.toClassFunction)).card * H.index) / H.index :=
        Nat.div_le_div_right hle
    _ = (T.image (fun θ => induce H θ.toClassFunction)).card := Nat.mul_div_cancel _ hidx

end OddOrder.RepresentationTheory
