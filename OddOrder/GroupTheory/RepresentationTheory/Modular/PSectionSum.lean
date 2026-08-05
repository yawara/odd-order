/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.PSection

/-!
# Summing a class function over a `p`-section

For a class function `f` and a `p`-element `x`,

`|C_G(x)| • ∑_{u ∈ S(x)} f(u) = |G| • ∑_{y ∈ C_G(x)⁰} f(x y)`.

Both sides are the double sum `∑_{(g, y) ∈ G × C_G(x)⁰} f(g (x y) g⁻¹)`: the summand does not
depend on `g` because `f` is a class function, which gives the right-hand side, while grouping by
the value `u = g (x y) g⁻¹` gives the left-hand side because every fibre has exactly `|C_G(x)|`
elements (`card_fiber_eq_card_centralizerOf`).

This is the reindexing Navarro performs silently in the proof of (5.13), where a sum over the
`p`-section is turned into a sum over the `p`-regular classes of `C_G(x)` weighted by
`|G : C_G(x y)|`.  Keeping the whole group `G` in the index set instead of choosing class
representatives avoids the class-size bookkeeping entirely.

## Main results

* `OddOrder.RepresentationTheory.Modular.card_centralizerOf_smul_sum_pSection`
-/

namespace OddOrder.RepresentationTheory.Modular

open OddOrder.GroupTheory

variable {p : ℕ} {G : Type*} [Group G] [Fintype G]

open scoped Classical in
/-- **`|C_G(x)| • ∑_{u ∈ S(x)} f(u) = |G| • ∑_{y ∈ C_G(x)⁰} f(x y)`** for a class function `f`. -/
theorem card_centralizerOf_smul_sum_pSection {M : Type*} [AddCommMonoid M] (hp : p.Prime)
    {x : G} (hx : IsPElement p x) (f : G → M) (hf : ∀ a b : G, IsConj a b → f a = f b) :
    Nat.card ↥(centralizerOf x)
        • (∑ u ∈ Finset.univ.filter (fun u : G => u ∈ pSection p x), f u)
      = Nat.card G
        • (∑ y ∈ Finset.univ.filter (fun y : ↥(centralizerOf x) => IsPRegular p ((y : G))),
            f (x * (y : G))) := by
  classical
  set C : Subgroup G := centralizerOf x with hC
  set R : Finset ↥C := Finset.univ.filter (fun y : ↥C => IsPRegular p ((y : G))) with hR
  set S : Finset G := Finset.univ.filter (fun u : G => u ∈ pSection p x) with hS
  set Ψ : G × ↥C → G := fun q => q.1 * (x * (q.2 : G)) * q.1⁻¹ with hΨ
  set T : Finset (G × ↥C) := Finset.univ ×ˢ R with hT
  -- the double sum, computed with `f` a class function
  have hA : (∑ q ∈ T, f (Ψ q)) = Nat.card G • ∑ y ∈ R, f (x * (y : G)) := by
    have hterm : ∀ q ∈ T, f (Ψ q) = f (x * ((q.2 : ↥C) : G)) := fun q _ =>
      hf _ _ (isConj_iff.mpr ⟨q.1⁻¹, by rw [hΨ]; group⟩)
    calc (∑ q ∈ T, f (Ψ q))
        = ∑ q ∈ T, f (x * ((q.2 : ↥C) : G)) := Finset.sum_congr rfl hterm
      _ = ∑ _g : G, ∑ y ∈ R, f (x * (y : G)) := by rw [hT, Finset.sum_product]
      _ = Nat.card G • ∑ y ∈ R, f (x * (y : G)) := by
            rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  -- the map lands in the section
  have hmaps : ∀ q ∈ T, Ψ q ∈ S := by
    intro q hq
    have hreg : IsPRegular p ((q.2 : ↥C) : G) :=
      (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).2
    have hcomm : Commute x ((q.2 : ↥C) : G) :=
      (Subgroup.mem_centralizer_iff.mp (q.2).2) x rfl
    have hmem : x * ((q.2 : ↥C) : G) ∈ pSection p x := mul_mem_pSection hp hcomm hx hreg
    have hconj : IsConj (x * ((q.2 : ↥C) : G)) (Ψ q) := isConj_iff.mpr ⟨q.1, by rw [hΨ]⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_pSection_iff_isConj_pPart.mpr
      ((isConj_pPart hconj).symm.trans (mem_pSection_iff_isConj_pPart.mp hmem))⟩
  -- every fibre has `|C_G(x)|` elements
  have hfib : ∀ u ∈ S, (T.filter fun q => Ψ q = u).card = Nat.card ↥C := by
    intro u hu
    have hus : u ∈ pSection p x := (Finset.mem_filter.mp hu).2
    rw [← card_fiber_eq_card_centralizerOf hp hx hus, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    refine congrArg Finset.card (Finset.ext fun q => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hT, hR, hΨ, Finset.mem_product]
  calc Nat.card ↥C • (∑ u ∈ S, f u)
      = ∑ u ∈ S, (T.filter fun q => Ψ q = u).card • f u := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun u hu => by rw [hfib u hu]
    _ = ∑ u ∈ S, ∑ q ∈ T.filter fun q => Ψ q = u, f (Ψ q) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_congr rfl (fun q hq => show f (Ψ q) = f u by
          rw [(Finset.mem_filter.mp hq).2]), Finset.sum_const]
    _ = ∑ q ∈ T, f (Ψ q) := Finset.sum_fiberwise_of_maps_to hmaps _
    _ = Nat.card G • ∑ y ∈ R, f (x * (y : G)) := hA

end OddOrder.RepresentationTheory.Modular
