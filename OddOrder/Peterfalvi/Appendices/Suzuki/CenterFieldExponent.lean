/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.QuotientKWField
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The coordinate on `Q₀ = Z(Q)` inside `E`, and the exponent `d`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §3, p. 120.  The standing identification at the top of
that page reads

> `K` can be identified with `F^*` in such a way that the actions of `K` on
> `S/Q₀` and on `Q₀`, identified with `F × F` and with `F` respectively, are given
> by `(a,b)^x = (xa, xb)` and `c^x = x^{1+θ} c`.

Step (1) of the Proposition supplies the `S/Q₀` half
(`Hypothesis.QuotientFieldModel`).  This file supplies the `Q₀` half *inside the
same field*: `Z(Q)` becomes a coordinate in the subfield `F = {x : x^q = x}` of
`E`, and the `K`-action becomes multiplication by a power `μ(k)^d`.

The exponent `d` exists because both identifications present `K` as the cyclic
group `F^×`: `γ` from Appendix I Proposition 2 applied to `Q₀`, and `μ|_K` from
step (1).  An endomorphism of a cyclic group is a power map
(`MonoidHom.map_cyclic`).

`d` is *not* canonical: replacing the `Q₀`-coordinate by `Frobⁱ ∘ ι` replaces `d`
by `2ⁱ d`.  That freedom is exactly what lets the book's `d = 1 + 2^j` — i.e. the
existence of `θ` with `c^x = x^{1+θ} c` — be *normalized into existence* rather
than imported from the type-B data; see issue 0167.

## Main results

* `Hypothesis.isElementaryAbelian_center_of_lemmaFiveSetup` — `Z(Q)` is
  elementary abelian of exponent `2`.
* `Hypothesis.actualKActor_free_on_center` — `K` acts freely on `Z(Q) ∖ {1}`
  (transitivity plus the count `|K| = |Z(Q)| − 1`).
The coordinate `ι` and the exponent `d` themselves are the next step; see
issue 0167 for the remaining ingredient (a subgroup of given order in a cyclic
group is unique, used to see that the two presentations of `K` inside `E^×` have
the same image).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

namespace Hypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## `Z(Q)` as an elementary abelian group with a regular `K`-action -/

/-- `Z(Q)` is elementary abelian of exponent `2`: it is abelian because it is a
centre, and has exponent `2` by `LemmaFiveSetup.centerSq`. -/
theorem isElementaryAbelian_center_of_lemmaFiveSetup {m : ℕ}
    (s : hyp.LemmaFiveSetup m) :
    IsElementaryAbelian 2 ↥(Subgroup.center hyp.Q) := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · exact Subtype.ext (Subgroup.mem_center_iff.mp x.2 (y : ↥hyp.Q)).symm
  · exact Subtype.ext (s.centerSq (x : ↥hyp.Q) x.2)

/-- The `K`-action on the (characteristic) subgroup `Z(Q)`. -/
noncomputable def centerKHom :
    ↥hyp.actualKActor →* MulAut ↥(Subgroup.center hyp.Q) :=
  IsAInvariant.toMulAutHom
    (IsAInvariant.of_characteristic (H := Subgroup.center hyp.Q)
      hyp.actualKActor.subtype)

@[simp] theorem centerKHom_apply_val (k : ↥hyp.actualKActor)
    (z : ↥(Subgroup.center hyp.Q)) :
    ((hyp.centerKHom k z : ↥(Subgroup.center hyp.Q)) : ↥hyp.Q) =
      hyp.actualKActor.subtype k (z : ↥hyp.Q) :=
  IsAInvariant.toMulAutHom_apply_val _ k z

/-- **`K` acts freely on `Z(Q) ∖ {1}`.**

`LemmaFiveSetup` gives transitivity on the nonidentity central elements together
with `|K| = |Z(Q)| − 1`; a surjection between finite sets of equal size is
injective, so each orbit map `k ↦ k·z` is injective and hence the stabilizers are
trivial. -/
theorem actualKActor_free_on_center {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)) (hz : z ≠ 1)
    (hfix : hyp.centerKHom k z = z) : k = 1 := by
  classical
  haveI : Fintype ↥(Subgroup.center hyp.Q) := Fintype.ofFinite _
  haveI : Fintype ↥hyp.actualKActor := Fintype.ofFinite _
  have hzQ : (z : ↥hyp.Q) ≠ 1 := fun h => hz (Subtype.ext h)
  -- the orbit map at `z`, valued in the nonidentity central elements
  have hzne : ∀ a : ↥hyp.actualKActor, hyp.centerKHom a z ≠ 1 := fun a hone =>
    hz ((hyp.centerKHom a).injective (hone.trans (map_one _).symm))
  set f : ↥hyp.actualKActor → {y : ↥(Subgroup.center hyp.Q) // y ≠ 1} :=
    fun a => ⟨hyp.centerKHom a z, hzne a⟩ with hf
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha⟩ := s.transCenter (z : ↥hyp.Q) (y : ↥hyp.Q) z.2 hzQ y.2
      (fun h => hy (Subtype.ext h))
    refine ⟨a, ?_⟩
    rw [hf]
    exact Subtype.ext (Subtype.ext (by rw [hyp.centerKHom_apply_val]; exact ha))
  -- equal cardinalities upgrade surjectivity to injectivity
  have hcardT : Fintype.card {y : ↥(Subgroup.center hyp.Q) // y ≠ 1} =
      Nat.card ↥(Subgroup.center hyp.Q) - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have hcards : Fintype.card ↥hyp.actualKActor =
      Fintype.card {y : ↥(Subgroup.center hyp.Q) // y ≠ 1} := by
    rw [hcardT, ← Nat.card_eq_fintype_card, s.cardActorCenter]
  have hinj : Function.Injective f :=
    ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj, hcards⟩).1
  refine hinj ?_
  rw [hf]
  exact Subtype.ext (by simpa [map_one] using hfix)

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
