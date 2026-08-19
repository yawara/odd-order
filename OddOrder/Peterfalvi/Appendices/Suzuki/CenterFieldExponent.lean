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
* `Hypothesis.exists_center_coordinate_exponent` — the coordinate `ι` and the
  exponent `d`.
* `Hypothesis.exists_quadraticMap_of_lemmaFiveSetup` — the book's `χ : E → F`, as a
  genuine `𝔽₂`-quadratic map on `E`, anisotropic and satisfying
  `χ (a x) = a^d χ (x)` for `a ∈ K₁`.
* `Hypothesis.exists_scalingPair_of_lemmaFiveSetup` — the pair of automorphisms
  `σ, τ` of `E` with `σ(a) τ(a) = a^d` on `K₁`, i.e. the book's
  `{σ|_F, τ|_F} = {1_F, θ}` before normalization.
* `Hypothesis.exists_sigma_inverting_W1` — **step (2) of the Proposition**: an
  automorphism `σ` of `E` with `ω^{1+σ} = 1` for every `ω ∈ W₁`, i.e. `σ` inverts
  `W₁`.
* `Hypothesis.exists_center_coordinate_equiv` — the coordinate `ι` upgraded to an
  additive *isomorphism* onto the subfield `F`, which is the form step (3) needs
  for the kernel map of Appendix III Lemma 1(c).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

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
  have : Fintype ↥(Subgroup.center hyp.Q) := Fintype.ofFinite _
  have : Fintype ↥hyp.actualKActor := Fintype.ofFinite _
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


/-! ## The coordinate and the exponent -/

open scoped Classical in
/-- **The `Q₀`-side coordinate inside `E`, with the exponent `d`** (Peterfalvi
Part II, Ch. III §3, p. 120).

`K` is regular on `Z(Q) ∖ {1}`, so Appendix I Proposition 2 in its regular form
turns `Z(Q)` into a field of order `q` on which `K` acts by multiplication; by
uniqueness of finite fields (`FiniteField.ringEquivOfCardEq`) that field *is* the
subfield `F = {x : x^q = x}` of `E`.  Transporting gives an additive embedding
`ι : Z(Q) → E` with image in `F`, and the `K`-action becomes multiplication by
`μ(k)^d` for a single integer `d`.

The exponent exists because the two presentations `γ` and `μ|_K` of `K` inside
`E^×` have the *same image*: both are injective, so the images are subgroups of
the cyclic group `E^×` of the same order, hence equal
(`cyclic_subgroup_eq_of_card_eq`).  Writing `k = k₀^t` for a generator `k₀` then
propagates a single `d` to all of `K`. -/
theorem exists_center_coordinate_exponent {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m) :
    ∃ (ι : Additive ↥(Subgroup.center hyp.Q) →+ M.E) (d : ℤ),
      Function.Injective ι ∧
      (∀ z, (ι z) ^ 2 ^ m = ι z) ∧
      ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
        ι (Additive.ofMul (hyp.centerKHom k z))
          = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) * ι (Additive.ofMul z) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEA : IsElementaryAbelian 2 ↥(Subgroup.center hyp.Q) :=
    hyp.isElementaryAbelian_center_of_lemmaFiveSetup s
  have hZcard : Nat.card ↥(Subgroup.center hyp.Q) = 2 ^ m := by
    rw [s.centerEqQ0,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv, hQ0card]
  let : CommGroup ↥(Subgroup.center hyp.Q) :=
    { (inferInstance : Group ↥(Subgroup.center hyp.Q)) with mul_comm := hEA.comm }
  have : Nontrivial ↥(Subgroup.center hyp.Q) := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hZcard]
    exact Nat.one_lt_pow hm (by norm_num)
  have := hyp.actualKActor_isCyclic
  let : CommGroup ↥hyp.actualKActor := IsCyclic.commGroup
  -- Appendix I Proposition 2 on `Z(Q)`
  obtain ⟨F, instF, instFin, γ, α, hcardF, hγ⟩ :=
    Huppert.exists_field_coordinate_realization hEA hyp.centerKHom
      (fun k z hz hfix => hyp.actualKActor_free_on_center s k z hz hfix)
      s.cardActorCenter
  let : Field F := instF
  have : Finite F := instFin
  -- `F` is the subfield `{x : x^q = x}` of `E`
  set F₁ : Subfield M.E := OddOrder.FiniteField.frobFixedSubfield M.E 2 m with hF₁
  have hF₁card : Nat.card ↥F₁ = 2 ^ m :=
    OddOrder.FiniteField.natCard_frobFixedSubfield M.card hm
  have : Fintype F := Fintype.ofFinite F
  have : Fintype ↥F₁ := Fintype.ofFinite _
  have hcards : Fintype.card F = Fintype.card ↥F₁ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardF, hZcard, hF₁card]
  let e : F ≃+* ↥F₁ := FiniteField.ringEquivOfCardEq hcards
  -- the coordinate
  let ι : Additive ↥(Subgroup.center hyp.Q) →+ M.E :=
    (F₁.subtype.toAddMonoidHom).comp
      ((e.toAddEquiv.toAddMonoidHom).comp α.toAddMonoidHom)
  have hιapply : ∀ z, ι z = ((e (α z) : ↥F₁) : M.E) := fun _ => rfl
  have hιinj : Function.Injective ι := by
    intro a b hab
    rw [hιapply, hιapply] at hab
    exact α.injective (e.injective (Subtype.ext hab))
  -- the two presentations of `K` inside `E^×`
  let ν : ↥hyp.actualKActor →* M.Eˣ :=
    ((Units.map F₁.subtype.toMonoidHom).comp (Units.map e.toMonoidHom)).comp
      γ.toMonoidHom
  let μ' : ↥hyp.actualKActor →* M.Eˣ := M.mu.comp (MonoidHom.inl _ _)
  have hνval : ∀ k, ((ν k : M.Eˣ) : M.E) = ((e (γ k : F) : ↥F₁) : M.E) :=
    fun _ => rfl
  have hνinj : Function.Injective ν := by
    intro a b hab
    refine γ.injective (Units.ext ?_)
    have := congrArg (fun u : M.Eˣ => (u : M.E)) hab
    rw [hνval, hνval] at this
    exact e.injective (Subtype.ext this)
  have hμ'inj : Function.Injective μ' := M.mu_K_injective
  -- equal ranges, by uniqueness of subgroups of a given order in a cyclic group
  have hrangecard : Nat.card ↥(ν.range) = Nat.card ↥(μ'.range) := by
    have h1 : Nat.card ↥hyp.actualKActor = Nat.card ↥(ν.range) :=
      Nat.card_congr (Equiv.ofInjective ν hνinj)
    have h2 : Nat.card ↥hyp.actualKActor = Nat.card ↥(μ'.range) :=
      Nat.card_congr (Equiv.ofInjective μ' hμ'inj)
    exact h1.symm.trans h2
  have hrange : ν.range = μ'.range :=
    OddOrder.GroupTheory.cyclic_subgroup_eq_of_card_eq hrangecard
  -- a generator of `K` transports a single exponent to all of `K`
  obtain ⟨k₀, hk₀⟩ := IsCyclic.exists_generator (α := ↥hyp.actualKActor)
  have hmem : ν k₀ ∈ μ'.range := hrange ▸ ⟨k₀, rfl⟩
  obtain ⟨k₁, hk₁⟩ := hmem
  obtain ⟨t₁, ht₁'⟩ := hk₀ k₁
  have ht₁ : k₀ ^ t₁ = k₁ := ht₁'
  refine ⟨ι, t₁, hιinj, ?_, ?_⟩
  · -- the coordinate lands in the subfield
    intro z
    have hz : ((e (α z) : ↥F₁) : M.E) ∈ F₁ := (e (α z)).2
    rw [hιapply]
    exact (OddOrder.FiniteField.mem_frobFixedSubfield).mp hz
  · -- equivariance
    intro k z
    have hν : ν k = μ' k ^ t₁ := by
      obtain ⟨t, ht'⟩ := hk₀ k
      have ht : k₀ ^ t = k := ht'
      have h₀ : ν k₀ = μ' k₀ ^ t₁ := by
        rw [← hk₁, ← ht₁, map_zpow]
      calc ν k = ν (k₀ ^ t) := by rw [ht]
        _ = (ν k₀) ^ t := by rw [map_zpow]
        _ = (μ' k₀ ^ t₁) ^ t := by rw [h₀]
        _ = (μ' k₀ ^ t) ^ t₁ := by rw [← zpow_mul, ← zpow_mul, mul_comm]
        _ = μ' k ^ t₁ := by rw [← map_zpow, ht]
    have hcoe : ((M.mu (k, 1) ^ t₁ : M.Eˣ) : M.E) = ((e (γ k : F) : ↥F₁) : M.E) := by
      have : (μ' k ^ t₁ : M.Eˣ) = ν k := hν.symm
      have h2 : (M.mu (k, 1) ^ t₁ : M.Eˣ) = ν k := this
      rw [h2, hνval]
    rw [hcoe, hιapply, hιapply, hγ k z, map_mul]
    simp


/-! ## The quadratic map `χ : E → F` -/

/-- Conjugation by `K` commutes with squaring: the descended square map of
Appendix III Lemma 1(a) is `K`-equivariant. -/
theorem centralSquare_quotientKHom
    (hW : IsElementaryAbelian 2 ↥(Subgroup.center hyp.Q))
    (hV : IsElementaryAbelian 2 (↥hyp.Q ⧸ Subgroup.center hyp.Q))
    (k : ↥hyp.actualKActor) (y : ↥hyp.Q ⧸ Subgroup.center hyp.Q) :
    Suzuki2Groups.centralSquare (le_refl (Subgroup.center ↥hyp.Q)) hW hV
        (hyp.quotientKHom k y)
      = hyp.centerKHom k
          (Suzuki2Groups.centralSquare (le_refl (Subgroup.center ↥hyp.Q)) hW hV y) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [hyp.quotientKHom_apply_mk, Suzuki2Groups.centralSquare_mk,
    Suzuki2Groups.centralSquare_mk]
  refine Subtype.ext ?_
  rw [hyp.centerKHom_apply_val]
  exact (map_pow (hyp.actualKActor.subtype k) x 2).symm

/-- `W` fixes the descended square map: `w` acts trivially on `Q₀ = Z(Q)`, and the
square of any element already lies there. -/
theorem centralSquare_quotientWHom {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (hW : IsElementaryAbelian 2 ↥(Subgroup.center hyp.Q))
    (hV : IsElementaryAbelian 2 (↥hyp.Q ⧸ Subgroup.center hyp.Q))
    (v : ↥hyp.W) (y : ↥hyp.Q ⧸ Subgroup.center hyp.Q) :
    Suzuki2Groups.centralSquare (le_refl (Subgroup.center ↥hyp.Q)) hW hV
        (hyp.quotientWHom v y)
      = Suzuki2Groups.centralSquare (le_refl (Subgroup.center ↥hyp.Q)) hW hV y := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [hyp.quotientWHom_apply_mk, Suzuki2Groups.centralSquare_mk,
    Suzuki2Groups.centralSquare_mk]
  refine Subtype.ext ?_
  have hsq : x ^ 2 ∈ Subgroup.center hyp.Q := s.sqMem x
  calc hyp.conjQByW v x ^ 2 = hyp.conjQByW v (x ^ 2) := (map_pow _ _ _).symm
    _ = x ^ 2 := hyp.conjQByW_fixes_center s.centerEqQ0 v (x ^ 2) hsq

open scoped Classical in
/-- **The quadratic map `χ : E → F` of the central extension `F → S → E`**
(Peterfalvi Part II, Ch. III §3, p. 121, the map expanded by Appendix III
Lemma 2(c) in step (2)).

Squaring descends to `S/Q₀ → Q₀` (Appendix III Lemma 1(a),
`Suzuki2Groups.centralSquareQuadraticMap`); transporting along the coordinate
`M.coord` of step (1) and the coordinate `ι` of
`exists_center_coordinate_exponent` puts it on `E`, valued in the subfield
`F = {x : x^q = x}`.

* it is **anisotropic** — `χ x = 0` forces `x = 0` — because an element of `Q`
  with square `1` is central (`LemmaFiveSetup.invMem`);
* it satisfies the book's scaling `χ (a x) = a^d χ (x)` for `a ∈ K₁ = μ(K)`,
  with `d` the exponent of `exists_center_coordinate_exponent`.  The book writes
  `d = 1 + θ`; that normalization is the next step. -/
theorem exists_quadraticMap_of_lemmaFiveSetup {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m) :
    ∃ (χ : QuadraticMap (ZMod 2) M.E M.E) (d : ℤ),
      (∀ x : M.E, χ x = 0 → x = 0) ∧
      (∀ x : M.E, (χ x) ^ 2 ^ m = χ x) ∧
      (∀ (k : ↥hyp.actualKActor) (x : M.E),
        χ (((M.mu (k, 1) : M.Eˣ) : M.E) * x)
          = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) * χ x) ∧
      ∀ (v : ↥hyp.W) (x : M.E),
        χ (((M.mu (1, v) : M.Eˣ) : M.E) * x) = χ x := by
  classical
  obtain ⟨ι, d, hιinj, hιF, hιequiv⟩ :=
    hyp.exists_center_coordinate_exponent hm hQ0card s M
  have hW : IsElementaryAbelian 2 ↥(Subgroup.center hyp.Q) :=
    hyp.isElementaryAbelian_center_of_lemmaFiveSetup s
  have hV : IsElementaryAbelian 2 (↥hyp.Q ⧸ Subgroup.center hyp.Q) :=
    s.isplit.split.quotientEA
  let : IsMulCommutative (↥hyp.Q ⧸ Subgroup.center hyp.Q) :=
    IsMulCommutative.of_comm hV.comm
  let : IsMulCommutative ↥(Subgroup.center hyp.Q) := IsMulCommutative.of_comm hW.comm
  let : Module (ZMod 2) (Additive (↥hyp.Q ⧸ Subgroup.center hyp.Q)) := hV.zmodModule
  let : Module (ZMod 2) (Additive ↥(Subgroup.center hyp.Q)) := hW.zmodModule
  -- the descended square map (Appendix III Lemma 1(a))
  set χ₀ := Suzuki2Groups.centralSquareQuadraticMap
    (le_refl (Subgroup.center ↥hyp.Q)) hW hV with hχ₀
  have hχ₀apply : ∀ a, χ₀ a =
      Additive.ofMul (Suzuki2Groups.centralSquare
        (le_refl (Subgroup.center ↥hyp.Q)) hW hV a.toMul) := fun _ => rfl
  -- the two coordinates as `ZMod 2`-linear maps
  let f : M.E →ₗ[ZMod 2] Additive (↥hyp.Q ⧸ Subgroup.center hyp.Q) :=
    { toFun := M.coord.symm
      map_add' := M.coord.symm.map_add
      map_smul' := fun a x => ZMod.map_smul M.coord.symm.toAddMonoidHom a x }
  let g : Additive ↥(Subgroup.center hyp.Q) →ₗ[ZMod 2] M.E :=
    { toFun := ι
      map_add' := ι.map_add
      map_smul' := fun a x => ZMod.map_smul ι a x }
  refine ⟨g.compQuadraticMap (χ₀.comp f), d, ?_, ?_, ?_, ?_⟩
  · -- anisotropy
    intro x hx
    have hx' : ι (χ₀ (M.coord.symm x)) = 0 := hx
    have hz : χ₀ (M.coord.symm x) = 0 := by
      have h0 : ι 0 = 0 := ι.map_zero
      exact hιinj (hx'.trans h0.symm)
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (M.coord.symm x).toMul
    have hsq : (y : ↥hyp.Q) ^ 2 = 1 := by
      have := hχ₀apply (M.coord.symm x)
      rw [hz, ← hy] at this
      rw [Suzuki2Groups.centralSquare_mk] at this
      exact congrArg (Subtype.val (p := fun z => z ∈ Subgroup.center ↥hyp.Q))
        (Additive.ofMul.injective this.symm)
    have hyZ : y ∈ Subgroup.center ↥hyp.Q := s.invMem y hsq
    have : (M.coord.symm x).toMul = 1 := by
      rw [← hy]
      exact (QuotientGroup.eq_one_iff y).mpr hyZ
    have hzero : M.coord.symm x = 0 := Additive.toMul.injective this
    have := congrArg M.coord hzero
    rwa [M.coord.apply_symm_apply, map_zero] at this
  · -- the values lie in the subfield `F`
    intro x
    exact hιF _
  · -- the scaling law
    intro k x
    have hact : M.coord.symm (((M.mu (k, 1) : M.Eˣ) : M.E) * x)
        = Additive.ofMul (hyp.quotientKHom k (M.coord.symm x).toMul) := by
      refine M.coord.injective ?_
      rw [M.coord.apply_symm_apply]
      have h := M.coord_act (k, 1) (M.coord.symm x).toMul
      have hkw : hyp.quotientKWHom (k, 1) = hyp.quotientKHom k := by
        rw [hyp.quotientKWHom_apply, map_one, mul_one]
      rw [hkw] at h
      rw [h]
      congr 1
      exact (M.coord.apply_symm_apply x).symm
    change ι (χ₀ (M.coord.symm (((M.mu (k, 1) : M.Eˣ) : M.E) * x)))
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) * ι (χ₀ (M.coord.symm x))
    rw [hact, hχ₀apply, hχ₀apply]
    simp only [toMul_ofMul]
    rw [hyp.centralSquare_quotientKHom hW hV, hιequiv]
  · -- `W` acts trivially on the values, so `χ` is `W`-invariant
    intro v x
    have hact : M.coord.symm (((M.mu (1, v) : M.Eˣ) : M.E) * x)
        = Additive.ofMul (hyp.quotientWHom v (M.coord.symm x).toMul) := by
      refine M.coord.injective ?_
      rw [M.coord.apply_symm_apply]
      have h := M.coord_act (1, v) (M.coord.symm x).toMul
      have hkw : hyp.quotientKWHom (1, v) = hyp.quotientWHom v := by
        rw [hyp.quotientKWHom_apply, map_one, one_mul]
      rw [hkw] at h
      rw [h]
      congr 1
      exact (M.coord.apply_symm_apply x).symm
    change ι (χ₀ (M.coord.symm (((M.mu (1, v) : M.Eˣ) : M.E) * x)))
        = ι (χ₀ (M.coord.symm x))
    rw [hact, hχ₀apply, hχ₀apply]
    simp only [toMul_ofMul]
    rw [hyp.centralSquare_quotientWHom s hW hV]


/-! ## The automorphism pair of the Lemma 2(c) expansion -/

/-- **The scaling pair `(σ, τ)` of `χ`** (Peterfalvi Part II, Ch. III §3, p. 121,
step (2)).

`χ` is nonzero (it is anisotropic and `E` is nontrivial), so the Lemma 2(c)
expansion has a surviving coefficient, and the corresponding automorphism pair
converts *every* scaling relation of `χ` into an identity
`σ(a) τ(a) = b`.  Applied to `χ (a x) = a^d χ (x)` for `a ∈ K₁`, this is the book's

> if `λ_{μν} ≠ 0`, then `a^μ a^ν = a a^θ` for `a ∈ F`, whence
> `{μ|_F, ν|_F} = {1_F, θ}`

before the normalization of `d` into the shape `1 + 2^j`.

The pair does not depend on the relation, which is what will let the *same* pair be
re-used on `χ (ω x) = χ (x)` to produce `ω^{1+σ} = 1`. -/
theorem exists_scalingPair_of_lemmaFiveSetup {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m) :
    ∃ (d : ℤ) (σ τ : M.E ≃ₐ[ZMod 2] M.E),
      (∀ k : ↥hyp.actualKActor,
        σ ((M.mu (k, 1) : M.Eˣ) : M.E) * τ ((M.mu (k, 1) : M.Eˣ) : M.E)
          = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E)) ∧
      ∀ v : ↥hyp.W,
        σ ((M.mu (1, v) : M.Eˣ) : M.E) * τ ((M.mu (1, v) : M.Eˣ) : M.E) = 1 := by
  classical
  obtain ⟨χ, d, haniso, _hF, hscale, hWinv⟩ :=
    hyp.exists_quadraticMap_of_lemmaFiveSetup hm hQ0card s M
  have hχ : χ ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : M.E)
    refine hx (haniso x ?_)
    rw [h]
    rfl
  obtain ⟨σ, τ, hpair⟩ :=
    OddOrder.RepresentationTheory.exists_algAut_pair_scaling_of_ne_zero M.E χ hχ
  refine ⟨d, σ, τ, fun k => hpair _ _ (hscale k), fun v => ?_⟩
  refine hpair _ _ (fun x => ?_)
  rw [hWinv v x, one_mul]


/-! ## Step (2) of the Proposition: the automorphism `σ` -/

/-- **Step (2) of the Ch. III §3 Proposition** (Peterfalvi Part II, p. 121):
there is an automorphism `σ` of `E` — a power of the Frobenius — with

> `x^σ = x^{-1}` for `x ∈ W₁`, equivalently `x^{1+σ} = 1`.

The pair `(σ, τ)` of the Lemma 2(c) expansion satisfies `σ(ω) τ(ω) = 1` for every
`ω ∈ W₁`, because `w` acts trivially on `Q₀` and hence `χ (ω x) = χ (x)`.  Both are
Frobenius powers, so `exists_qFrobenius_normalized_index` rewrites the symmetric
relation `ω^{p^i} ω^{p^{i'}} = 1` in the Proposition's form `ω · ω^{p^j} = 1` —
this is the book's "possibly on replacing `σ` by `σ̄`".

The restriction of `σ` to `F` is the book's `θ`; in this development `θ` is *defined*
that way rather than imported from the type-B data, so no further compatibility is
needed (see issue 0167). -/
theorem exists_sigma_inverting_W1 {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m) :
    ∃ j : ℕ, ∀ v : ↥hyp.W,
      ((M.mu (1, v) : M.Eˣ) : M.E) *
          OddOrder.FiniteField.qFrobenius M.E 2 j ((M.mu (1, v) : M.Eˣ) : M.E) = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_d, σ, τ, _hK, hW⟩ :=
    hyp.exists_scalingPair_of_lemmaFiveSetup hm hQ0card s M
  -- `|E| = 2 ^ (2m)`
  have hcard : Nat.card M.E = 2 ^ (m * 2) := by
    rw [M.card, ← pow_mul]
  have hN : m * 2 ≠ 0 := by positivity
  -- both automorphisms are Frobenius powers
  have hpow : ∀ ρ : M.E ≃ₐ[ZMod 2] M.E, ∃ i : ℕ, ∀ x : M.E, ρ x = x ^ 2 ^ i := by
    intro ρ
    obtain ⟨i, hi⟩ := OddOrder.FiniteField.exists_pow_eq_of_ringAut
      (K := M.E) (p := 2) (n := m * 2) hcard hN
      ((OddOrder.RepresentationTheory.ringAutMulEquivAlgAut M.E 2).symm ρ)
    exact ⟨i, fun x => (hi x)⟩
  obtain ⟨i, hi⟩ := hpow σ
  obtain ⟨i', hi'⟩ := hpow τ
  obtain ⟨j, hj⟩ :=
    OddOrder.FiniteField.exists_qFrobenius_normalized_index
      (E := M.E) (p := 2) (N := m * 2) hcard hN i i'
  refine ⟨j, fun v => ?_⟩
  refine hj _ ?_
  rw [OddOrder.FiniteField.qFrobenius_apply, OddOrder.FiniteField.qFrobenius_apply,
    ← hi, ← hi']
  exact hW v


/-! ## The centre coordinate as an isomorphism onto `F`

Appendix III Lemma 1(c) (`GroupExtension.exists_mulEquiv_of_comp_squareMap_eq`)
takes an additive *isomorphism* between the kernels of the two extensions, so the
embedding `ι` of `exists_center_coordinate_exponent` has to be corestricted to its
image and upgraded.  Both sides have `q` elements, so injectivity suffices. -/

open scoped Classical in
/-- **The centre coordinate as an isomorphism `Z(Q) ≃+ F`.**  Same content as
`exists_center_coordinate_exponent`, with `ι` presented as an additive isomorphism
onto the subfield `F = {x : x^q = x}` of `E` — the form required by the kernel map
of Appendix III Lemma 1(c) in step (3) of the Proposition. -/
theorem exists_center_coordinate_equiv {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m) :
    ∃ (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ),
      ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
        ((ι (Additive.ofMul (hyp.centerKHom k z)) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
            ((ι (Additive.ofMul z) :
              ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι₀, d, hinj, hF, hequiv⟩ :=
    hyp.exists_center_coordinate_exponent hm hQ0card s M
  -- corestrict `ι₀` to the subfield
  set F₁ : Subfield M.E := OddOrder.FiniteField.frobFixedSubfield M.E 2 m with hF₁
  have hmem : ∀ z, ι₀ z ∈ F₁ := fun z =>
    (OddOrder.FiniteField.mem_frobFixedSubfield).mpr (hF z)
  set ι₁ : Additive ↥(Subgroup.center hyp.Q) →+ ↥F₁ :=
    { toFun := fun z => ⟨ι₀ z, hmem z⟩
      map_zero' := Subtype.ext ι₀.map_zero
      map_add' := fun a b => Subtype.ext (ι₀.map_add a b) } with hι₁
  have hι₁inj : Function.Injective ι₁ := fun a b hab =>
    hinj (congrArg (Subtype.val (p := fun x => x ∈ F₁)) hab)
  -- both sides have `q` elements, so `ι₁` is bijective
  have hZcard : Nat.card ↥(Subgroup.center hyp.Q) = 2 ^ m := by
    rw [s.centerEqQ0,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv, hQ0card]
  have hcards : Nat.card (Additive ↥(Subgroup.center hyp.Q)) = Nat.card ↥F₁ := by
    rw [Nat.card_congr (Additive.toMul (α := ↥(Subgroup.center hyp.Q))), hZcard, hF₁]
    exact (OddOrder.FiniteField.natCard_frobFixedSubfield M.card hm).symm
  have : Finite ↥F₁ := Subtype.finite
  have : Finite (Additive ↥(Subgroup.center hyp.Q)) := by
    exact Finite.of_equiv _ (Additive.ofMul (α := ↥(Subgroup.center hyp.Q)))
  have : Fintype (Additive ↥(Subgroup.center hyp.Q)) := Fintype.ofFinite _
  have : Fintype ↥F₁ := Fintype.ofFinite _
  have hbij : Function.Bijective ι₁ := by
    refine (Fintype.bijective_iff_injective_and_card ι₁).mpr ⟨hι₁inj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcards]
  refine ⟨AddEquiv.ofBijective ι₁ hbij, d, fun k z => ?_⟩
  exact hequiv k z

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
