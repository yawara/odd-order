/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.TwoKSubgroups
import OddOrder.Peterfalvi.Appendices.SemilinearField

/-!
# `K` as the multiplicative group of a field, with the twist coming from `V`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §2, Propositions 1 and 3 (pp. 102–104).

`K` acts on the elementary abelian group `Q₀` freely off the identity
(Ch. I §2, Proposition 1(a) — in the repository
`Hypothesis.Q_inf_centralizer_eq_bot_of_mem_KSet`) and `|K| = |Q₀| − 1`
(`Hypothesis.card_K_eq_card_Q0_sub_one`), so `K` is transitive on `Q₀ ∖ {1}` and
in particular acts irreducibly.  Appendix I, Proposition 2 then turns `Q₀` into a
line over a finite field `F` with `|F| = |Q₀|`, on which `K` acts by scalars; the
resulting `μ : K →* Fˣ` is injective (freeness) between sets of the same size
`|Q₀| − 1`, hence a bijection.

Conjugation by `x ∈ V` normalizes `K` (`K ⊴ D`) and acts semilinearly on `Q₀`
for some `σ ∈ Aut F` satisfying `μ ∘ α = σ ∘ μ`.  The twist `σ` is non-trivial
precisely because `W = C_V(K) = 1`.

This is the input that `OddOrder.GroupTheory.exists_ne_one_fixed_of_free_orbit_semilinear`
needs in order to run Hilbert 90 on a `K`-orbit — see
`StructureOfH/HilbertNinetyOnQ.lean`.

## Main results

* `Hypothesis.exists_field_realization_K` — the field `F`, the isomorphism
  `μ : K ≃* Fˣ` and the non-trivial twist `σ`.
* `Hypothesis.exists_Q0_field_coordinate` — the same field with the *coordinate*
  `α : Q₀ → F` under which the `K`-action is multiplication.  This is the half
  `Q₀ ≅ F`, `K ≅ F^×` of the standing identification of Ch. III §3, p. 120, and
  unlike `exists_field_realization_K` it does not need `W = 1`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

universe uG uΩ

open OddOrder.GroupTheory OddOrder.Isaacs.Ch03

namespace Hypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- **`K` acts freely on `Q₀ ∖ {1}`** (Peterfalvi Part II, Ch. I §2,
Proposition 1(a), p. 102): `C_Q(k) = 1` for `1 ≠ k ∈ K`, and `Q₀ ≤ Q`. -/
theorem conjQ0_fixed_eq_one {k : ↥hyp.K} (hk : k ≠ 1) {y : ↥hyp.Q0}
    (hfix : hyp.conjQ0 ⟨(k : G), hyp.K_le_D k.2⟩ y = y) : y = 1 := by
  by_contra hy
  have hkKSet : (k : G) ∈ hyp.KSet := by rw [← hyp.coe_K]; exact k.2
  have hk1 : (k : G) ≠ 1 := fun h => hk (Subtype.ext h)
  have hval : (k : G) * (y : G) * (k : G)⁻¹ = (y : G) :=
    congrArg (Subtype.val (p := fun z => z ∈ hyp.Q0)) hfix
  have hmem : (y : G) ∈ hyp.Q ⊓ Subgroup.centralizer ({(k : G)} : Set G) := by
    refine ⟨hyp.Q0_le_Q y.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (y : G) * (k : G) = ((k : G) * (y : G) * (k : G)⁻¹) * (k : G) := by rw [hval]
      _ = (k : G) * (y : G) := by group
  rw [hyp.Q_inf_centralizer_eq_bot_of_mem_KSet hkKSet hk1, Subgroup.mem_bot] at hmem
  exact hy (Subtype.ext hmem)

/-- **The conjugation action of `K` on `Q₀` is irreducible**: it is free off the
identity and `|K| = |Q₀| − 1`, so `K` is transitive on `Q₀ ∖ {1}` and no proper
non-trivial subgroup can be invariant. -/
theorem isAInvariant_eq_bot_or_eq_top_conjQ0
    (ψ : ↥hyp.K →* MulAut ↥hyp.Q0)
    (hψ : ∀ (k : ↥hyp.K) (y : ↥hyp.Q0),
      ((ψ k y : ↥hyp.Q0) : G) = (k : G) * (y : G) * (k : G)⁻¹)
    (B : Subgroup ↥hyp.Q0) (hB : IsAInvariant ψ B) : B = ⊥ ∨ B = ⊤ := by
  classical
  have hfree : ∀ (k : ↥hyp.K) (y : ↥hyp.Q0), y ≠ 1 → ψ k y = y → k = 1 := by
    intro k y hy hfix
    by_contra hk
    refine hy (hyp.conjQ0_fixed_eq_one hk (Subtype.ext ?_))
    rw [hyp.conjQ0_apply_coe, ← hψ k y, hfix]
  by_cases hBbot : B = ⊥
  · exact Or.inl hBbot
  right
  obtain ⟨b, hbB, hb1⟩ : ∃ b : ↥hyp.Q0, b ∈ B ∧ b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hBbot (le_bot_iff.mp fun y hy => Subgroup.mem_bot.mpr (hcon y hy))
  have hbne : ∀ k : ↥hyp.K, ψ k b ≠ 1 := by
    intro k h
    exact hb1 (by simpa using congrArg (ψ k)⁻¹ h)
  set f : Option ↥hyp.K → ↥B := fun o =>
    o.rec (⟨1, B.one_mem⟩) (fun k => ⟨ψ k b, hB.smul_mem k hbB⟩) with hfdef
  have hfinj : Function.Injective f := by
    rintro (_ | k) (_ | l) h
    · rfl
    · exact absurd (congrArg (Subtype.val (p := fun z => z ∈ B)) h).symm (hbne l)
    · exact absurd (congrArg (Subtype.val (p := fun z => z ∈ B)) h) (hbne k)
    · have hval : ψ k b = ψ l b := congrArg (Subtype.val (p := fun z => z ∈ B)) h
      have hfix : ψ (l⁻¹ * k) b = b := by
        rw [map_mul, map_inv]
        change (ψ l)⁻¹ ((ψ k) b) = b
        rw [hval]
        simp
      exact congrArg some (inv_mul_eq_one.mp (hfree _ b hb1 hfix)).symm
  have hcard : Nat.card ↥hyp.K + 1 ≤ Nat.card ↥B := by
    have := Nat.card_le_card_of_injective f hfinj
    rwa [Finite.card_option] at this
  have hKcard : Nat.card ↥hyp.K = Nat.card ↥hyp.Q0 - 1 := hyp.card_K_eq_card_Q0_sub_one
  have hQ0two : 2 ≤ Nat.card ↥hyp.Q0 := hyp.two_le_card_Q0
  have hBle : Nat.card ↥B ≤ Nat.card ↥hyp.Q0 := Subgroup.card_le_card_group B
  exact Subgroup.eq_top_of_card_eq B (by omega)

/-- **The field realization of `K`, with the twist induced by an element of `V`**
(Peterfalvi Part II, Ch. I §2, Propositions 1 and 3, pp. 102–104, in the form
Appendix I, Proposition 2 delivers them).

`K` acts freely on `Q₀ ∖ {1}` and `|K| = |Q₀| − 1`, so the action is transitive
there and in particular irreducible; hence `Q₀` is a line over a field `F` with
`|F| = |Q₀|` on which `K` acts by scalars, and `μ : K → Fˣ` is a bijection since
both sides have `|Q₀| − 1` elements.

Conjugation by `x ∈ V` normalizes `K` and acts `σ`-semilinearly on `Q₀`, the two
being related by `μ ∘ α = σ ∘ μ`.  The twist `σ` is non-trivial exactly because
`W = C_V(K) = 1`: an `x` centralizing `K` would lie in `W`. -/
theorem exists_field_realization_K (hW : hyp.W = ⊥)
    {x : G} (hxV : x ∈ hyp.V) (hxne : x ≠ 1)
    (α : ↥hyp.K ≃* ↥hyp.K)
    (hα : ∀ k : ↥hyp.K, ((α k : ↥hyp.K) : G) = x * (k : G) * x⁻¹) :
    ∃ (F : Type uG) (_ : Field F) (_ : Finite F)
      (μ : ↥hyp.K ≃* Fˣ) (σ : RingAut F), σ ≠ 1 ∧
        Nat.card F = Nat.card ↥hyp.Q0 ∧
        ∀ k : ↥hyp.K, ((μ (α k) : Fˣ) : F) = σ ((μ k : Fˣ) : F) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hyp.K_isCyclic
  letI : CommGroup ↥hyp.K := IsCyclic.commGroup
  have hQ0two : 2 ≤ Nat.card ↥hyp.Q0 := hyp.two_le_card_Q0
  haveI : Nontrivial ↥hyp.Q0 :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr fun hbot => by
      rw [hbot, Subgroup.card_bot] at hQ0two; omega
  letI : CommGroup ↥hyp.Q0 :=
    { (inferInstance : Group ↥hyp.Q0) with mul_comm := hyp.isElementaryAbelian_Q0.comm }
  have hxD : x ∈ hyp.D := hyp.V_le_D hxV
  -- the conjugation action of `K` on `Q₀`
  set ψ : ↥hyp.K →* MulAut ↥hyp.Q0 :=
    hyp.conjQ0.comp (Subgroup.inclusion hyp.K_le_D) with hψdef
  have hψval : ∀ (k : ↥hyp.K) (y : ↥hyp.Q0),
      ((ψ k y : ↥hyp.Q0) : G) = (k : G) * (y : G) * (k : G)⁻¹ := fun _ _ => rfl
  have hfree : ∀ (k : ↥hyp.K) (y : ↥hyp.Q0), y ≠ 1 → ψ k y = y → k = 1 := by
    intro k y hy hfix
    by_contra hk
    refine hy (hyp.conjQ0_fixed_eq_one hk (Subtype.ext ?_))
    rw [hyp.conjQ0_apply_coe, ← hψval k y, hfix]
  have hirr : ∀ B : Subgroup ↥hyp.Q0, IsAInvariant ψ B → B = ⊥ ∨ B = ⊤ :=
    hyp.isAInvariant_eq_bot_or_eq_top_conjQ0 ψ hψval
  -- Appendix I, Proposition 2
  obtain ⟨F, instF, instMod, instFin, -, hcardF, ⟨μ₀, hμ₀⟩, hsemi⟩ :=
    Huppert.exists_field_semilinear_with_scalar hyp.isElementaryAbelian_Q0 ψ hirr
  letI : Field F := instF
  letI : Module F (Additive ↥hyp.Q0) := instMod
  letI : Finite F := instFin
  have hμ₀' : ∀ (k : ↥hyp.K) (y : ↥hyp.Q0), ((μ₀ k : Fˣ) : F) • (Additive.ofMul y)
      = Additive.ofMul (ψ k y) := fun k y => hμ₀ k (Additive.ofMul y)
  -- `μ₀` is injective, hence bijective
  have hμinj : Function.Injective μ₀ := by
    refine (injective_iff_map_eq_one μ₀).mpr fun k hk1 => ?_
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥hyp.Q0)
    refine hfree k y hy ?_
    have h := hμ₀' k y
    rw [hk1, Units.val_one, one_smul] at h
    exact (Additive.ofMul.injective h).symm
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype ↥hyp.K := Fintype.ofFinite _
  have hunits : Nat.card Fˣ = Nat.card ↥hyp.Q0 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcardF]
  have hμbij : Function.Bijective μ₀ := by
    refine (Fintype.bijective_iff_injective_and_card μ₀).mpr ⟨hμinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hunits,
      hyp.card_K_eq_card_Q0_sub_one]
  set μ : ↥hyp.K ≃* Fˣ := MulEquiv.ofBijective μ₀ hμbij with hμdef
  have hμval : ∀ k : ↥hyp.K, (μ k : Fˣ) = μ₀ k := fun _ => rfl
  -- the twist
  set g₀ : MulAut ↥hyp.Q0 := hyp.conjQ0 ⟨x, hxD⟩ with hg₀def
  have hg₀val : ∀ y : ↥hyp.Q0, ((g₀ y : ↥hyp.Q0) : G) = x * (y : G) * x⁻¹ := fun _ => rfl
  have hg₀inv : ∀ y : ↥hyp.Q0, ((g₀⁻¹ y : ↥hyp.Q0) : G) = x⁻¹ * (y : G) * x := fun _ => rfl
  have hcompat : ∀ k : ↥hyp.K, ψ (α k) = g₀ * ψ k * g₀⁻¹ := by
    intro k
    ext y
    have hrhs : ((g₀ * ψ k * g₀⁻¹) y : ↥hyp.Q0) = g₀ (ψ k (g₀⁻¹ y)) := rfl
    rw [hrhs]
    simp only [hψval, hg₀val, hg₀inv, hα k]
    group
  obtain ⟨σ, hσ⟩ := hsemi g₀ α hcompat
  -- `μ ∘ α = σ ∘ μ`
  obtain ⟨y₀, hy₀⟩ := exists_ne (1 : ↥hyp.Q0)
  have he₀ : (Additive.ofMul y₀ : Additive ↥hyp.Q0) ≠ 0 := fun h =>
    hy₀ (by simpa using congrArg Additive.toMul h)
  have hinjsmul : Function.Injective
      (fun a : F => a • (Additive.ofMul y₀ : Additive ↥hyp.Q0)) :=
    smul_left_injective F he₀
  have hμσ : ∀ k : ↥hyp.K, ((μ (α k) : Fˣ) : F) = σ ((μ k : Fˣ) : F) := by
    intro k
    refine hinjsmul ?_
    have hlhs : ((μ (α k) : Fˣ) : F) • (Additive.ofMul y₀ : Additive ↥hyp.Q0)
        = Additive.ofMul (g₀ (ψ k (g₀⁻¹ y₀))) := by
      rw [hμval, hμ₀' (α k) y₀, hcompat k]
      rfl
    have hrhs : (σ ((μ k : Fˣ) : F)) • (Additive.ofMul y₀ : Additive ↥hyp.Q0)
        = Additive.ofMul (g₀ (ψ k (g₀⁻¹ y₀))) := by
      have h1 := hσ ((μ k : Fˣ) : F) (Additive.ofMul (g₀⁻¹ y₀))
      have h2 : (MulEquiv.toAdditive g₀) (Additive.ofMul (g₀⁻¹ y₀))
          = (Additive.ofMul y₀ : Additive ↥hyp.Q0) := by
        change Additive.ofMul (g₀ (g₀⁻¹ y₀)) = Additive.ofMul y₀
        rw [MulAut.apply_inv_self]
      rw [hμval, hμ₀' k (g₀⁻¹ y₀), h2] at h1
      exact h1.symm
    exact hlhs.trans hrhs.symm
  -- non-triviality of the twist: `x` does not centralize `K`, since `W = 1`
  have hσne : σ ≠ 1 := by
    intro h1
    obtain ⟨k₀, hk₀K, hk₀ne⟩ : ∃ k ∈ hyp.K, x * k * x⁻¹ ≠ k := by
      by_contra hcon
      push Not at hcon
      have hxW : x ∈ hyp.W := by
        refine ⟨hxV, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
        have hkK : k ∈ hyp.K := by rw [← SetLike.mem_coe, hyp.coe_K]; exact hk
        have h := hcon k hkK
        calc k * x = (x * k * x⁻¹) * x := by rw [h]
          _ = x * k := by group
      rw [hW, Subgroup.mem_bot] at hxW
      exact hxne hxW
    refine hk₀ne ?_
    have h2 : μ (α ⟨k₀, hk₀K⟩) = μ (⟨k₀, hk₀K⟩ : ↥hyp.K) := by
      refine Units.ext ?_
      rw [hμσ ⟨k₀, hk₀K⟩, h1]
      rfl
    have h3 : α (⟨k₀, hk₀K⟩ : ↥hyp.K) = ⟨k₀, hk₀K⟩ := μ.injective h2
    have h4 := hα (⟨k₀, hk₀K⟩ : ↥hyp.K)
    rw [h3] at h4
    exact h4.symm
  exact ⟨F, instF, instFin, μ, σ, hσne, hcardF, hμσ⟩

/-- **`Q₀ ≅ F` and `K ≅ F^×`, with the coordinate** (Peterfalvi Part II, the
standing identification set up at the top of Ch. III §3, p. 120:

> `K` can be identified with `F^*` in such a way that the actions of `K` on
> `S/Q₀` and on `Q₀`, identified with `F × F` and with `F` respectively, are given
> by `(a,b)^x = (xa, xb)` and `c^x = x^{1+θ} c`.

This supplies the `Q₀` half.)  `K` acts freely on `Q₀ ∖ {1}` and
`|K| = |Q₀| − 1`, so the action is regular and Appendix I Proposition 2 in its
regular form (`Huppert.exists_field_coordinate_realization`) turns `Q₀` into a
field `F` of order `|Q₀|` with `K` acting by multiplication.

Unlike `exists_field_realization_K` this needs no hypothesis on `W`: the twist
`σ` — the only part of that theorem that uses `W = 1` — is not asserted here. -/
theorem exists_Q0_field_coordinate :
    ∃ (F : Type uG) (_ : Field F) (_ : Finite F)
      (γ : ↥hyp.K ≃* Fˣ) (α : Additive ↥hyp.Q0 ≃+ F),
      Nat.card F = Nat.card ↥hyp.Q0 ∧
      ∀ (k : ↥hyp.K) (y : ↥hyp.Q0),
        α (Additive.ofMul
            (hyp.conjQ0 (Subgroup.inclusion hyp.K_le_D k) y))
          = ((γ k : Fˣ) : F) * α (Additive.ofMul y) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hyp.K_isCyclic
  letI : CommGroup ↥hyp.K := IsCyclic.commGroup
  have hQ0two : 2 ≤ Nat.card ↥hyp.Q0 := hyp.two_le_card_Q0
  haveI : Nontrivial ↥hyp.Q0 :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr fun hbot => by
      rw [hbot, Subgroup.card_bot] at hQ0two; omega
  letI : CommGroup ↥hyp.Q0 :=
    { (inferInstance : Group ↥hyp.Q0) with
      mul_comm := hyp.isElementaryAbelian_Q0.comm }
  set ψ : ↥hyp.K →* MulAut ↥hyp.Q0 :=
    hyp.conjQ0.comp (Subgroup.inclusion hyp.K_le_D) with hψdef
  have hψval : ∀ (k : ↥hyp.K) (y : ↥hyp.Q0),
      ((ψ k y : ↥hyp.Q0) : G) = (k : G) * (y : G) * (k : G)⁻¹ := fun _ _ => rfl
  have hfree : ∀ (k : ↥hyp.K) (y : ↥hyp.Q0), y ≠ 1 → ψ k y = y → k = 1 := by
    intro k y hy hfix
    by_contra hk
    refine hy (hyp.conjQ0_fixed_eq_one hk (Subtype.ext ?_))
    rw [hyp.conjQ0_apply_coe, ← hψval k y, hfix]
  have hcard : Nat.card ↥hyp.K = Nat.card ↥hyp.Q0 - 1 :=
    hyp.card_K_eq_card_Q0_sub_one
  obtain ⟨F, instF, instFin, γ, α, hcardF, hγ⟩ :=
    Huppert.exists_field_coordinate_realization hyp.isElementaryAbelian_Q0 ψ
      hfree hcard
  exact ⟨F, instF, instFin, γ, α, hcardF, hγ⟩

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
