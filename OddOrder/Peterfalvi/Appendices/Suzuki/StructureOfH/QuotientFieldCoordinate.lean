/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.HilbertNinetyOnQ
import OddOrder.Peterfalvi.Appendices.SemilinearField

/-!
# Coordinates on `S ⧸ Q₀`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §2, p. 119:

> We identify `S/Q₀` with `𝐅_q` and `K` with `𝐅_q^×` in such a way that the
> action of `K` on `S/Q₀` is multiplication, and we write `α` for the
> corresponding map `S → 𝐅_q`.

In case (b) the group `S = Q` has order `q²` with `Z(Q) = Q₀` of order `q`, so
the central quotient has exactly `q` elements while `|K| = q − 1`; the free
action of `K` on it is therefore transitive off the identity, and Appendix I
Proposition 2 (`Huppert.exists_field_coordinate_realization`) turns the quotient
into a field `F` with `|F| = q` on which `K` acts by multiplication.

## Main results

* `Hypothesis.exists_quotient_field_coordinate` — the map `α` of p. 119,
  packaged as a function `β : G → F` that is additive on `Q`, has kernel `Q₀`,
  and satisfies `β (a⁻¹ y a) = γ a * β y` for a group isomorphism
  `γ : K ≃* Fˣ`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory OddOrder.Isaacs.Ch03

namespace Hypothesis

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- **The identification of `S/Q₀` with `𝐅_q` and of `K` with `𝐅_q^×`**
(Peterfalvi Part II, Ch. III §2, p. 119).

`K` acts freely on the central quotient `Q ⧸ Z(Q)` (`hKfree`), which in case (b)
has `|Q| / |Q₀| = |Q₀|` elements, one more than `|K|`; so the action is
transitive off the identity and Appendix I Proposition 2 applies.  The resulting
coordinate `β` is the book's `α`, and `γ` is the identification of `K` with the
multiplicative group of the field.

The last conjunct records that `F` has characteristic `2`, which is what makes
`β y⁻¹ = β y` and makes squaring injective — both used constantly on p. 119. -/
theorem exists_quotient_field_coordinate
    (hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hQEA : IsElementaryAbelian 2 (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q))
    (hKfree : ∀ k ∈ hyp.K, k ≠ 1 → ∀ y ∈ hyp.Q,
      k * y * k⁻¹ * y⁻¹ ∈ hyp.Q0 → y ∈ hyp.Q0)
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2) :
    ∃ (F : Type u) (_ : Field F) (γ : ↥hyp.K ≃* Fˣ) (β : G → F),
      (2 : F) = 0 ∧
      (∀ y ∈ hyp.Q, ∀ z ∈ hyp.Q, β (y * z) = β y + β z) ∧
      (∀ y ∈ hyp.Q, β y = 0 ↔ y ∈ hyp.Q0) ∧
      (∀ (a : ↥hyp.K) (y : G), y ∈ hyp.Q →
        β ((a : G)⁻¹ * y * (a : G)) = (γ a : F) * β y) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := ↥hyp.Q ⧸ Subgroup.center ↥hyp.Q with hMdef
  set π : ↥hyp.Q →* M := QuotientGroup.mk' (Subgroup.center ↥hyp.Q) with hπ
  -- the center of `Q` is `Q₀`
  have hmemZ : ∀ (y : G) (hy : y ∈ hyp.Q),
      (⟨y, hy⟩ : ↥hyp.Q) ∈ Subgroup.center ↥hyp.Q ↔ y ∈ hyp.Q0 := by
    intro y hy
    rw [hZQ0]
    exact Subgroup.mem_subgroupOf
  have hπone : ∀ (y : G) (hy : y ∈ hyp.Q), π ⟨y, hy⟩ = 1 ↔ y ∈ hyp.Q0 := by
    intro y hy
    rw [hπ, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hmemZ y hy
  have hKH : hyp.K ≤ hyp.H := hyp.K_le_D.trans hyp.D_le_H
  have hact : ∀ (a : ↥hyp.K) (y : G) (hy : y ∈ hyp.Q),
      (hyp.conjQuotientBy hKH) a (π ⟨y, hy⟩)
        = π ⟨(a : G) * y * (a : G)⁻¹, hyp.Q_normal_in_H (a : G) (hKH a.2) y hy⟩ := by
    intro a y hy
    rw [conjQuotientBy, IsAInvariant.quotientMulAutHom_apply_mk']
    rfl
  -- `|M| = |Q₀|`
  have hQ0two : 2 ≤ Nat.card ↥hyp.Q0 := hyp.two_le_card_Q0
  have hQ0pos : 0 < Nat.card ↥hyp.Q0 := by omega
  have hZcard : Nat.card ↥(Subgroup.center ↥hyp.Q) = Nat.card ↥hyp.Q0 := by
    rw [hZQ0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv]
  have hMcard : Nat.card M = Nat.card ↥hyp.Q0 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥hyp.Q)
    rw [hZcard, hQcard, sq] at h
    exact (Nat.eq_of_mul_eq_mul_right hQ0pos h.symm)
  haveI : Nontrivial M := Finite.one_lt_card_iff_nontrivial.mp (by rw [hMcard]; omega)
  letI : CommGroup M := { (inferInstance : Group M) with mul_comm := hQEA.comm }
  -- the action of `K` on the central quotient
  haveI := hyp.K_isCyclic
  letI : CommGroup ↥hyp.K := IsCyclic.commGroup
  set ψ : ↥hyp.K →* MulAut M := hyp.conjQuotientBy hKH with hψ
  -- `K` acts freely off the identity
  have hfree : ∀ (k : ↥hyp.K) (u : M), u ≠ 1 → ψ k u = u → k = 1 := by
    intro k u hu hfix
    by_contra hkne
    obtain ⟨⟨y, hyQ⟩, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥hyp.Q) u
    have hk1 : (k : G) ≠ 1 := fun h => hkne (Subtype.ext h)
    rw [hψ, hact k y hyQ, hπ, QuotientGroup.mk'_eq_mk'] at hfix
    obtain ⟨z, hzZ, hz⟩ := hfix
    have hzc : ∀ w : ↥hyp.Q, w * z⁻¹ = z⁻¹ * w := by
      intro w
      have := (Subgroup.mem_center_iff.mp hzZ) w
      exact (inv_mul_eq_iff_eq_mul.mpr (by rw [← mul_assoc, ← this, mul_assoc,
        mul_inv_cancel, mul_one])).symm
    set a : ↥hyp.Q :=
      ⟨(k : G) * y * (k : G)⁻¹, hyp.Q_normal_in_H (k : G) (hKH k.2) y hyQ⟩ with hadef
    have hab : a * (⟨y, hyQ⟩ : ↥hyp.Q)⁻¹ = z⁻¹ := by
      rw [← hz, mul_inv_rev, ← mul_assoc, hzc a, mul_assoc, mul_inv_cancel, mul_one]
    have hmem : (k : G) * y * (k : G)⁻¹ * y⁻¹ ∈ hyp.Q :=
      hyp.Q.mul_mem (hyp.Q_normal_in_H (k : G) (hKH k.2) y hyQ) (hyp.Q.inv_mem hyQ)
    have hval : (⟨(k : G) * y * (k : G)⁻¹ * y⁻¹, hmem⟩ : ↥hyp.Q)
        ∈ Subgroup.center ↥hyp.Q := by
      have hrw : (⟨(k : G) * y * (k : G)⁻¹ * y⁻¹, hmem⟩ : ↥hyp.Q)
          = a * (⟨y, hyQ⟩ : ↥hyp.Q)⁻¹ := rfl
      rw [hrw, hab]
      exact Subgroup.inv_mem _ hzZ
    exact hu ((hπone y hyQ).mpr
      (hKfree (k : G) k.2 hk1 y hyQ ((hmemZ _ hmem).mp hval)))
  have hcard : Nat.card ↥hyp.K = Nat.card M - 1 := by
    rw [hMcard, hyp.card_K_eq_card_Q0_sub_one]
  obtain ⟨F, instF, instFinF, μ, α, hFcard, hμ⟩ :=
    Huppert.exists_field_coordinate_realization hQEA ψ hfree hcard
  letI : Field F := instF
  -- the coordinate map, extended by zero off `Q`
  set β : G → F := fun y => if hy : y ∈ hyp.Q then α (Additive.ofMul (π ⟨y, hy⟩)) else 0
    with hβ
  have hβval : ∀ (y : G) (hy : y ∈ hyp.Q), β y = α (Additive.ofMul (π ⟨y, hy⟩)) := by
    intro y hy
    rw [hβ]
    exact dif_pos hy
  refine ⟨F, instF, μ.trans (MulEquiv.inv Fˣ), β, ?_, ?_, ?_, ?_⟩
  · -- characteristic `2`
    obtain ⟨u, hu⟩ := exists_ne (1 : M)
    have h1 : Additive.ofMul u + Additive.ofMul u = 0 := by
      have := hQEA.pow_eq_one u
      rw [pow_two] at this
      exact Additive.toMul.injective (by simpa using this)
    have h2 : α (Additive.ofMul u) + α (Additive.ofMul u) = 0 := by
      rw [← map_add, h1, map_zero]
    have hne : α (Additive.ofMul u) ≠ 0 := by
      intro h
      refine hu ?_
      have := α.injective (h.trans (map_zero α).symm)
      exact Additive.ofMul.injective this
    have h3 : (2 : F) * α (Additive.ofMul u) = 0 := by
      rw [two_mul]; exact h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hne
  · -- additivity on `Q`
    intro y hy z hz
    rw [hβval y hy, hβval z hz, hβval (y * z) (hyp.Q.mul_mem hy hz)]
    have : (⟨y * z, hyp.Q.mul_mem hy hz⟩ : ↥hyp.Q) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
    rw [this, map_mul, ofMul_mul, map_add]
  · -- the kernel is `Q₀`
    intro y hy
    rw [hβval y hy, ← hπone y hy]
    constructor
    · intro h
      have := α.injective (h.trans (map_zero α).symm)
      exact Additive.ofMul.injective this
    · intro h
      rw [h, ofMul_one, map_zero]
  · -- equivariance
    intro a y hy
    have hyc : (a : G)⁻¹ * y * (a : G) ∈ hyp.Q := by
      have := hyp.Q_normal_in_H (a : G)⁻¹ (hyp.H.inv_mem (hKH a.2)) y hy
      rwa [inv_inv] at this
    rw [hβval _ hyc, hβval y hy]
    have hkey : π ⟨(a : G)⁻¹ * y * (a : G), hyc⟩ = ψ a⁻¹ (π ⟨y, hy⟩) := by
      rw [hψ, hact a⁻¹ y hy]
      congr 1
      exact Subtype.ext (by simp)
    rw [hkey, hμ a⁻¹ (π ⟨y, hy⟩)]
    congr 1
    have : (μ a⁻¹ : Fˣ) = ((μ.trans (MulEquiv.inv Fˣ)) a : Fˣ) := by
      rw [MulEquiv.trans_apply, map_inv]
      rfl
    rw [this]

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
