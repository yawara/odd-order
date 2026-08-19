/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.QuotientFieldCoordinate
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.OrderFiveSubgroup

/-!
# The last non-conjugacy of Peterfalvi Part II, Ch. III §2 (p. 119)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §2, p. 119.  The system of representatives
`s, r, r⁻¹, r r^{-k} (k ∈ K#)` of p. 118 is pairwise non-conjugate under `K`
except for the last family among itself, and *that* is settled by a computation
in the field `𝐅_q` with which `S/Q₀` is identified.

Identifying `S/Q₀` with `𝐅_q` and `K` with `𝐅_q^×`
(`exists_quotient_field_coordinate`) and writing `α` for the coordinate, a
conjugacy `(r r^{-k₁})^a = r r^{-k₂}` gives the book's relations (5), (6), (7)
between `a`, `k₁`, `k₂` and the elements `ℓ₁`, `ℓ₂` of (4); the substitution
`xᵢ = ℓᵢ⁻¹(kᵢ⁻¹+1)`, `yᵢ = kᵢ⁻¹+ℓᵢ` and the characteristic `2` identity
`(x+1)k⁻¹ = xy + 1` then force `k₁ = k₂`, provided `x ≠ 1`.

The excluded degenerate case `x = 1` amounts to `f g ∈ Q₀`; the book rules it
out by an involution count, and here it is ruled out by the uniqueness of the
canonical form.

With this the Proposition of §2 is complete.

## Main results

* `eq_of_charTwo_pairing` — the field computation of p. 119.
* `Hypothesis.tConjRight_mul_tConjLeft_notMem_Q0` — `f g ∉ Q₀`, which is the
  book's `x ≠ 1`.
* `Hypothesis.coord_tConjTriple_values` — the coordinates of `g`, `h`, `f`.
* `Hypothesis.structureConjugator_mul_conj_inv_pairwise` — the last
  non-conjugacy.
* `Hypothesis.tConjMiddle_mem_K_of_case_b` and `Hypothesis.caseBSubgroup` —
  **the Proposition of Ch. III §2**: in case (b), `(SK) ∪ (SKtS)` is a subgroup.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory

section CharTwoAlgebra

/-- **The field computation of Peterfalvi Part II, Ch. III §2, p. 119.**

In the identification of `S/Q₀` with `𝐅_q` and of `K` with `𝐅_q^×`, a
`K`-conjugacy `(r r^{-k₁})^a = r r^{-k₂}` produces the three relations

* (5) `1 + k₂ = a (1 + k₁)`   (from `α`),
* (6) `ℓ₂ k₂ = a ℓ₁ k₁`       (from `h`, after taking square roots),
* (7) `ℓ₂⁻¹ k₂⁻² + k₂⁻¹ = a⁻¹ (ℓ₁⁻¹ k₁⁻² + k₁⁻¹)`  (from `f`),

and the book puts `xᵢ = ℓᵢ⁻¹(kᵢ⁻¹ + 1)`, `yᵢ = kᵢ⁻¹ + ℓᵢ`.  Dividing (5) by (6)
gives `x₁ = x₂`, multiplying (6) by (7) gives `y₁ = y₂`, and the characteristic
`2` identity `(x + 1)k⁻¹ = xy + 1` then reads `(x+1)k₁⁻¹ = (x+1)k₂⁻¹`.  So
`k₁ = k₂` as soon as `x ≠ 1`. -/
theorem eq_of_charTwo_pairing {F : Type*} [Field F] (h2 : (2 : F) = 0)
    {A k₁ k₂ l₁ l₂ : F} (hA : A ≠ 0) (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0)
    (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (h5 : 1 + k₂ = A * (1 + k₁))
    (h6 : l₂ * k₂ = A * (l₁ * k₁))
    (h7 : l₂⁻¹ * (k₂⁻¹) ^ 2 + k₂⁻¹ = A⁻¹ * (l₁⁻¹ * (k₁⁻¹) ^ 2 + k₁⁻¹))
    (hx : l₁⁻¹ * (k₁⁻¹ + 1) ≠ 1) :
    k₁ = k₂ := by
  have hone : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  -- `xᵢ` and `yᵢ` in closed form
  have ex : ∀ k l : F, k ≠ 0 → l ≠ 0 → l⁻¹ * (k⁻¹ + 1) = (1 + k) * (l * k)⁻¹ := by
    intro k l hk hl; field_simp
  have ey : ∀ k l : F, k ≠ 0 → l ≠ 0 →
      k⁻¹ + l = (l * k) * (l⁻¹ * (k⁻¹) ^ 2 + k⁻¹) := by
    intro k l hk hl; field_simp
  -- (5)/(6): the `x` are equal
  have hxx : l₂⁻¹ * (k₂⁻¹ + 1) = l₁⁻¹ * (k₁⁻¹ + 1) :=
    calc l₂⁻¹ * (k₂⁻¹ + 1) = (1 + k₂) * (l₂ * k₂)⁻¹ := ex k₂ l₂ hk₂ hl₂
      _ = (A * (1 + k₁)) * (A * (l₁ * k₁))⁻¹ := by rw [h5, h6]
      _ = (1 + k₁) * (l₁ * k₁)⁻¹ := by
            rw [mul_inv, ← mul_assoc, mul_comm (A * (1 + k₁)) A⁻¹, ← mul_assoc,
              inv_mul_cancel₀ hA, one_mul]
      _ = l₁⁻¹ * (k₁⁻¹ + 1) := (ex k₁ l₁ hk₁ hl₁).symm
  -- (6)·(7): the `y` are equal
  have hyy : k₂⁻¹ + l₂ = k₁⁻¹ + l₁ :=
    calc k₂⁻¹ + l₂ = (l₂ * k₂) * (l₂⁻¹ * (k₂⁻¹) ^ 2 + k₂⁻¹) := ey k₂ l₂ hk₂ hl₂
      _ = (A * (l₁ * k₁)) * (A⁻¹ * (l₁⁻¹ * (k₁⁻¹) ^ 2 + k₁⁻¹)) := by rw [h6, h7]
      _ = (l₁ * k₁) * (l₁⁻¹ * (k₁⁻¹) ^ 2 + k₁⁻¹) := by
            rw [mul_comm A (l₁ * k₁), mul_assoc, ← mul_assoc A A⁻¹,
              mul_inv_cancel₀ hA, one_mul]
      _ = k₁⁻¹ + l₁ := (ey k₁ l₁ hk₁ hl₁).symm
  -- the characteristic-`2` identity `(x + 1)k⁻¹ = x y + 1`
  have hid : ∀ k l : F, k ≠ 0 → l ≠ 0 →
      (l⁻¹ * (k⁻¹ + 1) + 1) * k⁻¹ = (l⁻¹ * (k⁻¹ + 1)) * (k⁻¹ + l) + 1 := by
    intro k l hk hl
    field_simp
    linear_combination (-(l * k ^ 2)) * h2
  have hkey : (l₁⁻¹ * (k₁⁻¹ + 1) + 1) * k₁⁻¹ = (l₁⁻¹ * (k₁⁻¹ + 1) + 1) * k₂⁻¹ := by
    rw [hid k₁ l₁ hk₁ hl₁, ← hxx, hid k₂ l₂ hk₂ hl₂, hyy]
  have hxne : l₁⁻¹ * (k₁⁻¹ + 1) + 1 ≠ 0 := by
    intro hcon
    exact hx (add_right_cancel (b := (1 : F)) (hcon.trans hone.symm))
  exact inv_injective (mul_left_cancel₀ hxne hkey)

/-- Squaring is injective in characteristic `2`. -/
theorem eq_of_sq_eq_sq_of_charTwo {F : Type*} [Field F] (h2 : (2 : F) = 0)
    {u v : F} (h : u ^ 2 = v ^ 2) : u = v := by
  have hz : (u - v) ^ 2 = 0 := by linear_combination h + (v ^ 2 - u * v) * h2
  exact sub_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp hz)

/-- **The degenerate case `x = 1` of p. 119**: it forces `α(f g) = 0`, i.e.
`f g ∈ Q₀`, which `tConjRight_mul_tConjLeft_notMem_Q0` excludes. -/
theorem charTwo_pairing_degenerate {F : Type*} [Field F] (h2 : (2 : F) = 0)
    {k l : F} (hx : l⁻¹ * (k⁻¹ + 1) = 1) :
    (l⁻¹ * (k⁻¹) ^ 2 + k⁻¹) + (1 + l⁻¹) = 0 := by
  linear_combination (k⁻¹ + 1) * hx + (k⁻¹ + 1 - k⁻¹ * l⁻¹) * h2

end CharTwoAlgebra

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- Squares of elements of `Q` lie in `Q₀`: the central quotient `Q ⧸ Z(Q)` is
elementary abelian of exponent `2` and `Z(Q) = Q₀`. -/
theorem sq_mem_Q0_of_mem_Q
    (hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hQEA : IsElementaryAbelian 2 (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q))
    {y : G} (hy : y ∈ hyp.Q) : y ^ 2 ∈ hyp.Q0 := by
  set π : ↥hyp.Q →* (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q) :=
    QuotientGroup.mk' (Subgroup.center ↥hyp.Q) with hπ
  have hker : π (⟨y, hy⟩ ^ 2) = 1 := by
    rw [map_pow]
    exact hQEA.pow_eq_one _
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZQ0] at hker
  exact Subgroup.mem_subgroupOf.mp hker

/-- Two elements of `K` commute (`K` is cyclic). -/
theorem mul_comm_of_mem_K {x y : G} (hx : x ∈ hyp.K) (hy : y ∈ hyp.K) :
    x * y = y * x := by
  have := hyp.K_isCyclic
  let : CommGroup ↥hyp.K := IsCyclic.commGroup
  exact congrArg (Subtype.val (p := fun z => z ∈ hyp.K))
    (mul_comm (⟨x, hx⟩ : ↥hyp.K) ⟨y, hy⟩)

/-- An element of `K` squaring to `1` is trivial (`|K|` is odd). -/
theorem eq_one_of_sq_eq_one_of_mem_K {x : G} (hx : x ∈ hyp.K) (hx2 : x ^ 2 = 1) :
    x = 1 := by
  have hdvd : orderOf (⟨x, hx⟩ : ↥hyp.K) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hx2))
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact congrArg (Subtype.val (p := fun z => z ∈ hyp.K)) (orderOf_eq_one_iff.mp h1)
  · exfalso
    have h2dvd : 2 ∣ Nat.card ↥hyp.K := h2 ▸ orderOf_dvd_natCard _
    obtain ⟨m, hm⟩ := hyp.card_K_odd
    omega

/-- **The obstruction behind the book's `x ≠ 1`** (Peterfalvi Part II,
Ch. III §2, p. 119).

Let `w ∈ Q ∖ Q₀` with `h(w) ∈ K`, and write `t w t = g h t f`.  Then
`f g ∉ Q₀`.

Indeed `w² ∈ Q₀ ∖ {1}` (the central quotient has exponent `2`, and `w ∉ Q₀`
means `w² ≠ 1`), and since `t` inverts `K` one computes
`t w² t = (t w t)² = g · t (fg)^h t · f`.  If `fg` lay in `Q₀`, then `z = (fg)^h`
would too, and comparing the canonical decompositions of `t w² t` would force
`h(w²) = h(z)`.  All involutions of `H` are `K`-conjugate, say `z = (w²)^c`, so
`h(z) = c h(w²) c` with `h(w²) ∈ K`; as `K` is abelian of odd order this gives
`c = 1`, i.e. `z = w²` — and then the left factors give `g = 1`, contradicting
`g ≠ 1`. -/
theorem tConjRight_mul_tConjLeft_notMem_Q0
    (hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hQEA : IsElementaryAbelian 2 (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q))
    {w : G} (hw : w ∈ hyp.Q) (hw0 : w ∉ hyp.Q0)
    (hhK : hyp.tConjMiddle w ∈ hyp.K) :
    hyp.tConjRight w * hyp.tConjLeft w ∉ hyp.Q0 := by
  intro hu
  have hw1 : w ≠ 1 := fun hcon => hw0 (hcon ▸ hyp.Q0.one_mem)
  obtain ⟨⟨hgQ, hg1⟩, hdD, ⟨hfQ, hf1⟩, heq⟩ := hyp.tConjTriple_spec hw hw1
  set g : G := hyp.tConjLeft w with hgdef
  set h : G := hyp.tConjMiddle w with hhdef
  set f : G := hyp.tConjRight w with hfdef
  -- `w² ∈ Q₀ ∖ {1}`
  have hw2Q : w ^ 2 ∈ hyp.Q := hyp.Q.pow_mem hw 2
  have hw2Q0 : w ^ 2 ∈ hyp.Q0 := hyp.sq_mem_Q0_of_mem_Q hZQ0 hQEA hw
  have hw2ne : w ^ 2 ≠ 1 := fun hcon => hw0 ⟨hcon, hyp.Q_le_H hw⟩
  -- `t` inverts the middle factor
  have hhKSet : h ∈ hyp.KSet := by rw [← hyp.coe_K]; exact hhK
  have hth : hyp.t * h * hyp.t = h⁻¹ := hyp.t_conj_eq_inv_of_mem_KSet hhKSet
  have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  have hht : h * hyp.t = hyp.t * h⁻¹ := by
    calc h * hyp.t = hyp.t * hyp.t * h * hyp.t := by rw [htt, one_mul]
      _ = hyp.t * (hyp.t * h * hyp.t) := by group
      _ = hyp.t * h⁻¹ := by rw [hth]
  have hhit : h⁻¹ * hyp.t = hyp.t * h := by
    have hinv : hyp.t * h⁻¹ * hyp.t = h := by
      have h1 : (hyp.t * h * hyp.t) * (hyp.t * h⁻¹ * hyp.t) = hyp.t * hyp.t := by
        calc (hyp.t * h * hyp.t) * (hyp.t * h⁻¹ * hyp.t)
            = hyp.t * h * (hyp.t * hyp.t) * h⁻¹ * hyp.t := by group
          _ = hyp.t * h * h⁻¹ * hyp.t := by rw [htt]; group
          _ = hyp.t * hyp.t := by group
      rw [hth, htt] at h1
      exact (inv_mul_eq_one.mp h1).symm
    calc h⁻¹ * hyp.t = hyp.t * hyp.t * h⁻¹ * hyp.t := by rw [htt, one_mul]
      _ = hyp.t * (hyp.t * h⁻¹ * hyp.t) := by group
      _ = hyp.t * h := by rw [hinv]
  -- `t w² t = g · (t z t) · f` with `z = (f g)^h`
  set z : G := h⁻¹ * (f * g) * h with hzdef
  have hzQ0 : z ∈ hyp.Q0 := hyp.conj_mem_Q0_of_mem_KSet hhKSet hu
  have hsq : hyp.t * w ^ 2 * hyp.t = (hyp.t * w * hyp.t) * (hyp.t * w * hyp.t) := by
    rw [sq]
    calc hyp.t * (w * w) * hyp.t = hyp.t * w * (hyp.t * hyp.t) * w * hyp.t := by
          rw [htt]; group
      _ = _ := by group
  have hexp : (g * h * hyp.t * f) * (g * h * hyp.t * f)
      = g * (hyp.t * z * hyp.t) * f := by
    rw [hzdef]
    calc g * h * hyp.t * f * (g * h * hyp.t * f)
        = g * (h * hyp.t) * (f * g) * (h * hyp.t) * f := by group
      _ = g * (hyp.t * h⁻¹) * (f * g) * (hyp.t * h⁻¹) * f := by rw [hht]
      _ = g * hyp.t * (h⁻¹ * (f * g) * h) * (h⁻¹ * hyp.t) * h⁻¹ * f := by group
      _ = g * hyp.t * (h⁻¹ * (f * g) * h) * (hyp.t * h) * h⁻¹ * f := by rw [hhit]
      _ = g * (hyp.t * (h⁻¹ * (f * g) * h) * hyp.t) * f := by group
  have hzeq : hyp.t * w ^ 2 * hyp.t = g * (hyp.t * z * hyp.t) * f := by
    rw [hsq, heq, hexp]
  -- `z ≠ 1`, else `t w² t ∈ H`
  have hz1 : z ≠ 1 := by
    intro hcon
    refine hyp.t_conj_notMem_H_of_mem_Q hw2Q hw2ne ?_
    rw [hzeq, hcon, mul_one, htt, mul_one]
    exact hyp.Q_le_H (hyp.Q.mul_mem hgQ hfQ)
  have hzQ : z ∈ hyp.Q := hyp.Q0_le_Q hzQ0
  obtain ⟨⟨hgzQ, -⟩, hdzD, ⟨hfzQ, -⟩, heqz⟩ := hyp.tConjTriple_spec hzQ hz1
  -- comparing canonical decompositions of `t w² t`
  have hfull : hyp.t * w ^ 2 * hyp.t
      = (g * hyp.tConjLeft z) * hyp.tConjMiddle z * hyp.t * (hyp.tConjRight z * f) := by
    rw [hzeq, heqz]; group
  obtain ⟨hgw, hhw, -⟩ := hyp.tConjTriple_eq_of hw2Q hw2ne
    (hyp.Q.mul_mem hgQ hgzQ) hdzD (hyp.Q.mul_mem hfzQ hfQ) hfull
  -- all involutions of `H` are `K`-conjugate, so `z = (w²)^c`
  have hinvol : ∀ x : G, x ∈ hyp.Q0 → x ≠ 1 →
      x ∈ {y : G | y ^ 2 = 1 ∧ y ≠ 1 ∧ y ∈ hyp.H} := fun x hx hx1 => ⟨hx.1, hx1, hx.2⟩
  obtain ⟨c, hcK, hc⟩ : ∃ c ∈ hyp.KSet, c⁻¹ * w ^ 2 * c = z := by
    have himg := hyp.image_conj_KSet_eq_involutions_H (hyp.Q_le_H hw2Q) hw2Q0.1 hw2ne
    have hmem : z ∈ (fun k : G => k⁻¹ * w ^ 2 * k) '' hyp.KSet := by
      rw [himg]; exact hinvol z hzQ0 hz1
    obtain ⟨c, hc, hceq⟩ := hmem
    exact ⟨c, hc, hceq⟩
  -- `h(w²) ∈ K` because `w²` is `K`-conjugate to `s`
  obtain ⟨b, hbK, hb⟩ : ∃ b ∈ hyp.KSet,
      b⁻¹ * hyp.distinguishedInvolution * b = w ^ 2 := by
    have himg := hyp.image_conj_KSet_eq_involutions_H
      hyp.distinguishedInvolution_mem_H hyp.distinguishedInvolution_sq
      hyp.distinguishedInvolution_ne_one
    have hmem : w ^ 2 ∈ (fun k : G => k⁻¹ * hyp.distinguishedInvolution * k) ''
        hyp.KSet := by
      rw [himg]; exact hinvol _ hw2Q0 hw2ne
    obtain ⟨b, hb, hbeq⟩ := hmem
    exact ⟨b, hb, hbeq⟩
  have hhwK : hyp.tConjMiddle (w ^ 2) ∈ hyp.K := by
    rw [← hb]
    exact hyp.tConjMiddle_conj_mem_K hyp.distinguishedInvolution_mem_Q
      hyp.distinguishedInvolution_ne_one (by rw [← SetLike.mem_coe, hyp.coe_K]; exact hbK)
      hyp.tConjMiddle_distinguishedInvolution_mem_K
  -- `h(z) = c h(w²) c`, and `h(w²) = h(z)`, so `c² = 1`
  have hconj := (hyp.tConjTriple_conj hw2Q hw2ne hcK).2.1
  rw [hc] at hconj
  have hcK' : c ∈ hyp.K := by rw [← SetLike.mem_coe, hyp.coe_K]; exact hcK
  have hc2 : c ^ 2 = 1 := by
    have hstep : c * c * hyp.tConjMiddle (w ^ 2) = 1 * hyp.tConjMiddle (w ^ 2) := by
      rw [one_mul]
      calc c * c * hyp.tConjMiddle (w ^ 2) = c * (c * hyp.tConjMiddle (w ^ 2)) := by
            group
        _ = c * (hyp.tConjMiddle (w ^ 2) * c) := by
              rw [hyp.mul_comm_of_mem_K hcK' hhwK]
        _ = c * hyp.tConjMiddle (w ^ 2) * c := by group
        _ = hyp.tConjMiddle z := hconj.symm
        _ = hyp.tConjMiddle (w ^ 2) := hhw.symm
    rw [sq]
    exact mul_right_cancel hstep
  have hcone : c = 1 := hyp.eq_one_of_sq_eq_one_of_mem_K hcK' hc2
  -- so `z = w²`, and the left factors give `g = 1`
  rw [hcone, inv_one, one_mul, mul_one] at hc
  rw [← hc] at hgw
  exact hg1 (mul_right_cancel (b := hyp.tConjLeft (w ^ 2))
    (by rw [one_mul]; exact hgw)).symm

/-! ## The coordinate `α` of p. 119 applied to the canonical triple -/

section Coordinate

variable {F : Type*} [Field F]

/-- A map additive on `Q` kills `1`. -/
theorem coord_one {β : G → F}
    (hadd : ∀ y ∈ hyp.Q, ∀ z ∈ hyp.Q, β (y * z) = β y + β z) : β 1 = 0 := by
  have h := hadd 1 hyp.Q.one_mem 1 hyp.Q.one_mem
  rw [mul_one] at h
  exact (add_right_cancel (a := (0 : F)) (b := β 1) (by rw [zero_add]; exact h)).symm

/-- In characteristic `2` the coordinate does not see inversion. -/
theorem coord_inv (h2 : (2 : F) = 0) {β : G → F}
    (hadd : ∀ y ∈ hyp.Q, ∀ z ∈ hyp.Q, β (y * z) = β y + β z)
    {y : G} (hy : y ∈ hyp.Q) : β y⁻¹ = β y := by
  have h := hadd y hy y⁻¹ (hyp.Q.inv_mem hy)
  rw [mul_inv_cancel, hyp.coord_one hadd] at h
  have h3 : β y + β y = 0 := by rw [← two_mul, h2, zero_mul]
  exact add_left_cancel (h.symm.trans h3.symm)

/-- The equivariance of the coordinate, with the conjugating element spelled as
an element of `G`. -/
theorem coord_conj_inv {γ : ↥hyp.K ≃* Fˣ} {β : G → F}
    (hequiv : ∀ (b : ↥hyp.K) (y : G), y ∈ hyp.Q →
      β ((b : G)⁻¹ * y * (b : G)) = (γ b : F) * β y)
    {a : G} (ha : a ∈ hyp.K) {y : G} (hy : y ∈ hyp.Q) :
    β (a⁻¹ * y * a) = (γ ⟨a, ha⟩ : F) * β y := hequiv ⟨a, ha⟩ y hy

/-- The equivariance of the coordinate, in the opposite direction. -/
theorem coord_conj {γ : ↥hyp.K ≃* Fˣ} {β : G → F}
    (hequiv : ∀ (b : ↥hyp.K) (y : G), y ∈ hyp.Q →
      β ((b : G)⁻¹ * y * (b : G)) = (γ b : F) * β y)
    {a : G} (ha : a ∈ hyp.K) {y : G} (hy : y ∈ hyp.Q) :
    β (a * y * a⁻¹) = ((γ ⟨a, ha⟩ : F))⁻¹ * β y := by
  have h := hequiv ⟨a, ha⟩⁻¹ y hy
  have hcoe : ((⟨a, ha⟩⁻¹ : ↥hyp.K) : G) = a⁻¹ := rfl
  rw [hcoe, inv_inv, map_inv] at h
  rw [h]
  simp

/-- **The coordinates of the canonical triple of `t (r r^{-k}) t`** (Peterfalvi
Part II, Ch. III §2, p. 119 — the inputs to its relations (5), (6), (7)).

With `α` the coordinate and `μ` the identification of `K` with `𝐅_q^×`, and
`ℓ` the element of (4):

* `α(r r^{-k}) = α(r)(1 + k)`,
* `α(g) = α(r)(1 + ℓ⁻¹)` because `g = r r^{-ℓ⁻¹}`,
* `α(f) = α(r)(ℓ⁻¹k⁻² + k⁻¹)` because `f = r^{ℓ⁻¹k⁻²} r^{-k⁻¹}`,
* `h = ℓ²k²`.

(Characteristic `2` is what makes `α(r⁻¹) = α(r)`.) -/
theorem coord_tConjTriple_values (h2 : (2 : F) = 0) {γ : ↥hyp.K ≃* Fˣ} {β : G → F}
    (hadd : ∀ y ∈ hyp.Q, ∀ z ∈ hyp.Q, β (y * z) = β y + β z)
    (hequiv : ∀ (b : ↥hyp.K) (y : G), y ∈ hyp.Q →
      β ((b : G)⁻¹ * y * (b : G)) = (γ b : F) * β y)
    {k : G} (hk : k ∈ hyp.K) (hk1 : k ≠ 1) :
    ∃ (l : G) (hl : l ∈ hyp.K), l ≠ 1 ∧
      hyp.tConjMiddle (hyp.structureConjugator *
          (k⁻¹ * hyp.structureConjugator⁻¹ * k)) = l ^ 2 * k ^ 2 ∧
      β (hyp.structureConjugator * (k⁻¹ * hyp.structureConjugator⁻¹ * k))
        = β hyp.structureConjugator * (1 + (γ ⟨k, hk⟩ : F)) ∧
      β (hyp.tConjLeft (hyp.structureConjugator *
          (k⁻¹ * hyp.structureConjugator⁻¹ * k)))
        = β hyp.structureConjugator * (1 + ((γ ⟨l, hl⟩ : F))⁻¹) ∧
      β (hyp.tConjRight (hyp.structureConjugator *
          (k⁻¹ * hyp.structureConjugator⁻¹ * k)))
        = β hyp.structureConjugator *
            (((γ ⟨l, hl⟩ : F))⁻¹ * ((γ ⟨k, hk⟩ : F))⁻¹ ^ 2
              + ((γ ⟨k, hk⟩ : F))⁻¹) := by
  have hkKSet : k ∈ hyp.KSet := by rw [← hyp.coe_K]; exact hk
  obtain ⟨l, hlKSet, hl1, hg, hh, hf⟩ := hyp.exists_tConjTriple_eq hkKSet hk1
  have hlK : l ∈ hyp.K := by rw [← SetLike.mem_coe, hyp.coe_K]; exact hlKSet
  have hrQ : hyp.structureConjugator ∈ hyp.Q := hyp.structureConjugator_mem_Q
  have hrQi : hyp.structureConjugator⁻¹ ∈ hyp.Q := hyp.Q.inv_mem hrQ
  have hkH : k ∈ hyp.H := hyp.D_le_H (hyp.K_le_D hk)
  have hlH : l ∈ hyp.H := hyp.D_le_H (hyp.K_le_D hlK)
  have hk2K : k ^ 2 ∈ hyp.K := hyp.K.pow_mem hk 2
  have hk2H : k ^ 2 ∈ hyp.H := hyp.H.pow_mem hkH 2
  have hcQ : k⁻¹ * hyp.structureConjugator⁻¹ * k ∈ hyp.Q := by
    have := hyp.Q_normal_in_H k⁻¹ (hyp.H.inv_mem hkH) _ hrQi
    rwa [inv_inv] at this
  have hlrQ : l * hyp.structureConjugator⁻¹ * l⁻¹ ∈ hyp.Q :=
    hyp.Q_normal_in_H l hlH _ hrQi
  have hlrQ' : l * hyp.structureConjugator * l⁻¹ ∈ hyp.Q :=
    hyp.Q_normal_in_H l hlH _ hrQ
  have hkrQ : k * hyp.structureConjugator⁻¹ * k⁻¹ ∈ hyp.Q :=
    hyp.Q_normal_in_H k hkH _ hrQi
  have hbigQ : k ^ 2 * (l * hyp.structureConjugator * l⁻¹) * (k ^ 2)⁻¹ ∈ hyp.Q :=
    hyp.Q_normal_in_H (k ^ 2) hk2H _ hlrQ'
  have hγk2 : (γ ⟨k ^ 2, hk2K⟩ : F) = ((γ ⟨k, hk⟩ : F)) ^ 2 := by
    have hsub : (⟨k ^ 2, hk2K⟩ : ↥hyp.K) = ⟨k, hk⟩ ^ 2 := by
      refine Subtype.ext ?_
      simp [pow_two]
    rw [hsub, map_pow]
    push_cast
    ring
  refine ⟨l, hlK, hl1, hh, ?_, ?_, ?_⟩
  · rw [hadd _ hrQ _ hcQ, hyp.coord_conj_inv hequiv hk hrQi,
      hyp.coord_inv h2 hadd hrQ]
    ring
  · rw [hg, hadd _ hrQ _ hlrQ, hyp.coord_conj hequiv hlK hrQi,
      hyp.coord_inv h2 hadd hrQ]
    ring
  · rw [hf, hadd _ hbigQ _ hkrQ, hyp.coord_conj hequiv hk2K hlrQ',
      hyp.coord_conj hequiv hlK hrQ, hyp.coord_conj hequiv hk hrQi,
      hyp.coord_inv h2 hadd hrQ, hγk2]
    ring

end Coordinate

/-! ## The last non-conjugacy -/

/-- **`r r^{-k₁}` and `r r^{-k₂}` are `K`-conjugate only if `k₁ = k₂`**
(Peterfalvi Part II, Ch. III §2, p. 119).

Identify `S/Q₀` with `𝐅_q` and `K` with `𝐅_q^×` (`exists_quotient_field_coordinate`)
and write `α` for the coordinate.  Applying `α` to `(r r^{-k₁})^a = r r^{-k₂}`,
to `f`, and applying the identification to `h`, the equivariance (1) of p. 118
and the values (4) give the book's

* (5) `1 + k₂ = a (1 + k₁)`,
* (6) `ℓ₂ k₂ = a ℓ₁ k₁` (from `h(x^a) = a h(x) a` and `ℓ²k²`, taking square
  roots — legitimate in characteristic `2`),
* (7) `ℓ₂⁻¹k₂⁻² + k₂⁻¹ = a⁻¹(ℓ₁⁻¹k₁⁻² + k₁⁻¹)`.

The field algebra `eq_of_charTwo_pairing` then yields `k₁ = k₂` provided
`x = ℓ₁⁻¹(k₁⁻¹+1) ≠ 1`, and `x = 1` would make `α(f g) = 0`, i.e. `f g ∈ Q₀`,
which `tConjRight_mul_tConjLeft_notMem_Q0` forbids. -/
theorem structureConjugator_mul_conj_inv_pairwise
    (hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hQEA : IsElementaryAbelian 2 (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q))
    (hKfree : ∀ k ∈ hyp.K, k ≠ 1 → ∀ y ∈ hyp.Q,
      k * y * k⁻¹ * y⁻¹ ∈ hyp.Q0 → y ∈ hyp.Q0)
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2)
    (hr2 : hyp.structureConjugator ^ 2 ≠ 1)
    {k₁ k₂ a : G} (hk₁ : k₁ ∈ hyp.KSet) (hk₁1 : k₁ ≠ 1)
    (hk₂ : k₂ ∈ hyp.KSet) (hk₂1 : k₂ ≠ 1) (ha : a ∈ hyp.KSet)
    (hconj : a⁻¹ * (hyp.structureConjugator *
          (k₁⁻¹ * hyp.structureConjugator⁻¹ * k₁)) * a
        = hyp.structureConjugator * (k₂⁻¹ * hyp.structureConjugator⁻¹ * k₂)) :
    k₁ = k₂ := by
  obtain ⟨F, instF, γ, β, h2, hadd, hker, hequiv⟩ :=
    hyp.exists_quotient_field_coordinate hZQ0 hQEA hKfree hQcard
  let : Field F := instF
  have hk₁K : k₁ ∈ hyp.K := by rw [← SetLike.mem_coe, hyp.coe_K]; exact hk₁
  have hk₂K : k₂ ∈ hyp.K := by rw [← SetLike.mem_coe, hyp.coe_K]; exact hk₂
  have haK : a ∈ hyp.K := by rw [← SetLike.mem_coe, hyp.coe_K]; exact ha
  have hrQ : hyp.structureConjugator ∈ hyp.Q := hyp.structureConjugator_mem_Q
  have hρne : β hyp.structureConjugator ≠ 0 := fun hc =>
    hyp.structureConjugator_notMem_Q0 hr2 ((hker _ hrQ).mp hc)
  have hw₁Q := hyp.structureConjugator_mul_conj_inv_mem hk₁
  have hw₁1 := hyp.structureConjugator_mul_conj_inv_ne_one hk₁ hk₁1
  have hw₁0 := hyp.structureConjugator_mul_conj_inv_notMem_Q0 hr2 hk₁ hk₁1
  obtain ⟨l₁, hl₁K, -, hh₁, hbw₁, hbg₁, hbf₁⟩ :=
    hyp.coord_tConjTriple_values h2 hadd hequiv hk₁K hk₁1
  obtain ⟨l₂, hl₂K, -, hh₂, hbw₂, -, hbf₂⟩ :=
    hyp.coord_tConjTriple_values h2 hadd hequiv hk₂K hk₂1
  -- (5): the coordinate of `r r^{-k}`
  have h5 : 1 + (γ ⟨k₂, hk₂K⟩ : F)
      = (γ ⟨a, haK⟩ : F) * (1 + (γ ⟨k₁, hk₁K⟩ : F)) := by
    have hrel := hyp.coord_conj_inv hequiv haK hw₁Q
    rw [hconj, hbw₁, hbw₂] at hrel
    exact mul_left_cancel₀ hρne (by linear_combination hrel)
  -- (6): the middle factor, after taking square roots
  have h6 : (γ ⟨l₂, hl₂K⟩ : F) * (γ ⟨k₂, hk₂K⟩ : F)
      = (γ ⟨a, haK⟩ : F) * ((γ ⟨l₁, hl₁K⟩ : F) * (γ ⟨k₁, hk₁K⟩ : F)) := by
    have hmid := (hyp.tConjTriple_conj hw₁Q hw₁1 ha).2.1
    rw [hconj, hh₁, hh₂] at hmid
    have hmidK : (⟨l₂, hl₂K⟩ : ↥hyp.K) ^ 2 * ⟨k₂, hk₂K⟩ ^ 2
        = ⟨a, haK⟩ * (⟨l₁, hl₁K⟩ ^ 2 * ⟨k₁, hk₁K⟩ ^ 2) * ⟨a, haK⟩ := by
      refine Subtype.ext ?_
      push_cast
      exact hmid
    refine eq_of_sq_eq_sq_of_charTwo h2 ?_
    have hval := congrArg (fun u : Fˣ => (u : F)) (congrArg γ hmidK)
    simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val] at hval
    linear_combination hval
  -- (7): the right factor
  have h7 : ((γ ⟨l₂, hl₂K⟩ : F))⁻¹ * (((γ ⟨k₂, hk₂K⟩ : F))⁻¹) ^ 2
        + ((γ ⟨k₂, hk₂K⟩ : F))⁻¹
      = ((γ ⟨a, haK⟩ : F))⁻¹ * (((γ ⟨l₁, hl₁K⟩ : F))⁻¹
          * (((γ ⟨k₁, hk₁K⟩ : F))⁻¹) ^ 2 + ((γ ⟨k₁, hk₁K⟩ : F))⁻¹) := by
    have hrig := (hyp.tConjTriple_conj hw₁Q hw₁1 ha).2.2
    rw [hconj] at hrig
    rw [hrig, hyp.coord_conj hequiv haK (hyp.tConjRight_mem hw₁Q hw₁1),
      hbf₁] at hbf₂
    exact mul_left_cancel₀ hρne (by linear_combination -hbf₂)
  -- `x ≠ 1`: otherwise `f g ∈ Q₀`
  have hfQ := hyp.tConjRight_mem hw₁Q hw₁1
  have hgQ := hyp.tConjLeft_mem hw₁Q hw₁1
  have hx : ((γ ⟨l₁, hl₁K⟩ : F))⁻¹ * (((γ ⟨k₁, hk₁K⟩ : F))⁻¹ + 1) ≠ 1 := by
    intro hcon
    refine hyp.tConjRight_mul_tConjLeft_notMem_Q0 hZQ0 hQEA hw₁Q hw₁0
      (hyp.tConjMiddle_structureConjugator_mul_conj_inv_mem_K hk₁K hk₁1)
      ((hker _ (hyp.Q.mul_mem hfQ hgQ)).mp ?_)
    rw [hadd _ hfQ _ hgQ, hbf₁, hbg₁]
    linear_combination β hyp.structureConjugator * charTwo_pairing_degenerate h2 hcon
  -- the field computation
  have hfin := eq_of_charTwo_pairing h2 (Units.ne_zero (γ ⟨a, haK⟩))
    (Units.ne_zero (γ ⟨k₁, hk₁K⟩)) (Units.ne_zero (γ ⟨k₂, hk₂K⟩))
    (Units.ne_zero (γ ⟨l₁, hl₁K⟩)) (Units.ne_zero (γ ⟨l₂, hl₂K⟩)) h5 h6 h7 hx
  exact congrArg (Subtype.val (p := fun z => z ∈ hyp.K))
    (γ.injective (Units.ext hfin))

/-! ## The Proposition of Ch. III §2 -/

/-- **`h(x) ∈ K` for every `x ∈ S ∖ {1}`** (Peterfalvi Part II, Ch. III §2,
pp. 118-119), with no residual hypothesis beyond case (b).

This *is* the content of the Proposition: `t x t = g(x) h(x) t f(x)` with
`h(x) ∈ K` says `t S t ⊆ S K t S`. -/
theorem tConjMiddle_mem_K_of_case_b
    (hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hQEA : IsElementaryAbelian 2 (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q))
    (hKfree : ∀ k ∈ hyp.K, k ≠ 1 → ∀ y ∈ hyp.Q,
      k * y * k⁻¹ * y⁻¹ ∈ hyp.Q0 → y ∈ hyp.Q0)
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2)
    (h5 : orderOf (hyp.distinguishedInvolution * hyp.t) = 5)
    {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) : hyp.tConjMiddle x ∈ hyp.K :=
  hyp.tConjMiddle_mem_K_of_orderOf_st_eq_five h5 hQcard
    (fun _ _ _ hk₁ hk₁1 hk₂ hk₂1 ha hcj =>
      hyp.structureConjugator_mul_conj_inv_pairwise hZQ0 hQEA hKfree hQcard
        (hyp.structureConjugator_sq_ne_one h5) hk₁ hk₁1 hk₂ hk₂1 ha hcj)
    hx hx1

/-- **The Proposition of Peterfalvi Part II, Ch. III §2** (pp. 118-119):

> If case (b) of the proposition of §1 holds, then `(SK) ∪ (SKtS)` is a subgroup
> of `G`.

Case (b) supplies `orderOf (st) = 5` and `|S| = |Q₀|²`; the remaining inputs
(`Z(S) = Q₀`, `S/Q₀` elementary abelian, `K` free on `S/Q₀`) are the standing
structure of the type A Suzuki `2`-group `S`. -/
def caseBSubgroup
    (hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hQEA : IsElementaryAbelian 2 (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q))
    (hKfree : ∀ k ∈ hyp.K, k ≠ 1 → ∀ y ∈ hyp.Q,
      k * y * k⁻¹ * y⁻¹ ∈ hyp.Q0 → y ∈ hyp.Q0)
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2)
    (h5 : orderOf (hyp.distinguishedInvolution * hyp.t) = 5) : Subgroup G :=
  hyp.orderFiveSubgroup fun _ hx hx1 =>
    hyp.tConjMiddle_mem_K_of_case_b hZQ0 hQEA hKfree hQcard h5 hx hx1

@[simp] lemma coe_caseBSubgroup
    (hZQ0 : Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hQEA : IsElementaryAbelian 2 (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q))
    (hKfree : ∀ k ∈ hyp.K, k ≠ 1 → ∀ y ∈ hyp.Q,
      k * y * k⁻¹ * y⁻¹ ∈ hyp.Q0 → y ∈ hyp.Q0)
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2)
    (h5 : orderOf (hyp.distinguishedInvolution * hyp.t) = 5) :
    ((hyp.caseBSubgroup hZQ0 hQEA hKfree hQcard h5 : Subgroup G) : Set G)
      = hyp.orderFiveCarrier := rfl

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
