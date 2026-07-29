/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.QuotientFieldCoordinate
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.OrderFiveOrbits

/-!
# The last non-conjugacy of Peterfalvi Part II, Ch. III §2 (p. 119)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §2, p. 119.  The system of representatives
`s, r, r⁻¹, r r^{-k} (k ∈ K#)` of p. 118 is pairwise non-conjugate under `K`
except for the last family among itself, and *that* is settled by a computation
in the field `𝐅_q` with which `S/Q₀` is identified.

This file supplies the group-theoretic obstruction behind the book's
"`x ≠ 1`" step:

> `f(r r^{-k}) g(r r^{-k}) ∉ Q₀`

(the book argues that otherwise `(t r r^{-k} t)²` would exhibit an involution of
`H` and one of `G − H` whose product is an involution).

## Main results

* `Hypothesis.sq_mem_Q0_of_mem_Q` — `S` has exponent `4` modulo `Q₀`.
* `Hypothesis.tConjRight_mul_tConjLeft_notMem_Q0` — the obstruction above, for
  any `w ∈ Q ∖ Q₀` whose middle factor lies in `K`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory

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
  haveI := hyp.K_isCyclic
  letI : CommGroup ↥hyp.K := IsCyclic.commGroup
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

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
