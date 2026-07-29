/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.CoherenceContradiction

/-!
# Peterfalvi Part II, Ch. III §1, Proposition: the three cases for `S`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III, §1, pp. 116–117.

> **Proposition.** One of the following three cases holds.
> (a) `S = Q₀` and `st` has order `3`.
> (b) `S` is a Suzuki `2`-group of type A, `st` has order `5` and `W = 1`.
> (c) `S` is a Suzuki `2`-group of type B, `st` has order `3` and `W ≠ 1`.

By Theorem C (`CoherenceContradiction.lean`) the group `Q` is a `2`-group, so
`S = Q` (`sylowTwoOfQ_eq_Q`) and the Proposition is a statement about `Q`
itself.

This leaf carries the **case (1)** branch, the book's

> Suppose that `S` is abelian.  Then `C_S(P)` is abelian and so `st` has order
> `3` and `C_S(P) ⊂ Q₀`.  Suppose that `S ≠ Q₀`.  There is then an element
> `x ∈ S` such that `x² = s` (since `K` is transitive on `Q₀^#`); since `S` is
> abelian, `{y ∈ S | y² = s} = xQ₀`.  But `P` centralizes `s` (Chapter I, §1,
> Proposition 5) and so normalizes `xQ₀` which is of cardinality prime to `p`,
> whence `C_S(P) ⊄ Q₀`, which is a contradiction.  Thus `S = Q₀`.

## Main results

* `sylowTwoOfQ_eq_Q` — after Theorem C, the book's `S` is `Q`.
* `exists_sq_eq_distinguishedInvolution` — the book's "there is an element
  `x ∈ S` such that `x² = s` (since `K` is transitive on `Q₀^#`)".
* `Q_eq_Q0_of_commute_of_centralizer_le` — the case-(1) core: an abelian `Q`
  whose `P`-centralizer lies in `Q₀` equals `Q₀`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

universe uG uΩ

namespace Hypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- **`Ω₁(Q) = Q₀`** (Peterfalvi Part II, Ch. I §2, p. 103): an element of `Q`
squaring to `1` lies in `Q₀`.

Immediate from the repository's encoding `Q₀ = {x | x² = 1 ∧ x ∈ H}` together
with `Q ≤ H`; recorded because the book uses it as a step ("`{y ∈ S | y² = s}`
`= xQ₀`"). -/
theorem mem_Q0_of_mem_Q_of_sq_eq_one {x : G} (hxQ : x ∈ hyp.Q) (hx : x ^ 2 = 1) :
    x ∈ hyp.Q0 :=
  ⟨hx, hyp.Q_le_H hxQ⟩

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (1), first step**
(p. 117): "there is then an element `x ∈ S` such that `x² = s` (since `K` is
transitive on `Q₀^#`)".

Stated for `Q`: if `Q` is a `2`-group not equal to `Q₀`, some element of `Q`
squares to the distinguished involution `s`.

The book's parenthesis is the whole argument.  An element `z ∈ Q ∖ Q₀` has
`z² ≠ 1`, so its order is `2^m` with `m ≥ 2` and `z^(2^(m-1))` is an involution
of `H` that is the square of `z^(2^(m-2))`.  Since `K` is transitive on the
involutions of `H` (§1 Proposition 3, `image_conj_KSet_eq_involutions_H`), a
`K`-conjugate of `z^(2^(m-2))` squares to `s`. -/
theorem exists_sq_eq_distinguishedInvolution
    (hQ2 : IsPGroup 2 ↥hyp.Q) (hne : hyp.Q ≠ hyp.Q0) :
    ∃ x ∈ hyp.Q, x ^ 2 = hyp.distinguishedInvolution := by
  classical
  -- an element of `Q` outside `Q₀`
  obtain ⟨z, hzQ, hzQ0⟩ : ∃ z ∈ hyp.Q, z ∉ hyp.Q0 := by
    by_contra h
    push Not at h
    exact hne (le_antisymm h hyp.Q0_le_Q)
  have hz2 : z ^ 2 ≠ 1 := fun h => hzQ0 (hyp.mem_Q0_of_mem_Q_of_sq_eq_one hzQ h)
  -- `z` has `2`-power order
  have hex : ∃ k, z ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hQ2 ⟨z, hzQ⟩
    exact ⟨k, by simpa using congrArg (Subtype.val (p := fun x => x ∈ hyp.Q)) hk⟩
  set m := Nat.find hex with hmdef
  have hmspec : z ^ 2 ^ m = 1 := Nat.find_spec hex
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm1 : m = 0 ∨ m = 1 := by omega
    rcases hm1 with h | h
    · rw [h, pow_zero, pow_one] at hmspec
      exact hz2 (by rw [hmspec, one_pow])
    · rw [h, pow_one] at hmspec
      exact hz2 hmspec
  -- the involution `u = z^(2^(m-1))` and its square root `w = z^(2^(m-2))`
  have hu2 : (z ^ 2 ^ (m - 1)) ^ 2 = 1 := by
    rw [← pow_mul, show 2 ^ (m - 1) * 2 = 2 ^ m by rw [← pow_succ]; congr 1; omega]
    exact hmspec
  have hune : z ^ 2 ^ (m - 1) ≠ 1 := Nat.find_min hex (by omega)
  have hwsq : (z ^ 2 ^ (m - 2)) ^ 2 = z ^ 2 ^ (m - 1) := by
    rw [← pow_mul, show 2 ^ (m - 2) * 2 = 2 ^ (m - 1) by rw [← pow_succ]; congr 1; omega]
  have hwQ : z ^ 2 ^ (m - 2) ∈ hyp.Q := hyp.Q.pow_mem hzQ _
  have huH : z ^ 2 ^ (m - 1) ∈ hyp.H := hyp.Q_le_H (hyp.Q.pow_mem hzQ _)
  -- `K` is transitive on the involutions of `H`
  have himg := hyp.image_conj_KSet_eq_involutions_H
    hyp.distinguishedInvolution_mem_H hyp.distinguishedInvolution_sq
    hyp.distinguishedInvolution_ne_one
  have humem : z ^ 2 ^ (m - 1) ∈ {y : G | y ^ 2 = 1 ∧ y ≠ 1 ∧ y ∈ hyp.H} :=
    ⟨hu2, hune, huH⟩
  rw [← himg] at humem
  obtain ⟨k, hkK, hk⟩ := humem
  -- conjugate `w` back by `k`
  refine ⟨k * z ^ 2 ^ (m - 2) * k⁻¹, hyp.Q_normal_in_H k (hyp.D_le_H hkK.1) _ hwQ, ?_⟩
  have hconj : (k * z ^ 2 ^ (m - 2) * k⁻¹) ^ 2
      = k * (z ^ 2 ^ (m - 2)) ^ 2 * k⁻¹ := by
    rw [sq, sq]; group
  rw [hconj, hwsq, ← hk]
  group

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (1) core** (p. 117):
if `Q` is abelian and `C_Q(P) ≤ Q₀` for some prime-order `P ≤ V`, then
`Q = Q₀`.

The book's argument verbatim.  Assuming `Q ≠ Q₀`, pick `x ∈ Q` with `x² = s`
(`exists_sq_eq_distinguishedInvolution`).  Commutativity turns the fibre
`T = {y ∈ Q | y² = s}` into the coset `xQ₀`, so `|T| = |Q₀|` is a power of `2`
and hence prime to the odd `p`.  Since `P ≤ V = C_D(s)` (Ch. I §1
Proposition 5) centralizes `s` and normalizes `Q`, it acts on `T`, so it has a
fixed point `y ∈ T`.  Then `y ∈ C_Q(P) ≤ Q₀` forces `y² = 1`, contradicting
`y² = s ≠ 1`. -/
theorem Q_eq_Q0_of_commute_of_centralizer_le
    (hQ2 : IsPGroup 2 ↥hyp.Q)
    (hcomm : ∀ a ∈ hyp.Q, ∀ b ∈ hyp.Q, Commute a b)
    {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    (hPV : P ≤ hyp.V)
    (hCle : hyp.Q ⊓ Subgroup.centralizer (P : Set G) ≤ hyp.Q0) :
    hyp.Q = hyp.Q0 := by
  classical
  by_contra hne
  obtain ⟨x, hxQ, hxs⟩ := hyp.exists_sq_eq_distinguishedInvolution hQ2 hne
  set s := hyp.distinguishedInvolution with hsdef
  -- the fibre `T = {y ∈ Q | y² = s}`
  set T : Set G := {y | y ∈ hyp.Q ∧ y ^ 2 = s} with hTdef
  -- `T = xQ₀`, hence `|T| = |Q₀|`
  have hcardT : Nat.card ↥hyp.Q0 = Nat.card ↥T := by
    refine Nat.card_eq_of_bijective
      (fun q : ↥hyp.Q0 => (⟨x * (q : G), ?_, ?_⟩ : ↥T)) ⟨?_, ?_⟩
    · exact hyp.Q.mul_mem hxQ (hyp.Q0_le_Q q.2)
    · have hq2 : ((q : G)) ^ 2 = 1 := hyp.sq_eq_one_of_mem_Q0 q.2
      have hcm : Commute x (q : G) := hcomm _ hxQ _ (hyp.Q0_le_Q q.2)
      calc (x * (q : G)) ^ 2 = x * ((q : G) * x) * (q : G) := by rw [sq]; group
        _ = x * (x * (q : G)) * (q : G) := by rw [← hcm.eq]
        _ = x ^ 2 * (q : G) ^ 2 := by rw [sq, sq]; group
        _ = s := by rw [hxs, hq2, mul_one]
    · intro q₁ q₂ h
      exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
    · rintro ⟨y, hyQ, hys⟩
      have hcm : Commute x⁻¹ y := ((hcomm _ hxQ _ hyQ).inv_left)
      refine ⟨⟨x⁻¹ * y, ?_, hyp.Q_le_H (hyp.Q.mul_mem (hyp.Q.inv_mem hxQ) hyQ)⟩,
        Subtype.ext (by group)⟩
      calc (x⁻¹ * y) ^ 2 = x⁻¹ * (y * x⁻¹) * y := by rw [sq]; group
        _ = x⁻¹ * (x⁻¹ * y) * y := by rw [← hcm.eq]
        _ = (x ^ 2)⁻¹ * y ^ 2 := by rw [sq, sq]; group
        _ = 1 := by rw [hxs, hys, inv_mul_cancel]
  -- `p` is odd, and `|Q₀|` is a power of `2`
  have hpodd : p ≠ 2 := by
    intro hp2
    have hdvd : p ∣ Nat.card ↥hyp.D :=
      hPcard ▸ Subgroup.card_dvd_of_le (hPV.trans hyp.V_le_D)
    obtain ⟨j, hj⟩ := hyp.D_odd
    rw [hp2] at hdvd
    omega
  obtain ⟨n, hn⟩ := (hQ2.to_le hyp.Q0_le_Q).exists_card_eq
  have hnotdvd : ¬ p ∣ Nat.card ↥T := by
    rw [← hcardT, hn]
    intro hdvd
    exact hpodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow hdvd))
  -- `P` acts on `T` by conjugation
  have hTsmul : ∀ (g : ↥P) (y : ↥T), (g : G) * (y : G) * (g : G)⁻¹ ∈ T := by
    intro g y
    have hgH : (g : G) ∈ hyp.H := hyp.D_le_H (hyp.V_le_D (hPV g.2))
    refine ⟨hyp.Q_normal_in_H _ hgH _ y.2.1, ?_⟩
    have hgs : (g : G) * s * (g : G)⁻¹ = s := by
      have hgV : (g : G) ∈ hyp.V := hPV g.2
      rw [hyp.V_eq_centralizer_distinguishedInvolution] at hgV
      have hc := Subgroup.mem_centralizer_iff.mp hgV.2 s rfl
      rw [← hc]; group
    calc ((g : G) * (y : G) * (g : G)⁻¹) ^ 2
        = (g : G) * (y : G) ^ 2 * (g : G)⁻¹ := by rw [sq, sq]; group
      _ = s := by rw [y.2.2]; exact hgs
  letI actP : MulAction ↥P ↥T :=
    { smul := fun g y => ⟨(g : G) * (y : G) * (g : G)⁻¹, hTsmul g y⟩
      one_smul := fun y => Subtype.ext (by
        change ((1 : ↥P) : G) * (y : G) * ((1 : ↥P) : G)⁻¹ = (y : G)
        simp)
      mul_smul := fun g h y => Subtype.ext (by
        change ((g * h : ↥P) : G) * (y : G) * ((g * h : ↥P) : G)⁻¹
            = (g : G) * ((h : G) * (y : G) * (h : G)⁻¹) * (g : G)⁻¹
        push_cast
        group) }
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hPp : IsPGroup p ↥P := IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one])
  obtain ⟨y, hy⟩ := hPp.nonempty_fixed_point_of_prime_not_dvd_card ↥T hnotdvd
  -- the fixed point lies in `C_Q(P) ≤ Q₀`, so it squares to `1`
  have hyC : (y : G) ∈ hyp.Q ⊓ Subgroup.centralizer (P : Set G) := by
    refine ⟨y.2.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro g hg
    show g * (y : G) = (y : G) * g
    have hval : g * (y : G) * g⁻¹ = (y : G) :=
      congrArg (Subtype.val (p := fun z => z ∈ T))
        (MulAction.mem_fixedPoints.mp hy ⟨g, hg⟩)
    calc g * (y : G) = g * (y : G) * g⁻¹ * g := by group
      _ = (y : G) * g := by rw [hval]
  have h1 : (y : G) ^ 2 = 1 := hyp.sq_eq_one_of_mem_Q0 (hCle hyC)
  rw [y.2.2] at h1
  exact hyp.distinguishedInvolution_ne_one h1

end Hypothesis

namespace SecondCaseHypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (sc : SecondCaseHypothesis G Ω)

/-- **After Theorem C, the book's `S` is `Q`**: `Q₁ = 1` (`Q1_eq_bot`) makes the
Sylow `2`-subgroup `S` of `Q` equal to `Q`, so Ch. III §1's Proposition — stated
for `S` — is a statement about `Q`. -/
theorem sylowTwoOfQ_eq_Q (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    sc.toHypothesis.sylowTwoOfQ = sc.toHypothesis.Q := by
  refine Subgroup.eq_of_le_of_card_ge sc.toHypothesis.sylowTwoOfQ_le_Q ?_
  have h := sc.toHypothesis.card_sylowTwoOfQ_mul_card_Q1
  rw [sc.Q1_eq_bot ind, Subgroup.card_bot, mul_one] at h
  exact h.ge

end SecondCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
