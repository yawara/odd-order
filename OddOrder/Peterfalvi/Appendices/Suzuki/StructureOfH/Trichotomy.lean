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
* `centralizer_le_Q0_and_orderOf_st_of_commute` — the branch selection: an
  abelian `Q` forces the `PSL(2, ℓ)` alternative of Ch. I §3 Proposition 1(c),
  giving `orderOf (st) = 3` and `C_Q(P) ≤ Q₀`.
* `Q_eq_Q0_and_orderOf_st_of_commute` — **case (1)**: if `Q` is abelian then
  `Q = Q₀` and `st` has order `3`.
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

/-- The set of square roots of the distinguished involution `s` inside `Q` —
the book's `{y ∈ S | y² = s}` (p. 117), which appears in cases (1), (2) and (3)
of the Ch. III §1 Proposition. -/
def sqFibre : Set G := {y | y ∈ hyp.Q ∧ y ^ 2 = hyp.distinguishedInvolution}

lemma mem_sqFibre_iff {y : G} :
    y ∈ hyp.sqFibre ↔ y ∈ hyp.Q ∧ y ^ 2 = hyp.distinguishedInvolution := Iff.rfl

/-- **The fibre is a union of `Q₀`-cosets**: `Q₀ ≤ Z(Q)` (Ch. I §2 Prop 1(c)), so
multiplying a square root of `s` by an element of `Q₀` gives another one.  No
commutativity of `Q` is needed — this is the inclusion `xQ₀ ⊆ {y | y² = s}` the
book uses in all three cases. -/
theorem mul_mem_sqFibre {y c : G} (hy : y ∈ hyp.sqFibre) (hc : c ∈ hyp.Q0) :
    y * c ∈ hyp.sqFibre := by
  have hcm : c * y = y * c :=
    (Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hc) y hy.1).symm
  refine ⟨hyp.Q.mul_mem hy.1 (hyp.Q0_le_Q hc), ?_⟩
  calc (y * c) ^ 2 = y * (c * y) * c := by rw [sq]; group
    _ = y * (y * c) * c := by rw [hcm]
    _ = y ^ 2 * c ^ 2 := by rw [sq, sq]; group
    _ = hyp.distinguishedInvolution := by
        rw [hy.2, hyp.sq_eq_one_of_mem_Q0 hc, mul_one]

/-- **A prime-order subgroup of `V` has odd order**: `V ≤ D` and `|D|` is odd. -/
theorem prime_ne_two_of_le_V {P : Subgroup G} {p : ℕ} (hPcard : Nat.card ↥P = p)
    (hPV : P ≤ hyp.V) : p ≠ 2 := by
  intro hp2
  have hdvd : p ∣ Nat.card ↥hyp.D :=
    hPcard ▸ Subgroup.card_dvd_of_le (hPV.trans hyp.V_le_D)
  obtain ⟨j, hj⟩ := hyp.D_odd
  rw [hp2] at hdvd
  omega

/-- **`p` does not divide `|Q₀|`**: `Q₀` is a `2`-group and `p` is odd. -/
theorem not_dvd_card_Q0 (hQ2 : IsPGroup 2 ↥hyp.Q) {P : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hPcard : Nat.card ↥P = p) (hPV : P ≤ hyp.V) :
    ¬ p ∣ Nat.card ↥hyp.Q0 := by
  obtain ⟨n, hn⟩ := (hQ2.to_le hyp.Q0_le_Q).exists_card_eq
  rw [hn]
  intro hdvd
  exact hyp.prime_ne_two_of_le_V hPcard hPV
    ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

/-- **Peterfalvi Part II, Ch. III §1, Proposition, the fixed-point step**
(p. 117): "`P` … normalizes `xQ₀` which is of cardinality prime to `p`".

`P ≤ V = C_D(s)` (Ch. I §1 Proposition 5) centralizes `s` and normalizes `Q`, so
it acts by conjugation on the fibre `{y ∈ Q | y² = s}`.  If `p` does not divide
the size of that fibre, the action has a fixed point — an element of `C_Q(P)`
squaring to `s`.

The book invokes this twice: in case (1) it contradicts `C_S(P) ⊆ Q₀`, and in
case (2) it shows `C_S(P)` has exponent `4`. -/
theorem exists_mem_centralizer_mem_sqFibre
    {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    (hPV : P ≤ hyp.V) (hnotdvd : ¬ p ∣ Nat.card ↥hyp.sqFibre) :
    ∃ y ∈ hyp.sqFibre, y ∈ Subgroup.centralizer (P : Set G) := by
  classical
  set T : Set G := hyp.sqFibre with hTdef
  have hTsmul : ∀ (g : ↥P) (y : ↥T), (g : G) * (y : G) * (g : G)⁻¹ ∈ T := by
    intro g y
    have hgH : (g : G) ∈ hyp.H := hyp.D_le_H (hyp.V_le_D (hPV g.2))
    refine ⟨hyp.Q_normal_in_H _ hgH _ y.2.1, ?_⟩
    have hgs : (g : G) * hyp.distinguishedInvolution * (g : G)⁻¹
        = hyp.distinguishedInvolution := by
      have hgV : (g : G) ∈ hyp.V := hPV g.2
      rw [hyp.V_eq_centralizer_distinguishedInvolution] at hgV
      have hc := Subgroup.mem_centralizer_iff.mp hgV.2
        hyp.distinguishedInvolution rfl
      rw [← hc]; group
    calc ((g : G) * (y : G) * (g : G)⁻¹) ^ 2
        = (g : G) * (y : G) ^ 2 * (g : G)⁻¹ := by rw [sq, sq]; group
      _ = hyp.distinguishedInvolution := by rw [y.2.2]; exact hgs
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
  refine ⟨(y : G), y.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro g hg
  show g * (y : G) = (y : G) * g
  have hval : g * (y : G) * g⁻¹ = (y : G) :=
    congrArg (Subtype.val (p := fun z => z ∈ T))
      (MulAction.mem_fixedPoints.mp hy ⟨g, hg⟩)
  calc g * (y : G) = g * (y : G) * g⁻¹ * g := by group
    _ = (y : G) * g := by rw [hval]

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (1), the coset count**
(p. 117): "since `S` is abelian, `{y ∈ S | y² = s} = xQ₀`".

For abelian `Q` the fibre is exactly one coset, because `y² = x²` forces
`(x⁻¹y)² = 1`, i.e. `x⁻¹y ∈ Q₀`. -/
theorem card_sqFibre_eq_card_Q0_of_commute
    (hcomm : ∀ a ∈ hyp.Q, ∀ b ∈ hyp.Q, Commute a b)
    {x : G} (hx : x ∈ hyp.sqFibre) :
    Nat.card ↥hyp.Q0 = Nat.card ↥hyp.sqFibre := by
  classical
  refine Nat.card_eq_of_bijective
    (fun c : ↥hyp.Q0 => (⟨x * (c : G), hyp.mul_mem_sqFibre hx c.2⟩ :
      ↥hyp.sqFibre)) ⟨?_, ?_⟩
  · intro c₁ c₂ h
    exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
  · rintro ⟨y, hyQ, hys⟩
    have hcm : Commute x⁻¹ y := (hcomm _ hx.1 _ hyQ).inv_left
    refine ⟨⟨x⁻¹ * y, ?_, hyp.Q_le_H (hyp.Q.mul_mem (hyp.Q.inv_mem hx.1) hyQ)⟩,
      Subtype.ext (by group)⟩
    calc (x⁻¹ * y) ^ 2 = x⁻¹ * (y * x⁻¹) * y := by rw [sq]; group
      _ = x⁻¹ * (x⁻¹ * y) * y := by rw [← hcm.eq]
      _ = (x ^ 2)⁻¹ * y ^ 2 := by rw [sq, sq]; group
      _ = 1 := by rw [hx.2, hys, inv_mul_cancel]

/-- **`s ∈ Q₀`**, so `Q₀ ≠ 1` and `|Q₀| ≥ 2`. -/
theorem two_le_card_Q0 : 2 ≤ Nat.card ↥hyp.Q0 := by
  have hs : hyp.distinguishedInvolution ∈ hyp.Q0 :=
    ⟨hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_mem_H⟩
  have hpos : 0 < Nat.card ↥hyp.Q0 := Nat.card_pos
  rcases Nat.lt_or_ge (Nat.card ↥hyp.Q0) 2 with hlt | hge
  · exfalso
    have h1 : Nat.card ↥hyp.Q0 = 1 := by omega
    rw [Subgroup.eq_bot_of_card_eq _ h1, Subgroup.mem_bot] at hs
    exact hyp.distinguishedInvolution_ne_one hs
  · exact hge

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (2), the coset count**
(p. 117): "Let `x ∈ S` be such that `x² = s`.  Since
`|{y ∈ S | y² = s}| = (q² − q)/(q − 1) = q`, we again find that
`{y ∈ S | y² = s} = xQ₀`."

A Suzuki `2`-group has exponent dividing `4` (Higman Theorem 1(a),
`pow_four_eq_one_of_isSuzuki2Group`), so squaring maps `Q` into `Q₀` and maps
`Q ∖ Q₀` onto `Q₀^#`.  Conjugation by `K`, which is transitive on `Q₀^#`
(§1 Proposition 3), matches the fibres bijectively, so all `|Q₀| − 1` of them
have the same size and `(|Q₀| − 1)·|fibre| = |Q| − |Q₀|`.  With `|Q| = |Q₀|²`
this gives `|fibre| = |Q₀|`. -/
theorem card_sqFibre_eq_card_Q0_of_isSuzuki2Group
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    (hcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2) :
    Nat.card ↥hyp.sqFibre = Nat.card ↥hyp.Q0 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- exponent `4`: squares land in `Q₀`
  have hsq : ∀ y ∈ hyp.Q, y ^ 2 ∈ hyp.Q0 := by
    intro y hy
    refine hyp.mem_Q0_of_mem_Q_of_sq_eq_one (hyp.Q.pow_mem hy 2) ?_
    have h4 : (⟨y, hy⟩ : ↥hyp.Q) ^ 4 = 1 :=
      OddOrder.Higman.Suzuki2Groups.pow_four_eq_one_of_isSuzuki2Group hQsuz _
    have hy4 : y ^ 4 = 1 := by
      simpa using congrArg (Subtype.val (p := fun z => z ∈ hyp.Q)) h4
    calc (y ^ 2) ^ 2 = y ^ 4 := by group
      _ = 1 := hy4
  -- the relevant finsets
  set QS : Finset G := (hyp.Q : Set G).toFinset with hQS
  set Q0S : Finset G := (hyp.Q0 : Set G).toFinset with hQ0S
  have hQ0sub : Q0S ⊆ QS := by
    intro y hy
    simp only [hQ0S, Set.mem_toFinset, SetLike.mem_coe] at hy
    simp only [hQS, Set.mem_toFinset, SetLike.mem_coe]
    exact hyp.Q0_le_Q hy
  set A : Finset G := QS \ Q0S with hA
  set B : Finset G := Q0S.erase 1 with hB
  have hmemA : ∀ y : G, y ∈ A ↔ y ∈ hyp.Q ∧ y ∉ hyp.Q0 := by
    intro y
    simp only [hA, Finset.mem_sdiff, hQS, hQ0S, Set.mem_toFinset, SetLike.mem_coe]
  have hmemB : ∀ u : G, u ∈ B ↔ u ∈ hyp.Q0 ∧ u ≠ 1 := by
    intro u
    simp only [hB, Finset.mem_erase, hQ0S, Set.mem_toFinset, SetLike.mem_coe]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  -- squaring maps `A` into `B`
  have hfibmap : ∀ y ∈ A, y ^ 2 ∈ B := by
    intro y hy
    obtain ⟨hyQ, hyQ0⟩ := (hmemA y).mp hy
    refine (hmemB _).mpr ⟨hsq y hyQ, ?_⟩
    intro h
    exact hyQ0 (hyp.mem_Q0_of_mem_Q_of_sq_eq_one hyQ h)
  have hsum := Finset.card_eq_sum_card_fiberwise hfibmap
  -- all fibres have the size of the one over `s`
  have hconst : ∀ u ∈ B, (A.filter fun y => y ^ 2 = u).card
      = (A.filter fun y => y ^ 2 = hyp.distinguishedInvolution).card := by
    intro u hu
    obtain ⟨huQ0, hu1⟩ := (hmemB u).mp hu
    -- `K` moves `s` to `u`
    have himg := hyp.image_conj_KSet_eq_involutions_H
      hyp.distinguishedInvolution_mem_H hyp.distinguishedInvolution_sq
      hyp.distinguishedInvolution_ne_one
    have humem : u ∈ {y : G | y ^ 2 = 1 ∧ y ≠ 1 ∧ y ∈ hyp.H} :=
      ⟨hyp.sq_eq_one_of_mem_Q0 huQ0, hu1, huQ0.2⟩
    rw [← himg] at humem
    obtain ⟨k, hkK, hk0⟩ := humem
    have hk : k⁻¹ * hyp.distinguishedInvolution * k = u := hk0
    have hkH : k ∈ hyp.H := hyp.D_le_H hkK.1
    have hkiH : k⁻¹ ∈ hyp.H := hyp.H.inv_mem hkH
    have hinj : Function.Injective (fun y : G => k⁻¹ * y * k) := by
      intro a b h
      simp only at h
      exact mul_left_cancel (mul_right_cancel h)
    -- conjugation by `k⁻¹` sends the `s`-fibre onto the `u`-fibre
    have hfwd : ∀ y : G, y ^ 2 = hyp.distinguishedInvolution →
        (k⁻¹ * y * k) ^ 2 = u := by
      intro y hy
      calc (k⁻¹ * y * k) ^ 2 = k⁻¹ * y ^ 2 * k := by rw [sq, sq]; group
        _ = k⁻¹ * hyp.distinguishedInvolution * k := by rw [hy]
        _ = u := hk
    have hbwd : ∀ z : G, z ^ 2 = u →
        (k * z * k⁻¹) ^ 2 = hyp.distinguishedInvolution := by
      intro z hz
      calc (k * z * k⁻¹) ^ 2 = k * z ^ 2 * k⁻¹ := by rw [sq, sq]; group
        _ = k * u * k⁻¹ := by rw [hz]
        _ = k * (k⁻¹ * hyp.distinguishedInvolution * k) * k⁻¹ := by rw [hk]
        _ = hyp.distinguishedInvolution := by group
    have himg2 : (A.filter fun y => y ^ 2 = u)
        = (A.filter fun y => y ^ 2 = hyp.distinguishedInvolution).image
            (fun y => k⁻¹ * y * k) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hzA, hzu⟩
        obtain ⟨hzQ, -⟩ := (hmemA z).mp hzA
        have hsqz : (k * z * k⁻¹) ^ 2 = hyp.distinguishedInvolution := hbwd z hzu
        refine ⟨k * z * k⁻¹, ⟨(hmemA _).mpr
          ⟨hyp.Q_normal_in_H k hkH z hzQ, ?_⟩, hsqz⟩, by group⟩
        intro hmem
        exact hyp.distinguishedInvolution_ne_one
          (by rw [← hsqz, hyp.sq_eq_one_of_mem_Q0 hmem])
      · rintro ⟨y, ⟨hyA, hys⟩, rfl⟩
        obtain ⟨hyQ, -⟩ := (hmemA y).mp hyA
        have hval : (k⁻¹ * y * k) ^ 2 = u := hfwd y hys
        have hmemQ : k⁻¹ * y * k ∈ hyp.Q := by
          have h := hyp.Q_normal_in_H k⁻¹ hkiH y hyQ
          rwa [inv_inv] at h
        refine ⟨(hmemA _).mpr ⟨hmemQ, ?_⟩, hval⟩
        intro hmem
        exact hu1 (by rw [← hval, hyp.sq_eq_one_of_mem_Q0 hmem])
    rw [himg2, Finset.card_image_of_injective _ hinj]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul] at hsum
  -- turn the finset counts into `Nat.card`s
  have hQScard : QS.card = Nat.card ↥hyp.Q := by
    simp [hQS, Set.toFinset_card, Nat.card_eq_fintype_card]
  have hQ0Scard : Q0S.card = Nat.card ↥hyp.Q0 := by
    simp [hQ0S, Set.toFinset_card, Nat.card_eq_fintype_card]
  have hAcard : A.card = Nat.card ↥hyp.Q - Nat.card ↥hyp.Q0 := by
    rw [hA, Finset.card_sdiff, Finset.inter_eq_left.mpr hQ0sub, hQScard, hQ0Scard]
  have hBcard : B.card = Nat.card ↥hyp.Q0 - 1 := by
    rw [hB, Finset.card_erase_of_mem (by
      simp only [hQ0S, Set.mem_toFinset, SetLike.mem_coe]; exact hyp.Q0.one_mem),
      hQ0Scard]
  have hFcard : (A.filter fun y => y ^ 2 = hyp.distinguishedInvolution).card
      = Nat.card ↥hyp.sqFibre := by
    have hset : (A.filter fun y => y ^ 2 = hyp.distinguishedInvolution)
        = hyp.sqFibre.toFinset := by
      ext z
      simp only [Finset.mem_filter, Set.mem_toFinset, hyp.mem_sqFibre_iff]
      constructor
      · rintro ⟨hzA, hzs⟩
        exact ⟨((hmemA z).mp hzA).1, hzs⟩
      · rintro ⟨hzQ, hzs⟩
        refine ⟨(hmemA z).mpr ⟨hzQ, ?_⟩, hzs⟩
        intro hmem
        exact hyp.distinguishedInvolution_ne_one
          (by rw [← hzs, hyp.sq_eq_one_of_mem_Q0 hmem])
    rw [hset]
    simp [Set.toFinset_card, Nat.card_eq_fintype_card]
  rw [hAcard, hBcard, hFcard, hcard] at hsum
  -- `q² − q = (q − 1) · F` with `q ≥ 2` gives `F = q`
  have hq2 := hyp.two_le_card_Q0
  set q := Nat.card ↥hyp.Q0 with hqdef
  set F := Nat.card ↥hyp.sqFibre with hFdef
  have hkey : (q - 1) * q = (q - 1) * F := by
    rw [← hsum]
    have : q ^ 2 - q = (q - 1) * q := by
      rw [sq, Nat.sub_mul]
      omega
    rw [this]
  exact (Nat.eq_of_mul_eq_mul_left (by omega) hkey).symm

/-- **The fibre is a single `Q₀`-coset once its size is `|Q₀|`** — the book's
"`{y ∈ S | y² = s} = xQ₀`" (p. 117), in the form used by both case (1) and
case (2).

`xQ₀ ⊆ {y ∈ Q | y² = s}` always (`mul_mem_sqFibre`), so equality of sizes
forces equality of sets. -/
theorem sqFibre_eq_coset_of_card
    (hcard : Nat.card ↥hyp.sqFibre = Nat.card ↥hyp.Q0)
    {x y : G} (hx : x ∈ hyp.sqFibre) (hy : y ∈ hyp.sqFibre) :
    x⁻¹ * y ∈ hyp.Q0 := by
  classical
  have hsub : (fun c => x * c) '' (hyp.Q0 : Set G) ⊆ hyp.sqFibre := by
    rintro z ⟨c, hc, rfl⟩
    exact hyp.mul_mem_sqFibre hx hc
  have hinj : Function.Injective (fun c : G => x * c) := fun a b h =>
    mul_left_cancel h
  have heq : (fun c => x * c) '' (hyp.Q0 : Set G) = hyp.sqFibre := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [Set.ncard_image_of_injective _ hinj,
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard]
    exact le_rfl
  rw [← heq] at hy
  obtain ⟨c, hc, hcy⟩ := hy
  have hxy : x⁻¹ * y = c := by rw [← hcy]; group
  rw [hxy]
  exact hc

/-- **`[K, W] = 1`** — a Chapter I fact the Ch. III §1 Proposition needs but that
Chapters I and II never state.

`W = C_D(Q₀)` is the kernel of the conjugation action of `D` on `Q₀`
(`ker_conjQ0`), `K` is normal in `D` (`K_normal`, Ch. I §2 Proposition 2) and
`K ⊓ V = 1` (`K_inf_V_eq_bot`) with `W ≤ V`.  For `k ∈ K` and `w ∈ W` the
commutator `wkw⁻¹k⁻¹` lies in `K` by normality and acts trivially on `Q₀`
because `w` does, so it lies in `K ⊓ W ≤ K ⊓ V = 1`. -/
theorem commute_of_mem_K_of_mem_W {k w : G} (hk : k ∈ hyp.K) (hw : w ∈ hyp.W) :
    Commute k w := by
  have hkD : k ∈ hyp.D := hyp.K_le_D hk
  have hwD : w ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hw)
  set e : ↥hyp.D := ⟨k, hkD⟩ with hedef
  set d : ↥hyp.D := ⟨w, hwD⟩ with hddef
  have hkK : e ∈ hyp.K.subgroupOf hyp.D := Subgroup.mem_subgroupOf.mpr hk
  have hd1 : hyp.conjQ0 d = 1 := by
    rw [← MonoidHom.mem_ker, hyp.ker_conjQ0]
    exact Subgroup.mem_subgroupOf.mpr hw
  have hcomm : d * e * d⁻¹ * e⁻¹ = 1 := by
    have h1 : d * e * d⁻¹ * e⁻¹ ∈ hyp.K.subgroupOf hyp.D :=
      Subgroup.mul_mem _ (hyp.K_normal.conj_mem e hkK d) (Subgroup.inv_mem _ hkK)
    have h2 : d * e * d⁻¹ * e⁻¹ ∈ hyp.W.subgroupOf hyp.D := by
      rw [← hyp.ker_conjQ0, MonoidHom.mem_ker]
      simp [map_mul, map_inv, hd1]
    have h3 : ((d * e * d⁻¹ * e⁻¹ : ↥hyp.D) : G) ∈ hyp.K ⊓ hyp.V :=
      ⟨Subgroup.mem_subgroupOf.mp h1, hyp.W_le_V (Subgroup.mem_subgroupOf.mp h2)⟩
    rw [hyp.K_inf_V_eq_bot, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hcd : Commute d e := by
    have hconj : d * e * d⁻¹ = e :=
      calc d * e * d⁻¹ = (d * e * d⁻¹ * e⁻¹) * e := by group
        _ = e := by rw [hcomm, one_mul]
    calc d * e = (d * e * d⁻¹) * d := by group
      _ = e * d := by rw [hconj]
  have hval : w * k = k * w := by
    simpa [hedef, hddef] using
      congrArg (Subtype.val (p := fun x => x ∈ hyp.D)) hcd.eq
  exact hval.symm

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (2)**: "`C_S(P)` is a
`K`-subgroup of `S`" (p. 117).

This is where the book's choice at the start of the proof — "if `W ≠ 1`, assume
that `P ⊂ W`" — is used: `K` centralizes `W` (`commute_of_mem_K_of_mem_W`), hence
centralizes `P`, hence normalizes `C_Q(P)`.  Together with `K ≤ D ≤ H` and
`Q ⊴ H` this makes `C_Q(P)` a `K`-invariant subgroup of `Q`. -/
theorem conj_mem_centralizer_of_mem_K_of_le_W {P : Subgroup G} (hPW : P ≤ hyp.W)
    {k : G} (hk : k ∈ hyp.K) {y : G}
    (hy : y ∈ hyp.Q ⊓ Subgroup.centralizer (P : Set G)) :
    k * y * k⁻¹ ∈ hyp.Q ⊓ Subgroup.centralizer (P : Set G) := by
  refine ⟨hyp.Q_normal_in_H k (hyp.D_le_H (hyp.K_le_D hk)) y hy.1,
    Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro g hg
  have hkg : Commute k g := hyp.commute_of_mem_K_of_mem_W hk (hPW hg)
  have hgk : g * k = k * g := hkg.symm.eq
  have hgki : g * k⁻¹ = k⁻¹ * g := hkg.symm.inv_right.eq
  have hyg : g * y = y * g := Subgroup.mem_centralizer_iff.mp hy.2 g hg
  calc g * (k * y * k⁻¹) = (g * k) * y * k⁻¹ := by group
    _ = (k * g) * y * k⁻¹ := by rw [hgk]
    _ = k * (g * y) * k⁻¹ := by group
    _ = k * (y * g) * k⁻¹ := by rw [hyg]
    _ = k * y * (g * k⁻¹) := by group
    _ = k * y * (k⁻¹ * g) := by rw [hgki]
    _ = (k * y * k⁻¹) * g := by group

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (1) core** (p. 117):
if `Q` is abelian and `C_Q(P) ≤ Q₀` for some prime-order `P ≤ V`, then
`Q = Q₀`.

The book's argument verbatim.  Assuming `Q ≠ Q₀`, pick `x ∈ Q` with `x² = s`
(`exists_sq_eq_distinguishedInvolution`).  Commutativity turns the fibre
`{y ∈ Q | y² = s}` into the coset `xQ₀`, so its size `|Q₀|` is a power of `2`
and hence prime to the odd `p`; the fixed-point step then produces
`y ∈ C_Q(P) ≤ Q₀` with `y² = s ≠ 1`, a contradiction. -/
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
  have hx : x ∈ hyp.sqFibre := ⟨hxQ, hxs⟩
  have hnotdvd : ¬ p ∣ Nat.card ↥hyp.sqFibre := by
    rw [← hyp.card_sqFibre_eq_card_Q0_of_commute hcomm hx]
    exact hyp.not_dvd_card_Q0 hQ2 hp hPcard hPV
  obtain ⟨y, hyT, hyC⟩ :=
    hyp.exists_mem_centralizer_mem_sqFibre hp hPcard hPV hnotdvd
  have h1 : y ^ 2 = 1 := hyp.sq_eq_one_of_mem_Q0 (hCle ⟨hyT.1, hyC⟩)
  rw [hyT.2] at h1
  exact hyp.distinguishedInvolution_ne_one h1

end Hypothesis

namespace SecondCaseHypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (sc : SecondCaseHypothesis G Ω)

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (1), branch selection**
(p. 117): "Suppose that `S` is abelian.  Then `C_S(P)` is abelian and so `st`
has order `3` and `C_S(P) ⊂ Q₀`."

An abelian `Q` makes `C_Q(P)` abelian, which rules out the two branches of
Ch. I §3 Proposition 1(c) whose payload is a Suzuki `2`-group (those are
non-abelian by definition).  The remaining `PSL(2, ℓ)` branch carries
`orderOf (st) = 3` and gives `|C_{Q₀}(P)| = |F| = |C_Q(P)|`, which upgrades the
inclusion `C_{Q₀}(P) ≤ C_Q(P)` to an equality. -/
theorem centralizer_le_Q0_and_orderOf_st_of_commute
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hcomm : ∀ a ∈ sc.toHypothesis.Q, ∀ b ∈ sc.toHypothesis.Q, Commute a b)
    {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    (hPV : P ≤ sc.toHypothesis.V) :
    sc.toHypothesis.Q ⊓ Subgroup.centralizer (P : Set G) ≤ sc.toHypothesis.Q0 ∧
      orderOf (sc.toHypothesis.distinguishedInvolution * sc.toHypothesis.t)
        = 3 := by
  classical
  set C : Subgroup G := Subgroup.centralizer (P : Set G) with hCdef
  -- `C_Q(P)` inherits commutativity from `Q`
  haveI habel : IsMulCommutative ↥(sc.toHypothesis.Q.subgroupOf C) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext
      (hcomm _ (Subgroup.mem_subgroupOf.mp a.2) _
        (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩
  -- `P ≠ 1`, since it has prime order
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hp.one_lt.ne hPcard
  letI := sc.toHypothesis.centralizerQuotientMulAction hPV
  obtain ⟨data⟩ := sc.toHypothesis.centralizer_trichotomy_of_induction hPV hPne
    (sc.twoRank_centralizer_ge_two P hPV p hp hPcard) ind
  -- the `C_Q(P) ≤ Q₀` half, given the two matching cardinalities
  have hle : ∀ n : ℕ,
      Nat.card ↥(sc.toHypothesis.Q0.subgroupOf C) = n →
      Nat.card ↥(sc.toHypothesis.Q.subgroupOf C) = n →
      sc.toHypothesis.Q ⊓ C ≤ sc.toHypothesis.Q0 := by
    intro n h0 hQ
    have hsub : sc.toHypothesis.Q0.subgroupOf C ≤ sc.toHypothesis.Q.subgroupOf C :=
      fun x hx => Subgroup.mem_subgroupOf.mpr
        (sc.toHypothesis.Q0_le_Q (Subgroup.mem_subgroupOf.mp hx))
    have heq : sc.toHypothesis.Q0.subgroupOf C = sc.toHypothesis.Q.subgroupOf C :=
      Subgroup.eq_of_le_of_card_ge hsub (by rw [h0, hQ])
    intro x hx
    have hxC : x ∈ C := hx.2
    have hmem : (⟨x, hxC⟩ : ↥C) ∈ sc.toHypothesis.Q.subgroupOf C :=
      Subgroup.mem_subgroupOf.mpr hx.1
    rw [← heq] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  rcases data.branch with ⟨d, -, det⟩ | ⟨d, -, det⟩ | ⟨d, -, det⟩
  · exact ⟨hle _ det.natCard_cQ0_eq_field det.natCard_cQ_eq_field,
      det.distinguishedProduct_order⟩
  · exact absurd habel det.cQ_isSuzuki2Group.2.1
  · exact absurd habel det.cQ_isSuzuki2Group.2.1

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (1)** (p. 117):
if `Q` (`= S`, by Theorem C) is abelian then `S = Q₀` and `st` has order `3`.

Combines the branch selection with the coset/fixed-point argument
`Q_eq_Q0_of_commute_of_centralizer_le`.  The prime-order `P ≤ V` the book fixes
at the start of the proof exists because (C1) gives `V ≠ 1`. -/
theorem Q_eq_Q0_and_orderOf_st_of_commute
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hQ2 : IsPGroup 2 ↥sc.toHypothesis.Q)
    (hcomm : ∀ a ∈ sc.toHypothesis.Q, ∀ b ∈ sc.toHypothesis.Q, Commute a b) :
    sc.toHypothesis.Q = sc.toHypothesis.Q0 ∧
      orderOf (sc.toHypothesis.distinguishedInvolution * sc.toHypothesis.t)
        = 3 := by
  classical
  -- a prime-order subgroup of `V ≠ 1`
  obtain ⟨g, hgV, hg1⟩ : ∃ g ∈ sc.toHypothesis.V, g ≠ 1 := by
    by_contra hall
    push Not at hall
    exact sc.V_ne_bot (le_bot_iff.mp fun x hx => Subgroup.mem_bot.mpr (hall x hx))
  have hord : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord
  have hpos : 0 < orderOf g := orderOf_pos g
  have hmpos : 0 < orderOf g / p := Nat.div_pos (Nat.le_of_dvd hpos hpdvd) hp.pos
  have hyord : orderOf (g ^ (orderOf g / p)) = p := by
    rw [orderOf_pow_of_dvd hmpos.ne' (Nat.div_dvd_of_dvd hpdvd)]
    exact Nat.div_div_self hpdvd hpos.ne'
  have hcardP : Nat.card ↥(Subgroup.zpowers (g ^ (orderOf g / p))) = p := by
    rw [Nat.card_zpowers, hyord]
  have hPV : Subgroup.zpowers (g ^ (orderOf g / p)) ≤ sc.toHypothesis.V :=
    Subgroup.zpowers_le.mpr (pow_mem hgV _)
  obtain ⟨hCle, hst⟩ :=
    sc.centralizer_le_Q0_and_orderOf_st_of_commute ind hcomm hp hcardP hPV
  exact ⟨sc.toHypothesis.Q_eq_Q0_of_commute_of_centralizer_le hQ2 hcomm hp
    hcardP hPV hCle, hst⟩

/-- **Peterfalvi Part II, Ch. III §1, Proposition, cases (2) and (3), the
exponent-`4` step** (p. 117): "`P` normalizes `xQ₀` whence `C_S(P)` has
exponent `4`".

If `Q` is a Suzuki `2`-group of order `|Q₀|²` then the fibre `{y ∈ Q | y² = s}`
has `|Q₀|` elements (`card_sqFibre_eq_card_Q0_of_isSuzuki2Group`), a power of
`2`, so the fixed-point step yields `y ∈ C_Q(P)` with `y² = s ≠ 1`. -/
theorem exists_mem_centralizer_mem_sqFibre_of_isSuzuki2Group
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥sc.toHypothesis.Q)
    (hcard : Nat.card ↥sc.toHypothesis.Q = Nat.card ↥sc.toHypothesis.Q0 ^ 2)
    {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    (hPV : P ≤ sc.toHypothesis.V) :
    ∃ y ∈ sc.toHypothesis.sqFibre, y ∈ Subgroup.centralizer (P : Set G) := by
  refine sc.toHypothesis.exists_mem_centralizer_mem_sqFibre hp hPcard hPV ?_
  rw [sc.toHypothesis.card_sqFibre_eq_card_Q0_of_isSuzuki2Group hQsuz hcard]
  exact sc.toHypothesis.not_dvd_card_Q0 hQsuz.1 hp hPcard hPV

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (2), branch selection**
(p. 117): if `Q` is a Suzuki `2`-group of order `|Q₀|²` then `C_Q(P)` is a
Suzuki `2`-group.

Equivalently: the `PSL(2, ℓ)` alternative of Ch. I §3 Proposition 1(c), whose
payload makes `C_Q(P)` elementary abelian, cannot occur — the previous lemma
puts an element of order `4` in `C_Q(P)`.  Both surviving alternatives
(`Sz(ℓ)`, `PSU(3, ℓ)`) carry `cQ_isSuzuki2Group`.

This is the input to the book's remaining step, which rules out `PSU(3, ℓ)` by
the computation `C_{D₀}(Ω₁(S₀)) ≠ 1` in `PSU(3, ℓ)` and then concludes
`F/Z(F) ≅ Sz(ℓ)` with `st` of order `5`. -/
theorem isSuzuki2Group_centralizer_of_card_sq
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥sc.toHypothesis.Q)
    (hcard : Nat.card ↥sc.toHypothesis.Q = Nat.card ↥sc.toHypothesis.Q0 ^ 2)
    {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    (hPV : P ≤ sc.toHypothesis.V) :
    OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group
      ↥(sc.toHypothesis.Q.subgroupOf (Subgroup.centralizer (P : Set G))) := by
  classical
  obtain ⟨y, hyT, hyC⟩ := sc.exists_mem_centralizer_mem_sqFibre_of_isSuzuki2Group
    hQsuz hcard hp hPcard hPV
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hp.one_lt.ne hPcard
  letI := sc.toHypothesis.centralizerQuotientMulAction hPV
  obtain ⟨data⟩ := sc.toHypothesis.centralizer_trichotomy_of_induction hPV hPne
    (sc.twoRank_centralizer_ge_two P hPV p hp hPcard) ind
  rcases data.branch with ⟨d, -, det⟩ | ⟨d, -, det⟩ | ⟨d, -, det⟩
  · -- the `PSL(2, ℓ)` branch would make `C_Q(P)` elementary abelian
    exfalso
    have hmem : (⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.mpr hyT.1⟩ :
        ↥(sc.toHypothesis.Q.subgroupOf (Subgroup.centralizer (P : Set G))))
        ^ 2 = 1 := det.cQ_isElementaryAbelian.2 _
    have h1 : y ^ 2 = 1 := by
      simpa using congrArg (fun z => ((z : ↥(Subgroup.centralizer (P : Set G))) : G))
        (congrArg (Subtype.val (p := fun z =>
          z ∈ sc.toHypothesis.Q.subgroupOf (Subgroup.centralizer (P : Set G))))
          hmem)
    rw [hyT.2] at h1
    exact sc.toHypothesis.distinguishedInvolution_ne_one h1
  · exact det.cQ_isSuzuki2Group
  · exact det.cQ_isSuzuki2Group

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
