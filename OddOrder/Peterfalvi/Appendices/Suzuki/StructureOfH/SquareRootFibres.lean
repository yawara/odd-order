/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.CoherenceContradiction

/-!
# The square-root fibre `{y ∈ S | y² = s}` and its `K`-symmetry

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III, §1, pp. 116–117.

The proof of the Ch. III §1 Proposition — the trichotomy for `S`
(`Trichotomy.lean`) — runs three times through the same apparatus: the set of
square roots of the distinguished involution,

`{y ∈ S | y² = s}`,

its decomposition into `Q₀`-cosets, its cardinality, the fixed points of `P` on
it, and the way `K` permutes it.  This file isolates that apparatus, stated for
`Q` (which is the book's `S` once Theorem C gives `Q₁ = 1`).

## Main results

### The fibre and its cosets

* `mem_Q0_of_mem_Q_of_sq_eq_one` — `Ω₁(Q) = Q₀`.
* `exists_sq_eq_distinguishedInvolution` — the book's "there is an element
  `x ∈ S` such that `x² = s` (since `K` is transitive on `Q₀^#`)".
* `sqFibre`, `mul_mem_sqFibre` — the fibre and the inclusion `xQ₀ ⊆ fibre`,
  which needs only `Q₀ ≤ Z(Q)`.
* `sqFibre_eq_coset_of_card` — "`{y ∈ S | y² = s} = xQ₀`", from equal sizes.

### Counting

* `card_sqFibre_eq_card_Q0_of_commute` — case (1)'s count (`Q` abelian).
* `sq_mem_Q0_of_isSuzuki2Group`, `card_sqFibre_eq_card_Q0_of_isSuzuki2Group` —
  case (2)'s count `(q² − q)/(q − 1) = q`, via Higman Theorem 1(a).
* `natCard_inf_centralizer_le_sq` — `|C_Q(P)| ≤ |C_{Q₀}(P)|²`, the bound that
  rules out the `PSU(3, ℓ)` alternative in case (2).

### The fixed-point step

* `prime_ne_two_of_le_V`, `not_dvd_card_Q0` — `p` is odd, so prime to `|Q₀|`.
* `exists_mem_centralizer_mem_sqFibre` — "`P` … normalizes `xQ₀` which is of
  cardinality prime to `p`", producing a square root of `s` in `C_Q(P)`.

### `K`-invariance

* `exists_mem_K_conj_eq_of_mem_Q0` — `K` is transitive on `Q₀^#` (§1 Prop 3).
* `eq_bot_or_Q0_le_of_kInvariant`, `inv_mul_mem_Q0_of_sq_eq`,
  `exists_mem_K_conj_mem_coset`, `Q_le_of_kInvariant_of_sq_ne_one` — a
  `K`-invariant subgroup of `Q` containing an element of order `4` is `Q`.
* `commute_of_mem_K_of_mem_W`, `conj_mem_centralizer_of_mem_K_of_le_W` —
  `[K, W] = 1`, hence the book's "`C_S(P)` is a `K`-subgroup of `S`".

### Case (1)'s core

* `Q_eq_Q0_of_commute_of_centralizer_le` — an abelian `Q` whose `P`-centralizer
  lies in `Q₀` equals `Q₀`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

universe uG uΩ

/-! ## Two general steps of the Proposition's proof -/

/-- **"Let `P` be a subgroup of prime order `p`"** (Peterfalvi Part II, Ch. III
§1, p. 116) — a non-trivial subgroup of a finite group has a subgroup of prime
order.

The Proposition's proof opens by choosing such a `P` inside `V`, and — when
`W ≠ 1` — inside `W`; both choices are instances of this. -/
theorem exists_le_card_eq_prime {G : Type uG} [Group G] [Finite G]
    {Y : Subgroup G} (hY : Y ≠ ⊥) :
    ∃ (P : Subgroup G) (p : ℕ), p.Prime ∧ Nat.card ↥P = p ∧ P ≤ Y := by
  obtain ⟨g, hgY, hg1⟩ : ∃ g ∈ Y, g ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hY (le_bot_iff.mp fun x hx => Subgroup.mem_bot.mpr (hall x hx))
  have hord : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord
  have hpos : 0 < orderOf g := orderOf_pos g
  have hmpos : 0 < orderOf g / p := Nat.div_pos (Nat.le_of_dvd hpos hpdvd) hp.pos
  have hyord : orderOf (g ^ (orderOf g / p)) = p := by
    rw [orderOf_pow_of_dvd hmpos.ne' (Nat.div_dvd_of_dvd hpdvd)]
    exact Nat.div_div_self hpdvd hpos.ne'
  exact ⟨Subgroup.zpowers (g ^ (orderOf g / p)), p, hp,
    by rw [Nat.card_zpowers, hyord], Subgroup.zpowers_le.mpr (Y.pow_mem hgY _)⟩

/-- **The fixed-point step** (Peterfalvi Part II, Ch. III §1, p. 117): "`P` …
normalizes `xQ₀` which is of cardinality prime to `p`", in the general form the
Proposition uses it.

A subgroup `P` of prime order `p` acting by conjugation on a set `T` whose
cardinality is prime to `p` has a fixed point in `T` — that is, some element of
`T` centralizes `P`.  The Proposition applies this to the fibre
`{y ∈ S | y² = s}` in cases (1) and (2), and to its intersection with a
`K`-subgroup of `S` in case (3). -/
theorem exists_mem_centralizer_of_conj_invariant {G : Type uG} [Group G] [Finite G]
    {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    {T : Set G} (hTinv : ∀ g ∈ P, ∀ y ∈ T, g * y * g⁻¹ ∈ T)
    (hnotdvd : ¬ p ∣ Nat.card ↥T) :
    ∃ y ∈ T, y ∈ Subgroup.centralizer (P : Set G) := by
  classical
  letI actP : MulAction ↥P ↥T :=
    { smul := fun g y => ⟨(g : G) * (y : G) * (g : G)⁻¹, hTinv g g.2 y y.2⟩
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

/-- The square roots of the distinguished involution `s` inside a subgroup `X`
of `Q`.

Cases (1) and (2) of the Ch. III §1 Proposition use `X = S`; case (3) uses the
two `K`-subgroups `X`, `Y` of `S` of order `q²` (p. 117). -/
def sqFibreIn (X : Subgroup G) : Set G :=
  {y | y ∈ X ∧ y ^ 2 = hyp.distinguishedInvolution}

lemma mem_sqFibreIn_iff {X : Subgroup G} {y : G} :
    y ∈ hyp.sqFibreIn X ↔ y ∈ X ∧ y ^ 2 = hyp.distinguishedInvolution := Iff.rfl

/-- The book's `{y ∈ S | y² = s}` (p. 117). -/
def sqFibre : Set G := hyp.sqFibreIn hyp.Q

lemma mem_sqFibre_iff {y : G} :
    y ∈ hyp.sqFibre ↔ y ∈ hyp.Q ∧ y ^ 2 = hyp.distinguishedInvolution := Iff.rfl

/-- **The fibre is a union of `Q₀`-cosets**: `Q₀ ≤ Z(Q)` (Ch. I §2 Prop 1(c)), so
multiplying a square root of `s` by an element of `Q₀` gives another one.  No
commutativity of `Q` is needed — this is the inclusion `xQ₀ ⊆ {y | y² = s}` the
book uses in all three cases. -/
theorem mul_mem_sqFibreIn {X : Subgroup G} (hXQ : X ≤ hyp.Q) (hQ0X : hyp.Q0 ≤ X)
    {y c : G} (hy : y ∈ hyp.sqFibreIn X) (hc : c ∈ hyp.Q0) :
    y * c ∈ hyp.sqFibreIn X := by
  have hcm : c * y = y * c :=
    (Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hc) y
      (hXQ hy.1)).symm
  refine ⟨X.mul_mem hy.1 (hQ0X hc), ?_⟩
  calc (y * c) ^ 2 = y * (c * y) * c := by rw [sq]; group
    _ = y * (y * c) * c := by rw [hcm]
    _ = y ^ 2 * c ^ 2 := by rw [sq, sq]; group
    _ = hyp.distinguishedInvolution := by
        rw [hy.2, hyp.sq_eq_one_of_mem_Q0 hc, mul_one]

/-- The `X = S` case of `mul_mem_sqFibreIn`. -/
theorem mul_mem_sqFibre {y c : G} (hy : y ∈ hyp.sqFibre) (hc : c ∈ hyp.Q0) :
    y * c ∈ hyp.sqFibre :=
  hyp.mul_mem_sqFibreIn le_rfl hyp.Q0_le_Q hy hc

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

/-- **The fibre is `P`-invariant for any `P ≤ V`** — the book's "`P` centralizes
`s` (Chapter I, §1, Proposition 5) and so normalizes `xQ₀`" (p. 117).

`V = C_D(s)` centralizes `s` and `V ≤ D ≤ H` normalizes `Q`, so conjugation by an
element of `V` permutes `{y ∈ Q | y² = s}`. -/
theorem conj_mem_sqFibre_of_mem_V {g : G} (hg : g ∈ hyp.V) {y : G}
    (hy : y ∈ hyp.sqFibre) : g * y * g⁻¹ ∈ hyp.sqFibre := by
  have hgH : g ∈ hyp.H := hyp.D_le_H (hyp.V_le_D hg)
  refine ⟨hyp.Q_normal_in_H _ hgH _ hy.1, ?_⟩
  have hgs : g * hyp.distinguishedInvolution * g⁻¹
      = hyp.distinguishedInvolution := by
    have hgV : g ∈ hyp.V := hg
    rw [hyp.V_eq_centralizer_distinguishedInvolution] at hgV
    have hc := Subgroup.mem_centralizer_iff.mp hgV.2
      hyp.distinguishedInvolution rfl
    rw [← hc]; group
  calc (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ := by rw [sq, sq]; group
    _ = hyp.distinguishedInvolution := by rw [hy.2]; exact hgs

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
    ∃ y ∈ hyp.sqFibre, y ∈ Subgroup.centralizer (P : Set G) :=
  exists_mem_centralizer_of_conj_invariant hp hPcard
    (fun _ hg _ hy => hyp.conj_mem_sqFibre_of_mem_V (hPV hg) hy) hnotdvd

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

/-- **Squares of a Suzuki `2`-group `Q` lie in `Q₀`** — Higman Theorem 1(a)
(`pow_four_eq_one_of_isSuzuki2Group`) gives `Q` exponent dividing `4`, and
`Q₀ = Ω₁(Q)` (`mem_Q0_of_mem_Q_of_sq_eq_one`).

Used by cases (2) and (3) of the Ch. III §1 Proposition, where the induced map
`Q/Q₀ → Q₀` carries the `K`-action across. -/
theorem sq_mem_Q0_of_isSuzuki2Group
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    {y : G} (hy : y ∈ hyp.Q) : y ^ 2 ∈ hyp.Q0 := by
  refine hyp.mem_Q0_of_mem_Q_of_sq_eq_one (hyp.Q.pow_mem hy 2) ?_
  have h4 : (⟨y, hy⟩ : ↥hyp.Q) ^ 4 = 1 :=
    OddOrder.Higman.Suzuki2Groups.pow_four_eq_one_of_isSuzuki2Group hQsuz _
  have hy4 : y ^ 4 = 1 := by
    simpa using congrArg (Subtype.val (p := fun z => z ∈ hyp.Q)) h4
  calc (y ^ 2) ^ 2 = y ^ 4 := by group
    _ = 1 := hy4

/-- **Peterfalvi Part II, Ch. III §1, Proposition, the coset count** (p. 117):
"Since `|{y ∈ S | y² = s}| = (q² − q)/(q − 1) = q`, we again find that
`{y ∈ S | y² = s} = xQ₀`."

Stated for an arbitrary `K`-invariant subgroup `X` with `Q₀ ≤ X ≤ Q` of order
`|Q₀|²`: case (2) takes `X = S` and case (3) takes for `X` each of the two
`K`-subgroups of `S` of order `q²`.

A Suzuki `2`-group has exponent dividing `4` (Higman Theorem 1(a),
`pow_four_eq_one_of_isSuzuki2Group`), so squaring maps `X` into `Q₀` and maps
`X ∖ Q₀` onto `Q₀^#`.  Conjugation by `K`, which is transitive on `Q₀^#`
(§1 Proposition 3) and preserves `X`, matches the fibres bijectively, so all
`|Q₀| − 1` of them have the same size and `(|Q₀| − 1)·|fibre| = |X| − |Q₀|`.
With `|X| = |Q₀|²` this gives `|fibre| = |Q₀|`. -/
theorem card_sqFibreIn_eq_card_Q0_of_kInvariant
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    {X : Subgroup G} (hXQ : X ≤ hyp.Q) (hQ0X : hyp.Q0 ≤ X)
    (hXinv : ∀ k ∈ hyp.K, ∀ y ∈ X, k * y * k⁻¹ ∈ X)
    (hcard : Nat.card ↥X = Nat.card ↥hyp.Q0 ^ 2) :
    Nat.card ↥(hyp.sqFibreIn X) = Nat.card ↥hyp.Q0 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- exponent `4`: squares land in `Q₀`
  have hsq : ∀ y ∈ X, y ^ 2 ∈ hyp.Q0 := fun _ hy =>
    hyp.sq_mem_Q0_of_isSuzuki2Group hQsuz (hXQ hy)
  -- the relevant finsets
  set QS : Finset G := (X : Set G).toFinset with hQS
  set Q0S : Finset G := (hyp.Q0 : Set G).toFinset with hQ0S
  have hQ0sub : Q0S ⊆ QS := by
    intro y hy
    simp only [hQ0S, Set.mem_toFinset, SetLike.mem_coe] at hy
    simp only [hQS, Set.mem_toFinset, SetLike.mem_coe]
    exact hQ0X hy
  set A : Finset G := QS \ Q0S with hA
  set B : Finset G := Q0S.erase 1 with hB
  have hmemA : ∀ y : G, y ∈ A ↔ y ∈ X ∧ y ∉ hyp.Q0 := by
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
    exact hyQ0 (hyp.mem_Q0_of_mem_Q_of_sq_eq_one (hXQ hyQ) h)
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
    have hkKsub : k ∈ hyp.K := Subgroup.subset_closure hkK
    have hkiK : k⁻¹ ∈ hyp.K := hyp.K.inv_mem hkKsub
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
          ⟨hXinv k hkKsub z hzQ, ?_⟩, hsqz⟩, by group⟩
        intro hmem
        exact hyp.distinguishedInvolution_ne_one
          (by rw [← hsqz, hyp.sq_eq_one_of_mem_Q0 hmem])
      · rintro ⟨y, ⟨hyA, hys⟩, rfl⟩
        obtain ⟨hyQ, -⟩ := (hmemA y).mp hyA
        have hval : (k⁻¹ * y * k) ^ 2 = u := hfwd y hys
        have hmemQ : k⁻¹ * y * k ∈ X := by
          have h := hXinv k⁻¹ hkiK y hyQ
          rwa [inv_inv] at h
        refine ⟨(hmemA _).mpr ⟨hmemQ, ?_⟩, hval⟩
        intro hmem
        exact hu1 (by rw [← hval, hyp.sq_eq_one_of_mem_Q0 hmem])
    rw [himg2, Finset.card_image_of_injective _ hinj]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul] at hsum
  -- turn the finset counts into `Nat.card`s
  have hQScard : QS.card = Nat.card ↥X := by
    simp [hQS, Set.toFinset_card, Nat.card_eq_fintype_card]
  have hQ0Scard : Q0S.card = Nat.card ↥hyp.Q0 := by
    simp [hQ0S, Set.toFinset_card, Nat.card_eq_fintype_card]
  have hAcard : A.card = Nat.card ↥X - Nat.card ↥hyp.Q0 := by
    rw [hA, Finset.card_sdiff, Finset.inter_eq_left.mpr hQ0sub, hQScard, hQ0Scard]
  have hBcard : B.card = Nat.card ↥hyp.Q0 - 1 := by
    rw [hB, Finset.card_erase_of_mem (by
      simp only [hQ0S, Set.mem_toFinset, SetLike.mem_coe]; exact hyp.Q0.one_mem),
      hQ0Scard]
  have hFcard : (A.filter fun y => y ^ 2 = hyp.distinguishedInvolution).card
      = Nat.card ↥(hyp.sqFibreIn X) := by
    have hset : (A.filter fun y => y ^ 2 = hyp.distinguishedInvolution)
        = (hyp.sqFibreIn X).toFinset := by
      ext z
      simp only [Finset.mem_filter, Set.mem_toFinset, hyp.mem_sqFibreIn_iff]
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
  set F := Nat.card ↥(hyp.sqFibreIn X) with hFdef
  have hkey : (q - 1) * q = (q - 1) * F := by
    rw [← hsum]
    have : q ^ 2 - q = (q - 1) * q := by
      rw [sq, Nat.sub_mul]
      omega
    rw [this]
  exact (Nat.eq_of_mul_eq_mul_left (by omega) hkey).symm

/-- The `X = S` case of `card_sqFibreIn_eq_card_Q0_of_kInvariant`: case (2)'s
count `(q² − q)/(q − 1) = q`. -/
theorem card_sqFibre_eq_card_Q0_of_isSuzuki2Group
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    (hcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2) :
    Nat.card ↥hyp.sqFibre = Nat.card ↥hyp.Q0 :=
  hyp.card_sqFibreIn_eq_card_Q0_of_kInvariant hQsuz le_rfl hyp.Q0_le_Q
    (fun k hk y hy => hyp.Q_normal_in_H k (hyp.D_le_H (hyp.K_le_D hk)) y hy)
    hcard

/-- **The fibre is a single `Q₀`-coset once its size is `|Q₀|`** — the book's
"`{y ∈ S | y² = s} = xQ₀`" (p. 117), used in all three cases.

`xQ₀ ⊆ {y ∈ X | y² = s}` always (`mul_mem_sqFibreIn`), so equality of sizes
forces equality of sets. -/
theorem sqFibreIn_eq_coset_of_card
    {X : Subgroup G} (hXQ : X ≤ hyp.Q) (hQ0X : hyp.Q0 ≤ X)
    (hcard : Nat.card ↥(hyp.sqFibreIn X) = Nat.card ↥hyp.Q0)
    {x y : G} (hx : x ∈ hyp.sqFibreIn X) (hy : y ∈ hyp.sqFibreIn X) :
    x⁻¹ * y ∈ hyp.Q0 := by
  classical
  have hsub : (fun c => x * c) '' (hyp.Q0 : Set G) ⊆ hyp.sqFibreIn X := by
    rintro z ⟨c, hc, rfl⟩
    exact hyp.mul_mem_sqFibreIn hXQ hQ0X hx hc
  have hinj : Function.Injective (fun c : G => x * c) := fun a b h =>
    mul_left_cancel h
  have heq : (fun c => x * c) '' (hyp.Q0 : Set G) = hyp.sqFibreIn X := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [Set.ncard_image_of_injective _ hinj,
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard]
    exact le_rfl
  rw [← heq] at hy
  obtain ⟨c, hc, hcy⟩ := hy
  have hxy : x⁻¹ * y = c := by rw [← hcy]; group
  rw [hxy]
  exact hc

/-- The `X = S` case of `sqFibreIn_eq_coset_of_card`. -/
theorem sqFibre_eq_coset_of_card
    (hcard : Nat.card ↥hyp.sqFibre = Nat.card ↥hyp.Q0)
    {x y : G} (hx : x ∈ hyp.sqFibre) (hy : y ∈ hyp.sqFibre) :
    x⁻¹ * y ∈ hyp.Q0 :=
  hyp.sqFibreIn_eq_coset_of_card le_rfl hyp.Q0_le_Q hcard hx hy

/-- **"As in case (2), `P` then centralizes an element `x ∈ X` such that
`x² = s`"** (p. 117, case (3)).

For a `K`-invariant `X` with `Q₀ ≤ X ≤ Q` of order `|Q₀|²` the fibre
`{y ∈ X | y² = s}` has `|Q₀|` elements
(`card_sqFibreIn_eq_card_Q0_of_kInvariant`), a power of `2` and so prime to the
odd `p`.  If `P` also normalizes `X`, it acts on the fibre and therefore fixes
a point of it. -/
theorem exists_mem_centralizer_mem_sqFibreIn
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    {X : Subgroup G} (hXQ : X ≤ hyp.Q) (hQ0X : hyp.Q0 ≤ X)
    (hXinv : ∀ k ∈ hyp.K, ∀ y ∈ X, k * y * k⁻¹ ∈ X)
    (hXcard : Nat.card ↥X = Nat.card ↥hyp.Q0 ^ 2)
    {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    (hPV : P ≤ hyp.V) (hPX : ∀ g ∈ P, ∀ y ∈ X, g * y * g⁻¹ ∈ X) :
    ∃ y ∈ hyp.sqFibreIn X, y ∈ Subgroup.centralizer (P : Set G) := by
  refine exists_mem_centralizer_of_conj_invariant hp hPcard
    (fun g hg y hy => ⟨hPX g hg y hy.1,
      (hyp.conj_mem_sqFibre_of_mem_V (hPV hg) ⟨hXQ hy.1, hy.2⟩).2⟩) ?_
  rw [hyp.card_sqFibreIn_eq_card_Q0_of_kInvariant hQsuz hXQ hQ0X hXinv hXcard]
  exact hyp.not_dvd_card_Q0 hQsuz.1 hp hPcard hPV

/-- **`K` is transitive on `Q₀^#`** in the elementwise form used below: any two
non-trivial elements of `Q₀` are `K`-conjugate.

Restatement of §1 Proposition 3 (`image_conj_KSet_eq_involutions_H`) — the
involutions of `H` are exactly `Q₀^#`, and `K` permutes them transitively. -/
theorem exists_mem_K_conj_eq_of_mem_Q0 {u v : G} (hu : u ∈ hyp.Q0) (hu1 : u ≠ 1)
    (hv : v ∈ hyp.Q0) (hv1 : v ≠ 1) :
    ∃ k ∈ hyp.K, k * u * k⁻¹ = v := by
  have himgu := hyp.image_conj_KSet_eq_involutions_H hu.2
    (hyp.sq_eq_one_of_mem_Q0 hu) hu1
  have hvmem : v ∈ {y : G | y ^ 2 = 1 ∧ y ≠ 1 ∧ y ∈ hyp.H} :=
    ⟨hyp.sq_eq_one_of_mem_Q0 hv, hv1, hv.2⟩
  rw [← himgu] at hvmem
  obtain ⟨k, hkK, hk⟩ := hvmem
  refine ⟨k⁻¹, Subgroup.inv_mem _ (Subgroup.subset_closure hkK), ?_⟩
  have hk' : k⁻¹ * u * k = v := hk
  rw [inv_inv]
  exact hk'

/-- **`K`-invariant subgroups of `Q₀` are trivial or all of `Q₀`** — step (1) of
the "`C_S(P)` is a `K`-subgroup, hence `= S`" argument (p. 117).

Immediate from transitivity of `K` on `Q₀^#`: a non-trivial `K`-invariant subset
of `Q₀` swallows every non-trivial element. -/
theorem eq_bot_or_Q0_le_of_kInvariant {X : Subgroup G} (hXQ0 : X ≤ hyp.Q0)
    (hXinv : ∀ k ∈ hyp.K, ∀ y ∈ X, k * y * k⁻¹ ∈ X) :
    X = ⊥ ∨ hyp.Q0 ≤ X := by
  rcases eq_or_ne X ⊥ with h | h
  · exact Or.inl h
  refine Or.inr ?_
  obtain ⟨u, huX, hu1⟩ : ∃ u ∈ X, u ≠ 1 := by
    by_contra hall
    push Not at hall
    exact h (le_bot_iff.mp fun z hz => Subgroup.mem_bot.mpr (hall z hz))
  intro v hv
  rcases eq_or_ne v 1 with rfl | hv1
  · exact X.one_mem
  obtain ⟨k, hkK, hk⟩ :=
    hyp.exists_mem_K_conj_eq_of_mem_Q0 (hXQ0 huX) hu1 hv hv1
  rw [← hk]
  exact hXinv k hkK u huX

/-- **Every fibre of squaring over `Q₀^#` is a single `Q₀`-coset**, given that
the one over `s` is (`sqFibreIn_eq_coset_of_card`).

Transitivity of `K` on `Q₀^#` moves any fibre onto the `s`-fibre, and `Q₀` is
`D`-invariant, so the coset statement transports back. -/
theorem inv_mul_mem_Q0_of_sq_eq_in
    {X : Subgroup G} (hXQ : X ≤ hyp.Q) (hQ0X : hyp.Q0 ≤ X)
    (hXinv : ∀ k ∈ hyp.K, ∀ y ∈ X, k * y * k⁻¹ ∈ X)
    (hcard : Nat.card ↥(hyp.sqFibreIn X) = Nat.card ↥hyp.Q0)
    {y w : G} (hyX : y ∈ X) (hwX : w ∈ X) (hsq : y ^ 2 = w ^ 2)
    (hne : y ^ 2 ≠ 1) (hsqQ0 : y ^ 2 ∈ hyp.Q0) :
    y⁻¹ * w ∈ hyp.Q0 := by
  obtain ⟨k, hkK, hk⟩ := hyp.exists_mem_K_conj_eq_of_mem_Q0 hsqQ0 hne
    ⟨hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_mem_H⟩
    hyp.distinguishedInvolution_ne_one
  have hkD : k ∈ hyp.D := hyp.K_le_D hkK
  have hconjsq : ∀ v : G, (k * v * k⁻¹) ^ 2 = k * v ^ 2 * k⁻¹ := by
    intro v; rw [sq, sq]; group
  have hy' : k * y * k⁻¹ ∈ hyp.sqFibreIn X :=
    ⟨hXinv k hkK y hyX, by rw [hconjsq]; exact hk⟩
  have hw' : k * w * k⁻¹ ∈ hyp.sqFibreIn X :=
    ⟨hXinv k hkK w hwX, by rw [hconjsq, ← hsq]; exact hk⟩
  have hmem := hyp.sqFibreIn_eq_coset_of_card hXQ hQ0X hcard hy' hw'
  have hrw : (k * y * k⁻¹)⁻¹ * (k * w * k⁻¹) = k * (y⁻¹ * w) * k⁻¹ := by group
  rw [hrw] at hmem
  have hback := hyp.conj_mem_Q0_of_mem_D (Subgroup.inv_mem _ hkD) hmem
  rw [show k⁻¹ * (k * (y⁻¹ * w) * k⁻¹) * (k⁻¹)⁻¹ = y⁻¹ * w from by group] at hback
  exact hback

/-- The `X = S` case of `inv_mul_mem_Q0_of_sq_eq_in`. -/
theorem inv_mul_mem_Q0_of_sq_eq
    (hcard : Nat.card ↥hyp.sqFibre = Nat.card ↥hyp.Q0)
    {y w : G} (hyQ : y ∈ hyp.Q) (hwQ : w ∈ hyp.Q) (hsq : y ^ 2 = w ^ 2)
    (hne : y ^ 2 ≠ 1) (hsqQ0 : y ^ 2 ∈ hyp.Q0) :
    y⁻¹ * w ∈ hyp.Q0 :=
  hyp.inv_mul_mem_Q0_of_sq_eq_in le_rfl hyp.Q0_le_Q
    (fun k hk v hv => hyp.Q_normal_in_H k (hyp.D_le_H (hyp.K_le_D hk)) v hv)
    hcard hyQ hwQ hsq hne hsqQ0

/-- **`K` is transitive on `(X/Q₀)^#`** in elementwise form.

Squaring induces a `K`-equivariant map `X/Q₀ → Q₀` (well defined because
`Q₀ ≤ Z(Q)` has exponent `2`) whose fibres over `Q₀^#` are single cosets
(`inv_mul_mem_Q0_of_sq_eq_in`).  So transitivity on `Q₀^#` lifts: given
`y, z ∈ X` outside `Q₀`, some `k ∈ K` carries `y` into the coset `zQ₀`.

Case (2) uses `X = S`; case (3) uses each of the two `K`-subgroups of order
`q²`. -/
theorem exists_mem_K_conj_mem_coset_in
    {X : Subgroup G} (hXQ : X ≤ hyp.Q) (hQ0X : hyp.Q0 ≤ X)
    (hXinv : ∀ k ∈ hyp.K, ∀ y ∈ X, k * y * k⁻¹ ∈ X)
    (hcard : Nat.card ↥(hyp.sqFibreIn X) = Nat.card ↥hyp.Q0)
    {y z : G} (hyX : y ∈ X) (hzX : z ∈ X)
    (hy2 : y ^ 2 ≠ 1) (hz2 : z ^ 2 ≠ 1)
    (hyQ0 : y ^ 2 ∈ hyp.Q0) (hzQ0 : z ^ 2 ∈ hyp.Q0) :
    ∃ k ∈ hyp.K, z⁻¹ * (k * y * k⁻¹) ∈ hyp.Q0 := by
  obtain ⟨k, hkK, hk⟩ :=
    hyp.exists_mem_K_conj_eq_of_mem_Q0 hyQ0 hy2 hzQ0 hz2
  have hyX' : k * y * k⁻¹ ∈ X := hXinv k hkK y hyX
  have hsq' : (k * y * k⁻¹) ^ 2 = z ^ 2 := by
    rw [show (k * y * k⁻¹) ^ 2 = k * y ^ 2 * k⁻¹ from by rw [sq, sq]; group]
    exact hk
  exact ⟨k, hkK, hyp.inv_mul_mem_Q0_of_sq_eq_in hXQ hQ0X hXinv hcard hzX hyX'
    hsq'.symm hz2 hzQ0⟩

/-- The `X = S` case of `exists_mem_K_conj_mem_coset_in`. -/
theorem exists_mem_K_conj_mem_coset
    (hcard : Nat.card ↥hyp.sqFibre = Nat.card ↥hyp.Q0)
    {y z : G} (hyQ : y ∈ hyp.Q) (hzQ : z ∈ hyp.Q)
    (hy2 : y ^ 2 ≠ 1) (hz2 : z ^ 2 ≠ 1)
    (hyQ0 : y ^ 2 ∈ hyp.Q0) (hzQ0 : z ^ 2 ∈ hyp.Q0) :
    ∃ k ∈ hyp.K, z⁻¹ * (k * y * k⁻¹) ∈ hyp.Q0 :=
  hyp.exists_mem_K_conj_mem_coset_in le_rfl hyp.Q0_le_Q
    (fun k hk v hv => hyp.Q_normal_in_H k (hyp.D_le_H (hyp.K_le_D hk)) v hv)
    hcard hyQ hzQ hy2 hz2 hyQ0 hzQ0

/-- **`X` is simple as a `K`-group over `Q₀`**: a `K`-invariant subgroup between
`Q₀` and `X` is one of the two.

The book's case (3) uses this twice: to see that two distinct `K`-subgroups of
`S` of order `q²` meet in `Q₀`, and — with `X = S` in case (2) — that a
`K`-invariant subgroup of `S` containing an element of order `4` is all of `S`.

A `K`-invariant `Z` with an element `y` of order `4` swallows `Q₀`
(`eq_bot_or_Q0_le_of_kInvariant` applied to `Z ⊓ Q₀`, which contains `y²`) and
then meets every `Q₀`-coset of `X` by transitivity on `(X/Q₀)^#`. -/
theorem le_of_kInvariant_of_sq_ne_one_in
    {X : Subgroup G} (hXQ : X ≤ hyp.Q) (hQ0X : hyp.Q0 ≤ X)
    (hXinv : ∀ k ∈ hyp.K, ∀ y ∈ X, k * y * k⁻¹ ∈ X)
    (hcard : Nat.card ↥(hyp.sqFibreIn X) = Nat.card ↥hyp.Q0)
    (hsqQ0 : ∀ v ∈ X, v ^ 2 ∈ hyp.Q0)
    {Z : Subgroup G} (hZX : Z ≤ X)
    (hZinv : ∀ k ∈ hyp.K, ∀ v ∈ Z, k * v * k⁻¹ ∈ Z)
    {y : G} (hyZ : y ∈ Z) (hy2 : y ^ 2 ≠ 1) :
    X ≤ Z := by
  -- `Q₀ ≤ Z`
  have hQ0le : hyp.Q0 ≤ Z := by
    have hinter : Z ⊓ hyp.Q0 ≤ hyp.Q0 := inf_le_right
    have hintinv : ∀ k ∈ hyp.K, ∀ v ∈ Z ⊓ hyp.Q0, k * v * k⁻¹ ∈ Z ⊓ hyp.Q0 := by
      intro k hk v hv
      exact ⟨hZinv k hk v hv.1,
        hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D hk) hv.2⟩
    rcases hyp.eq_bot_or_Q0_le_of_kInvariant hinter hintinv with h | h
    · exfalso
      have hmem : y ^ 2 ∈ Z ⊓ hyp.Q0 :=
        ⟨Z.pow_mem hyZ 2, hsqQ0 _ (hZX hyZ)⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hy2 hmem
    · exact le_trans h inf_le_left
  -- reach every element of `X`
  intro z hzX
  rcases eq_or_ne (z ^ 2) 1 with hz2 | hz2
  · exact hQ0le (hyp.mem_Q0_of_mem_Q_of_sq_eq_one (hXQ hzX) hz2)
  obtain ⟨k, hkK, hc⟩ := hyp.exists_mem_K_conj_mem_coset_in hXQ hQ0X hXinv hcard
    (hZX hyZ) hzX hy2 hz2 (hsqQ0 _ (hZX hyZ)) (hsqQ0 _ hzX)
  have hyk : k * y * k⁻¹ ∈ Z := hZinv k hkK y hyZ
  have hzeq : z = (k * y * k⁻¹) * (z⁻¹ * (k * y * k⁻¹))⁻¹ := by group
  rw [hzeq]
  exact Z.mul_mem hyk (Z.inv_mem (hQ0le hc))

/-- The `X = S` case of `le_of_kInvariant_of_sq_ne_one_in` — case (2)'s
"`C_S(P)` is a `K`-subgroup of `S` which has exponent `4` and so
`C_S(P) = S`". -/
theorem Q_le_of_kInvariant_of_sq_ne_one
    (hcard : Nat.card ↥hyp.sqFibre = Nat.card ↥hyp.Q0)
    (hsqQ0 : ∀ v ∈ hyp.Q, v ^ 2 ∈ hyp.Q0)
    {X : Subgroup G} (hXQ : X ≤ hyp.Q)
    (hXinv : ∀ k ∈ hyp.K, ∀ v ∈ X, k * v * k⁻¹ ∈ X)
    {y : G} (hyX : y ∈ X) (hy2 : y ^ 2 ≠ 1) :
    hyp.Q ≤ X :=
  hyp.le_of_kInvariant_of_sq_ne_one_in le_rfl hyp.Q0_le_Q
    (fun k hk v hv => hyp.Q_normal_in_H k (hyp.D_le_H (hyp.K_le_D hk)) v hv)
    hcard hsqQ0 hXQ hXinv hyX hy2

/-- **Two distinct `K`-subgroups of `S` of order `q²` meet in `Q₀`** — the step
that makes the contradiction of case (3) work (p. 117): the element `y ∈ Y` that
turns out to lie in `X` is then in `Q₀`, contradicting `y² = s ≠ 1`.

`X ⊓ Y` is a `K`-invariant subgroup between `Q₀` and `X`; if it were bigger than
`Q₀` it would contain an element of order `4` and hence be all of `X`
(`le_of_kInvariant_of_sq_ne_one_in`), forcing `X ≤ Y` and so `X = Y`. -/
theorem inf_eq_Q0_of_ne_of_kInvariant
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    {X Y : Subgroup G} (hXQ : X ≤ hyp.Q) (hQ0X : hyp.Q0 ≤ X)
    (hXinv : ∀ k ∈ hyp.K, ∀ y ∈ X, k * y * k⁻¹ ∈ X)
    (hXcard : Nat.card ↥X = Nat.card ↥hyp.Q0 ^ 2)
    (hQ0Y : hyp.Q0 ≤ Y)
    (hYinv : ∀ k ∈ hyp.K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y)
    (hYcard : Nat.card ↥Y = Nat.card ↥hyp.Q0 ^ 2)
    (hne : X ≠ Y) :
    X ⊓ Y = hyp.Q0 := by
  refine le_antisymm ?_ (le_inf hQ0X hQ0Y)
  by_contra hnotle
  obtain ⟨y, hyZ, hyQ0⟩ : ∃ y ∈ X ⊓ Y, y ∉ hyp.Q0 := by
    by_contra hall
    push Not at hall
    exact hnotle fun z hz => hall z hz
  have hy2 : y ^ 2 ≠ 1 := fun h =>
    hyQ0 (hyp.mem_Q0_of_mem_Q_of_sq_eq_one (hXQ hyZ.1) h)
  have hXle : X ≤ X ⊓ Y :=
    hyp.le_of_kInvariant_of_sq_ne_one_in hXQ hQ0X hXinv
      (hyp.card_sqFibreIn_eq_card_Q0_of_kInvariant hQsuz hXQ hQ0X hXinv hXcard)
      (fun v hv => hyp.sq_mem_Q0_of_isSuzuki2Group hQsuz (hXQ hv))
      inf_le_left
      (fun k hk v hv => ⟨hXinv k hk v hv.1, hYinv k hk v hv.2⟩)
      hyZ hy2
  exact hne (Subgroup.eq_of_le_of_card_ge (le_trans hXle inf_le_right)
    (by rw [hXcard, hYcard]))

/-- **`s` is a non-trivial element of `C_{Q₀}(P)`** for any `P ≤ V`, since
`V = C_D(s)` (Ch. I §1 Proposition 5).  Hence `|C_{Q₀}(P)| ≥ 2`. -/
theorem two_le_natCard_inf_Q0_centralizer {P : Subgroup G} (hPV : P ≤ hyp.V) :
    2 ≤ Nat.card ↥(hyp.Q0 ⊓ Subgroup.centralizer (P : Set G)) := by
  have hsC : hyp.distinguishedInvolution ∈ Subgroup.centralizer (P : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
    have hgV : g ∈ hyp.V := hPV hg
    rw [hyp.V_eq_centralizer_distinguishedInvolution] at hgV
    exact (Subgroup.mem_centralizer_iff.mp hgV.2 hyp.distinguishedInvolution rfl).symm
  have hs : hyp.distinguishedInvolution ∈
      hyp.Q0 ⊓ Subgroup.centralizer (P : Set G) :=
    ⟨⟨hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_mem_H⟩, hsC⟩
  rcases Nat.lt_or_ge
    (Nat.card ↥(hyp.Q0 ⊓ Subgroup.centralizer (P : Set G))) 2 with hlt | hge
  · exfalso
    have h1 : Nat.card ↥(hyp.Q0 ⊓ Subgroup.centralizer (P : Set G)) = 1 := by
      have := Nat.card_pos (α := ↥(hyp.Q0 ⊓ Subgroup.centralizer (P : Set G)))
      omega
    rw [Subgroup.eq_bot_of_card_eq _ h1, Subgroup.mem_bot] at hs
    exact hyp.distinguishedInvolution_ne_one hs
  · exact hge

/-- **`|C_Q(P)| ≤ |C_{Q₀}(P)|²`** — the count that rules out the `PSU(3, ℓ)`
alternative in case (2) of the Ch. III §1 Proposition (p. 117).

In case (2) squaring maps `Q` into `Q₀` (exponent `4`,
`sq_mem_Q0_of_isSuzuki2Group`) with every fibre inside a single `Q₀`-coset
(`inv_mul_mem_Q0_of_sq_eq`).  Both properties survive intersecting with any
centralizer, so squaring gives `C_Q(P) → C_{Q₀}(P)` with at most `|C_{Q₀}(P)|`
fibres, each of size at most `|C_{Q₀}(P)|`.

**Deviation from the book.**  Peterfalvi rules out `PSU(3, ℓ)` here by the
structural computation "if `G₀ = PSU(3, ℓ)`, `S₀ ∈ Syl₂(G₀)` and
`N_{G₀}(S₀) = S₀ ⋊ D₀`, then, as can be checked, `C_{D₀}(Ω₁(S₀)) ≠ 1`", which he
does not carry out.  The repository's Ch. I §3 Proposition 1(c) already records
the exact cardinality relation `|C_Q(P)| = |C_{Q₀}(P)|³` of that branch
(`CentralizerPSUData.natCard_cQ_eq_cQ0_cube`), so the present bound contradicts
it outright once `|C_{Q₀}(P)| ≥ 2` (`two_le_natCard_inf_Q0_centralizer`).  Same
conclusion, no `PSU(3, ℓ)` Sylow-normalizer computation. -/
theorem natCard_inf_centralizer_le_sq
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    (hcard : Nat.card ↥hyp.sqFibre = Nat.card ↥hyp.Q0) (P : Subgroup G) :
    Nat.card ↥(hyp.Q ⊓ Subgroup.centralizer (P : Set G)) ≤
      Nat.card ↥(hyp.Q0 ⊓ Subgroup.centralizer (P : Set G)) ^ 2 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set C : Subgroup G := Subgroup.centralizer (P : Set G) with hC
  set A : Finset G := ((hyp.Q ⊓ C : Subgroup G) : Set G).toFinset with hA
  set B : Finset G := ((hyp.Q0 ⊓ C : Subgroup G) : Set G).toFinset with hB
  have hmemA : ∀ y : G, y ∈ A ↔ y ∈ hyp.Q ∧ y ∈ C := by
    intro y
    simp only [hA, Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_inf]
  have hmemB : ∀ y : G, y ∈ B ↔ y ∈ hyp.Q0 ∧ y ∈ C := by
    intro y
    simp only [hB, Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_inf]
  -- squaring sends `C_Q(P)` into `C_{Q₀}(P)`
  have hmap : ∀ y ∈ A, y ^ 2 ∈ B := by
    intro y hy
    obtain ⟨hyQ, hyC⟩ := (hmemA y).mp hy
    exact (hmemB _).mpr ⟨hyp.sq_mem_Q0_of_isSuzuki2Group hQsuz hyQ, C.pow_mem hyC 2⟩
  have hsum := Finset.card_eq_sum_card_fiberwise hmap
  -- every fibre lies in a coset of `C_{Q₀}(P)`
  have hfib : ∀ u ∈ B, (A.filter fun y => y ^ 2 = u).card ≤ B.card := by
    intro u hu
    rcases Finset.eq_empty_or_nonempty (A.filter fun y => y ^ 2 = u) with he | ⟨y₀, hy₀⟩
    · simp [he]
    obtain ⟨hy₀A, hy₀u⟩ := Finset.mem_filter.mp hy₀
    obtain ⟨hy₀Q, hy₀C⟩ := (hmemA y₀).mp hy₀A
    refine Finset.card_le_card_of_injOn (fun y => y₀⁻¹ * y) ?_ fun a _ b _ hab =>
      mul_left_cancel hab
    intro y hy
    obtain ⟨hyA, hyu⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyQ, hyC⟩ := (hmemA y).mp hyA
    refine (hmemB _).mpr ⟨?_, C.mul_mem (C.inv_mem hy₀C) hyC⟩
    rcases eq_or_ne u 1 with rfl | hu1
    · exact hyp.Q0.mul_mem
        (hyp.Q0.inv_mem (hyp.mem_Q0_of_mem_Q_of_sq_eq_one hy₀Q hy₀u))
        (hyp.mem_Q0_of_mem_Q_of_sq_eq_one hyQ hyu)
    · exact hyp.inv_mul_mem_Q0_of_sq_eq hcard hy₀Q hyQ (hy₀u.trans hyu.symm)
        (by rw [hy₀u]; exact hu1) (by rw [hy₀u]; exact ((hmemB u).mp hu).1)
  have hAcard : A.card = Nat.card ↥(hyp.Q ⊓ C) := by
    rw [hA, Set.toFinset_card, ← Nat.card_eq_fintype_card]; rfl
  have hBcard : B.card = Nat.card ↥(hyp.Q0 ⊓ C) := by
    rw [hB, Set.toFinset_card, ← Nat.card_eq_fintype_card]; rfl
  rw [← hAcard, ← hBcard]
  calc A.card = ∑ u ∈ B, (A.filter fun y => y ^ 2 = u).card := hsum
    _ ≤ ∑ _u ∈ B, B.card := Finset.sum_le_sum hfib
    _ = B.card ^ 2 := by rw [Finset.sum_const, smul_eq_mul, sq]

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

end OddOrder.Peterfalvi.Appendices.Suzuki
