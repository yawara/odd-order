/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.SquareRootFibres

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
itself.  The apparatus shared by the three cases — the fibre
`{y ∈ S | y² = s}`, its counts, the fixed-point step and the `K`-action — lives
in `SquareRootFibres.lean`; this file assembles the cases from it.

**Case (1)** (`S` abelian) is the book's

> Suppose that `S` is abelian.  Then `C_S(P)` is abelian and so `st` has order
> `3` and `C_S(P) ⊂ Q₀`.  Suppose that `S ≠ Q₀`.  There is then an element
> `x ∈ S` such that `x² = s` (since `K` is transitive on `Q₀^#`); since `S` is
> abelian, `{y ∈ S | y² = s} = xQ₀`.  But `P` centralizes `s` (Chapter I, §1,
> Proposition 5) and so normalizes `xQ₀` which is of cardinality prime to `p`,
> whence `C_S(P) ⊄ Q₀`, which is a contradiction.  Thus `S = Q₀`.

**Case (2)** (`S` non-abelian of order `q²`) concludes `W = 1` and
`orderOf (st) = 5`.  The book's `PSU(3, ℓ)` exclusion, which it defers with "as
can be checked", is replaced by a count against the cardinality relation
Ch. I §3 Proposition 1(c) carries in that branch; see
`Hypothesis.natCard_inf_centralizer_le_sq`.

## Main results

* `sylowTwoOfQ_eq_Q` — after Theorem C, the book's `S` is `Q`.
* `exists_le_card_eq_prime` — "let `P` be a subgroup of prime order `p`".
* `centralizer_le_Q0_and_orderOf_st_of_commute`,
  `Q_eq_Q0_and_orderOf_st_of_commute` — **case (1)**: if `Q` is abelian then
  `Q = Q₀` and `st` has order `3`.
* `exists_mem_centralizer_mem_sqFibre_of_isSuzuki2Group`,
  `isSuzuki2Group_centralizer_of_card_sq` — case (2)'s exponent-`4` step and
  the resulting branch selection (`C_Q(P)` is a Suzuki `2`-group).
* `orderOf_st_eq_five_of_isSuzuki2Group`, `W_eq_bot_of_isSuzuki2Group` —
  **case (2)**: `st` has order `5` and `W = 1`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

universe uG uΩ

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
  obtain ⟨P, p, hp, hcardP, hPV⟩ := exists_le_card_eq_prime sc.V_ne_bot
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

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (2), conclusion** (p. 117):
if `S = Q` is a Suzuki `2`-group of order `q²`, then `st` has order `5`.

The book:

> But, if `G₀ = PSU(3, ℓ)`, `S₀` is a Sylow `2`-subgroup of `G₀` and
> `N_{G₀}(S₀) = S₀ ⋊ D₀`, then, as can be checked, `C_{D₀}(Ω₁(S₀)) ≠ 1`.  It
> follows that `F/Z(F)` is not isomorphic to `PSU(3, ℓ)` and so, since `C_S(P)`
> has exponent `4`, `F/Z(F) ≅ Sz(ℓ)` and `st` has order `5`.

Both exclusions are carried out against Ch. I §3 Proposition 1(c):

* `PSL(2, ℓ)` is out because its payload makes `C_Q(P)` elementary abelian while
  the exponent-`4` step puts an element of order `4` there
  (`exists_mem_centralizer_mem_sqFibre_of_isSuzuki2Group`);
* `PSU(3, ℓ)` is out because its payload asserts `|C_Q(P)| = |C_{Q₀}(P)|³`,
  which exceeds the bound `|C_Q(P)| ≤ |C_{Q₀}(P)|²` forced by squaring
  (`natCard_inf_centralizer_le_sq`) as soon as `|C_{Q₀}(P)| ≥ 2` — and `s` is a
  non-trivial element of `C_{Q₀}(P)`.  This replaces the book's unperformed
  `PSU(3, ℓ)` Sylow-normalizer computation; see
  `natCard_inf_centralizer_le_sq` for the discussion.

What survives is the `Sz(ℓ)` branch, whose payload is `orderOf (st) = 5`. -/
theorem orderOf_st_eq_five_of_isSuzuki2Group
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥sc.toHypothesis.Q)
    (hcard : Nat.card ↥sc.toHypothesis.Q = Nat.card ↥sc.toHypothesis.Q0 ^ 2)
    {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    (hPV : P ≤ sc.toHypothesis.V) :
    orderOf (sc.toHypothesis.distinguishedInvolution * sc.toHypothesis.t) = 5 := by
  classical
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hp.one_lt.ne hPcard
  letI := sc.toHypothesis.centralizerQuotientMulAction hPV
  obtain ⟨data⟩ := sc.toHypothesis.centralizer_trichotomy_of_induction hPV hPne
    (sc.twoRank_centralizer_ge_two P hPV p hp hPcard) ind
  have hconv : ∀ H : Subgroup G,
      Nat.card ↥(H.subgroupOf (Subgroup.centralizer (P : Set G))) =
        Nat.card ↥(H ⊓ Subgroup.centralizer (P : Set G)) := by
    intro H
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : H ⊓ Subgroup.centralizer (P : Set G) ≤ _)).toEquiv
  rcases data.branch with ⟨d, -, det⟩ | ⟨d, -, det⟩ | ⟨d, -, det⟩
  · -- the `PSL(2, ℓ)` branch would make `C_Q(P)` elementary abelian
    exfalso
    obtain ⟨y, hyT, hyC⟩ := sc.exists_mem_centralizer_mem_sqFibre_of_isSuzuki2Group
      hQsuz hcard hp hPcard hPV
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
  · exact det.distinguishedProduct_order
  · -- the `PSU(3, ℓ)` branch asserts `|C_Q(P)| = |C_{Q₀}(P)|³`
    exfalso
    have hb := sc.toHypothesis.natCard_inf_centralizer_le_sq hQsuz
      (sc.toHypothesis.card_sqFibre_eq_card_Q0_of_isSuzuki2Group hQsuz hcard) P
    have h3 := det.natCard_cQ_eq_cQ0_cube
    simp only [hconv] at h3
    have h2 := sc.toHypothesis.two_le_natCard_inf_Q0_centralizer hPV
    rw [h3] at hb
    set c := Nat.card ↥(sc.toHypothesis.Q0 ⊓ Subgroup.centralizer (P : Set G))
      with hcdef
    have hpow : c ^ 3 = c ^ 2 * c := by ring
    have hcpos : 0 < c ^ 2 := pow_pos (by omega) 2
    have hmul : c ^ 2 * 2 ≤ c ^ 2 * c := Nat.mul_le_mul_left _ h2
    omega

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (2): `W = 1`** (p. 117).

> If `W ≠ 1`, `C_S(P)` is a `K`-subgroup of `S` which has exponent `4` and so
> `C_S(P) = S`, contrary to the fact that `D` acts faithfully on `S`.

Assume `W ≠ 1` and take `P ≤ W` of prime order — this is the book's opening
choice "if `W ≠ 1`, assume that `P ⊂ W`".  Then

* `C_Q(P)` is `K`-invariant, because `K` centralizes `W`
  (`conj_mem_centralizer_of_mem_K_of_le_W`, resting on `commute_of_mem_K_of_mem_W`);
* `C_Q(P)` contains an element of order `4`, namely a `P`-fixed square root of
  `s` (`exists_mem_centralizer_mem_sqFibre_of_isSuzuki2Group`);

so `C_Q(P) = Q` (`Q_le_of_kInvariant_of_sq_ne_one`).  That makes `P` centralize
`Q` while `P ≤ W ≤ V ≤ D`, and `C_D(Q) = 1` (Ch. I Proposition 4(c),
`centralizer_Q_inf_D_eq_bot`) forces `P = 1`, contradicting `|P| = p`. -/
theorem W_eq_bot_of_isSuzuki2Group
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥sc.toHypothesis.Q)
    (hcard : Nat.card ↥sc.toHypothesis.Q = Nat.card ↥sc.toHypothesis.Q0 ^ 2) :
    sc.toHypothesis.W = ⊥ := by
  classical
  by_contra hW
  obtain ⟨P, p, hp, hPcard, hPW⟩ := exists_le_card_eq_prime hW
  have hPV : P ≤ sc.toHypothesis.V := le_trans hPW sc.toHypothesis.W_le_V
  -- a `P`-fixed square root of `s`, i.e. an element of order `4` in `C_Q(P)`
  obtain ⟨y, hyT, hyC⟩ := sc.exists_mem_centralizer_mem_sqFibre_of_isSuzuki2Group
    hQsuz hcard hp hPcard hPV
  have hy2 : y ^ 2 ≠ 1 := by
    rw [hyT.2]; exact sc.toHypothesis.distinguishedInvolution_ne_one
  -- the `K`-invariant subgroup `C_Q(P)` is therefore all of `Q`
  have hQle : sc.toHypothesis.Q ≤
      sc.toHypothesis.Q ⊓ Subgroup.centralizer (P : Set G) :=
    sc.toHypothesis.Q_le_of_kInvariant_of_sq_ne_one
      (sc.toHypothesis.card_sqFibre_eq_card_Q0_of_isSuzuki2Group hQsuz hcard)
      (fun _ hv => sc.toHypothesis.sq_mem_Q0_of_isSuzuki2Group hQsuz hv)
      inf_le_left
      (fun _ hk _ hv =>
        sc.toHypothesis.conj_mem_centralizer_of_mem_K_of_le_W hPW hk hv)
      ⟨hyT.1, hyC⟩ hy2
  -- so `P ≤ C_D(Q) = 1`
  have hPbot : P = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hmem : x ∈ sc.toHypothesis.D ⊓
        Subgroup.centralizer (sc.toHypothesis.Q : Set G) := by
      refine ⟨sc.toHypothesis.V_le_D (hPV hx), Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro q hq
      exact (Subgroup.mem_centralizer_iff.mp (hQle hq).2 x hx).symm
    rwa [sc.toHypothesis.centralizer_Q_inf_D_eq_bot] at hmem
  rw [hPbot, Subgroup.card_bot] at hPcard
  exact hp.one_lt.ne hPcard

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
