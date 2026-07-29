/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.TwoKSubgroups

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

**Case (3)** (`S` non-abelian of order `q³`) concludes `orderOf (st) = 3` and
`W ≠ 1`; Ch. I §3 Lemma 5 (`lemmaFive_of_orderThree`) then gives type B.  The
first half is complete here; the book's count of the `K`-subgroups of `S` of
order `q²` is replaced by a construction plus operator Maschke, see
`Hypothesis.exists_two_kSubgroups_invariant_of_card_cube`.

**Case (2)** (`S` non-abelian of order `q²`) concludes `W = 1` and
`orderOf (st) = 5`.  The book's `PSU(3, ℓ)` exclusion, which it defers with "as
can be checked", is replaced by a count against the cardinality relation
Ch. I §3 Proposition 1(c) carries in that branch; see
`Hypothesis.natCard_inf_centralizer_le_sq`.

## Main results

* `sylowTwoOfQ_eq_Q` — after Theorem C, the book's `S` is `Q`.
* `centralizer_le_Q0_and_orderOf_st_of_commute`,
  `Q_eq_Q0_and_orderOf_st_of_commute` — **case (1)**: if `Q` is abelian then
  `Q = Q₀` and `st` has order `3`.
* `exists_mem_centralizer_mem_sqFibre_of_isSuzuki2Group`,
  `isSuzuki2Group_centralizer_of_card_sq` — case (2)'s exponent-`4` step and
  the resulting branch selection (`C_Q(P)` is a Suzuki `2`-group).
* `orderOf_st_eq_five_of_isSuzuki2Group`, `W_eq_bot_of_isSuzuki2Group` —
  **case (2)**: `st` has order `5` and `W = 1`.
* `false_of_typeA_centralizer_of_two_kSubgroups`,
  `orderOf_st_eq_three_of_two_kSubgroups` — **case (3)'s `st` has order `3`**,
  given the two `K`-subgroups of `S` of order `q²` that `P` normalizes.
* `orderOf_st_eq_three_of_card_cube_of_not_isTypeB`,
  `orderOf_st_eq_three_of_card_cube` — **case (3)**: `S` of order `q³` forces
  `st` to have order `3`, with no hypothesis on the type of `S`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

universe uG uΩ

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

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (3): `st` does not have
order `5`** (p. 117), given the two `K`-subgroups the book produces.

> As in case (2), `P` then centralizes an element `x ∈ X` and an element `y ∈ Y`
> such that `x² = y² = s`.  But, since `C_S(P)` is of type A, it follows that
> `y ∈ x Ω₁ C_S(P)` and `y ∈ X`, which is a contradiction.

Hypotheses: `X` and `Y` are distinct `K`-invariant subgroups between `Q₀` and
`Q` of order `|Q₀|²`, both normalized by `P`, and `C_Q(P)` carries standard
type-A data — which is exactly what the `Sz(ℓ)` branch of Ch. I §3
Proposition 1(c) supplies when `st` has order `5`.

The two square roots come from `exists_mem_centralizer_mem_sqFibreIn`.  Type A
makes squaring injective modulo `Ω₁` (`sq_inv_mul_eq_one_of_sq_eq`), so
`(x⁻¹y)² = 1` and hence `x⁻¹y ∈ Q₀`; then `y ∈ xQ₀ ⊆ X`, so
`y ∈ X ⊓ Y = Q₀` (`inf_eq_Q0_of_ne_of_kInvariant`) while `y² = s ≠ 1`. -/
theorem false_of_typeA_centralizer_of_two_kSubgroups
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥sc.toHypothesis.Q)
    {X Y : Subgroup G}
    (hXQ : X ≤ sc.toHypothesis.Q) (hQ0X : sc.toHypothesis.Q0 ≤ X)
    (hXinv : ∀ k ∈ sc.toHypothesis.K, ∀ y ∈ X, k * y * k⁻¹ ∈ X)
    (hXcard : Nat.card ↥X = Nat.card ↥sc.toHypothesis.Q0 ^ 2)
    (hYQ : Y ≤ sc.toHypothesis.Q) (hQ0Y : sc.toHypothesis.Q0 ≤ Y)
    (hYinv : ∀ k ∈ sc.toHypothesis.K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y)
    (hYcard : Nat.card ↥Y = Nat.card ↥sc.toHypothesis.Q0 ^ 2)
    (hne : X ≠ Y)
    {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    (hPV : P ≤ sc.toHypothesis.V)
    (hPX : ∀ g ∈ P, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hPY : ∀ g ∈ P, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (dataA : OddOrder.GroupTheory.SpecificGroups.Suzuki.StandardTypeAData
      ↥(sc.toHypothesis.Q.subgroupOf (Subgroup.centralizer (P : Set G)))) :
    False := by
  classical
  obtain ⟨x, hxT, hxC⟩ := sc.toHypothesis.exists_mem_centralizer_mem_sqFibreIn
    hQsuz hXQ hQ0X hXinv hXcard hp hPcard hPV hPX
  obtain ⟨y, hyT, hyC⟩ := sc.toHypothesis.exists_mem_centralizer_mem_sqFibreIn
    hQsuz hYQ hQ0Y hYinv hYcard hp hPcard hPV hPY
  -- type A: equal squares force `x⁻¹y ∈ Ω₁`
  have hsq : (⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.mpr (hXQ hxT.1)⟩ :
        ↥(sc.toHypothesis.Q.subgroupOf (Subgroup.centralizer (P : Set G)))) ^ 2
      = (⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.mpr (hYQ hyT.1)⟩ :
        ↥(sc.toHypothesis.Q.subgroupOf (Subgroup.centralizer (P : Set G)))) ^ 2 := by
    have hval : x ^ 2 = y ^ 2 := by rw [hxT.2, hyT.2]
    exact Subtype.ext (Subtype.ext hval)
  have hone := dataA.sq_inv_mul_eq_one_of_sq_eq hsq
  have hsq1 : (x⁻¹ * y) ^ 2 = 1 := by
    simpa using congrArg
      (fun z => ((z : ↥(Subgroup.centralizer (P : Set G))) : G))
      (congrArg (Subtype.val (p := fun z =>
        z ∈ sc.toHypothesis.Q.subgroupOf (Subgroup.centralizer (P : Set G))))
        hone)
  have hQ0mem : x⁻¹ * y ∈ sc.toHypothesis.Q0 :=
    sc.toHypothesis.mem_Q0_of_mem_Q_of_sq_eq_one
      (sc.toHypothesis.Q.mul_mem (sc.toHypothesis.Q.inv_mem (hXQ hxT.1))
        (hYQ hyT.1)) hsq1
  -- so `y ∈ X ⊓ Y = Q₀`, contradicting `y² = s ≠ 1`
  have hyX : y ∈ X := by
    rw [show y = x * (x⁻¹ * y) from by group]
    exact X.mul_mem hxT.1 (hQ0X hQ0mem)
  have hinf := sc.toHypothesis.inf_eq_Q0_of_ne_of_kInvariant hQsuz hXQ hQ0X
    hXinv hXcard hQ0Y hYinv hYcard hne
  have hyQ0 : y ∈ sc.toHypothesis.Q0 := by
    rw [← hinf]; exact ⟨hyX, hyT.1⟩
  have hy1 : y ^ 2 = 1 := sc.toHypothesis.sq_eq_one_of_mem_Q0 hyQ0
  rw [hyT.2] at hy1
  exact sc.toHypothesis.distinguishedInvolution_ne_one hy1

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (3): `st` has order 3**
(p. 117), given the two `K`-subgroups.

> Suppose that `st` has order 5. … `P` normalizes at least two `K`-subgroups `X`
> and `Y` of order `q²` in `S`. … which is a contradiction.  Thus `st` has
> order 3.

Of the three alternatives of Ch. I §3 Proposition 1(c) only the `Sz(ℓ)` one has
`orderOf (st) = 5`, and it puts standard type-A data on `C_Q(P)` — refuted by
`false_of_typeA_centralizer_of_two_kSubgroups`.  Both surviving alternatives
carry `orderOf (st) = 3`. -/
theorem orderOf_st_eq_three_of_two_kSubgroups
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥sc.toHypothesis.Q)
    {X Y : Subgroup G}
    (hXQ : X ≤ sc.toHypothesis.Q) (hQ0X : sc.toHypothesis.Q0 ≤ X)
    (hXinv : ∀ k ∈ sc.toHypothesis.K, ∀ y ∈ X, k * y * k⁻¹ ∈ X)
    (hXcard : Nat.card ↥X = Nat.card ↥sc.toHypothesis.Q0 ^ 2)
    (hYQ : Y ≤ sc.toHypothesis.Q) (hQ0Y : sc.toHypothesis.Q0 ≤ Y)
    (hYinv : ∀ k ∈ sc.toHypothesis.K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y)
    (hYcard : Nat.card ↥Y = Nat.card ↥sc.toHypothesis.Q0 ^ 2)
    (hne : X ≠ Y)
    {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    (hPV : P ≤ sc.toHypothesis.V)
    (hPX : ∀ g ∈ P, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hPY : ∀ g ∈ P, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) :
    orderOf (sc.toHypothesis.distinguishedInvolution * sc.toHypothesis.t) = 3 := by
  classical
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hp.one_lt.ne hPcard
  letI := sc.toHypothesis.centralizerQuotientMulAction hPV
  obtain ⟨data⟩ := sc.toHypothesis.centralizer_trichotomy_of_induction hPV hPne
    (sc.twoRank_centralizer_ge_two P hPV p hp hPcard) ind
  rcases data.branch with ⟨d, -, det⟩ | ⟨d, -, det⟩ | ⟨d, -, det⟩
  · exact det.distinguishedProduct_order
  · exact (sc.false_of_typeA_centralizer_of_two_kSubgroups hQsuz hXQ hQ0X hXinv
      hXcard hYQ hQ0Y hYinv hYcard hne hp hPcard hPV hPX hPY
      det.standardTypeAData).elim
  · exact det.distinguishedProduct_order

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (3), types C and D**
(p. 117): if `S` is a Suzuki `2`-group of order `q³` that is not of type B, then
`st` has order `3`.

Higman's clause (d) supplies two `K`-subgroups of order `q²`, and outside type B
they are the only ones (`exists_two_kSubgroups_unique_of_card_cube`), so the
odd-order `P` normalizes both (`conj_mem_of_unique_of_le_V`) — the input of
`orderOf_st_eq_three_of_two_kSubgroups`. -/
theorem orderOf_st_eq_three_of_card_cube_of_not_isTypeB
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥sc.toHypothesis.Q)
    {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥sc.toHypothesis.Q0 = 2 ^ m)
    (hcardQ : Nat.card ↥sc.toHypothesis.Q = Nat.card ↥sc.toHypothesis.Q0 ^ 3)
    (hnotB : ¬ Suzuki2Groups.IsTypeB.{uG, 0} ↥sc.toHypothesis.Q)
    {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    (hPV : P ≤ sc.toHypothesis.V) :
    orderOf (sc.toHypothesis.distinguishedInvolution * sc.toHypothesis.t) = 3 := by
  obtain ⟨X, Y, hX, hY, hne, huniq⟩ :=
    sc.toHypothesis.exists_two_kSubgroups_unique_of_card_cube hQsuz hm hQ0card
      hcardQ hnotB
  exact sc.orderOf_st_eq_three_of_two_kSubgroups ind hQsuz
    hX.1 hX.2.1 hX.2.2.1 hX.2.2.2 hY.1 hY.2.1 hY.2.2.1 hY.2.2.2 hne hp hPcard hPV
    (Hypothesis.conj_mem_of_unique_of_le_V hp hPcard hPV hX hne huniq)
    (Hypothesis.conj_mem_of_unique_of_le_V hp hPcard hPV hY (Ne.symm hne)
      (fun Z hZ => (huniq Z hZ).symm))

/-- **Peterfalvi Part II, Ch. III §1, Proposition, case (3): `st` has order 3**
(p. 117), unconditionally.

> Suppose that `st` has order 5.  It follows that `C_S(P)` is a Suzuki `2`-group
> of type A. … `P` normalizes at least two `K`-subgroups `X` and `Y` of order
> `q²` in `S`. … which is a contradiction.  Thus `st` has order 3.

If `st` had order `5`, Ch. I §3 Proposition 1(c) would put a Suzuki `2`-group
structure on `C_Q(P)`; being non-abelian it has an element `v` of order `4`,
which `P` centralizes.  `exists_two_kSubgroups_invariant_of_card_cube` then
produces the two `K`-subgroups of order `q²` normalized by `P`, and
`false_of_typeA_centralizer_of_two_kSubgroups` refutes the branch. -/
theorem orderOf_st_eq_three_of_card_cube
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥sc.toHypothesis.Q)
    {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥sc.toHypothesis.Q0 = 2 ^ m)
    (hcardQ : Nat.card ↥sc.toHypothesis.Q = Nat.card ↥sc.toHypothesis.Q0 ^ 3)
    {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    (hPV : P ≤ sc.toHypothesis.V) :
    orderOf (sc.toHypothesis.distinguishedInvolution * sc.toHypothesis.t) = 3 := by
  classical
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hp.one_lt.ne hPcard
  letI := sc.toHypothesis.centralizerQuotientMulAction hPV
  obtain ⟨data⟩ := sc.toHypothesis.centralizer_trichotomy_of_induction hPV hPne
    (sc.twoRank_centralizer_ge_two P hPV p hp hPcard) ind
  rcases data.branch with ⟨d, -, det⟩ | ⟨d, -, det⟩ | ⟨d, -, det⟩
  · exact det.distinguishedProduct_order
  · exfalso
    -- a non-abelian group of exponent dividing `4` has an element of order `4`
    obtain ⟨x, hx⟩ : ∃ x : ↥(sc.toHypothesis.Q.subgroupOf
        (Subgroup.centralizer (P : Set G))), x ^ 2 ≠ 1 := by
      by_contra hall
      push Not at hall
      refine det.cQ_isSuzuki2Group.2.1 ⟨⟨fun a b => ?_⟩⟩
      have ha : a * a = 1 := by rw [← sq]; exact hall a
      have hb : b * b = 1 := by rw [← sq]; exact hall b
      have hab : (a * b) * (a * b) = 1 := by rw [← sq]; exact hall (a * b)
      have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hb,
        inv_eq_of_mul_eq_one_right ha] at h1
      exact h1.symm
    set v : G := ((x : ↥(Subgroup.centralizer (P : Set G))) : G) with hvdef
    have hvQ : v ∈ sc.toHypothesis.Q := Subgroup.mem_subgroupOf.mp x.2
    have hvC : ∀ g ∈ P, g * v = v * g := fun g hg =>
      Subgroup.mem_centralizer_iff.mp
        (x : ↥(Subgroup.centralizer (P : Set G))).2 g hg
    have hvsq : v ^ 2 ≠ 1 := by
      intro h
      refine hx (Subtype.ext (Subtype.ext ?_))
      simpa using h
    have hvQ0 : v ∉ sc.toHypothesis.Q0 := fun h =>
      hvsq (sc.toHypothesis.sq_eq_one_of_mem_Q0 h)
    obtain ⟨X, Y, hX, hY, hne, hXP, hYP⟩ :=
      sc.toHypothesis.exists_two_kSubgroups_invariant_of_card_cube hQsuz hm
        hQ0card hcardQ hp hPcard hPV hvQ hvQ0 hvC
    exact sc.false_of_typeA_centralizer_of_two_kSubgroups hQsuz
      hX.1 hX.2.1 hX.2.2.1 hX.2.2.2 hY.1 hY.2.1 hY.2.2.1 hY.2.2.2 hne hp hPcard
      hPV hXP hYP det.standardTypeAData
  · exact det.distinguishedProduct_order

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
