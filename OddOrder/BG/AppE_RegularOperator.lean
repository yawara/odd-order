/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_CollectionFormula
import OddOrder.BG.Ch1_Preliminary.S04_SmallRankBasic
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.GroupTheory.HallCollection
import OddOrder.GroupTheory.HallPetresco
import OddOrder.GroupTheory.RegularPGroup
import OddOrder.GroupTheory.OmegaSubgroup
import OddOrder.GroupTheory.SubgroupInAmbient

/-!
# BG Appendix E — the 1991 Feit–Thompson regular-operator layer (E.3/E.4 opening)

The `C_R(R₀) = R₀ × R₁` structure and the commutator/cyclic-order helper layer of the
regular-operator results, up to (but not including) the small-order commutator lemmas.

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
-/

namespace OddOrder.BG.AppE

open OddOrder.GroupTheory
open scoped commutatorElement Pointwise


/-! ## E.3 / E.4: the 1991 Feit--Thompson regular-operator results -/

section RegularOperator

open OddOrder.Isaacs.Ch03 OddOrder.Isaacs.Ch04

variable {R B : Type*} [Group R] [Group B]

/-- `Φ(H)` transported back into the ambient group along `H.subtype`. -/
def frattiniInG {G : Type*} [Group G] (H : Subgroup G) : Subgroup G :=
  (frattini ↥H).map H.subtype

/-- **BG Theorem E.3, standing hypotheses** (Feit and Thompson, 1991).

`p` and `q` are distinct odd primes, `R` is a `p`-group, `R₀` and `R₁` are
nonidentity subgroups of `R`, `B` is an operator group on `R` and `A ≤ B`, with
`p ∤ |B|`, `|A| = q`, `|R₀| = p`, `R₁` cyclic, `C_R(R₀) = R₀ × R₁`, and `A` fixes
`R₀` and acts regularly on `R`.

Every field is a genuine proposition about the data; there are no opaque `Prop`
placeholders.  The operator action is the repo's standard encoding
`act : B →* MulAut R` (see `OddOrder.Isaacs.Ch03.IsAInvariant`), and "acts
regularly" is BG's `C_R(α) = 1` for all `α ∈ A^#`, spelled pointwise. -/
structure RegularOperatorSetup (R B : Type*) [Group R] [Group B] (p q : ℕ) where
  /-- `p` is prime. -/
  p_prime : p.Prime
  /-- `p` is odd. -/
  p_odd : Odd p
  /-- `q` is prime. -/
  q_prime : q.Prime
  /-- `q` is odd. -/
  q_odd : Odd q
  /-- `p` and `q` are distinct. -/
  p_ne_q : p ≠ q
  /-- `R` is a `p`-group. -/
  R_pGroup : IsPGroup p R
  /-- `B` acts on `R` as a group of operators. -/
  act : B →* MulAut R
  /-- `p` does not divide `|B|`. -/
  p_not_dvd_card_B : ¬ p ∣ Nat.card B
  /-- The distinguished subgroup `A ≤ B`. -/
  A : Subgroup B
  /-- `|A| = q`. -/
  A_card : Nat.card ↥A = q
  /-- The distinguished subgroup `R₀ ≤ R`. -/
  R₀ : Subgroup R
  /-- `|R₀| = p`. -/
  R₀_card : Nat.card ↥R₀ = p
  /-- The distinguished subgroup `R₁ ≤ R`. -/
  R₁ : Subgroup R
  /-- `R₁ ≠ 1`. -/
  R₁_ne_bot : R₁ ≠ ⊥
  /-- `R₁` is cyclic. -/
  R₁_cyclic : IsCyclic ↥R₁
  /-- `C_R(R₀) = R₀ R₁` (half of `C_R(R₀) = R₀ × R₁`). -/
  centralizer_eq : Subgroup.centralizer (R₀ : Set R) = R₀ ⊔ R₁
  /-- `R₀ ∩ R₁ = 1` (the other half of `C_R(R₀) = R₀ × R₁`;
  `R₁` centralizes `R₀` because `R₁ ≤ R₀ ⊔ R₁ = C_R(R₀)`). -/
  R₀_disjoint_R₁ : Disjoint R₀ R₁
  /-- `A` fixes `R₀` setwise. -/
  A_fixes_R₀ : ∀ a ∈ A, (act a) • R₀ = R₀
  /-- `A` acts regularly on `R`: `C_R(α) = 1` for every `α ∈ A^#`. -/
  A_regular : ∀ a ∈ A, a ≠ 1 → ∀ x : R, act a x = x → x = 1

variable {p q : ℕ}

/-- `R₀` is `A`-invariant in the repo's `IsAInvariant` sense. -/
theorem RegularOperatorSetup.isAInvariant_R₀ (hyp : RegularOperatorSetup R B p q) :
    IsAInvariant (hyp.act.comp hyp.A.subtype) hyp.R₀ :=
  fun a => hyp.A_fixes_R₀ a.val a.property

/-- **BG Theorem E.3(a)** (proved, sorry-free): `q` divides `(p - 1)/2`.

BG's Step 1: `A` acts regularly on `R`, hence regularly on `R₀`, which has order
`p`; so the induced map `A → Aut(R₀) ≅ C_{p-1}` is injective and `q ∣ p - 1`.
Since `p` and `q` are odd, `q ∣ (p-1)/2` (and in particular `p ≥ 2q + 1 ≥ 7`). -/
theorem RegularOperatorSetup.card_A_dvd_half_p_sub_one [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) : q ∣ (p - 1) / 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  -- The restricted action of `A` on `R₀`.
  set ψ : ↥hyp.A →* MulAut ↥hyp.R₀ :=
    OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hyp.isAInvariant_R₀ with hψ
  -- `R₀` is nontrivial, since `|R₀| = p ≥ 2`.
  have hR₀ne : hyp.R₀ ≠ ⊥ := by
    intro h
    have hc := hyp.R₀_card
    rw [h, Subgroup.card_bot] at hc
    have := hyp.p_prime.one_lt
    omega
  haveI hnt : Nontrivial ↥hyp.R₀ := (Subgroup.nontrivial_iff_ne_bot _).mpr hR₀ne
  -- `ψ` is injective: a nontrivial `a ∈ A` acting trivially on `R₀` would fix a
  -- nonidentity element of `R`, contradicting regularity.
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    by_contra hane
    obtain ⟨h, hh⟩ := exists_ne (1 : ↥hyp.R₀)
    have hfix : hyp.act a.val h.val = h.val := by
      have := congrArg (fun (f : MulAut ↥hyp.R₀) => (f h).val) ha
      simpa [hψ, OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom_apply_val] using this
    have hval : (h : R) = 1 :=
      hyp.A_regular a.val a.property (by simpa using hane) h.val hfix
    exact hh (Subtype.ext (by simpa using hval))
  -- `q = |A|` divides `|Aut R₀| = φ(p) = p - 1`.
  haveI : IsCyclic ↥hyp.R₀ := isCyclic_of_prime_card hyp.R₀_card
  have hdvd : q ∣ p - 1 := by
    have h1 : Nat.card ↥hyp.A ∣ Nat.card (MulAut ↥hyp.R₀) :=
      Subgroup.card_dvd_of_injective ψ hinj
    rwa [hyp.A_card, IsCyclic.card_mulAut ↥hyp.R₀, hyp.R₀_card,
      Nat.totient_prime hyp.p_prime] at h1
  -- `q` is odd and `p - 1` is even, so `q ∣ (p-1)/2`.
  obtain ⟨m, hm⟩ := hyp.p_odd
  have hhalf : p - 1 = 2 * m := by omega
  have hcop : Nat.Coprime q 2 := hyp.q_odd.coprime_two_right
  have : q ∣ m := hcop.dvd_of_dvd_mul_left (by rwa [hhalf] at hdvd)
  simpa [hhalf] using this

/-! ### The structure of `C_R(R₀) = R₀ × R₁`

BG's Step 2 opens with the single sentence *"Since `C_R(R₀) = R₀ × R₁` we have
`R₀ ∩ Z = 1`"* (`Z = Ω₁(Z(S))` for the maximal `A`-invariant subgroup `S` of exponent
`p`).  Unpacked, the argument is: `|R₀| = p` forces `R₀ ⊓ Z ∈ {1, R₀}`, and `R₀ ≤ Z`
would put `S` inside `C_R(R₀)`, whose `p`-rank is at most `2` — contradicting the
`r(S) ≥ 3` obtained just before.  The three lemmas below supply the rank bound. -/

/-- `R₀` centralizes `R₁`.

This is the symmetric half of the setup datum `C_R(R₀) = R₀ R₁`: every `y ∈ R₁` lies
in `R₀ ⊔ R₁ = C_R(R₀)`, hence commutes with every `x ∈ R₀`. -/
theorem RegularOperatorSetup.R₀_le_centralizer_R₁ (hyp : RegularOperatorSetup R B p q) :
    hyp.R₀ ≤ Subgroup.centralizer (hyp.R₁ : Set R) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyC : y ∈ Subgroup.centralizer (hyp.R₀ : Set R) := by
    rw [hyp.centralizer_eq]
    exact (le_sup_right : hyp.R₁ ≤ hyp.R₀ ⊔ hyp.R₁) hy
  exact (Subgroup.mem_centralizer_iff.mp hyC x hx).symm

/-- **`C_R(R₀) = R₀ × R₁` is abelian.**

`R₀` has order `p`, hence is cyclic, and `R₁` is cyclic by hypothesis; the two
centralize each other, so their join is abelian
(`Ch4.S15.isMulCommutative_sup_of_le_centralizer`). -/
theorem RegularOperatorSetup.isMulCommutative_centralizer_R₀
    (hyp : RegularOperatorSetup R B p q) :
    IsMulCommutative ↥(Subgroup.centralizer (hyp.R₀ : Set R)) := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  haveI : IsCyclic ↥hyp.R₀ := isCyclic_of_prime_card hyp.R₀_card
  haveI : IsCyclic ↥hyp.R₁ := hyp.R₁_cyclic
  rw [hyp.centralizer_eq]
  exact OddOrder.BG.Ch4.S15.isMulCommutative_sup_of_le_centralizer
    IsCyclic.isMulCommutative IsCyclic.isMulCommutative hyp.R₀_le_centralizer_R₁

/-- **`|C_R(R₀)| = p · |R₁|`**, the cardinality form of the direct decomposition
`C_R(R₀) = R₀ × R₁`.

`R₀` normalizes `R₁` (it centralizes it), so the join is the set product
`↑R₀ * ↑R₁` (`Subgroup.coe_mul_of_left_le_normalizer_right`); the classical product
formula and `R₀ ∩ R₁ = 1` then give `|R₀ R₁| = |R₀| · |R₁| = p · |R₁|`. -/
theorem RegularOperatorSetup.card_centralizer_R₀ [Finite R]
    (hyp : RegularOperatorSetup R B p q) :
    Nat.card ↥(Subgroup.centralizer (hyp.R₀ : Set R)) = p * Nat.card ↥hyp.R₁ := by
  have hnorm : hyp.R₀ ≤ Subgroup.normalizer (hyp.R₁ : Set R) :=
    hyp.R₀_le_centralizer_R₁.trans (Subgroup.centralizer_le_normalizer _)
  have hcoe : (↑(hyp.R₀ ⊔ hyp.R₁) : Set R) = (hyp.R₀ : Set R) * (hyp.R₁ : Set R) :=
    Subgroup.coe_mul_of_left_le_normalizer_right hyp.R₀ hyp.R₁ hnorm
  have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card hyp.R₀ hyp.R₁
  have hinf : Nat.card ↥(hyp.R₀ ⊓ hyp.R₁) = 1 := by
    rw [disjoint_iff.mp hyp.R₀_disjoint_R₁]
    exact Subgroup.card_bot
  rw [hinf, mul_one, hyp.R₀_card] at hprod
  rw [hyp.centralizer_eq]
  exact (Nat.card_congr (Equiv.setCongr hcoe)).trans hprod

/-- **`r(C_R(R₀)) ≤ 2`.**

`C_R(R₀) = R₀ × R₁` contains the cyclic subgroup `R₁` with index `p`
(`card_centralizer_R₀`), so `pRank_le_two_of_isCyclic_of_index_le_prime` applies.

This is the rank bound behind BG's elided *"Since `C_R(R₀) = R₀ × R₁` we have
`R₀ ∩ Z = 1`"* in the proof of Theorem E.3(b). -/
theorem RegularOperatorSetup.pRank_centralizer_R₀_le_two [Finite R]
    (hyp : RegularOperatorSetup R B p q) :
    pRank ↥(Subgroup.centralizer (hyp.R₀ : Set R)) p ≤ 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  have hR₁le : hyp.R₁ ≤ Subgroup.centralizer (hyp.R₀ : Set R) := by
    rw [hyp.centralizer_eq]
    exact le_sup_right
  set K : Subgroup ↥(Subgroup.centralizer (hyp.R₀ : Set R)) :=
    hyp.R₁.subgroupOf (Subgroup.centralizer (hyp.R₀ : Set R)) with hKdef
  have hKcyc : IsCyclic ↥K :=
    (Subgroup.subgroupOfEquivOfLe hR₁le).isCyclic.mpr hyp.R₁_cyclic
  have hKcard : Nat.card ↥K = Nat.card ↥hyp.R₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₁le).toEquiv
  have hidx : K.index ≤ p := by
    have hmul := K.card_mul_index
    rw [hKcard, hyp.card_centralizer_R₀, mul_comm p] at hmul
    exact le_of_eq (Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul)
  exact pRank_le_two_of_isCyclic_of_index_le_prime hKcyc hidx

/-- **BG Theorem E.3(b), Step 2, (E.1)--(E.3)**: an exponent-`p` subgroup `S ≤ R` with
`p³ < |S|` has `r(S) ≥ 3`.

BG argues via `V ∈ SCN(S)`: `|S/V|` divides `|Aut V|` and `V` is elementary abelian
(as `exp S = p`), so `|V| ≤ p²` would force `|S/V| ≤ p` and `|S| ≤ p³`.  The repo already
records the conclusion of that argument as
`Ch1.S04.card_le_prime_cube_of_pRank_le_two_of_exponent_prime` (`r ≤ 2` and `exp = p` imply
`|·| ≤ p³`), so BG's (E.1)--(E.3) is exactly its contrapositive. -/
theorem three_le_pRank_of_prime_cube_lt_card {S : Type*} [Group S] [Finite S] {p : ℕ}
    [Fact p.Prime] (hS : IsPGroup p S) (hexp : ∀ x : S, x ^ p = 1)
    (hcard : p ^ 3 < Nat.card S) :
    3 ≤ pRank S p := by
  by_contra h
  exact absurd (OddOrder.BG.Ch1.S04.card_le_prime_cube_of_pRank_le_two_of_exponent_prime
    hS (by omega) hexp) (by omega)

/-- **BG Theorem E.3(b), Step 2**: a subgroup `S ≤ R` of `p`-rank at least `3` cannot
centralize `R₀`.

Otherwise `S ≤ C_R(R₀)`, whose `p`-rank is at most `2` (`pRank_centralizer_R₀_le_two`). -/
theorem RegularOperatorSetup.not_le_centralizer_R₀_of_three_le_pRank [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hS : 3 ≤ pRank ↥S p) :
    ¬ S ≤ Subgroup.centralizer (hyp.R₀ : Set R) := by
  intro hle
  have hmono : pRank ↥S p ≤ pRank ↥(Subgroup.centralizer (hyp.R₀ : Set R)) p :=
    pRank_le_of_injective (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have := hyp.pRank_centralizer_R₀_le_two
  omega

/-- **BG Theorem E.3(b), Step 2**: *"Since `C_R(R₀) = R₀ × R₁` we have `R₀ ∩ Z = 1`."*

BG states this in one line.  Unpacked: `Z` is central in `S` and `|R₀| = p` is prime, so
`R₀ ⊓ Z` is either `1` or all of `R₀`; in the latter case `R₀` would be central in `S`,
putting `S` inside `C_R(R₀)` and contradicting `r(S) ≥ 3`
(`not_le_centralizer_R₀_of_three_le_pRank`).

The hypothesis `hcent : S ≤ C_R(Z)` is the ambient spelling of `Z ≤ Z(S)`, which is how
BG's `Z = Ω₁(Z(S))` enters. -/
theorem RegularOperatorSetup.inf_eq_bot_of_three_le_pRank [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S Z : Subgroup R}
    (hcent : S ≤ Subgroup.centralizer (Z : Set R)) (hS : 3 ≤ pRank ↥S p) :
    hyp.R₀ ⊓ Z = ⊥ := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  -- `|R₀ ⊓ Z|` divides `|R₀| = p`, so it is `1` or `p`.
  have hdvd : Nat.card ↥(hyp.R₀ ⊓ Z) ∣ p := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : hyp.R₀ ⊓ Z ≤ hyp.R₀)
    rwa [hyp.R₀_card] at h
  rcases (Nat.dvd_prime hyp.p_prime).mp hdvd with h1 | hp
  · exact Subgroup.card_eq_one.mp h1
  · -- `R₀ ⊓ Z = R₀`, i.e. `R₀ ≤ Z`; then `S ≤ C_R(Z) ≤ C_R(R₀)`.
    exfalso
    have heq : hyp.R₀ ⊓ Z = hyp.R₀ :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : hyp.R₀ ⊓ Z ≤ hyp.R₀)
        (le_of_eq (hyp.R₀_card.trans hp.symm))
    have hR₀Z : hyp.R₀ ≤ Z := le_trans (le_of_eq heq.symm) inf_le_right
    exact hyp.not_le_centralizer_R₀_of_three_le_pRank hS
      (hcent.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hR₀Z)))

/-- `R₀` viewed inside a subgroup `S` containing it still has order `p`. -/
theorem RegularOperatorSetup.card_R₀_subgroupOf [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S) :
    Nat.card ↥(hyp.R₀.subgroupOf S) = p := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀S).toEquiv]
  exact hyp.R₀_card

/-- **BG's `v ∈ R₀^#`**: a generator of `R₀`, viewed inside `S`.

`R₀` has prime order `p`, so any nonidentity element generates it.  BG picks such a `v` at
the start of `(E.9)` and keeps it for the whole of Step 2; several results below take
`Subgroup.zpowers v = R₀.subgroupOf S` as a hypothesis, and this is what supplies it. -/
theorem RegularOperatorSetup.exists_zpowers_eq_R₀_subgroupOf [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S) :
    ∃ v : ↥S, Subgroup.zpowers v = hyp.R₀.subgroupOf S := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set R₀' : Subgroup ↥S := hyp.R₀.subgroupOf S with hR₀'def
  have hR₀'card : Nat.card ↥R₀' = p := hyp.card_R₀_subgroupOf hR₀S
  haveI : Nontrivial ↥R₀' := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro h
    rw [h, Subgroup.card_bot] at hR₀'card
    exact hyp.p_prime.one_lt.ne hR₀'card
  obtain ⟨v, hv⟩ := exists_ne (1 : ↥R₀')
  have hord : orderOf (v : ↥S) = p := by
    have h1 : orderOf v ∣ Nat.card ↥R₀' := orderOf_dvd_natCard v
    rw [hR₀'card] at h1
    have h2 : orderOf (v : ↥S) = orderOf v := Subgroup.orderOf_coe v
    rcases (Nat.dvd_prime hyp.p_prime).mp h1 with h | h
    · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp (h2.trans h))) hv
    · exact h2.trans h
  exact ⟨(v : ↥S), Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr v.2)
    (by rw [hR₀'card, Nat.card_zpowers, hord])⟩

/-- `r(C_S(R₀)) ≤ 2` for any `S` containing `R₀`: the centralizer taken inside `S` embeds in
`C_R(R₀)` along `S.subtype`, and that has rank `≤ 2` (`pRank_centralizer_R₀_le_two`).

BG obtains this from the sharper `|C_S(R₀)| = p²` of (E.4); the rank bound alone is what
Corollary 5.4 and Theorem 5.3(d) actually consume, and it needs no exponent hypothesis. -/
theorem RegularOperatorSetup.pRank_centralizer_subgroupOf_le_two [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S) :
    pRank ↥(Subgroup.centralizer ((hyp.R₀.subgroupOf S : Subgroup ↥S) : Set ↥S)) p ≤ 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set C : Subgroup ↥S :=
    Subgroup.centralizer ((hyp.R₀.subgroupOf S : Subgroup ↥S) : Set ↥S) with hCdef
  have hmem : ∀ x : ↥C, ((x : ↥S) : R) ∈ Subgroup.centralizer (hyp.R₀ : Set R) := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hcomm := Subgroup.mem_centralizer_iff.mp x.2 ⟨h, hR₀S hh⟩
      (by simpa [Subgroup.mem_subgroupOf] using hh)
    exact congrArg (fun y : ↥S => (y : R)) hcomm
  have hcomp : Function.Injective ((S.subtype).comp C.subtype) :=
    S.subtype_injective.comp C.subtype_injective
  have hfinj : Function.Injective
      (((S.subtype).comp C.subtype).codRestrict _ hmem) := fun a b hab =>
    hcomp (congrArg (fun y : ↥(Subgroup.centralizer (hyp.R₀ : Set R)) => (y : R)) hab)
  exact (pRank_le_of_injective hfinj).trans hyp.pRank_centralizer_R₀_le_two

/-- **BG Theorem E.3(b), Step 2**: *"Note that `S` is narrow."*

`R₀`, of order `p`, is a witness for Corollary 5.4
(`Ch1.S05.narrow_iff_exists_card_prime_centralizer_pRank_le_two`). -/
theorem RegularOperatorSetup.isNarrow_of_three_le_pRank [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hS : 3 ≤ pRank ↥S p) :
    IsNarrow p ↥S := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  exact (OddOrder.BG.Ch1.S05.narrow_iff_exists_card_prime_centralizer_pRank_le_two
    hyp.p_odd (hyp.R_pGroup.to_subgroup S) hS).mpr
    ⟨hyp.R₀.subgroupOf S, hyp.card_R₀_subgroupOf hR₀S,
      hyp.pRank_centralizer_subgroupOf_le_two hR₀S⟩

/-- **BG Theorem E.3(b), Step 2, first conclusion of (E.13)**: `R₀ ⊄ S'`.

BG derives this from `S = R₀T` with `S' ≤ T` and `R₀ ∩ T = 1` (E.5); in the repo the same
content is packaged as Theorem 5.3(d) (`Ch1.S05.narrow_centralizer_decomp`), whose second
clause is exactly `R₀ ∩ S' = 1` for a narrow `S`.  Since `|R₀| = p ≠ 1`, that forces
`R₀ ⊄ S'`. -/
theorem RegularOperatorSetup.not_le_derivedInG_of_three_le_pRank [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hS : 3 ≤ pRank ↥S p) :
    ¬ hyp.R₀ ≤ derivedInG S := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  intro hle
  -- Theorem 5.3(d) applied inside `↥S` with the order-`p` subgroup `R₀`.
  have hdecomp := OddOrder.BG.Ch1.S05.narrow_centralizer_decomp
    hyp.p_odd (hyp.R_pGroup.to_subgroup S) hS (hyp.isNarrow_of_three_le_pRank hR₀S hS)
    (hyp.R₀.subgroupOf S) (hyp.card_R₀_subgroupOf hR₀S)
    (hyp.pRank_centralizer_subgroupOf_le_two hR₀S)
  -- `R₀ ≤ S'` transports to `R₀.subgroupOf S ≤ commutator ↥S`, contradicting `⊓ = ⊥`.
  have hsub : hyp.R₀.subgroupOf S ≤ _root_.commutator ↥S := by
    intro x hx
    have hxR₀ : (x : R) ∈ hyp.R₀ := hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hle hxR₀)
    exact (Subtype.ext hyx.symm : x = y) ▸ hy
  have hbot : hyp.R₀.subgroupOf S = ⊥ :=
    le_bot_iff.mp (hdecomp.2.1 ▸ le_inf le_rfl hsub)
  have hcard := hyp.card_R₀_subgroupOf hR₀S
  rw [hbot, Subgroup.card_bot] at hcard
  exact hyp.p_prime.one_lt.ne hcard

/-- **BG Theorem E.3(b), Step 2, (E.4) and the first half of (E.5)**.

Applying Lemma 5.2 (`Ch1.S05.lemma52`) inside the narrow group `S`, with `Z = Ω₁(Z(S))`
and `T = C_S(Ω₁(Z₂(S)))`:

* `|Z| = p` — BG's (E.4) (BG gets it from `R₀ × Z ⊆ C_S(R₀) ⊆ R₀ × Ω₁(R₁)`);
* `|S : T| = p` — the index clause of BG's (E.5).

The maximal elementary abelian subgroup of order `p²` that Lemma 5.2 consumes is supplied by
narrowness itself (`narrow_iff_exists_maximalElementaryAbelian_card_prime_sq`), so BG's
explicit witness `E = C_S(R₀)` — and with it the computation `|C_S(R₀)| = p²` — is not
needed on this route. -/
theorem RegularOperatorSetup.card_omega1Center_and_index_centralizer [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hS : 3 ≤ pRank ↥S p) :
    Nat.card ↥(OddOrder.BG.Ch1.S05.omega1Center ↥S p) = p ∧
      (Subgroup.centralizer
        (omega1UpperCentralTwo ↥S p : Set ↥S)).index = p := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  obtain ⟨E, hEcard, hEstar⟩ :=
    (OddOrder.BG.Ch1.S05.narrow_iff_exists_maximalElementaryAbelian_card_prime_sq
      hyp.p_odd (hyp.R_pGroup.to_subgroup S) hS).mp
      (hyp.isNarrow_of_three_le_pRank hR₀S hS)
  have h := OddOrder.BG.Ch1.S05.lemma52
    hyp.p_odd (hyp.R_pGroup.to_subgroup S) hS E hEcard hEstar
  exact ⟨h.2.1.1, h.2.2⟩

/-- **BG Theorem E.3(b), Step 2, (E.4)**: `C_S(R₀) = R₀ × Ω₁(Z(S))`, of order `p²`.

BG sandwiches `R₀ × Z ⊆ C_S(R₀) ⊆ R₀ × Ω₁(R₁)` and reads off both `|Z| = p` and the
decomposition.  Here `|Z| = p` is already in hand from Lemma 5.2
(`card_omega1Center_and_index_centralizer`), and the upper bound comes more cheaply than
BG's: `C_S(R₀)` is elementary abelian — abelian because it sits in the abelian `C_R(R₀)`,
of exponent `p` by hypothesis on `S` — and `r(C_R(R₀)) ≤ 2`, so `|C_S(R₀)| ≤ p²`.  The
lower bound `R₀ × Z` already has order `p²` (`R₀ ∩ Z = 1` by
`inf_eq_bot_of_three_le_pRank`), so the two meet.  `Ω₁(R₁)` never enters. -/
theorem RegularOperatorSetup.centralizer_inf_eq_sup_omega1Center [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) :
    S ⊓ Subgroup.centralizer (hyp.R₀ : Set R)
        = hyp.R₀ ⊔ (OddOrder.BG.Ch1.S05.omega1Center ↥S p).map S.subtype ∧
      Nat.card ↥(S ⊓ Subgroup.centralizer (hyp.R₀ : Set R)) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  haveI : IsCyclic ↥hyp.R₀ := isCyclic_of_prime_card hyp.R₀_card
  set C : Subgroup R := Subgroup.centralizer (hyp.R₀ : Set R) with hCdef
  set Z : Subgroup R := (OddOrder.BG.Ch1.S05.omega1Center ↥S p).map S.subtype with hZdef
  -- `|Z| = p` (Lemma 5.2) and `Z ≤ S`, `Z` central in `S`.
  have hZcard : Nat.card ↥Z = p := by
    rw [hZdef, Subgroup.card_map_of_injective S.subtype_injective]
    exact (hyp.card_omega1Center_and_index_centralizer hR₀S hS).1
  have hZS : Z ≤ S := by
    rw [hZdef]
    rintro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hSZ : S ≤ Subgroup.centralizer (Z : Set R) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [hZdef] at hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    have hc := Subgroup.mem_center_iff.mp
      (OddOrder.BG.Ch1.S05.omega1Center_le_center hy) ⟨x, hx⟩
    simpa using (congrArg (fun z : ↥S => (z : R)) hc).symm
  -- `R₀ ∩ Z = 1`, so `|R₀ Z| = p²`.
  have hinf : hyp.R₀ ⊓ Z = ⊥ := hyp.inf_eq_bot_of_three_le_pRank hSZ hS
  have hR₀Z : hyp.R₀ ≤ Subgroup.centralizer (Z : Set R) := hR₀S.trans hSZ
  have hsupcard : Nat.card ↥(hyp.R₀ ⊔ Z) = p ^ 2 := by
    have hcoe : (↑(hyp.R₀ ⊔ Z) : Set R) = (hyp.R₀ : Set R) * (Z : Set R) :=
      Subgroup.coe_mul_of_left_le_normalizer_right hyp.R₀ Z
        (hR₀Z.trans (Subgroup.centralizer_le_normalizer _))
    have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card hyp.R₀ Z
    rw [hinf, Subgroup.card_bot, mul_one, hyp.R₀_card, hZcard] at hprod
    have hcong : Nat.card ↥(hyp.R₀ ⊔ Z) = Nat.card ↥((hyp.R₀ : Set R) * (Z : Set R)) :=
      Nat.card_congr (Equiv.setCongr hcoe)
    rw [hcong, hprod]; ring
  -- `R₀ Z ≤ C_S(R₀)`.
  have hle : hyp.R₀ ⊔ Z ≤ S ⊓ C := by
    refine sup_le (le_inf hR₀S ?_) (le_inf hZS ?_)
    · rw [hCdef]
      exact Subgroup.le_centralizer_iff_isMulCommutative.mpr IsCyclic.isMulCommutative
    · rw [hCdef, ← Subgroup.le_centralizer_iff]
      exact hR₀S.trans hSZ
  -- `C_S(R₀)` is elementary abelian inside `C_R(R₀)`, whose `p`-rank is `≤ 2`.
  have hEA : ((S ⊓ C).subgroupOf C).IsElementaryAbelian p := by
    refine ⟨fun x y => Subtype.ext ?_, fun x => Subtype.ext ?_⟩
    · exact hyp.isMulCommutative_centralizer_R₀.is_comm.comm (x : ↥C) (y : ↥C)
    · have hxS : ((x : ↥C) : R) ∈ S := (Subgroup.mem_subgroupOf.mp x.2).1
      have hp1 := congrArg (fun z : ↥S => (z : R)) (hexp ⟨((x : ↥C) : R), hxS⟩)
      exact Subtype.ext (by simpa using hp1)
  have hEcard : Nat.card ↥(S ⊓ C) ≤ p ^ 2 := by
    obtain ⟨k, hk⟩ := (hyp.R_pGroup.to_subgroup (S ⊓ C)).exists_card_eq
    have hlog := le_pRank ((S ⊓ C).subgroupOf C) hEA
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : S ⊓ C ≤ C)).toEquiv,
      hk, Nat.log_pow hyp.p_prime.one_lt] at hlog
    have h2 : pRank ↥C p ≤ 2 := hyp.pRank_centralizer_R₀_le_two
    rw [hk]
    exact Nat.pow_le_pow_right hyp.p_prime.pos (by omega)
  have heq : hyp.R₀ ⊔ Z = S ⊓ C :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hsupcard]; exact hEcard)
  exact ⟨heq.symm, by rw [← heq, hsupcard]⟩

/-- The centralizer of `R₀` computed inside `↥S` is the `subgroupOf` of the ambient
`S ⊓ C_R(R₀)`: an `x ∈ S` centralizes `R₀ ∩ S = R₀` iff `↑x` centralizes `R₀`. -/
theorem RegularOperatorSetup.centralizer_subgroupOf_eq
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S) :
    Subgroup.centralizer ((hyp.R₀.subgroupOf S : Subgroup ↥S) : Set ↥S)
      = (S ⊓ Subgroup.centralizer (hyp.R₀ : Set R)).subgroupOf S := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · refine fun h => ⟨x.2, fun g hg => ?_⟩
    exact congrArg (fun y : ↥S => (y : R))
      (h ⟨g, hR₀S hg⟩ (by simpa [Subgroup.mem_subgroupOf] using hg))
  · rintro ⟨-, h⟩ g hg
    exact Subtype.ext (h (g : R) (by simpa [Subgroup.mem_subgroupOf] using hg))

/-- **BG Theorem E.3(b), Step 2, (E.5)**: `|C_T(R₀)| = p`, where `T = C_S(Ω₁(Z₂(S)))`.

Theorem 5.3(d) (`Ch1.S05.narrow_centralizer_decomp`) gives the internal direct
decomposition `C_S(R₀) = R₀ × C_T(R₀)`; with `|C_S(R₀)| = p²` from (E.4) and `|R₀| = p`,
the cyclic factor `C_T(R₀)` has order `p`.

Together with `|S : T| = p` (`card_omega1Center_and_index_centralizer`) this is BG's
`|S : T| = |C_T(R₀)| = p`. -/
theorem RegularOperatorSetup.card_centralizer_inf_centralizer_eq [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) :
    Nat.card ↥(Subgroup.centralizer ((hyp.R₀.subgroupOf S : Subgroup ↥S) : Set ↥S) ⊓
      Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) = p := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set R₀' : Subgroup ↥S := hyp.R₀.subgroupOf S with hR₀'
  set CS : Subgroup ↥S := Subgroup.centralizer ((R₀' : Subgroup ↥S) : Set ↥S) with hCS
  set T : Subgroup ↥S :=
    Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hT
  obtain ⟨-, -, hR₀T, hdecomp⟩ := OddOrder.BG.Ch1.S05.narrow_centralizer_decomp
    hyp.p_odd (hyp.R_pGroup.to_subgroup S) hS (hyp.isNarrow_of_three_le_pRank hR₀S hS)
    R₀' (hyp.card_R₀_subgroupOf hR₀S) (hyp.pRank_centralizer_subgroupOf_le_two hR₀S)
  -- `|C_S(R₀)| = p²` via (E.4), transported into `↥S`.
  have hCScard : Nat.card ↥CS = p ^ 2 := by
    rw [hCS, hR₀', hyp.centralizer_subgroupOf_eq hR₀S,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
        S ⊓ Subgroup.centralizer (hyp.R₀ : Set R) ≤ S)).toEquiv]
    exact (hyp.centralizer_inf_eq_sup_omega1Center hR₀S hexp hS).2
  -- `C_S(R₀) = R₀ × (C_S(R₀) ⊓ T)` with `R₀ ⊓ T = ⊥`, so `p² = p · |C_T(R₀)|`.
  have hnorm : R₀' ≤ Subgroup.normalizer ((CS ⊓ T : Subgroup ↥S) : Set ↥S) :=
    (Subgroup.le_centralizer_iff.mpr (inf_le_left.trans (le_of_eq hCS))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcoe : (↑(R₀' ⊔ (CS ⊓ T)) : Set ↥S) = (R₀' : Set ↥S) * ((CS ⊓ T : Subgroup ↥S) : Set ↥S) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
  have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card R₀' (CS ⊓ T)
  have hinfbot : R₀' ⊓ (CS ⊓ T) = ⊥ :=
    le_bot_iff.mp ((le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans (le_of_eq hR₀T))
  rw [hinfbot, Subgroup.card_bot, mul_one, hyp.card_R₀_subgroupOf hR₀S] at hprod
  have hcong : Nat.card ↥(R₀' ⊔ (CS ⊓ T)) =
      Nat.card ↥((R₀' : Set ↥S) * ((CS ⊓ T : Subgroup ↥S) : Set ↥S)) :=
    Nat.card_congr (Equiv.setCongr hcoe)
  rw [← hdecomp, hCScard, hprod] at hcong
  have hmul : p * p = p * Nat.card ↥(CS ⊓ T) := by rw [← sq]; exact hcong
  exact (Nat.eq_of_mul_eq_mul_left hyp.p_prime.pos hmul).symm

/-- **BG Theorem E.3(b), Step 2, the (E.6) counting step**: `|H| ≤ |⁅R₀, H⁆| · p` for any
`H ≤ T`.

This is BG's *"a short argument using the mapping `H → [R, H]` given by `x ↦ [v,x]`"*: for a
generator `v` of `R₀` that map is constant exactly on the cosets of `C_H(v)`, so
`|H : C_H(v)| ≤ |⁅R₀, H⁆|`; and `C_H(v) ≤ C_T(R₀)`, of order `p` by (E.5).

The counting itself is `Ch1.S05.card_le_card_mul_of_commutator_mem_of_card_centralizer_le`
— the same lemma that drives Theorem 5.5's own `H_i` chain, which is why BG can say
"follow the part of the proof of Theorem 5.5 that comes after (5.5)". -/
theorem RegularOperatorSetup.card_le_card_commutator_mul_prime [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {H : Subgroup ↥S}
    (hHT : H ≤ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) :
    Nat.card ↥H ≤ Nat.card ↥⁅hyp.R₀.subgroupOf S, H⁆ * p := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set R₀' : Subgroup ↥S := hyp.R₀.subgroupOf S with hR₀'def
  have hR₀'card : Nat.card ↥R₀' = p := hyp.card_R₀_subgroupOf hR₀S
  -- pick a generator `v` of the order-`p` group `R₀`
  obtain ⟨w, hzp⟩ := hyp.exists_zpowers_eq_R₀_subgroupOf hR₀S
  rw [← hR₀'def] at hzp
  have hvR₀ : (w : ↥S) ∈ R₀' := by rw [← hzp]; exact Subgroup.mem_zpowers w
  refine OddOrder.BG.Ch1.S05.card_le_card_mul_of_commutator_mem_of_card_centralizer_le
    (v := (w : ↥S)) (fun x hx => Subgroup.commutator_mem_commutator hvR₀ hx) ?_
  -- `C_H(v) ≤ C_T(R₀)`, which has order `p`.
  have hsub : Subgroup.centralizer ({(w : ↥S)} : Set ↥S) ⊓ H ≤
      Subgroup.centralizer ((R₀' : Subgroup ↥S) : Set ↥S) ⊓
        Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) := by
    refine inf_le_inf ?_ hHT
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [← hzp] at hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hc : Commute (w : ↥S) x := Subgroup.mem_centralizer_iff.mp hx (w : ↥S) rfl
    exact hc.zpow_left k
  calc Nat.card ↥(Subgroup.centralizer ({(w : ↥S)} : Set ↥S) ⊓ H)
      ≤ Nat.card ↥(Subgroup.centralizer ((R₀' : Subgroup ↥S) : Set ↥S) ⊓
          Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) :=
        Nat.card_le_card_of_injective (Subgroup.inclusion hsub)
          (Subgroup.inclusion_injective hsub)
    _ = p := hyp.card_centralizer_inf_centralizer_eq hR₀S hexp hS

/-- **BG Lemma 4.2(a), both slots at once**: if `⁅x, y⁆` is central then
`⁅x ^ m, y ^ n⁆ = ⁅x, y⁆ ^ (m * n)`.

The repo has the two single-slot forms
(`Ch1.S04.commutatorElement_pow_{left,right}_of_central`); this is the bilinear
combination, which is what BG's (E.12) actually applies.  Note the right slot is applied to
`⁅x^m, y⁆`, central because it *equals* `⁅x,y⁆^m`.

BG uses it inside `S/Hᵢ₊₁` — where `H̄ᵢ` is central, so commutators into `H̄ᵢ` are central —
to compute `[wᵢ₋₁^{rᵢ₋₁} u, vʳ] = wᵢ^{rᵢ₋₁ r}`, giving `rᵢ ≡ rᵢ₋₁ r (mod p)`. -/
theorem commutatorElement_pow_pow_of_central {K : Type*} [Group K] {x y : K}
    (hz : ⁅x, y⁆ ∈ Subgroup.center K) (m n : ℕ) :
    ⁅x ^ m, y ^ n⁆ = ⁅x, y⁆ ^ (m * n) := by
  have h1 : ⁅x ^ m, y⁆ = ⁅x, y⁆ ^ m :=
    OddOrder.BG.Ch1.S04.commutatorElement_pow_left_of_central hz m
  have hc : ⁅x ^ m, y⁆ ∈ Subgroup.center K := by
    rw [h1]; exact Subgroup.pow_mem _ hz m
  rw [OddOrder.BG.Ch1.S04.commutatorElement_pow_right_of_central hc n, h1, ← pow_mul]

/-- **BG Theorem E.3(b), Step 2: the arithmetic core of (E.10)--(E.12)**.

In a finite **cyclic** group: if `u ≠ 1` satisfies `u^q = 1` for a prime `q`, if `u₀`
satisfies `u₀^q = 1`, and if `u₀ uⁱ ≠ 1` for every `i < n`, then `n ≤ q − 1`.

This is BG's closing count — *"the nonzero integers (mod p) form a cyclic group of order
`p−1` and `r^q ≡ 1`… therefore `q − 1 ≥ j + n − 1 ≥ n`"*.  `u` has order exactly `q`;
cyclicity is what puts `u₀` inside `⟨u⟩`, so `u₀ = uʲ` with `1 ≤ j ≤ q−1`; then
`u₀ uⁱ = u^{j+i}` avoiding `1` forces the interval `[j, j+n−1]` to miss `q`.

Stated for an abstract cyclic group rather than `(ZMod p)ˣ`: nothing here is about `ZMod`,
and the consumer supplies cyclicity of the unit group. -/
theorem le_pred_of_forall_mul_pow_ne_one {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {q n : ℕ} (hq : q.Prime) {u u₀ : C} (hu : u ^ q = 1) (hune : u ≠ 1) (hu₀ : u₀ ^ q = 1)
    (hne : ∀ i < n, u₀ * u ^ i ≠ 1) : n ≤ q - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · omega
  -- `u` has order exactly `q`
  have hordu : orderOf u = q := by
    rcases (Nat.dvd_prime hq).mp (orderOf_dvd_of_pow_eq_one hu) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hune
    · exact h
  -- cyclicity puts `u₀` in `⟨u⟩`
  have hmem : u₀ ∈ Subgroup.zpowers u := by
    rcases (Nat.dvd_prime hq).mp (orderOf_dvd_of_pow_eq_one hu₀) with h | h
    · rw [orderOf_eq_one_iff.mp h]; exact Subgroup.one_mem _
    · have hcard : Nat.card ↥(Subgroup.zpowers u₀) = Nat.card ↥(Subgroup.zpowers u) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, h, hordu]
      exact OddOrder.GroupTheory.cyclic_subgroup_eq_of_card_eq hcard ▸
        Subgroup.mem_zpowers u₀
  obtain ⟨j, hj⟩ : ∃ j : ℕ, u ^ j = u₀ :=
    (Submonoid.mem_powers_iff u₀ u).mp (mem_powers_iff_mem_zpowers.mpr hmem)
  -- reduce the exponent below `q`
  set j' := j % q with hj'def
  have hj'lt : j' < q := Nat.mod_lt _ hq.pos
  have hj' : u ^ j' = u₀ := by rw [hj'def, ← hordu, pow_mod_orderOf, hj]
  have hj'pos : 0 < j' := by
    rcases Nat.eq_zero_or_pos j' with h | h
    · exact absurd (by simpa [h] using hj'.symm) (by simpa using hne 0 hnpos)
    · exact h
  -- `u₀ uⁱ = u^{j'+i} ≠ 1` says `q ∤ j' + i`
  by_contra hlt
  push Not at hlt
  have hqn : q ≤ n := by omega
  have hi : q - j' < n := by omega
  refine hne (q - j') hi ?_
  rw [← hj', ← pow_add]
  have : j' + (q - j') = q := by omega
  rw [this, hu]


end RegularOperator

end OddOrder.BG.AppE
