/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.Basic
import OddOrder.Peterfalvi.Appendices.Suzuki.SylowTwo
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionNonSimple
import OddOrder.Peterfalvi.Appendices.FeitSibleyMain

/-!
# Peterfalvi Part II, Ch. III: the Feit–Sibley configuration

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III, §1, p. 115.

The proof of Theorem C observes, once `D` acts fixed-point-freely on `Q₁`
(`StructureOfH/Basic.lean`) and `Q` has trivial intersections in `G`, that
"the hypotheses of the Feit–Sibley Theorem, stated in Appendix IV, are
therefore satisfied".

This leaf supplies the remaining inputs of `FeitSibley.Hypothesis`:

* the conjugation action of `D` on the odd part `Q₁` (`conjQ1ByD`), which is
  Frobenius by Theorem C's step 1 and hence forces `(|Q₁|, |D|) = 1`;
* the ambient Sylow `2`-subgroup `S ≤ Q` of the book's `Q = S × Q₁`, together
  with the direct-product bookkeeping;
* `(|Q|, |D|) = 1`: an odd prime dividing `|Q|` divides the odd part `|Q₁|`,
  and `|D|` is odd, so the `2`-part is excluded as well.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.Isaacs.Ch06 (IsFrobeniusAction)

universe uG uΩ

namespace Hypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## The conjugation action of `D` on `Q₁` -/

/-- Conjugation by `D` on the odd part `Q₁` (`D ≤ H ≤ N_G(Q₁)`). -/
def conjQ1ByD : ↥hyp.D →* MulAut ↥hyp.Q1 where
  toFun k :=
    { toFun := fun x => ⟨(k : G) * x * (k : G)⁻¹,
        hyp.conj_mem_Q1_of_mem_H (hyp.D_le_H k.2) x.2⟩
      invFun := fun x => ⟨(k : G)⁻¹ * x * (k : G), by
        simpa using hyp.conj_mem_Q1_of_mem_H (inv_mem (hyp.D_le_H k.2)) x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by
        change (k : G) * ((x : G) * (y : G)) * (k : G)⁻¹ =
          ((k : G) * x * (k : G)⁻¹) * ((k : G) * y * (k : G)⁻¹)
        group) }
  map_one' := by
    ext x
    change ((1 : ↥hyp.D) : G) * (x : G) * ((1 : ↥hyp.D) : G)⁻¹ = (x : G)
    simp
  map_mul' k l := by
    ext x
    change (((k : G) * (l : G)) * (x : G) * (((k : G) * (l : G))⁻¹)) =
      (k : G) * ((l : G) * (x : G) * (l : G)⁻¹) * (k : G)⁻¹
    group

@[simp] lemma conjQ1ByD_apply_val (k : ↥hyp.D) (x : ↥hyp.Q1) :
    ((hyp.conjQ1ByD k x : ↥hyp.Q1) : G) = (k : G) * (x : G) * (k : G)⁻¹ := rfl

/-! ## The ambient Sylow `2`-subgroup `S` of `Q` -/

/-- The book's `S`: a Sylow `2`-subgroup of `Q`, as a subgroup of `G`.  Since `Q`
is nilpotent its Sylow `2`-subgroup is unique, so the choice is canonical. -/
noncomputable def sylowTwoOfQ : Subgroup G :=
  ((default : Sylow 2 ↥hyp.Q) : Subgroup ↥hyp.Q).map hyp.Q.subtype

lemma sylowTwoOfQ_le_Q : hyp.sylowTwoOfQ ≤ hyp.Q := by
  rintro x ⟨s, _, rfl⟩
  exact s.2

lemma card_sylowTwoOfQ :
    Nat.card ↥hyp.sylowTwoOfQ =
      Nat.card ↥((default : Sylow 2 ↥hyp.Q) : Subgroup ↥hyp.Q) :=
  (Nat.card_congr
    (Subgroup.equivMapOfInjective _ hyp.Q.subtype hyp.Q.subtype_injective).toEquiv).symm

/-- `|S| · |Q₁| = |Q|`: the book's internal direct decomposition `Q = S × Q₁`. -/
theorem card_sylowTwoOfQ_mul_card_Q1 :
    Nat.card ↥hyp.sylowTwoOfQ * Nat.card ↥hyp.Q1 = Nat.card ↥hyp.Q := by
  have h := Nat.card_congr
    (hyp.sylowTwoProdQ1MulEquiv (default : Sylow 2 ↥hyp.Q)).toEquiv
  rw [Nat.card_prod] at h
  rw [hyp.card_sylowTwoOfQ, hyp.card_Q1]
  exact h

/-- `S` is a `2`-group. -/
theorem isPGroup_sylowTwoOfQ : IsPGroup 2 ↥hyp.sylowTwoOfQ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_equiv (default : Sylow 2 ↥hyp.Q).isPGroup' ?_
  exact (Subgroup.equivMapOfInjective _ hyp.Q.subtype hyp.Q.subtype_injective)

/-- `|Q₁|` is odd: `Q₁` is the normal `2`-complement of `Q`. -/
theorem odd_card_Q1 : Odd (Nat.card ↥hyp.Q1) := by
  rw [hyp.card_Q1]
  rcases Nat.even_or_odd (Nat.card hyp.Q1Subgroup) with h | h
  · exact absurd h.two_dvd hyp.two_not_dvd_card_Q1Subgroup
  · exact h

/-- Membership in the ambient `S`, in terms of the bundled Sylow subgroup of `Q`. -/
lemma mem_sylowTwoOfQ_iff {x : G} (hx : x ∈ hyp.Q) :
    x ∈ hyp.sylowTwoOfQ ↔
      (⟨x, hx⟩ : ↥hyp.Q) ∈ ((default : Sylow 2 ↥hyp.Q) : Subgroup ↥hyp.Q) := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hxs : (⟨x, hx⟩ : ↥hyp.Q) = s := Subtype.ext hsx.symm
    rw [hxs]; exact hs
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

/-- Membership in the ambient `Q₁`, in terms of the normal `2`-complement of `Q`. -/
lemma mem_Q1_iff {x : G} (hx : x ∈ hyp.Q) :
    x ∈ hyp.Q1 ↔ (⟨x, hx⟩ : ↥hyp.Q) ∈ hyp.Q1Subgroup := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hxy : (⟨x, hx⟩ : ↥hyp.Q) = y := Subtype.ext hyx.symm
    rw [hxy]; exact hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

/-- `S ∩ Q₁ = 1` (the book's `Q = S × Q₁`, first clause). -/
theorem sylowTwoOfQ_inf_Q1_eq_bot : hyp.sylowTwoOfQ ⊓ hyp.Q1 = ⊥ := by
  refine le_bot_iff.mp fun x hx => ?_
  obtain ⟨hxS, hxQ1⟩ := Subgroup.mem_inf.mp hx
  have hxQ : x ∈ hyp.Q := hyp.sylowTwoOfQ_le_Q hxS
  have hmem : (⟨x, hxQ⟩ : ↥hyp.Q) ∈
      ((default : Sylow 2 ↥hyp.Q) : Subgroup ↥hyp.Q) ⊓ hyp.Q1Subgroup :=
    Subgroup.mem_inf.mpr ⟨(hyp.mem_sylowTwoOfQ_iff hxQ).mp hxS,
      (hyp.mem_Q1_iff hxQ).mp hxQ1⟩
  rw [hyp.sylowTwo_inf_Q1Subgroup_eq_bot (default : Sylow 2 ↥hyp.Q),
    Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hmem

open scoped Pointwise in
/-- `S · Q₁ = Q` (the book's `Q = S × Q₁`, second clause). -/
theorem sylowTwoOfQ_mul_Q1_eq_Q :
    (hyp.sylowTwoOfQ : Set G) * (hyp.Q1 : Set G) = (hyp.Q : Set G) := by
  apply Set.Subset.antisymm
  · rintro x ⟨s, hs, y, hy, rfl⟩
    exact hyp.Q.mul_mem (hyp.sylowTwoOfQ_le_Q hs) (hyp.Q1_le_Q hy)
  · intro x hx
    obtain ⟨⟨⟨s, hs⟩, ⟨y, hy⟩⟩, hsy⟩ :=
      (hyp.sylowTwo_isComplement'_Q1Subgroup (default : Sylow 2 ↥hyp.Q)).2 ⟨x, hx⟩
    refine ⟨(s : G), ?_, (y : G), ?_, ?_⟩
    · exact (hyp.mem_sylowTwoOfQ_iff s.2).mpr hs
    · exact (hyp.mem_Q1_iff y.2).mpr hy
    · exact congrArg Subtype.val hsy

/-- `S` and `Q₁` commute elementwise (the book's `Q = S × Q₁`, third clause). -/
theorem sylowTwoOfQ_commutes_Q1 {s : G} (hs : s ∈ hyp.sylowTwoOfQ)
    {y : G} (hy : y ∈ hyp.Q1) : s * y = y * s := by
  have hsQ : s ∈ hyp.Q := hyp.sylowTwoOfQ_le_Q hs
  have hyQ : y ∈ hyp.Q := hyp.Q1_le_Q hy
  have h := hyp.sylowTwo_commute_Q1Subgroup (default : Sylow 2 ↥hyp.Q)
    ⟨⟨s, hsQ⟩, (hyp.mem_sylowTwoOfQ_iff hsQ).mp hs⟩
    ⟨⟨y, hyQ⟩, (hyp.mem_Q1_iff hyQ).mp hy⟩
  exact congrArg Subtype.val h

/-- `(|S|, |Q₁|) = 1`: `S` is a `2`-group and `|Q₁|` is odd. -/
theorem coprime_card_sylowTwoOfQ_Q1 :
    Nat.Coprime (Nat.card ↥hyp.sylowTwoOfQ) (Nat.card ↥hyp.Q1) := by
  obtain ⟨n, hn⟩ := hyp.isPGroup_sylowTwoOfQ.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hyp.odd_card_Q1)

/-- `S` is nilpotent, being a `2`-group. -/
theorem isNilpotent_sylowTwoOfQ : Group.IsNilpotent ↥hyp.sylowTwoOfQ :=
  hyp.isPGroup_sylowTwoOfQ.isNilpotent

/-- `H ≠ G`: the involution `t` lies outside `H`. -/
theorem H_ne_top : hyp.H ≠ ⊤ := fun h => hyp.t_not_mem_H (h ▸ Subgroup.mem_top _)

/-- `Q₁` is nilpotent, being a subgroup of the nilpotent group `Q`
(Ch. I §2, Proposition 1(b)). -/
theorem isNilpotent_Q1 : Group.IsNilpotent ↥hyp.Q1 := by
  letI : Group.IsNilpotent ↥hyp.Q := hyp.isNilpotent_Q
  haveI : Group.IsNilpotent ↥hyp.Q1Subgroup := Subgroup.isNilpotent _
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.equivMapOfInjective hyp.Q1Subgroup hyp.Q.subtype hyp.Q.subtype_injective)

end Hypothesis

namespace SecondCaseHypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (sc : SecondCaseHypothesis G Ω)

/-- **Theorem C, step 1, in Frobenius form**: the conjugation action of `D` on
`Q₁` is a Frobenius action. -/
theorem isFrobeniusAction_conjQ1ByD (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    letI : MulDistribMulAction ↥sc.toHypothesis.D ↥sc.toHypothesis.Q1 :=
      MulDistribMulAction.compHom _ sc.toHypothesis.conjQ1ByD
    IsFrobeniusAction ↥sc.toHypothesis.D ↥sc.toHypothesis.Q1 := by
  letI : MulDistribMulAction ↥sc.toHypothesis.D ↥sc.toHypothesis.Q1 :=
    MulDistribMulAction.compHom _ sc.toHypothesis.conjQ1ByD
  intro a ha n hn hfix
  refine hn (Subtype.ext ?_)
  refine sc.D_fixedPointFree_on_Q1 ind (a : G) a.2 (fun h => ha (Subtype.ext h)) (n : G) n.2 ?_
  exact congrArg (fun y : ↥sc.toHypothesis.Q1 => (y : G)) hfix

/-- `(|Q₁|, |D|) = 1`, from the Frobenius action of `D` on `Q₁`. -/
theorem coprime_card_Q1_D (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    Nat.Coprime (Nat.card ↥sc.toHypothesis.Q1) (Nat.card ↥sc.toHypothesis.D) := by
  classical
  letI : MulDistribMulAction ↥sc.toHypothesis.D ↥sc.toHypothesis.Q1 :=
    MulDistribMulAction.compHom _ sc.toHypothesis.conjQ1ByD
  haveI : Fintype ↥sc.toHypothesis.Q1 := Fintype.ofFinite _
  haveI : Fintype ↥sc.toHypothesis.D := Fintype.ofFinite _
  have h := (sc.isFrobeniusAction_conjQ1ByD ind).coprime_card
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

/-- **`(|Q|, |D|) = 1`**, the coprimality hypothesis of Appendix IV.

An odd prime dividing `|Q| = |S|·|Q₁|` divides `|Q₁|` (as `|S|` is a power of
`2`), and `(|Q₁|, |D|) = 1`; the prime `2` is excluded because `|D|` is odd. -/
theorem coprime_card_Q_D (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    Nat.Coprime (Nat.card ↥sc.toHypothesis.Q) (Nat.card ↥sc.toHypothesis.D) := by
  set hyp := sc.toHypothesis with hhyp
  by_contra hcop
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcop
  have hpQ : p ∣ Nat.card ↥hyp.Q := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpD : p ∣ Nat.card ↥hyp.D := hpdvd.trans (Nat.gcd_dvd_right _ _)
  -- `p ≠ 2`, since `|D|` is odd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hyp.D_odd) (even_iff_two_dvd.mpr hpD)
  -- `p ∣ |Q| = |S|·|Q₁|` with `|S|` a power of `2`, so `p ∣ |Q₁|`
  obtain ⟨n, hn⟩ := (hyp.isPGroup_sylowTwoOfQ).exists_card_eq
  have hpQ1 : p ∣ Nat.card ↥hyp.Q1 := by
    rw [← hyp.card_sylowTwoOfQ_mul_card_Q1, hn] at hpQ
    rcases (Nat.Prime.dvd_mul hp).mp hpQ with hS | hQ1
    · exact absurd (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two |>.mp
        (hp.dvd_of_dvd_pow hS)) hp2
    · exact hQ1
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes (sc.coprime_card_Q1_D ind) hpQ1 hpD)

/-- `Q₁` is not a `2`-group, given that it is non-trivial: it has odd order. -/
theorem Q1_not_isPGroup_two (hQ1 : sc.toHypothesis.Q1 ≠ ⊥) :
    ¬ IsPGroup 2 ↥sc.toHypothesis.Q1 := by
  intro hp
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact hQ1 (Subgroup.eq_bot_of_card_eq _ (by simpa using hn))
  · have h2 : 2 ∣ Nat.card ↥sc.toHypothesis.Q1 := by
      rw [hn]; exact dvd_pow_self 2 hpos.ne'
    exact (Nat.not_even_iff_odd.mpr sc.toHypothesis.odd_card_Q1) (even_iff_two_dvd.mpr h2)

/-- `Q` is a Hall subgroup of `G`: `|G| = |Q|·|D|·(|Q|+1)`, so
`[G : Q] = |D|·(|Q|+1)` is coprime to `|Q|`. -/
theorem coprime_card_Q_index (ind : Hypothesis.TheoremAInductionBelow G Ω) :
    Nat.Coprime (Nat.card ↥sc.toHypothesis.Q) sc.toHypothesis.Q.index := by
  set hyp := sc.toHypothesis with hhyp
  have hQpos : 0 < Nat.card ↥hyp.Q := Nat.card_pos
  have hidx : hyp.Q.index = Nat.card ↥hyp.D * (Nat.card ↥hyp.Q + 1) := by
    have h1 : Nat.card ↥hyp.Q * hyp.Q.index = Nat.card G := hyp.Q.card_mul_index
    have h2 : Nat.card G = Nat.card ↥hyp.Q * (Nat.card ↥hyp.D * (Nat.card ↥hyp.Q + 1)) := by
      rw [hyp.card_G_eq]; ring
    exact Nat.eq_of_mul_eq_mul_left hQpos (h1.trans h2)
  have hsucc : Nat.Coprime (Nat.card ↥hyp.Q) (Nat.card ↥hyp.Q + 1) := by
    refine Nat.coprime_of_dvd fun p hp hpn hpn1 => ?_
    have h1 : p ∣ 1 := by simpa using Nat.dvd_sub hpn1 hpn
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  rw [hidx]
  exact Nat.Coprime.mul_right (sc.coprime_card_Q_D ind) hsucc

/-- **Peterfalvi Part II, Ch. III, Theorem C, step 3** (p. 115): under (C1), if
`Q₁ ≠ 1` then `H = Q ⋊ D` satisfies the hypotheses of the Feit–Sibley Theorem
(Appendix IV).

Every field is one of the Chapter I axioms, the trivial-intersection statement
(step 2), the fixed-point-freeness of `D` on `Q₁` (step 1), or a fact about the
decomposition `Q = S × Q₁` into its Sylow `2`-subgroup and its odd part. -/
noncomputable def feitSibleyHypothesis (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hQ1 : sc.toHypothesis.Q1 ≠ ⊥) : FeitSibley.Hypothesis G where
  H := sc.toHypothesis.H
  Q := sc.toHypothesis.Q
  D := sc.toHypothesis.D
  S := sc.toHypothesis.sylowTwoOfQ
  Q1 := sc.toHypothesis.Q1
  H_ne_top := sc.toHypothesis.H_ne_top
  Q_le_H := sc.toHypothesis.Q_le_H
  D_le_H := sc.toHypothesis.D_le_H
  Q_normal_in_H := sc.toHypothesis.Q_normal_in_H
  Q_inf_D_eq_bot := sc.toHypothesis.Q_inf_D_eq_bot
  Q_mul_D_eq_H := sc.toHypothesis.Q_mul_D_eq_H
  coprime_Q_D := sc.coprime_card_Q_D ind
  Q_trivial_intersection := fun _ hx => sc.toHypothesis.Q_inf_map_conj_eq_bot hx
  S_le_Q := sc.toHypothesis.sylowTwoOfQ_le_Q
  Q1_le_Q := sc.toHypothesis.Q1_le_Q
  S_inf_Q1_eq_bot := sc.toHypothesis.sylowTwoOfQ_inf_Q1_eq_bot
  S_mul_Q1_eq_Q := sc.toHypothesis.sylowTwoOfQ_mul_Q1_eq_Q
  S_commutes_Q1 := fun _ hs _ hy => sc.toHypothesis.sylowTwoOfQ_commutes_Q1 hs hy
  coprime_S_Q1 := sc.toHypothesis.coprime_card_sylowTwoOfQ_Q1
  S_nilpotent := sc.toHypothesis.isNilpotent_sylowTwoOfQ
  Q1_not_two_group := sc.Q1_not_isPGroup_two hQ1
  D_fixedPointFree_on_Q1 := sc.D_fixedPointFree_on_Q1 ind

set_option maxHeartbeats 800000 in
-- The `FeitSibley.Hypothesis` value is a 22-field structure literal built from `sc`; unfolding it
-- to check the `tau`/`Sset`/`A` projections in the statement exceeds the default budget.
/-- **Peterfalvi Part II, Ch. III, Theorem C, step 3** (p. 115): "By this theorem,
`𝒮 = {χ ∈ Irr(H) | Q₁ ⊄ Ker χ}` is coherent for `Ind_H^G`."

The Feit–Sibley Theorem applies to the configuration built above: `d = |D|` is odd
by (A2)/(A3), `|Q₁|` is odd (`Q₁` is the normal `2`-complement of `Q`), `Q₁` is
nilpotent (a subgroup of the nilpotent `Q`), and `Q` is a Hall subgroup of `G`. -/
theorem sset_isCoherent [Fintype G] [Invertible (Nat.card G : ℂ)]
    (ind : Hypothesis.TheoremAInductionBelow G Ω) (hQ1 : sc.toHypothesis.Q1 ≠ ⊥)
    [Fintype ↥(sc.feitSibleyHypothesis ind hQ1).H]
    [Invertible (Nat.card ↥(sc.feitSibleyHypothesis ind hQ1).H : ℂ)] :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (sc.feitSibleyHypothesis ind hQ1).tau
      (sc.feitSibleyHypothesis ind hQ1).Sset
      (sc.feitSibleyHypothesis ind hQ1).A) := by
  have hd : Odd (sc.feitSibleyHypothesis ind hQ1).d := sc.toHypothesis.D_odd
  have hQ1odd : Odd (Nat.card ↥(sc.feitSibleyHypothesis ind hQ1).Q1) :=
    sc.toHypothesis.odd_card_Q1
  have hnil : Group.IsNilpotent ↥(sc.feitSibleyHypothesis ind hQ1).Q1 :=
    sc.toHypothesis.isNilpotent_Q1
  have hHall : Nat.Coprime (Nat.card ↥(sc.feitSibleyHypothesis ind hQ1).Q)
      (sc.feitSibleyHypothesis ind hQ1).Q.index := sc.coprime_card_Q_index ind
  exact FeitSibley.feit_sibley_coherence _ hd hQ1odd hnil hHall

/-- **Abelian subgroups of `D` are cyclic** — the standard Frobenius-complement
property, in the only form Chapter III needs.

The book invokes [H], Kapitel V, Satz 8.15 ("a fixed-point-free group has no
non-cyclic subgroup of order `p²`").  Here it is cheaper to argue directly: a
non-cyclic abelian `A ≤ D` acts coprimely on `Q₁` (`coprime_card_Q1_D`), so
**Isaacs Theorem 6.21** writes `Q₁ = ⟨C_{Q₁}(a) | a ∈ A^#⟩`; but the action of
`D` on `Q₁` is fixed-point-free (Theorem C, step 1), so every generator is
trivial and `Q₁ = 1`, contrary to hypothesis. -/
theorem isCyclic_of_isMulCommutative_le_D (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hQ1 : sc.toHypothesis.Q1 ≠ ⊥) {A : Subgroup G} (hAD : A ≤ sc.toHypothesis.D)
    [IsMulCommutative ↥A] : IsCyclic ↥A := by
  classical
  by_contra hnc
  letI : MulDistribMulAction ↥A ↥sc.toHypothesis.Q1 :=
    MulDistribMulAction.compHom _
      (sc.toHypothesis.conjQ1ByD.comp (Subgroup.inclusion hAD))
  haveI : Nontrivial ↥sc.toHypothesis.Q1 := (Subgroup.nontrivial_iff_ne_bot _).mpr hQ1
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥sc.toHypothesis.Q1) :=
    ((sc.coprime_card_Q1_D ind).symm).coprime_dvd_left (Subgroup.card_dvd_of_le hAD)
  have htop := OddOrder.Isaacs.Ch06.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic
    (A := ↥A) (N := ↥sc.toHypothesis.Q1) hcop hnc
  -- fixed-point-freeness makes the generating set trivial
  have hbot : OddOrder.Isaacs.Ch06.nontrivialActionFixedByClosure
      (MulDistribMulAction.toMulAut ↥A ↥sc.toHypothesis.Q1) = ⊥ := by
    rw [OddOrder.Isaacs.Ch06.nontrivialActionFixedByClosure, Subgroup.closure_eq_bot_iff]
    rintro u ⟨a, ha1, hfix⟩
    have haG : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hfixG : (a : G) * (u : G) * (a : G)⁻¹ = (u : G) :=
      congrArg (fun y : ↥sc.toHypothesis.Q1 => (y : G)) hfix
    have := sc.D_fixedPointFree_on_Q1 ind (a : G) (hAD a.2) haG (u : G) u.2 hfixG
    exact Set.mem_singleton_iff.mpr (Subtype.ext this)
  rw [hbot] at htop
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥sc.toHypothesis.Q1)
  have hmem : x ∈ (⊥ : Subgroup ↥sc.toHypothesis.Q1) := by
    rw [htop]; exact Subgroup.mem_top x
  exact hx (Subgroup.mem_bot.mp hmem)

/-! ## The conclusion of Theorem C, from a proper non-trivial normal subgroup -/

/-- `Q` a `2`-group forces `Q₁ = 1`: the odd part of a `2`-group is trivial. -/
theorem Q1_eq_bot_of_isPGroup_two (hQ : IsPGroup 2 ↥sc.toHypothesis.Q) :
    sc.toHypothesis.Q1 = ⊥ := by
  have hQ1 : IsPGroup 2 ↥sc.toHypothesis.Q1 :=
    hQ.to_le sc.toHypothesis.Q1_le_Q
  obtain ⟨n, hn⟩ := hQ1.exists_card_eq
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact Subgroup.eq_bot_of_card_eq _ (by simpa using hn)
  · exact absurd (even_iff_two_dvd.mpr (hn ▸ dvd_pow_self 2 hpos.ne'))
      (Nat.not_even_iff_odd.mpr sc.toHypothesis.odd_card_Q1)

/-- **Peterfalvi Part II, Ch. III, Theorem C, step 13** (p. 116): "Therefore
`N = Ker f_j` is a normal subgroup of `G` such that `1 ≠ N ≠ G`.  By Chapter I,
§3, Proposition 2, `G` satisfies the conclusion of Theorem A and so `Q₁ = 1`
(Chapter I, §3, Lemma 1)."

Once `G` is known not to be simple, Ch. I §3 Proposition 2 supplies Theorem A's
conclusion and Ch. I §3 Lemma 1 (`TheoremAConclusion.Q_and_residual`) makes `Q` a
`2`-group; its odd part `Q₁` is then trivial. -/
theorem Q1_eq_bot_of_not_isSimpleGroup (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hG : ¬ IsSimpleGroup G) : sc.toHypothesis.Q1 = ⊥ := by
  obtain ⟨result⟩ := sc.toHypothesis.theoremAConclusion_of_not_simple hG ind
  exact sc.Q1_eq_bot_of_isPGroup_two (result.Q_and_residual sc.toHypothesis).1

end SecondCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
