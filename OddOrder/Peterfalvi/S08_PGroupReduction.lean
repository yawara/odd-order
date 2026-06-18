/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S08_CaseBSeedGlue
import OddOrder.Peterfalvi.S08_CoherenceCore

/-!
# Peterfalvi (6.5): reduction to a non-abelian `p`-group — `(6.8)` application

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §6, (6.5).

The group-theoretic core of Peterfalvi (6.5)(b) — *a finite nilpotent group on whose abelianization a
finite group acts fixed-point-freely, with the `≤ 4|·|² + 1` index bound, is a `p`-group* — is
already formalized abstractly:
* `isPGroup_of_isFrobeniusGroup_of_card_le` (`S08_CoherenceCorePart1`) for the (6.8)(c1) Frobenius
  case (full fixed-point-free conjugation action), and
* `isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator` for the (6.8)(c2) certain-type case
  (fixed points in `⁅H,H⁆`).

Both take the **index bound** `hbound : |Abelianization H| ≤ 4|W₁|² + 1` as the single nontrivial
input; that bound is the contrapositive of Theorem (6.3) (`¬coherent S` + nilpotent + `S(⁅H,H⁆) = Y`
coherent ⟹ the bound), which is the remaining gate (via (6.2)).

This leaf supplies the two odd-order side conditions and wires the **(6.8)(c1) Frobenius** reduction
into the `SibleyDadeHypothesis` context, isolating `hbound` as the residual obligation.
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- Any natural dividing `|L|` is odd (since `|L|` is odd, Peterfalvi (6.4.a)). -/
theorem odd_of_dvd_card_L (hyp : SibleyDadeHypothesis G L H) {a : ℕ} (ha : a ∣ Nat.card ↥L) :
    Odd a := by
  rcases Nat.even_or_odd a with he | ho
  · obtain ⟨c, hc⟩ := ha
    exact absurd (hc ▸ he.mul_right c) (Nat.not_even_iff_odd.mpr hyp.card_L_odd)
  · exact ho

/-- `|W₁|` is odd. -/
theorem card_W1_odd (hyp : SibleyDadeHypothesis G L H) : Odd (Nat.card ↥hyp.W1) :=
  odd_of_dvd_card_L hyp (Subgroup.card_subgroup_dvd_card hyp.W1)

/-- `|H|` is odd. -/
theorem card_H_odd (hyp : SibleyDadeHypothesis G L H) : Odd (Nat.card ↥H) :=
  odd_of_dvd_card_L hyp (Subgroup.card_subgroup_dvd_card H)

/-- `|Abelianization H| = |H : ⁅H,H⁆|` is odd (it divides `|H|`, which divides the odd `|L|`). -/
theorem card_abelianization_H_odd (hyp : SibleyDadeHypothesis G L H) :
    Odd (Nat.card (Abelianization ↥H)) :=
  odd_of_dvd_card_L hyp
    ((Subgroup.card_quotient_dvd_card (commutator ↥H)).trans (Subgroup.card_subgroup_dvd_card H))

/-- **Peterfalvi (6.5)(b) reduction — (6.8)(c1) Frobenius case, in the Sibley context.**

When `L` is a Frobenius group with kernel `H` and complement `W₁` ((6.8)(c1), `hyp.cases.inl`), the
nilpotent kernel `H` is a `p`-group for some prime `p`, given the (6.2)/(6.3) index bound
`hbound : |Abelianization H| ≤ 4|W₁|² + 1`.  The odd-order side conditions are discharged from
`|L|` odd; the fixed-point-free `W₁`-action on `Abelianization H` is the Frobenius structure.

This wires `isPGroup_of_isFrobeniusGroup_of_card_le` into the capstone, isolating `hbound` (the
contrapositive of Theorem (6.3)) as the only residual obligation of the (6.8)(c1) `p`-group
reduction. -/
theorem exists_isPGroup_H_of_frobenius_of_card_le (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hbound : Nat.card (Abelianization ↥H) ≤ 4 * Nat.card ↥hyp.W1 ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p ↥H := by
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  exact isPGroup_of_isFrobeniusGroup_of_card_le hF (card_abelianization_H_odd hyp)
    (card_W1_odd hyp) hbound

/-- **Peterfalvi (6.5)(b) reduction — (6.8)(c2) certain-type case, in the Sibley context.**

In case (6.8)(c2) the complement `W₁` does *not* act fixed-point-freely on `H`, but the
`W₁`-conjugation fixed points lie in `⁅H,H⁆` (the certain-type centralizer condition `hfix`, phrased
via the explicit `L`-conjugation `w x w⁻¹ = x`).  Together with the Hall coprimality `hcop` and the
(6.2)/(6.3) index bound `hbound`, the nilpotent `H` is a `p`-group.

This wires `isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator` into the capstone via the
`W₁`-conjugation action, isolating `hfix` (the (4.6)/(6.4.c) fixed-point condition) and `hbound` (the
contrapositive of Theorem (6.3)) as the residual obligations of the (6.8)(c2) `p`-group reduction. -/
theorem exists_isPGroup_H_of_c2_of_card_le (hyp : SibleyDadeHypothesis G L H)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥hyp.W1))
    (hfix : ∀ w : ↥hyp.W1, w ≠ 1 → ∀ x : ↥H,
      (w : ↥L) * (x : ↥L) * (w : ↥L)⁻¹ = (x : ↥L) → x ∈ commutator ↥H)
    (hbound : Nat.card (Abelianization ↥H) ≤ 4 * Nat.card ↥hyp.W1 ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p ↥H := by
  letI : H.Normal := hyp.H_normal
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  -- the `W₁`-conjugation action on `H`.
  letI actH : MulDistribMulAction ↥hyp.W1 ↥H :=
    MulDistribMulAction.compHom H ((MulAut.conjNormal (H := H)).comp hyp.W1.subtype)
  have hsmulH : ∀ (a : ↥hyp.W1) (x : ↥H),
      ((a • x : ↥H) : ↥L) = (a : ↥L) * (x : ↥L) * (a : ↥L)⁻¹ := by
    intro a x
    have h1 : (a • x : ↥H) = (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a) x := by
      simp [MulDistribMulAction.toMulAut_apply]
    rw [h1]
    show ((MulAut.conjNormal (H := H) (hyp.W1.subtype a)) x : ↥L) = _
    rw [MulAut.conjNormal_apply]; rfl
  -- convert the explicit-conjugation `hfix` to the smul form the reduction lemma consumes.
  have hfix' : ∀ w : ↥hyp.W1, w ≠ 1 → ∀ x : ↥H, w • x = x → x ∈ commutator ↥H := by
    intro w hw x hwx
    refine hfix w hw x ?_
    have hb := hsmulH w x
    rw [hwx] at hb
    exact hb.symm
  exact isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator hcop.symm hfix'
    (card_abelianization_H_odd hyp) (card_W1_odd hyp) hbound

/-- A `p`-group factor of the odd group `H` (`p` prime, `H ≠ ⊥`) has `p ≥ 3`: `p ∣ |H| ∣ |L|` and
`|L|` is odd, so `p` is an odd prime. -/
theorem three_le_of_isPGroup_H (hyp : SibleyDadeHypothesis G L H)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) : 3 ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hHp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot)).ne' hn
  have hpH : p ∣ Nat.card ↥H := hn ▸ dvd_pow_self p hn0
  have hpL : p ∣ Nat.card ↥L := hpH.trans H.card_subgroup_dvd_card
  have hpodd : Odd p := hyp.card_L_odd.of_dvd_nat hpL
  have h2 : 2 ≤ p := hp.two_le
  rcases Nat.lt_or_ge p 3 with h | h
  · interval_cases p
    · exact absurd hpodd (by decide)
  · exact h

/-- **`H` is non-abelian** in the `X`-nonempty branch: `X(⁅H,H⁆) ≠ ∅` forces `⁅H,H⁆ ≠ ⊥`, hence
`commutator ↥H ≠ ⊥`.  (If `⁅H,H⁆ = ⊥` then `S(⁅H,H⁆) = S(⊥) = S`, so `X(⁅H,H⁆) = S − S = ∅`.) -/
theorem commutator_ne_bot_of_Xset_commutator_nonempty (hyp : SibleyDadeHypothesis G L H)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty) : _root_.commutator ↥H ≠ ⊥ := by
  letI : H.Normal := hyp.H_normal
  intro hbot
  rw [← commutator_subgroupOf_self] at hbot
  have hcommbot : (⁅H, H⁆ : Subgroup ↥L) = ⊥ :=
    (Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le (Subgroup.commutator_le_left H H)
  have hXempty : hyp.Xset ⁅H, H⁆ = ∅ := by
    show hyp.S \ hyp.SsubFiltration ⁅H, H⁆ = ∅
    rw [hcommbot, hyp.SsubFiltration_bot, Set.diff_self]
  rw [hXempty] at hXne
  exact Set.not_nonempty_empty hXne

/-- **Peterfalvi (6.8) — Frobenius case (6.8)(c1): `S` is coherent.**  When `L` is a Frobenius group
with kernel `H` and complement `W₁`, and the `X`-set `X(⁅H,H⁆)` is nonempty (so `H` is non-abelian),
the Sibley set `S` is coherent.

This *fully closes* the (6.8)(c1) branch: by contradiction, if `S` is not coherent then the (6.5)
reduction `isPGroup_of_not_coherent` makes `H` a `p`-group; `p ≥ 3` (odd order) and `H` non-abelian
(`X`-nonempty) feed the case-(A) Frobenius coherence `nonempty_coherent_S_caseA_of_frobenius`,
contradicting non-coherence. -/
theorem nonempty_coherent_S_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  letI : H.Normal := hyp.H_normal
  by_contra hncoh
  obtain ⟨p, hp, hHp⟩ := hyp.isPGroup_of_not_coherent hF hncoh
  exact hncoh (hyp.nonempty_coherent_S_caseA_of_frobenius hF
    (commutator_ne_bot_of_Xset_commutator_nonempty hyp hXne) hp
    (three_le_of_isPGroup_H hyp hp hHp) hHp)

/-- **Peterfalvi (6.4.c) for case (6.8)(c2): the `W₁`-conjugation fixed points lie in `⁅H,H⁆`.**

The certain-type Hypothesis (4.2)(b) gives `C_K(w) = W₂` for every `w ∈ W₁^#` (`centralizer_W2`),
and case (c2) has `W₂ ⊆ ⁅H,H⁆`.  Hence any `x ∈ H` fixed by conjugation by a nonidentity
`w ∈ W₁` lies in `C_L(w) ⊓ K = W₂ ⊆ ⁅H,H⁆`, so `x ∈ ⁅H,H⁆.subgroupOf H = commutator ↥H`
(`commutator_subgroupOf_self`).  This is exactly the `hfix` hypothesis consumed by
`exists_isPGroup_H_of_c2_of_card_le`, mirroring the `caseB_W1_dvd_index_commutator` fixed-point
argument — the (6.4.c) Frobenius-action condition is a *consequence* of the certain-type centralizer
datum, not an extra input. -/
theorem fixedPoints_W1_subset_commutator_of_c2 (hyp : SibleyDadeHypothesis G L H)
    (cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L)
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1) (hW2 : cert.W2 ≤ ⁅H, H⁆) :
    ∀ w : ↥hyp.W1, w ≠ 1 → ∀ x : ↥H,
      (w : ↥L) * (x : ↥L) * (w : ↥L)⁻¹ = (x : ↥L) → x ∈ commutator ↥H := by
  intro w hw x hwx
  -- `(x:L)` commutes with `(w:L)` (from the conjugation-fixed hypothesis), so lies in `C_L(w)`.
  have hxcen : (x : ↥L) ∈ Subgroup.centralizer ({(w : ↥L)} : Set ↥L) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hwx).symm
  have hwW1 : (w : ↥L) ∈ cert.W1 := by rw [hW1]; exact w.2
  have hwne : (w : ↥L) ≠ 1 := fun h => hw (OneMemClass.coe_eq_one.mp h)
  -- `(x:L) ∈ C_L(w) ⊓ K = W₂` by the certain-type centralizer datum (4.2.b).
  have hxW2 : (x : ↥L) ∈ cert.W2 := by
    rw [← cert.centralizer_W2 (w : ↥L) hwW1 hwne]
    exact Subgroup.mem_inf.mpr ⟨hxcen, by rw [hK]; exact x.2⟩
  -- `W₂ ⊆ ⁅H,H⁆`, so `x ∈ ⁅H,H⁆.subgroupOf H = commutator ↥H`.
  rw [← commutator_subgroupOf_self]
  exact Subgroup.mem_subgroupOf.mpr (hW2 hxW2)

/-- **Peterfalvi (6.8) — certain-type case (6.8)(c2): `S` is coherent (dispatch skeleton).**

The (6.8)(c2) branch of `sibleySetup_is_coherent`, assembled from the certain-type data `h46` of
`hyp.cases.inr`.  By contradiction-free assembly: the (6.5) reduction
(`exists_isPGroup_H_of_c2_of_card_le`, fed `hfix` from `fixedPoints_W1_subset_commutator_of_c2` and
the (6.3) index bound `hbound`) makes `H` a `p`-group, then the math case split (6.8.A/B) on whether
`W₂ ⊆ Z(H)` routes to the case-A coherence producer (`Z(H) ∩ W₂ = 1`) or the case-B one
(`1 ≠ W₂ ⊆ Z(H)`, `nonempty_coherent_S_caseB_of_structure`, cont.¹³).

This is the [[gated-endpoint-skeleton]] form: the three genuine residual obligations are isolated as
named hypotheses — `hbound` (Theorem (6.3) c2, the main remaining work, via the reducible-break
norm-weighted (5.6) engine), `hcaseA` (the case-A `_of_c2_caseA` → `S` bootstrap), and `hcaseB` (the
case-B structure-data discharge feeding `nonempty_coherent_S_caseB_of_structure`).  The A/B split
itself (`hsplit`, prime-order `W₂.subgroupOf H` ⟹ `⊥` or all in `Z(H)`) is also named, to be
discharged separately.  Wiring this into `S08_CoherenceTheorems:59` (the c2 branch) follows once the
three obligations are filled. -/
theorem nonempty_coherent_S_of_c2_of_branches (hyp : SibleyDadeHypothesis G L H)
    [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    (hHK : h46.K = H) (hW1 : h46.W1 = hyp.W1) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    (hbound : Nat.card (Abelianization ↥H) ≤ 4 * Nat.card ↥hyp.W1 ^ 2 + 1)
    (hsplit : h46.W2.subgroupOf H ≤ Subgroup.center ↥H ∨
      Disjoint (h46.W2.subgroupOf H) (Subgroup.center ↥H))
    (hcaseA : ∀ {p : ℕ}, p.Prime → IsPGroup p ↥H →
      Disjoint (h46.W2.subgroupOf H) (Subgroup.center ↥H) →
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hcaseB : ∀ {p : ℕ}, p.Prime → IsPGroup p ↥H →
      h46.W2.subgroupOf H ≤ Subgroup.center ↥H →
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  have hfix := fixedPoints_W1_subset_commutator_of_c2 hyp h46.toCertainTypeHypothesis hHK hW1 hW2comm
  obtain ⟨p, hp, hHp⟩ := exists_isPGroup_H_of_c2_of_card_le hyp hcop hfix hbound
  rcases hsplit with hB | hA
  · exact hcaseB hp hHp hB
  · exact hcaseA hp hHp hA

end OddOrder.Peterfalvi.S08
