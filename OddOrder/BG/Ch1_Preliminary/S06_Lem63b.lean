/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S06_Additional
import OddOrder.GroupTheory.FrattiniPGroup
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Nat.Factorization.Basic

/-!
# BG §6.3(b): the derived subgroup of a solvable group with `|G/G'|` prime

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §6, Lemma 6.3(b) (mmd `references/bg/local-analysis.mmd`
L2000-2015). Tracking issue: [`issues/3016-lem63b-derived-hall.md`].

**Lemma 6.3(b)**: let `G` be a finite solvable group. If `G'` (`= commutator G`) is
nilpotent and `|G/G'|` is prime, then `G'` is a Hall subgroup of `G`, and
`G' = [G, K]` (`= ⁅⊤, K⁆`) for every complement `K` of `G'` in `G`.

## Proof (BG mmd L2013)

Let `p = |G/G'|`.  Then `G/O_{p'}(G')` is a `p`-group whose derived group has index `p`;
hence it is cyclic of order `p` and `G' = O_{p'}(G')` (a `p'`-group).  The rest follows
from Lemma 6.3(a).

The formalization spells out the "cyclic of order `p`" step: with `N = O_{p'}(G')` (the
`p'`-core of the nilpotent group `G'`, characteristic in `G'` hence normal in `G`), the
quotient `Q = G/N` is a `p`-group (every prime `q ≠ p` has its full `q`-part of `G'`
already inside the `q`-Sylow `≤ N`, using that a nilpotent group's Sylow subgroups are
normal), its derived group `⁅G,G⁆·N/N` has index `p` (Noether III), so `Q/[Q,Q]` is
cyclic of order `p`; as `[Q,Q] ≤ Φ(Q)` for a `p`-group, `Q/Φ(Q)` is cyclic and Burnside's
basis theorem makes `Q` cyclic, forcing `[Q,Q] = 1`, i.e. `G' ≤ N`, i.e. `G' = N` is a
`p'`-group.  Coprimality of `|G'|` and `|G/G'| = p` is the Hall property; the `[G,K]`
clause is Lemma 6.3(a) applied to `H := G'` (`⁅G',K⁆ = G'`) sandwiched between
`⁅G',K⁆ ≤ ⁅⊤,K⁆ ≤ ⁅⊤,⊤⁆ = G'`.

## Main results

* `commutator_isHall_of_nilpotent_prime_index`: `Nat.Coprime |G'| |G/G'|` (the Hall
  property, i.e. `G'` is a normal Hall subgroup).
* `commutator_eq_commutator_top_of_isComplement'`: `G' = ⁅⊤, K⁆` for every complement `K`.
* `lemma63b`: both conclusions bundled as in the book.

## References

* BG, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994), Lemma 6.3(b).
-/

namespace OddOrder.BG.Ch1.S06

open OddOrder.Isaacs
open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## 6.3(b): `G'` nilpotent + `|G/G'|` prime ⟹ `G'` Hall and `G' = [G,K]`

**Lemma 6.3(b)** (mmd L2000). See the module docstring for the proof outline. -/

section /- 6.3(b) -/

/-- **BG Lemma 6.3(b), Hall part** (mmd L2000): for a finite solvable `G` with `G'` nilpotent
and `|G/G'|` prime, `G'` is a Hall subgroup of `G`, i.e. `Nat.Coprime |G'| |G:G'|`.

This is the substance of (b): the book's `G' = O_{p'}(G')`.  With `p = |G/G'|` and
`N = O_{p'}(G')` (`p'`-core of the nilpotent `G'`, characteristic in `G'` hence normal in
`G`), the quotient `Q = G/N` is a `p`-group whose derived group has index `p`; Burnside's
basis theorem forces `Q` cyclic, so `⁅Q,Q⁆ = 1`, i.e. `G' ≤ N ≤ G'`, so `G' = N` is a
`p'`-group and `p ∤ |G'|`. -/
theorem commutator_isHall_of_nilpotent_prime_index [Finite G]
    (hnil : Group.IsNilpotent ↥(commutator G))
    (hprime : (commutator G).index.Prime) :
    Nat.Coprime (Nat.card ↥(commutator G)) (commutator G).index := by
  classical
  set p : ℕ := (commutator G).index with hpdef
  haveI : Fact p.Prime := ⟨hprime⟩
  -- `N = O_{p'}(G')`, and its image `N'` in `G`.
  set N : Subgroup ↥(commutator G) := Ch03.oPiCore {q | q ≠ p} ↥(commutator G) with hNdef
  set N' : Subgroup G := N.map (commutator G).subtype with hN'def
  -- `N'` is normal in `G` (characteristic-in-normal), lies in `G'`, has the same order as `N`.
  haveI hN'_normal : N'.Normal := by rw [hN'def, hNdef]; infer_instance
  have hN'_le : N' ≤ commutator G := by
    rw [hN'def]; rintro _ ⟨a, _, rfl⟩; exact a.2
  have hN'_card : Nat.card ↥N' = Nat.card ↥N := by
    rw [hN'def]
    exact Nat.card_congr (Subgroup.equivMapOfInjective N (commutator G).subtype
      (commutator G).subtype_injective).symm.toEquiv
  -- `N` is a `p'`-group.
  have hN_pi : Ch03.Subgroup.IsPiGroup {q | q ≠ p} N := by
    rw [hNdef]; exact Ch03.oPiCore.isPiGroup (G := ↥(commutator G)) {q | q ≠ p}
  have hp_not_dvd_N' : ¬ p ∣ Nat.card ↥N' := by
    rw [hN'_card]
    intro hdvd
    exact (hN_pi p (Nat.mem_primeFactors.mpr ⟨hprime, hdvd, Nat.card_pos.ne'⟩)) rfl
  -- `Nat.card G = |G'| * p`.
  have hcardG : Nat.card G = Nat.card ↥(commutator G) * p := by
    rw [hpdef]; exact (Subgroup.card_mul_index (commutator G)).symm
  -- **`Q = G/N'` is a `p`-group**: any prime `q ∣ |Q|` is `p`.
  have hQ_pgroup : IsPGroup p (G ⧸ N') := by
    rw [IsPGroup.iff_card]
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
    intro q hq_prime hq_dvd
    by_contra hqp
    have hqp' : q ≠ p := hqp
    have hQdvdG : Nat.card (G ⧸ N') ∣ Nat.card G := N'.index_dvd_card
    have hq_dvd_G : q ∣ Nat.card G := hq_dvd.trans hQdvdG
    have hq_dvd_H : q ∣ Nat.card ↥(commutator G) := by
      rw [hcardG] at hq_dvd_G
      rcases (Nat.Prime.dvd_mul hq_prime).mp hq_dvd_G with h | h
      · exact h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq_prime hprime).mp h) hqp'
    haveI : Fact q.Prime := ⟨hq_prime⟩
    obtain ⟨Sq⟩ : Nonempty (Sylow q ↥(commutator G)) := inferInstance
    haveI : Group.IsNilpotent ↥(commutator G) := hnil
    haveI hSq_normal : (Sq : Subgroup ↥(commutator G)).Normal := inferInstance
    -- `Sq` is a `p'`-group (it is a `q`-group with `q ≠ p`), hence `≤ N`.
    have hSq_pi : Ch03.Subgroup.IsPiGroup {q | q ≠ p} (Sq : Subgroup ↥(commutator G)) := by
      have hSq_q : Ch03.Subgroup.IsPiGroup ({q} : Set ℕ) (Sq : Subgroup ↥(commutator G)) :=
        Ch04.isPiGroup_singleton_of_isPGroup Sq.isPGroup'
      intro r hr
      have hrq : r = q := by simpa using hSq_q r hr
      simp only [Set.mem_setOf_eq, hrq]; exact hqp'
    have hSq_le_N : (Sq : Subgroup ↥(commutator G)) ≤ N := by
      rw [hNdef]; exact Ch03.Subgroup.IsPiGroup.le_oPiCore hSq_pi
    have hSq_dvd_N : Nat.card (Sq : Subgroup ↥(commutator G)) ∣ Nat.card ↥N :=
      Subgroup.card_dvd_of_le hSq_le_N
    -- The full `q`-part of `|G'|` divides `|N'|`.
    have hpow_dvd_N' : q ^ (Nat.card ↥(commutator G)).factorization q ∣ Nat.card ↥N' := by
      rw [hN'_card, ← Sq.card_eq_multiplicity]; exact hSq_dvd_N
    have hle1 : (Nat.card ↥(commutator G)).factorization q ≤ (Nat.card ↥N').factorization q :=
      (Nat.Prime.pow_dvd_iff_le_factorization hq_prime Nat.card_pos.ne').mp hpow_dvd_N'
    -- Factorization bookkeeping at `q`.
    have hcardG2 : Nat.card G = Nat.card ↥N' * Nat.card (G ⧸ N') :=
      (Subgroup.card_mul_index N').symm
    have hp_fact_zero : p.factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (fun hd => hqp' ((Nat.prime_dvd_prime_iff_eq hq_prime hprime).mp hd))
    have hfactG_H : (Nat.card G).factorization q = (Nat.card ↥(commutator G)).factorization q := by
      rw [hcardG, Nat.factorization_mul Nat.card_pos.ne' hprime.pos.ne', Finsupp.add_apply,
        hp_fact_zero, add_zero]
    have hfactG_N'Q : (Nat.card G).factorization q
        = (Nat.card ↥N').factorization q + (Nat.card (G ⧸ N')).factorization q := by
      rw [hcardG2, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply]
    have hposQ : 0 < (Nat.card (G ⧸ N')).factorization q :=
      hq_prime.factorization_pos_of_dvd Nat.card_pos.ne' hq_dvd
    omega
  -- **`⁅Q,Q⁆ = image of `G'` in `Q`** and it has index `p`.
  set q0 : G →* G ⧸ N' := QuotientGroup.mk' N' with hq0def
  have hq0surj : Function.Surjective q0 := QuotientGroup.mk'_surjective _
  have hcomm_map : (commutator G).map q0 = commutator (G ⧸ N') := by
    rw [hq0def, map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ hq0surj,
      ← _root_.commutator_def]
  have hcomm_index : (commutator (G ⧸ N')).index = p := by
    rw [← hcomm_map, Subgroup.index_map_eq (commutator G) hq0surj
      (by rw [hq0def, QuotientGroup.ker_mk']; exact hN'_le)]
  -- `⁅Q,Q⁆ ≤ Φ(Q)` (p-group) and `Q/Φ(Q)` cyclic ⟹ `Q` cyclic.
  have hcomm_le_frat : commutator (G ⧸ N') ≤ frattini (G ⧸ N') :=
    le_trans le_sup_left
      (OddOrder.GroupTheory.IsPGroup.commutator_sup_pow_closure_le_frattini hQ_pgroup)
  haveI hcyc_frat : IsCyclic ((G ⧸ N') ⧸ frattini (G ⧸ N')) := by
    have hdvd : Nat.card ((G ⧸ N') ⧸ frattini (G ⧸ N')) ∣ p := by
      have h1 := Subgroup.index_dvd_of_le hcomm_le_frat
      rw [hcomm_index] at h1; exact h1
    rcases hprime.eq_one_or_self_of_dvd _ hdvd with h1 | hpc
    · haveI : Subsingleton ((G ⧸ N') ⧸ frattini (G ⧸ N')) :=
        (Nat.card_eq_one_iff_unique.mp h1).1
      infer_instance
    · exact isCyclic_of_prime_card hpc
  haveI hcyc_Q : IsCyclic (G ⧸ N') :=
    OddOrder.GroupTheory.isCyclic_of_isCyclic_quotient_frattini hcyc_frat
  -- `Q` cyclic ⟹ abelian ⟹ `⁅Q,Q⁆ = 1` ⟹ `G' ≤ N'`, hence `G' = N'`.
  have hcommQ_bot : commutator (G ⧸ N') = ⊥ := commutator_eq_bot (G := G ⧸ N')
  have hH_le_N' : commutator G ≤ N' := by
    have hmb : (commutator G).map q0 = ⊥ := by rw [hcomm_map, hcommQ_bot]
    rw [Subgroup.map_eq_bot_iff, hq0def, QuotientGroup.ker_mk'] at hmb
    exact hmb
  have hHeqN' : commutator G = N' := le_antisymm hH_le_N' hN'_le
  -- `p ∤ |G'|`, i.e. `Nat.Coprime |G'| p`.
  have hp_not_dvd_H : ¬ p ∣ Nat.card ↥(commutator G) := by rw [hHeqN']; exact hp_not_dvd_N'
  exact (hprime.coprime_iff_not_dvd.mpr hp_not_dvd_H).symm

/-- **BG Lemma 6.3(b), commutator part** (mmd L2000): under the hypotheses of (b), for every
complement `K` of `G'` in `G` one has `G' = ⁅⊤, K⁆` (`= [G, K]`).

`Lemma 6.3(a)` gives `⁅G', K⁆ = G'`; monotonicity sandwiches
`G' = ⁅G', K⁆ ≤ ⁅⊤, K⁆ ≤ ⁅⊤, ⊤⁆ = G'`.  (The Hall/nilpotence hypotheses of (b) are not
needed here — only solvability and that `K` is a complement — but complements exist precisely
because `G'` is a normal Hall subgroup, cf. `commutator_isHall_of_nilpotent_prime_index`.) -/
theorem commutator_eq_commutator_top_of_isComplement' [IsSolvable G]
    {K : Subgroup G} (hK : (commutator G).IsComplement' K) :
    commutator G = ⁅(⊤ : Subgroup G), K⁆ := by
  have h63a : ⁅commutator G, K⁆ = commutator G :=
    commutator_eq_self_of_isComplement'_le_commutator hK le_rfl
  refine le_antisymm ?_ ?_
  · calc commutator G = ⁅commutator G, K⁆ := h63a.symm
      _ ≤ ⁅(⊤ : Subgroup G), K⁆ := Subgroup.commutator_mono le_top le_rfl
  · calc ⁅(⊤ : Subgroup G), K⁆
        ≤ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := Subgroup.commutator_mono le_rfl le_top
      _ = commutator G := (_root_.commutator_def (G := G)).symm

/-- **BG Lemma 6.3(b)** (mmd L2000): let `G` be a finite solvable group.  If `G'` is nilpotent
and `|G/G'|` is prime, then `G'` is a Hall subgroup of `G` and `G' = ⁅⊤, K⁆` (`= [G, K]`) for
every complement `K` of `G'` in `G`. -/
theorem lemma63b [Finite G] [IsSolvable G]
    (hnil : Group.IsNilpotent ↥(commutator G))
    (hprime : (commutator G).index.Prime) :
    Nat.Coprime (Nat.card ↥(commutator G)) (commutator G).index ∧
      ∀ K : Subgroup G, (commutator G).IsComplement' K → commutator G = ⁅(⊤ : Subgroup G), K⁆ :=
  ⟨commutator_isHall_of_nilpotent_prime_index hnil hprime,
    fun _ hK => commutator_eq_commutator_top_of_isComplement' hK⟩

end /- 6.3(b) -/

end OddOrder.BG.Ch1.S06
