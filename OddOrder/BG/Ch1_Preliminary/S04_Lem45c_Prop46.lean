/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Nilpotent
import OddOrder.BG.Ch1_Preliminary.S04_SmallRankBasic
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import OddOrder.GroupTheory.OmegaSubgroup
import OddOrder.GroupTheory.NarrowPGroup
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh02

/-!
# BG §4B: Lemma 4.5(c) and Proposition 4.6 (normal `E_{p²}` inside a noncyclic normal subgroup)

**Scope**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §4, mmd `references/bg/local-analysis.mmd` L1496-1516.
Two `S`-sized derivations from already-formalised infrastructure (issue 3013).

## Results

* **BG Lemma 4.5(c)** (mmd L1498): for `p` odd and a noncyclic `p`-group `R`, the subgroup
  `Ω₁(Z₂(R))` (`OddOrder.GroupTheory.omega1UpperCentralTwo R p`) is **noncyclic of exponent `p`**
  and has order `≥ p²`.
  (`omega1UpperCentralTwo_not_isCyclic_and_card_prime_sq_le_of_not_isCyclic`.)

* **BG Proposition 4.6** (mmd L1516): for `p` odd, a `p`-group `R`, and a **noncyclic normal**
  subgroup `S ⊴ R`, `S` contains a normal-in-`R` elementary abelian subgroup of order `p²`
  (`exists_normal_isElementaryAbelian_card_prime_sq_le_of_normal_not_isCyclic`).

## Proof outline

`Ω₁(Z₂(R))` and its exponent-`p` half are already available from
`OddOrder.GroupTheory.NarrowPGroup`:

* `omega1UpperCentralTwo R p = (Ω₁(↥Z₂(R))).map Z₂(R).subtype`, `Z₂(R) = upperCentralSeries R 2`;
* `commutator_upperCentralSeries_two_le_center`: `Z₂(R)` has class `≤ 2`;
* `pow_eq_one_of_mem_omega1UpperCentralTwo`: for `p` odd every element of `Ω₁(Z₂(R))` has `pᵗʰ`
  power `1` (this is the exponent-`p` half of 4.5(c), from `Omega.pow_eq_one_of_class_le_two`).

The genuinely new content here is the **noncyclic / order `≥ p²`** half:

1. By BG Lemma 4.5(a)
   (`exists_normal_isElementaryAbelian_card_prime_sq_of_not_isCyclic`, S04_SmallRankBasic §4E)
   `R` has a normal elementary abelian `W ⊴ R` with `|W| = p²`.
2. `W ⊆ Z₂(R)`: `R` is nilpotent (a `p`-group), so for the nontrivial normal `W`,
   `⁅W, R⁆ < W` (`commutator_lt_self_of_isNilpotent_ambient`), hence `|⁅W, R⁆| ∈ {1, p}`. If
   `⁅W, R⁆ = ⊥` then `W ≤ Z(R)`; otherwise `⁅W, R⁆` is normal of order `p`, so
   `⁅W, R⁆ ⊓ Z(R)` is a nontrivial subgroup of the order-`p` group `⁅W, R⁆`
   (`IsPGroup.normal_inf_center_nontrivial`), forcing `⁅W, R⁆ ≤ Z(R)`. Either way
   `⁅W, R⁆ ≤ Z(R)`, i.e. `W ≤ Z₂(R)`.
3. `W` elementary abelian (exponent `p`) and `W ⊆ Z₂(R)` give `W ≤ Ω₁(Z₂(R))`, so `Ω₁(Z₂(R))`
   is noncyclic (a subgroup of a cyclic group is cyclic, but `W` is not) and `|Ω₁(Z₂(R))| ≥ p²`.

Proposition 4.6 applies Lemma 4.5(c) to `↥S`, notes `Ω₁(Z₂(↥S))` is characteristic in `↥S`
(hence, pushed forward along `S.subtype`, normal in `R` since `S ⊴ R`), has exponent `p` and
order `≥ p²`, and extracts an `R`-normal order-`p²` subgroup with BG Lemma 1.22
(`normal_subgroup_card_pow_le_of_pGroup`). That subgroup has order `p²` and exponent `p`, hence
is elementary abelian.

## References

* BG mmd `references/bg/local-analysis.mmd` L1496-1516.
* Reused infrastructure: `OddOrder.GroupTheory.NarrowPGroup` (`omega1UpperCentralTwo` API),
  `OddOrder.BG.Ch1.S04.exists_normal_isElementaryAbelian_card_prime_sq_of_not_isCyclic` (4.5(a)),
  `OddOrder.BG.Ch1.S01.normal_subgroup_card_pow_le_of_pGroup` (1.22),
  `OddOrder.Isaacs.Ch04.commutator_lt_self_of_isNilpotent_ambient`.
* Issue 3013.
-/

namespace OddOrder.BG.Ch1.S04

open OddOrder.GroupTheory
open scoped commutatorElement

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- A characteristic subgroup `L` of a normal subgroup `N ⊴ W` pushes forward to a normal
subgroup `L.map N.subtype ⊴ W`. (Local copy of the BG §3/§10 helper, to avoid a downstream
import; the conjugation automorphism `MulAut.conjNormal w` restricts to `↥N` and fixes the
characteristic `L`.) -/
private theorem normal_map_subtype_of_characteristic {W : Type*} [Group W] {N : Subgroup W}
    [N.Normal] {L : Subgroup ↥N} (hL : L.Characteristic) : (L.map N.subtype).Normal := by
  refine ⟨fun a ha w => ?_⟩
  obtain ⟨⟨a', ha'N⟩, ha'L, rfl⟩ := ha
  have hmap : L.map (MulAut.conjNormal w).toMonoidHom = L :=
    (Subgroup.characteristic_iff_map_eq.mp hL) (MulAut.conjNormal w)
  have hmem : (MulAut.conjNormal w) ⟨a', ha'N⟩ ∈ L := by
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ ha'L
  exact ⟨(MulAut.conjNormal w) ⟨a', ha'N⟩, hmem, MulAut.conjNormal_apply w ⟨a', ha'N⟩⟩

/-! ## BG Lemma 4.5(c): `Ω₁(Z₂(R))` is noncyclic of exponent `p`

The exponent-`p` half is `OddOrder.GroupTheory.pow_eq_one_of_mem_omega1UpperCentralTwo`. Here we
supply the noncyclic / order-`≥ p²` half by exhibiting a normal `E_{p²}` inside `Ω₁(Z₂(R))`. -/

/-- **BG Lemma 4.5(c) core**: the normal `E_{p²}` from Lemma 4.5(a) lies inside `Ω₁(Z₂(R))`.

For `p` odd and `R` a noncyclic `p`-group there is a normal elementary abelian `W ⊴ R` with
`|W| = p²` and `W ≤ Ω₁(Z₂(R))`. This witnesses both the noncyclicity and the order bound of
Lemma 4.5(c). -/
theorem exists_normal_isElementaryAbelian_card_prime_sq_le_omega1UpperCentralTwo
    (hR : IsPGroup p R) (hp_odd : Odd p) (hnc : ¬ IsCyclic R) :
    ∃ W : Subgroup R, W.Normal ∧ W.IsElementaryAbelian p ∧ Nat.card W = p ^ 2
      ∧ W ≤ omega1UpperCentralTwo R p := by
  have hp : p.Prime := Fact.out
  haveI hRnil : Group.IsNilpotent R := hR.isNilpotent
  -- (1) Lemma 4.5(a): a normal `E_{p²}`.
  obtain ⟨W, hWn, hWea, hWcard⟩ :=
    exists_normal_isElementaryAbelian_card_prime_sq_of_not_isCyclic hR hp_odd hnc
  haveI : W.Normal := hWn
  have hW_ne_bot : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hWcard
    have : (1 : ℕ) < p ^ 2 := one_lt_pow₀ hp.one_lt (by norm_num)
    omega
  -- (2) `⁅W, R⁆ ≤ Z(R)`, whence `W ≤ Z₂(R)`.
  have hC_lt : ⁅W, (⊤ : Subgroup R)⁆ < W :=
    OddOrder.Isaacs.Ch04.commutator_lt_self_of_isNilpotent_ambient hW_ne_bot
  have hC_le_W : ⁅W, (⊤ : Subgroup R)⁆ ≤ W := hC_lt.le
  have hC_le_center : ⁅W, (⊤ : Subgroup R)⁆ ≤ Subgroup.center R := by
    by_cases hCbot : ⁅W, (⊤ : Subgroup R)⁆ = ⊥
    · rw [hCbot]; exact bot_le
    · haveI hCnt : Nontrivial ↥(⁅W, (⊤ : Subgroup R)⁆) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hCbot
      have hC_dvd : Nat.card ↥(⁅W, (⊤ : Subgroup R)⁆) ∣ p ^ 2 :=
        hWcard ▸ Subgroup.card_dvd_of_le hC_le_W
      have hC_gt1 : 1 < Nat.card ↥(⁅W, (⊤ : Subgroup R)⁆) :=
        Finite.one_lt_card_iff_nontrivial.mpr hCnt
      have hC_ne_sq : Nat.card ↥(⁅W, (⊤ : Subgroup R)⁆) ≠ p ^ 2 := by
        intro hEq
        exact hC_lt.ne (Subgroup.eq_of_le_of_card_ge hC_le_W (le_of_eq (by rw [hWcard, hEq])))
      have hC_card_p : Nat.card ↥(⁅W, (⊤ : Subgroup R)⁆) = p := by
        rcases (Nat.dvd_prime_pow hp).mp hC_dvd with ⟨m, hm_le, hm_eq⟩
        interval_cases m
        · simp only [pow_zero] at hm_eq; omega
        · simpa using hm_eq
        · exact absurd hm_eq hC_ne_sq
      -- `⁅W, R⁆ ⊓ Z(R)` is a nontrivial subgroup of the order-`p` group `⁅W, R⁆`, hence equals it.
      have hinf_nt :
          Nontrivial ((⁅W, (⊤ : Subgroup R)⁆ ⊓ Subgroup.center R : Subgroup R)) :=
        OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial hR hCnt
      have hinf_gt1 :
          1 < Nat.card ((⁅W, (⊤ : Subgroup R)⁆ ⊓ Subgroup.center R : Subgroup R)) :=
        Finite.one_lt_card_iff_nontrivial.mpr hinf_nt
      have hinf_dvd :
          Nat.card ((⁅W, (⊤ : Subgroup R)⁆ ⊓ Subgroup.center R : Subgroup R))
            ∣ Nat.card ↥(⁅W, (⊤ : Subgroup R)⁆) :=
        Subgroup.card_dvd_of_le inf_le_left
      rw [hC_card_p] at hinf_dvd
      have hinf_eq : (⁅W, (⊤ : Subgroup R)⁆ ⊓ Subgroup.center R) = ⁅W, (⊤ : Subgroup R)⁆ := by
        apply Subgroup.eq_of_le_of_card_ge inf_le_left
        rw [hC_card_p]
        rcases (Nat.dvd_prime hp).mp hinf_dvd with h1 | hpp
        · omega
        · omega
      calc ⁅W, (⊤ : Subgroup R)⁆
          = ⁅W, (⊤ : Subgroup R)⁆ ⊓ Subgroup.center R := hinf_eq.symm
        _ ≤ Subgroup.center R := inf_le_right
  have hW_le_Z2 : W ≤ Subgroup.upperCentralSeries R 2 := by
    intro w hw
    refine Subgroup.mem_upperCentralSeries_succ_iff.mpr (fun r => ?_)
    rw [Subgroup.upperCentralSeries_one]
    exact hC_le_center (Subgroup.commutator_mem_commutator hw (Subgroup.mem_top r))
  -- (3) `W ≤ Ω₁(Z₂(R))` (elements of `W` have `pᵗʰ` power `1`).
  have hW_le : W ≤ omega1UpperCentralTwo R p := by
    intro w hw
    rw [omega1UpperCentralTwo, Subgroup.mem_map]
    have hwZ2 : w ∈ Subgroup.upperCentralSeries R 2 := hW_le_Z2 hw
    have hwp : w ^ p = 1 := by
      have h := hWea.2 (⟨w, hw⟩ : ↥W)
      have h2 := congrArg (Subtype.val : ↥W → R) h
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
    refine ⟨⟨w, hwZ2⟩, Omega.mem_of_pow_eq_one ?_, rfl⟩
    rw [pow_one]
    exact Subtype.ext (by simpa using hwp)
  exact ⟨W, hWn, hWea, hWcard, hW_le⟩

/-- **BG Lemma 4.5(c)** (order bound). For `p` odd and `R` a noncyclic `p`-group,
`p² ≤ |Ω₁(Z₂(R))|`. -/
theorem card_prime_sq_le_omega1UpperCentralTwo_of_not_isCyclic
    (hR : IsPGroup p R) (hp_odd : Odd p) (hnc : ¬ IsCyclic R) :
    p ^ 2 ≤ Nat.card ↥(omega1UpperCentralTwo R p) := by
  obtain ⟨W, _, _, hWcard, hW_le⟩ :=
    exists_normal_isElementaryAbelian_card_prime_sq_le_omega1UpperCentralTwo hR hp_odd hnc
  rw [← hWcard]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hW_le)

/-- **BG Lemma 4.5(c)**. For `p` odd and a noncyclic `p`-group `R`, the subgroup `Ω₁(Z₂(R))`
(`omega1UpperCentralTwo R p`) is **noncyclic**, has order `≥ p²`, and has **exponent `p`**
(every element has `pᵗʰ` power `1`). -/
theorem omega1UpperCentralTwo_not_isCyclic_and_card_prime_sq_le_of_not_isCyclic
    (hR : IsPGroup p R) (hp_odd : Odd p) (hnc : ¬ IsCyclic R) :
    ¬ IsCyclic ↥(omega1UpperCentralTwo R p)
      ∧ p ^ 2 ≤ Nat.card ↥(omega1UpperCentralTwo R p)
      ∧ ∀ g ∈ omega1UpperCentralTwo R p, g ^ p = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨W, _, hWea, hWcard, hW_le⟩ :=
    exists_normal_isElementaryAbelian_card_prime_sq_le_omega1UpperCentralTwo hR hp_odd hnc
  refine ⟨?_, ?_, fun _ hg => pow_eq_one_of_mem_omega1UpperCentralTwo hp_odd hg⟩
  · -- noncyclic: `W ≤ Ω₁(Z₂(R))` with `W` noncyclic; a subgroup of a cyclic group is cyclic.
    intro hcyc
    haveI := hcyc
    have hWnc : ¬ IsCyclic ↥W :=
      IsElementaryAbelian.not_isCyclic_of_card_prime_sq hp hWea hWcard
    exact hWnc (isCyclic_of_injective (Subgroup.inclusion hW_le)
      (Subgroup.inclusion_injective hW_le))
  · -- order `≥ p²`.
    rw [← hWcard]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hW_le)

/-! ## BG Proposition 4.6: normal `E_{p²}` inside a noncyclic normal subgroup -/

/-- **BG Proposition 4.6**. For `p` odd, `R` a `p`-group, and `S ⊴ R` a **noncyclic normal**
subgroup, `S` contains a subgroup `L` that is **normal in `R`**, **elementary abelian**, and of
order `p²`.

Proof: apply Lemma 4.5(c) to `↥S` to get `Z = Ω₁(Z₂(↥S))` with `|Z| ≥ p²` and exponent `p`.
`Z` is characteristic in `↥S` and `S ⊴ R`, so `Z' := Z.map S.subtype ⊴ R` (a `p`-group of order
`≥ p²`). By Lemma 1.22 (`normal_subgroup_card_pow_le_of_pGroup`) `Z'` contains an `R`-normal
subgroup `L` of order `p²`; `L ≤ Z'` has exponent `p`, so (being of order `p²`) it is elementary
abelian, and `L ≤ Z' ≤ S`. -/
theorem exists_normal_isElementaryAbelian_card_prime_sq_le_of_normal_not_isCyclic
    (hR : IsPGroup p R) (hp_odd : Odd p) {S : Subgroup R} [S.Normal]
    (hSnc : ¬ IsCyclic ↥S) :
    ∃ L : Subgroup R, L ≤ S ∧ L.Normal ∧ L.IsElementaryAbelian p ∧ Nat.card L = p ^ 2 := by
  have hp : p.Prime := Fact.out
  haveI hSpg : IsPGroup p ↥S := hR.to_subgroup S
  -- `Z = Ω₁(Z₂(↥S))`, characteristic in `↥S`, with `|Z| ≥ p²`.
  have hZcard_ge : p ^ 2 ≤ Nat.card ↥(omega1UpperCentralTwo ↥S p) :=
    card_prime_sq_le_omega1UpperCentralTwo_of_not_isCyclic hSpg hp_odd hSnc
  -- `Z' = Z.map S.subtype ⊴ R`.
  haveI hZ'norm : ((omega1UpperCentralTwo ↥S p).map S.subtype).Normal :=
    normal_map_subtype_of_characteristic inferInstance
  -- Exponent `p` on `Z'`.
  have hZ'_exp : ∀ g ∈ (omega1UpperCentralTwo ↥S p).map S.subtype, g ^ p = 1 := by
    intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨z', hz', rfl⟩ := hg
    have hz'p : z' ^ p = 1 := pow_eq_one_of_mem_omega1UpperCentralTwo hp_odd hz'
    rw [← map_pow, hz'p, map_one]
  -- `p² ∣ |Z'|` (a `p`-group of order `≥ p²`).
  have hZ'card : Nat.card ↥((omega1UpperCentralTwo ↥S p).map S.subtype)
      = Nat.card ↥(omega1UpperCentralTwo ↥S p) :=
    Subgroup.card_map_of_injective S.subtype_injective
  have hZ'pg : IsPGroup p ↥((omega1UpperCentralTwo ↥S p).map S.subtype) :=
    hR.to_subgroup _
  have hp2_dvd : p ^ 2 ∣ Nat.card ↥((omega1UpperCentralTwo ↥S p).map S.subtype) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hZ'pg
    have hge : p ^ 2 ≤ p ^ k := by rw [← hk, hZ'card]; exact hZcard_ge
    have hk2 : 2 ≤ k := by
      by_contra hlt
      rw [not_le] at hlt
      have hle : p ^ k ≤ p ^ 1 := pow_le_pow_right₀ hp.one_lt.le (by omega : k ≤ 1)
      have hgt : p ^ 1 < p ^ 2 := by
        simpa using pow_lt_pow_right₀ hp.one_lt (by norm_num : (1 : ℕ) < 2)
      omega
    rw [hk]; exact pow_dvd_pow p hk2
  -- Lemma 1.22: extract an `R`-normal `L ≤ Z'` of order `p²`.
  obtain ⟨L, hLnorm, hL_le_Z', hLcard⟩ :=
    OddOrder.BG.Ch1.S01.normal_subgroup_card_pow_le_of_pGroup hR
      (N := (omega1UpperCentralTwo ↥S p).map S.subtype) hp2_dvd
  have hL_le_S : L ≤ S := hL_le_Z'.trans (Subgroup.map_subtype_le _)
  -- `L` has exponent `p` (subgroup of the exponent-`p` group `Z'`).
  have hL_exp : ∀ x : ↥L, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hZ'_exp (x : R) (hL_le_Z' x.2)
  -- `L` of order `p²` with exponent `p` is noncyclic, hence elementary abelian.
  have hL_nc : ¬ IsCyclic ↥L := by
    intro hcyc
    haveI := hcyc
    have h2 : Monoid.exponent ↥L ∣ p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hL_exp
    rw [IsCyclic.exponent_eq_card, hLcard] at h2
    have hp_lt_sq : p < p ^ 2 := by
      simpa using pow_lt_pow_right₀ hp.one_lt (by norm_num : (1 : ℕ) < 2)
    exact (Nat.not_dvd_of_pos_of_lt hp.pos hp_lt_sq) h2
  have hL_ea : L.IsElementaryAbelian p :=
    IsElementaryAbelian.of_card_prime_sq_of_not_isCyclic hp hLcard hL_nc
  exact ⟨L, hL_le_S, hLnorm, hL_ea, hLcard⟩

end OddOrder.BG.Ch1.S04
