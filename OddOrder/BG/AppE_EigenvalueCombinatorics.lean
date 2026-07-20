/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_AbelianCentralizer

/-!
# BG Appendix E, Proposition E.4: the combinatorics of `(E.24)`–`(E.27)`

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, pp. 163–164.

`AppE_AbelianCentralizer` proves the general lemmas behind the abelian clause of Proposition
E.4 — the eigenvalue algebra `(E.20)`/`(E.21)`, the two-slot Lemma 4.2 step
`(E.26)`/`(E.27)`, the closing arithmetic, and the *shapes* of BG's index extractions.  This
file **feeds Step 2's chain into them**:

> Take `k` minimal such that `T/H_k` is not abelian.  Then `⁅H₀,H₀⁆H_k = T'H_k = H_{k-1}`
> `(E.24)`.  Now take `i` maximal such that `⁅Hᵢ,T⁆ ⊄ H_k` and `j` maximal such that
> `⁅Hᵢ,Hⱼ⁆ ⊄ H_k`.  Then `0 ≤ j ≤ i ≤ k-2` and `⁅wᵢ,wⱼ⁆ ∈ H_{k-1} − H_k`  `(E.25)`.

with `Hₐ = ⁅…⁅T, S⁆, …, S⁆` (`Isaacs.Ch04.iterCommutator T ⊤ a`, `T = C_S(Ω₁(Z₂(S)))`) and
`wₐ = ⁅…⁅w, v⁆, …, v⁆` (`commutatorIterate w v a`) BG's sequences from `(E.9)`.

Three things are supplied here:

* `sup_zpowers_commutatorIterate` — BG's `(E.19)` `Hₐ = ⟨wₐ⟩H_{a+1}` along the chain, the
  `hgen` input of `commutator_le_of_generators`;
* `add_two_le_of_iterCommutator_ne_bot` — BG's `k ≤ q − 1` out of `|T|·p = |S| ≤ p^q`;
* `exists_commutator_indices` — the whole of `(E.25)`, `k`/`i`/`j` together with the range
  `1 ≤ i`, `j ≤ i`, `i + 2 ≤ k` (hence `3 ≤ k`), the two cross-term inclusions that kill the
  error terms in Lemma 4.2, and the witness `⁅wᵢ, wⱼ⁆ ∉ H_k`.

The lower bound `3 ≤ k` is the one BG does not state; it is what rules out the alternative
recursion in `(E.23)` (see `commutator_self_le_of_generator`).
-/

namespace OddOrder.BG.AppE

open OddOrder.GroupTheory OddOrder.Isaacs.Ch03
open scoped commutatorElement Pointwise

variable {R B : Type*} [Group R] [Group B] {p q : ℕ}

/-! ## `(E.19)` along the chain: `Hₐ = ⟨wₐ⟩ H_{a+1}` -/

/-- **BG `(E.19)` along Step 2's chain**: `Hₐ = ⟨wₐ⟩·H_{a+1}` for every `a`.

`sup_zpowers_eq_of_card_eq_prime_mul` applied to `|Hₐ| = p·|H_{a+1}|` (`(E.6)`) and
`wₐ ∈ Hₐ − H_{a+1}` (`(E.9)`).  Below the end of the chain both sides are trivial, so no
liveness hypothesis is needed — which matters, because `commutator_le_of_generators` consumes
this at the indices `i` and `j` produced by `(E.25)`, where liveness is only implicit. -/
theorem RegularOperatorSetup.sup_zpowers_commutatorIterate [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p)
    {v : ↥S} (hv : Subgroup.zpowers v = hyp.R₀.subgroupOf S)
    {w : ↥S} (hw : w ∈ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S))
    (hw1 : w ∉ OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) 1)
    (a : ℕ) :
    Subgroup.zpowers (commutatorIterate w v a) ⊔
        OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
          (a + 1) =
      OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) a := by
  set T : Subgroup ↥S := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hT
  by_cases hne : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) a = ⊥
  · -- Past the end of the chain both sides are trivial.
    have hsucc : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (a + 1) = ⊥ :=
      le_bot_iff.mp ((iterCommutator_antitone a).trans (le_of_eq hne))
    have hw0 : commutatorIterate w v a = 1 := by
      have := commutatorIterate_mem_chain (T := T) (v := v) hw a
      rw [hne] at this
      simpa using this
    rw [hne, hsucc, hw0]
    simp
  · exact sup_zpowers_eq_of_card_eq_prime_mul hyp.p_prime (iterCommutator_antitone a)
      (hyp.card_iterCommutator_eq hR₀S hexp hS (le_refl T) hne)
      (commutatorIterate_mem_chain hw a)
      (hyp.commutatorIterate_not_mem hR₀S hexp hS hv hw hw1 a hne)

/-! ## `k ≤ q − 1`

BG: *"Now `p^k = |T/H_k| ≤ |T| = pⁿ = |S|/p < p^{q-1}` by Theorem E.3(c), so `k ≤ q − 1`."*
-/

/-- **BG's `k ≤ q − 1`**, in the sharper form the chain actually gives: if `H_k ≠ 1` then
`k + 2 ≤ q`.

`|T| = p^k·|H_k|` (`card_start_eq_pow_mul`) and `|H_k| = p·|H_{k+1}| ≥ p` (`(E.6)`), so
`p^{k+1} ≤ |T|`; and `|T|·p ≤ p^q` is E.3(c) with `|S : T| = p`.  Proposition E.4 uses it at
the index `k − 1`, where it reads `k + 1 ≤ q` — exactly the `m + 2 ≤ q` that
`eq_of_eigenvalue_relations` wants for `m = k − 1`. -/
theorem RegularOperatorSetup.add_two_le_of_iterCommutator_ne_bot [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) (hcard : p ^ 4 ≤ Nat.card ↥(Omega R p 1)) {k : ℕ}
    (hne : OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1)))
      (⊤ : Subgroup ↥(Omega R p 1)) k ≠ ⊥) :
    k + 2 ≤ q := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set S : Subgroup R := Omega R p 1 with hSdef
  set T : Subgroup ↥S := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hT
  have hS3 : 3 ≤ pRank ↥S p := hyp.three_le_pRank_omega hcard
  have hstart := hyp.card_start_eq_pow_mul hyp.R₀_le_omega hyp.omega_pow_eq_one' hS3
    (le_refl T) k hne
  have hstep := hyp.card_iterCommutator_eq hyp.R₀_le_omega hyp.omega_pow_eq_one' hS3
    (le_refl T) hne
  have hpos : 1 ≤ Nat.card ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (k + 1)) :=
    Nat.card_pos
  have hTge : p ^ (k + 1) ≤ Nat.card ↥T := by
    rw [hstart, hstep, pow_succ]
    calc p ^ k * p = p ^ k * p * 1 := by ring
      _ ≤ p ^ k * p * Nat.card
            ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (k + 1)) := by
          exact Nat.mul_le_mul_left _ hpos
      _ = p ^ k * (p * Nat.card
            ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (k + 1))) := by ring
  have hle : Nat.card ↥T * p ≤ p ^ q := hyp.card_centralizer_mul_prime_le hcard
  have hfinal : p ^ (k + 2) ≤ p ^ q := by
    calc p ^ (k + 2) = p ^ (k + 1) * p := by ring
      _ ≤ Nat.card ↥T * p := Nat.mul_le_mul_right _ hTge
      _ ≤ p ^ q := hle
  exact (Nat.pow_le_pow_iff_right hyp.p_prime.one_lt).mp hfinal

/-! ## `(E.24)`/`(E.25)`: BG's `k`, `i` and `j` along the chain

BG extracts three indices in one breath.  The shapes are in `AppE_AbelianCentralizer`
(`exists_min_index_commutator_not_le`, `exists_max_of_holds_at_zero`,
`range_of_max_commutator_indices`, `commutator_self_le_of_generator`,
`commutator_le_of_generators`); here they are run against a chain given abstractly by the
five facts Step 2 supplies, so that the statement is free of the `RegularOperatorSetup`
plumbing. -/

/-- **BG `(E.25)`**: the indices `k`, `i`, `j` and the witness `⁅wᵢ, wⱼ⁆ ∉ H_k`.

Given a descending chain `H` starting at `T`, stepping by `⁅·, T⁆`, reaching `1`, and
generated level by level by BG's elements `wₐ` (`(E.19)`), and given that `T` is **not**
abelian, there are indices with

* `3 ≤ k`, `1 ≤ i`, `j ≤ i`, `i + 2 ≤ k` — BG's `0 ≤ j ≤ i ≤ k − 2`, plus the lower bounds
  BG leaves implicit;
* `T' ≤ H_{k-1}` and `T' ⊄ H_k` — the minimality of `k`, i.e. `(E.24)`;
* `⁅H_{i+1}, H_j⁆ ≤ H_k` and `⁅H_i, H_{j+1}⁆ ≤ H_k` — the maximality of `i` and `j`, which is
  what kills the two error terms in the Lemma 4.2 step `(E.26)`/`(E.27)`;
* `⁅wᵢ, wⱼ⁆ ∉ H_k` — BG's `⁅wᵢ,wⱼ⁆ ∈ H_{k-1} − H_k` (the `∈ H_{k-1}` half is `T' ≤ H_{k-1}`).

`1 ≤ i` is the diagonal case of `commutator_le_of_generators`: were `i = 0`, then `j = 0`
too, and `⁅w₀, w₀⁆ = 1` would force `T' ≤ H_k`, against the minimality of `k`. -/
theorem exists_commutator_indices {G : Type*} [Group G] {T : Subgroup G}
    {H : ℕ → Subgroup G} {w : ℕ → G} (hnorm : ∀ a, (H a).Normal)
    (h0 : H 0 = T) (hanti : ∀ a b : ℕ, a ≤ b → H b ≤ H a)
    (hstep : ∀ a : ℕ, ⁅H a, T⁆ ≤ H (a + 1))
    (hgen : ∀ a : ℕ, H a ≤ Subgroup.zpowers (w a) ⊔ H (a + 1))
    (hwmem : ∀ a : ℕ, w a ∈ H a)
    {n : ℕ} (hn : H n = ⊥) (hne : ⁅T, T⁆ ≠ ⊥) :
    ∃ k i j : ℕ, 3 ≤ k ∧ 1 ≤ i ∧ j ≤ i ∧ i + 2 ≤ k ∧
      ⁅T, T⁆ ≤ H (k - 1) ∧ ¬ (⁅T, T⁆ ≤ H k) ∧
      ⁅H (i + 1), H j⁆ ≤ H k ∧ ⁅H i, H (j + 1)⁆ ≤ H k ∧ ⁅w i, w j⁆ ∉ H k := by
  classical
  haveI : ∀ a, (H a).Normal := hnorm
  have hT : ∀ a : ℕ, H a ≤ T := fun a => h0 ▸ hanti 0 a (Nat.zero_le a)
  -- BG's minimal `k`.
  obtain ⟨k, hk1, hkle, hkspec⟩ := exists_min_index_commutator_not_le h0 hn hne
  -- BG's maximal `i`: `⁅H i, T⁆ ⊄ H k`.
  have hP0 : ¬ (⁅H 0, T⁆ ≤ H k) := by rw [h0]; exact hkspec
  obtain ⟨i, hi, himax'⟩ :=
    exists_max_of_holds_at_zero (P := fun a => ¬ (⁅H a, T⁆ ≤ H k)) hP0 (n := k)
      (fun m hm => not_not_intro ((hstep m).trans (hanti k (m + 1) (by omega))))
  have himax : ∀ m : ℕ, i < m → ⁅H m, T⁆ ≤ H k := fun m hm => not_not.mp (himax' m hm)
  -- BG's maximal `j`: `⁅H i, H j⁆ ⊄ H k`.
  have hQ0 : ¬ (⁅H i, H 0⁆ ≤ H k) := by rw [h0]; exact hi
  obtain ⟨j, hj, hjmax'⟩ :=
    exists_max_of_holds_at_zero (P := fun b => ¬ (⁅H i, H b⁆ ≤ H k)) hQ0 (n := k)
      (fun m hm => not_not_intro (by
        calc ⁅H i, H m⁆ ≤ ⁅T, H m⁆ := Subgroup.commutator_mono (hT i) le_rfl
          _ = ⁅H m, T⁆ := Subgroup.commutator_comm _ _
          _ ≤ H (m + 1) := hstep m
          _ ≤ H k := hanti k (m + 1) (by omega)))
  have hjmax : ∀ m : ℕ, j < m → ⁅H i, H m⁆ ≤ H k := fun m hm => not_not.mp (hjmax' m hm)
  -- BG's `(E.25)` range.
  obtain ⟨hji, hik⟩ := range_of_max_commutator_indices hanti hT hstep hi himax hj
  -- The two cross terms that maximality kills.
  have hcross_left : ⁅H (i + 1), H j⁆ ≤ H k :=
    (Subgroup.commutator_mono le_rfl (hT j)).trans (himax (i + 1) (Nat.lt_succ_self i))
  have hcross_right : ⁅H i, H (j + 1)⁆ ≤ H k := hjmax (j + 1) (Nat.lt_succ_self j)
  -- `i = 0` is impossible: then `j = 0` and `⁅w₀, w₀⁆ = 1` collapses `T'` into `H k`.
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with hi0 | hpos
    · exfalso
      have hj0 : j = 0 := Nat.le_zero.mp (hi0 ▸ hji)
      refine hkspec ?_
      have h1 : ⁅H 1, T⁆ ≤ H k := himax 1 (by omega)
      have h2 : ⁅T, H 1⁆ ≤ H k := by
        rw [Subgroup.commutator_comm]; exact h1
      haveI : (H 1).Normal := hnorm 1
      have := commutator_self_le_of_generator (A := T) (A' := H 1) (K := H k) (w := w 0)
        (h0 ▸ hwmem 0) (hT 1) (h0 ▸ hgen 0) h1 h2
      exact this
    · exact hpos
  -- BG's `⁅wᵢ, wⱼ⁆ ∉ H_k`, by contraposing `commutator_le_of_generators`.
  have hwij : ⁅w i, w j⁆ ∉ H k := by
    intro hmem
    exact hj (commutator_le_of_generators (hwmem i) (hwmem j) (hanti j (j + 1) (by omega))
      (hgen i) (hgen j) hcross_left hcross_right hmem)
  exact ⟨k, i, j, by omega, hi1, hji, hik, hkle, hkspec, hcross_left, hcross_right, hwij⟩

/-- **BG `(E.25)` along Step 2's chain**: `exists_commutator_indices` with all five chain
facts discharged.

Antitonicity is `iterCommutator_le_of_le`, the step is `iterCommutator_commutator_le_succ`,
generation is `(E.19)` (`sup_zpowers_commutatorIterate`), membership is `(E.9)`
(`commutatorIterate_mem_chain`), and the chain reaches `1` because `S` is a finite `p`-group,
hence nilpotent. -/
theorem RegularOperatorSetup.exists_commutator_indices_chain [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p)
    {v : ↥S} (hv : Subgroup.zpowers v = hyp.R₀.subgroupOf S)
    {w : ↥S} (hw : w ∈ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S))
    (hw1 : w ∉ OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) 1)
    (hnonab : ⁅Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S),
      Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)⁆ ≠ ⊥) :
    ∃ k i j : ℕ, 3 ≤ k ∧ 1 ≤ i ∧ j ≤ i ∧ i + 2 ≤ k ∧
      ⁅Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S),
        Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)⁆ ≤
        OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
          (k - 1) ∧
      ¬ (⁅Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S),
          Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)⁆ ≤
        OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) k) ∧
      ⁅OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
          (i + 1),
        OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) j⁆ ≤
        OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) k ∧
      ⁅OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i,
        OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
          (j + 1)⁆ ≤
        OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) k ∧
      ⁅commutatorIterate w v i, commutatorIterate w v j⁆ ∉
        OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) k := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  haveI : Group.IsNilpotent ↥S := IsPGroup.isNilpotent (hyp.R_pGroup.to_subgroup S)
  set T : Subgroup ↥S := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hT
  obtain ⟨n, hn⟩ :=
    OddOrder.Isaacs.Ch04.iterCommutator_eq_bot_of_isNilpotent_ambient T (⊤ : Subgroup ↥S)
  exact exists_commutator_indices
    (H := fun a => OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) a)
    (w := fun a => commutatorIterate w v a)
    (fun a => inferInstance) rfl (fun _ _ hab => iterCommutator_le_of_le hab)
    (fun a => iterCommutator_commutator_le_succ T a)
    (fun a => (hyp.sup_zpowers_commutatorIterate hR₀S hexp hS hv hw hw1 a).ge)
    (fun a => commutatorIterate_mem_chain hw a) hn hnonab

/-! ## `(E.26)`/`(E.27)`: the Lemma 4.2 step, fed from `(E.22)`/`(E.23)`

BG: *"By `(E.22)`, there exist `x ∈ Hᵢ₊₁` and `x' ∈ Hⱼ₊₁` such that `wᵢᵅ = wᵢ^{rᵢ}x` and
`wⱼᵅ = wⱼ^{rⱼ}x'`.  Also `⁅wᵢ,wⱼ⁆ ∈ H_{k-1}`, so `⁅wᵢ,wⱼ⁆ᵅ ≡ ⁅wᵢ,wⱼ⁆^{r_{k-1}} (mod H_k)`.
By Lemma 4.2, `⁅wᵢ,wⱼ⁆ᵅ ≡ ⁅wᵢ,wⱼ⁆^{rᵢrⱼ} (mod H_k)`.  Therefore, by `(E.25)`,
`rᵢrⱼ = r_{k-1}`."*

`dvd_sub_mul_of_commutator_eigen` is that computation once everything has been pushed into
`G/H_k`; the lemma below does the pushing, in exactly the shape `exists_eigenvalue_pow`
delivers its conclusion — `(y^s)⁻¹·yᵅ ∈ H_{a+1}` rather than an equation. -/

/-- **BG `(E.26)`/`(E.27)`**, operator-agnostic and stated against the chain data.

`σ` scales `x` and `y` up to errors landing in `Ai` and `Bj`, and scales `⁅x,y⁆` exactly
modulo `K`.  The three cross-term hypotheses are the maximality of BG's `i` and `j`, which is
what makes the errors invisible in `G/K`; `hcenter` is `⁅x,y⁆ ∈ H_{k-1}` together with
`H_{k-1}/H_k ≤ Z(S/H_k)`.  The conclusion is BG's `rᵢrⱼ = r_{k-1}` (resp. `tᵢtⱼ = t_{k-1}`)
as a congruence of exponents mod `p`. -/
theorem dvd_sub_mul_of_chain_eigenvalues {G : Type*} [Group G] {pp : ℕ} (hp : pp.Prime)
    {K L Ai Bj : Subgroup G} [K.Normal] (σ : G →* G)
    (hcenter : L.map (QuotientGroup.mk' K) ≤ Subgroup.center (G ⧸ K))
    {x y : G} (hxy : ⁅x, y⁆ ∈ L) (hnotmem : ⁅x, y⁆ ∉ K) (hexp : ⁅x, y⁆ ^ pp = 1)
    (hAy : ∀ u ∈ Ai, ⁅u, y⁆ ∈ K) (hAB : ∀ u ∈ Ai, ∀ u' ∈ Bj, ⁅u, u'⁆ ∈ K)
    (hxB : ∀ u' ∈ Bj, ⁅x, u'⁆ ∈ K)
    {m n c : ℤ}
    (hσx : (x ^ m)⁻¹ * σ x ∈ Ai) (hσy : (y ^ n)⁻¹ * σ y ∈ Bj)
    (hσxy : (⁅x, y⁆ ^ c)⁻¹ * σ ⁅x, y⁆ ∈ K) :
    (pp : ℤ) ∣ m * n - c := by
  -- Membership in `K` is commutation in `G/K`.
  have hcomm : ∀ a b : G, ⁅a, b⁆ ∈ K →
      Commute ((QuotientGroup.mk' K) a) ((QuotientGroup.mk' K) b) := by
    intro a b h
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr h
  have hu : Commute ((QuotientGroup.mk' K) ((x ^ m)⁻¹ * σ x)) ((QuotientGroup.mk' K) y) :=
    hcomm _ _ (hAy _ hσx)
  have huv : Commute ((QuotientGroup.mk' K) ((x ^ m)⁻¹ * σ x))
      ((QuotientGroup.mk' K) ((y ^ n)⁻¹ * σ y)) :=
    hcomm _ _ (hAB _ hσx _ hσy)
  have hv : Commute ((QuotientGroup.mk' K) ((y ^ n)⁻¹ * σ y)) ((QuotientGroup.mk' K) x) :=
    (hcomm _ _ (hxB _ hσy)).symm
  have hz : ⁅(QuotientGroup.mk' K) x, (QuotientGroup.mk' K) y⁆ ∈ Subgroup.center (G ⧸ K) := by
    rw [← map_commutatorElement]
    exact hcenter ⟨⁅x, y⁆, hxy, rfl⟩
  have hexpq : ⁅(QuotientGroup.mk' K) x, (QuotientGroup.mk' K) y⁆ ^ pp = 1 := by
    rw [← map_commutatorElement, ← map_pow, hexp, map_one]
  have hne : ⁅(QuotientGroup.mk' K) x, (QuotientGroup.mk' K) y⁆ ≠ 1 := by
    rw [← map_commutatorElement]
    exact fun h => hnotmem ((QuotientGroup.eq_one_iff _).mp h)
  -- `σ` in the quotient: exact on `x` and `y` up to the errors, exact on `⁅x, y⁆`.
  have hx' : ((QuotientGroup.mk' K) x) ^ m * (QuotientGroup.mk' K) ((x ^ m)⁻¹ * σ x) =
      (QuotientGroup.mk' K) (σ x) := by
    rw [← map_zpow, ← map_mul]
    congr 1
    group
  have hy' : ((QuotientGroup.mk' K) y) ^ n * (QuotientGroup.mk' K) ((y ^ n)⁻¹ * σ y) =
      (QuotientGroup.mk' K) (σ y) := by
    rw [← map_zpow, ← map_mul]
    congr 1
    group
  have hc' : (QuotientGroup.mk' K) (σ ⁅x, y⁆) =
      ⁅(QuotientGroup.mk' K) x, (QuotientGroup.mk' K) y⁆ ^ c := by
    have h1 : (QuotientGroup.mk' K) ((⁅x, y⁆ ^ c)⁻¹ * σ ⁅x, y⁆) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hσxy
    rw [map_mul, map_inv, map_zpow, inv_mul_eq_one] at h1
    rw [← map_commutatorElement, ← h1]
  have hsigma : ⁅((QuotientGroup.mk' K) x) ^ m * (QuotientGroup.mk' K) ((x ^ m)⁻¹ * σ x),
      ((QuotientGroup.mk' K) y) ^ n * (QuotientGroup.mk' K) ((y ^ n)⁻¹ * σ y)⁆ =
      ⁅(QuotientGroup.mk' K) x, (QuotientGroup.mk' K) y⁆ ^ c := by
    rw [hx', hy', ← map_commutatorElement, ← map_commutatorElement σ x y]
    exact hc'
  exact dvd_sub_mul_of_commutator_eigen hp hu huv hv hz hexpq hne hsigma

/-- **BG `(E.26)`, assembled against Step 2's chain**: with `α`'s eigenvalues `r`, `r₀`,
`rᵢrⱼ = r_{k-1}` in `ZMod p`, i.e. `(r₀rⁱ)(r₀rʲ) = r₀r^{k-1}`.

Every ingredient of `dvd_sub_mul_of_chain_eigenvalues` is discharged from the chain: the
scaling data at `i`, `j`, `k−1` is `exists_eigenvalue_pow` (BG's `(E.22)`); the three
cross-term inclusions are the maximality of `i`, `j` in `(E.25)`; the centrality is
`chain_map_le_center`; and the exponent `⁅wᵢ,wⱼ⁆^p = 1` is the exponent-`p` hypothesis on
`S`.  The output is BG's `rᵢrⱼ = r_{k-1}` (`(E.26)`) as a `ZMod p` equation among the
eigenvalues, the only remaining move being the passage to `(ZMod p)ˣ` with `orderOf r = q`. -/
theorem RegularOperatorSetup.dvd_sub_mul_eigenvalues_chain [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p)
    (hSinv : IsAInvariant (hyp.act.comp hyp.A.subtype) S)
    {a : B} (ha : a ∈ hyp.A)
    {v : ↥S} (hv : Subgroup.zpowers v = hyp.R₀.subgroupOf S)
    {w : ↥S} (hw : w ∈ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S))
    (hw1 : w ∉ OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) 1)
    {r r₀ : ℤ} (hr : (hSinv.restrict ⟨a, ha⟩) v = v ^ r)
    (hr₀ : ∀ y ∈ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) 0,
      (y ^ r₀)⁻¹ * (hSinv.restrict ⟨a, ha⟩) y ∈ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) 1)
    (hnonab : ⁅Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S),
      Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)⁆ ≠ ⊥)
    {k i j : ℕ} (hi1 : 1 ≤ i) (hji : j ≤ i) (hik : i + 2 ≤ k)
    (hTle : ⁅Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S),
        Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)⁆ ≤
      OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) (k - 1))
    (hcl : ⁅OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) (i + 1),
        OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) j⁆ ≤
      OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) k)
    (hcr : ⁅OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i,
        OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
          (j + 1)⁆ ≤
      OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) k)
    (hwij : ⁅commutatorIterate w v i, commutatorIterate w v j⁆ ∉
      OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) k) :
    ((r₀ : ZMod p) * (r : ZMod p) ^ i) * ((r₀ : ZMod p) * (r : ZMod p) ^ j) =
      (r₀ : ZMod p) * (r : ZMod p) ^ (k - 1) := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set T : Subgroup ↥S := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hT
  haveI hTchar : T.Characteristic := by rw [hT]; infer_instance
  -- Work with `k = d + 1` so that `H k = H (d+1)` and `H (k-1) = H d` hold definitionally.
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  set σ : ↥S →* ↥S := (hSinv.restrict ⟨a, ha⟩ : MulAut ↥S).toMonoidHom with hσ
  -- Liveness of the relevant chain terms.
  have hlive_d : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) d ≠ ⊥ := fun h =>
    hnonab (le_bot_iff.mp (hTle.trans (le_of_eq h)))
  have hlive_i : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i ≠ ⊥ :=
    iterCommutator_ne_bot_of_le (by omega) hlive_d
  have hlive_j : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) j ≠ ⊥ :=
    iterCommutator_ne_bot_of_le (by omega) hlive_d
  -- BG's `(E.22)` eigenvalue supply at `i`, `j`, `d = k − 1`.
  have hep := hyp.exists_eigenvalue_pow hR₀S hexp hS hSinv ha hv hw hw1 hr hr₀
  obtain ⟨si, hsi_cong, hsi_mem⟩ := hep i hlive_i
  obtain ⟨sj, hsj_cong, hsj_mem⟩ := hep j hlive_j
  obtain ⟨sd, hsd_cong, hsd_mem⟩ := hep d hlive_d
  -- BG's `⁅wᵢ, wⱼ⁆ ∈ H_{k-1}`.
  have hwiT : commutatorIterate w v i ∈ T := iterCommutator_le_base i (commutatorIterate_mem_chain hw i)
  have hwjT : commutatorIterate w v j ∈ T := iterCommutator_le_base j (commutatorIterate_mem_chain hw j)
  have hxy : ⁅commutatorIterate w v i, commutatorIterate w v j⁆ ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) d :=
    hTle (Subgroup.commutator_mem_commutator hwiT hwjT)
  -- The Lemma 4.2 step in `S / H_k`.
  have hdvd : (p : ℤ) ∣ si * sj - sd := by
    refine dvd_sub_mul_of_chain_eigenvalues hyp.p_prime σ (chain_map_le_center T d) hxy hwij
      (hexp _) ?_ ?_ ?_ (hsi_mem _ (commutatorIterate_mem_chain hw i))
      (hsj_mem _ (commutatorIterate_mem_chain hw j)) (hsd_mem _ hxy)
    · exact fun u hu =>
        hcl (Subgroup.commutator_mem_commutator hu (commutatorIterate_mem_chain hw j))
    · exact fun u hu u' hu' =>
        hcl (Subgroup.commutator_mem_commutator hu ((iterCommutator_antitone j) hu'))
    · exact fun u' hu' =>
        hcr (Subgroup.commutator_mem_commutator (commutatorIterate_mem_chain hw i) hu')
  -- Cast the divisibility into `ZMod p` and substitute the eigenvalue congruences.
  have hzmod : (si : ZMod p) * (sj : ZMod p) = (sd : ZMod p) := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (si * sj - sd) p).mpr hdvd
    push_cast at this
    linear_combination this
  rw [hsi_cong, hsj_cong] at hzmod
  rw [hzmod, hsd_cong, Nat.add_sub_cancel]

/-! ## The closing arithmetic, in the shape the chain delivers it

`eq_of_eigenvalue_relations` is stated for the bare relations `r^{i+j+1} = r^m` and
`t₀t^{i+j} = t^m`.  What `(E.26)`/`(E.27)` actually produce is `rᵢrⱼ = r_{k-1}` with
`rₐ = r₀rᵃ` — and `r₀ = r` after `dvd_sub_eigenvalues`.  Peeling the extra factor off each
side is the only difference. -/

/-- **BG Proposition E.4, the ending**, with the eigenvalues in chain form.

`rₐ = r·rᵃ` (using `r₀ = r`) and `tₐ = t₀·tᵃ`, so `(E.26)` and `(E.27)` read as the two
displayed products; cancelling one `r` resp. one `t₀` recovers the hypotheses of
`eq_of_eigenvalue_relations`, whose conclusion `t₀ = t` contradicts `(E.21)`. -/
theorem eq_of_chain_eigenvalue_relations {pp qq : ℕ} {r t t₀ : (ZMod pp)ˣ}
    (hord : orderOf r = qq) {i j m : ℕ} (hji : j ≤ i) (him : i + 1 ≤ m) (hmq : m + 2 ≤ qq)
    (hE26 : (r * r ^ i) * (r * r ^ j) = r * r ^ m)
    (hE27 : (t₀ * t ^ i) * (t₀ * t ^ j) = t₀ * t ^ m) :
    t₀ = t := by
  refine eq_of_eigenvalue_relations hord hji him hmq ?_ ?_
  · have e1 : (r * r ^ i) * (r * r ^ j) = r ^ (i + j + 2) := by
      rw [← pow_succ' r i, ← pow_succ' r j, ← pow_add]
      congr 1
      omega
    rw [e1] at hE26
    refine mul_left_cancel (a := r) ?_
    rw [← pow_succ' r (i + j + 1)]
    exact hE26
  · refine mul_left_cancel (a := t₀) ?_
    calc t₀ * (t₀ * t ^ (i + j)) = t₀ * t₀ * t ^ (i + j) := (mul_assoc _ _ _).symm
      _ = t₀ * t₀ * (t ^ i * t ^ j) := by rw [pow_add]
      _ = (t₀ * t ^ i) * (t₀ * t ^ j) := mul_mul_mul_comm _ _ _ _
      _ = t₀ * t ^ m := hE27

/-! ## `(E.27)`: the β side of the cross-term relation, gated on the eigenvalue supply

The α assembly `dvd_sub_mul_eigenvalues_chain` discharges its eigenvalue supply with
`exists_eigenvalue_pow`, whose induction uses that **`α` fixes `R₀`** (`α v = v ^ r`).  BG's
`β` does *not* fix `R₀` — that is `(E.18)` — so its supply, BG's `(E.23)`
`wᵢ^β ≡ wᵢ^{tᵢ} (mod Hᵢ₊₁)` with `tᵢ = t₀ tⁱ`, has to be produced by the Case A/B argument
(issue 3021, session (43)).  *Everything downstream of that supply is operator-agnostic*:
the lemma below is the α computation with the operator `σ` and its supply abstracted, so
`σ = β` plugs straight in once `(E.23)` is available.  This is what "putting
`dvd_sub_mul_of_chain_eigenvalues` in a form applicable to `σ = β`" means. -/

/-- **BG `(E.26)`/`(E.27)`, assembled from an abstract eigenvalue supply**.

For a characteristic subgroup `T` of any group `G`, an operator `σ`, and a *supply* scaling
each live chain term `Hₐ = ⁅…⁅T,G⁆,…⁆` by `t₀ tᵃ` up to `Hₐ₊₁` (BG's `(E.22)`/`(E.23)`), the
cross-term relation `(t₀ tⁱ)(t₀ tʲ) = t₀ t^{k−1}` holds in `ZMod pp`.

* `σ = α`, `t₀ = r₀`, `t = r`, supply from `exists_eigenvalue_pow` ⟹ `(E.26)` — the content
  of `dvd_sub_mul_eigenvalues_chain`;
* `σ = β`, supply from `(E.23)` ⟹ `(E.27)`.

Same proof as the α case: `dvd_sub_mul_of_chain_eigenvalues` fed at `i`, `j`, `k−1`, whose
cross-term hypotheses are the maximality inclusions `hcl`, `hcr` of `(E.25)`, whose centrality
is `chain_map_le_center`, and whose exponent input is `hexpT`. -/
theorem dvd_sub_mul_of_chain_supply {G : Type*} [Group G] {pp : ℕ} (hp : pp.Prime)
    {T : Subgroup G} [T.Characteristic] (σ : G →* G) {w v : G} (hw : w ∈ T)
    (hexpT : ∀ y ∈ T, y ^ pp = 1) {t t₀ : ℤ}
    (hsupply : ∀ a : ℕ, OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) a ≠ ⊥ →
      ∃ s : ℤ, (s : ZMod pp) = (t₀ : ZMod pp) * (t : ZMod pp) ^ a ∧
        ∀ y ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) a,
          (y ^ s)⁻¹ * σ y ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + 1))
    (hnonab : ⁅T, T⁆ ≠ ⊥) {k i j : ℕ} (hji : j ≤ i) (hik : i + 2 ≤ k)
    (hTle : ⁅T, T⁆ ≤ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (k - 1))
    (hcl : ⁅OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 1),
        OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) j⁆ ≤
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) k)
    (hcr : ⁅OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i,
        OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (j + 1)⁆ ≤
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) k)
    (hwij : ⁅commutatorIterate w v i, commutatorIterate w v j⁆ ∉
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) k) :
    ((t₀ : ZMod pp) * (t : ZMod pp) ^ i) * ((t₀ : ZMod pp) * (t : ZMod pp) ^ j) =
      (t₀ : ZMod pp) * (t : ZMod pp) ^ (k - 1) := by
  haveI : Fact pp.Prime := ⟨hp⟩
  -- Work with `k = d + 1` so that `H k` and `H (k-1) = H d` hold definitionally.
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  -- Liveness of the relevant chain terms.
  have hlive_d : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) d ≠ ⊥ := fun h =>
    hnonab (le_bot_iff.mp (hTle.trans (le_of_eq h)))
  have hlive_i : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i ≠ ⊥ :=
    iterCommutator_ne_bot_of_le (by omega) hlive_d
  have hlive_j : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) j ≠ ⊥ :=
    iterCommutator_ne_bot_of_le (by omega) hlive_d
  -- The supply at `i`, `j`, `d = k − 1`.
  obtain ⟨si, hsi_cong, hsi_mem⟩ := hsupply i hlive_i
  obtain ⟨sj, hsj_cong, hsj_mem⟩ := hsupply j hlive_j
  obtain ⟨sd, hsd_cong, hsd_mem⟩ := hsupply d hlive_d
  have hwiT : commutatorIterate w v i ∈ T :=
    iterCommutator_le_base i (commutatorIterate_mem_chain hw i)
  have hwjT : commutatorIterate w v j ∈ T :=
    iterCommutator_le_base j (commutatorIterate_mem_chain hw j)
  have hxy : ⁅commutatorIterate w v i, commutatorIterate w v j⁆ ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) d :=
    hTle (Subgroup.commutator_mem_commutator hwiT hwjT)
  have hexpwij : ⁅commutatorIterate w v i, commutatorIterate w v j⁆ ^ pp = 1 := by
    refine hexpT _ ?_
    rw [commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem hwiT hwjT) (T.inv_mem hwiT)) (T.inv_mem hwjT)
  -- The Lemma 4.2 step in `G / H_k`.
  have hdvd : (pp : ℤ) ∣ si * sj - sd := by
    refine dvd_sub_mul_of_chain_eigenvalues hp σ (chain_map_le_center T d) hxy hwij
      hexpwij ?_ ?_ ?_ (hsi_mem _ (commutatorIterate_mem_chain hw i))
      (hsj_mem _ (commutatorIterate_mem_chain hw j)) (hsd_mem _ hxy)
    · exact fun u hu =>
        hcl (Subgroup.commutator_mem_commutator hu (commutatorIterate_mem_chain hw j))
    · exact fun u hu u' hu' =>
        hcl (Subgroup.commutator_mem_commutator hu ((iterCommutator_antitone j) hu'))
    · exact fun u' hu' =>
        hcr (Subgroup.commutator_mem_commutator (commutatorIterate_mem_chain hw i) hu')
  -- Cast the divisibility into `ZMod pp` and substitute the eigenvalue congruences.
  have hzmod : (si : ZMod pp) * (sj : ZMod pp) = (sd : ZMod pp) := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (si * sj - sd) pp).mpr hdvd
    push_cast at this
    linear_combination this
  rw [hsi_cong, hsj_cong] at hzmod
  rw [hzmod, hsd_cong, Nat.add_sub_cancel]

/-! ## From `ZMod p` eigenvalue relations to `t₀ = t`

`eq_of_chain_eigenvalue_relations` lives in `(ZMod p)ˣ`, but the two chain assemblies
(`dvd_sub_mul_eigenvalues_chain` for `α`, `dvd_sub_mul_of_chain_supply` for `β`) deliver ring
equations in `ZMod p` among the integer eigenvalues.  The bridge lifts everything to units:
`α`'s eigenvalue `r` is a unit of order exactly `q` (its `q`-th power is `1` — BG's `(E.9)` —
and it is `≠ 1` — BG's `(E.11)`), and BG's `β`-eigenvalues `t, t₀` are units on the
order-`p` lines they act on. -/

/-- **BG Proposition E.4's ending, from `ZMod p` data**: the two product relations
`(r·rⁱ)(r·rʲ) = r·r^m` and `(t₀·tⁱ)(t₀·tʲ) = t₀·t^m`, read in `ZMod p` with integer
eigenvalues, force `t₀ ≡ t (mod p)`.

The α relation already carries `r₀ = r` (BG's `(E.20)`/`r = r₀`); its eigenvalue is a unit
of order `q` because `r^q ≡ 1` (`(E.9)`) and `r ≢ 1` (`(E.11)`), and the `β`-eigenvalues are
units by hypothesis.  Then `eq_of_chain_eigenvalue_relations` applies verbatim, and its
`(ZMod p)ˣ` conclusion `t₀ = t` pushes back down to `ZMod p`. -/
theorem eq_of_chain_eigenvalue_relations_intCast {p q : ℕ} [Fact p.Prime] (hq : q.Prime)
    {r t t₀ : ℤ} (hrq : (r : ZMod p) ^ q = 1) (hr1 : (r : ZMod p) ≠ 1)
    (htu : IsUnit (t : ZMod p)) (ht₀u : IsUnit (t₀ : ZMod p))
    {i j m : ℕ} (hji : j ≤ i) (him : i + 1 ≤ m) (hmq : m + 2 ≤ q)
    (hE26 : ((r : ZMod p) * (r : ZMod p) ^ i) * ((r : ZMod p) * (r : ZMod p) ^ j) =
      (r : ZMod p) * (r : ZMod p) ^ m)
    (hE27 : ((t₀ : ZMod p) * (t : ZMod p) ^ i) * ((t₀ : ZMod p) * (t : ZMod p) ^ j) =
      (t₀ : ZMod p) * (t : ZMod p) ^ m) :
    (t₀ : ZMod p) = (t : ZMod p) := by
  -- `r` is a unit: `ZMod p` is a field and `r ≠ 0` since `0^q = 0 ≠ 1`.
  have hru : IsUnit (r : ZMod p) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, zero_pow hq.pos.ne'] at hrq
    exact zero_ne_one hrq
  set ru : (ZMod p)ˣ := hru.unit with hrudef
  set tu : (ZMod p)ˣ := htu.unit with htudef
  set t₀u : (ZMod p)ˣ := ht₀u.unit with ht₀udef
  have hrus : (ru : ZMod p) = (r : ZMod p) := hru.unit_spec
  have htus : (tu : ZMod p) = (t : ZMod p) := htu.unit_spec
  have ht₀us : (t₀u : ZMod p) = (t₀ : ZMod p) := ht₀u.unit_spec
  -- `orderOf ru = q`, from `ru^q = 1`, `ru ≠ 1`, `q` prime.
  have hru_q : ru ^ q = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hrus, hrq, Units.val_one]
  have hru_ne : ru ≠ 1 := fun h => hr1 (by rw [← hrus, h, Units.val_one])
  have hord : orderOf ru = q := by
    rcases (Nat.dvd_prime hq).mp (orderOf_dvd_of_pow_eq_one hru_q) with h1 | hq'
    · exact absurd (orderOf_eq_one_iff.mp h1) hru_ne
    · exact hq'
  -- Lift both relations to `(ZMod p)ˣ`.
  have hE26u : (ru * ru ^ i) * (ru * ru ^ j) = ru * ru ^ m := by
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, hrus]
    exact hE26
  have hE27u : (t₀u * tu ^ i) * (t₀u * tu ^ j) = t₀u * tu ^ m := by
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, htus, ht₀us]
    exact hE27
  have := eq_of_chain_eigenvalue_relations hord hji him hmq hE26u hE27u
  rw [← ht₀us, ← htus, this]

/-! ## `(E.23)` the `β`-side supply: the bilinear-commutator foundation

BG's `(E.23)` `wₐ^β ≡ wₐ^{t₀tᵃ} (mod Hₐ₊₁)` is the `β` analogue of `(E.22)`.  Unlike `α`, `β`
does **not** normalise `R₀` (`(E.18)`), so the `α` route `exists_eigenvalue_pow` — whose
induction consumes `β v = v^r` — does not transfer.  BG's recursion instead comes from the
`β`-equivariant bilinear commutator map `Hₐ/Hₐ₊₁ ⊗ S/S' → Hₐ₊₁/Hₐ₊₂` together with the
eigenvalue split `t ≠ t₀` on `S/S' = Q/S' ⊕ T/S'`, in two cases (issue 3021, session (43)):

* **Case A** `⁅Hₐ, T⁆ ≤ Hₐ₊₂`, giving BG's recursion `tₐ₊₁ = tₐ·t`;
* **Case B** `⁅Hₐ, Q'⁆ ≤ Hₐ₊₂`, giving the fatal `tₐ₊₁ = tₐ·t₀`, which **must be excluded**.

This section supplies the operator-agnostic foundations for that argument, all sorry-free:

* `commutator_sup_le_of_le` — "bilinearity modulo `K`": `⁅A, B ⊔ C⁆ ≤ K` from `⁅A, B⁆ ≤ K`,
  `⁅A, C⁆ ≤ K` (the naïve distribution `⁅A, B ⊔ C⁆ = ⁅A, B⁆ ⊔ ⁅A, C⁆` is *false*, but holds
  modulo a normal `K`);
* `commutator_right_mul_mem_chain`, `iterCommutator_commutator_iterCommutator_le` — the
  chain's second-slot multiplicativity and the weight bound `⁅Hₐ, H_b⁆ ≤ H_{a+b+1}` (so the
  `S' = H₁` error in `sᵦ ≡ s^t (mod S')` is invisible modulo `Hₐ₊₂`);
* `caseB_excluded` — BG's **Case B exclusion**: it forces `H₁ ≤ H₂`, against strict descent;
* `caseA_eigenvalue_step` — BG's **Case A** recursion at the generator level: `σ` scales
  `⁅x, q·c⁆` by `sₐ·t` modulo `Hₐ₊₂`.

Assembling these into the full `hβsupply` (extending from the generators `⁅x, s⁆` to all of
`Hₐ₊₁`, splitting each `s ∈ S` along `S = Q'·T`, and running the induction against the
`RegularOperatorSetup` eigenvalue data) is the remaining `β`-side work. -/

/-- **Bilinearity modulo a normal subgroup**: if `⁅A, B⁆ ≤ K` and `⁅A, C⁆ ≤ K` with `K ⊴ G`,
then `⁅A, B ⊔ C⁆ ≤ K`.

The naïve `⁅A, B ⊔ C⁆ = ⁅A, B⁆ ⊔ ⁅A, C⁆` is **false**, but modulo a normal `K` the
distribution holds: in `G/K`, `A` centralises the images of `B` and of `C`, hence of `B ⊔ C`.
This is the "bilinearity modulo `Hₐ₊₂`" on which BG's `(E.23)` argument runs. -/
theorem commutator_sup_le_of_le {G : Type*} [Group G] {A B C K : Subgroup G} [K.Normal]
    (hB : ⁅A, B⁆ ≤ K) (hC : ⁅A, C⁆ ≤ K) : ⁅A, B ⊔ C⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha x hx
  have hle : (B ⊔ C).map (QuotientGroup.mk' K) ≤
      Subgroup.centralizer ({(QuotientGroup.mk' K) a} : Set (G ⧸ K)) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_ <;>
    · rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      change Commute ((QuotientGroup.mk' K) a) ((QuotientGroup.mk' K) y)
      rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      first
        | exact hB (Subgroup.commutator_mem_commutator ha hy)
        | exact hC (Subgroup.commutator_mem_commutator ha hy)
  have hcomm : Commute ((QuotientGroup.mk' K) a) ((QuotientGroup.mk' K) x) := by
    have hmem := hle (Subgroup.mem_map_of_mem _ hx)
    rw [Subgroup.mem_centralizer_iff] at hmem
    exact hmem ((QuotientGroup.mk' K) a) rfl
  rw [← QuotientGroup.eq_one_iff,
    show ((⁅a, x⁆ : G) : G ⧸ K) = (QuotientGroup.mk' K) ⁅a, x⁆ from rfl,
    map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact hcomm

/-- If `a` commutes with `c`, the right factor drops out: `⁅a, b * c⁆ = ⁅a, b⁆`.

The `Commute`-hypothesis specialisation of `commutatorElement_mul_right_eq_mul_conj`; it is
what removes the `T`-part (Case A) and the `S'`-error from the right slot of a chain
commutator once those factors centralise `x` in `G/Hₐ₊₂`. -/
theorem commutatorElement_mul_right_of_commute {K : Type*} [Group K] {a b c : K}
    (h : Commute a c) : ⁅a, b * c⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, commutatorElement_eq_one_iff_commute.mpr h,
    mul_one, mul_inv_cancel_right]

/-- **Second-slot multiplicativity of the chain commutator**: for `x ∈ Hₐ`,
`(⁅x, s⁆ * ⁅x, s'⁆)⁻¹ * ⁅x, s * s'⁆ ∈ Hₐ₊₂`.

The right-slot companion of `commutator_mul_mem_chain`: `s ↦ ⁅x, s⁆` is a homomorphism
`S → Hₐ₊₁/Hₐ₊₂` for `x ∈ Hₐ`.  The difference is exactly `⁅⁅x, s'⁆⁻¹, s⁆ ∈ ⁅Hₐ₊₁, ⊤⁆ = Hₐ₊₂`
(`⁅x, s'⁆ ∈ Hₐ₊₁`).  No hypothesis relating `s, s'` to the chain is needed. -/
theorem commutator_right_mul_mem_chain {G : Type*} [Group G] {T : Subgroup G} {a : ℕ}
    {x s s' : G} (hx : x ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) a) :
    (⁅x, s⁆ * ⁅x, s'⁆)⁻¹ * ⁅x, s * s'⁆ ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + 2) := by
  have hxs' : ⁅x, s'⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + 1) := by
    rw [OddOrder.Isaacs.Ch04.iterCommutator_succ]
    exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_top s')
  have hrw : (⁅x, s⁆ * ⁅x, s'⁆)⁻¹ * ⁅x, s * s'⁆ = ⁅⁅x, s'⁆⁻¹, s⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hrw, OddOrder.Isaacs.Ch04.iterCommutator_succ]
  exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hxs') (Subgroup.mem_top s)

/-- **Weight bound for the chain**: `⁅Hₐ, H_b⁆ ≤ H_{a+b+1}` for `Hₙ = iterCommutator T ⊤ n`.

The analogue of `⁅γᵢ, γⱼ⁆ ≤ γᵢ₊ⱼ` for the right-`⊤`-commutator chain, by the Three Subgroups
Lemma exactly as for the lower central series.  Its `b = 1` case `⁅Hₐ, H₁⁆ ≤ Hₐ₊₂` makes the
`S' = H₁` error in `sᵦ ≡ s^t (mod S')` invisible modulo `Hₐ₊₂`. -/
theorem iterCommutator_commutator_iterCommutator_le {G : Type*} [Group G] {T : Subgroup G}
    [T.Normal] (a b : ℕ) :
    ⁅OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) a,
        OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) b⁆ ≤
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + b + 1) := by
  induction b generalizing a with
  | zero =>
    have hrhs : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + 0 + 1) =
        ⁅OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) a, (⊤ : Subgroup G)⁆ := by
      rw [show a + 0 + 1 = a + 1 by omega]; exact OddOrder.Isaacs.Ch04.iterCommutator_succ T ⊤ a
    rw [hrhs, OddOrder.Isaacs.Ch04.iterCommutator_zero]
    exact Subgroup.commutator_mono le_rfl le_top
  | succ b ih =>
    haveI : (OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + b + 2)).Normal :=
      OddOrder.Isaacs.Ch04.iterCommutator_normal _
    have key : ⁅⁅OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) b, (⊤ : Subgroup G)⁆,
        OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) a⁆ ≤
        OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + b + 2) := by
      refine OddOrder.Isaacs.Ch04.commutator_commutator_le_of_rotate ?_ ?_
      · have htop : (⁅(⊤ : Subgroup G),
            OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) a⁆ : Subgroup G) =
            OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + 1) := by
          rw [Subgroup.commutator_comm]; exact (OddOrder.Isaacs.Ch04.iterCommutator_succ T ⊤ a).symm
        rw [htop]
        have hIH := ih (a + 1)
        rwa [show a + 1 + b + 1 = a + b + 2 by omega] at hIH
      · calc ⁅⁅OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) a,
              OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) b⁆, (⊤ : Subgroup G)⁆
            ≤ ⁅OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + b + 1),
              (⊤ : Subgroup G)⁆ := Subgroup.commutator_mono (ih a) le_rfl
          _ = OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + b + 2) := by
              rw [← OddOrder.Isaacs.Ch04.iterCommutator_succ,
                show a + b + 1 + 1 = a + b + 2 by omega]
    have hgoal : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (b + 1) =
        ⁅OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) b, (⊤ : Subgroup G)⁆ :=
      OddOrder.Isaacs.Ch04.iterCommutator_succ T ⊤ b
    rw [show a + (b + 1) + 1 = a + b + 2 by omega, hgoal, Subgroup.commutator_comm]
    exact key

/-- **Case B core**: `⁅T, Q⁆ ≤ H₂`, `⁅T, T⁆ ≤ H₂` and `⊤ = Q ⊔ T` force `H₁ ≤ H₂`.

`H₁ = ⁅H₀, ⊤⁆ = ⁅T, Q ⊔ T⁆`, so `commutator_sup_le_of_le` collapses it into `H₂` once both
`⁅T, Q⁆` (Case B) and `⁅T, T⁆ = T'` land there. -/
theorem iterCommutator_one_le_two_of_caseB {G : Type*} [Group G] {T Q : Subgroup G} [T.Normal]
    (hQT : (⊤ : Subgroup G) = Q ⊔ T)
    (hB : ⁅T, Q⁆ ≤ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) 2)
    (hT'2 : ⁅T, T⁆ ≤ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) 2) :
    OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) 1 ≤
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) 2 := by
  haveI : (OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) 2).Normal :=
    OddOrder.Isaacs.Ch04.iterCommutator_normal 2
  have hH1 : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) 1 = ⁅T, ⊤⁆ := by
    rw [OddOrder.Isaacs.Ch04.iterCommutator_succ, OddOrder.Isaacs.Ch04.iterCommutator_zero]
  rw [hH1]
  conv_lhs => rw [hQT]
  exact commutator_sup_le_of_le hB hT'2

/-- **BG's Case B exclusion** (issue 3021, (43) 段 2): Case B `⁅T, Q⁆ ≤ H₂` at index `0` is
impossible.

With `k ≥ 3` (so `H_{k-1} ≤ H₂`) and the minimality `T' ≤ H_{k-1}`,
`iterCommutator_one_le_two_of_caseB` forces `H₁ ≤ H₂`, contradicting the strict descent
`H₂ < H₁`.  This is what rules out the
fatal recursion `tₐ₊₁ = tₐ·t₀`, leaving BG's Case A `tₐ₊₁ = tₐ·t` of `(E.23)`. -/
theorem caseB_excluded {G : Type*} [Group G] {T Q : Subgroup G} [T.Normal] {k : ℕ}
    (hQT : (⊤ : Subgroup G) = Q ⊔ T)
    (hB : ⁅T, Q⁆ ≤ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) 2) (hk : 3 ≤ k)
    (hT' : ⁅T, T⁆ ≤ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (k - 1))
    (hlt : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) 2 <
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) 1) : False := by
  have hle := iterCommutator_one_le_two_of_caseB hQT hB
    (hT'.trans (iterCommutator_le_of_le (by omega)))
  exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)

/-- **BG `(E.23)`, Case A, at the generator level**: for `x ∈ Hₐ`, if `σ` scales `x` by `sₐ`
(mod `Hₐ₊₁`) and `q` by `t` (mod `H₁ = S'`), and the second-slot base part `c` satisfies
`c, σc ∈ T` with Case A `⁅Hₐ, T⁆ ≤ Hₐ₊₂`, then `σ` scales the generator `⁅x, q·c⁆` of `Hₐ₊₁`
by `sₐ·t` modulo `Hₐ₊₂`.

Operator-agnostic (`σ = β` is the intended use).  The computation is in `G/Hₐ₊₂`: the `Hₐ₊₁`
error on `x` is central and drops (`commutatorElement_mul_central_left`); the `T`-part `σc`
and the `S'`-error on `q` centralise `x` (Case A and `iterCommutator_commutator_iterCommutator_le`)
so drop from the right slot (`commutatorElement_mul_right_of_commute`); and BG Lemma 4.2(a)
(`commutatorElement_zpow_zpow_of_central`) turns the surviving `⁅x^{sₐ}, q^t⁆` into
`⁅x, q⁆^{sₐt} = ⁅x, q·c⁆^{sₐt}`. -/
theorem caseA_eigenvalue_step {G : Type*} [Group G] {T : Subgroup G} [T.Characteristic]
    {a : ℕ} (σ : G →* G) {x q c : G} {sₐ t : ℤ}
    (hx : x ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) a)
    (hσx : (x ^ sₐ)⁻¹ * σ x ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + 1))
    (hσq : (q ^ t)⁻¹ * σ q ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) 1)
    (hc : c ∈ T) (hσc : σ c ∈ T)
    (hCaseA : ⁅OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) a, T⁆ ≤
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + 2)) :
    (⁅x, q * c⁆ ^ (sₐ * t))⁻¹ * σ ⁅x, q * c⁆ ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + 2) := by
  set N := OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + 2) with hN
  set π := QuotientGroup.mk' N with hπ
  set u := (x ^ sₐ)⁻¹ * σ x with hu
  set v := (q ^ t)⁻¹ * σ q with hv
  have hσxeq : σ x = x ^ sₐ * u := by rw [hu]; group
  have hσqeq : σ q = q ^ t * v := by rw [hv]; group
  have hUc : π u ∈ Subgroup.center (G ⧸ N) :=
    chain_map_le_center T (a + 1) (Subgroup.mem_map.mpr ⟨u, hσx, rfl⟩)
  have hxq1 : ⁅x, q⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (a + 1) := by
    rw [OddOrder.Isaacs.Ch04.iterCommutator_succ]
    exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_top q)
  have hXQc : ⁅π x, π q⁆ ∈ Subgroup.center (G ⧸ N) := by
    rw [← map_commutatorElement]
    exact chain_map_le_center T (a + 1) (Subgroup.mem_map.mpr ⟨⁅x, q⁆, hxq1, rfl⟩)
  have hcomm_c : Commute (π x) (π c) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, hπ,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hCaseA (Subgroup.commutator_mem_commutator hx hc)
  have hcomm_sc : Commute (π x) (π (σ c)) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, hπ,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hCaseA (Subgroup.commutator_mem_commutator hx hσc)
  have hcomm_v : Commute (π x) (π v) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, hπ,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have h := iterCommutator_commutator_iterCommutator_le (T := T) a 1
      (Subgroup.commutator_mem_commutator hx hσq)
    rwa [show a + 1 + 1 = a + 2 by omega] at h
  refine QuotientGroup.eq.mp ?_
  change π (⁅x, q * c⁆ ^ (sₐ * t)) = π (σ ⁅x, q * c⁆)
  rw [map_commutatorElement σ x (q * c), map_mul σ q c, hσxeq, hσqeq]
  simp only [map_zpow, map_commutatorElement, map_mul]
  rw [commutatorElement_mul_central_left hUc,
    commutatorElement_mul_right_of_commute (hcomm_sc.zpow_left sₐ),
    commutatorElement_mul_right_of_commute (hcomm_v.zpow_left sₐ),
    commutatorElement_zpow_zpow_of_central hXQc sₐ t,
    commutatorElement_mul_right_of_commute hcomm_c]

/-! ## `(E.28)`: `T = C_S(Z₂(S))` is abelian, gated on the `β` supply

BG closes Proposition E.4 by contradiction: were `T` non-abelian, the minimal `k` with
`T/H_k` non-abelian and the maximal `i`, `j` of `(E.25)` produce `⁅wᵢ, wⱼ⁆ ∈ H_{k-1} − H_k`,
whose `α`- and `β`-eigenvalues `(E.26)`/`(E.27)` are computed two ways, forcing `t₀ = t`
against `(E.21)`.

Everything below the `β` supply is now assembled: the α relation is the *proved*
`dvd_sub_mul_eigenvalues_chain`, the index extraction is `exists_commutator_indices_chain`,
the bound `k ≤ q − 1` is `add_two_le_of_iterCommutator_ne_bot`, and the passage to `t₀ = t`
is `eq_of_chain_eigenvalue_relations_intCast`.  The single remaining input is BG's `(E.23)`
`wₐ^β ≡ wₐ^{t₀tᵃ} (mod Hₐ₊₁)` — taken here as `hβsupply` — which the Case A/B argument
(issue 3021, session (43)) establishes.  Discharging `hβsupply` closes the abelian clause of
Proposition E.4. -/

/-- **BG Proposition E.4, abelian clause, gated on `(E.23)`**: `⁅T, T⁆ = ⊥`.

Given `α`'s chain data (`hr`/`hr₀`, with `(E.20)`'s `r₀ = r`, `(E.9)`'s `r^q ≡ 1`, `(E.11)`'s
`r ≢ 1`) and, as a *hypothesis*, a `β`-side eigenvalue supply `hβsupply` scaling each live
`Hₐ` by `t₀ tᵃ` (BG's `(E.23)`), with `t, t₀` units and `t ≢ t₀` (`(E.21)`), the centralizer
`T = C_S(Ω₁(Z₂(S)))` is abelian.

The proof is BG's contradiction verbatim: extract `k, i, j` once, run the `α` computation
(`dvd_sub_mul_eigenvalues_chain`) and the `β` computation (`dvd_sub_mul_of_chain_supply`) at
those indices, bound `k` by `q − 1`, and conclude `t₀ ≡ t` — impossible by `(E.21)`. -/
theorem RegularOperatorSetup.commutator_centralizer_eq_bot_of_beta_supply [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) (hcard4 : p ^ 4 ≤ Nat.card ↥(Omega R p 1))
    (hSinv : IsAInvariant (hyp.act.comp hyp.A.subtype) (Omega R p 1))
    {a : B} (ha : a ∈ hyp.A)
    {v : ↥(Omega R p 1)} (hv : Subgroup.zpowers v = hyp.R₀.subgroupOf (Omega R p 1))
    {w : ↥(Omega R p 1)}
    (hw : w ∈ Subgroup.centralizer (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1)))
    (hw1 : w ∉ OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1)))
      (⊤ : Subgroup ↥(Omega R p 1)) 1)
    {r r₀ : ℤ} (hr : (hSinv.restrict ⟨a, ha⟩) v = v ^ r)
    (hr₀ : ∀ y ∈ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1)))
        (⊤ : Subgroup ↥(Omega R p 1)) 0,
      (y ^ r₀)⁻¹ * (hSinv.restrict ⟨a, ha⟩) y ∈ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1)))
        (⊤ : Subgroup ↥(Omega R p 1)) 1)
    (hr0r : (r₀ : ZMod p) = (r : ZMod p)) (hrq : (r : ZMod p) ^ q = 1) (hr1 : (r : ZMod p) ≠ 1)
    (σβ : ↥(Omega R p 1) →* ↥(Omega R p 1)) {t t₀ : ℤ}
    (hβsupply : ∀ a : ℕ, OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1)))
        (⊤ : Subgroup ↥(Omega R p 1)) a ≠ ⊥ →
      ∃ s : ℤ, (s : ZMod p) = (t₀ : ZMod p) * (t : ZMod p) ^ a ∧
        ∀ y ∈ OddOrder.Isaacs.Ch04.iterCommutator
            (Subgroup.centralizer (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1)))
            (⊤ : Subgroup ↥(Omega R p 1)) a,
          (y ^ s)⁻¹ * σβ y ∈ OddOrder.Isaacs.Ch04.iterCommutator
            (Subgroup.centralizer (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1)))
            (⊤ : Subgroup ↥(Omega R p 1)) (a + 1))
    (htu : IsUnit (t : ZMod p)) (ht₀u : IsUnit (t₀ : ZMod p))
    (htne : (t₀ : ZMod p) ≠ (t : ZMod p)) :
    ⁅Subgroup.centralizer (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1)),
      Subgroup.centralizer
        (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1))⁆ = ⊥ := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  have hR₀S : hyp.R₀ ≤ Omega R p 1 := hyp.R₀_le_omega
  have hexp : ∀ x : ↥(Omega R p 1), x ^ p = 1 := hyp.omega_pow_eq_one'
  have hS3 : 3 ≤ pRank ↥(Omega R p 1) p := hyp.three_le_pRank_omega hcard4
  by_contra hnonab
  -- BG's `k`, `i`, `j` from `(E.24)`/`(E.25)`.
  obtain ⟨k, i, j, _hk3, hi1, hji, hik, hTle, _hknot, hcl, hcr, hwij⟩ :=
    hyp.exists_commutator_indices_chain hR₀S hexp hS3 hv hw hw1 hnonab
  -- `(E.26)`: the `α` relation, from the *proved* assembly.
  have hE26α := hyp.dvd_sub_mul_eigenvalues_chain hR₀S hexp hS3 hSinv ha hv hw hw1 hr hr₀
    hnonab hi1 hji hik hTle hcl hcr hwij
  -- `(E.27)`: the `β` relation, from the supply `(E.23)`.
  have hE27β := dvd_sub_mul_of_chain_supply hyp.p_prime σβ hw (fun y _ => hexp y)
    hβsupply hnonab hji hik hTle hcl hcr hwij
  -- `k ≤ q − 1`: `H_{k-1} ≠ 1` since it contains `⁅T, T⁆ ≠ 1`.
  have hlivek1 : OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1)))
      (⊤ : Subgroup ↥(Omega R p 1)) (k - 1) ≠ ⊥ :=
    fun h => hnonab (le_bot_iff.mp (hTle.trans (le_of_eq h)))
  have hmq : (k - 1) + 2 ≤ q := hyp.add_two_le_of_iterCommutator_ne_bot hcard4 hlivek1
  -- `(E.28)`: the two relations force `t₀ ≡ t`, against `(E.21)`.
  rw [hr0r] at hE26α
  exact htne (eq_of_chain_eigenvalue_relations_intCast hyp.q_prime hrq hr1 htu ht₀u
    hji (by omega) hmq hE26α hE27β)

end OddOrder.BG.AppE
