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

end OddOrder.BG.AppE
