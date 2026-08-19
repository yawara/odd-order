/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleySsetCoherence

/-!
# Peterfalvi Appendix IV: the Feit–Sibley Theorem — supporting layer (pp. 145–150)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, pp. 145–150.  Support for the Theorem `feit_sibley_coherence`
(campaign issue 1054): degree-square counting for the reduction steps (1)–(3),
the conjugate-pair decomposition of a conjugation-closed family, the
fixed-point-free lower bounds on subgroups of `Q₁`, and the `𝒮(R)` counting
layer feeding the endgame (4)–(8) of pp. 146–150.

The `𝒮(Q')` coherence layer (derived subgroups, `H = Q ⋊ D` counting, the
degree-`d` Remark) lives upstream in
`OddOrder.Peterfalvi.Appendices.FeitSibleySsetCoherence` (prefix-split,
issue 0149).  The statements live in the `Hypothesis` namespace of
`OddOrder.Peterfalvi.Appendices.FeitSibley` and extend the structure API of
that file.
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

open scoped commutatorElement ComplexOrder

variable {G : Type*} [Group G]

/-! ## Degree-square counting for the reduction steps (pp. 146–147)

The reductions (1)–(3) repeatedly use
`∑_{χ ∈ 𝒮(R)} χ(1)² = |H/R| − |H/R·Q₁|`.  The generic form below (over any finite
group `K` with two normal subgroups) reduces to the inflation counting of
`InflationCharacter.lean`. -/

open scoped Classical in
/-- **Two-kernel degree-square counting**: the squared degrees of the irreducibles
of `K` whose kernel contains `N` but not `M` sum to `|K⧸N| − |K⧸(N ⊔ M)|`.
Splitting the `N ⊆ ker` sum (`sumInflatedDegreeSq` = `|K⧸N|`) by the
`M ⊆ ker` condition, the both-kernels part is the `N ⊔ M ⊆ ker` part
(the character kernel is a subgroup, `characterKernelSubgroup`), which sums to
`|K⧸(N ⊔ M)|`. -/
theorem sum_degreeSq_ker_subset_not_subset
    {K : Type*} [Group K] [Finite K] [Invertible (Nat.card K : ℂ)]
    (N M : Subgroup K) [N.Normal] [(N ⊔ M).Normal] :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter K =>
        (N : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction K ℂ) ∧
        ¬ (M : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction K ℂ)),
        ((χ : ClassFunction K ℂ) 1) ^ 2
      = (Nat.card (K ⧸ N) : ℂ) - (Nat.card (K ⧸ (N ⊔ M)) : ℂ) := by
  classical
  let : Fintype K := Fintype.ofFinite _
  have hker_iff : ∀ χ : IrreducibleCharacter K,
      (((N : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction K ℂ)) ∧
        ((M : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction K ℂ)))
      ↔ (((N ⊔ M : Subgroup K) : Set K)
          ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction K ℂ)) := by
    intro χ
    have hKSset := OddOrder.Peterfalvi.S13.coe_characterKernelSubgroup
      χ.isIrreducible.isCharacter
    constructor
    · rintro ⟨h1, h2⟩
      rw [← hKSset] at h1 h2 ⊢
      have hN : N ≤ OddOrder.Peterfalvi.S13.characterKernelSubgroup
          χ.isIrreducible.isCharacter := fun x hx => h1 hx
      have hM : M ≤ OddOrder.Peterfalvi.S13.characterKernelSubgroup
          χ.isIrreducible.isCharacter := fun x hx => h2 hx
      exact fun x hx => (sup_le hN hM) hx
    · intro h
      exact ⟨Set.Subset.trans (SetLike.coe_subset_coe.mpr le_sup_left) h,
        Set.Subset.trans (SetLike.coe_subset_coe.mpr le_sup_right) h⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun χ : IrreducibleCharacter K =>
      (N : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction K ℂ)))
    (fun χ => (M : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction K ℂ))
    (fun χ => ((χ : ClassFunction K ℂ) 1) ^ 2)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have hfilter_sup : (Finset.univ.filter (fun χ : IrreducibleCharacter K =>
        (N : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction K ℂ) ∧
        (M : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction K ℂ)))
      = Finset.univ.filter (fun χ : IrreducibleCharacter K =>
        ((N ⊔ M : Subgroup K) : Set K)
          ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction K ℂ)) :=
    Finset.filter_congr fun χ _ => by
      constructor
      · exact fun h => (hker_iff χ).mp (by simpa using h)
      · exact fun h => by simpa using (hker_iff χ).mpr h
  rw [hfilter_sup] at hsplit
  rw [sumInflatedDegreeSq (N := N ⊔ M), sumInflatedDegreeSq (N := N)] at hsplit
  linear_combination hsplit

/-! ## Conjugate-pair decomposition of a conjugation-closed family

The `coherentPairChain`/`coherentOfPairChainCover` engine (CoherenceUnion) consumes a
pair enumeration; here we *construct* one: a finite, conjugation-closed, real-free
family `Y` containing a conjugation-closed base `B` decomposes as
`pairUnion B pair N = Y` with each adjoined pair a fresh conjugate pair `{χ, χ̄}`.
This is the decomposition input for the reduction steps (1)–(2) of the Feit–Sibley
Theorem; the enumeration also records a min-degree clause (each step's first member
has minimal degree real part among the not-yet-accumulated members of `Y`). -/

/-- **Conjugate-pair decomposition**: a finite, conjugation-closed family `Y` with no
real members is reached from any conjugation-closed base `B ⊆ Y` by adjoining
conjugate pairs, each fresh at its step (`(pair j).1, (pair j).2 ∉ pairUnion B pair j`).
Each step's first member additionally has minimal degree real part among the
not-yet-accumulated members of `Y` (min-degree clause).  Constructed by strong
induction on `(Y ∖ B).ncard`: pick `χ ∈ Y ∖ B` minimizing `(χ 1).re`
(`Set.exists_min_image`), adjoin `{χ, χ̄}` (fresh, `χ̄ ≠ χ` by non-reality),
recurse with base `B ∪ {χ, χ̄}`. -/
theorem exists_conjPair_pairUnion_eq {L : Type*} [Group L]
    {Y B : Set (ClassFunction L ℂ)} (hBY : B ⊆ Y) (hYfin : Y.Finite)
    (hYconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Y)
    (hBconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate B)
    (hnoreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters Y) :
    ∃ (N : ℕ) (pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ),
      OddOrder.Peterfalvi.S07.pairUnion (L := L) B pair N = Y ∧
      (∀ j, j < N → (pair j).2 = (pair j).1.conj ∧ (pair j).1 ∈ Y ∧
        (pair j).1 ∉ OddOrder.Peterfalvi.S07.pairUnion (L := L) B pair j ∧
        (pair j).2 ∉ OddOrder.Peterfalvi.S07.pairUnion (L := L) B pair j) ∧
      ∀ j, j < N → ∀ χ ∈ Y, χ ∉ OddOrder.Peterfalvi.S07.pairUnion (L := L) B pair j →
        (((pair j).1) (1 : L)).re ≤ (χ (1 : L)).re := by
  classical
  suffices h : ∀ (n : ℕ) (B : Set (ClassFunction L ℂ)), B ⊆ Y →
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate B → (Y \ B).ncard = n →
      ∃ (N : ℕ) (pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ),
        OddOrder.Peterfalvi.S07.pairUnion (L := L) B pair N = Y ∧
        (∀ j, j < N → (pair j).2 = (pair j).1.conj ∧ (pair j).1 ∈ Y ∧
          (pair j).1 ∉ OddOrder.Peterfalvi.S07.pairUnion (L := L) B pair j ∧
          (pair j).2 ∉ OddOrder.Peterfalvi.S07.pairUnion (L := L) B pair j) ∧
        ∀ j, j < N → ∀ χ ∈ Y, χ ∉ OddOrder.Peterfalvi.S07.pairUnion (L := L) B pair j →
          (((pair j).1) (1 : L)).re ≤ (χ (1 : L)).re by
    exact h _ B hBY hBconj rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B hBY hBconj hn
    by_cases hYB : Y ⊆ B
    · have hBeq : B = Y := Set.Subset.antisymm hBY hYB
      exact ⟨0, fun _ => (0, 0), by simpa using hBeq, fun j hj => absurd hj (by omega),
        fun j hj => absurd hj (by omega)⟩
    · -- min-degree choice: `χ ∈ Y ∖ B` minimizing `(χ 1).re`
      have hYBne : (Y \ B).Nonempty := by
        obtain ⟨ψ₀, hψ₀Y, hψ₀B⟩ := Set.not_subset.mp hYB
        exact ⟨ψ₀, hψ₀Y, hψ₀B⟩
      obtain ⟨χ, ⟨hχY, hχB⟩, hχmin⟩ := Set.exists_min_image (Y \ B)
        (fun ψ => (ψ (1 : L)).re) hYfin.sdiff hYBne
      have hχconjY : χ.conj ∈ Y := hYconj hχY
      have hχconjB : χ.conj ∉ B := fun h => hχB (by simpa using hBconj h)
      have hne : χ.conj ≠ χ := fun h => hnoreal hχY h
      set B' : Set (ClassFunction L ℂ) := B ∪ {χ, χ.conj} with hB'
      have hB'Y : B' ⊆ Y := by
        rintro x (hx | hx)
        · exact hBY hx
        · rcases (by simpa using hx : x = χ ∨ x = χ.conj) with rfl | rfl
          · exact hχY
          · exact hχconjY
      have hB'conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate B' := by
        rintro x (hx | hx)
        · exact Or.inl (hBconj hx)
        · rcases (by simpa using hx : x = χ ∨ x = χ.conj) with rfl | rfl
          · exact Or.inr (by simp)
          · exact Or.inr (by simp)
      have hsub : Y \ B' ⊆ Y \ B := fun x hx => ⟨hx.1, fun hB => hx.2 (Or.inl hB)⟩
      have hχnot : χ ∉ Y \ B' := fun hx => hx.2 (Or.inr (by simp))
      have hlt : (Y \ B').ncard < n := by
        rw [← hn]
        exact Set.ncard_lt_ncard
          ((Set.ssubset_iff_of_subset hsub).mpr ⟨χ, ⟨hχY, hχB⟩, hχnot⟩)
          (hYfin.sdiff)
      obtain ⟨N', pair', hUnion', hstep', hmin'⟩ := ih _ hlt B' hB'Y hB'conj rfl
      set pr : ℕ → ClassFunction L ℂ × ClassFunction L ℂ :=
        fun j => if j = 0 then (χ, χ.conj) else pair' (j - 1) with hpr
      have hshift : ∀ k, OddOrder.Peterfalvi.S07.pairUnion (L := L) B pr (k + 1)
          = OddOrder.Peterfalvi.S07.pairUnion (L := L) B' pair' k := by
        intro k
        induction k with
        | zero =>
          rw [OddOrder.Peterfalvi.S07.pairUnion_succ]
          simp only [OddOrder.Peterfalvi.S07.pairUnion_zero,
            OddOrder.Peterfalvi.S07.pairSet, hpr, if_pos rfl, hB']
        | succ k ihk =>
          have hps : OddOrder.Peterfalvi.S07.pairSet (L := L) pr (k + 1)
              = OddOrder.Peterfalvi.S07.pairSet (L := L) pair' k := by
            simp [OddOrder.Peterfalvi.S07.pairSet, hpr]
          rw [OddOrder.Peterfalvi.S07.pairUnion_succ, ihk, hps,
            ← OddOrder.Peterfalvi.S07.pairUnion_succ]
      refine ⟨N' + 1, pr, by rw [hshift N']; exact hUnion', ?_, ?_⟩
      · intro j hj
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · refine ⟨by simp [hpr], by simpa [hpr] using hχY, ?_, ?_⟩
          · simpa [hpr] using hχB
          · simpa [hpr] using hχconjB
        · obtain ⟨j', rfl⟩ : ∃ j'', j = j'' + 1 := ⟨j - 1, by omega⟩
          have hj' : j' < N' := by omega
          obtain ⟨hc, hY', hn1, hn2⟩ := hstep' j' hj'
          have hpr_eval : pr (j' + 1) = pair' j' := by simp [hpr]
          refine ⟨by rw [hpr_eval]; exact hc, by rw [hpr_eval]; exact hY', ?_, ?_⟩
          · rw [hpr_eval, hshift j']
            exact hn1
          · rw [hpr_eval, hshift j']
            exact hn2
      · intro j hj ψ hψY hψnot
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · -- `pairUnion B pr 0 = B`: minimality of the chosen `χ` over `Y ∖ B`
          have hψB : ψ ∉ B := by simpa using hψnot
          simpa [hpr] using hχmin ψ ⟨hψY, hψB⟩
        · -- shift into the recursive min clause over the base `B' = B ∪ {χ, χ̄}`
          obtain ⟨j', rfl⟩ : ∃ j'', j = j'' + 1 := ⟨j - 1, by omega⟩
          have hj' : j' < N' := by omega
          have hψnot' : ψ ∉ OddOrder.Peterfalvi.S07.pairUnion (L := L) B' pair' j' := by
            rw [← hshift j']
            exact hψnot
          have hpr_eval : pr (j' + 1) = pair' j' := by simp [hpr]
          rw [hpr_eval]
          exact hmin' j' hj' ψ hψY hψnot'

/-- **First incoherent step extraction**: if the base of a pair chain is coherent
but the full accumulation is not, some step turns a coherent accumulation
incoherent.  Pure finite induction on the chain length (the contrapositive of
`coherentPairChain`); this is how the reduction steps of the Feit–Sibley Theorem
produce the counterexample character `ψ` of Peterfalvi's "(by Lemma 1(a)) there is
a character `ψ` such that …". -/
theorem exists_first_incoherent_step {L G' : Type*} [Group L] [Group G']
    [Fintype L] [Fintype G'] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G' : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G'} {A : Set L}
    {B : Set (ClassFunction L ℂ)}
    {pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ} {N : ℕ}
    (h0 : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ B A))
    (hfail : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := L) B pair N) A)) :
    ∃ i, i < N ∧
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
        (OddOrder.Peterfalvi.S07.pairUnion (L := L) B pair i) A) ∧
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
        (OddOrder.Peterfalvi.S07.pairUnion (L := L) B pair (i + 1)) A) := by
  classical
  induction N with
  | zero =>
    rw [OddOrder.Peterfalvi.S07.pairUnion_zero] at hfail
    exact absurd h0 hfail
  | succ N ihN =>
    by_cases hN : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
        (OddOrder.Peterfalvi.S07.pairUnion (L := L) B pair N) A)
    · exact ⟨N, Nat.lt_succ_self N, hN, hfail⟩
    · obtain ⟨i, hiN, hcoh, hnot⟩ := ihN hN
      exact ⟨i, hiN.trans (Nat.lt_succ_self N), hcoh, hnot⟩

namespace Hypothesis

variable (hyp : Hypothesis G)

/-- **`LeKer` is the character-kernel inclusion**: `χ` is constant (`= χ(1)`) on the
`R`-part of `H` iff `R.subgroupOf H` is contained in `characterKernel χ`. -/
theorem leKer_iff_subset_characterKernel {R : Subgroup G} {χ : ClassFunction ↥hyp.H ℂ} :
    hyp.LeKer χ R ↔ ((R.subgroupOf hyp.H : Subgroup ↥hyp.H) : Set ↥hyp.H)
      ⊆ OddOrder.Peterfalvi.S03.characterKernel χ := by
  constructor
  · intro h y hy
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel]
    have hmem : (y : G) ∈ R := Subgroup.mem_subgroupOf.mp hy
    simpa using h y hmem
  · intro h x hx
    have hmem : x ∈ ((R.subgroupOf hyp.H : Subgroup ↥hyp.H) : Set ↥hyp.H) :=
      Subgroup.mem_subgroupOf.mpr hx
    have := h hmem
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at this
    simpa using this

/-! ### Fixed-point-free lower bounds (pp. 146–147)

The reductions use `|Z| ≥ d+1` (and, for `|Z|` odd, `|Z| ≥ 2d+1`) for nontrivial
`D`-invariant subgroups `Z ≤ Q₁`: the conjugation action of `D` on `Z` is free off
the unique fixed point `1`, so `d ∣ |Z| − 1`. -/

/-- **`d ∣ |Z| − 1`** for a `D`-invariant subgroup `Z ≤ Q₁`: conjugation by `D` acts
on `Z` with unique fixed point `1` (fixed-point-freeness on `Q₁`) and freely off it
(trivial stabilizers), so the non-identity elements split into free `D`-orbits
(`dvd_card_sub_one_of_free_off_unique_fixed`). -/
theorem d_dvd_card_sub_one_of_le_Q1 [Finite G] {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1)
    (hZinv : ∀ δ ∈ hyp.D, ∀ z ∈ Z, δ * z * δ⁻¹ ∈ Z) :
    hyp.d ∣ Nat.card ↥Z - 1 := by
  classical
  by_cases hd1 : hyp.d = 1
  · rw [hd1]; exact one_dvd _
  let : SMul ↥hyp.D ↥Z :=
    ⟨fun δ z => ⟨(δ : G) * z * (δ : G)⁻¹, hZinv δ δ.2 z z.2⟩⟩
  have hsmul_def : ∀ (δ : ↥hyp.D) (z : ↥Z),
      ((δ • z : ↥Z) : G) = (δ : G) * z * (δ : G)⁻¹ := fun _ _ => rfl
  let : MulAction ↥hyp.D ↥Z :=
    { one_smul := fun z => Subtype.ext (by rw [hsmul_def]; simp)
      mul_smul := fun δ₁ δ₂ z => Subtype.ext (by
        rw [hsmul_def, hsmul_def, hsmul_def]
        simp only [Subgroup.coe_mul]
        group) }
  have h1fix : (1 : ↥Z) ∈ MulAction.fixedPoints ↥hyp.D ↥Z := by
    intro δ
    exact Subtype.ext (by rw [hsmul_def]; simp)
  have huniq : ∀ z : ↥Z, z ∈ MulAction.fixedPoints ↥hyp.D ↥Z → z = 1 := by
    intro z hz
    have : Nontrivial ↥hyp.D := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      have hpos : 0 < Nat.card ↥hyp.D := Nat.card_pos
      have : Nat.card ↥hyp.D ≠ 1 := hd1
      omega
    obtain ⟨δ0, hδ0⟩ := exists_ne (1 : ↥hyp.D)
    have hδ0G : (δ0 : G) ≠ 1 := fun h => hδ0 (Subtype.ext (by simpa using h))
    have hfix := hz δ0
    have hfixG : (δ0 : G) * (z : G) * (δ0 : G)⁻¹ = (z : G) := by
      have := congrArg (fun w : ↥Z => (w : G)) hfix
      rwa [hsmul_def] at this
    have hz1 : (z : G) = 1 :=
      hyp.D_fixedPointFree_on_Q1 (δ0 : G) δ0.2 hδ0G (z : G) (hZQ1 z.2) hfixG
    exact Subtype.ext hz1
  have hfree : ∀ z : ↥Z, z ∉ MulAction.fixedPoints ↥hyp.D ↥Z →
      Nat.card (MulAction.orbit ↥hyp.D z) = Nat.card ↥hyp.D := by
    intro z hz
    have hstab : MulAction.stabilizer ↥hyp.D z = ⊥ := by
      rw [eq_bot_iff]
      intro δ hδ
      rw [Subgroup.mem_bot]
      by_contra hδ1
      have hδG : (δ : G) ≠ 1 := fun h => hδ1 (Subtype.ext (by simpa using h))
      have hfixG : (δ : G) * (z : G) * (δ : G)⁻¹ = (z : G) := by
        have := congrArg (fun w : ↥Z => (w : G)) (MulAction.mem_stabilizer_iff.mp hδ)
        rwa [hsmul_def] at this
      have hz1 : (z : G) = 1 :=
        hyp.D_fixedPointFree_on_Q1 (δ : G) δ.2 hδG (z : G) (hZQ1 z.2) hfixG
      have hzeq : z = (1 : ↥Z) := Subtype.ext hz1
      exact hz (by rw [hzeq]; exact h1fix)
    have hinj : Function.Injective (fun δ : ↥hyp.D => δ • z) := by
      intro δ₁ δ₂ heq
      have heq' : δ₁ • z = δ₂ • z := heq
      have hmem : δ₂⁻¹ * δ₁ ∈ MulAction.stabilizer ↥hyp.D z := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, heq', ← mul_smul, inv_mul_cancel, one_smul]
      rw [hstab, Subgroup.mem_bot] at hmem
      exact (inv_mul_eq_one.mp hmem).symm
    exact Nat.card_range_of_injective hinj
  exact OddOrder.GroupTheory.FreeActionOrbitCount.dvd_card_sub_one_of_free_off_unique_fixed
    (1 : ↥Z) h1fix huniq hfree

/-- **`|Z| ≥ d + 1`** for a nontrivial `D`-invariant `Z ≤ Q₁`
(`d ∣ |Z| − 1` and `|Z| > 1`). -/
theorem d_add_one_le_card_of_le_Q1 [Finite G] {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1)
    (hZinv : ∀ δ ∈ hyp.D, ∀ z ∈ Z, δ * z * δ⁻¹ ∈ Z) (hZne : Z ≠ ⊥) :
    hyp.d + 1 ≤ Nat.card ↥Z := by
  have hdvd := hyp.d_dvd_card_sub_one_of_le_Q1 hZQ1 hZinv
  have hlt : 1 < Nat.card ↥Z :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot Z).mpr hZne)
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0, mul_zero] at hk; omega
    · exact h
  have hle : hyp.d ≤ hyp.d * k := Nat.le_mul_of_pos_right hyp.d hkpos
  omega

/-- **`|Z| ≥ 2d + 1`** for a nontrivial `D`-invariant `Z ≤ Q₁` of odd order, `d`
odd: `|Z| = kd + 1` with `k ≥ 1`, and `k = 1` would make `|Z| = d + 1` even. -/
theorem two_mul_d_add_one_le_card_of_le_Q1 [Finite G] (hd : Odd hyp.d)
    {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1)
    (hZinv : ∀ δ ∈ hyp.D, ∀ z ∈ Z, δ * z * δ⁻¹ ∈ Z) (hZne : Z ≠ ⊥)
    (hZodd : Odd (Nat.card ↥Z)) :
    2 * hyp.d + 1 ≤ Nat.card ↥Z := by
  have hdvd := hyp.d_dvd_card_sub_one_of_le_Q1 hZQ1 hZinv
  have hlt : 1 < Nat.card ↥Z :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot Z).mpr hZne)
  obtain ⟨k, hk⟩ := hdvd
  have hcard : Nat.card ↥Z = hyp.d * k + 1 := by omega
  have hkeven : Even k := by
    have heven : Even (hyp.d * k) :=
      Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp (hcard ▸ hZodd))
    rcases Nat.even_mul.mp heven with h | h
    · exact absurd h (Nat.not_even_iff_odd.mpr hd)
    · exact h
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0, mul_zero] at hk; omega
    · exact h
  have hk2 : 2 ≤ k := by
    rcases hkeven with ⟨m, hm⟩
    omega
  have hle : hyp.d * 2 ≤ hyp.d * k := Nat.mul_le_mul_left hyp.d hk2
  omega

section SsetOfCounting

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable [Invertible (Nat.card ↥hyp.H : ℂ)]

open scoped Classical in
omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- **The `𝒮(R)` degree-square sum** (the counting input of the reduction steps
(1)–(3), pp. 146–147): for `R ≤ Q` with `R.subgroupOf H` and
`(R ⊔ Q₁).subgroupOf H`-side joins normal in `↥H`,
`∑_{χ ∈ 𝒮(R)} χ(1)² = |H⧸R| − |H⧸(R·Q₁)|` (quotients taken inside `↥H`).
Membership in `𝒮(R)` is exactly "kernel contains `R` but not `Q₁`"
(`leKer_iff_subset_characterKernel`), so this is
`sum_degreeSq_ker_subset_not_subset`. -/
theorem sum_degreeSq_SsetOf [Finite G] (R : Subgroup G)
    [(R.subgroupOf hyp.H).Normal]
    [((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H)).Normal] :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter ↥hyp.H =>
        (χ : ClassFunction ↥hyp.H ℂ) ∈ hyp.SsetOf R),
        ((χ : ClassFunction ↥hyp.H ℂ) 1) ^ 2
      = (Nat.card (↥hyp.H ⧸ R.subgroupOf hyp.H) : ℂ)
        - (Nat.card (↥hyp.H ⧸ ((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H))) : ℂ) := by
  classical
  let : Fintype ↥hyp.H := Fintype.ofFinite _
  have hcongr : ∀ χb : IrreducibleCharacter ↥hyp.H,
      ((χb : ClassFunction ↥hyp.H ℂ) ∈ hyp.SsetOf R)
      ↔ (((R.subgroupOf hyp.H : Subgroup ↥hyp.H) : Set ↥hyp.H)
            ⊆ OddOrder.Peterfalvi.S03.characterKernel (χb : ClassFunction ↥hyp.H ℂ) ∧
          ¬ ((hyp.Q1.subgroupOf hyp.H : Subgroup ↥hyp.H) : Set ↥hyp.H)
            ⊆ OddOrder.Peterfalvi.S03.characterKernel (χb : ClassFunction ↥hyp.H ℂ)) := by
    intro χb
    constructor
    · rintro ⟨⟨-, hk1⟩, hkR⟩
      exact ⟨(hyp.leKer_iff_subset_characterKernel).mp hkR,
        fun h => hk1 ((hyp.leKer_iff_subset_characterKernel).mpr h)⟩
    · rintro ⟨hR, hQ1⟩
      exact ⟨⟨χb.isIrreducible,
        fun hall => hQ1 ((hyp.leKer_iff_subset_characterKernel).mp hall)⟩,
        (hyp.leKer_iff_subset_characterKernel).mpr hR⟩
  rw [Finset.filter_congr (fun χb _ => by
    constructor
    · exact fun h => by simpa using (hcongr χb).mp (by simpa using h)
    · exact fun h => by simpa using (hcongr χb).mpr (by simpa using h))]
  exact sum_degreeSq_ker_subset_not_subset (R.subgroupOf hyp.H) (hyp.Q1.subgroupOf hyp.H)

omit [Fintype G] in
/-- **Every member of `𝒮` has degree `d·m` with `m ≥ 1`** (Lemma 2(a) + the induced
degree formula): `χ = Ind_Q^H φ` gives `χ(1) = [H:Q]·φ(1) = d·φ(1)`, and `φ(1)` is
a positive natural.  This is the `d ∣ χ(1)` divisibility feeding the anchor
hypothesis of Lemma 1(a) throughout the reduction steps. -/
theorem exists_apply_one_eq_d_mul [Finite G]
    [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]
    {χ : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) :
    ∃ m : ℕ, 0 < m ∧ χ (1 : ↥hyp.H) = (hyp.d : ℂ) * (m : ℂ) := by
  classical
  let : Fintype ↥hyp.H := Fintype.ofFinite _
  let : Fintype ↥(hyp.Q.subgroupOf hyp.H) := Fintype.ofFinite _
  have hχ' := hχ
  rw [Sset_eq_induced_of_Q hyp] at hχ'
  obtain ⟨φ, ⟨hφirr, -⟩, rfl⟩ := hχ'
  obtain ⟨m, hmpos, hm, -⟩ := hφirr.exists_natDegree_charValue_one_dvd_card
  refine ⟨m, hmpos, ?_⟩
  rw [ClassFunction.induce_apply_one, hyp.index_Q_subgroupOf_eq_d, hm]

end SsetOfCounting

open scoped Classical in
/-- **`sum_degreeSq_SsetOf`, `toFinset` form**: the `𝒮(R)` degree-square sum over
the plain class-function `toFinset` (the shape produced by
`exists_counterexample_of_not_coherent`) equals the same quotient-card difference.
Bundling `x ↦ ⟨x, irr⟩` is a bijection onto the filtered irreducible-character
`Finset` of `sum_degreeSq_SsetOf`. -/
theorem sum_degreeSq_SsetOf_toFinset [Finite G]
    [Invertible (Nat.card ↥hyp.H : ℂ)] (R : Subgroup G)
    [(R.subgroupOf hyp.H).Normal]
    [((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H)).Normal]
    (hfin : (hyp.SsetOf R).Finite) :
    ∑ x ∈ hfin.toFinset, (x (1 : ↥hyp.H)) ^ 2
      = (Nat.card (↥hyp.H ⧸ R.subgroupOf hyp.H) : ℂ)
        - (Nat.card (↥hyp.H ⧸ ((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H))) : ℂ) := by
  classical
  let : Fintype ↥hyp.H := Fintype.ofFinite _
  rw [← hyp.sum_degreeSq_SsetOf R]
  refine Finset.sum_bij'
    (fun x hx => (⟨x, ((hfin.mem_toFinset.mp hx).1.1 :)⟩ : IrreducibleCharacter ↥hyp.H))
    (fun χb hb => (χb : ClassFunction ↥hyp.H ℂ)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using hfin.mem_toFinset.mp hx⟩
  · intro χb hb
    rw [Set.Finite.mem_toFinset]
    exact (Finset.mem_filter.mp hb).2
  · intro x hx
    rfl
  · intro χb hb
    rfl
  · intro x hx
    rfl

/-- **The (1.1)-shaped counting bound**: if every member of `𝒮(R)` has degree
`d·m(x)` and `∑ m(x)² ≤ 2a` (the conclusion of
`exists_counterexample_of_not_coherent` with base `B = 𝒮(R)`), then the
quotient-card difference of `sum_degreeSq_SsetOf` is bounded:
`|H⧸R| − |H⧸R·Q₁| ≤ d²·2a`.  This is Peterfalvi's
`|H/S'Q₂| − |H/S'Q₁| = ∑ χ(1)² ≤ 2dψ(1)` in real form. -/
theorem card_quot_sub_le_of_forall_deg_of_sum_le [Finite G]
    [Invertible (Nat.card ↥hyp.H : ℂ)] (R : Subgroup G)
    [(R.subgroupOf hyp.H).Normal]
    [((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H)).Normal]
    (hfin : (hyp.SsetOf R).Finite)
    {m : ClassFunction ↥hyp.H ℂ → ℕ} {a : ℕ}
    (hmdeg : ∀ x ∈ hyp.SsetOf R, x (1 : ↥hyp.H) = (hyp.d : ℂ) * (m x : ℂ))
    (hmsum : (∑ x ∈ hfin.toFinset, ((m x : ℝ)) ^ 2) ≤ 2 * (a : ℝ)) :
    (Nat.card (↥hyp.H ⧸ R.subgroupOf hyp.H) : ℝ)
      - (Nat.card (↥hyp.H ⧸ ((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H))) : ℝ)
      ≤ (hyp.d : ℝ) ^ 2 * (2 * (a : ℝ)) := by
  classical
  have key : (hyp.d : ℝ) ^ 2 * ∑ x ∈ hfin.toFinset, ((m x : ℝ)) ^ 2
      = (Nat.card (↥hyp.H ⧸ R.subgroupOf hyp.H) : ℝ)
        - (Nat.card (↥hyp.H ⧸ ((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H))) : ℝ) := by
    have hC := hyp.sum_degreeSq_SsetOf_toFinset R hfin
    have h2 : ∑ x ∈ hfin.toFinset, (x (1 : ↥hyp.H)) ^ 2
        = (hyp.d : ℂ) ^ 2 * ∑ x ∈ hfin.toFinset, ((m x : ℂ)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hmdeg x (hfin.mem_toFinset.mp hx)]
      ring
    rw [h2] at hC
    exact_mod_cast hC
  rw [← key]
  exact mul_le_mul_of_nonneg_left hmsum (sq_nonneg _)

/-- **`𝒮(·)` is antitone**: a smaller kernel condition admits more characters,
`R₁ ≤ R₂ ⟹ 𝒮(R₂) ⊆ 𝒮(R₁)`. -/
theorem ssetOf_antitone {R₁ R₂ : Subgroup G} (hR : R₁ ≤ R₂) :
    hyp.SsetOf R₂ ⊆ hyp.SsetOf R₁ := by
  rintro χ ⟨hχS, hker⟩
  exact ⟨hχS, fun x hx => hker x (hR hx)⟩

/-- `S'·Q₂ ≤ Q'` for `Q₂ ≤ [Q₁,Q₁]`: both `S' = [S,S]` and `[Q₁,Q₁]` sit inside
`Q' = [Q,Q]` (commutator monotonicity), so `𝒮(Q') ⊆ 𝒮(S'·Q₂)` — the reduction
steps' base families contain the degree-`d` anchors of the Remark. -/
theorem sup_Sder_le_Qder {Q₂ : Subgroup G} (hQ₂ : Q₂ ≤ ⁅hyp.Q1, hyp.Q1⁆) :
    hyp.Sder ⊔ Q₂ ≤ hyp.Qder := by
  refine sup_le ?_ (le_trans hQ₂ ?_)
  · exact Subgroup.commutator_mono hyp.S_le_Q hyp.S_le_Q
  · exact Subgroup.commutator_mono hyp.Q1_le_Q hyp.Q1_le_Q

/-! ## The §7 hypothesis for the full family `𝒮` (Lemma 1(a) ambient input)

`coherent_adjoin_of_degree_bound` consumes an `S07.Hypothesis` for the *ambient*
family `𝒮`; the `𝒮(Q')`-level construction above specialises it.  The pieces
mirror the `𝒮(Q')` versions with the degree-`d` constancy replaced by the general
`χ(1) = d·m` (real, so conjugate degrees agree). -/

section FullSsetHypothesis

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
variable [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥hyp.H]
  [Invertible (Nat.card ↥hyp.H : ℂ)]
  [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)] in
/-- **`𝒮` is closed under complex conjugation** (the `Qder`-free form of
`conj_mem_SsetOf_Qder`). -/
theorem conj_mem_Sset [Finite G] {χ : ClassFunction ↥hyp.H ℂ}
    (hχ : χ ∈ hyp.Sset) : χ.conj ∈ hyp.Sset := by
  obtain ⟨hirr, hker1⟩ := hχ
  refine ⟨hirr.conj, ?_⟩
  intro hall
  apply hker1
  intro x hxQ1
  have := hall x hxQ1
  rw [ClassFunction.conj_apply, ClassFunction.conj_apply] at this
  exact star_injective this

omit [Fintype G] [Fintype ↥hyp.H] in
/-- **The conjugate difference of a member of `𝒮` is `A`-supported**: at `1` the
degrees agree (`χ(1) = d·m` is a natural number, hence real and conjugation-fixed),
and off `Q` both `χ` and `χ̄` vanish. -/
theorem conj_diff_support_subset_A_of_mem_Sset [Finite G]
    {χ : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) :
    ((χ.conj - χ : ClassFunction ↥hyp.H ℂ)).support ⊆ hyp.A := by
  let : Fintype ↥hyp.H := Fintype.ofFinite _
  intro x hx
  rw [ClassFunction.mem_support] at hx
  by_contra hxA
  apply hx
  rw [ClassFunction.sub_apply]
  by_cases hx1 : x = 1
  · subst hx1
    obtain ⟨m, -, hm⟩ := hyp.exists_apply_one_eq_d_mul hχ
    rw [ClassFunction.conj_apply, hm,
      show ((hyp.d : ℂ) * (m : ℂ)) = ((hyp.d * m : ℕ) : ℂ) by push_cast; ring,
      star_natCast, sub_self]
  · have hxQ : (x : G) ∉ hyp.Q := fun hQ => hxA ⟨hQ, hx1⟩
    have h0 := apply_eq_zero_of_mem_Sset_of_not_mem_Q hyp hχ hxQ
    rw [ClassFunction.conj_apply, h0, star_zero, sub_zero]

omit [Fintype G] [Fintype ↥hyp.H] in
/-- **The conjugate difference vanishes at `1`** (degrees are conjugation-fixed
naturals). -/
theorem conj_diff_apply_one_of_mem_Sset [Finite G]
    {χ : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) :
    (χ.conj - χ : ClassFunction ↥hyp.H ℂ) (1 : ↥hyp.H) = 0 := by
  obtain ⟨m, -, hm⟩ := hyp.exists_apply_one_eq_d_mul hχ
  rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hm,
    show ((hyp.d : ℂ) * (m : ℂ)) = ((hyp.d * m : ℕ) : ℂ) by push_cast; ring,
    star_natCast, sub_self]

/-- **The Lemma 2(b) isometry on the `A`-supported `𝒮`-sublattice** (the
`tau_isometry_diff` field of the full-`𝒮` §7 hypothesis; the `𝒮(Q')` version
specialises via span monotonicity). -/
theorem tau_inner_eq_of_supported_Sset [Finite G]
    ⦃φ ψ : ClassFunction ↥hyp.H ℂ⦄
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) hyp.Sset hyp.A)
    (hψ : ψ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) hyp.Sset hyp.A) :
    ClassFunction.inner (hyp.tau φ) (hyp.tau ψ) = ClassFunction.inner φ ψ := by
  have hφ1 : φ (1 : ↥hyp.H) = 0 := by
    by_contra h0
    exact hyp.one_notMem_A (hφ.2 (ClassFunction.mem_support.mpr h0))
  have hψ1 : ψ (1 : ↥hyp.H) = 0 := by
    by_contra h0
    exact hyp.one_notMem_A (hψ.2 (ClassFunction.mem_support.mpr h0))
  exact (induction_isometry_on_degree_zero hyp φ ψ hφ.1 hψ.1 hφ1 hψ1).1

/-- **The (5.2.d) difference image for a member of `𝒮`** (`Sset`-level mirror of
`ssetOfQderDifferenceImage`): both keystone differences lie in the `A`-supported
`𝒮`-sublattice, so the (1.4) inputs come from Lemma 2(b); non-reality is
Lemma 2(c). -/
noncomputable def ssetDifferenceImage [Finite G] (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    {χ : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage hyp.tau χ := by
  classical
  have hχc : χ.conj ∈ hyp.Sset := hyp.conj_mem_Sset hχ
  set χb : IrreducibleCharacter ↥hyp.H := ⟨χ, hχ.1⟩ with hχb
  set fam : Fin 2 → IrreducibleCharacter ↥hyp.H :=
    OddOrder.Peterfalvi.S07.conjPairFamily (L := ↥hyp.H) χb with hfam
  have hfam0 : (fam 0 : ClassFunction ↥hyp.H ℂ) = χ := by
    simp [hfam, OddOrder.Peterfalvi.S07.conjPairFamily, hχb]
  have hfam1 : (fam 1 : ClassFunction ↥hyp.H ℂ) = χ.conj := by
    simp [hfam, OddOrder.Peterfalvi.S07.conjPairFamily, hχb]
  have hdiff0 : irreducibleCharacterDifference fam 0 = 0 := by
    simp [irreducibleCharacterDifference]
  have hdiff1 : irreducibleCharacterDifference fam 1 = χ.conj - χ := by
    simp only [irreducibleCharacterDifference, hfam1, hfam0]
  have hmem : ∀ i, irreducibleCharacterDifference fam i
      ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) hyp.Sset hyp.A := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [hdiff0]
      exact ⟨Submodule.zero_mem _,
        fun x hx => absurd (ClassFunction.zero_apply x) (ClassFunction.mem_support.mp hx)⟩
    · rw [hdiff1]
      exact ⟨Submodule.sub_mem _ (Submodule.subset_span hχc) (Submodule.subset_span hχ),
        hyp.conj_diff_support_subset_A_of_mem_Sset hχ⟩
  refine OddOrder.Peterfalvi.S07.characterDifferenceImageOfIsometry hyp.tau χb
    ((hasNoRealCharacters_Sset hyp hd hQ1odd) hχ) ?_ ?_ ?_
  · change ∀ i, isometryDifferenceImage hyp.tau fam i ∈ ZIrr G
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · change hyp.tau (irreducibleCharacterDifference fam 0) ∈ ZIrr G
      rw [hdiff0, map_zero]
      exact Submodule.zero_mem _
    · change hyp.tau (irreducibleCharacterDifference fam 1) ∈ ZIrr G
      rw [hdiff1]
      exact hyp.tau_mem_ZIrr (Submodule.sub_mem _
        (Submodule.subset_span hχc) (Submodule.subset_span hχ))
  · change ∀ i, isometryDifferenceImage hyp.tau fam i (1 : G) = 0
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · change hyp.tau (irreducibleCharacterDifference fam 0) (1 : G) = 0
      rw [hdiff0, map_zero]
      exact ClassFunction.zero_apply _
    · change hyp.tau (irreducibleCharacterDifference fam 1) (1 : G) = 0
      rw [hdiff1]
      exact hyp.tau_apply_one (hyp.conj_diff_apply_one_of_mem_Sset hχ)
  · intro i j
    exact hyp.tau_inner_eq_of_supported_Sset (hmem i) (hmem j)

/-- **(5.2.e) orthogonality of the `𝒮` difference images** (`Sset`-level mirror of
`ssetOfQderDifferenceImages_orthogonal`). -/
theorem ssetDifferenceImages_orthogonal [Finite G] (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    {φ χ : ClassFunction ↥hyp.H ℂ} (hφ : φ ∈ hyp.Sset) (hχ : χ ∈ hyp.Sset)
    (h1 : ClassFunction.inner φ χ = 0) (h2 : ClassFunction.inner φ χ.conj = 0) :
    (hyp.ssetDifferenceImage hd hQ1odd hφ).Orthogonal
      (hyp.ssetDifferenceImage hd hQ1odd hχ) := by
  have hφc := hyp.conj_mem_Sset hφ
  have hχc := hyp.conj_mem_Sset hχ
  have hself : ∀ ⦃ζ : ClassFunction ↥hyp.H ℂ⦄, ζ ∈ hyp.Sset →
      ClassFunction.inner ζ ζ = 1 := by
    intro ζ hζ
    have h := irreducibleCharacter_inner_eq_ite (G := ↥hyp.H)
      (⟨ζ, hζ.1⟩ : IrreducibleCharacter ↥hyp.H) (⟨ζ, hζ.1⟩ : IrreducibleCharacter ↥hyp.H)
    rw [if_pos rfl] at h
    simpa using h
  refine
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage.orthogonal_of_signedDifference_inner_eq_zero
    _ _ ?_
  rw [← (hyp.ssetDifferenceImage hd hQ1odd hφ).image_conjugateDifference,
      ← (hyp.ssetDifferenceImage hd hQ1odd hχ).image_conjugateDifference]
  change ClassFunction.inner (hyp.tau (φ - φ.conj)) (hyp.tau (χ - χ.conj)) = 0
  have hmemφ : (φ - φ.conj : ClassFunction ↥hyp.H ℂ)
      ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) hyp.Sset hyp.A :=
    ⟨Submodule.sub_mem _ (Submodule.subset_span hφ) (Submodule.subset_span hφc),
      fun x hx => hyp.conj_diff_support_subset_A_of_mem_Sset hφ (by
        rw [ClassFunction.mem_support] at hx ⊢
        intro h0
        apply hx
        rw [show φ - φ.conj = -(φ.conj - φ) by abel, ClassFunction.neg_apply, h0, neg_zero])⟩
  have hmemχ : (χ - χ.conj : ClassFunction ↥hyp.H ℂ)
      ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) hyp.Sset hyp.A :=
    ⟨Submodule.sub_mem _ (Submodule.subset_span hχ) (Submodule.subset_span hχc),
      fun x hx => hyp.conj_diff_support_subset_A_of_mem_Sset hχ (by
        rw [ClassFunction.mem_support] at hx ⊢
        intro h0
        apply hx
        rw [show χ - χ.conj = -(χ.conj - χ) by abel, ClassFunction.neg_apply, h0, neg_zero])⟩
  rw [hyp.tau_inner_eq_of_supported_Sset hmemφ hmemχ]
  have hne1 : φ.conj ≠ χ := by
    intro heq
    have hcc : χ.conj = φ := by rw [← heq, ClassFunction.conj_conj]
    rw [hcc, hself hφ] at h2
    exact one_ne_zero h2
  have hne2 : φ.conj ≠ χ.conj := by
    intro heq
    have hpc : φ = χ := by
      have h := congrArg ClassFunction.conj heq
      rwa [ClassFunction.conj_conj, ClassFunction.conj_conj] at h
    rw [hpc, hself hχ] at h1
    exact one_ne_zero h1
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, h1, h2,
    hyp.Sset_pairwiseOrthogonal hφc hχ hne1,
    hyp.Sset_pairwiseOrthogonal hφc hχc hne2]
  ring

omit [Fintype G] [Fintype ↥hyp.H] in
/-- **Degree-matched scaled differences of members of `𝒮` are `A`-supported** (the
`hdegdiffsupp` input of Lemma 1(a)): if `n·a(1) = m·b(1)` then `n•a − m•b` vanishes
at `1`, and off `Q` both members vanish. -/
theorem scaled_diff_support_subset_A_of_mem_Sset [Finite G]
    {a b : ClassFunction ↥hyp.H ℂ} (ha : a ∈ hyp.Sset) (hb : b ∈ hyp.Sset)
    {n m : ℕ} (hdeg : (n : ℂ) * a (1 : ↥hyp.H) = (m : ℂ) * b (1 : ↥hyp.H)) :
    ((n • a - m • b : ClassFunction ↥hyp.H ℂ)).support ⊆ hyp.A := by
  let : Fintype ↥hyp.H := Fintype.ofFinite _
  intro x hx
  rw [ClassFunction.mem_support] at hx
  by_contra hxA
  apply hx
  rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ n a,
    ← Nat.cast_smul_eq_nsmul ℂ m b, ClassFunction.smul_apply, ClassFunction.smul_apply]
  by_cases hx1 : x = 1
  · subst hx1
    rw [hdeg, sub_self]
  · have hxQ : (x : G) ∉ hyp.Q := fun hQ => hxA ⟨hQ, hx1⟩
    rw [apply_eq_zero_of_mem_Sset_of_not_mem_Q hyp ha hxQ,
      apply_eq_zero_of_mem_Sset_of_not_mem_Q hyp hb hxQ, mul_zero, mul_zero, sub_self]

/-- **The §7 (5.2) hypothesis for the full family `𝒮`** — the ambient input of
Lemma 1(a) (`coherent_adjoin_of_degree_bound`) throughout the Theorem's proof. -/
noncomputable def ssetS07Hypothesis [Finite G] (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1)) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.H) (G := G) hyp.Sset hyp.A where
  tau := hyp.tau
  tau_isometry_diff := fun _ _ hφ hψ => hyp.tau_inner_eq_of_supported_Sset hφ hψ
  conjugate_closed := fun _ hχ => hyp.conj_mem_Sset hχ
  no_real_characters := hasNoRealCharacters_Sset hyp hd hQ1odd
  pairwise_orthogonal := hyp.Sset_pairwiseOrthogonal
  difference_image := fun _ hχ => hyp.ssetDifferenceImage hd hQ1odd hχ
  difference_images_orthogonal := fun _ _ hφ hχ h1 h2 =>
    hyp.ssetDifferenceImages_orthogonal hd hQ1odd hφ hχ h1 h2

/-- **Peterfalvi p. 144, Lemma 1(a), positive direction with a general anchor
degree** (issue 1054, step (3) Part A): adjoining a fresh conjugate pair `{χ, χ̄}`
(`χ ∈ 𝒮`, `χ, χ̄ ∉ S₁`) to a coherent, conjugation-closed finite `S₁ ⊆ 𝒮`
*preserves coherence* under Peterfalvi's degree inequality.  Degrees are recorded
in units of `d`: members have `x(1) = d·m(x)` (`hmdeg`), the anchor `χ₀ ∈ S₁` has
degree `d·m(χ₀)` with `m(χ₀) ∣ a`, where `χ(1) = d·a` (member ratios may be
rational — issue 1050);
Peterfalvi's inequality `2·χ₀(1)·χ(1) < ∑_{x ∈ S₁} x(1)²` appears with `d²`
cancelled, as `2·m(χ₀)·a < ∑_{x ∈ S₁} m(x)²` (`hlt`).  All structural inputs of
Lemma 1(a) — orthonormality, `A`-support, `τ`-facts, enumeration — are supplied
unconditionally from the `𝒮`-level toolkit (`ssetS07Hypothesis` and friends).
This is the wrapper the chain adjoins of step (3) Part A consume; the degree-`d`
anchor contrapositive `sq_ratio_sum_le_of_adjoin_incoherent` specialises it at
`m(χ₀) = 1`. -/
theorem coherent_insert_pair_of_two_mul_lt_sum [Finite G] (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    {S₁ : Set (ClassFunction ↥hyp.H ℂ)} (hS₁S : S₁ ⊆ hyp.Sset) (hS₁fin : S₁.Finite)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁ hyp.A))
    {χ₀ : ClassFunction ↥hyp.H ℂ} (hχ₀S₁ : χ₀ ∈ S₁)
    {m : ClassFunction ↥hyp.H ℂ → ℕ}
    (hmdeg : ∀ x ∈ S₁, x (1 : ↥hyp.H) = (hyp.d : ℂ) * (m x : ℂ))
    (hm₀pos : 0 < m χ₀)
    {χ : ClassFunction ↥hyp.H ℂ} (hχS : χ ∈ hyp.Sset)
    (hχS₁ : χ ∉ S₁) (hχbarS₁ : χ.conj ∉ S₁)
    {a : ℕ} (hχdeg : χ (1 : ↥hyp.H) = (hyp.d : ℂ) * (a : ℂ)) (hdvd : m χ₀ ∣ a)
    (hlt : 2 * (m χ₀ : ℝ) * (a : ℝ) < ∑ x ∈ hS₁fin.toFinset, ((m x : ℝ)) ^ 2) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (S₁ ∪ {χ, χ.conj}) hyp.A) := by
  classical
  have hself : ∀ ⦃ζ : ClassFunction ↥hyp.H ℂ⦄, ζ ∈ hyp.Sset →
      ClassFunction.inner ζ ζ = 1 := by
    intro ζ hζ
    have h := irreducibleCharacter_inner_eq_ite (G := ↥hyp.H)
      (⟨ζ, hζ.1⟩ : IrreducibleCharacter ↥hyp.H) (⟨ζ, hζ.1⟩ : IrreducibleCharacter ↥hyp.H)
    rw [if_pos rfl] at h
    simpa using h
  have hmem : ∀ {i : ClassFunction ↥hyp.H ℂ}, i ∈ hS₁fin.toFinset → i ∈ S₁ :=
    fun hi => hS₁fin.mem_toFinset.mp hi
  -- `(a / m χ₀) · m χ₀ = a` in `ℂ` (`m χ₀ ∣ a`), converting `χ(1) = d·a` to
  -- Lemma 1(a)'s anchor-unit form `χ(1) = (a / m χ₀) · (d · m χ₀)`.
  have hm₀C : ((a / m χ₀ : ℕ) : ℂ) * (m χ₀ : ℂ) = (a : ℂ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  refine coherent_adjoin_of_degree_bound (hyp.ssetS07Hypothesis hd hQ1odd)
    hyp.one_notMem_A hS₁S hcoh hχS (hself hχS) (hself (hyp.conj_mem_Sset hχS))
    (fun x hx => hyp.Sset_pairwiseOrthogonal hχS (hS₁S hx) (fun h => hχS₁ (h ▸ hx)))
    (fun x hx => hyp.Sset_pairwiseOrthogonal (hyp.conj_mem_Sset hχS) (hS₁S hx)
      (fun h => hχbarS₁ (h ▸ hx)))
    (hyp.conj_diff_support_subset_A_of_mem_Sset hχS)
    hS₁fin.toFinset id (fun x => hyp.d * m x) χ₀ (hS₁fin.mem_toFinset.mpr hχ₀S₁)
    (fun x hx => ⟨x, hS₁fin.mem_toFinset.mpr hx, rfl⟩)
    (fun _ hi => hmem hi)
    (fun _ hi => hS₁conj (hmem hi))
    (fun i hi j hj => by
      by_cases hij : i = j
      · rw [if_pos hij, hij]
        exact hself (hS₁S (hmem hj))
      · rw [if_neg hij]
        exact hyp.Sset_pairwiseOrthogonal (hS₁S (hmem hi)) (hS₁S (hmem hj)) hij)
    (fun i hi => hyp.Sset_pairwiseOrthogonal (hS₁S (hmem hi))
      (hyp.conj_mem_Sset (hS₁S (hmem hi)))
      (fun h => (hasNoRealCharacters_Sset hyp hd hQ1odd) (hS₁S (hmem hi)) h.symm))
    (Nat.mul_pos hyp.d_pos hm₀pos)
    (fun i hi => by
      rw [show ((id i : ClassFunction ↥hyp.H ℂ) : ↥hyp.H → ℂ) 1 = i (1 : ↥hyp.H) from rfl,
        hmdeg i (hmem hi)]
      push_cast
      ring)
    (fun i hi => hyp.conj_diff_support_subset_A_of_mem_Sset (hS₁S (hmem hi)))
    (fun i hi => hyp.scaled_diff_support_subset_A_of_mem_Sset
      (hS₁S (hmem hi)) (hS₁S hχ₀S₁)
      (by rw [hmdeg i (hmem hi), hmdeg χ₀ hχ₀S₁]; push_cast; ring))
    (a := a / m χ₀)
    (by
      rw [show ((χ : ClassFunction ↥hyp.H ℂ) : ↥hyp.H → ℂ) 1 = χ (1 : ↥hyp.H) from rfl,
        hχdeg, ← hm₀C]
      push_cast
      ring)
    (by
      have h := hyp.scaled_diff_support_subset_A_of_mem_Sset hχS (hS₁S hχ₀S₁)
        (n := 1) (m := a / m χ₀)
        (by rw [hχdeg, hmdeg χ₀ hχ₀S₁, ← hm₀C]; push_cast; ring)
      simpa [one_smul] using h)
    (hyp.tau_mem_ZIrr (Submodule.sub_mem _ (Submodule.subset_span hχS)
      (by
        change ((a / m χ₀) • χ₀ : ClassFunction ↥hyp.H ℂ) ∈ _
        rw [← Nat.cast_smul_eq_nsmul ℤ (a / m χ₀) χ₀]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (hS₁S hχ₀S₁)))))
    (by
      have hdR : (hyp.d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.d_pos.ne'
      have hm₀R : (0 : ℝ) < (m χ₀ : ℝ) := by exact_mod_cast hm₀pos
      -- `(a / m χ₀ : ℕ)` casts to the real quotient (`m χ₀ ∣ a`).
      have ha' : ((a / m χ₀ : ℕ) : ℝ) = (a : ℝ) / (m χ₀ : ℝ) := by
        rw [eq_div_iff hm₀R.ne', ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
      -- the `d`-factors of the degree ratios cancel, leaving `m x / m χ₀`
      have hsum : ∑ x ∈ hS₁fin.toFinset,
          (((hyp.d * m x : ℕ) : ℝ) / ((hyp.d * m χ₀ : ℕ) : ℝ)) ^ 2
          = (∑ x ∈ hS₁fin.toFinset, ((m x : ℝ)) ^ 2) / ((m χ₀ : ℝ)) ^ 2 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← div_pow]
        congr 1
        push_cast
        rw [mul_div_mul_left _ _ hdR]
      rw [ha', hsum, lt_div_iff₀ (pow_pos hm₀R 2)]
      calc 2 * ((a : ℝ) / (m χ₀ : ℝ)) * ((m χ₀ : ℝ)) ^ 2
          = 2 * ((a : ℝ) / (m χ₀ : ℝ) * (m χ₀ : ℝ)) * (m χ₀ : ℝ) := by ring
        _ = 2 * (a : ℝ) * (m χ₀ : ℝ) := by rw [div_mul_cancel₀ _ hm₀R.ne']
        _ = 2 * (m χ₀ : ℝ) * (a : ℝ) := by ring
        _ < _ := hlt)

/-- **The counterexample degree bound** (the reductions' "by Lemma 1(a), there is a
`ψ` with `∑ χ(1)² ≤ 2dψ(1)`"): if adjoining the fresh conjugate pair `{χ, χ̄}` to a
coherent, conjugation-closed `S₁ ⊆ 𝒮` containing a degree-`d` anchor *breaks*
coherence, then Lemma 1(a)'s strict degree inequality must fail:
`∑_{x ∈ S₁} m(x)² ≤ 2a`, where `x(1) = d·m(x)` and `χ(1) = d·a`.  The
contrapositive of `coherent_insert_pair_of_two_mul_lt_sum` at the degree-`d`
anchor (`m(χ₀) = 1`, so both divisibility inputs are trivial and the inequality
reads `2a < ∑ m(x)²`). -/
theorem sq_ratio_sum_le_of_adjoin_incoherent [Finite G] (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    {S₁ : Set (ClassFunction ↥hyp.H ℂ)} (hS₁S : S₁ ⊆ hyp.Sset) (hS₁fin : S₁.Finite)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁ hyp.A))
    {χ₀ : ClassFunction ↥hyp.H ℂ} (hχ₀S₁ : χ₀ ∈ S₁)
    (hχ₀deg : χ₀ (1 : ↥hyp.H) = (hyp.d : ℂ))
    {χ : ClassFunction ↥hyp.H ℂ} (hχS : χ ∈ hyp.Sset)
    (hχS₁ : χ ∉ S₁) (hχbarS₁ : χ.conj ∉ S₁)
    {a : ℕ} (hχdeg : χ (1 : ↥hyp.H) = (hyp.d : ℂ) * (a : ℂ))
    (hfail : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (S₁ ∪ {χ, χ.conj}) hyp.A)) :
    ∃ m : ClassFunction ↥hyp.H ℂ → ℕ,
      (∀ x ∈ S₁, x (1 : ↥hyp.H) = (hyp.d : ℂ) * (m x : ℂ)) ∧
      (∑ x ∈ hS₁fin.toFinset, ((m x : ℝ)) ^ 2) ≤ 2 * (a : ℝ) := by
  classical
  have hm : ∀ x ∈ S₁, ∃ mx : ℕ, x (1 : ↥hyp.H) = (hyp.d : ℂ) * (mx : ℂ) :=
    fun x hx => (hyp.exists_apply_one_eq_d_mul (hS₁S hx)).imp fun _ h => h.2
  choose! m hmdeg using hm
  refine ⟨m, hmdeg, ?_⟩
  by_contra hlt
  push Not at hlt
  apply hfail
  have hd0 : (hyp.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.d_pos.ne'
  have hmχ₀ : m χ₀ = 1 := by
    have h1 := hmdeg χ₀ hχ₀S₁
    rw [hχ₀deg] at h1
    have h2 : (hyp.d : ℂ) * 1 = (hyp.d : ℂ) * (m χ₀ : ℂ) := by rw [mul_one]; exact h1
    have h3 := mul_left_cancel₀ hd0 h2
    exact_mod_cast h3.symm
  exact hyp.coherent_insert_pair_of_two_mul_lt_sum hd hQ1odd hS₁S hS₁fin hS₁conj hcoh
    hχ₀S₁ hmdeg (by rw [hmχ₀]; exact Nat.one_pos)
    hχS hχS₁ hχbarS₁ hχdeg (by rw [hmχ₀]; exact one_dvd _)
    (by rw [hmχ₀]; simpa using hlt)

/-- **The reductions' counterexample extraction** (Peterfalvi's "Suppose `𝒮(…)` is
not coherent.  By Lemma 1(a), there is a character `ψ` such that
`∑ χ(1)² ≤ 2dψ(1)`"): if a coherent, conjugation-closed base `B` (containing a
degree-`d` anchor) sits inside a finite, conjugation-closed `Y ⊆ 𝒮` that is *not*
coherent, then some `ψ ∈ Y` of degree `d·a` bounds the base's degree data:
`∑_{x ∈ B} m(x)² ≤ 2a`.

Assembles the three-part machinery: the conjugate-pair decomposition
(`exists_conjPair_pairUnion_eq`), the first incoherent step
(`exists_first_incoherent_step`), and the Lemma 1(a) contrapositive
(`sq_ratio_sum_le_of_adjoin_incoherent`), restricting the resulting sum from the
accumulated family to `B` (squares are nonnegative). -/
theorem exists_counterexample_of_not_coherent [Finite G] (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    {B Y : Set (ClassFunction ↥hyp.H ℂ)} (hBY : B ⊆ Y) (hYS : Y ⊆ hyp.Sset)
    (hYfin : Y.Finite)
    (hYconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Y)
    (hBconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate B)
    (hcohB : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau B hyp.A))
    {χ₀ : ClassFunction ↥hyp.H ℂ} (hχ₀B : χ₀ ∈ B)
    (hχ₀deg : χ₀ (1 : ↥hyp.H) = (hyp.d : ℂ))
    (hfail : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)) :
    ∃ (ψ : ClassFunction ↥hyp.H ℂ) (a : ℕ) (m : ClassFunction ↥hyp.H ℂ → ℕ),
      ψ ∈ Y ∧ 0 < a ∧ ψ (1 : ↥hyp.H) = (hyp.d : ℂ) * (a : ℂ) ∧
      (∀ x ∈ B, x (1 : ↥hyp.H) = (hyp.d : ℂ) * (m x : ℂ)) ∧
      (∑ x ∈ (hYfin.subset hBY).toFinset, ((m x : ℝ)) ^ 2) ≤ 2 * (a : ℝ) := by
  classical
  have hnoreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters Y :=
    (hasNoRealCharacters_Sset hyp hd hQ1odd).mono hYS
  obtain ⟨N, pair, hUnion, hstep, -⟩ :=
    exists_conjPair_pairUnion_eq hBY hYfin hYconj hBconj hnoreal
  obtain ⟨i, hiN, hcoh_i, hfail_i⟩ :=
    exists_first_incoherent_step (τ := hyp.tau) (A := hyp.A) hcohB (hUnion ▸ hfail)
  obtain ⟨hconj_i, hmemY_i, hfresh1, hfresh2⟩ := hstep i hiN
  -- the accumulated family `S₁ = pairUnion B pair i` and its closure properties
  have hsub : ∀ j, j ≤ N →
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair j ⊆ Y := by
    intro j hjN x hx
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hx with hB | ⟨k, hkj, hk⟩
    · exact hBY hB
    · have hkN : k < N := by omega
      obtain ⟨hc, hY1, -, -⟩ := hstep k hkN
      rcases (by simpa [OddOrder.Peterfalvi.S07.pairSet] using hk : x = (pair k).1 ∨
          x = (pair k).2) with rfl | rfl
      · exact hY1
      · rw [hc]
        exact hYconj hY1
  have hconj_closed : ∀ j, j ≤ N → OddOrder.Peterfalvi.S03.ClosedUnderConjugate
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair j) := by
    intro j hjN
    induction j with
    | zero => simpa using hBconj
    | succ j ihj =>
      intro x hx
      rw [OddOrder.Peterfalvi.S07.pairUnion_succ] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihj (by omega) hx)
      · obtain ⟨hcj, -, -, -⟩ := hstep j (by omega)
        rcases (by simpa [OddOrder.Peterfalvi.S07.pairSet] using hx : x = (pair j).1 ∨
            x = (pair j).2) with rfl | rfl
        · exact Or.inr (by
            rw [← hcj]
            simp [OddOrder.Peterfalvi.S07.pairSet])
        · exact Or.inr (by
            rw [hcj, ClassFunction.conj_conj]
            simp [OddOrder.Peterfalvi.S07.pairSet])
  -- degree data of the failing pair's first member
  have hψY : (pair i).1 ∈ Y := hmemY_i
  obtain ⟨a, hapos, hadeg⟩ := hyp.exists_apply_one_eq_d_mul (hYS hψY)
  -- apply the Lemma 1(a) contrapositive at the failing step
  have hS₁S : OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair i ⊆ hyp.Sset :=
    fun x hx => hYS (hsub i (by omega) hx)
  have hχ₀S₁ : χ₀ ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair i :=
    OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hχ₀B)
  have hfail' : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      ((OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair i)
        ∪ {(pair i).1, ((pair i).1).conj}) hyp.A) := by
    intro h
    apply hfail_i
    rw [OddOrder.Peterfalvi.S07.pairUnion_succ]
    have hps : OddOrder.Peterfalvi.S07.pairSet (L := ↥hyp.H) pair i
        = {(pair i).1, ((pair i).1).conj} := by
      rw [OddOrder.Peterfalvi.S07.pairSet, hconj_i]
    rw [hps]
    exact h
  have hfresh2' : ((pair i).1).conj ∉
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥hyp.H) B pair i := by
    rw [← hconj_i]
    exact hfresh2
  obtain ⟨m, hmdeg, hmsum⟩ := hyp.sq_ratio_sum_le_of_adjoin_incoherent hd hQ1odd
    hS₁S (hYfin.subset (hsub i (by omega))) (hconj_closed i (by omega)) hcoh_i
    hχ₀S₁ hχ₀deg (hYS hψY) hfresh1 hfresh2' hadeg hfail'
  refine ⟨(pair i).1, a, m, hψY, hapos, hadeg,
    fun x hx => hmdeg x (OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hx)), ?_⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hmsum
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx ⊢
    exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hx)
  · intro x _ _
    positivity

end FullSsetHypothesis

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
