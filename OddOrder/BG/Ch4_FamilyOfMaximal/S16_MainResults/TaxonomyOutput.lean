import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.TypeBridges
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.LocalTaxonomy

/-!
# BG Proposition 16.1 taxonomy + Theorems I/II (Peterfalvi が消費する出力)

Split from the former monolithic `OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults` (directory split,
issue 0103).
-/

namespace OddOrder.BG.Ch4.S16
open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S14
open OddOrder.BG.Ch4.S15
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Theorems I and II: the BG output consumed by Peterfalvi -/

/-- **§16 helper (general, §14-independent).**  A `π`-Hall subgroup `H` of `G` contained in a
subgroup `K` is a `π`-Hall subgroup of `K` (no normality needed): the order of `H.subgroupOf K`
equals `|H|` (so its prime factors are `⊆ π`), and its index `[K : H] = H.relIndex K` divides
`[G : H]` (so the index prime factors avoid `π`).  Used in Theorem I to turn the global nilpotent
Hall hypothesis on `H` into the `H.subgroupOf M_σ`-Hall hypothesis that Corollary 15.3(b)
(`mf_hall_centralizer_control`) consumes, after Corollary 15.4 places `H ≤ M_σ`. -/
theorem isHallSubgroup_subgroupOf_of_le [Finite G] {π : Set ℕ} {H K : Subgroup G}
    (hH : Ch03.IsHallSubgroup π H) (hHK : H ≤ K) :
    Ch03.IsHallSubgroup π (H.subgroupOf K) := by
  have hcard : Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  refine ⟨?_, ?_⟩
  · -- `|H.subgroupOf K| = |H|`, so its prime factors are exactly those of `|H| ⊆ π`.
    intro q hq
    rw [hcard] at hq
    exact hH.1 q hq
  · -- `[K : H] = H.relIndex K ∣ [G : H]`, so its prime factors avoid `π`.
    intro q hq hqπ
    have hdvd : (H.subgroupOf K).index ∣ H.index := by
      have he : (H.subgroupOf K).index = H.relIndex K := rfl
      rw [he]
      exact Subgroup.relIndex_dvd_index_of_le hHK
    rw [Nat.mem_primeFactors] at hq
    exact hH.2 q (Nat.mem_primeFactors.mpr
      ⟨hq.1, hq.2.1.trans hdvd, Subgroup.index_ne_zero_of_finite⟩) hqπ

/-- **§16 helper** (issue 8005): the `κ(M)`-Hall factor of a type-P maximal subgroup is
nontrivial — `κ(M)` is nonempty, each `p ∈ κ(M)` divides `|M|` via the rank-one witness
`P ≤ M`, and the Hall subgroup must catch that `p` (else `p` divides its index). -/
theorem kappaHall_ne_bot_of_isTypeP [Finite G] {M K : Subgroup G}
    (hP : S14.IsTypeP M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) : K ≠ ⊥ := by
  obtain ⟨p, hpκ⟩ := hP
  obtain ⟨hpprime, -, P, hPmem, hPM, -⟩ := id hpκ
  have hcardP : Nat.card ↥P = p := by
    have h := (mem_elemAbelianOfRank.mp hPmem).2
    rwa [pow_one] at h
  have hpM : p ∣ Nat.card ↥M := hcardP ▸ Subgroup.card_dvd_of_le hPM
  intro hKbot
  have hidx : (K.subgroupOf M).index = Nat.card ↥M := by
    rw [hKbot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
  exact hK.2 p (Nat.mem_primeFactors.mpr
    ⟨hpprime, hidx ▸ hpM, hidx ▸ Nat.card_pos.ne'⟩) hpκ

/-- **§16 helper** (issue 8005): an `IsComplement'` between `subgroupOf`-images lifts to the
ambient lattice equations `A ⊔ B = M`, `A ⊓ B = ⊥` (for `A, B ≤ M`). -/
theorem sup_eq_and_inf_eq_bot_of_isComplement'_subgroupOf {M A B : Subgroup G}
    (hA : A ≤ M) (hB : B ≤ M)
    (h : Subgroup.IsComplement' (A.subgroupOf M) (B.subgroupOf M)) :
    A ⊔ B = M ∧ A ⊓ B = ⊥ := by
  constructor
  · refine le_antisymm (sup_le hA hB) ?_
    have hsup := h.sup_eq_top
    rw [← Subgroup.subgroupOf_sup hA hB] at hsup
    exact Subgroup.subgroupOf_eq_top.mp hsup
  · refine le_bot_iff.mp fun x hx => ?_
    obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
    have hxM : x ∈ M := hA hxA
    have hxb : (⟨x, hxM⟩ : ↥M) ∈ A.subgroupOf M ⊓ B.subgroupOf M :=
      ⟨Subgroup.mem_subgroupOf.mpr hxA, Subgroup.mem_subgroupOf.mpr hxB⟩
    have h1 := h.disjoint.le_bot hxb
    rw [Subgroup.mem_bot] at h1 ⊢
    exact congrArg Subtype.val h1

/-- **BG Theorem I** (mmd L4526): nilpotent Hall conjugacy and the global maximal
subgroup dichotomy used by Peterfalvi (8.8).

**Tame-embedding structure restored (issue 8005, 2026-07-25)**: the second disjunct now
carries the mmd clauses (1)(2) that the original port dropped — `W₁, W₂ ≠ 1`, the
normalizer-`V` property `N_G(W₀) = W` for every nonempty subset `W₀ ⊆ W ∖ W₁ ∖ W₂`
(from the `Ẑ` TI-property of Theorem 14.7 + `W` cyclic), and the decompositions
`S = W₁S'`, `T = W₂T'` with `S' ∩ W₁ = T' ∩ W₂ = 1` (from Theorem 14.7 part (h),
`S' = [S,S]`, `T' = [T,T]`). -/
theorem theoremI_nilpotentHall_conjugacy_and_type_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (∀ H : Subgroup G, Group.IsNilpotent ↥H →
      Ch03.IsHallSubgroup (S14.piSet H) H →
        ∀ x ∈ H, ∀ y ∈ H,
          (∃ g : G, y = g * x * g⁻¹) ↔
            ∃ n ∈ Subgroup.normalizer (H : Set G), y = n * x * n⁻¹) ∧
      ((∀ M : Subgroup G, M ∈ maximalSubgroups G → OddOrder.GroupTheory.IsTypeI M) ∨
        ∃ S T W1 W2 W : Subgroup G,
          S ∈ maximalSubgroups G ∧ T ∈ maximalSubgroups G ∧ S ≠ T ∧
          W = W1 ⊔ W2 ∧ IsCyclic ↥W ∧ S ⊓ T = W ∧
          OddOrder.GroupTheory.IsTypeNonI S ∧ OddOrder.GroupTheory.IsTypeNonI T ∧
          (OddOrder.GroupTheory.IsTypeII S ∨ OddOrder.GroupTheory.IsTypeII T) ∧
          (∀ M : Subgroup G, M ∈ maximalSubgroups G →
            OddOrder.GroupTheory.IsTypeI M ∨ S14.IsConjugateSubgroup M S ∨
              S14.IsConjugateSubgroup M T) ∧
          W1 ≠ ⊥ ∧ W2 ≠ ⊥ ∧
          (∀ W₀ : Set G, W₀ ⊆ ((W : Set G) \ (W1 : Set G)) \ (W2 : Set G) →
            W₀.Nonempty → Subgroup.normalizer W₀ = W) ∧
          ∃ S' T' : Subgroup G,
            S = W1 ⊔ S' ∧ T = W2 ⊔ T' ∧ S' ⊓ W1 = ⊥ ∧ T' ⊓ W2 = ⊥) := by
  classical
  refine ⟨?_, ?_⟩
  · -- **Theorem I, first assertion** (mmd L4524): nilpotent Hall fusion is `N_G(H)`-controlled.
    -- "follows directly from Corollaries 15.4 and 15.3(b)".
    intro H hHnil hHall x hx y hy
    constructor
    · -- `→`: `G`-conjugacy of `x, y ∈ H` is already `N_G(H)`-conjugacy.
      rintro ⟨g, hg⟩
      by_cases hHne : H = ⊥
      · -- `H = ⊥`: then `x = y = 1`, witnessed by `n = 1 ∈ N_G(H)`.
        subst hHne
        rw [Subgroup.mem_bot] at hx hy
        exact ⟨1, Subgroup.one_mem _, by rw [hx, hy]; group⟩
      · -- `H ≠ ⊥`: Corollary 15.4 embeds `H ≤ M_σ` for some `M ∈ ℳ(H)`.
        obtain ⟨M, hMmem, hHMσ⟩ :=
          S15.nilpotent_hall_embeds_in_msigma hG hHnil hHne hHall
        have hM : M ∈ maximalSubgroups G := (mem_maximalSubgroupsContaining.mp hMmem).1
        -- `H ≤ M_σ`, so `H.subgroupOf M_σ` is a `π(H)`-Hall subgroup of `M_σ`.
        have hHall' : Ch03.IsHallSubgroup (S14.piSet H)
            (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) :=
          isHallSubgroup_subgroupOf_of_le hHall hHMσ
        -- Corollary 15.3(b): `N_M(H)`-fusion control; `N_M(H) ⊆ N_G(H)`.
        obtain ⟨_, hfusion⟩ := S15.mf_hall_centralizer_control hG hM hHMσ hHall' hHne
        exact hfusion x hx y hy ⟨g, hg⟩
    · -- `←`: `N_G(H)`-conjugacy is in particular `G`-conjugacy.
      rintro ⟨n, _, hn⟩
      exact ⟨n, hn⟩
  · -- **Theorem I, dichotomy** (mmd L4528): every maximal is Type I, or the type-P pair
    -- `S, T` covers everything.  Proposition 16.1(a) + Theorem C(4)(6)(7) + Theorem 14.7 duality.
    -- **Bridge: a non-Type-I maximal is type P.**  Proposition 16.1(a) gives `TypeI ⟺ TypeF`,
    -- and `TypeF ⟺ κ(M) = ∅`, so `¬TypeI` forces `κ(M)` nonempty, i.e. `IsTypeP`.
    have notTypeI_imp_typeP : ∀ N : Subgroup G, N ∈ maximalSubgroups G →
        ¬ OddOrder.GroupTheory.IsTypeI N → S14.IsTypeP N := by
      intro N hN hnotI
      have hiff := (proposition_type_classification hG hN).1
      have hnotF : ¬ S14.IsTypeF N := fun hF => hnotI (hiff.mpr hF)
      rw [S14.IsTypeP, Set.nonempty_iff_ne_empty]
      exact fun he => hnotF he
    -- **Bridge: a type-P maximal is non-Type-I (`II`/`III`/`IV`/`V`).**  Split `κ(M)` against
    -- `π(M) - σ(M)`: equal ⟹ `P₁` ⟹ Type V (`M_F = M_σ`) or III/IV (`M_F ≠ M_σ`); unequal ⟹
    -- `P₂` ⟹ Type II.  Uses Proposition 16.1(b)(c)(d).
    have typeP_imp_nonI : ∀ N : Subgroup G, N ∈ maximalSubgroups G →
        S14.IsTypeP N → OddOrder.GroupTheory.IsTypeNonI N := by
      intro N hN hP
      obtain ⟨_, hbII, hcIII_IV, hdV, _, _⟩ := proposition_type_classification hG hN
      by_cases hk : S14.kappa N = S14.sigmaComplementPrimes N
      · -- `P₁`: Type III/IV (if `M_F ≠ M_σ`) or Type V (if `M_F = M_σ`).
        have hP1 : S14.IsTypeP1 N := ⟨hP, hk⟩
        by_cases hMF : S15.MF N = OddOrder.BG.Ch3.S10.Msigma N
        · exact Or.inr (Or.inr (Or.inr (hdV.mpr ⟨hP1, hMF⟩)))
        · rcases hcIII_IV.mpr ⟨hP1, hMF⟩ with hIII | hIV
          · exact Or.inr (Or.inl hIII)
          · exact Or.inr (Or.inr (Or.inl hIV))
      · -- `P₂`: Type II.
        exact Or.inl (hbII.mpr ⟨hP, hk⟩)
    -- Case split: either every maximal is Type I, or some `S` is not.
    by_cases hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G →
        OddOrder.GroupTheory.IsTypeI M
    · exact Or.inl hall
    · -- Pick a non-Type-I maximal `S`; it is type P.
      push Not at hall
      obtain ⟨S, hS, hSnotI⟩ := hall
      have hSP : S14.IsTypeP S := notTypeI_imp_typeP S hS hSnotI
      haveI : IsSolvable ↥S := hG.solvable_of_mem_maximalSubgroups hS
      -- Produce the `κ(S)`-Hall subgroup `K` of `S` (Hall's theorem in the solvable `S`).
      obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥S) (S14.kappa S)
      set K : Subgroup G := K'.map S.subtype with hKdef
      have hKeq : K.subgroupOf S = K' :=
        Subgroup.comap_map_eq_self_of_injective S.subtype_injective K'
      have hK : Ch03.IsHallSubgroup (S14.kappa S) (K.subgroupOf S) := by
        rw [hKeq]; exact hK'
      set Kstar : Subgroup G :=
        OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G) with hKstardef
      -- Theorem 14.7 (`typeP_duality`): the dual pair `S, T := Mstar`, with covering.
      obtain ⟨hparthS, _, Mstar, ⟨hMstarMem, hMstarP, hSnconjMstar,
          ⟨hKstarMstar, hKstar_hall, hK_eq⟩, hcyc, hTI, hP2disj, hcover⟩, _⟩ :=
        typeP_duality hG hS hSP (Subgroup.map_subtype_le K') hK hKstardef
      -- A Hall `(κ(S) ∪ σ(S))'`-subgroup `U` of `S` (Hall's theorem in the solvable `S`), needed
      -- to invoke `typeP_pair_inf_eq` (the reverse inclusion `S ∩ Mstar ≤ K ⊔ K*`).
      obtain ⟨U', hU'⟩ :=
        Ch03.hall_E_exists (G := ↥S) ((S14.kappa S ∪ OddOrder.BG.Ch3.S10.sigma S)ᶜ)
      have hUeq : (U'.map S.subtype).subgroupOf S = U' :=
        Subgroup.comap_map_eq_self_of_injective S.subtype_injective U'
      have hU : Ch03.IsHallSubgroup ((S14.kappa S ∪ OddOrder.BG.Ch3.S10.sigma S)ᶜ)
          ((U'.map S.subtype).subgroupOf S) := by rw [hUeq]; exact hU'
      refine Or.inr ⟨S, Mstar, K, Kstar, K ⊔ Kstar, hS, hMstarMem, ?_, rfl, hcyc, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_⟩
      · -- `S ≠ Mstar`: else `S` would be conjugate to itself `= Mstar`, against `¬conj S Mstar`.
        rintro rfl
        exact hSnconjMstar (S14.IsConjugateSubgroup.refl S)
      · -- `S ∩ Mstar = W = K ⊔ K*`: **BG Theorem I clause (2)** (= Theorem 14.7(4) / C(6)).  The
        -- forward inclusion is immediate; the reverse `S ∩ Mstar ≤ K ⊔ K*` is the genuine §16
        -- structural content, proved in `S16_PairIntersection` as `typeP_pair_inf_eq`.
        exact typeP_pair_inf_eq hG hS hSP (Subgroup.map_subtype_le K') hK hKstardef hU
          hMstarMem hMstarP hSnconjMstar hKstarMstar hKstar_hall hcyc hK_eq
      · -- `IsTypeNonI S`: `S` is type P.
        exact typeP_imp_nonI S hS hSP
      · -- `IsTypeNonI Mstar`: `Mstar` is type P.
        exact typeP_imp_nonI Mstar hMstarMem hMstarP
      · -- `IsTypeII S ∨ IsTypeII Mstar`: from `IsTypeP2 S ∨ IsTypeP2 Mstar` via Prop 16.1(b).
        rcases hP2disj with hP2S | hP2M
        · exact Or.inl ((proposition_type_classification hG hS).2.1.mpr hP2S)
        · exact Or.inr ((proposition_type_classification hG hMstarMem).2.1.mpr hP2M)
      · -- Covering: each maximal is Type I, or (being type P) conjugate to `S` or `Mstar`.
        intro M hM
        by_cases hMI : OddOrder.GroupTheory.IsTypeI M
        · exact Or.inl hMI
        · exact Or.inr (hcover M hM (notTypeI_imp_typeP M hM hMI))
      · -- `W₁ = K ≠ ⊥` (restored, mmd L4526 (1)): `κ(S) ≠ ∅` and `K` is its Hall factor.
        exact kappaHall_ne_bot_of_isTypeP hSP hK
      · -- `W₂ = K* ≠ ⊥` (restored): `K*` is the `κ(Mstar)`-Hall factor, `Mstar` type P.
        exact kappaHall_ne_bot_of_isTypeP hMstarP hKstar_hall
      · -- normalizer-`V` (restored, mmd L4526 (1)): `N_G(W₀) = W` for nonempty `W₀ ⊆ W∖W₁∖W₂`.
        -- `≤` is the `Ẑ` TI-property (Theorem 14.7); `≥` is `W` cyclic hence abelian.
        intro W₀ hW₀sub hW₀ne
        have hzsub : W₀ ⊆ zTilde K Kstar := by
          intro x hx
          have h := hW₀sub hx
          rw [Set.sdiff_sdiff] at h
          exact h
        refine le_antisymm ?_ ?_
        · intro g hg
          obtain ⟨x, hx⟩ := hW₀ne
          exact hTI g ⟨x, hzsub hx,
            hzsub ((Subgroup.mem_set_normalizer_iff.mp hg x).mp hx)⟩
        · intro w hw
          have hfix : ∀ n ∈ (K ⊔ Kstar : Subgroup G), w * n * w⁻¹ = n := by
            intro n hn
            haveI := hcyc
            letI : CommGroup ↥(K ⊔ Kstar : Subgroup G) := IsCyclic.commGroup
            have hcm := congrArg Subtype.val
              (mul_comm (⟨w, hw⟩ : ↥(K ⊔ Kstar : Subgroup G)) ⟨n, hn⟩)
            simp only [Subgroup.coe_mul] at hcm
            rw [mul_inv_eq_iff_eq_mul]
            exact hcm
          rw [Subgroup.mem_set_normalizer_iff]
          intro n
          constructor
          · intro hn
            rw [hfix n (hzsub hn).1]
            exact hn
          · intro hn'
            have hnW : n ∈ (K ⊔ Kstar : Subgroup G) := by
              have hmem : w * n * w⁻¹ ∈ (K ⊔ Kstar : Subgroup G) := (hzsub hn').1
              have h2 : w⁻¹ * (w * n * w⁻¹) * w ∈ (K ⊔ Kstar : Subgroup G) :=
                Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) hmem) hw
              simpa [mul_assoc] using h2
            rwa [hfix n hnW] at hn'
      · -- decompositions (restored, mmd L4526 (2)): `S = W₁S'`, `T = W₂T'` with trivial
        -- intersections, `S' = [S,S]`, `T' = [Mstar,Mstar]`, from Theorem 14.7 part (h).
        have hparthT :
            Subgroup.IsComplement' ((derivedInG Mstar).subgroupOf Mstar)
              (Kstar.subgroupOf Mstar) :=
          (typeP_duality hG hMstarMem hMstarP hKstarMstar hKstar_hall hK_eq).1
        obtain ⟨hSsup, hSinf⟩ := sup_eq_and_inf_eq_bot_of_isComplement'_subgroupOf
          (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le K') hparthS
        obtain ⟨hTsup, hTinf⟩ := sup_eq_and_inf_eq_bot_of_isComplement'_subgroupOf
          (Subgroup.map_subtype_le _) hKstarMstar hparthT
        exact ⟨derivedInG S, derivedInG Mstar,
          by rw [sup_comm]; exact hSsup.symm,
          by rw [sup_comm]; exact hTsup.symm,
          hSinf, hTinf⟩

/-- **Assembly for BG Theorem II (Ti)** (mmd L4546--L4550), as a `sorry`-free,
axiom-clean *gated-endpoint skeleton*.

The mmd proof decomposes `A_0(M)` into the disjoint pieces `M_σ`, `A(M) - M_σ`,
and `A_0(M) - A(M)`, observes that cross-piece elements have distinct orders (so
are never `G`-conjugate), and concludes:
* within `M_σ`, `G`-conjugacy is `M`-conjugacy by **Theorem D(1)** (`hD1`);
* within either TI piece (**Theorem B(5)**/`hTI_B`, **Theorem C(9)**/`hTI_C`),
  `G`-conjugacy forces the conjugator into `M` by the TI condition.

This bundles those three inputs plus the cross-piece exclusion `hPieceInv`
(`G`-conjugate elements of `X` share `M_σ`- and `A(M)`-membership — the formal
content of "distinct orders across pieces") and discharges (Ti) with no `sorry`
of its own.  The remaining gated obligation when this is applied is exactly
`hPieceInv` (BG Theorem E prime-structure of the pieces). -/
theorem theoremII_conjunct1_of_inputs {M K U : Subgroup G}
    (hD1 : ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M, ∀ y ∈ OddOrder.BG.Ch3.S10.Msigma M,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹)
    (hTI_B : IsTISubset (ASet M U \ (OddOrder.BG.Ch3.S10.Msigma M : Set G)) M)
    (hTI_C : IsTISubset (A0Set M K \ ASet M U) M)
    {X : Set G} (hX : X = ASet M U ∨ X = A0Set M K)
    (hPieceInv : ∀ x ∈ X, ∀ y ∈ X, (∃ g : G, y = g * x * g⁻¹) →
      (x ∈ OddOrder.BG.Ch3.S10.Msigma M ↔ y ∈ OddOrder.BG.Ch3.S10.Msigma M) ∧
        (x ∈ ASet M U ↔ y ∈ ASet M U)) :
    ∀ x ∈ X, ∀ y ∈ X, (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹ := by
  intro x hxX y hyX hconj
  obtain ⟨g, hg⟩ := hconj
  obtain ⟨hMσiff, hAiff⟩ := hPieceInv x hxX y hyX ⟨g, hg⟩
  by_cases hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M
  · -- Both in `M_σ`: Theorem D(1).
    exact hD1 x hxMσ y (hMσiff.mp hxMσ) ⟨g, hg⟩
  · -- `x ∉ M_σ`, hence `y ∉ M_σ`; `x, y` lie in a common TI piece.
    have hyMσ : y ∉ OddOrder.BG.Ch3.S10.Msigma M := fun h => hxMσ (hMσiff.mpr h)
    have hxMσ' : x ∉ (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by rwa [SetLike.mem_coe]
    have hyMσ' : y ∉ (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by rwa [SetLike.mem_coe]
    by_cases hxA : x ∈ ASet M U
    · -- `x, y ∈ A(M) - M_σ` (TI piece, Theorem B(5)): the conjugator lies in `M`.
      have hyA : y ∈ ASet M U := hAiff.mp hxA
      exact ⟨g, hTI_B g ⟨x, ⟨hxA, hxMσ'⟩, hg ▸ ⟨hyA, hyMσ'⟩⟩, hg⟩
    · -- `x ∉ A(M)`: only possible for `X = A_0(M)`.
      rcases hX with hXA | hXA0
      · exact absurd (hXA ▸ hxX) hxA
      · -- `x, y ∈ A_0(M) - A(M)` (TI piece, Theorem C(9)).
        have hyA : y ∉ ASet M U := fun h => hxA (hAiff.mpr h)
        exact ⟨g, hTI_C g ⟨x, ⟨hXA0 ▸ hxX, hxA⟩, hg ▸ ⟨hXA0 ▸ hyX, hyA⟩⟩, hg⟩

/-- **Assembly for BG Theorem II** (mmd L4548), as a *gated-endpoint skeleton* (`sorry`-free in its
own body).  `A(M)`/`A_0(M)` are tamely embedded — the BG form of the centralizer-control input used
by Peterfalvi (8.12)--(8.13).

The body is the full Theorem II proof, citing the §16 structure theorems A--D and Proposition 16.1
inline (those were `sorry`-stated when this skeleton was written and have since been proved).  What
the skeleton isolates are the two obligations *beyond* that standard A--D suite, as named hypotheses
(cf. `theoremII_conjunct1_of_inputs`):
* `hPieceInv` — the conjunct-1 cross-piece exclusion: `G`-conjugate elements of `X` share `M_σ`-
  and `A(M)`-membership (the "distinct orders across pieces" content of BG Theorem E);
* `hMaxUnique` — the conjunct-3 uniqueness `|ℳ(C_G(x))| = 1` for an escaping centralizer
  (BG §9--§10 Uniqueness), which pins the Type I/II maximal overgroup of `C_G(x)` to Theorem
  D(4)'s `N(x)`.

The wrapper `theoremII_tame_embedding` cites this with both obligations discharged. -/
theorem theoremII_tame_embedding_of_inputs [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M))
    {X : Set G} (hX : X = ASet M U ∨ X = A0Set M K)
    (hPieceInv : ∀ x ∈ X, ∀ y ∈ X, (∃ g : G, y = g * x * g⁻¹) →
      (x ∈ OddOrder.BG.Ch3.S10.Msigma M ↔ y ∈ OddOrder.BG.Ch3.S10.Msigma M) ∧
        (x ∈ ASet M U ↔ y ∈ ASet M U))
    (hMaxUnique : ∀ x : G, x ∈ X → x ≠ 1 →
      ¬ Subgroup.centralizer ({x} : Set G) ≤ M →
        ∀ N₁ N₂ : Subgroup G,
          N₁ ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) →
          N₂ ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) → N₁ = N₂) :
    (∀ x ∈ X, ∀ y ∈ X,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹) ∧
      let D : Set G := {x | x ∈ X ∧ x ≠ 1 ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M}
      -- BG Thm II: `D ⊆ A(M)` (not merely `D ⊆ X`); a genuine claim when `X = A_0(M)`.
      D ⊆ ASet M U ∧
        ∀ x : G, x ∈ D →
          ∃! N : Subgroup G,
            N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
            (OddOrder.GroupTheory.IsTypeI N ∨ OddOrder.GroupTheory.IsTypeII N) := by
  classical
  -- Abbreviate the escaping set `D`.
  set D : Set G := {x | x ∈ X ∧ x ≠ 1 ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M} with hDdef
  -- **Core gated reduction (mmd L4546-L4548).**  `A_0(M)` is the disjoint union of `M_σ`,
  -- `A(M) - M_σ`, and `A_0(M) - A(M)`; the latter two are `TI`-subsets of `G` with normalizer
  -- `M` (Theorem B(5) and Theorem C(9)), so every element of them has its `G`-centralizer inside
  -- `M`.  Hence an `x ∈ X` with `C_G(x) ⊄ M` must lie in `M_σ`, i.e. `D ⊆ M_σ#`.
  --
  -- This step needs the Hall data behind Theorem B(5)/C(9), which the *statement* of Theorem II
  -- does not carry (its `K`, `U` are free, not pinned to the `(κ ∪ σ)'`-Hall / `κ`-Hall factors).
  -- It is therefore isolated as a gated input; once it (and the dual-piece `TI` facts) land with
  -- their Hall hypotheses, `D ⊆ A(M)` (conjunct 2) becomes pure citation, as below.
  have hDsub : D ⊆ S14.sigmaSharp M := by
    intro x hxD
    obtain ⟨hxX, hx1, hxc⟩ := hxD
    -- `x ∈ M_σ#`: it suffices to show `x ∈ M_σ` (we already have `x ≠ 1`).
    simp only [S14.sigmaSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe,
      Set.mem_singleton_iff]
    refine ⟨?_, hx1⟩
    by_contra hxnMσ
    -- `x ∉ M_σ`; the coerced form, and the TI piece for `A(M) - M_σ` (Theorem B(5)).
    have hxnMσ' : x ∉ (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by rwa [SetLike.mem_coe]
    have hTIB : IsTISubset (ASet M U \ (OddOrder.BG.Ch3.S10.Msigma M : Set G)) M :=
      theoremB_A_minus_Msigma_isTISubset hG hM hKM hUM hK hU
    rcases hX with hXA | hXA0
    · -- `X = A(M)`: `x ∈ A(M) - M_σ`, so `C_G(x) ≤ M` (Theorem B(5)) contradicts `C_G(x) ⊄ M`.
      exact hxc (hTIB.centralizer_le ⟨hXA ▸ hxX, hxnMσ'⟩)
    · -- `X = A_0(M)`.
      have hxA0 : x ∈ A0Set M K := hXA0 ▸ hxX
      by_cases hxA : x ∈ ASet M U
      · -- `x ∈ A(M) - M_σ`: Theorem B(5) again.
        exact hxc (hTIB.centralizer_le ⟨hxA, hxnMσ'⟩)
      · -- `x ∈ A_0(M) - A(M)`.
        by_cases hKbot : K = ⊥
        · -- **Type-F** (`K = ⊥`): `A_0(M) = \widehat{M_σ} ⊆ M = U M_σ` (Theorem A(3)),
          -- so `x ∈ A(M)`, contradicting `x ∉ A(M)`.
          refine hxA ⟨hxA0.1, ?_⟩
          have hxM : x ∈ M := hxA0.1.1
          have hA3 : M = K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M :=
            (theoremA_maximal_structure_faithful hG hM hKM hUM hK rfl hU).2.2.1
          have hx' : x ∈ (K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) := hA3 ▸ hxM
          rw [hKbot, bot_sup_eq] at hx'
          exact hx'
        · -- `K ≠ ⊥`: TI by Theorem C(9), giving `C_G(x) ≤ M`.
          obtain ⟨_, _, _, _, _, _, _, _, _, hTIC, _, _⟩ :=
            theoremC_paired_structure hG hM hKbot hKM hUM hK rfl hU
          exact hxc (hTIC.centralizer_le ⟨hxA0, hxA⟩)
  -- **`D ⊆ A(M)` (conjunct 2).**  `D ⊆ M_σ#` and `M_σ# ⊆ A(M)`: a nonidentity `x ∈ M_σ` lies in
  -- `\widehat{M_σ}` (`sigmaSharp_subset_hatMsigma`) and in `M_σ ≤ U M_σ`, so `x ∈ A(M)`.
  have hMσsharp_sub_A : S14.sigmaSharp M ⊆ ASet M U := by
    intro x hx
    refine ⟨sigmaSharp_subset_hatMsigma M hx, ?_⟩
    have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := (Set.mem_sdiff _).mp hx |>.1
    exact (le_sup_right : OddOrder.BG.Ch3.S10.Msigma M ≤
      (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G)) hxMσ
  refine ⟨?_, hDsub.trans hMσsharp_sub_A, ?_⟩
  · -- **Conjunct 1 (Ti) (mmd L4546-L4550).**  Assembled from Theorem D(1) (`M_σ` fusion),
    -- Theorem B(5)/C(9) (the two TI pieces), and the cross-piece exclusion `hPieceInv`, via
    -- `theoremII_conjunct1_of_inputs`.  Only `hPieceInv` remains gated (BG Theorem E).
    have hTI_C : IsTISubset (A0Set M K \ ASet M U) M := by
      by_cases hKbot : K = ⊥
      · -- `K = ⊥` (type F): `A_0(M) = \widehat{M_σ} ⊆ M = U M_σ` (Thm A(3)), so the diff is empty.
        intro g hex
        obtain ⟨z, ⟨hzA0, hznA⟩, _⟩ := hex
        refine absurd ⟨hzA0.1, ?_⟩ hznA
        have hA3 : M = K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M :=
          (theoremA_maximal_structure_faithful hG hM hKM hUM hK rfl hU).2.2.1
        have hz' : z ∈ (K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) := hA3 ▸ hzA0.1.1
        rw [hKbot, bot_sup_eq] at hz'
        exact hz'
      · obtain ⟨_, _, _, _, _, _, _, _, _, hTIC, _, _⟩ :=
          theoremC_paired_structure hG hM hKbot hKM hUM hK rfl hU
        exact hTIC
    refine theoremII_conjunct1_of_inputs
      (theoremD_msigma_conjugacy_and_centralizers hG hM).1
      (theoremB_A_minus_Msigma_isTISubset hG hM hKM hUM hK hU) hTI_C hX ?_
    -- `hPieceInv`: `G`-conjugate elements of `X` share `M_σ`- and `A(M)`-membership — the
    -- "distinct orders across pieces" input of the mmd proof (BG Theorem E), a named obligation.
    exact hPieceInv
  · -- **Conjunct 3 (mmd L4552).**  For `x ∈ D ⊆ M_σ#` with `C_G(x) ⊄ M`, Theorem D(4) gives a
    -- unique maximal `N(x) ⊇ C_G(x)` that is of type `F` or `P₂`; Proposition 16.1(a)(b) rewrites
    -- this as Type I or Type II.  Existence and the type classification are pure citation; the
    -- *uniqueness* of the maximal overgroup is the residual gated input (BG §9-§10 Uniqueness).
    intro x hxD
    obtain ⟨hxX, hx1, hxc⟩ := hxD
    have hxMσsharp : x ∈ S14.sigmaSharp M := hDsub ⟨hxX, hx1, hxc⟩
    -- Theorem D(4): the `∃! N` with the type-`F`/`P₂` data attached to escaping centralizers.
    obtain ⟨_, _, _, hD4⟩ := theoremD_msigma_conjugacy_and_centralizers hG hM
    obtain ⟨_R, _hR, N₀, hQN₀, _hQuniq⟩ := hD4 x hxMσsharp hxc
    -- Unpack what Theorem II needs from the rich Theorem D(4) predicate `Q N₀`.
    obtain ⟨hN₀mem, _, _, _, hN₀type, _⟩ := hQN₀
    -- Convert `IsTypeF N₀ ∨ IsTypeP2 N₀` to `IsTypeI N₀ ∨ IsTypeII N₀` (Proposition 16.1(a)(b)).
    have hN₀ : N₀ ∈ maximalSubgroups G := (mem_maximalSubgroupsContaining.mp hN₀mem).1
    have htype : OddOrder.GroupTheory.IsTypeI N₀ ∨ OddOrder.GroupTheory.IsTypeII N₀ := by
      obtain ⟨hIiff, hIIiff, _⟩ := proposition_type_classification hG hN₀
      rcases hN₀type with hF | hP2
      · exact Or.inl (hIiff.mpr hF)
      · exact Or.inr (hIIiff.mpr hP2)
    refine ⟨N₀, ⟨hN₀mem, htype⟩, ?_⟩
    -- Uniqueness of the maximal overgroup of `C_G(x)`: the named obligation `hMaxUnique`.  Theorem
    -- D(4) gives uniqueness only for its *full* predicate `Q`; pinning the weaker "maximal
    -- overgroup, Type I/II" to the same `N₀` is exactly `|ℳ(C_G(x))| = 1` (BG §9--§10 Uniqueness).
    rintro N' ⟨hN'mem, _hN'type⟩
    exact hMaxUnique x hxX hx1 hxc N' N₀ hN'mem hN₀mem

/-- **The escaping piece of `A(M)`/`A_0(M)` lands in `M_σ#`** (the `D ⊆ M_σ#` reduction of Theorem
II's conjunct 2, extracted for reuse).  An `x ∈ X` (`X = A(M)` or `A_0(M)`) with `x ≠ 1` and
`C_G(x) ⊄ M` must lie in `M_σ`: the dual TI pieces `A(M) - M_σ` (Theorem B(5)) and `A_0(M) - A(M)`
(Theorem C(9), or empty in the type-`F` case via Theorem A(3)) have `G`-centralizer inside `M`. -/
theorem mem_sigmaSharp_of_mem_aSet_of_escape [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {X : Set G} (hX : X = ASet M U ∨ X = A0Set M K)
    {x : G} (hxX : x ∈ X) (hx1 : x ≠ 1)
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    x ∈ S14.sigmaSharp M := by
  simp only [S14.sigmaSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  refine ⟨?_, hx1⟩
  by_contra hxnMσ
  have hxnMσ' : x ∉ (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by rwa [SetLike.mem_coe]
  have hTIB : IsTISubset (ASet M U \ (OddOrder.BG.Ch3.S10.Msigma M : Set G)) M :=
    theoremB_A_minus_Msigma_isTISubset hG hM hKM hUM hK hU
  rcases hX with hXA | hXA0
  · exact hesc (hTIB.centralizer_le ⟨hXA ▸ hxX, hxnMσ'⟩)
  · have hxA0 : x ∈ A0Set M K := hXA0 ▸ hxX
    by_cases hxA : x ∈ ASet M U
    · exact hesc (hTIB.centralizer_le ⟨hxA, hxnMσ'⟩)
    · by_cases hKbot : K = ⊥
      · refine hxA ⟨hxA0.1, ?_⟩
        have hxM : x ∈ M := hxA0.1.1
        have hA3 : M = K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M :=
          (theoremA_maximal_structure_faithful hG hM hKM hUM hK rfl hU).2.2.1
        have hx' : x ∈ (K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) := hA3 ▸ hxM
        rw [hKbot, bot_sup_eq] at hx'
        exact hx'
      · obtain ⟨_, _, _, _, _, _, _, _, _, hTIC, _, _⟩ :=
          theoremC_paired_structure hG hM hKbot hKM hUM hK rfl hU
        exact hesc (hTIC.centralizer_le ⟨hxA0, hxA⟩)

/-- **`ℳ(C_G(x))` is a singleton for an escaping `σ`-sharp element** (`|ℳ(C_G(x))| = 1`, the BG
§9--§10 uniqueness input of Theorem II's conjunct 3).  For `x ∈ M_σ#` with `C_G(x) ⊄ M`, the escape
forces `|𝓜_σ(x)| > 1` (`centralizer_le_of_maximalSigma_le_one`), so the signalizer structure
(`signalizer_structure_of_mem_sigmaSharp`) supplies the type-`F`/`P₂` neighbour `N` over `C_G(x)`
whose `τ₂`-element data feeds the Corollary-14.3 uniqueness
`maximalContaining_centralizer_eq_singleton_of_tau2_element`, pinning `ℳ(C_G(x)) = {N}`. -/
theorem maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hx : x ∈ S14.sigmaSharp M) (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    ∃ N : Subgroup G,
      maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {N} := by
  have hx1 : x ≠ 1 := hx.2
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hx.1
  have hgt : 1 < (S14.maximalSigmaSubgroupsOfElement x).ncard := by
    by_contra h
    push Not at h
    exact hesc (centralizer_le_of_maximalSigma_le_one hG hM hxMσ hx1 h)
  obtain ⟨N, hNstruct, -⟩ := signalizer_structure_of_mem_sigmaSharp hG hM hx hgt
  obtain ⟨hNmax, hCN, hRne, _hRhall, hxtau2, _hNtype, _hforall⟩ := hNstruct
  have hxN : x ∈ N := hCN (Subgroup.mem_centralizer_iff.mpr
    (fun y hy => by rw [Set.mem_singleton_iff.mp hy]))
  exact ⟨N, maximalContaining_centralizer_eq_singleton_of_tau2_element hG hNmax hxN hx1 hxtau2 hRne⟩

/-- **The signalizer maximal is the unique type-`I`/`II` overgroup of `C_G(x)`** (full per-element
half of Peterfalvi (8.13)): for an escaping `σ`-sharp element `x` (`x ∈ M_σ#`, `C_G(x) ⊄ M`) there
is
a *unique* maximal subgroup `L` over `C_G(x)` of Peterfalvi type `I`/`II`.  Existence is the
previous `exists_maximal_centralizer_le_typeI_or_typeII` (the type-`F`/`P₂` neighbour of
`signalizer_structure_of_mem_sigmaSharp`, converted to type `I`/`II`); uniqueness is the Theorem-D
singleton `ℳ(C_G(x)) = {N[x]}`
(`maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape`), which collapses
*every*
maximal over `C_G(x)` — not merely the type-`I`/`II` ones — to `N[x]`.  This is exactly the `∃!`
clause of (8.13)'s conclusion; the escape hypothesis `C_G(x) ⊄ M` supplies the `1 < |𝓜_σ(x)|` the
existence half needs (`centralizer_le_of_maximalSigma_le_one`). -/
theorem existsUnique_maximal_centralizer_le_typeI_or_typeII [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hxM : x ∈ S14.sigmaSharp M)
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    ∃! L : Subgroup G, L ∈ maximalSubgroups G ∧
      Subgroup.centralizer ({x} : Set G) ≤ L ∧
      (OddOrder.GroupTheory.IsTypeI L ∨ OddOrder.GroupTheory.IsTypeII L) := by
  -- Theorem-D singleton `ℳ(C_G(x)) = {N}` collapses every maximal over `C_G(x)`.
  obtain ⟨N, hMC⟩ := maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
    hG hM hxM hesc
  have key : ∀ L : Subgroup G, L ∈ maximalSubgroups G →
      Subgroup.centralizer ({x} : Set G) ≤ L → L = N := fun L hLmax hLC => by
    have hmem : L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨hLmax, hLC⟩
    rw [hMC, Set.mem_singleton_iff] at hmem; exact hmem
  -- `1 < |𝓜_σ(x)|` from escape, feeding the existence half.
  have hx1 : x ≠ 1 := hxM.2
  have hgt : 1 < (S14.maximalSigmaSubgroupsOfElement x).ncard := by
    by_contra h
    push Not at h
    exact hesc (centralizer_le_of_maximalSigma_le_one hG hM hxM.1 hx1 h)
  obtain ⟨L₀, hL₀max, hL₀C, hL₀type⟩ :=
    exists_maximal_centralizer_le_typeI_or_typeII hG hM hxM hgt
  have hL₀eq : L₀ = N := key L₀ hL₀max hL₀C
  exact ⟨N, ⟨hL₀eq ▸ hL₀max, hL₀eq ▸ hL₀C, hL₀eq ▸ hL₀type⟩, fun L hL => key L hL.1 hL.2.1⟩

/-- **BG Theorem II** (mmd L4548): `A(M)` and `A_0(M)` are tamely embedded.  The BG form of the
centralizer-control input used by Peterfalvi (8.12)--(8.13).  Cites the gated-endpoint skeleton
`theoremII_tame_embedding_of_inputs`; **both residual obligations are now discharged** — the BG
Theorem E cross-piece exclusion `hPieceInv` via the order-determined `M_σ`/`A(M)`-membership
(`mem_Msigma_iff_isPiElement_sigma` / `mem_U_sup_Msigma_iff_isPiElement_kappa_compl`), and the BG
§9--§10 maximal-overgroup uniqueness `hMaxUnique` via the signalizer uniqueness
(`maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape`).  The `_of_inputs`
skeleton cites the §16 structure theorems A--D inline; those are proved. -/
theorem theoremII_tame_embedding [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M))
    {X : Set G} (hX : X = ASet M U ∨ X = A0Set M K) :
    (∀ x ∈ X, ∀ y ∈ X,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹) ∧
      let D : Set G := {x | x ∈ X ∧ x ≠ 1 ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M}
      -- BG Thm II: `D ⊆ A(M)` (not merely `D ⊆ X`); a genuine claim when `X = A_0(M)`.
      D ⊆ ASet M U ∧
        ∀ x : G, x ∈ D →
          ∃! N : Subgroup G,
            N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
            (OddOrder.GroupTheory.IsTypeI N ∨ OddOrder.GroupTheory.IsTypeII N) :=
  theoremII_tame_embedding_of_inputs hG hM hKM hUM hK hU hX
    -- `hPieceInv`: BG Theorem E cross-piece exclusion.  `M_σ` (normal `σ`-Hall) and `U⊔M_σ` (normal
    -- `κ′`-Hall, Theorem A(3)) make `M_σ`- and `A(M)`-membership of an element of `M`
    -- order-determined
    -- (`mem_Msigma_iff_isPiElement_sigma` / `mem_U_sup_Msigma_iff_isPiElement_kappa_compl`), hence
    -- conjugation-invariant (`isPiElement_conj`).
    (by
      have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
      have hnorm : ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hUM hMσM)).mpr
          (theoremA_ungated_conjuncts hG hM hKM hUM hK rfl hU).2.2.1
      intro x hxX y hyX hconj
      obtain ⟨g, hg⟩ := hconj
      have hxhat : x ∈ hatMsigma M := by
        rcases hX with h | h
        · have hm := h ▸ hxX; simp only [ASet, Set.mem_inter_iff] at hm; exact hm.1
        · have hm := h ▸ hxX; simp only [A0Set, Set.mem_sdiff] at hm; exact hm.1
      have hyhat : y ∈ hatMsigma M := by
        rcases hX with h | h
        · have hm := h ▸ hyX; simp only [ASet, Set.mem_inter_iff] at hm; exact hm.1
        · have hm := h ▸ hyX; simp only [A0Set, Set.mem_sdiff] at hm; exact hm.1
      refine ⟨?_, ?_⟩
      · rw [S14.mem_Msigma_iff_isPiElement_sigma hG hM hxhat.1,
          S14.mem_Msigma_iff_isPiElement_sigma hG hM hyhat.1]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [hg]; exact S14.isPiElement_conj g h
        · rw [show x = g⁻¹ * y * (g⁻¹)⁻¹ from by rw [hg]; group]
          exact S14.isPiElement_conj g⁻¹ h
      · have hAx : x ∈ ASet M U ↔ x ∈ U ⊔ OddOrder.BG.Ch3.S10.Msigma M := by
          simp only [ASet, Set.mem_inter_iff, SetLike.mem_coe]
          exact ⟨fun h => h.2, fun h => ⟨hxhat, h⟩⟩
        have hAy : y ∈ ASet M U ↔ y ∈ U ⊔ OddOrder.BG.Ch3.S10.Msigma M := by
          simp only [ASet, Set.mem_inter_iff, SetLike.mem_coe]
          exact ⟨fun h => h.2, fun h => ⟨hyhat, h⟩⟩
        rw [hAx, hAy,
          S14.mem_U_sup_Msigma_iff_isPiElement_kappa_compl hG hM hUM hU hnorm hxhat.1,
          S14.mem_U_sup_Msigma_iff_isPiElement_kappa_compl hG hM hUM hU hnorm hyhat.1]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [hg]; exact S14.isPiElement_conj g h
        · rw [show x = g⁻¹ * y * (g⁻¹)⁻¹ from by rw [hg]; group]
          exact S14.isPiElement_conj g⁻¹ h)
    -- `hMaxUnique`: BG §9--§10 maximal-overgroup uniqueness `|ℳ(C_G(x))| = 1`, discharged from the
    -- signalizer uniqueness
    -- (`maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape`)
    -- via the `D ⊆ M_σ#` reduction (`mem_sigmaSharp_of_mem_aSet_of_escape`).
    (fun x hxX hx1 hesc N₁ N₂ hN₁ hN₂ => by
      obtain ⟨N, hMC⟩ := maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
        hG hM (mem_sigmaSharp_of_mem_aSet_of_escape hG hM hKM hUM hK hU hX hxX hx1 hesc) hesc
      rw [hMC, Set.mem_singleton_iff] at hN₁ hN₂
      exact hN₁.trans hN₂.symm)

/-! **BG Lemma 14.13(a)** (`non_disjoint_signalizer_frobenius`) lives in the sibling leaf
`S16_Lemma1413.lean` (file-granularity: this file is already large).  Its proof assembles the
signalizer structure below with the type-`P` dual-pair machinery (`typeP_structure`,
`typeP_duality`) and Corollaries 12.9/12.14.  See that leaf for the faithful
(prime-restricted `τ₂`) statement and proof. -/

end OddOrder.BG.Ch4.S16

