import OddOrder.Peterfalvi.S14_MaximalI.FrobeniusStructure
import OddOrder.Peterfalvi.S14_MaximalI.CentralizerContainment
import OddOrder.Peterfalvi.S13_NonGaloisExclusion

/-!
# WitnessSylowCyclic

Prefix-split from `OddOrder.Peterfalvi.S14_MaximalI.MinimalCounterexample` (2000-line limit, issue
0103 第 2 パス).
-/

/-!
# Peterfalvi (12.8)-(12.12) — minimal counterexample analysis

Split from the former monolithic `OddOrder.Peterfalvi.S14_MaximalI` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S14
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ## (12.8)--(12.12): minimal counterexample analysis -/

/-- **Peterfalvi (12.8), the prime set `π`**: `q ∈ π` when some type-`I` maximal subgroup `M'`
has a **noncyclic Sylow `q`-subgroup in `M' / M'_F`**.  Encoded by a Sylow `q`-subgroup `P ≤ M'`
(`q`-group with `q ∤ [M' : P]`) that is noncyclic and satisfies `q ∣ [M' : M'_F]` — so `P` is not
contained in `M'_F` and its image in `M'/M'_F` is a noncyclic Sylow `q`-subgroup. -/
def InPi (q : ℕ) : Prop :=
  ∃ M' : Subgroup G, M' ∈ maximalSubgroups G ∧ IsTypeI M' ∧
    ∃ P : Subgroup G, P ≤ M' ∧ IsPGroup q ↥P ∧ ¬ q ∣ P.relIndex M' ∧
      ¬ IsCyclic ↥P ∧ q ∣ (maxNilpotentNormalHall M').relIndex M'

/-- **Peterfalvi (12.7), the `π = ∅` case** (the first sentence of the proof of (12.16)): if the
prime set `π` of (12.8) is empty, every type-I maximal `M` is a Frobenius group with kernel `M_F`.

`M_F = H` is a normal Hall subgroup (8.11), so its complement `U` has `|U| = [M : M_F]` coprime
to `|M_F|`; hence every Sylow `q`-subgroup `P` of `U` has full `q`-order in `M`.  Were `P`
noncyclic, its `M`-image `P.map U.subtype` would be a noncyclic Sylow `q`-subgroup of `M` with
`q ∣ [M : M_F]`, i.e. `q ∈ π` — contradicting `π = ∅`.  So `U` is a Z-group and the bridge
`typeI_frobenius_of_isZGroup_complement` applies.  Its only gap is the (8.11) Hall input. -/
theorem typeI_frobenius_of_pi_empty [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hpi : ∀ q : ℕ, q.Prime → ¬ InPi (G := G) q)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypeIData M) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.typeF.H.subgroupOf M)
      (data.typeF.U.subgroupOf M) := by
  classical
  refine typeI_frobenius_of_isZGroup_complement data ?_
  set H := data.typeF.H with hHdef
  set U := data.typeF.U with hUdef
  have hUM : U ≤ M := data.typeF.U_le
  -- `[M : H] = |U|` (complement) and `|M| = |H| * |U|`.
  have hrel : H.relIndex M = Nat.card ↥U := by
    rw [Subgroup.relIndex, data.typeF.complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
  have hMcard : Nat.card ↥M = Nat.card ↥H * Nat.card ↥U := by
    rw [← (H.subgroupOf M).card_mul_index,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeF.H_le).toEquiv,
      ← Subgroup.relIndex, hrel]
  -- `H = M_F` is Hall in `G` (8.11), so `|H|` is coprime to `[M : H] = |U|`.
  have hHall := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG hM
    (tau := PeterfalviType.I) ⟨data⟩).1
  rw [← data.typeF.H_eq] at hHall
  have hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥U) :=
    hHall.coprime_index.coprime_dvd_right
      (hrel ▸ Subgroup.relIndex_dvd_index_of_le data.typeF.H_le)
  -- Every Sylow `q`-subgroup `P` of `U` is cyclic.
  refine ⟨fun q hq P => ?_⟩
  haveI : Fact q.Prime := ⟨hq⟩
  by_contra hnc
  -- `P ≠ ⊥`, so `q ∣ |U|`, and `|H|` has no `q`.
  have hPcard : Nat.card ↥(P : Subgroup ↥U) = q ^ (Nat.card ↥U).factorization q :=
    P.card_eq_multiplicity
  have hPne : (P : Subgroup ↥U) ≠ ⊥ := fun h => hnc (h ▸ inferInstance)
  have hfacU_pos : 0 < (Nat.card ↥U).factorization q := by
    rcases Nat.eq_zero_or_pos ((Nat.card ↥U).factorization q) with h0 | h
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hPcard, h0, pow_zero])) hPne
    · exact h
  have hqU : q ∣ Nat.card ↥U := Nat.dvd_of_factorization_pos hfacU_pos.ne'
  have hHfac0 : (Nat.card ↥H).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      (hq.coprime_iff_not_dvd.mp (hcop.coprime_dvd_right hqU).symm)
  have hMfac : (Nat.card ↥M).factorization q = (Nat.card ↥U).factorization q := by
    rw [hMcard, Nat.factorization_mul (Nat.card_pos (α := ↥H)).ne'
      (Nat.card_pos (α := ↥U)).ne', Finsupp.add_apply, hHfac0, zero_add]
  -- `Pm = P.map U.subtype`: a noncyclic `q`-subgroup of `M` of full `q`-order.
  set Pm := (P : Subgroup ↥U).map U.subtype with hPmdef
  have hPmM : Pm ≤ M := (Subgroup.map_subtype_le _).trans hUM
  have hPmcard : Nat.card ↥Pm = q ^ (Nat.card ↥M).factorization q := by
    rw [hPmdef, Subgroup.card_map_of_injective U.subtype_injective, hPcard, hMfac]
  have hPmsub : Nat.card ↥(Pm.subgroupOf M) = q ^ (Nat.card ↥M).factorization q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPmM).toEquiv, hPmcard]
  have hPmP : IsPGroup q ↥Pm := (IsPGroup.iff_card).mpr ⟨_, hPmcard⟩
  refine hpi q hq ⟨M, hM, ⟨data⟩, Pm, hPmM, hPmP, ?_, ?_, ?_⟩
  · -- `¬ q ∣ Pm.relIndex M`: `Pm` has the full `q`-part of `|M|`.
    rw [Subgroup.relIndex]
    intro hdvd
    have hsplit : (Nat.card ↥M).factorization q
        = (Nat.card ↥(Pm.subgroupOf M)).factorization q
          + ((Pm.subgroupOf M).index).factorization q := by
      conv_lhs => rw [← (Pm.subgroupOf M).card_mul_index]
      rw [Nat.factorization_mul (Nat.card_pos (α := ↥(Pm.subgroupOf M))).ne'
        Subgroup.index_ne_zero_of_finite, Finsupp.add_apply]
    rw [hPmsub, hq.factorization_pow, Finsupp.single_eq_same] at hsplit
    exact absurd (Nat.Prime.factorization_pos_of_dvd hq Subgroup.index_ne_zero_of_finite hdvd)
      (by omega)
  · -- `¬ IsCyclic ↥Pm`: `Pm ≃* P` and `P` is noncyclic.
    intro hc
    haveI := hc
    exact hnc (isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (P : Subgroup ↥U) U.subtype U.subtype_injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective (P : Subgroup ↥U) U.subtype U.subtype_injective).symm.surjective)
  · -- `q ∣ (maxNilpotentNormalHall M).relIndex M = [M : H] = |U|`.
    rw [← data.typeF.H_eq, hrel]; exact hqU

/-- **Peterfalvi (12.8)**: the minimal counterexample hypothesis for (12.7).

`M` is a type-`I` maximal subgroup whose Fitting kernel is `K = M_F` (`K' = [K, K]`), and `P₀`
is a Sylow `p`-subgroup of `M` that is noncyclic with `p ∣ [M : M_F]` (so the image of `P₀` in
`M/M_F` is a noncyclic Sylow `p`-subgroup, i.e. `p ∈ π`); `p` is the smallest element of `π`. -/
structure CounterexampleHypothesis where
  p : ℕ
  p_prime : p.Prime
  M : Subgroup G
  K : Subgroup G
  Kprime : Subgroup G
  P0 : Subgroup G
  M_maximal : M ∈ maximalSubgroups G
  M_typeI : IsTypeI M
  K_eq_MF : K = maxNilpotentNormalHall M
  Kprime_eq : Kprime = derivedInG K
  P0_le_M : P0 ≤ M
  /-- `P₀` is a `p`-group… -/
  P0_pGroup : IsPGroup p ↥P0
  /-- …and a Sylow `p`-subgroup of `M` (`p ∤ [M : P₀]`). -/
  P0_sylow : ¬ p ∣ P0.relIndex M
  /-- The Sylow `p`-subgroup of `M/M_F` is noncyclic (so `P₀` is noncyclic). -/
  P0_noncyclic : ¬ IsCyclic ↥P0
  /-- …and `p ∣ [M : M_F]` (so `P₀ ⊄ M_F`; together with the Hall property this gives `p ∤ |M_F|`). -/
  p_dvd_index : p ∣ K.relIndex M
  /-- `p` is the smallest prime in `π`. -/
  minimal_p : ∀ q : ℕ, q.Prime → InPi (G := G) q → p ≤ q

/-- **Peterfalvi (12.8), existence of the minimal counterexample.**  If the prime set `π` of
(12.8) is nonempty, its least element `p = Nat.find` yields a `CounterexampleHypothesis`: the
`InPi` witness for `p` supplies a type-`I` maximal `M'` with a noncyclic Sylow `p`-subgroup `P₀`
that has `p ∣ [M' : M'_F]`, and `Nat.find_min'` records that `p` is the smallest prime in `π`.

This is the well-ordering step that opens the minimal-counterexample analysis of (12.7); it is
`§8`-free and unconditional (its only input is `InPi` for some prime). -/
theorem exists_counterexampleHypothesis [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (h : ∃ q : ℕ, q.Prime ∧ InPi (G := G) q) :
    Nonempty (CounterexampleHypothesis (G := G)) := by
  classical
  obtain ⟨hp_prime, M', hM', hM'I, P, hPle, hPpg, hPsyl, hPnc, hqdvd⟩ := Nat.find_spec h
  exact ⟨{
    p := Nat.find h
    p_prime := hp_prime
    M := M'
    K := maxNilpotentNormalHall M'
    Kprime := derivedInG (maxNilpotentNormalHall M')
    P0 := P
    M_maximal := hM'
    M_typeI := hM'I
    K_eq_MF := rfl
    Kprime_eq := rfl
    P0_le_M := hPle
    P0_pGroup := hPpg
    P0_sylow := hPsyl
    P0_noncyclic := hPnc
    p_dvd_index := hqdvd
    minimal_p := fun q hq hqInPi => Nat.find_min' h ⟨hq, hqInPi⟩ }⟩

/-- The rank-two witness extracted in Peterfalvi (12.9), with all fields stated faithfully.

`L` is the second maximal subgroup with `P₀ ⊆ L_s` (`L_s = mainSubgroup L L_type`); `x` is the
order-`p` element of `Ω₁(P₀)^#` whose centralizer in `K = M_F` escapes `K'`, controls `N_G(⟨x⟩)`,
and escapes `L`. -/
structure RankTwoWitnessData (ctr : CounterexampleHypothesis (G := G)) where
  L : Subgroup G
  L_maximal : L ∈ maximalSubgroups G
  /-- Peterfalvi's type attached to `L` (so `L_s = mainSubgroup L L_type`). -/
  L_type : PeterfalviType
  L_hasType : HasPeterfalviType L_type L
  /-- `P₀ ⊆ L_s`. -/
  P0_le_Ls : ctr.P0 ≤ mainSubgroup L L_type
  x : G
  x_mem_P0 : x ∈ ctr.P0
  x_ne_one : x ≠ 1
  /-- `x ∈ Ω₁(P₀)^#`: `x` has order dividing `p`. -/
  x_mem_omega1 : x ^ ctr.p = 1
  /-- `C_K(x) ⊄ K'` (equivalently `C_{K/K'}(x) ≠ 1`). -/
  CKx_not_le_Kprime : ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime)
  /-- `N_G(⟨x⟩) ⊆ M`. -/
  normalizer_closure_x_le_M :
    Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≤ ctr.M
  /-- `C_G(x) ⊄ L`. -/
  centralizer_x_not_le_L : ¬ (Subgroup.centralizer ({x} : Set G) ≤ L)

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Group-theoretic core of Peterfalvi (12.9)** (fully general, `§8`-independent).

If a **noncyclic abelian** group `A` acts **coprimely** on a finite group `K` whose
abelianization is nontrivial (`[K, K] ≠ K`), then some **nontrivial** `a ∈ A` has a fixed
subgroup `C_K(a)` that is *not* contained in the derived subgroup `[K, K]`.

This is the abstract content of the centralizer step of (12.9): there Peterfalvi takes
`A = Ω₁(P₀)` (elementary abelian of rank `2`, hence noncyclic) acting by conjugation on
`K = M_F`, with `[K, K] = K'`, and concludes `∃ x ∈ Ω₁(P₀)^#` with `C_K(x) ⊄ K'`
(equivalently `C_{K/K'}(x) ≠ 1`).

Proof.  `[K, K]` is characteristic, hence `A`-invariant, so `A` acts on the quotient
`K / [K, K]`.  By **BG Proposition 1.16(1)** (Isaacs 6.21,
`nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'`) applied to that quotient action,
`K / [K, K] = ⟨ C_{K/[K,K]}(a) ∣ a ≠ 1 ⟩`.  Since `K / [K, K]` is nontrivial, some
`a ≠ 1` has `C_{K/[K,K]}(a) ≠ 1`; the witnessing coset lifts, by the coprime fixed-point
lifting (**Isaacs Cor 3.28**, `coprime_fixedPoints_quotient`), to an element of `C_K(a)`
outside `[K, K]`. -/
theorem exists_ne_one_actionFixedBy_not_le_commutator
    {A K : Type*} [Group A] [Finite A] [IsMulCommutative A] [Group K] [Finite K]
    (φ : A →* MulAut K) (hCop : Nat.Coprime (Nat.card A) (Nat.card K))
    (hSolv : IsSolvable A ∨ IsSolvable K) (hNC : ¬ IsCyclic A)
    (hK' : commutator K ≠ ⊤) :
    ∃ a : A, a ≠ 1 ∧ ¬ (Ch06.actionFixedBy φ a ≤ commutator K) := by
  classical
  -- `[K, K]` is characteristic, hence `A`-invariant; let `ψ` be the induced quotient action.
  have hN_inv : Ch03.IsAInvariant φ (commutator K) := Ch03.IsAInvariant.of_characteristic φ
  set ψ := quotientMulAutHom hN_inv with hψ
  -- Coprimality on the quotient: `|K / [K,K]|` divides `|K|`.
  have hCopQ : Nat.Coprime (Nat.card A) (Nat.card (K ⧸ commutator K)) :=
    hCop.coprime_dvd_right (commutator K).card_quotient_dvd_card
  -- BG 1.16(1) on the quotient action: the nontrivial fixed-point closure is everything.
  have htop : Ch06.nontrivialActionFixedByClosure ψ = ⊤ :=
    OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic' ψ hCopQ hNC
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ a, a ≠ 1 → C_K(a) ≤ [K, K]`.  Show the quotient closure is `⊥`.
  have hquot_bot : Ch06.nontrivialActionFixedByClosure ψ ≤ ⊥ := by
    rw [Ch06.nontrivialActionFixedByClosure_le_iff]
    intro a ha q hq
    -- `q ∈ C_{K/K'}(a)`: `q` is fixed by every element of `⟨a⟩`.
    have hq_zp : q ∈ Ch06.actionFixedPoints ψ (Subgroup.zpowers a) := by
      rw [← Ch06.actionFixedBy_eq_actionFixedPoints_zpowers]; exact hq
    -- Lift `q = mk' g` and assemble the coset-fixed hypothesis on `⟨a⟩`.
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator K) q
    have hg_fix : ∀ b : ↥(Subgroup.zpowers a), ∃ n ∈ commutator K, φ (b : A) g = g * n := by
      intro b
      have hb := (Ch06.mem_actionFixedPoints.mp hq_zp) b
      rw [hψ, quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq] at hb
      exact ⟨g⁻¹ * φ (b : A) g, by simpa using (commutator K).inv_mem hb, by group⟩
    -- Coprime fixed-point lifting (Isaacs Cor 3.28) on the cyclic group `⟨a⟩`.
    have hCop' : Nat.Coprime (Nat.card ↥(Subgroup.zpowers a)) (Nat.card K) :=
      hCop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
    have hSolv' : IsSolvable ↥(Subgroup.zpowers a) ∨ IsSolvable K := by
      rcases hSolv with hA | hK
      · haveI := hA; exact Or.inl inferInstance
      · exact Or.inr hK
    obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
      Ch04.coprime_fixedPoints_quotient hCop' hSolv'
        (Ch03.IsAInvariant.of_characteristic (φ.comp (Subgroup.zpowers a).subtype)) hg_fix
    -- `c` is fixed by `a`, hence `c ∈ C_K(a) ≤ [K, K]` by `hcon`.
    have hca : φ a c = c := hc_fix ⟨a, Subgroup.mem_zpowers a⟩
    have hc_mem : c ∈ commutator K := hcon a ha (Ch06.mem_actionFixedBy.mpr hca)
    -- Then `g = c * n⁻¹ ∈ [K, K]`, so the coset `q = mk' g` is trivial.
    have hg_mem : g ∈ commutator K := by
      have : g = c * n⁻¹ := by rw [hcn]; group
      rw [this]; exact (commutator K).mul_mem hc_mem ((commutator K).inv_mem hn)
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hg_mem
  -- `⊤ ≤ ⊥` forces `K / [K, K]` trivial, i.e. `[K, K] = ⊤`, contradicting `hK'`.
  have hbot : (⊤ : Subgroup (K ⧸ commutator K)) = ⊥ := le_bot_iff.mp (htop ▸ hquot_bot)
  apply hK'
  rw [Subgroup.eq_top_iff']
  intro k
  have hk1 : QuotientGroup.mk' (commutator K) k ∈ (⊥ : Subgroup (K ⧸ commutator K)) := by
    rw [← hbot]; exact Subgroup.mem_top _
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk1
  exact hk1

/-- **Conjugation form of the (12.9) centralizer core** (ambient subgroups, directly the
form consumed by (12.9)).  If a **noncyclic abelian** subgroup `A ≤ G` normalizes a finite
subgroup `K` of **coprime** order whose abelianization is nontrivial (`⁅K, K⁆ ≠ K`), then
some `x ∈ A`, `x ≠ 1`, has `C_K(x) = C_G(x) ⊓ K` **not** contained in `⁅K, K⁆`.

Specialization of `exists_ne_one_actionFixedBy_not_le_commutator` to the conjugation action
`A → MulAut K` (`Subgroup.normalizerMonoidHom`): the abstract fixed subgroup `C_K(a)` becomes
`C_G(a) ⊓ K` and `commutator ↥K` maps to `⁅K, K⁆` under `K.subtype`. -/
theorem exists_mem_centralizer_inf_not_le_commutator
    {A K : Subgroup G} [Finite ↥A] [IsMulCommutative ↥A] [Finite ↥K]
    (hAK : A ≤ Subgroup.normalizer K) (hCop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥K))
    (hSolv : IsSolvable ↥A ∨ IsSolvable ↥K) (hNC : ¬ IsCyclic ↥A) (hK' : ⁅K, K⁆ ≠ K) :
    ∃ x : G, x ∈ A ∧ x ≠ 1 ∧ ¬ (Subgroup.centralizer {x} ⊓ K ≤ ⁅K, K⁆) := by
  classical
  -- The conjugation action `φ : A → MulAut K` and the `K.subtype`-image of `[↥K, ↥K]`.
  set φ : ↥A →* MulAut ↥K := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hAK)
    with hφ
  have htop_map : (⊤ : Subgroup ↥K).map K.subtype = K := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hg; exact ⟨⟨g, hg⟩, rfl⟩
  have hmap : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, htop_map]
  -- `[↥K, ↥K] ≠ ⊤`: else its `K.subtype`-image would be `⁅K, K⁆ = K`.
  have hKtop : commutator ↥K ≠ ⊤ := by
    intro h; exact hK' (by rw [← hmap, h, htop_map])
  obtain ⟨a, ha_ne, hnle⟩ :=
    exists_ne_one_actionFixedBy_not_le_commutator φ hCop hSolv hNC hKtop
  -- Translate the abstract conclusion to ambient subgroups.
  obtain ⟨n, hn_fix, hn_out⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨(a : G), a.2, fun h => ha_ne (Subtype.ext h), SetLike.not_le_iff_exists.mpr
    ⟨(n : G), ?_, ?_⟩⟩
  · -- `n ∈ C_G(a) ⊓ K`: `a` conjugates `n` to itself, and `n ∈ K`.
    rw [Ch06.mem_actionFixedBy] at hn_fix
    have hval : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) :=
      congrArg (Subtype.val) hn_fix
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, n.2⟩
    rintro y rfl
    exact mul_inv_eq_iff_eq_mul.mp hval
  · -- `n ∉ ⁅K, K⁆`: else `n ∈ [↥K, ↥K]`, contradicting `hn_out`.
    rw [← hmap]
    intro hmem
    obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp hmem
    exact hn_out (by rw [show n = m from Subtype.ext hmn.symm]; exact hm)

/-- **Peterfalvi (12.9), the order-`p` centralizer witness** (the genuine, `§8`-free heart of
(12.9)).  Given the counterexample data with `P₀` abelian, coprime to `K = M_F`, normalizing `K`,
and `K` not perfect, there is an element `x ∈ Ω₁(P₀)^#` (order dividing `p`) with `C_K(x) ⊄ K'`.

Proof: apply the centralizer core `exists_mem_centralizer_inf_not_le_commutator` to the abelian
noncyclic `P₀` acting by conjugation on `K`, yielding `y ∈ P₀^#` with `C_K(y) ⊄ K'`; then pass to
the order-`p` power `x = y ^ (|y| / p)` — its centralizer contains `C_K(y)`, so still escapes `K'`. -/
theorem exists_orderP_centralizer_witness [Finite G]
    (ctr : CounterexampleHypothesis (G := G))
    (habelian : IsMulCommutative ↥ctr.P0)
    (hcoprime : Nat.Coprime (Nat.card ↥ctr.P0) (Nat.card ↥ctr.K))
    (hP0_norm : ctr.P0 ≤ Subgroup.normalizer ctr.K)
    (hKperfect : ⁅ctr.K, ctr.K⁆ ≠ ctr.K) :
    ∃ x : G, x ∈ ctr.P0 ∧ x ≠ 1 ∧ x ^ ctr.p = 1 ∧
      ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime) := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  haveI := habelian
  haveI : Group.IsNilpotent ↥ctr.P0 := ctr.P0_pGroup.isNilpotent
  -- `K' = ⁅K, K⁆`.
  have hKprime : ctr.Kprime = ⁅ctr.K, ctr.K⁆ :=
    ctr.Kprime_eq.trans (Subgroup.map_subtype_commutator ctr.K)
  -- Centralizer core (A = P₀, abelian noncyclic, coprime, normalizing K, K not perfect).
  obtain ⟨y, hyP0, hy_ne, hy_cent⟩ :=
    exists_mem_centralizer_inf_not_le_commutator (A := ctr.P0) (K := ctr.K)
      hP0_norm hcoprime (Or.inl inferInstance) ctr.P0_noncyclic hKperfect
  -- `y` has `p`-power order `p ^ k` with `k ≥ 1`.
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp ctr.P0_pGroup) ⟨y, hyP0⟩
  have hoy : orderOf y = ctr.p ^ k :=
    (orderOf_injective ctr.P0.subtype ctr.P0.subtype_injective ⟨y, hyP0⟩).trans hk
  have hk_pos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0, pow_zero, orderOf_eq_one_iff] at hoy; exact absurd hoy hy_ne
    · exact h
  have hp_dvd : ctr.p ∣ orderOf y := hoy ▸ dvd_pow_self ctr.p (by omega)
  have hord_pos : 0 < orderOf y := hoy ▸ pow_pos ctr.p_prime.pos k
  -- The order-`p` power `x = y ^ (|y| / p)`.
  set n := orderOf y / ctr.p with hn
  have hnp : n * ctr.p = orderOf y := Nat.div_mul_cancel hp_dvd
  have hn_pos : 0 < n := by
    rw [hn]; exact Nat.div_pos (Nat.le_of_dvd hord_pos hp_dvd) ctr.p_prime.pos
  have hn_lt : n < orderOf y := by
    rw [hn]; exact Nat.div_lt_self hord_pos ctr.p_prime.one_lt
  refine ⟨y ^ n, ctr.P0.pow_mem hyP0 n, ?_, ?_, ?_⟩
  · -- `y ^ n ≠ 1`: else `|y| ∣ n < |y|`, impossible.
    rw [Ne, ← orderOf_dvd_iff_pow_eq_one]
    exact Nat.not_dvd_of_pos_of_lt hn_pos hn_lt
  · -- `(y ^ n) ^ p = y ^ (n * p) = y ^ |y| = 1`.
    rw [← pow_mul, hnp, pow_orderOf_eq_one]
  · -- `C_K(y ^ n) ⊇ C_K(y) ⊄ K'`.
    rw [hKprime]
    intro hle
    apply hy_cent
    refine le_trans (inf_le_inf_right ctr.K ?_) hle
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    rintro z rfl
    exact Commute.pow_left (hg y rfl) n

/-- **Peterfalvi (12.9), the `(κ ∪ σ)ᶜ`-Hall complement obligation** — the precise BG §16
(Proposition 16.1) bridge behind `(8.12.a)`.  For the type-`I` minimal-counterexample `M`, the
Sylow `p`-subgroup `P₀` (with `p ∣ [M : M_F]`, hence `p ∤ |M_F|` as `M_F` is Hall) lies in a
`(κ(M) ∪ σ(M))ᶜ`-Hall subgroup `U ≤ M`.

*Why this is the gate (and not `(8.12.a)` itself).*  BG Theorem B(1)
(`theoremB_U_sylow_abelian_rank_le_two`, already **proved** in the repo) says every Sylow of such
a `U` is abelian of rank `≤ 2`; the only missing input is producing the complement `U`.  The
type-`I` complement of `M_F` is `π(M_F)ᶜ`-Hall (immediate from `M_F` being a normal Hall
subgroup), and Proposition 16.1's type-`I` classification (`κ(M) = ∅` and `M_F = M_σ`)
identifies `π(M_F)ᶜ` with `(κ ∪ σ)ᶜ`.

**Proof (issue 2016).**  Write `M = ctr.M`, `p = ctr.p`.  Proposition 16.1 (clause (a)) gives
`κ(M) = ∅` for the type-`I` `M`, and (clause (f)) gives `M_F = M_σ`.  Since `M_F` is `π(M_F)`-Hall
in `M` (`maxNilpotentNormalHall_isHall`) and `p ∣ [M : M_F]`, we have `p ∤ |M_F| = |M_σ|`.  As
`M_σ` is `σ(M)`-Hall in `G` (`S10.isHall_Msigma_Malpha`), `p ∤ |M_σ|` forces `p ∉ σ(M)` (else
`p` would divide the `σ`-part `|M_σ|` of `|G|`).  With `κ(M) = ∅` this gives `p ∈ (κ ∪ σ)ᶜ`, so
the `p`-group `P₀` is a `(κ ∪ σ)ᶜ`-subgroup of the solvable `M` and Hall's theorem D
(`Ch03.hall_D`) places it in a `(κ ∪ σ)ᶜ`-Hall subgroup `U` of `M`.  The only `§16`-gated inputs
are the cited Proposition 16.1 type-`I` clauses (lane-f frontier, issue 8015). -/
theorem exists_sigmaKappaCompl_hall_ge_P0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ∃ U : Subgroup G, ctr.P0 ≤ U ∧ U ≤ ctr.M ∧
      Ch03.IsHallSubgroup
        ((OddOrder.BG.Ch4.S14.kappa ctr.M ∪ OddOrder.BG.Ch3.S10.sigma ctr.M)ᶜ)
        (U.subgroupOf ctr.M) := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  haveI hMsolv : IsSolvable ↥ctr.M := hG.solvable_of_mem_maximalSubgroups ctr.M_maximal
  -- κ(M) = ∅ (Type I ⟹ Type F, Prop 16.1 clause (a)).
  have hκ : OddOrder.BG.Ch4.S14.kappa ctr.M = ∅ :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG ctr.M_maximal).1.mp ctr.M_typeI
  -- M_F = M_σ (Prop 16.1 clause (f)).
  have hMFσ : maxNilpotentNormalHall ctr.M = OddOrder.BG.Ch3.S10.Msigma ctr.M :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG ctr.M_maximal).2.2.2.2.2.mpr
      (Or.inl ctr.M_typeI)
  -- `p ∤ |M_F|`: `M_F` is `π(M_F)`-Hall in `M` and `p ∣ [M : M_F]`.
  have hpidx : ctr.p ∣ ((maxNilpotentNormalHall ctr.M).subgroupOf ctr.M).index := by
    have h := ctr.p_dvd_index
    rwa [ctr.K_eq_MF, Subgroup.relIndex] at h
  have hMFhall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall ctr.M
  have hp_not_dvd_MF : ¬ ctr.p ∣ Nat.card ↥(maxNilpotentNormalHall ctr.M) := fun hdvd =>
    hMFhall.index_no_pi ctr.p
      (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hpidx, Subgroup.index_ne_zero_of_finite⟩)
      (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hdvd, Nat.card_pos.ne'⟩)
  have hp_not_dvd_Mσ : ¬ ctr.p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma ctr.M) :=
    hMFσ ▸ hp_not_dvd_MF
  -- `p ∣ |G|` (`p ∣ [M : M_F] ∣ |M| ∣ |G|`).
  have hp_dvd_G : ctr.p ∣ Nat.card G :=
    (hpidx.trans (Subgroup.index_dvd_card _)).trans (Subgroup.card_subgroup_dvd_card ctr.M)
  -- `p ∉ σ(M)`: `M_σ` is `σ(M)`-Hall in `G`, and `p ∤ |M_σ|` with `p ∣ |G| = |M_σ|·[G:M_σ]`.
  have hσHall := (OddOrder.BG.Ch3.S10.isHall_Msigma_Malpha hG ctr.M_maximal).1
  have hp_not_sigma : ctr.p ∉ OddOrder.BG.Ch3.S10.sigma ctr.M := by
    intro hpσ
    refine hp_not_dvd_Mσ ?_
    have hpmul : ctr.p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma ctr.M)
        * (OddOrder.BG.Ch3.S10.Msigma ctr.M).index := by
      rw [Subgroup.card_mul_index]; exact hp_dvd_G
    rcases (Nat.Prime.dvd_mul ctr.p_prime).mp hpmul with h | h
    · exact h
    · exact absurd hpσ (hσHall.index_no_pi ctr.p
        (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, h, Subgroup.index_ne_zero_of_finite⟩))
  -- `p ∈ (κ ∪ σ)ᶜ`.
  have hp_compl : ctr.p ∈ (OddOrder.BG.Ch4.S14.kappa ctr.M
      ∪ OddOrder.BG.Ch3.S10.sigma ctr.M)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    exact ⟨hκ ▸ Set.notMem_empty ctr.p, hp_not_sigma⟩
  -- Every prime divisor of `|P₀|` (a `p`-power) is `p ∈ (κ ∪ σ)ᶜ`; place `P₀` via Hall D.
  have hcond : ∀ q ∈ (Nat.card ↥(ctr.P0.subgroupOf ctr.M)).primeFactors,
      q ∈ (OddOrder.BG.Ch4.S14.kappa ctr.M ∪ OddOrder.BG.Ch3.S10.sigma ctr.M)ᶜ := by
    intro q hq
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp ctr.P0_pGroup)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ctr.P0_le_M).toEquiv, hn] at hq
    obtain ⟨hqp, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
    rw [(Nat.prime_dvd_prime_iff_eq hqp ctr.p_prime).mp (hqp.dvd_of_dvd_pow hqdvd)]
    exact hp_compl
  obtain ⟨V, hVhall, hPV⟩ := Ch03.hall_D (G := ↥ctr.M) hcond
  refine ⟨V.map ctr.M.subtype, ?_, Subgroup.map_subtype_le V, ?_⟩
  · rw [show ctr.P0 = (ctr.P0.subgroupOf ctr.M).map ctr.M.subtype from
      (Subgroup.map_subgroupOf_eq_of_le ctr.P0_le_M).symm]
    exact Subgroup.map_mono hPV
  · have hUeq : (V.map ctr.M.subtype).subgroupOf ctr.M = V :=
      Subgroup.comap_map_eq_self_of_injective ctr.M.subtype_injective V
    rw [hUeq]; exact hVhall

/-- **Peterfalvi (12.9), the rank-two structure for `P₀`** = `(8.12.a)`.

Every Sylow subgroup of the type-`I` complement `U` (`M = M_F ⋊ U`) is abelian of rank `≤ 2`
(BG **Theorem B(1)**, `theoremB_U_sylow_abelian_rank_le_two`, **proved**); applied to the Sylow
`p`-subgroup `P₀ ≤ U` and combined with `P₀` noncyclic (Hypothesis `(12.8)`, `ctr.P0_noncyclic`,
giving `2 ≤ rank P₀` via `two_le_rank_of_noncyclic_pSubgroup`), this forces `P₀` abelian of rank
exactly `2`.

The substantive content (Theorem B(1) + the rank lower bound) is therefore **wired and
load-bearing**; the only remaining gap is the `(κ ∪ σ)ᶜ`-Hall complement obligation
`exists_sigmaKappaCompl_hall_ge_P0` (the BG §16 / Proposition 16.1 bridge, lane-f).

(The other structural inputs `P₀` coprime to `K`, `P₀ ≤ N_G(K)`, `⁅K, K⁆ ≠ K` are discharged in
`exists_rankTwoWitness` from `(8.11)` [`M_F` Hall] and `M_F ◁ M` nilpotent + nontrivial.) -/
theorem counterexample_P0_K_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    IsMulCommutative ↥ctr.P0 ∧ rank ↥ctr.P0 = 2 := by
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  obtain ⟨U, hP0U, hUM, hU⟩ := exists_sigmaKappaCompl_hall_ge_P0 hG ctr
  obtain ⟨hrank_le, habelian⟩ :=
    OddOrder.BG.Ch4.S16.theoremB_U_sylow_abelian_rank_le_two hG ctr.M_maximal hUM hU
      ctr.p ctr.p_prime ctr.P0 hP0U ctr.P0_pGroup
  exact ⟨habelian, le_antisymm hrank_le
    (OddOrder.BG.Ch2.S09.two_le_rank_of_noncyclic_pSubgroup hG ctr.P0_pGroup ctr.P0_noncyclic)⟩

/-- **Counterexample fact: `K = M_F = M_σ`.**  For the type-`I` minimal counterexample `M`, its
Fitting kernel `K = M_F` equals the `σ`-core `M_σ` (Proposition 16.1 clause (f), via
`proposition_type_classification`). -/
theorem MF_eq_Msigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ctr.K = OddOrder.BG.Ch3.S10.Msigma ctr.M := by
  rw [ctr.K_eq_MF]
  exact (OddOrder.BG.Ch4.S16.proposition_type_classification hG ctr.M_maximal).2.2.2.2.2.mpr
    (Or.inl ctr.M_typeI)

/-- **Counterexample fact: `p ∉ σ(M)`.**  The minimal prime `p` of Hypothesis (12.8) does not lie
in `σ(M)`: `M_σ` is `σ(M)`-Hall in `G` and `p ∤ |M_σ| = |M_F|` (as `M_F` is Hall in `M` and
`p ∣ [M : M_F]`), while `p ∣ |G| = |M_σ| · [G : M_σ]`, so `p` divides `[G : M_σ]`, forcing
`p ∉ σ(M)`. -/
theorem p_not_mem_sigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ctr.p ∉ OddOrder.BG.Ch3.S10.sigma ctr.M := by
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  have hMFσ : maxNilpotentNormalHall ctr.M = OddOrder.BG.Ch3.S10.Msigma ctr.M :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG ctr.M_maximal).2.2.2.2.2.mpr
      (Or.inl ctr.M_typeI)
  have hpidx : ctr.p ∣ ((maxNilpotentNormalHall ctr.M).subgroupOf ctr.M).index := by
    have h := ctr.p_dvd_index
    rwa [ctr.K_eq_MF, Subgroup.relIndex] at h
  have hMFhall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall ctr.M
  have hp_not_dvd_MF : ¬ ctr.p ∣ Nat.card ↥(maxNilpotentNormalHall ctr.M) := fun hdvd =>
    hMFhall.index_no_pi ctr.p
      (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hpidx, Subgroup.index_ne_zero_of_finite⟩)
      (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hdvd, Nat.card_pos.ne'⟩)
  have hp_not_dvd_Mσ : ¬ ctr.p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma ctr.M) :=
    hMFσ ▸ hp_not_dvd_MF
  have hp_dvd_G : ctr.p ∣ Nat.card G :=
    (hpidx.trans (Subgroup.index_dvd_card _)).trans (Subgroup.card_subgroup_dvd_card ctr.M)
  have hσHall := (OddOrder.BG.Ch3.S10.isHall_Msigma_Malpha hG ctr.M_maximal).1
  intro hpσ
  refine hp_not_dvd_Mσ ?_
  have hpmul : ctr.p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma ctr.M)
      * (OddOrder.BG.Ch3.S10.Msigma ctr.M).index := by
    rw [Subgroup.card_mul_index]; exact hp_dvd_G
  rcases (Nat.Prime.dvd_mul ctr.p_prime).mp hpmul with h | h
  · exact h
  · exact absurd hpσ (hσHall.index_no_pi ctr.p
      (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, h, Subgroup.index_ne_zero_of_finite⟩))

/-- **Peterfalvi (12.11), step (8.1.c): `P₀` does not centralize `K = M_F`.**  If `P₀ ≤ C_G(K)`,
then (as `K = M_σ`) `P₀ ≤ C_G(M_σ)`, so `C_G(M_σ) ⊓ P₀ = P₀` has `rank ≤ 1` by BG Proposition
10.11(b) (`rank_centralizer_Msigma_inf_le_one`, applicable since `P₀` is a `p`-group with
`p ∉ σ(M)`, hence a `σ(M)ᶜ`-subgroup of `M`).  But `P₀` is noncyclic (Hypothesis (12.8)), so
`2 ≤ rank P₀` — a contradiction.  This is the honest content of the "(8.1.c) ⟹ `P₀` does not
centralize `K`" step of Peterfalvi (12.11). -/
theorem P0_not_le_centralizer_K [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ¬ ctr.P0 ≤ Subgroup.centralizer (ctr.K : Set G) := by
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  intro hP0C
  -- `P₀` is a `σ(M)ᶜ`-subgroup (a `p`-group with `p ∉ σ(M)`).
  have hpσ : ctr.p ∉ OddOrder.BG.Ch3.S10.sigma ctr.M := p_not_mem_sigma hG ctr
  have hP0pi : ctr.P0.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma ctr.M)ᶜ := by
    intro q hq
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp ctr.P0_pGroup
    rw [hn] at hq
    obtain ⟨hqp, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
    rw [(Nat.prime_dvd_prime_iff_eq hqp ctr.p_prime).mp (hqp.dvd_of_dvd_pow hqdvd)]
    exact hpσ
  -- `rank (C_G(M_σ) ⊓ P₀) ≤ 1` (BG Prop 10.11(b)).
  have hrank := OddOrder.BG.Ch3.S10.rank_centralizer_Msigma_inf_le_one hG ctr.M_maximal
    ctr.P0_le_M hP0pi
  -- `P₀ ≤ C_G(M_σ)` (from `hP0C` and `K = M_σ`), so `C_G(M_σ) ⊓ P₀ = P₀`.
  have hP0Cσ : ctr.P0 ≤ Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma ctr.M : Set G) := by
    rwa [MF_eq_Msigma hG ctr] at hP0C
  rw [inf_eq_right.mpr hP0Cσ] at hrank
  have h2 := OddOrder.BG.Ch2.S09.two_le_rank_of_noncyclic_pSubgroup hG ctr.P0_pGroup
    ctr.P0_noncyclic
  omega

open scoped Pointwise in
/-- **Peterfalvi (8.1.b) for an arbitrary complement of `M_F`.**  For a type-`F` group `M` with
kernel `K = M_F`, if `V` is *any* complement of `K` in `M`, then the `V`-centralizers of nontrivial
kernel elements all lie in a single abelian subgroup `W ≤ V` — the conjugate of the type-`F` datum's
`U₁` by the Schur–Zassenhaus element carrying the datum's complement `U` to `V`.  (Peterfalvi (8.1)
remark: "(b) holds whatever complement `U` is chosen".)

Used in (12.11): with `V = M ∩ L` (a complement of `K` by the first assertion `(12.11)`), both a
`p'`-subgroup `A ≤ M ∩ L` and the witness `x ∈ P₀ ⊆ M ∩ L` land in this abelian `W` (via
`C_K(A) ≠ 1` and `C_K(x) ≠ 1`), so `A` centralizes `x`. -/
theorem exists_abelian_centralizer_le_of_isComplement [Finite G] {M : Subgroup G}
    (hMsolv : IsSolvable ↥M) (typeF : TypeFData M) {V : Subgroup G} (hV_le : V ≤ M)
    (hVcompl : Subgroup.IsComplement' (typeF.H.subgroupOf M) (V.subgroupOf M)) :
    ∃ W : Subgroup G, IsMulCommutative ↥W ∧
      ∀ y ∈ typeF.H, y ≠ 1 → V ⊓ Subgroup.centralizer ({y} : Set G) ≤ W := by
  classical
  haveI hHnormal : (typeF.H.subgroupOf M).Normal := by
    rw [typeF.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal M
  have hcop : Nat.Coprime (Nat.card ↥(typeF.H.subgroupOf M)) (typeF.H.subgroupOf M).index := by
    rw [typeF.H_eq]; exact (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall M).coprime_index
  -- Schur–Zassenhaus: `U` and `V` are conjugate in `↥M` by `n ∈ H = M_F`.
  haveI : IsSolvable ↥M := hMsolv
  obtain ⟨n, hn_mem, hn_conj⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop (Or.inl inferInstance) typeF.complement
      hVcompl
  set m : G := (n : G) with hm
  have hmH : m ∈ typeF.H := Subgroup.mem_subgroupOf.mp hn_mem
  have hmM : m ∈ M := n.2
  -- Bridge `↥M`-conjugation to ambient `G`: `U.map (conj m) = V`.
  have hbridge : M.subtype.comp (MulAut.conj n).toMonoidHom
      = (MulAut.conj m).toMonoidHom.comp M.subtype := by
    ext a; simp [MulAut.conj_apply, hm, mul_assoc]
  have hUmV : typeF.U.map (MulAut.conj m).toMonoidHom = V := by
    have h1 := congrArg (Subgroup.map M.subtype) hn_conj
    rw [Subgroup.map_map, hbridge, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le typeF.U_le,
      Subgroup.map_subgroupOf_eq_of_le hV_le] at h1
    exact h1
  refine ⟨typeF.U1.map (MulAut.conj m).toMonoidHom, ⟨⟨?_⟩⟩, ?_⟩
  · -- `W = U₁ᵐ` is abelian (conjugate of abelian `U₁`).
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨u, hu, hua⟩ := Subgroup.mem_map.mp ha
    obtain ⟨u', hu', hub⟩ := Subgroup.mem_map.mp hb
    have huu' : u * u' = u' * u := by
      have h := typeF.U1_commutative.is_comm.comm (⟨u, hu⟩ : ↥typeF.U1) ⟨u', hu'⟩
      simpa using congrArg Subtype.val h
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hua, ← hub, ← map_mul, ← map_mul, huu']
  · -- `V ⊓ C(y) ≤ W`: `v ∈ V = Uᵐ`, `v` centralizes `y`, so `u = vᵐ⁻¹ ∈ U ⊓ C(yᵐ⁻¹) ≤ U₁`.
    intro y hyH hy1 v hv
    obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.mp hv
    rw [← hUmV] at hvV
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hvV
    apply Subgroup.mem_map_of_mem
    -- `y' = m⁻¹ y m ∈ H^#`.
    have hy'H : m⁻¹ * y * m ∈ typeF.H := by
      have hyM : y ∈ M := typeF.H_le hyH
      have hconj := hHnormal.conj_mem ⟨y, hyM⟩ (Subgroup.mem_subgroupOf.mpr hyH)
        ⟨m⁻¹, M.inv_mem hmM⟩
      have := Subgroup.mem_subgroupOf.mp hconj
      simpa [mul_assoc] using this
    have hy'1 : m⁻¹ * y * m ≠ 1 := by
      intro h; apply hy1
      have hyeq : y = m * (m⁻¹ * y * m) * m⁻¹ := by group
      rw [hyeq, h]; group
    -- `u` centralizes `m⁻¹ y m` because `mᵘ = (conj m) u` centralizes `y`.
    have hcvy : (m * u * m⁻¹) * y = y * (m * u * m⁻¹) := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hvC
      simpa [MulAut.conj_apply] using h
    have hthis : m * (u * (m⁻¹ * y * m)) * m⁻¹ = m * ((m⁻¹ * y * m) * u) * m⁻¹ := by
      have hE : m * (u * (m⁻¹ * y * m)) * m⁻¹ = (m * u * m⁻¹) * y := by group
      have hE' : m * ((m⁻¹ * y * m) * u) * m⁻¹ = y * (m * u * m⁻¹) := by group
      rw [hE, hE', hcvy]
    have hu_cent : u ∈ Subgroup.centralizer ({m⁻¹ * y * m} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_left_cancel (mul_right_cancel hthis))
    exact typeF.centralizer_le_U1 (m⁻¹ * y * m) hy'H hy'1 (Subgroup.mem_inf.mpr ⟨hu, hu_cent⟩)

/-- A `p`-Hall subgroup `H` (its order having only `p`-primary divisors among `π = π(|H|)`) with
`p ∣ |H|` contains a Sylow `p`-subgroup of the ambient group `G`.

A Sylow `p`-subgroup `R` of `↥H` maps to a subgroup `R.map H.subtype ≤ H` of `G` of the same
order `p ^ v_p(|H|)`.  Since `H` is Hall, `p ∤ [G : H]`, so `v_p(|H|) = v_p(|G|)`; hence
`R.map H.subtype` is a Sylow `p`-subgroup of `G` contained in `H`. -/
theorem exists_sylow_le_of_hall [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hHall : Ch03.IsHallSubgroup (Nat.card ↥H).primeFactors H) (hp : p ∣ Nat.card ↥H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) ≤ H := by
  classical
  -- A Sylow `p`-subgroup `R` of `↥H`.
  obtain ⟨R⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥H))
  -- The `p`-multiplicity of `|H|` equals that of `|G|`, because `H` is Hall and `p ∣ |H|`.
  have hfact : (Nat.card ↥H).factorization p = (Nat.card G).factorization p := by
    have hcop : Nat.Coprime (Nat.card ↥H) H.index := hHall.coprime_index
    have hp_notdvd : ¬ p ∣ H.index :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hp)
    have hidx0 : H.index.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_notdvd
    have hsplit : (Nat.card G).factorization p =
        (Nat.card ↥H).factorization p + H.index.factorization p := by
      rw [← H.card_mul_index, Nat.factorization_mul (Nat.card_pos (α := ↥H)).ne'
        Subgroup.index_ne_zero_of_finite]
      rfl
    rw [hsplit, hidx0, add_zero]
  -- `R.map H.subtype` is a `p ^ v_p(|G|)`-subgroup of `G`, i.e. a Sylow `p`-subgroup.
  have hcardR : Nat.card ↥(R : Subgroup ↥H) = p ^ (Nat.card G).factorization p := by
    rw [R.card_eq_multiplicity, hfact]
  have hcardQ : Nat.card ↥((R : Subgroup ↥H).map H.subtype) =
      p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hcardR]
  exact ⟨Sylow.ofCard ((R : Subgroup ↥H).map H.subtype) hcardQ,
    by rw [Sylow.coe_ofCard]; exact Subgroup.map_subtype_le _⟩

/-- **Peterfalvi (12.9), existence of the second maximal `L`** — a §8 obligation
(`(8.17.a)` `bgTheoremE_cover_data`: `p ∈ π(G)` is covered by some `π((M_i)_s)`, giving a maximal
`L` with `p ∣ |L_s|`; then `(8.11)`/`L_s ⊇ Sylow_p(G)` and Sylow conjugation place `P₀ ⊆ L_s`). -/
theorem exists_second_maximal [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ∃ (L : Subgroup G) (Lt : PeterfalviType), L ∈ maximalSubgroups G ∧ L ≠ ctr.M ∧
      HasPeterfalviType Lt L ∧ ctr.P0 ≤ mainSubgroup L Lt := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- `p ∈ π(G)`: `p ∣ [M : M_F] ∣ |M| ∣ |G|`.
  have hp_in_G : ctr.p ∈ (Nat.card G).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨ctr.p_prime, ?_, Nat.card_pos.ne'⟩
    refine dvd_trans ctr.p_dvd_index (dvd_trans ?_ (Subgroup.card_subgroup_dvd_card ctr.M))
    exact Subgroup.relIndex_dvd_card (H := ctr.K) (K := ctr.M)
  -- `p ∤ |M_F| = |K|`: `(8.11)` makes `M_F` Hall, and `p ∣ [M : M_F] ∣ [G : M_F]`.
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  have hpK : ¬ ctr.p ∣ Nat.card ↥ctr.K := by
    have hHall := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG
      ctr.M_maximal (tau := PeterfalviType.I) ctr.M_typeI).1
    rw [← ctr.K_eq_MF] at hHall
    have hp_idx : ctr.p ∣ ctr.K.index :=
      ctr.p_dvd_index.trans (Subgroup.relIndex_dvd_index_of_le hKM)
    exact ctr.p_prime.coprime_iff_not_dvd.mp
      (Nat.Coprime.coprime_dvd_left hp_idx hHall.coprime_index.symm)
  -- BG Theorem E cover data: `p ∈ π((M_i)_s)` for some representative `M_i = L₀`.  Repackage the
  -- representative as genuine local variables `L₀, Lt` (so we may later `cases` on the type label).
  obtain ⟨data, -⟩ := OddOrder.Peterfalvi.S10.bgTheoremE_cover_data.{_, 0} hG
  obtain ⟨i, hi⟩ := (data.primeFactors_cover ctr.p ctr.p_prime).mp hp_in_G
  obtain ⟨L₀, Lt, hL₀max, hL₀typed, hi'⟩ :
      ∃ (L₀ : Subgroup G) (Lt : PeterfalviType), L₀ ∈ maximalSubgroups G ∧
        HasPeterfalviType Lt L₀ ∧
        ctr.p ∈ (Nat.card ↥(mainSubgroup L₀ Lt)).primeFactors :=
    ⟨data.reps i, data.tau i, data.maximal i, data.typed i, hi⟩
  have hp_Ls : ctr.p ∣ Nat.card ↥(mainSubgroup L₀ Lt) := (Nat.mem_primeFactors.mp hi').2.1
  -- `(8.11)`: `(L₀)_s` is Hall, hence contains a Sylow `p`-subgroup `Q` of `G`.
  have hLsHall : Ch03.IsHallSubgroup (Nat.card ↥(mainSubgroup L₀ Lt)).primeFactors
      (mainSubgroup L₀ Lt) :=
    (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG hL₀max hL₀typed).2
  obtain ⟨Q, hQle⟩ := exists_sylow_le_of_hall hLsHall hp_Ls
  -- A Sylow `p`-subgroup `Q'` of `G` over `P₀`, then conjugate `Q` to `Q'`.
  obtain ⟨Q', hQ'le⟩ := ctr.P0_pGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q Q'
  -- `P₀ ≤ Q' = ↑(g • Q) = conj g • ↑Q ≤ conj g • (L₀)_s`.
  have hP0_le : ctr.P0 ≤ MulAut.conj g • mainSubgroup L₀ Lt := by
    refine hQ'le.trans ?_
    have hQ'eq : (Q' : Subgroup G) = MulAut.conj g • (Q : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul]
    rw [hQ'eq]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQle
  -- Assemble: `L = conj g • L₀`, type `Lt`, with `P₀ ⊆ (conj g • L₀)_s`.
  refine ⟨MulAut.conj g • L₀, Lt, mem_maximalSubgroups.mpr
    (OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hL₀max)), ?_,
    hasPeterfalviType_pointwise_smul (MulAut.conj g) Lt hL₀typed, ?_⟩
  · -- `conj g • L₀ ≠ M`: else `M` has type `Lt`; if `Lt = I` then `p ∣ |K|` (false), else `M` is
    -- both type I and non-I (false).
    rintro hEq
    have hMtype : HasPeterfalviType Lt ctr.M :=
      hEq ▸ hasPeterfalviType_pointwise_smul (MulAut.conj g) Lt hL₀typed
    -- transport the divisibility `p ∣ |(L₀)_s|` to `p ∣ |M_s|`.
    have hp_Ms : ctr.p ∣ Nat.card ↥(mainSubgroup ctr.M Lt) := by
      have hcard : Nat.card ↥(mainSubgroup ctr.M Lt) = Nat.card ↥(mainSubgroup L₀ Lt) := by
        rw [← hEq, ← mainSubgroup_pointwise_smul, card_pointwise_smul]
      rw [hcard]; exact hp_Ls
    -- `ctr.M` has type `Lt` and type I.  Type `I` forces `p ∣ |K|` (false); any non-I label
    -- makes `ctr.M` non-I, contradicting type I via `not_isTypeI_of_isTypeNonI`.
    have hMnotNonI : ¬ IsTypeNonI ctr.M := fun h =>
      OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG ctr.M_maximal h ctr.M_typeI
    cases Lt with
    | I => exact hpK (by rw [ctr.K_eq_MF]; exact hp_Ms)
    | II => exact hMnotNonI (Or.inl hMtype)
    | III => exact hMnotNonI (Or.inr (Or.inl hMtype))
    | IV => exact hMnotNonI (Or.inr (Or.inr (Or.inl hMtype)))
    | V => exact hMnotNonI (Or.inr (Or.inr (Or.inr hMtype)))
  · -- `P₀ ⊆ mainSubgroup (conj g • L₀) Lt`.
    rw [← mainSubgroup_pointwise_smul]; exact hP0_le

/-- **Peterfalvi (12.9), centralizer control** — **discharged** from `(8.12.b)`
(`typeI_or_typeII_centralizer_unique`) + `G` simple.

Applying `(8.12.b)` with `U = M` and `X = {x}` (`x ∈ M^#`, and `C_K(x) ⊄ K'` gives
`M_F ⊓ C_G(x) ≠ 1`) yields `C_G(x) ≤ M` together with `IsUniquelyMaximal (C_G(x))` — `M` is the
*unique* maximal subgroup over `C_G(x)`.  Hence: `N_G(⟨x⟩) ⊇ C_G(x)` is a proper subgroup
(`⟨x⟩` is a proper nontrivial subgroup of the nonabelian simple `G`, so not normal), so it lies
in a maximal subgroup over `C_G(x)`, which must be `M`; and any maximal `L ≠ M` cannot contain
`C_G(x)`. -/
theorem centralizer_control_of_CKx [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) {L : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hLM : L ≠ ctr.M)
    {Lt : PeterfalviType} (_hLt : HasPeterfalviType Lt L) (_hPL : ctr.P0 ≤ mainSubgroup L Lt)
    {x : G} (hx : x ∈ ctr.P0) (hxne : x ≠ 1)
    (hCKx : ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime)) :
    Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≤ ctr.M ∧
      ¬ (Subgroup.centralizer ({x} : Set G) ≤ L) := by
  classical
  haveI : IsSimpleGroup G := hG.simple
  have hMcoatom : IsCoatom ctr.M := ctr.M_maximal
  have hLcoatom : IsCoatom L := hL
  have hxM : x ∈ ctr.M := ctr.P0_le_M hx
  -- `M_F ⊓ C_G(x) ≠ ⊥` from `C_K(x) ⊄ K'`.
  have hCKne : maxNilpotentNormalHall ctr.M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    intro hbot; apply hCKx; rw [ctr.K_eq_MF, inf_comm, hbot]; exact bot_le
  -- The genuine `(κ ∪ σ)ᶜ`-Hall complement `U₀ ⊇ P₀ ∋ x` that BG (8.12.b) requires.
  obtain ⟨U0, hP0U0, hU0M, hU0hall⟩ := exists_sigmaKappaCompl_hall_ge_P0 hG ctr
  have hxsharp : ({x} : Set G) ⊆ sharpSubgroup U0 := by
    intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
    exact ⟨hP0U0 hx, fun h => hxne (Set.mem_singleton_iff.mp h)⟩
  -- (8.12.b): `C_G(x) ≤ M` and uniquely maximal.
  obtain ⟨hCxleM, huniq⟩ := OddOrder.Peterfalvi.S10.typeI_or_typeII_centralizer_unique_hall hG
    ctr.M_maximal (Or.inl ctr.M_typeI) hU0M hU0hall ({x} : Set G) (Set.singleton_nonempty x)
    hxsharp hCKne
  refine ⟨?_, fun hCxleL => hLM (huniq.eq_of_isCoatom_of_le hMcoatom hCxleM hLcoatom hCxleL).symm⟩
  -- `N_G(⟨x⟩) ⊆ M`.
  have hCx_le_Nx : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) := by
    rw [← Subgroup.centralizer_closure]; exact Subgroup.centralizer_le_normalizer _
  have hcl_le_M : Subgroup.closure ({x} : Set G) ≤ ctr.M := Subgroup.closure_le _ |>.mpr (by
    simpa using hxM)
  have hNx_lt : Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≠ ⊤ := by
    intro htop
    rcases (Subgroup.normalizer_eq_top_iff.mp htop).eq_bot_or_eq_top with hb | ht
    · exact hxne (by simpa [hb] using Subgroup.subset_closure (Set.mem_singleton x))
    · exact hMcoatom.1 (top_le_iff.mp (ht ▸ hcl_le_M))
  obtain ⟨N, hNco, hNx_le_N⟩ := (eq_top_or_exists_le_coatom _).resolve_left hNx_lt
  exact hNx_le_N.trans (le_of_eq
    (huniq.eq_of_isCoatom_of_le hMcoatom hCxleM hNco (hCx_le_Nx.trans hNx_le_N)).symm)

/-- **Peterfalvi (12.9)**: the counterexample has an abelian rank-two Sylow
witness and an element whose centralizers force a second maximal subgroup.

Honest assembly: the structural inputs `(8.12.a)`/`(8.11)` (`counterexample_P0_K_structure`) give
`P₀` abelian of rank `2`, coprime to `K`, normalizing `K`, with `K` not perfect; the genuine
`§8`-free `exists_orderP_centralizer_witness` then produces the order-`p` element `x` with
`C_K(x) ⊄ K'`; `(8.17.a)` (`exists_second_maximal`) supplies `L`; and `(8.12.b)`
(`centralizer_control_of_CKx`) the centralizer conditions. -/
theorem exists_rankTwoWitness [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    IsMulCommutative ↥ctr.P0 ∧ rank ↥ctr.P0 = 2 ∧ Nonempty (RankTwoWitnessData ctr) := by
  obtain ⟨hab, hrank⟩ := counterexample_P0_K_structure hG ctr
  refine ⟨hab, hrank, ?_⟩
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  -- `P₀` coprime to `K`: `(8.11)` makes `M_F` Hall (`p ∤ |M_F|` from `p ∣ [M : M_F] ∣ [G : M_F]`).
  have hcop : Nat.Coprime (Nat.card ↥ctr.P0) (Nat.card ↥ctr.K) := by
    have hHall := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG
      ctr.M_maximal (tau := PeterfalviType.I) ctr.M_typeI).1
    rw [← ctr.K_eq_MF] at hHall
    have hp_idx : ctr.p ∣ ctr.K.index :=
      ctr.p_dvd_index.trans (Subgroup.relIndex_dvd_index_of_le hKM)
    have hcop_p : Nat.Coprime ctr.p (Nat.card ↥ctr.K) :=
      Nat.Coprime.coprime_dvd_left hp_idx hHall.coprime_index.symm
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp ctr.P0_pGroup
    rw [hn]; exact hcop_p.pow_left n
  -- `P₀ ≤ N_G(K)` from `M_F ◁ M` (`maxNilpotentNormalHall_le_normalizer`).
  have hnorm : ctr.P0 ≤ Subgroup.normalizer ctr.K := by
    rw [ctr.K_eq_MF]
    exact ctr.P0_le_M.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer ctr.M)
  -- `⁅K, K⁆ ≠ K`: `K = M_F` is nilpotent and nontrivial, hence not perfect.
  have hperf : ⁅ctr.K, ctr.K⁆ ≠ ctr.K := by
    obtain ⟨tiData⟩ := ctr.M_typeI
    have hKH : ctr.K = tiData.typeF.H := ctr.K_eq_MF.trans tiData.typeF.H_eq.symm
    haveI : Nontrivial ↥ctr.K :=
      ctr.K.nontrivial_iff_ne_bot.mpr (hKH ▸ tiData.typeF.H_nontrivial)
    haveI : Group.IsNilpotent ↥ctr.K :=
      ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent ctr.M
    have hlt : commutator ↥ctr.K < ⊤ :=
      IsSolvable.commutator_lt_top_of_nontrivial (G := ↥ctr.K)
    intro hEq
    have htop_map : (⊤ : Subgroup ↥ctr.K).map ctr.K.subtype = ctr.K := by
      ext g
      simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
      exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩
    exact hlt.ne (Subgroup.map_injective ctr.K.subtype_injective
      (by rw [Subgroup.map_subtype_commutator, hEq, htop_map]))
  obtain ⟨x, hxP0, hxne, hxp, hCKx⟩ := exists_orderP_centralizer_witness ctr hab hcop hnorm hperf
  obtain ⟨L, Lt, hLmax, hLne, hLt, hPL⟩ := exists_second_maximal hG ctr
  obtain ⟨hNx, hCx⟩ := centralizer_control_of_CKx hG ctr hLmax hLne hLt hPL hxP0 hxne hCKx
  exact ⟨{ L := L, L_maximal := hLmax, L_type := Lt, L_hasType := hLt, P0_le_Ls := hPL,
           x := x, x_mem_P0 := hxP0, x_ne_one := hxne, x_mem_omega1 := hxp,
           CKx_not_le_Kprime := hCKx, normalizer_closure_x_le_M := hNx,
           centralizer_x_not_le_L := hCx }⟩

/-- **Peterfalvi (10.10)+(11.9.c)+(11.6)+(9.7.b) kernel reduction, Type III/IV** (pinned sorried
§9–§11 obligation, hub 9003 Cluster A): for a maximal subgroup `L` of Type III or IV, a noncyclic
`p`-group `P₀ ⊆ L_s` lies in the Fitting kernel `L_F`.

This is the second paragraph of (12.10) up to its final (8.6.a) step: by Theorem (10.10)
(`S12.no_typeV_maximal_unconditional`, available — excludes Type V) and (11.9.c)
(the §13 type determination, `S13_NonGaloisExclusion`) `L` is Type III with case (b) of
(9.7); by (11.6)
(`C_U(H) = 1`) and (9.7.b) the complement `U` of `H = L_F` in `[L,L]` is **cyclic**.  Since
`L_F` is a normal Hall subgroup of `L_s = [L,L]` with cyclic complement, a noncyclic `p`-group
`P₀ ≤ L_s` cannot embed in the complement side (`p ∣ |U|` would make `P₀ ↪ L_s/L_F ≅ U` cyclic),
so `p ∣ |L_F|` and `P₀` lies in the Sylow `p`-subgroup of the normal Hall `L_F`, i.e. `P₀ ⊆ L_F`.
**Genuinely still-missing**: assembling the (9.7.b)/(11.6) cyclicity of `U`
(`S13.U_isCyclic_of_hypothesis`, proven in `S13_NonGaloisExclusion`) and the Hall-embedding
bookkeeping in reach of S14. -/
theorem typeIIIorIV_noncyclic_le_fitting [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L P0 : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hIIIIV : IsTypeIII L ∨ IsTypeIV L) {p : ℕ} (hp : p.Prime) (hP0p : IsPGroup p ↥P0)
    (hP0nc : ¬ IsCyclic ↥P0)
    {Lt : PeterfalviType} (hLhasType : HasPeterfalviType Lt L)
    (hP0 : P0 ≤ mainSubgroup L Lt) :
    P0 ≤ maxNilpotentNormalHall L := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- The genuine content, for types III/IV where `mainSubgroup L = L' = [L,L]`.  For types I/II/V
  -- `mainSubgroup L = M_F` and the goal is exactly `hP0`.
  have key : P0 ≤ derivedInG L → P0 ≤ maxNilpotentNormalHall L := by
    intro hP0'
    -- (10.10)+(11.9.c): the (10.1)/(11.2) Hypothesis holds, so (11.6)+(9.7.b) makes `U` cyclic.
    obtain ⟨hyp12⟩ := OddOrder.Peterfalvi.S12.exists_hypothesis_of_typeIIIorIVorV hG hL
      (hIIIIV.imp id Or.inl)
    obtain ⟨s13, -⟩ := OddOrder.Peterfalvi.S13.exists_hypothesis_of_isTypeIIIorIV hG hyp12 hIIIIV
    haveI : NeZero (Nat.card (s13.base.toHypothesis46 hG hG.odd).W1) := ⟨Nat.card_pos.ne'⟩
    -- **(11.9.c)/(9.7.b): `U` is cyclic** (Peterfalvi §11.9, proven sorry-free in
    -- `S13_NonGaloisExclusion`).  Available here now that the §12–16 import inversion is resolved
    -- (HUB RULING, issue 9093: the §16 pair-data structures were extracted to
    -- `S13_Section16PairData`
    -- and the (12.17) producer to `FeitThompsonPairProducer`, so `S13_NonGaloisExclusion` sits
    -- upstream
    -- of §12.10 as the mathematics requires).
    have hUcyc : IsCyclic ↥s13.base.typeP.U :=
      OddOrder.Peterfalvi.S13.U_isCyclic_of_hypothesis hG s13
    set d : TypePData L := s13.base.typeP with hd
    -- `M_F = H ≤ L' ≤ L`, and `M_F ⊴ L'` (via `L' ≤ L ≤ N_G(M_F)`).
    have hLFle : maxNilpotentNormalHall L ≤ derivedInG L := by rw [← d.H_eq]; exact d.H_le
    have hL'le : derivedInG L ≤ L := Subgroup.map_subtype_le _
    have hNnorm : ((maxNilpotentNormalHall L).subgroupOf (derivedInG L)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLFle).mpr
        (hL'le.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer L))
    -- `|U| = [L' : M_F]` divides `[L : M_F]`, and `M_F` is Hall in `L`, so `gcd(|M_F|, |U|) = 1`.
    have hUdvd : Nat.card ↥d.U ∣ ((maxNilpotentNormalHall L).subgroupOf L).index := by
      have htower := Subgroup.relIndex_mul_relIndex (maxNilpotentNormalHall L) (derivedInG L) L
        hLFle hL'le
      rw [d.card_U_eq_index]
      change (maxNilpotentNormalHall L).relIndex (derivedInG L)
        ∣ (maxNilpotentNormalHall L).relIndex L
      exact ⟨(derivedInG L).relIndex L, htower.symm⟩
    have hcopHU : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (Nat.card ↥d.U) := by
      have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall L
      have hcard : Nat.card ↥((maxNilpotentNormalHall L).subgroupOf L)
          = Nat.card ↥(maxNilpotentNormalHall L) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L)).toEquiv
      have hci := hHall.coprime_index
      rw [hcard] at hci
      exact hci.coprime_dvd_right hUdvd
    -- The crux: `p ∤ |U|`.  Otherwise `P₀` embeds in the cyclic quotient `L'/M_F ≅ U`, making
    -- `P₀` cyclic (contradiction).
    have hpU : ¬ p ∣ Nat.card ↥d.U := by
      intro hpU
      apply hP0nc
      have hpLF : ¬ p ∣ Nat.card ↥(maxNilpotentNormalHall L) := fun h =>
        hp.ne_one (Nat.dvd_one.mp (hcopHU.gcd_eq_one ▸ Nat.dvd_gcd h hpU))
      -- `P₀ ∩ M_F = 1`: a `p`-group inside the `p'`-order `M_F`.
      have hP0inf : P0 ⊓ maxNilpotentNormalHall L = ⊥ := by
        obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp
          (hP0p.to_inf_left (K := maxNilpotentNormalHall L))
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · exact Subgroup.card_eq_one.mp (by rw [hn, h0, pow_zero])
        · exact absurd (dvd_trans (dvd_pow_self p hpos.ne')
            (hn ▸ Subgroup.card_dvd_of_le inf_le_right)) hpLF
      -- `L'/M_F ≅ U` is cyclic.
      have hcompl : Subgroup.IsComplement'
          ((maxNilpotentNormalHall L).subgroupOf (derivedInG L))
          (d.U.subgroupOf (derivedInG L)) := by rw [← d.H_eq]; exact d.derived_complement
      haveI : ((maxNilpotentNormalHall L).subgroupOf (derivedInG L)).Normal := hNnorm
      haveI hUcyc' : IsCyclic ↥(d.U.subgroupOf (derivedInG L)) :=
        (Subgroup.subgroupOfEquivOfLe d.U_le).isCyclic.mpr hUcyc
      haveI hQcyc :
          IsCyclic (↥(derivedInG L) ⧸ (maxNilpotentNormalHall L).subgroupOf (derivedInG L)) :=
        (hcompl.symm.QuotientMulEquiv).isCyclic.mpr hUcyc'
      -- `P₀ ↪ L'/M_F` (kernel `P₀ ∩ M_F = 1`), so `P₀` is cyclic.
      have hinj : Function.Injective
          ((QuotientGroup.mk' ((maxNilpotentNormalHall L).subgroupOf (derivedInG L))).comp
            (P0.subgroupOf (derivedInG L)).subtype) := by
        rw [injective_iff_map_eq_one]
        intro x hx
        have hxN : ((x : ↥(derivedInG L)) : G) ∈ maxNilpotentNormalHall L := by
          rwa [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
            Subgroup.mem_subgroupOf] at hx
        have hxP0 : ((x : ↥(derivedInG L)) : G) ∈ P0 := by
          have h2 := x.2; rwa [Subgroup.mem_subgroupOf] at h2
        have hbot : ((x : ↥(derivedInG L)) : G) ∈ P0 ⊓ maxNilpotentNormalHall L := ⟨hxP0, hxN⟩
        rw [hP0inf, Subgroup.mem_bot] at hbot
        exact Subtype.ext (Subtype.ext hbot)
      haveI : IsCyclic ↥(P0.subgroupOf (derivedInG L)) := isCyclic_of_injective _ hinj
      exact (Subgroup.subgroupOfEquivOfLe hP0').isCyclic.mp inferInstance
    -- With `p ∤ |U|`, `|P₀|` (a `p`-power) is coprime to `|U| = [L' : M_F]`, so `P₀ ≤ M_F`.
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP0p
    have hcop : Nat.Coprime (Nat.card ↥P0) (Nat.card ↥d.U) := by
      rw [hn]; exact (hp.coprime_iff_not_dvd.mpr hpU).pow_left n
    haveI : ((maxNilpotentNormalHall L).subgroupOf (derivedInG L)).Normal := hNnorm
    have hle : P0.subgroupOf (derivedInG L)
        ≤ (maxNilpotentNormalHall L).subgroupOf (derivedInG L) := by
      apply OddOrder.BG.Ch4.S14.le_of_coprime_index
      rw [← d.card_U_eq_index, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP0').toEquiv]
      exact hcop
    intro x hx
    have hxL' : x ∈ derivedInG L := hP0' hx
    have hmem : (⟨x, hxL'⟩ : ↥(derivedInG L))
        ∈ (maxNilpotentNormalHall L).subgroupOf (derivedInG L) :=
      hle (by rw [Subgroup.mem_subgroupOf]; exact hx)
    rwa [Subgroup.mem_subgroupOf] at hmem
  cases Lt with
  | I => simpa [mainSubgroup] using hP0
  | II => simpa [mainSubgroup] using hP0
  | III => exact key (by simpa [mainSubgroup] using hP0)
  | IV => exact key (by simpa [mainSubgroup] using hP0)
  | V => simpa [mainSubgroup] using hP0

/-- **Peterfalvi (10.10)+(11.9.c)+(11.6)+(9.7.b)+(8.6.a), Type III/IV route**: for a maximal
subgroup `L` of Type III or IV and a noncyclic `p`-group `P₀ ⊆ L_s`, `C_G(y) ⊆ L` for every
nonidentity `y ∈ P₀`.

**Assembly** (`sorry`-free modulo the (11.9.c)/(9.7.b) kernel reduction): the reduction
`typeIIIorIV_noncyclic_le_fitting` places `P₀ ⊆ L_F`, and the (8.6.a) TI containment
`typeP_core_centralizer_le_of_mem_fitting` (via the `TypePNontrivialCore` carried by both the
`TypeIIIData` and `TypeIVData` witnesses) yields `C_G(y) ≤ L` for `y ∈ L_F^#`. -/
theorem typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L P0 : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hIIIIV : IsTypeIII L ∨ IsTypeIV L) {p : ℕ} (hp : p.Prime) (hP0p : IsPGroup p ↥P0)
    (hP0nc : ¬ IsCyclic ↥P0)
    {Lt : PeterfalviType} (hLhasType : HasPeterfalviType Lt L)
    (hP0 : P0 ≤ mainSubgroup L Lt) {y : G} (hy : y ∈ P0) (hy1 : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) ≤ L := by
  have hyF : y ∈ maxNilpotentNormalHall L :=
    typeIIIorIV_noncyclic_le_fitting hG hL hIIIIV hp hP0p hP0nc hLhasType hP0 hy
  have hcommon : ∃ pdata : TypePData L, TypePNontrivialCore L pdata := by
    rcases hIIIIV with h3 | h4
    · obtain ⟨iiiData⟩ := h3
      exact ⟨iiiData.typeP, iiiData.common⟩
    · obtain ⟨ivData⟩ := h4
      exact ⟨ivData.typeP, ivData.common⟩
  obtain ⟨pdata, hcore⟩ := hcommon
  exact typeP_core_centralizer_le_of_mem_fitting hG hL hcore hyF hy1

/-- **Peterfalvi (12.10) obligation A**: the (12.9) witness `L` is of Type I.

(12.10) rules out every non-Type-I possibility, each forcing `C_G(x) ⊆ L` and so contradicting the
(12.9) escape condition `data.centralizer_x_not_le_L` (`¬ C_G(x) ≤ L`).  The witness `x` lies in
`P₀^# ⊆ (L_s)^#` (`data.x_mem_P0`, `data.P0_le_Ls`, `data.x_ne_one`), and `P₀` is noncyclic
(`ctr.P0_noncyclic`).

* **Type V** is excluded outright by the (10.10) hypothesis `hnoV` (instantiate with the
  axiom-clean `no_typeV_maximal_unconditional`, `S12_Noncoherence`; issue 9087).
* **Type II**: (8.16) gives `C_G(x) ⊆ L` for `x ∈ (L_s)^# = A_1(L)`
  (`typeII_centralizer_le_of_mem_mainSubgroup`), contradiction.
* **Types III/IV**: via (10.10)+(11.9.c)+(11.6)+(9.7.b), `P₀ ⊆ L_F`, and (8.6.a) gives
  `C_G(x) ⊆ L` for `x ∈ L_F^#` (`typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup`),
  contradiction.

The two §8–§11 centralizer-containment facts are pinned sorried above (genuinely missing as usable
containments — the upstream (8.16)/(8.6.a)/(11.9.c) results are themselves sorried or overstated);
the case analysis, the Type-V exclusion (hypothesised, honest), and the contradiction assembly
here are honest. -/
theorem witness_L_isTypeI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    IsTypeI data.L := by
  -- `x ∈ (L_s)^#`: nonidentity element of `mainSubgroup L L_type`.
  have hx_mem : data.x ∈ mainSubgroup data.L data.L_type := data.P0_le_Ls data.x_mem_P0
  -- The escape condition to be contradicted in every non-Type-I case.
  have hEsc : ¬ (Subgroup.centralizer ({data.x} : Set G) ≤ data.L) := data.centralizer_x_not_le_L
  -- Case-split on the Peterfalvi type of `L` (carried by `data.L_hasType`).
  have hLt := data.L_hasType
  cases hLtype : data.L_type with
  | I =>
    -- `HasPeterfalviType .I L` is definitionally `IsTypeI L`.
    rw [hLtype] at hLt; exact hLt
  | II =>
    rw [hLtype] at hLt hx_mem
    exact absurd (typeII_centralizer_le_of_mem_mainSubgroup hG data.L_maximal hLt hx_mem
      data.x_ne_one) hEsc
  | III =>
    rw [hLtype] at hLt
    exact absurd (typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup hG data.L_maximal
      (Or.inl hLt) ctr.p_prime ctr.P0_pGroup ctr.P0_noncyclic data.L_hasType data.P0_le_Ls
      data.x_mem_P0 data.x_ne_one) hEsc
  | IV =>
    rw [hLtype] at hLt
    exact absurd (typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup hG data.L_maximal
      (Or.inr hLt) ctr.p_prime ctr.P0_pGroup ctr.P0_noncyclic data.L_hasType data.P0_le_Ls
      data.x_mem_P0 data.x_ne_one) hEsc
  | V =>
    rw [hLtype] at hLt
    exact absurd ⟨data.L, data.L_maximal, hLt⟩ hnoV

/-- **Peterfalvi (12.9)/(12.10): the witness type is exactly `I`.**  The recorded type `data.L_type`
of the witness `L` is forced to be `I`: every other type contradicts the escape condition
`C_G(x) ⊄ L` (`data.centralizer_x_not_le_L`) via the type-II/III/IV centralizer-containment lemmas
(and type `V` is excluded outright by the (10.10) hypothesis `hnoV`).  Same case-split as
`witness_L_isTypeI`, but concluding the identity `data.L_type = I` needed to compute
`L_s = L_F`. -/
theorem witness_L_type_eq_typeI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    data.L_type = PeterfalviType.I := by
  have hx_mem : data.x ∈ mainSubgroup data.L data.L_type := data.P0_le_Ls data.x_mem_P0
  have hEsc : ¬ (Subgroup.centralizer ({data.x} : Set G) ≤ data.L) := data.centralizer_x_not_le_L
  have hLt := data.L_hasType
  cases hLtype : data.L_type with
  | I => rfl
  | II =>
    rw [hLtype] at hLt hx_mem
    exact absurd (typeII_centralizer_le_of_mem_mainSubgroup hG data.L_maximal hLt hx_mem
      data.x_ne_one) hEsc
  | III =>
    rw [hLtype] at hLt
    exact absurd (typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup hG data.L_maximal
      (Or.inl hLt) ctr.p_prime ctr.P0_pGroup ctr.P0_noncyclic data.L_hasType data.P0_le_Ls
      data.x_mem_P0 data.x_ne_one) hEsc
  | IV =>
    rw [hLtype] at hLt
    exact absurd (typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup hG data.L_maximal
      (Or.inr hLt) ctr.p_prime ctr.P0_pGroup ctr.P0_noncyclic data.L_hasType data.P0_le_Ls
      data.x_mem_P0 data.x_ne_one) hEsc
  | V =>
    rw [hLtype] at hLt
    exact absurd ⟨data.L, data.L_maximal, hLt⟩ hnoV

/-- **Peterfalvi (12.10): `P₀ ⊆ L_F`.**  Since the witness type is `I` (`witness_L_type_eq_typeI`),
`L_s = mainSubgroup L I = L_F`, so `data.P0_le_Ls` (`P₀ ⊆ L_s`) gives `P₀ ⊆ L_F`. -/
theorem witness_P0_le_kernel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ctr.P0 ≤ maxNilpotentNormalHall data.L := by
  have hI := witness_L_type_eq_typeI hG hnoV data
  have hP0 := data.P0_le_Ls
  rw [hI] at hP0
  simpa [mainSubgroup] using hP0

/-- **A `q`-subgroup of a nilpotent subgroup `K` lies in `O_q(K) = opiCoreInG {q} K`** (the unique
Sylow `q`-subgroup of the nilpotent `K`).  Generalisation of `pGroup_le_opiCoreInG_fittingInG` from
`F(E)` to any nilpotent `K`; the proof uses only `IsNilpotent ↥K`. -/
theorem pGroup_le_opiCoreInG_of_le_of_isNilpotent [Finite G]
    {K : Subgroup G} [Group.IsNilpotent ↥K] {q : ℕ} [Fact q.Prime]
    {T : Subgroup G} (hT : IsPGroup q ↥T) (hTK : T ≤ K) :
    T ≤ opiCoreInG ({q} : Set ℕ) K := by
  classical
  have hHall := OddOrder.BG.Ch3.S10.oPiCore_isHall_of_isNilpotent (K := ↥K) ({q} : Set ℕ)
  have hTpi : Ch03.Subgroup.IsPiGroup ({q} : Set ℕ) (T.subgroupOf K) := by
    intro r hr
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv, hk] at hr
    have h2 := Nat.prime_of_mem_primeFactors hr
    have h3 := Nat.dvd_of_mem_primeFactors hr
    have hrq : r = q := (Nat.prime_dvd_prime_iff_eq h2 Fact.out).mp (h2.dvd_of_dvd_pow h3)
    simpa using hrq
  have h1 : T.subgroupOf K ≤ Ch03.oPiCore ({q} : Set ℕ) ↥K :=
    OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hHall hTpi
  calc T = (T.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hTK).symm
    _ ≤ (Ch03.oPiCore ({q} : Set ℕ) ↥K).map K.subtype := Subgroup.map_mono h1
    _ = opiCoreInG ({q} : Set ℕ) K := rfl

/-- **`N_G(L_F) = L` for the witness subgroup** (`TypeIData` form, Frobenius-free): `L` is maximal
(a coatom) and normalizes its Fitting kernel `H = L_F ≠ ⊥`; a strictly larger normalizer would be
`⊤` by maximality, making `H ≠ ⊥` normal in the simple `G` — impossible.  Shared by the (12.10)
TI-case exclusion (`witness_H_sharp_not_isTISubset_of_typeI`) and its Frobenius specialization. -/
theorem witness_normalizer_kernel_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (typeI : TypeIData data.L) :
    Subgroup.normalizer ((typeI.typeF.H : Subgroup G) : Set G) = data.L := by
  have hne : maxNilpotentNormalHall data.L ≠ ⊥ := by
    rw [← typeI.typeF.H_eq]; exact typeI.typeF.H_nontrivial
  rw [typeI.typeF.H_eq]
  exact (maximalSubgroup_eq_normalizer_maxNilpotentNormalHall hG data.L_maximal hne).symm

/-- **(12.10), TI-case exclusion for the witness** (`TypeIData` form, Frobenius-free): the
kernel-sharp set `H^#` of the witness `L` is **not** a TI-subset of `G`.  The rank-two witness
`x ∈ Ω₁(P₀)^# ⊆ H^#` (`witness_P0_le_kernel`) has `C_G(x) ⊄ L` (`data.centralizer_x_not_le_L`)
while `N_G(H) = L` (`witness_normalizer_kernel_eq`); picking `g ∈ C_G(x) ∖ L` gives
`g x g⁻¹ = x ∈ H^# ∩ (H^#)^g` with `g ∉ N_G(H)` — the TI failure.  Dispatches case (a) of the
(8.3) alternative in the (12.10) minimality argument. -/
theorem witness_H_sharp_not_isTISubset_of_typeI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (typeI : TypeIData data.L) :
    ¬ OddOrder.GroupTheory.IsTISubset
        (OddOrder.GroupTheory.sharpSubgroup typeI.typeF.H)
        (Subgroup.normalizer (typeI.typeF.H : Set G)) := by
  intro hTI
  have hNL := witness_normalizer_kernel_eq hG data typeI
  have hxH : data.x ∈ typeI.typeF.H := by
    rw [typeI.typeF.H_eq]
    exact witness_P0_le_kernel hG hnoV data data.x_mem_P0
  have hxsharp : data.x ∈ OddOrder.GroupTheory.sharpSubgroup typeI.typeF.H :=
    ⟨hxH, by simpa using data.x_ne_one⟩
  obtain ⟨g, hgC, hgL⟩ := SetLike.not_le_iff_exists.mp data.centralizer_x_not_le_L
  have hgc : g * data.x * g⁻¹ = data.x := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hgC
  exact hgL (hNL ▸ hTI g ⟨data.x, hxsharp, by rw [hgc]; exact hxsharp⟩)

/-- An **odd** prime `q` dividing `p² − 1` for an **odd** prime `p` satisfies `q < p`:
`q ∣ (p+1)(p−1)` splits as `q ∣ p−1` (so `q ≤ p−1 < p`) or `q ∣ p+1`; in the latter case
`q ≠ p+1` (`p+1` is even, `q` odd), so `q` is a proper divisor: `2q ≤ p+1 < 2p`.  The `q < p`
conclusion of the (8.3.b)/(8.3.c) prime comparison in Peterfalvi (12.10). -/
theorem prime_lt_of_odd_dvd_sq_sub_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp_odd : Odd p) (hq_odd : Odd q) (hdvd : q ∣ p ^ 2 - 1) : q < p := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd hp_odd (by decide)
    · exact h
  have hfac : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    rw [sq]; exact mul_self_tsub_one p
  rcases (Nat.Prime.dvd_mul hq).mp (hfac ▸ hdvd) with h | h
  · -- `q ∣ p + 1`: a proper (odd) divisor of the even `p + 1`, so `2q ≤ p + 1 < 2p`.
    have hne : q ≠ p + 1 := by
      intro heq
      obtain ⟨m, hm⟩ := hq_odd
      obtain ⟨l, hl⟩ := hp_odd
      omega
    obtain ⟨c, hc⟩ := h
    have hc2 : 2 ≤ c := by
      rcases Nat.lt_or_ge c 2 with h' | h'
      · interval_cases c
        · omega
        · exact absurd (by omega : q = p + 1) hne
      · exact h'
    have h2q : 2 * q ≤ p + 1 := by
      calc 2 * q ≤ c * q := Nat.mul_le_mul_right q hc2
        _ = q * c := mul_comm c q
        _ = p + 1 := hc.symm
    omega
  · -- `q ∣ p − 1 < p`.
    have := Nat.le_of_dvd (by omega) h
    omega

/-- **(12.10), case (8.3.b) counting core** (type-`F` general form): if the kernel `H` of a
type-`F` subgroup is **abelian of rank ≤ 2** with `p ∣ |H|`, then every prime `q` dividing `|U|`
divides `p² − 1`.

Peterfalvi's argument: `q ∣ |U|` gives an order-`q` element of `U` (Cauchy), so
`q ∣ exp U = exp U₀ ∣ |U₀|` (the `(8.1.c)`/`(8.2.a)` fields) and `U₀` has an element `u` of
order `q`.  `H U₀` is Frobenius with kernel `H` (`frobenius_HU0`), so the nontrivial cyclic
`⟨u⟩` (meeting `H` trivially) acts fixed-point-freely on the `⟨u⟩`-invariant subgroup
`Ω₁(H) ≠ ⊥`, whence `|Ω₁(H)| ≡ 1 (mod q)`
(`IsFrobeniusGroup.card_modEq_one_of_invariant_le_kernel_ambient`).  As `H` is abelian of rank
≤ 2, `|Ω₁(H)| = p^k` with `1 ≤ k ≤ 2`, so `q ∣ p^k − 1 ∣ p² − 1`. -/
theorem _root_.OddOrder.GroupTheory.TypeFData.prime_dvd_sq_sub_one_of_abelian_kernel
    [Finite G] {M : Subgroup G} (typeF : OddOrder.GroupTheory.TypeFData M)
    (hab : IsMulCommutative ↥typeF.H) (hrank : OddOrder.GroupTheory.rank ↥typeF.H ≤ 2)
    {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hpH : p ∣ Nat.card ↥typeF.H)
    (hqU : q ∣ Nat.card ↥typeF.U) :
    q ∣ p ^ 2 - 1 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fintype ↥typeF.U := Fintype.ofFinite _
  haveI : Fintype ↥typeF.U0 := Fintype.ofFinite _
  haveI : Fintype ↥typeF.H := Fintype.ofFinite _
  -- Abelian commutation witness for `Ω₁(H)`.
  have hcomm : ∀ x ∈ typeF.H, ∀ y ∈ typeF.H, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hab.is_comm.comm (⟨x, hx⟩ : ↥typeF.H) (⟨y, hy⟩ : ↥typeF.H))
  set Ω : Subgroup G := OddOrder.GroupTheory.omega1OfAbelian G typeF.H p hcomm with hΩdef
  -- An order-`q` element `u ∈ U₀` via `q ∣ exp U = exp U₀ ∣ |U₀|`.
  obtain ⟨u₁, hu₁⟩ := exists_prime_orderOf_dvd_card (G := ↥typeF.U) q
    (by rwa [← Nat.card_eq_fintype_card])
  have hqU0 : q ∣ Nat.card ↥typeF.U0 :=
    ((hu₁ ▸ Monoid.order_dvd_exponent u₁ : q ∣ Monoid.exponent ↥typeF.U).trans
      (typeF.exponent_eq ▸ dvd_refl _ : Monoid.exponent ↥typeF.U ∣ Monoid.exponent ↥typeF.U0)).trans
      Group.exponent_dvd_nat_card
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := ↥typeF.U0) q
    (by rwa [← Nat.card_eq_fintype_card])
  have hu_ord : orderOf ((u : G)) = q := by
    rw [← hu]
    exact orderOf_injective typeF.U0.subtype typeF.U0.subtype_injective u
  have hu_ne : (u : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu_ord
    exact hq.one_lt.ne' hu_ord.symm
  set A : Subgroup G := Subgroup.zpowers (u : G) with hAdef
  have hAcard : Nat.card ↥A = q := by rw [hAdef, Nat.card_zpowers, hu_ord]
  -- `Ω₁(H) ≠ ⊥`: an order-`p` element of `H` (Cauchy at `p ∣ |H|`) lies in it.
  have hΩne : Ω ≠ ⊥ := by
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := ↥typeF.H) p
      (by rwa [← Nat.card_eq_fintype_card])
    have hg_ord : orderOf (g : G) = p := by
      rw [← hg]
      exact orderOf_injective typeF.H.subtype typeF.H.subtype_injective g
    have hgΩ : (g : G) ∈ Ω := ⟨g.2, by rw [← hg_ord]; exact pow_orderOf_eq_one _⟩
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hgΩ
    rw [hgΩ, orderOf_one] at hg_ord
    exact (Fact.out : p.Prime).one_lt.ne' hg_ord.symm
  -- `u ∉ H` (complement disjointness), so the prime-order `A = ⟨u⟩` meets `H` trivially.
  have huH : (u : G) ∉ typeF.H := by
    intro huH
    have huU : (u : G) ∈ typeF.U := typeF.U0_le u.2
    have huM : (u : G) ∈ M := typeF.U_le huU
    have hmem : (⟨(u : G), huM⟩ : ↥M) ∈ typeF.H.subgroupOf M ⊓ typeF.U.subgroupOf M :=
      ⟨Subgroup.mem_subgroupOf.mpr huH, Subgroup.mem_subgroupOf.mpr huU⟩
    rw [typeF.complement.disjoint.eq_bot, Subgroup.mem_bot] at hmem
    exact hu_ne (congrArg Subtype.val hmem)
  have hAH : A ⊓ typeF.H = ⊥ := by
    have hdvd : Nat.card ↥(A ⊓ typeF.H) ∣ q := by
      rw [← hAcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | hqq
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : A ⊓ typeF.H = A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hAcard, hqq])
      exact huH ((heq.symm ▸ Subgroup.mem_zpowers (u : G) : (u : G) ∈ A ⊓ typeF.H)).2
  -- `⟨u⟩` normalizes `Ω₁(H)` (it normalizes `H = M_F ◁ M`).
  have hAnorm : A ≤ Subgroup.normalizer ((Ω : Subgroup G) : Set G) := by
    rw [hAdef, Subgroup.zpowers_le]
    refine OddOrder.GroupTheory.mem_normalizer_omega1OfAbelian ?_
    have huM : (u : G) ∈ M := typeF.U_le (typeF.U0_le u.2)
    have hMN : M ≤ Subgroup.normalizer ((typeF.H : Subgroup G) : Set G) := by
      rw [typeF.H_eq]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M
    exact hMN huM
  -- Frobenius counting: `|Ω₁(H)| ≡ 1 (mod q)`.
  have hmod :=
    OddOrder.GroupTheory.IsFrobeniusGroup.card_modEq_one_of_invariant_le_kernel_ambient
      (le_sup_left : typeF.H ≤ typeF.H ⊔ typeF.U0) ⟨_, typeF.frobenius_HU0⟩
      (OddOrder.GroupTheory.omega1OfAbelian_le) hΩne
      (by rw [hAdef, Subgroup.zpowers_le]; exact Subgroup.mem_sup_right u.2) hAH
      (by
        rw [hAdef]
        intro hbot
        exact hu_ne (by
          have := Subgroup.mem_zpowers (u : G)
          rwa [hbot, Subgroup.mem_bot] at this))
      hAnorm
  rw [hAcard] at hmod
  have hq_dvd : q ∣ Nat.card ↥Ω - 1 :=
    (Nat.modEq_iff_dvd' Nat.card_pos).mp hmod.symm
  -- `|Ω₁(H)| = p^k` with `1 ≤ k ≤ 2` (elementary abelian; rank bound).
  have hΩelem : OddOrder.GroupTheory.IsElementaryAbelian p ↥Ω :=
    OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
  obtain ⟨k, hΩcard⟩ : ∃ k, Nat.card ↥Ω = p ^ k := ⟨_, hΩelem.card_eq_pow_finrank⟩
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    exact hΩne (Subgroup.card_eq_one.mp (by rw [hΩcard, hk0, pow_zero]))
  have hk2 : k ≤ 2 := by
    have hsub_elem : (Ω.subgroupOf typeF.H).IsElementaryAbelian p :=
      OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe OddOrder.GroupTheory.omega1OfAbelian_le).symm hΩelem
    have hle := OddOrder.GroupTheory.le_pRank (Ω.subgroupOf typeF.H) hsub_elem
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        OddOrder.GroupTheory.omega1OfAbelian_le).toEquiv,
      hΩcard, Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
    calc k ≤ OddOrder.GroupTheory.pRank ↥typeF.H p := hle
      _ ≤ OddOrder.GroupTheory.rank ↥typeF.H := OddOrder.GroupTheory.pRank_le_rank p
      _ ≤ 2 := hrank
  -- `q ∣ p^k − 1 ∣ p² − 1`.
  have hdvd_pk : q ∣ p ^ k - 1 := by rw [← hΩcard]; exact hq_dvd
  have hfac : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    rw [sq]; exact mul_self_tsub_one p
  interval_cases k
  · exact hdvd_pk.trans (by rw [hfac, pow_one]; exact dvd_mul_left _ _)
  · exact hdvd_pk

/-- **Counterexample fact: `p ∤ |K|`.**  `K = M_F` is Hall in `M` while `p ∣ [M : M_F]`
(Hypothesis (12.8)), so `p` cannot also divide `|K|`. -/
theorem p_not_dvd_card_K [Finite G] (ctr : CounterexampleHypothesis (G := G)) :
    ¬ ctr.p ∣ Nat.card ↥ctr.K := by
  intro hdvd
  have hKleM : ctr.K ≤ ctr.M :=
    ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  have hcard : Nat.card ↥(ctr.K.subgroupOf ctr.M) = Nat.card ↥ctr.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleM).toEquiv
  have hcop : Nat.Coprime (Nat.card ↥ctr.K) (ctr.K.relIndex ctr.M) := by
    have h := (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall ctr.M).coprime_index
    rw [← ctr.K_eq_MF, hcard] at h
    rwa [Subgroup.relIndex]
  exact Nat.Prime.not_dvd_one ctr.p_prime (hcop ▸ Nat.dvd_gcd hdvd ctr.p_dvd_index)

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Peterfalvi (8.1.c) → (12.16) numeric input: `4·|K'| ≤ |K|`** (the `hidx` field of
`CounterexampleDadeData`).

The type-I structure of `M` supplies, via the (8.1.c) Frobenius group `H ⋊ U₀`
(`typeF.frobenius_HU0`) and `p ∣ [M : M_F] = |U|` with `exp U₀ = exp U`, an element `u ∈ U₀`
of order `p` acting fixed-point-freely on `K = M_F` by conjugation.  The FPF property descends
along the coprime quotient `K/K'` (Isaacs Cor 3.28, `coprime_fixedPoints_quotient`), so the
`p`-group `⟨u⟩` acts on `K/K'` with `1` as its only fixed point; orbit counting
(`IsPGroup.card_modEq_card_fixedPoints`) gives `|K/K'| ≡ 1 (mod p)`.  `K` is nilpotent and
nontrivial, hence not perfect, so `|K/K'| ≠ 1`, whence `|K/K'| ≥ p + 1 ≥ 4` (`p ≥ 3` odd) and
`|K| = |K/K'|·|K'| ≥ 4·|K'|`. -/
theorem four_mul_card_Kprime_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    4 * Nat.card ↥ctr.Kprime ≤ Nat.card ↥ctr.K := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  obtain ⟨tI⟩ := ctr.M_typeI
  have hHK : tI.typeF.H = ctr.K := tI.typeF.H_eq.trans ctr.K_eq_MF.symm
  -- `p ∣ |U|` (the type-I complement realizes `[M : M_F]`).
  have hpU : ctr.p ∣ Nat.card ↥tI.typeF.U := by
    have h1 : ctr.p ∣ (ctr.K.subgroupOf ctr.M).index := by
      have h := ctr.p_dvd_index
      rwa [Subgroup.relIndex] at h
    rw [← hHK, tI.typeF.complement.symm.index_eq_card] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tI.typeF.U_le).toEquiv] at h1
  -- An order-`p` element `u ∈ U₀` (Cauchy through `exp U₀ = exp U`).
  haveI : Fintype ↥tI.typeF.U := Fintype.ofFinite _
  obtain ⟨xU, hxU⟩ := exists_prime_orderOf_dvd_card (G := ↥tI.typeF.U) ctr.p
    (by rwa [Nat.card_eq_fintype_card] at hpU)
  have hpU0 : ctr.p ∣ Nat.card ↥tI.typeF.U0 := by
    haveI : Fintype ↥tI.typeF.U0 := Fintype.ofFinite _
    have hexp : Monoid.exponent ↥tI.typeF.U0 ∣ Nat.card ↥tI.typeF.U0 := by
      rw [Nat.card_eq_fintype_card]
      exact Group.exponent_dvd_card
    refine Dvd.dvd.trans ?_ hexp
    rw [tI.typeF.exponent_eq]
    exact hxU ▸ Monoid.order_dvd_exponent xU
  haveI : Fintype ↥tI.typeF.U0 := Fintype.ofFinite _
  obtain ⟨u0, hu0⟩ := exists_prime_orderOf_dvd_card (G := ↥tI.typeF.U0) ctr.p
    (by rwa [Nat.card_eq_fintype_card] at hpU0)
  set u : G := (u0 : G) with hu_def
  have huU0 : u ∈ tI.typeF.U0 := u0.2
  have hu_ord : orderOf u = ctr.p := by
    rw [← hu0]
    exact orderOf_injective tI.typeF.U0.subtype tI.typeF.U0.subtype_injective u0
  have hu_ne : u ≠ 1 := fun h =>
    ctr.p_prime.one_lt.ne' (by rw [← hu_ord, h, orderOf_one])
  -- `u` acts fixed-point-freely on `K` (ambient form of `frobenius_HU0.conj_frobenius`).
  have hfpf : ∀ n ∈ ctr.K, u * n * u⁻¹ = n → n = 1 := by
    intro n hnK hconj
    by_contra hn_ne
    have hnH : n ∈ tI.typeF.H := hHK ▸ hnK
    have huS : u ∈ tI.typeF.H ⊔ tI.typeF.U0 := Subgroup.mem_sup_right huU0
    have hnS : n ∈ tI.typeF.H ⊔ tI.typeF.U0 := Subgroup.mem_sup_left hnH
    exact tI.typeF.frobenius_HU0.conj_frobenius ⟨u, huS⟩
      (Subgroup.mem_subgroupOf.mpr huU0)
      (fun h => hu_ne (congrArg Subtype.val h)) ⟨n, hnS⟩
      (Subgroup.mem_subgroupOf.mpr hnH)
      (fun h => hn_ne (congrArg Subtype.val h)) (Subtype.ext hconj)
  -- The conjugation action of `⟨u⟩` on `K` and its descent to `K/K'`.
  have huM : u ∈ ctr.M := tI.typeF.U_le (tI.typeF.U0_le huU0)
  have hu_norm : u ∈ Subgroup.normalizer ctr.K := by
    have h := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer ctr.M
    exact ctr.K_eq_MF ▸ h huM
  have hAnorm : Subgroup.zpowers u ≤ Subgroup.normalizer ctr.K :=
    Subgroup.zpowers_le.mpr hu_norm
  set φ : ↥(Subgroup.zpowers u) →* MulAut ↥ctr.K :=
    (Subgroup.normalizerMonoidHom ctr.K).comp (Subgroup.inclusion hAnorm) with hφ
  have hN_inv : Ch03.IsAInvariant φ (commutator ↥ctr.K) :=
    Ch03.IsAInvariant.of_characteristic φ
  set ψ := quotientMulAutHom hN_inv with hψ
  letI : MulAction ↥(Subgroup.zpowers u) (↥ctr.K ⧸ commutator ↥ctr.K) :=
    MulAction.compHom _ ψ
  -- `p ∤ |K|`, so Isaacs 3.28 lifts quotient fixed points; FPF then leaves only `1`.
  have hCop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers u)) (Nat.card ↥ctr.K) := by
    rw [Nat.card_zpowers, hu_ord]
    exact ctr.p_prime.coprime_iff_not_dvd.mpr (p_not_dvd_card_K ctr)
  have hfix_eq : MulAction.fixedPoints ↥(Subgroup.zpowers u) (↥ctr.K ⧸ commutator ↥ctr.K)
      = {1} := by
    ext q
    simp only [Set.mem_singleton_iff, MulAction.mem_fixedPoints]
    constructor
    · intro hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator ↥ctr.K) q
      have hg_fix : ∀ a : ↥(Subgroup.zpowers u), ∃ n ∈ commutator ↥ctr.K, φ a g = g * n := by
        intro a
        have hb : ψ a (QuotientGroup.mk' (commutator ↥ctr.K) g)
            = QuotientGroup.mk' (commutator ↥ctr.K) g := hq a
        rw [hψ, quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply,
          QuotientGroup.mk'_apply, QuotientGroup.eq] at hb
        exact ⟨g⁻¹ * φ a g, by simpa using (commutator ↥ctr.K).inv_mem hb, by group⟩
      obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
        Ch04.coprime_fixedPoints_quotient hCop (Or.inl inferInstance) hN_inv hg_fix
      have hca : φ ⟨u, Subgroup.mem_zpowers u⟩ c = c := hc_fix ⟨u, Subgroup.mem_zpowers u⟩
      have hc1 : (c : G) = 1 := hfpf (c : G) c.2 (congrArg Subtype.val hca)
      have hg_mem : g ∈ commutator ↥ctr.K := by
        have hgc : g = c * n⁻¹ := by rw [hcn]; group
        rw [hgc, show c = (1 : ↥ctr.K) from Subtype.ext hc1, one_mul]
        exact (commutator ↥ctr.K).inv_mem hn
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hg_mem
    · rintro rfl
      intro a
      change ψ a 1 = 1
      exact map_one (ψ a)
  -- Orbit counting: `|K/K'| ≡ 1 (mod p)`.
  haveI : Fintype (↥ctr.K ⧸ commutator ↥ctr.K) := Fintype.ofFinite _
  haveI : Fintype (MulAction.fixedPoints ↥(Subgroup.zpowers u)
    (↥ctr.K ⧸ commutator ↥ctr.K)) := Fintype.ofFinite _
  have hApG : IsPGroup ctr.p ↥(Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu_ord, pow_one])
  have hmod := hApG.card_modEq_card_fixedPoints (↥ctr.K ⧸ commutator ↥ctr.K)
  have hfixcard : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers u)
      (↥ctr.K ⧸ commutator ↥ctr.K)) = 1 := by
    rw [Nat.card_congr (Equiv.setCongr hfix_eq)]
    exact Nat.card_unique
  have hQmod : Nat.card (↥ctr.K ⧸ commutator ↥ctr.K) % ctr.p = 1 % ctr.p := by
    have h2 := hmod
    rw [hfixcard] at h2
    exact h2
  -- `|K/K'| ≠ 1` (`K` is nilpotent and nontrivial, hence not perfect).
  have hQne1 : Nat.card (↥ctr.K ⧸ commutator ↥ctr.K) ≠ 1 := by
    intro h1
    haveI : Nontrivial ↥ctr.K :=
      (Subgroup.nontrivial_iff_ne_bot ctr.K).mpr (hHK ▸ tI.typeF.H_nontrivial)
    haveI : Group.IsNilpotent ↥ctr.K :=
      ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent ctr.M
    have hcomm_ne : commutator ↥ctr.K ≠ ⊤ :=
      (IsSolvable.commutator_lt_top_of_nontrivial ↥ctr.K).ne
    exact hcomm_ne (Subgroup.index_eq_one.mp h1)
  -- `p ≥ 3` (odd), so `|K/K'| ≥ p + 1 ≥ 4`.
  have hpG : ctr.p ∣ Nat.card G := by
    have h1 : ctr.p ∣ (ctr.K.subgroupOf ctr.M).index := by
      have := ctr.p_dvd_index
      rwa [Subgroup.relIndex] at this
    exact (h1.trans (Subgroup.index_dvd_card _)).trans
      (Subgroup.card_subgroup_dvd_card ctr.M)
  have hpodd : Odd ctr.p := hG.odd.of_dvd_nat hpG
  have hp3 : 3 ≤ ctr.p := by
    have h2 := ctr.p_prime.two_le
    have hne : ctr.p ≠ 2 := fun h => by
      rw [h] at hpodd
      exact (by decide : ¬ Odd 2) hpodd
    omega
  have hQ4 : 4 ≤ Nat.card (↥ctr.K ⧸ commutator ↥ctr.K) := by
    set c := Nat.card (↥ctr.K ⧸ commutator ↥ctr.K) with hc
    have h1p : (1 : ℕ) % ctr.p = 1 := Nat.mod_eq_of_lt (by omega)
    have hdm := Nat.div_add_mod c ctr.p
    rw [hQmod, h1p] at hdm
    have hq1 : 1 ≤ c / ctr.p := by
      rcases Nat.eq_zero_or_pos (c / ctr.p) with h0 | hpos
      · rw [h0, mul_zero, zero_add] at hdm
        exact absurd hdm.symm hQne1
      · exact hpos
    have hple : ctr.p ≤ ctr.p * (c / ctr.p) := Nat.le_mul_of_pos_right _ hq1
    obtain ⟨X, hX⟩ : ∃ X, ctr.p * (c / ctr.p) = X := ⟨_, rfl⟩
    rw [hX] at hdm hple
    omega
  -- `|K| = |K/K'|·|K'|`.
  have hKfact : Nat.card ↥ctr.K
      = Nat.card (↥ctr.K ⧸ commutator ↥ctr.K) * Nat.card ↥(commutator ↥ctr.K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hK'card : Nat.card ↥ctr.Kprime = Nat.card ↥(commutator ↥ctr.K) := by
    rw [ctr.Kprime_eq]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (commutator ↥ctr.K) ctr.K.subtype
      ctr.K.subtype_injective).toEquiv).symm
  calc 4 * Nat.card ↥ctr.Kprime
      = 4 * Nat.card ↥(commutator ↥ctr.K) := by rw [hK'card]
    _ ≤ Nat.card (↥ctr.K ⧸ commutator ↥ctr.K) * Nat.card ↥(commutator ↥ctr.K) :=
        Nat.mul_le_mul_right _ hQ4
    _ = Nat.card ↥ctr.K := hKfact.symm

end OddOrder.Peterfalvi.S14
