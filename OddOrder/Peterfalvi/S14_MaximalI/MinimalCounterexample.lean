import OddOrder.Peterfalvi.S14_MaximalI.FrobeniusStructure

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

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
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
    {Lt : PeterfalviType} (hLt : HasPeterfalviType Lt L) (hPL : ctr.P0 ≤ mainSubgroup L Lt)
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

/-- **Normalizer bridge** (used by (12.10) and (12.17)): a maximal subgroup `L` of a minimal
simple group of odd order is the normalizer of its maximal nilpotent normal Hall subgroup `L_F`,
as soon as `L_F ≠ ⊥`.

`L ≤ N_G(L_F)` is `maxNilpotentNormalHall_le_normalizer`.  If `N_G(L_F) = ⊤` then `L_F ⊴ G`, so by
simplicity `L_F = ⊥` or `⊤`; both are excluded (`L_F ≠ ⊥` by hypothesis, `L_F ≤ L < ⊤`).  Hence
`L ≤ N_G(L_F) < ⊤`, and `L` being a coatom upgrades the containment to equality. -/
theorem maximalSubgroup_eq_normalizer_maxNilpotentNormalHall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hne : maxNilpotentNormalHall L ≠ ⊥) :
    L = Subgroup.normalizer (maxNilpotentNormalHall L : Set G) := by
  have hco : IsCoatom L := hL
  have hLleN : L ≤ Subgroup.normalizer (maxNilpotentNormalHall L : Set G) :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer L
  refine le_antisymm hLleN ?_
  rcases hLleN.lt_or_eq with hlt | heq
  · -- `L < N_G(L_F)` would force `N_G(L_F) = ⊤`, making `L_F ⊴ G`, which simplicity excludes.
    exfalso
    have hNtop : Subgroup.normalizer (maxNilpotentNormalHall L : Set G) = ⊤ := hco.2 _ hlt
    haveI hHnormal : (maxNilpotentNormalHall L).Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases hG.simple.eq_bot_or_eq_top_of_normal (maxNilpotentNormalHall L) hHnormal with hb | ht
    · exact hne hb
    · have hle : maxNilpotentNormalHall L ≤ L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
      rw [ht] at hle
      exact hco.1 (top_le_iff.mp hle)
  · exact heq.ge

/-- **Peterfalvi (8.6.a) centralizer containment for type-`P` kernels**: for a maximal `L` of
type II–IV — i.e. carrying the `TypePNontrivialCore` of Definition (8.6), whose clause (a) makes
`L_F^#` a TI-subset with normalizer `N_G(L_F)` — every nonidentity `y ∈ L_F` has `C_G(y) ≤ L`.

An element `c ∈ C_G(y)` fixes `y ∈ L_F^# ∩ (L_F^#)^c`, so the TI property puts
`c ∈ N_G(L_F) = L` (`maximalSubgroup_eq_normalizer_maxNilpotentNormalHall`).  This is the (8.16)
proof's "`(8.6.a)` implies `R(a) = 1`" mechanism, exposed as the containment the (12.10) type
exclusions consume.  (The textbook (8.6.a) states the TI property for the full Fitting subgroup
`F(L)^# ⊇ L_F^#`; the Lean `TypePNontrivialCore` carries the `L_F`-form, which is what we use.) -/
theorem typeP_core_centralizer_le_of_mem_fitting [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hL : L ∈ maximalSubgroups G)
    {data : TypePData L} (hcore : TypePNontrivialCore L data)
    {y : G} (hy : y ∈ maxNilpotentNormalHall L) (hy1 : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) ≤ L := by
  obtain ⟨-, -, hTI⟩ := hcore
  have hne : maxNilpotentNormalHall L ≠ ⊥ := by
    intro hb
    rw [hb] at hy
    exact hy1 (Subgroup.mem_bot.mp hy)
  have hNL := maximalSubgroup_eq_normalizer_maxNilpotentNormalHall hG hL hne
  intro c hc
  have hcy : c * y * c⁻¹ = y := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  have hysharp : y ∈ OddOrder.GroupTheory.sharpSubgroup (maxNilpotentNormalHall L) :=
    ⟨hy, by simpa using hy1⟩
  rw [hNL]
  exact hTI c ⟨y, hysharp, by rw [hcy]; exact hysharp⟩

/-- **Peterfalvi (8.16) centralizer-containment, Type II**: for a maximal subgroup `L` of
Type II, `C_G(y) ⊆ L` for every nonidentity `y ∈ L_s` (`L_s = L_F` for Type II).

This is the "By (8.16), `C_G(y) ⊆ L` for all `y ∈ A(L)`" step of (12.10), restricted to the
`A_1(L) = L_s^#` core the witness argument uses.  Peterfalvi's (8.16) proof reduces the `A_1(L)`
case to exactly clause (a) of Definition (8.6) — the kernel-sharp TI-set — which the Lean
`TypeIIData` carries in its `TypePNontrivialCore`; the containment is then
`typeP_core_centralizer_le_of_mem_fitting`. -/
theorem typeII_centralizer_le_of_mem_mainSubgroup [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hII : IsTypeII L) {y : G} (hy : y ∈ mainSubgroup L PeterfalviType.II) (hy1 : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) ≤ L := by
  obtain ⟨iiData⟩ := hII
  exact typeP_core_centralizer_le_of_mem_fitting hG hL iiData.common
    (by simpa [mainSubgroup] using hy) hy1

/-- **Peterfalvi (10.10)+(11.9.c)+(11.6)+(9.7.b) kernel reduction, Type III/IV** (pinned sorried
§9–§11 obligation, hub 9003 Cluster A): for a maximal subgroup `L` of Type III or IV, a noncyclic
`p`-group `P₀ ⊆ L_s` lies in the Fitting kernel `L_F`.

This is the second paragraph of (12.10) up to its final (8.6.a) step: by Theorem (10.10)
(`S12.no_typeV_maximal`, available — excludes Type V) and (11.9.c)
(`S13.final_typeIII_conclusions`, sorried) `L` is Type III with case (b) of (9.7); by (11.6)
(`C_U(H) = 1`) and (9.7.b) the complement `U` of `H = L_F` in `[L,L]` is **cyclic**.  Since
`L_F` is a normal Hall subgroup of `L_s = [L,L]` with cyclic complement, a noncyclic `p`-group
`P₀ ≤ L_s` cannot embed in the complement side (`p ∣ |U|` would make `P₀ ↪ L_s/L_F ≅ U` cyclic),
so `p ∣ |L_F|` and `P₀` lies in the Sylow `p`-subgroup of the normal Hall `L_F`, i.e. `P₀ ⊆ L_F`.
**Genuinely still-missing**: the (9.7.b)/(11.6) cyclicity of `U` (`S13.final_typeIII_conclusions`
is sorried) and the Hall-embedding bookkeeping are not assembled in reach of S14. -/
theorem typeIIIorIV_noncyclic_le_fitting [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L P0 : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hIIIIV : IsTypeIII L ∨ IsTypeIV L) (hP0nc : ¬ IsCyclic ↥P0)
    {Lt : PeterfalviType} (hLhasType : HasPeterfalviType Lt L)
    (hP0 : P0 ≤ mainSubgroup L Lt) :
    P0 ≤ maxNilpotentNormalHall L := by
  sorry

/-- **Peterfalvi (10.10)+(11.9.c)+(11.6)+(9.7.b)+(8.6.a), Type III/IV route**: for a maximal
subgroup `L` of Type III or IV and a noncyclic `p`-group `P₀ ⊆ L_s`, `C_G(y) ⊆ L` for every
nonidentity `y ∈ P₀`.

**Assembly** (`sorry`-free modulo the (11.9.c)/(9.7.b) kernel reduction): the reduction
`typeIIIorIV_noncyclic_le_fitting` places `P₀ ⊆ L_F`, and the (8.6.a) TI containment
`typeP_core_centralizer_le_of_mem_fitting` (via the `TypePNontrivialCore` carried by both the
`TypeIIIData` and `TypeIVData` witnesses) yields `C_G(y) ≤ L` for `y ∈ L_F^#`. -/
theorem typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L P0 : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hIIIIV : IsTypeIII L ∨ IsTypeIV L) (hP0nc : ¬ IsCyclic ↥P0)
    {Lt : PeterfalviType} (hLhasType : HasPeterfalviType Lt L)
    (hP0 : P0 ≤ mainSubgroup L Lt) {y : G} (hy : y ∈ P0) (hy1 : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) ≤ L := by
  have hyF : y ∈ maxNilpotentNormalHall L :=
    typeIIIorIV_noncyclic_le_fitting hG hL hIIIIV hP0nc hLhasType hP0 hy
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

* **Type V** is excluded outright by Theorem (10.10) (`S12.no_typeV_maximal`).
* **Type II**: (8.16) gives `C_G(x) ⊆ L` for `x ∈ (L_s)^# = A_1(L)`
  (`typeII_centralizer_le_of_mem_mainSubgroup`), contradiction.
* **Types III/IV**: via (10.10)+(11.9.c)+(11.6)+(9.7.b), `P₀ ⊆ L_F`, and (8.6.a) gives
  `C_G(x) ⊆ L` for `x ∈ L_F^#` (`typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup`),
  contradiction.

The two §8–§11 centralizer-containment facts are pinned sorried above (genuinely missing as usable
containments — the upstream (8.16)/(8.6.a)/(11.9.c) results are themselves sorried or overstated);
the case analysis, the Type-V exclusion (cited, real), and the contradiction assembly here are
honest. -/
theorem witness_L_isTypeI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
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
      (Or.inl hLt) ctr.P0_noncyclic data.L_hasType data.P0_le_Ls data.x_mem_P0 data.x_ne_one) hEsc
  | IV =>
    rw [hLtype] at hLt
    exact absurd (typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup hG data.L_maximal
      (Or.inr hLt) ctr.P0_noncyclic data.L_hasType data.P0_le_Ls data.x_mem_P0 data.x_ne_one) hEsc
  | V =>
    rw [hLtype] at hLt
    exact absurd ⟨data.L, data.L_maximal, hLt⟩ (OddOrder.Peterfalvi.S12.no_typeV_maximal hG)

/-- **Peterfalvi (12.9)/(12.10): the witness type is exactly `I`.**  The recorded type `data.L_type`
of the witness `L` is forced to be `I`: every other type contradicts the escape condition
`C_G(x) ⊄ L` (`data.centralizer_x_not_le_L`) via the type-II/III/IV centralizer-containment lemmas
(and type `V` is excluded outright).  Same case-split as `witness_L_isTypeI`, but concluding the
identity `data.L_type = I` needed to compute `L_s = L_F`. -/
theorem witness_L_type_eq_typeI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
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
      (Or.inl hLt) ctr.P0_noncyclic data.L_hasType data.P0_le_Ls data.x_mem_P0 data.x_ne_one) hEsc
  | IV =>
    rw [hLtype] at hLt
    exact absurd (typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup hG data.L_maximal
      (Or.inr hLt) ctr.P0_noncyclic data.L_hasType data.P0_le_Ls data.x_mem_P0 data.x_ne_one) hEsc
  | V =>
    rw [hLtype] at hLt
    exact absurd ⟨data.L, data.L_maximal, hLt⟩ (OddOrder.Peterfalvi.S12.no_typeV_maximal hG)

/-- **Peterfalvi (12.10): `P₀ ⊆ L_F`.**  Since the witness type is `I` (`witness_L_type_eq_typeI`),
`L_s = mainSubgroup L I = L_F`, so `data.P0_le_Ls` (`P₀ ⊆ L_s`) gives `P₀ ⊆ L_F`. -/
theorem witness_P0_le_kernel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ctr.P0 ≤ maxNilpotentNormalHall data.L := by
  have hI := witness_L_type_eq_typeI hG data
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
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (typeI : TypeIData data.L) :
    ¬ OddOrder.GroupTheory.IsTISubset
        (OddOrder.GroupTheory.sharpSubgroup typeI.typeF.H)
        (Subgroup.normalizer (typeI.typeF.H : Set G)) := by
  intro hTI
  have hNL := witness_normalizer_kernel_eq hG data typeI
  have hxH : data.x ∈ typeI.typeF.H := by
    rw [typeI.typeF.H_eq]
    exact witness_P0_le_kernel hG data data.x_mem_P0
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

/-- **Peterfalvi (12.10) obligation B, minimality core** (pinned sorried §8/(12.8) obligation, hub
9003 Cluster A): for the type-I witness `L` of (12.9), every Sylow `q`-subgroup of `L` at a prime
`q` dividing `|U|` (`U =` the complement of `H = L_F`) is **cyclic**.

Peterfalvi's argument: a prime `q ∣ |L/H|` has `q < p` — in case (8.3.c) `q ∣ p−1`; in case
(8.3.b) a Sylow `p`-subgroup `P` of `H` is of rank `2` and (8.1.c) yields an order-`q` element of
`L` acting fixed-point-freely on `Ω₁(P)`, so `q ∣ p²−1`, hence `q ∣ p−1` or `q ∣ p+1`, giving
`q < p`.  By the minimality of `p` in (12.8) (no type-I maximal has a noncyclic Sylow `q`-subgroup
of its `M/M_F` for `q < p`), a Sylow `q`-subgroup of `L` is cyclic.

**Assembly** (proven): case (a) of the (8.3) alternative is excluded by
`witness_H_sharp_not_isTISubset_of_typeI`; case (b) is the counting core
`TypeFData.prime_dvd_sq_sub_one_of_abelian_kernel` (`q ∣ p² − 1`) followed by
`prime_lt_of_odd_dvd_sq_sub_one` (`q < p`, using that `p`, `q` are odd); case (c) pairs the
exponent bound `exp U ∣ p − 1` at the prime `p ∣ |H|` with a Cauchy order-`q` element of `U`.
With `q < p`, a noncyclic Sylow `q`-subgroup `Q` of `L` would witness `InPi q` (its `L`-image has
full `q`-order, and `q ∣ [L : L_F] = |U|`), contradicting the (12.8) minimality `minimal_p`. -/
theorem witness_L_sylow_cyclic_of_dvd_complement [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (typeI : TypeIData data.L) {q : ℕ} (hq : q.Prime)
    (hqU : q ∣ Nat.card ↥typeI.typeF.U) (Q : Sylow q ↥data.L) :
    IsCyclic ↥(Q : Subgroup ↥data.L) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- `P₀ ≤ H`, so `p ∣ |H|`.
  have hP0H : ctr.P0 ≤ typeI.typeF.H := by
    rw [typeI.typeF.H_eq]; exact witness_P0_le_kernel hG data
  have hP0ne : ctr.P0 ≠ ⊥ := fun h => ctr.P0_noncyclic (h ▸ inferInstance)
  have hpH : ctr.p ∣ Nat.card ↥typeI.typeF.H := by
    obtain ⟨k, hk⟩ := ctr.P0_pGroup.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hP0ne (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
    exact (dvd_pow_self ctr.p hk0).trans (hk ▸ Subgroup.card_dvd_of_le hP0H)
  -- `p` and `q` are odd (divisors of the odd `|G|`).
  have hq_odd : Odd q :=
    hG.odd.of_dvd_nat (hqU.trans (Subgroup.card_subgroup_dvd_card _))
  have hp_odd : Odd ctr.p :=
    hG.odd.of_dvd_nat (hpH.trans (Subgroup.card_subgroup_dvd_card _))
  -- Step A: `q < p`, by the (8.3) alternative for the type-I witness `L`.
  have hqp : q < ctr.p := by
    rcases typeI.alternative with hTI | ⟨hab, hrank⟩ | ⟨hexp, _⟩
    · exact absurd hTI (witness_H_sharp_not_isTISubset_of_typeI hG data typeI)
    · exact prime_lt_of_odd_dvd_sq_sub_one ctr.p_prime hq hp_odd hq_odd
        (typeI.typeF.prime_dvd_sq_sub_one_of_abelian_kernel hab hrank.le hq hpH hqU)
    · have hpmem : ctr.p ∈ (Nat.card ↥typeI.typeF.H).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hpH, Nat.card_pos.ne'⟩
      haveI : Fintype ↥typeI.typeF.U := Fintype.ofFinite _
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := ↥typeI.typeF.U) q
        (by rwa [← Nat.card_eq_fintype_card])
      have hqp1 : q ∣ ctr.p - 1 :=
        (hu ▸ Monoid.order_dvd_exponent u).trans (hexp ctr.p ctr.p_prime hpmem)
      have hp2 := ctr.p_prime.two_le
      have := Nat.le_of_dvd (by omega) hqp1
      omega
  -- Step B: minimality of `p` (12.8) — a noncyclic Sylow `q` of `L` would put `q ∈ π`.
  by_contra hnc
  refine absurd (ctr.minimal_p q hq ⟨data.L, data.L_maximal, ⟨typeI⟩,
    (Q : Subgroup ↥data.L).map data.L.subtype, Subgroup.map_subtype_le _,
    Q.2.map data.L.subtype, ?_, ?_, ?_⟩) (not_le.mpr hqp)
  · -- The image has full `q`-order in `L`: `¬ q ∣ [L : Q]`.
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective data.L.subtype_injective]
    exact Q.not_dvd_index
  · -- Noncyclicity transfers along `Q ≅ Q.map L.subtype`.
    intro hc
    haveI := hc
    exact hnc (isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥data.L) data.L.subtype
        data.L.subtype_injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥data.L) data.L.subtype
        data.L.subtype_injective).symm.surjective)
  · -- `q ∣ [L : L_F] = |U|`.
    rw [← typeI.typeF.H_eq, Subgroup.relIndex, typeI.typeF.complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe typeI.typeF.U_le).toEquiv]
    exact hqU

/-- **Peterfalvi (12.10) obligation B**: the type-I witness `L`'s complement `U` is a Z-group.

**Assembly** (`sorry`-free modulo the (8.3)/(8.1.c)/(12.8) minimality core): to show every Sylow
`q`-subgroup `P` of `U` is cyclic, distinguish `q ∣ |U|` from `q ∤ |U|`.  If `q ∤ |U|` then `P` is
trivial (its order is a `q`-power dividing `|U|`, forcing order `1`), hence cyclic.  If `q ∣ |U|`,
embed `U ↪ L` (via `U_le`): `P` becomes a `q`-subgroup of `L`, contained in a Sylow `q`-subgroup `Q`
of `L`, which is cyclic by the minimality core `witness_L_sylow_cyclic_of_dvd_complement`; a subgroup
of a cyclic group is cyclic, so `P` is cyclic. -/
theorem witness_L_complement_isZGroup [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (typeI : TypeIData data.L) :
    _root_.IsZGroup ↥typeI.typeF.U := by
  classical
  rw [isZGroup_iff]
  intro q hq P
  haveI : Fact q.Prime := ⟨hq⟩
  by_cases hqU : q ∣ Nat.card ↥typeI.typeF.U
  · -- `q ∣ |U|`: embed `P` into `L`, contain it in a cyclic Sylow `q`-subgroup of `L`.
    -- `P`, pushed along `U ↪ L`, is a `q`-subgroup of `L`.
    have hincl : Function.Injective (Subgroup.inclusion typeI.typeF.U_le) :=
      Subgroup.inclusion_injective _
    set PL : Subgroup ↥data.L :=
      (P : Subgroup ↥typeI.typeF.U).map (Subgroup.inclusion typeI.typeF.U_le) with hPL
    have hPLpg : IsPGroup q ↥PL :=
      (P.2.map (Subgroup.inclusion typeI.typeF.U_le))
    obtain ⟨Q, hQle⟩ := hPLpg.exists_le_sylow
    -- The containing Sylow `q`-subgroup of `L` is cyclic (minimality core).
    haveI hQcyc : IsCyclic ↥(Q : Subgroup ↥data.L) :=
      witness_L_sylow_cyclic_of_dvd_complement hG data typeI hq hqU Q
    -- A subgroup of a cyclic group is cyclic; `PL ≤ Q ≅ P`.
    haveI : IsCyclic ↥PL := Subgroup.isCyclic_of_le hQle
    exact isCyclic_of_surjective _
      (Subgroup.equivMapOfInjective (P : Subgroup ↥typeI.typeF.U)
        (Subgroup.inclusion typeI.typeF.U_le) hincl).symm.surjective
  · -- `q ∤ |U|`: the Sylow `q`-subgroup is trivial, hence cyclic.
    have hcard : Nat.card ↥(P : Subgroup ↥typeI.typeF.U) ∣ Nat.card ↥typeI.typeF.U :=
      (P : Subgroup ↥typeI.typeF.U).card_subgroup_dvd_card
    obtain ⟨k, hk⟩ := P.2.exists_card_eq
    have hqk : q ^ k ∣ Nat.card ↥typeI.typeF.U := hk ▸ hcard
    have hk0 : k = 0 := by
      by_contra hk0
      exact hqU ((dvd_pow_self q hk0).trans hqk)
    have hcard1 : Nat.card ↥(P : Subgroup ↥typeI.typeF.U) = 1 := by rw [hk, hk0, pow_zero]
    haveI : Subsingleton ↥(P : Subgroup ↥typeI.typeF.U) :=
      (Finite.card_le_one_iff_subsingleton).mp (by omega)
    infer_instance

/-- **Peterfalvi (12.10)**: the maximal subgroup `L` supplied by (12.9) is Frobenius with kernel
`L_F`.  **Assembly** (`sorry`-free modulo the two (12.10) obligations): `L` is Type I
(`witness_L_isTypeI`) and its complement `U` is a Z-group (`witness_L_complement_isZGroup`), so the
(8.2.b) bridge `typeI_frobenius_of_isZGroup_complement` yields the Frobenius structure with kernel
`H = L_F` (`typeF.H_eq`). -/
theorem witness_L_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ frob : TypeIFrobeniusData data.L, frob.kernel_eq_MF := by
  obtain ⟨typeI⟩ := witness_L_isTypeI hG data
  exact ⟨{ typeI := typeI
           complement := typeI.typeF.U.subgroupOf data.L
           kernel_eq_MF := typeI.typeF.H = maxNilpotentNormalHall data.L
           kernel_eq_MF_holds := typeI.typeF.H_eq
           frobenius := typeI_frobenius_of_isZGroup_complement typeI
             (witness_L_complement_isZGroup hG data typeI) },
         typeI.typeF.H_eq⟩

/-- The type-`τ` **main subgroup** `M_s` is contained in `M` (both `M_F` and `[M,M]` are). -/
theorem mainSubgroup_le (M : Subgroup G) (tau : OddOrder.GroupTheory.PeterfalviType) :
    OddOrder.GroupTheory.mainSubgroup M tau ≤ M := by
  cases tau <;>
    simp only [OddOrder.GroupTheory.mainSubgroup, OddOrder.GroupTheory.derivedInG] <;>
    first
      | exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le M
      | exact Subgroup.map_subtype_le _

/-- **Peterfalvi (12.11), first assertion**: `M ∩ L` complements `K = M_F` in `M`.  This is the
"first assertion follows from (12.9) and (8.13.c1)" step, with the (8.13)/BG roles swapped from
the (12.11) notation: the witness `x ∈ Ω₁(P₀)^# ⊆ L_F = L_σ` (type I) is a `σ`-sharp element of
`L` **escaping `L`** (`C_G(x) ⊄ L`), and its supporting maximal is `M` (`C_G(x) ≤ N_G(⟨x⟩) ≤ M`
pins `M` in the singleton `𝓜(C_G(x))`).

**Assembly** (proven): BG Theorem D(4) tail — "`M ∩ N` is a complement of `N_σ` in `N`" — is the
`IsComplement'` conjunct of `signalizer_structure_of_mem_sigmaSharp` (its unique `N` is `M` by the
singleton), applied at `M' := L ∈ 𝓜_σ(x)`; `N_σ = M_σ = M_F = K` is the type-I identification
`MF_eq_Msigma`. -/
theorem intersection_complements_K [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Subgroup.IsComplement' (ctr.K.subgroupOf ctr.M) ((ctr.M ⊓ data.L).subgroupOf ctr.M) := by
  classical
  -- The witness `L` is type I with `L_F = L_σ`, so `x ∈ P₀ ⊆ L_F` is `σ`-sharp in `L`.
  have hLtypeI : IsTypeI data.L := witness_L_isTypeI hG data
  have hLF_eq : maxNilpotentNormalHall data.L = OddOrder.BG.Ch3.S10.Msigma data.L :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG data.L_maximal).2.2.2.2.2.mpr
      (Or.inl hLtypeI)
  have hxLσ : data.x ∈ OddOrder.BG.Ch3.S10.Msigma data.L :=
    hLF_eq ▸ witness_P0_le_kernel hG data data.x_mem_P0
  have hxσ : data.x ∈ OddOrder.BG.Ch4.S14.sigmaSharp data.L :=
    ⟨hxLσ, by simpa using data.x_ne_one⟩
  -- `C_G(x) ≤ M` (via `N_G(⟨x⟩) ≤ M`), so `M` is THE maximal subgroup over `C_G(x)`.
  have hCM : Subgroup.centralizer ({data.x} : Set G) ≤ ctr.M := by
    refine le_trans ?_ data.normalizer_closure_x_le_M
    rw [← Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le_normalizer _
  obtain ⟨N₀, hN₀⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG data.L_maximal hxσ data.centralizer_x_not_le_L
  have hMN₀ : ctr.M = N₀ := by
    have hMin : ctr.M ∈ maximalSubgroupsContaining
        (Subgroup.centralizer ({data.x} : Set G)) := ⟨ctr.M_maximal, hCM⟩
    rw [hN₀] at hMin
    exact hMin
  -- The signalizer structure at the escaping `σ`-sharp `x`; its unique `N` is `M`.
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement data.x).ncard := by
    by_contra h
    push Not at h
    exact data.centralizer_x_not_le_L
      (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG data.L_maximal hxLσ
        data.x_ne_one h)
  obtain ⟨N, ⟨hNmax, hCN, -, -, -, -, hforall⟩, -⟩ :=
    OddOrder.BG.Ch4.S16.signalizer_structure_of_mem_sigmaSharp hG data.L_maximal hxσ hgt
  have hNM : N = ctr.M := by
    have hNin : N ∈ maximalSubgroupsContaining
        (Subgroup.centralizer ({data.x} : Set G)) := ⟨hNmax, hCN⟩
    rw [hN₀] at hNin
    rw [hNin, ← hMN₀]
  -- `L ∈ 𝓜_σ(x)`: apply the Theorem D(4) complement conjunct at `M' = L`.
  have hLin : data.L ∈ OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement data.x :=
    ⟨data.L_maximal, hxLσ⟩
  obtain ⟨-, -, hcompl, -⟩ := hforall data.L hLin
  rw [hNM, ← MF_eq_Msigma hG ctr,
    show data.L ⊓ ctr.M = ctr.M ⊓ data.L from inf_comm .. ] at hcompl
  exact hcompl

/-- **`|M ∩ L|` is coprime to `|K|`** (from the first assertion (12.11) + `M_F` Hall).  `M ∩ L`
complements `K = M_F` in `M` (`intersection_complements_K`), so `|M ∩ L| = [M : K]`, which is
coprime to `|K|` because `K = M_F` is a Hall subgroup of `M`. -/
theorem card_MinfL_coprime_card_K [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Nat.Coprime (Nat.card ↥(ctr.M ⊓ data.L)) (Nat.card ↥ctr.K) := by
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  have hcompl := intersection_complements_K hG data
  have hHall := (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall ctr.M).coprime_index
  rw [← ctr.K_eq_MF] at hHall
  -- `hHall : Coprime |K| [M : K]`;  `[M : K] = |M ∩ L|` by the complement.
  have hidx : (ctr.K.subgroupOf ctr.M).index = Nat.card ↥((ctr.M ⊓ data.L).subgroupOf ctr.M) :=
    hcompl.symm.index_eq_card
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hHall
  exact hHall.symm

/-- **Peterfalvi (12.11), core of the second assertion**: a subgroup `A ≤ M ∩ L` meeting the
witness kernel `H = L_F` trivially (`A ⊓ H = ⊥`, i.e. of order prime to `|H|`) is trivial.

The genuine (12.11) argument, now fully assembled from the landed infrastructure.  Put
`P = O_p(H) ∩ M` (an `A`-invariant `p`-subgroup of `H` containing `P₀`, via the nilpotent core
`opiCoreInG`); then:
* `P` does not centralize `K` (`P₀_not_le_centralizer_K`, `P₀ ≤ P`);
* `P ⊔ A` is Frobenius with kernel `P` (from `L`'s Frobenius structure), acts coprimely on `K`
  (`P ⊔ A ≤ M ∩ L`, coprime to `|K|`), so by Wielandt (9.1)
  `exists_ne_one_centralized_by_complement_of_kernel_not_centralizes` gives `C_K(A) ≠ 1`;
* `C_K(x) ≠ 1` by (12.9) (`ctr.CKx_not_le_Kprime`);
* since `M ∩ L` complements `K` in `M` (first assertion), `A` and `x` land in a common abelian
  subgroup `W` (`exists_abelian_centralizer_le_of_isComplement` with `V = M ∩ L`), so `A`
  centralizes `x`;
* by `L`'s Frobenius condition (4) (`centralizer_kernel_le`, `x ∈ H^#`), `A ≤ C_L(x) ⊆ H`, so
  `A ⊆ H`, forcing `A = A ⊓ H = ⊥`. -/
theorem witness_MinfL_pprime_subgroup_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) {A : Subgroup G}
    (hAML : A ≤ ctr.M ⊓ data.L) (hAH : A ⊓ maxNilpotentNormalHall data.L = ⊥) (hAne : A ≠ ⊥) :
    False := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  set H : Subgroup G := maxNilpotentNormalHall data.L with hHdef
  have hAM : A ≤ ctr.M := hAML.trans inf_le_left
  have hAL : A ≤ data.L := hAML.trans inf_le_right
  haveI hHnilp : Group.IsNilpotent ↥H := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent data.L
  have hHL : H ≤ data.L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le data.L
  have hHnorm : data.L ≤ Subgroup.normalizer (H : Set G) :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer data.L
  -- Frobenius structure of `L` with kernel `H` (upstream of this theorem).
  obtain ⟨frob, _⟩ := witness_L_frobenius hG data
  have hHfrob : frob.typeI.typeF.H = H := frob.typeI.typeF.H_eq
  have hFrobL : ∃ C : Subgroup ↥data.L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥data.L (H.subgroupOf data.L) C :=
    ⟨frob.complement, hHfrob ▸ frob.frobenius⟩
  -- `x ∈ H^#` and `x ∈ M ∩ L`.
  have hxH : data.x ∈ H := witness_P0_le_kernel hG data data.x_mem_P0
  have hxML : data.x ∈ ctr.M ⊓ data.L := ⟨ctr.P0_le_M data.x_mem_P0, hHL hxH⟩
  -- `P = O_p(H) ∩ M` contains `P₀`, sits inside `H` and `M`.
  set P : Subgroup G := opiCoreInG ({ctr.p} : Set ℕ) H ⊓ ctr.M with hPdef
  have hP0_le_P : ctr.P0 ≤ P :=
    le_inf (pGroup_le_opiCoreInG_of_le_of_isNilpotent ctr.P0_pGroup (witness_P0_le_kernel hG data))
      ctr.P0_le_M
  have hP_le_H : P ≤ H := inf_le_left.trans (opiCoreInG_le _ _)
  have hP_le_M : P ≤ ctr.M := inf_le_right
  have hP0ne : ctr.P0 ≠ ⊥ := fun hb => ctr.P0_noncyclic (hb ▸ isCyclic_of_subsingleton)
  have hPne : P ≠ ⊥ := fun hb => hP0ne (le_bot_iff.mp (hb ▸ hP0_le_P))
  -- `A` normalises `P` (normalises `O_p(H)` and `M`).
  have hAnorm_opi : A ≤ Subgroup.normalizer (opiCoreInG ({ctr.p} : Set ℕ) H) :=
    le_normalizer_opiCoreInG_of_le_normalizer _ (hAL.trans hHnorm)
  have hAnorm_M : A ≤ Subgroup.normalizer (ctr.M : Set G) := hAM.trans Subgroup.le_normalizer
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hOpi := (Subgroup.mem_normalizer_iff.mp (hAnorm_opi ha)) y
    have hM := (Subgroup.mem_normalizer_iff.mp (hAnorm_M ha)) y
    simp only [hPdef, Subgroup.mem_inf]
    rw [hOpi, hM]
  -- `P ⊔ A ≤ N_G(K)` and `≤ M ∩ L`.
  have hMnorm_K : ctr.M ≤ Subgroup.normalizer (ctr.K : Set G) :=
    ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer ctr.M
  have hPAK : P ⊔ A ≤ Subgroup.normalizer (ctr.K : Set G) :=
    sup_le (hP_le_M.trans hMnorm_K) (hAM.trans hMnorm_K)
  have hPA_ML : P ⊔ A ≤ ctr.M ⊓ data.L :=
    sup_le (le_inf hP_le_M (hP_le_H.trans hHL)) hAML
  -- `K` is solvable (subgroup of the solvable maximal `M`).
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  haveI hMsolv : IsSolvable ↥ctr.M := hG.solvable_of_mem_maximalSubgroups ctr.M_maximal
  haveI hKsolv : IsSolvable ↥ctr.K :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hKM)
  -- Coprimality of the `P ⊔ A`-action on `K`.
  have hcop : Nat.Coprime (Nat.card ↥ctr.K) (Nat.card ↥(P ⊔ A)) :=
    (card_MinfL_coprime_card_K hG data).symm.coprime_dvd_right (Subgroup.card_dvd_of_le hPA_ML)
  -- `P` does not centralize `K`.
  have hPnc : ¬ P ≤ Subgroup.centralizer (ctr.K : Set G) := fun hPc =>
    P0_not_le_centralizer_K hG ctr (hP0_le_P.trans hPc)
  -- **`C_K(A) ≠ 1`** (Wielandt (9.1) via the sub-Frobenius engine).
  obtain ⟨n, hnK, hn1, hnA⟩ := exists_ne_one_centralized_by_complement_of_kernel_not_centralizes
    hHL hFrobL hP_le_H hPne hAL hAH hAne hAP hPAK hKsolv hcop hPnc
  -- **`C_K(x) ≠ 1`** (Peterfalvi (12.9)).
  obtain ⟨n', hn'mem, hn'K'⟩ := SetLike.not_le_iff_exists.mp data.CKx_not_le_Kprime
  obtain ⟨hn'C, hn'K⟩ := Subgroup.mem_inf.mp hn'mem
  have hn'1 : n' ≠ 1 := fun h => hn'K' (by rw [h]; exact Subgroup.one_mem _)
  -- **`A` and `x` in a common abelian `W ≤ M ∩ L`** (step (8.1.b), `V = M ∩ L`).
  obtain ⟨typeIM⟩ := ctr.M_typeI
  have htypeFH : typeIM.typeF.H = ctr.K := ctr.K_eq_MF ▸ typeIM.typeF.H_eq
  obtain ⟨W, hWab, hWle⟩ := exists_abelian_centralizer_le_of_isComplement hMsolv typeIM.typeF
    (V := ctr.M ⊓ data.L) inf_le_left (htypeFH ▸ intersection_complements_K hG data)
  have hnFH : n ∈ typeIM.typeF.H := by rw [htypeFH]; exact hnK
  have hn'FH : n' ∈ typeIM.typeF.H := by rw [htypeFH]; exact hn'K
  have hA_W : A ≤ W := by
    intro a haA
    have haC : (a : G) ∈ Subgroup.centralizer ({n} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (hnA a haA))
    exact hWle n hnFH hn1 ⟨hAML haA, haC⟩
  have hx_W : data.x ∈ W := by
    have hxC : data.x ∈ Subgroup.centralizer ({n'} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hn'C).symm
    exact hWle n' hn'FH hn'1 ⟨hxML, hxC⟩
  -- **`A` centralizes `x`** (both in abelian `W`), then **`A ⊆ H`** by Frobenius condition (4).
  have hA_H : A ≤ H := by
    intro a haA
    have hax : (a : G) * data.x = data.x * a :=
      congrArg Subtype.val (hWab.is_comm.comm ⟨a, hA_W haA⟩ ⟨data.x, hx_W⟩)
    have hxHfrob : (⟨data.x, hHL hxH⟩ : ↥data.L) ∈ frob.typeI.typeF.H.subgroupOf data.L := by
      rw [Subgroup.mem_subgroupOf, hHfrob]; exact hxH
    have hx1 : (⟨data.x, hHL hxH⟩ : ↥data.L) ≠ 1 :=
      fun h => data.x_ne_one (by simpa using congrArg Subtype.val h)
    have hcent := frob.frobenius.centralizer_kernel_le _ hxHfrob hx1
    have haC : (⟨a, hAL haA⟩ : ↥data.L) ∈
        Subgroup.centralizer ({(⟨data.x, hHL hxH⟩ : ↥data.L)} : Set ↥data.L) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (by simpa using hax)
    have haH := hcent haC
    rw [Subgroup.mem_subgroupOf, hHfrob] at haH
    exact haH
  exact hAne (le_bot_iff.mp (hAH ▸ le_inf le_rfl hA_H))

/-- **Peterfalvi (12.11), second assertion**: `M ∩ L ⊆ H = L_F`.  `M ∩ L` has no nontrivial
subgroup meeting `H` trivially (`witness_MinfL_pprime_subgroup_eq_bot`), so its order is coprime to
`[L : H]` (any common prime would give a nontrivial Sylow subgroup meeting `H` trivially), and the
normal-Hall reduction `le_of_coprime_card_index_of_normal` places `M ∩ L` inside `H`. -/
theorem intersection_le_kernel [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ctr.M ⊓ data.L ≤ maxNilpotentNormalHall data.L := by
  classical
  set H : Subgroup G := maxNilpotentNormalHall data.L with hHdef
  have hHL : H ≤ data.L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le data.L
  have hMLL : ctr.M ⊓ data.L ≤ data.L := inf_le_right
  haveI hHnorm : (H.subgroupOf data.L).Normal :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal data.L
  -- `|M ∩ L|` is coprime to `[L : H]`.
  have hcop : Nat.Coprime (Nat.card ↥((ctr.M ⊓ data.L).subgroupOf data.L))
      (H.subgroupOf data.L).index := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMLL).toEquiv, Nat.coprime_iff_gcd_eq_one]
    by_contra hgcd
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hgcd
    haveI : Fact q.Prime := ⟨hq⟩
    rw [Nat.dvd_gcd_iff] at hqdvd
    obtain ⟨hqML, hqidx⟩ := hqdvd
    -- A Sylow `q`-subgroup `Q` of `M ∩ L` is nontrivial, meets `H` trivially, contradicts the core.
    obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow q ↥(ctr.M ⊓ data.L)))
    set A : Subgroup G := (Q : Subgroup ↥(ctr.M ⊓ data.L)).map (ctr.M ⊓ data.L).subtype with hAdef
    have hApg : IsPGroup q ↥A := Q.2.map _
    have hAML : A ≤ ctr.M ⊓ data.L := Subgroup.map_subtype_le _
    -- `q ∉ π(H)` (as `q ∣ [L : H]` and `H` is Hall in `L`), so `A ⊓ H = ⊥`.
    have hqH : ¬ q ∣ Nat.card ↥H := by
      have hHallL := (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall data.L).coprime_index
      intro hdvd
      have hdvd' : q ∣ Nat.card ↥(H.subgroupOf data.L) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]; exact hdvd
      have hg : q ∣ Nat.gcd (Nat.card ↥(H.subgroupOf data.L)) (H.subgroupOf data.L).index :=
        Nat.dvd_gcd hdvd' hqidx
      rw [hHallL] at hg
      exact hq.one_lt.ne' (Nat.dvd_one.mp hg)
    have hAH : A ⊓ H = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzA, hzH⟩ := Subgroup.mem_inf.mp hz
      rw [Subgroup.mem_bot]
      by_contra hzne
      apply hqH
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hApg) ⟨z, hzA⟩
      have hoz : orderOf z = q ^ k := by
        rw [← hk]; exact orderOf_injective A.subtype A.subtype_injective ⟨z, hzA⟩
      have hk0 : k ≠ 0 := fun h => hzne (orderOf_eq_one_iff.mp (by rw [hoz, h, pow_zero]))
      have hqoz : q ∣ Nat.card ↥(Subgroup.zpowers z) := by
        rw [Nat.card_zpowers, hoz]; exact dvd_pow_self q hk0
      exact hqoz.trans (Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).mpr hzH))
    have hAne : A ≠ ⊥ := by
      have hqQ : q ∣ Nat.card ↥(Q : Subgroup ↥(ctr.M ⊓ data.L)) := by
        have hmul := Subgroup.card_mul_index (Q : Subgroup ↥(ctr.M ⊓ data.L))
        rcases (Nat.Prime.dvd_mul hq).mp (hmul ▸ hqML) with h | h
        · exact h
        · exact absurd h Q.not_dvd_index
      intro hb
      have hA1 : Nat.card ↥A = Nat.card ↥(Q : Subgroup ↥(ctr.M ⊓ data.L)) :=
        (Nat.card_congr (Subgroup.equivMapOfInjective _ _
          (ctr.M ⊓ data.L).subtype_injective).toEquiv).symm
      rw [hb, Subgroup.card_bot] at hA1
      rw [← hA1] at hqQ
      exact hq.one_lt.ne' (Nat.dvd_one.mp hqQ)
    exact witness_MinfL_pprime_subgroup_eq_bot hG data hAML hAH hAne
  -- Apply the normal-Hall reduction.
  have hle := Subgroup.le_of_coprime_card_index_of_normal hcop
  intro z hz
  have : (⟨z, hMLL hz⟩ : ↥data.L) ∈ H.subgroupOf data.L :=
    hle (Subgroup.mem_subgroupOf.mpr hz)
  exact Subgroup.mem_subgroupOf.mp this

/-- **Peterfalvi (12.11)**: `M ∩ L` complements `K` in `M` and lies in the Fitting kernel
`H = L_F` of the witness subgroup `L`.

**Assembly**: the two textbook assertions of (12.11) are `intersection_complements_K` (from (12.9)
and (8.13.c1)) and `intersection_le_kernel` (the (8.1.b/c)+(9.1)+(12.10) `A = 1` argument),
combined here. -/
theorem intersection_complement_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Subgroup.IsComplement' (ctr.K.subgroupOf ctr.M) ((ctr.M ⊓ data.L).subgroupOf ctr.M) ∧
      ctr.M ⊓ data.L ≤ maxNilpotentNormalHall data.L :=
  ⟨intersection_complements_K hG data, intersection_le_kernel hG data⟩

/-- **Peterfalvi (12.10), non-TI clause**: for the (12.9) witness `L`, its Frobenius kernel
`H = L_F` has `H^#` **not** a TI-subset of `G`.  This is the "By (12.9), `H^#` is not a TI-subset"
step of (12.10): the rank-two witness `x ∈ Ω₁(P₀)^#` has `C_G(x) ⊄ L` (`data.centralizer_x_not_le_L`)
while `N_G(H) = L` (maximality of `L` + `H = L_F` normal); pick `g ∈ C_G(x) ∖ L`, then `g ∉ N_G(H)`
yet `g x g⁻¹ = x ∈ H^#`, witnessing the TI failure (`x ∈ H^# ∩ (H^#)^g`).

This is the honest (12.9)/(12.10) prerequisite of the *witness* coherence route: with it,
`witness_L_coherent` dispatches only through the (b)/(c) cases of (12.6) (which are `sorry`-free),
never the TI-only case (a) — so the witness coherence depends on this genuine (12.9) fact rather
than on the (8.18.c) geometry that case (a) (`sibleyTarget_frobI`) transitively needs.

Specialization of the `TypeIData`-form `witness_H_sharp_not_isTISubset_of_typeI` to the
Frobenius witness (whose `x ∈ H` route is the upstream `witness_P0_le_kernel`, not (12.11)). -/
theorem witness_H_sharp_not_isTISubset [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (frob : TypeIFrobeniusData data.L) :
    ¬ OddOrder.GroupTheory.IsTISubset
        (OddOrder.GroupTheory.sharpSubgroup frob.typeI.typeF.H)
        (Subgroup.normalizer (frob.typeI.typeF.H : Set G)) :=
  witness_H_sharp_not_isTISubset_of_typeI hG data frob.typeI

/-- **Peterfalvi (12.1) for the witness subgroup `L`, with its Frobenius witness**: the second
maximal subgroup `L` of (12.9) carries the (12.1) Hypothesis together with an explicit Frobenius
decomposition of its kernel `H = L_F`.  Since `L` is type I (Frobenius, by (12.10)
`witness_L_frobenius`), `hypothesis_of_typeIData` applied to the recovered `TypeIData` yields the
Hypothesis whose `typeI` is that very data, so the Frobenius group structure `frob.frobenius`
transfers to `hyp.H`.  This Frobenius witness is the structural input to coherence (12.6). -/
theorem witness_L_hypothesis_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ hyp : Hypothesis data.L, ∃ C : Subgroup ↥data.L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥data.L (hyp.H.subgroupOf data.L) C ∧
      ¬ OddOrder.GroupTheory.IsTISubset
          (OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H)
          (Subgroup.normalizer (hyp.typeI.typeF.H : Set G)) := by
  obtain ⟨frob, hker⟩ := witness_L_frobenius hG data
  obtain ⟨hyp, hhyp⟩ := hypothesis_of_typeIData hG data.L_maximal frob.typeI
  have hH : hyp.typeI.typeF.H = frob.typeI.typeF.H := by rw [hhyp]
  refine ⟨hyp, frob.complement, ?_, ?_⟩
  · rw [show hyp.H = hyp.typeI.typeF.H from rfl, hH]
    exact frob.frobenius
  · rw [hH]
    exact witness_H_sharp_not_isTISubset hG data frob

/-- **Peterfalvi (12.1) Hypothesis for the witness subgroup `L`** (forgetful form of
`witness_L_hypothesis_frobenius`). -/
theorem witness_L_hypothesis [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Nonempty (Hypothesis data.L) := by
  obtain ⟨hyp, _⟩ := witness_L_hypothesis_frobenius hG data
  exact ⟨hyp⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.6) for the witness subgroup `L`**: the type-I family `S` of `L` is coherent.
Combines the Hypothesis + Frobenius witness of `witness_L_hypothesis_frobenius` with the (12.6)
Frobenius-case coherence.  Crucially the witness dispatches only through the **(b)/(c)** cases
(both `sorry`-free): its `H^#` is *not* TI (Peterfalvi (12.10), `witness_H_sharp_not_isTISubset`),
so the TI-only case (a) `sibleyTarget_frobI` is excluded — hence this coherence never depends on the
(8.18.c) geometry that case (a) transitively needs, only on the genuine (12.9)/(12.10) witness facts.
This is the coherence input "`S` coherent" of the (12.16) Dade calculation — it feeds the `(7.8.b)`
norm bound `hB` of `CounterexampleDadeData` via the §7 `Hypothesis78`/`NormEstimates`. -/
theorem witness_L_coherent [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ hyp : Hypothesis data.L,
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  obtain ⟨hyp, C, hC, hNonTI⟩ := witness_L_hypothesis_frobenius hG data
  refine ⟨hyp, ?_⟩
  rcases hyp.typeI.alternative with hTI | hab | hexp
  · exact absurd hTI hNonTI
  · exact frobenius_typeI_coherent_of_abelianKernel hG hyp ⟨C, hC⟩ hab
  · exact frobenius_typeI_coherent_of_cyclicQuotient hG hyp ⟨C, hC⟩ hexp


/-- **(12.12) Case A core.**  A finite group `E` acting faithfully on a one-dimensional
`𝔽_p`-space `V` is cyclic, with `|E| ∣ |V| - 1 = p - 1`.  This is the reducible / rank-one case
of Peterfalvi (12.12): `End_{𝔽_p}(V) ≅ 𝔽_p` (every endomorphism of a line is a homothety), so
`E ↪ End(V)ˣ ≅ (ℤ/p)ˣ`, a cyclic group of order `p - 1`. -/
theorem isCyclic_and_card_dvd_of_faithful_one_dim
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V) (hfaith : Function.Injective ρ)
    (hdim : Module.finrank (ZMod p) V = 1) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card V - 1 := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hdim
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- `End_{𝔽_p}(V) ≅ 𝔽_p` via `algebraMap` (bijective in dimension one: every endo is `c • id`).
  have hsurj : Function.Surjective (algebraMap (ZMod p) (Module.End (ZMod p) V)) := by
    intro u
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim u
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc, Module.End.one_eq_id]⟩
  have hinj : Function.Injective (algebraMap (ZMod p) (Module.End (ZMod p) V)) :=
    (algebraMap (ZMod p) (Module.End (ZMod p) V)).injective
  let eRing : ZMod p ≃+* Module.End (ZMod p) V := RingEquiv.ofBijective _ ⟨hinj, hsurj⟩
  -- `E ↪ End(V)ˣ ≃ (ℤ/p)ˣ`.
  let φ : E →* (ZMod p)ˣ :=
    (Units.mapEquiv eRing.toMulEquiv).symm.toMonoidHom.comp (MonoidHom.toHomUnits ρ)
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply hfaith
    have h1 : (MonoidHom.toHomUnits ρ) a = (MonoidHom.toHomUnits ρ) b :=
      (Units.mapEquiv eRing.toMulEquiv).symm.injective (by simpa [φ] using hab)
    simpa using congrArg (Units.val) h1
  haveI : IsCyclic (ZMod p)ˣ := inferInstance
  haveI : IsCyclic φ.range := inferInstance
  have hcardV : Nat.card V = p := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), hdim, pow_one, Nat.card_eq_fintype_card,
      ZMod.card]
  refine ⟨isCyclic_of_surjective (MonoidHom.ofInjective hφinj).symm.toMonoidHom
      (MonoidHom.ofInjective hφinj).symm.surjective, ?_⟩
  rw [hcardV]
  calc Nat.card E = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    _ ∣ Nat.card (ZMod p)ˣ := Subgroup.card_subgroup_dvd_card _
    _ = p - 1 := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out)]

/-- **(12.12) irreducible-case core.**  An odd-order group `E` acting faithfully and
irreducibly on a two-dimensional `𝔽_p`-space `V` (with `p ∤ |E|`) is cyclic, with
`|E| ∣ |V| - 1 = p² - 1`.  This is the rank-two irreducible case of Peterfalvi (12.12):
BG Theorem 2.6(a) (`odd_two_dim_abelian`) abelianizes `E`, and the commutativity-free Singer
mechanism (`isCyclic_and_card_dvd_of_faithful_irreducible_comm`) then realizes `E` inside the
units of the Singer field `𝔽_p[E] ⧸ I ≅ 𝔽_{p²}`. -/
theorem isCyclic_and_card_dvd_of_odd_two_dim_irreducible
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V) (hfaith : Function.Injective ρ)
    (hirr : Representation.IsIrreducible ρ)
    (hdim : Module.finrank (ZMod p) V = 2) (hp_ndvd : ¬ p ∣ Nat.card E) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card V - 1 := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- BG 2.6(a): a faithful odd two-dimensional representation has abelian image.
  have hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card E → ¬ CharP (ZMod p) q := fun q _ hqdvd hcharq =>
    hp_ndvd ((CharP.eq (ZMod p) hcharq (ZMod.charP p)) ▸ hqdvd)
  have hcomm : ∀ a b : E, a * b = b * a :=
    (OddOrder.BG.Ch1.S02.odd_two_dim_abelian hodd hdim ρ hfaith hchar).comm
  -- Give `V` the `𝔽_p[E]`-module structure of the representation *directly* (this is
  -- definitionally `ρ.asModule`'s instance, but stated on `V` so that instance synthesis does
  -- not choke on the `ρ.asModule` notation — which it does once `IsIrreducible ρ` is around).
  letI : Module (MonoidAlgebra (ZMod p) E) V := Module.compHom V (ρ.asAlgebraHom).toRingHom
  have hsmul : ∀ (e : E) (x : V), MonoidAlgebra.of (ZMod p) E e • x = ρ e x := fun e x => by
    show (ρ.asAlgebraHom) (MonoidAlgebra.of (ZMod p) E e) x = ρ e x
    rw [Representation.asAlgebraHom_of]
  haveI : IsSimpleModule (MonoidAlgebra (ZMod p) E) V :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
  have hfaith' : ∀ e : E, (∀ x : V, MonoidAlgebra.of (ZMod p) E e • x = x) → e = 1 := by
    intro e he
    apply hfaith
    ext v
    rw [map_one, Module.End.one_apply, ← hsmul e v]
    exact he v
  exact isCyclic_and_card_dvd_of_faithful_irreducible_comm (M := V) hcomm hfaith'

/-- **(12.12) `p + 1` refinement, irreducible case.**  An odd-order group `E` (`p ∤ |E|`) acting
faithfully and irreducibly on a two-dimensional `𝔽_p`-space `V`, with **no nontrivial element
acting as an `𝔽_p`-scalar** (`hnonscalar`), is cyclic with `|E| ∣ p + 1`.

This is the rank-two refinement of Peterfalvi (12.12): the plain irreducible core
(`isCyclic_and_card_dvd_of_odd_two_dim_irreducible`) only bounds `|E| ∣ p² - 1`.  The Singer
realization places `E` inside the cyclic group `𝔽_{p²}ˣ` (order `p² - 1`), where the non-scalar
hypothesis makes it meet the scalar subgroup `𝔽_pˣ` (order `p - 1`) trivially, so
`coprime_card_sub_one_of_faithful_irreducible_comm_nonscalar` gives `Coprime |E| (p - 1)`.  Together
with `|E| ∣ p² - 1 = (p - 1)(p + 1)`, coprimality to the first factor forces `|E| ∣ p + 1`. -/
theorem isCyclic_and_card_dvd_add_one_of_two_dim_irreducible_nonscalar
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V) (hfaith : Function.Injective ρ)
    (hirr : Representation.IsIrreducible ρ)
    (hdim : Module.finrank (ZMod p) V = 2) (hp_ndvd : ¬ p ∣ Nat.card E)
    (hnonscalar : ∀ e : E, (∃ n : ℕ, ∀ x : V, ρ e x = n • x) → e = 1) :
    IsCyclic E ∧ Nat.card E ∣ p + 1 := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- `|E| ∣ p² - 1` and cyclicity from the irreducible core.
  obtain ⟨hcyc, hdvd_sq⟩ :=
    isCyclic_and_card_dvd_of_odd_two_dim_irreducible hodd ρ hfaith hirr hdim hp_ndvd
  refine ⟨hcyc, ?_⟩
  have hcardV : Nat.card V = p ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), hdim, Nat.card_eq_fintype_card, ZMod.card]
  rw [hcardV] at hdvd_sq
  -- Singer non-scalar core ⟹ `Coprime |E| (p - 1)`.  Reuse the `𝔽ₚ[E]`-module setup of the core.
  have hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card E → ¬ CharP (ZMod p) q := fun q _ hqdvd hcharq =>
    hp_ndvd ((CharP.eq (ZMod p) hcharq (ZMod.charP p)) ▸ hqdvd)
  have hcomm : ∀ a b : E, a * b = b * a :=
    (OddOrder.BG.Ch1.S02.odd_two_dim_abelian hodd hdim ρ hfaith hchar).comm
  letI : Module (MonoidAlgebra (ZMod p) E) V := Module.compHom V (ρ.asAlgebraHom).toRingHom
  have hsmul : ∀ (e : E) (x : V), MonoidAlgebra.of (ZMod p) E e • x = ρ e x := fun e x => by
    show (ρ.asAlgebraHom) (MonoidAlgebra.of (ZMod p) E e) x = ρ e x
    rw [Representation.asAlgebraHom_of]
  haveI : IsSimpleModule (MonoidAlgebra (ZMod p) E) V :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
  have hfaith' : ∀ e : E, (∀ x : V, MonoidAlgebra.of (ZMod p) E e • x = x) → e = 1 := by
    intro e he
    apply hfaith
    ext v
    rw [map_one, Module.End.one_apply, ← hsmul e v]
    exact he v
  have hns' : ∀ e : E,
      (∃ n : ℕ, ∀ x : V, MonoidAlgebra.of (ZMod p) E e • x = n • x) → e = 1 := by
    rintro e ⟨n, hn⟩
    exact hnonscalar e ⟨n, fun x => by rw [← hsmul e x]; exact hn x⟩
  have hcop : Nat.Coprime (Nat.card E) (p - 1) :=
    OddOrder.RepresentationTheory.coprime_card_sub_one_of_faithful_irreducible_comm_nonscalar
      hcomm hfaith' hns'
  -- `|E| ∣ (p - 1)(p + 1) = p² - 1` and `Coprime |E| (p - 1)` force `|E| ∣ p + 1`.
  have hpq : (p - 1) * (p + 1) = p ^ 2 - 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 := ⟨p - 2, by have := (Fact.out (p := p.Prime)).two_le; omega⟩
    show (n + 1) * (n + 3) = (n + 2) ^ 2 - 1
    have hexp : (n + 2) ^ 2 = (n + 1) * (n + 3) + 1 := by ring
    omega
  rw [← hpq] at hdvd_sq
  exact hcop.dvd_of_dvd_mul_left hdvd_sq

/-- **(12.12) rep-theory core (dichotomy form).**  A finite odd-order group `E` (`p ∤ |E|`)
acting **fixed-point-freely** on an `𝔽_p`-space `V` of dimension `1` or `2` is **cyclic**, and
either `|E| ∣ p − 1`, or the action is `2`-dimensional **irreducible** with `|E| ∣ p² − 1`.
Dim 1 and the reducible dim-2 case (an `E`-invariant line) go through Case A
(`isCyclic_and_card_dvd_of_faithful_one_dim`); irreducible dim 2 is Case B
(`isCyclic_and_card_dvd_of_odd_two_dim_irreducible`).  The FPF hypothesis makes `E` faithful on
every nonzero invariant subspace.  The dichotomy (rather than the combined `|E| ∣ |V| − 1`)
retains the irreducibility needed by the (12.12) `p + 1` refinement
(`isCyclic_and_card_dvd_add_one_of_two_dim_irreducible_nonscalar`). -/
theorem isCyclic_and_card_dvd_dichotomy_of_fpf_dim_le_two
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V)
    (hfpf : ∀ e : E, e ≠ 1 → ∀ v : V, ρ e v = v → v = 0)
    (hdim : Module.finrank (ZMod p) V = 1 ∨ Module.finrank (ZMod p) V = 2)
    (hp_ndvd : ¬ p ∣ Nat.card E) :
    IsCyclic E ∧ (Nat.card E ∣ p - 1 ∨
      (Module.finrank (ZMod p) V = 2 ∧ Representation.IsIrreducible ρ ∧
        Nat.card E ∣ p ^ 2 - 1)) := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  -- Step 1: the FPF hypothesis makes `ρ` faithful.
  -- `V` is nontrivial because `finrank V ≥ 1`, so it has a nonzero vector; a nontrivial element in
  -- the kernel would fix that vector, contradicting `hfpf`.
  haveI hVnt : Nontrivial V := by
    rcases hdim with h | h
    · exact Module.nontrivial_of_finrank_eq_succ h
    · exact Module.nontrivial_of_finrank_eq_succ (n := 1) (by rw [h])
  have hfaith : Function.Injective ρ := by
    intro a b hab
    by_contra hne
    have hba : b⁻¹ * a ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine hv (hfpf (b⁻¹ * a) hba v ?_)
    rw [map_mul, Module.End.mul_apply, hab, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
  rcases hdim with hd1 | hd2
  · -- dim 1: Case A; `|V| = p`.
    obtain ⟨hcyc, hdvd⟩ := isCyclic_and_card_dvd_of_faithful_one_dim ρ hfaith hd1
    have hcardV : Nat.card V = p := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), hd1, pow_one, Nat.card_eq_fintype_card,
        ZMod.card]
    exact ⟨hcyc, Or.inl (by rwa [hcardV] at hdvd)⟩
  · -- dim 2.
    by_cases hirr : Representation.IsIrreducible ρ
    · -- irreducible: Case B; `|V| = p²`.
      obtain ⟨hcyc, hdvd⟩ :=
        isCyclic_and_card_dvd_of_odd_two_dim_irreducible hodd ρ hfaith hirr hd2 hp_ndvd
      have hcardV : Nat.card V = p ^ 2 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod p), hd2, Nat.card_eq_fintype_card, ZMod.card]
      exact ⟨hcyc, Or.inr ⟨hd2, hirr, by rwa [hcardV] at hdvd⟩⟩
    · -- reducible: a proper nonzero invariant line `W` exists; Case A on `W.toRepresentation`.
      have hbnt : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun h =>
        bot_ne_top (congrArg Subrepresentation.toSubmodule h)
      haveI : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, hbnt⟩
      have hnotall : ¬ ∀ W : Subrepresentation ρ, W = ⊥ ∨ W = ⊤ := fun H =>
        hirr { eq_bot_or_eq_top := H }
      push Not at hnotall
      obtain ⟨W, hWbot, hWtop⟩ := hnotall
      -- `W` is a proper nonzero subrepresentation; its submodule has `finrank = 1`.
      have hWsub_bot : W.toSubmodule ≠ ⊥ := fun h =>
        hWbot (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
      have hWsub_top : W.toSubmodule ≠ ⊤ := fun h =>
        hWtop (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
      haveI : Finite ↥W.toSubmodule := Subtype.finite
      haveI : Module.Finite (ZMod p) ↥W.toSubmodule := Module.Finite.of_finite
      have hpos : 0 < Module.finrank (ZMod p) ↥W.toSubmodule := by
        have := Submodule.finrank_lt_finrank_of_lt (s := (⊥ : Submodule (ZMod p) V))
          (t := W.toSubmodule) (lt_of_le_of_ne bot_le (Ne.symm hWsub_bot))
        simpa using this
      have hlt : Module.finrank (ZMod p) ↥W.toSubmodule < Module.finrank (ZMod p) V :=
        Submodule.finrank_lt hWsub_top
      have hWdim : Module.finrank (ZMod p) ↥W.toSubmodule = 1 := by
        rw [hd2] at hlt; omega
      -- faithfulness of `W.toRepresentation` from `hfpf` restricted to `W`.
      have hfaithW : Function.Injective W.toRepresentation := by
        intro a b hab
        by_contra hne
        have hba : b⁻¹ * a ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
        -- every element of `W` is fixed by `ρ (b⁻¹ a)`, hence is `0` by `hfpf`; so `W = ⊥`.
        apply hWsub_bot
        rw [Submodule.eq_bot_iff]
        intro w hw
        have hfix : W.toRepresentation (b⁻¹ * a) ⟨w, hw⟩ = ⟨w, hw⟩ := by
          rw [map_mul, Module.End.mul_apply, hab, ← Module.End.mul_apply, ← map_mul,
            inv_mul_cancel, map_one, Module.End.one_apply]
        have hfixV : ρ (b⁻¹ * a) w = w := by
          have := congrArg Subtype.val hfix
          simpa [Subrepresentation.toRepresentation, LinearMap.coe_restrict_apply] using this
        exact hfpf (b⁻¹ * a) hba w hfixV
      -- Case A on `W.toRepresentation` gives `IsCyclic E ∧ |E| ∣ p - 1`.
      obtain ⟨hcyc, hdvd⟩ :=
        isCyclic_and_card_dvd_of_faithful_one_dim W.toRepresentation hfaithW hWdim
      have hcardW : Nat.card ↥W.toSubmodule = p := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod p), hWdim, pow_one, Nat.card_eq_fintype_card,
          ZMod.card]
      exact ⟨hcyc, Or.inl (by rwa [hcardW] at hdvd)⟩

/-- **(12.12) rep-theory core (combined).**  A finite odd-order group `E` (`p ∤ |E|`) acting
**fixed-point-freely** (no nonzero vector is fixed by a nontrivial element) on an `𝔽_p`-space `V`
of dimension `1` or `2` is **cyclic**, with `|E| ∣ |V| - 1`.  Forgetful form of the dichotomy
`isCyclic_and_card_dvd_dichotomy_of_fpf_dim_le_two` (`p − 1` divides `|V| − 1` in both dims). -/
theorem isCyclic_and_card_dvd_of_fpf_dim_le_two
    {p : ℕ} [Fact p.Prime] {E V : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) E V)
    (hfpf : ∀ e : E, e ≠ 1 → ∀ v : V, ρ e v = v → v = 0)
    (hdim : Module.finrank (ZMod p) V = 1 ∨ Module.finrank (ZMod p) V = 2)
    (hp_ndvd : ¬ p ∣ Nat.card E) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card V - 1 := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  obtain ⟨hcyc, hdvd⟩ :=
    isCyclic_and_card_dvd_dichotomy_of_fpf_dim_le_two hodd ρ hfpf hdim hp_ndvd
  refine ⟨hcyc, ?_⟩
  have hsub_dvd : (p - 1 : ℕ) ∣ p ^ 2 - 1 := by
    have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_le
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    refine ⟨k + 2, ?_⟩
    have hsq : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
    rw [hsq, Nat.add_sub_cancel, Nat.add_sub_cancel]
  rcases hdim with hd1 | hd2
  · have hcardV : Nat.card V = p := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), hd1, pow_one, Nat.card_eq_fintype_card,
        ZMod.card]
    rw [hcardV]
    rcases hdvd with h1 | ⟨hd2, -, -⟩
    · exact h1
    · rw [hd1] at hd2; omega
  · have hcardV : Nat.card V = p ^ 2 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), hd2, Nat.card_eq_fintype_card, ZMod.card]
    rw [hcardV]
    rcases hdvd with h1 | ⟨-, -, hsq⟩
    · exact h1.trans hsub_dvd
    · exact hsq

/-- **(12.12) rep-theory bridge (abstract `MulDistribMulAction` form).**  A finite odd-order group
`E` (`p ∤ |E|`) acting **fixed-point-freely** on an elementary abelian `p`-group `M` — encoded by
a `ZMod p`-module structure on `Additive M` — of `𝔽_p`-dimension `1` or `2` is **cyclic**, with
`|E| ∣ |M| - 1`.

This lifts `isCyclic_and_card_dvd_of_fpf_dim_le_two` from an abstract `Representation` to a
`MulDistribMulAction` (via `Representation.ofDistribMulAction`), which is the form that a
conjugation action of `E` on an elementary abelian subgroup supplies. -/
theorem isCyclic_and_card_dvd_of_fpf_mulDistribMulAction
    {p : ℕ} [Fact p.Prime] {E M : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [CommGroup M] [Finite M] [Module (ZMod p) (Additive M)] [MulDistribMulAction E M]
    (hp_ndvd : ¬ p ∣ Nat.card E)
    (hdim : Module.finrank (ZMod p) (Additive M) = 1 ∨
      Module.finrank (ZMod p) (Additive M) = 2)
    (hfpf : ∀ e : E, e ≠ 1 → ∀ m : M, e • m = m → m = 1) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card M - 1 := by
  classical
  haveI : Finite (Additive M) := inferInstanceAs (Finite M)
  -- The fixed-point-free hypothesis, transported to the additive representation `ρ = e ↦ (e • ·)`.
  have hfpf' : ∀ e : E, e ≠ 1 → ∀ v : Additive M,
      (Representation.ofDistribMulAction (ZMod p) E (Additive M)) e v = v → v = 0 := by
    intro e he v hv
    rw [Representation.ofDistribMulAction_apply_apply] at hv
    -- `e • v = Additive.ofMul (e • v.toMul)` definitionally; pass to the multiplicative action.
    change Additive.ofMul (e • Additive.toMul v) = v at hv
    have hev : e • Additive.toMul v = Additive.toMul v := by
      have := congrArg Additive.toMul hv; simpa using this
    have hm1 : Additive.toMul v = 1 := hfpf e he _ hev
    exact Additive.toMul.injective (by simp [hm1])
  obtain ⟨hcyc, hdvd⟩ := isCyclic_and_card_dvd_of_fpf_dim_le_two hodd
    (Representation.ofDistribMulAction (ZMod p) E (Additive M)) hfpf' hdim hp_ndvd
  exact ⟨hcyc, by rwa [Nat.card_congr (Additive.toMul (α := M))] at hdvd⟩

/-- **(12.12) rep-theory bridge (conjugation form).**  Let a finite group `E` normalize an
elementary abelian `p`-subgroup `T` of order `p` or `p²` of `G`, with `|E|` odd and coprime to `p`,
and let `E` act **fixed-point-freely on `T` by conjugation** (no nontrivial element of `T` is fixed
by a nontrivial element of `E`).  Then `E` is **cyclic** and `|E|` divides `p - 1` or `p² - 1`.

This is the `§8`-free structural core of Peterfalvi (12.12): there `T = Ω₁(Z(O_p(H)))` is the
rank `≤ 2` elementary abelian subgroup and `E` the Frobenius complement of `L`, acting FPF on `T`
by (12.10).  The `p + 1` refinement of (12.12) is separate (it consumes (12.9)/(12.11)). -/
theorem isCyclic_and_card_dvd_of_fpf_conj_elemAbelian
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T E : Subgroup G} (hT : IsElementaryAbelian p ↥T)
    (hEnorm : E ≤ Subgroup.normalizer (T : Set G))
    (hodd : Odd (Nat.card ↥E)) (hp_ndvd : ¬ p ∣ Nat.card ↥E)
    (hT_card : Nat.card ↥T = p ∨ Nat.card ↥T = p ^ 2)
    (hfpf : ∀ e : G, e ∈ E → e ≠ 1 → ∀ t : G, t ∈ T → e * t * e⁻¹ = t → t = 1) :
    IsCyclic ↥E ∧ (Nat.card ↥E ∣ p - 1 ∨ Nat.card ↥E ∣ p ^ 2 - 1) := by
  classical
  letI : CommGroup ↥T := hT.subgroupCommGroup
  letI : Module (ZMod p) (Additive ↥T) := hT.subgroupZmodModule
  letI act : MulDistribMulAction ↥E ↥T :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (T : Set G))) ↥T
      (Subgroup.inclusion hEnorm)
  -- The conjugation action's coercion: `(ε • τ : G) = ε * τ * ε⁻¹`.
  have hsmul_coe : ∀ (ε : ↥E) (τ : ↥T), ((ε • τ : ↥T) : G) = (ε : G) * (τ : G) * (ε : G)⁻¹ :=
    fun _ _ => rfl
  -- `dim_{𝔽_p} (Additive T) ∈ {1, 2}` from `|T| ∈ {p, p²}`.
  have hcard_pow : p ^ Module.finrank (ZMod p) (Additive ↥T) = Nat.card ↥T := by
    rw [FiniteField.pow_finrank_eq_natCard p (Additive ↥T),
      Nat.card_congr (Additive.toMul (α := ↥T))]
  have h2le := (Fact.out (p := p.Prime)).two_le
  have hdim : Module.finrank (ZMod p) (Additive ↥T) = 1 ∨
      Module.finrank (ZMod p) (Additive ↥T) = 2 := by
    rcases hT_card with h | h
    · have e1 : p ^ Module.finrank (ZMod p) (Additive ↥T) = p ^ 1 := by rw [hcard_pow, h, pow_one]
      exact Or.inl (Nat.pow_right_injective h2le e1)
    · have e2 : p ^ Module.finrank (ZMod p) (Additive ↥T) = p ^ 2 := by rw [hcard_pow, h]
      exact Or.inr (Nat.pow_right_injective h2le e2)
  -- The conjugation FPF hypothesis, transported to the `MulDistribMulAction` form.
  have hfpf' : ∀ ε : ↥E, ε ≠ 1 → ∀ τ : ↥T, ε • τ = τ → τ = 1 := by
    intro ε hεne τ hτ
    have hc : (ε : G) * (τ : G) * (ε : G)⁻¹ = (τ : G) := by
      rw [← hsmul_coe]; exact congrArg Subtype.val hτ
    exact OneMemClass.coe_eq_one.mp
      (hfpf (ε : G) ε.2 (mt OneMemClass.coe_eq_one.mp hεne) (τ : G) τ.2 hc)
  obtain ⟨hcyc, hdvd⟩ :=
    isCyclic_and_card_dvd_of_fpf_mulDistribMulAction hodd hp_ndvd hdim hfpf'
  refine ⟨hcyc, ?_⟩
  rcases hT_card with h | h
  · exact Or.inl (by rwa [h] at hdvd)
  · exact Or.inr (by rwa [h] at hdvd)

/-- **(12.12) rep-theory bridge (abstract `MulDistribMulAction` form), `p ± 1` refinement.**
As in `isCyclic_and_card_dvd_of_fpf_mulDistribMulAction`, but with the **non-scalar** input in
the rank-two case — no nontrivial `e : E` acts on `M` as a uniform power `m ↦ m ^ n` — which
upgrades the rank-two branch to `|E| ∣ p + 1` (Singer,
`isCyclic_and_card_dvd_add_one_of_two_dim_irreducible_nonscalar`); the rank-one and reducible
branches give `|E| ∣ p − 1` outright (dichotomy core,
`isCyclic_and_card_dvd_dichotomy_of_fpf_dim_le_two`). -/
theorem isCyclic_and_card_dvd_sub_or_add_one_of_fpf_mulDistribMulAction
    {p : ℕ} [Fact p.Prime] {E M : Type*} [Group E] [Finite E] (hodd : Odd (Nat.card E))
    [CommGroup M] [Finite M] [Module (ZMod p) (Additive M)] [MulDistribMulAction E M]
    (hp_ndvd : ¬ p ∣ Nat.card E)
    (hdim : Module.finrank (ZMod p) (Additive M) = 1 ∨
      Module.finrank (ZMod p) (Additive M) = 2)
    (hfpf : ∀ e : E, e ≠ 1 → ∀ m : M, e • m = m → m = 1)
    (hnonscalar : Module.finrank (ZMod p) (Additive M) = 2 →
      ∀ e : E, (∃ n : ℕ, ∀ m : M, e • m = m ^ n) → e = 1) :
    IsCyclic E ∧ (Nat.card E ∣ p - 1 ∨ Nat.card E ∣ p + 1) := by
  classical
  haveI : Finite (Additive M) := inferInstanceAs (Finite M)
  -- The FPF hypothesis, transported to the additive representation `ρ = e ↦ (e • ·)`.
  have hfpf' : ∀ e : E, e ≠ 1 → ∀ v : Additive M,
      (Representation.ofDistribMulAction (ZMod p) E (Additive M)) e v = v → v = 0 := by
    intro e he v hv
    rw [Representation.ofDistribMulAction_apply_apply] at hv
    change Additive.ofMul (e • Additive.toMul v) = v at hv
    have hev : e • Additive.toMul v = Additive.toMul v := by
      have := congrArg Additive.toMul hv; simpa using this
    have hm1 : Additive.toMul v = 1 := hfpf e he _ hev
    exact Additive.toMul.injective (by simp [hm1])
  obtain ⟨hcyc, hdvd⟩ := isCyclic_and_card_dvd_dichotomy_of_fpf_dim_le_two hodd
    (Representation.ofDistribMulAction (ZMod p) E (Additive M)) hfpf' hdim hp_ndvd
  refine ⟨hcyc, ?_⟩
  rcases hdvd with h1 | ⟨hd2, hirr, -⟩
  · exact Or.inl h1
  · -- Irreducible rank-two branch: supply the non-scalar input and apply Singer.
    have hfaith :
        Function.Injective (Representation.ofDistribMulAction (ZMod p) E (Additive M)) := by
      intro a b hab
      by_contra hne
      have hba : b⁻¹ * a ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
      haveI : Nontrivial (Additive M) :=
        Module.nontrivial_of_finrank_eq_succ (n := 1) (by rw [hd2])
      obtain ⟨v, hv⟩ := exists_ne (0 : Additive M)
      refine hv (hfpf' (b⁻¹ * a) hba v ?_)
      rw [map_mul, Module.End.mul_apply, hab, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply]
    have hns : ∀ e : E, (∃ n : ℕ, ∀ v : Additive M,
        (Representation.ofDistribMulAction (ZMod p) E (Additive M)) e v = n • v) → e = 1 := by
      rintro e ⟨n, hn⟩
      refine hnonscalar hd2 e ⟨n, fun m => ?_⟩
      have h1 := hn (Additive.ofMul m)
      rw [Representation.ofDistribMulAction_apply_apply] at h1
      have := congrArg Additive.toMul h1
      rw [show Additive.toMul (e • Additive.ofMul m) = e • m from rfl] at this
      simpa using this
    obtain ⟨-, hp1⟩ :=
      isCyclic_and_card_dvd_add_one_of_two_dim_irreducible_nonscalar hodd
        (Representation.ofDistribMulAction (ZMod p) E (Additive M)) hfaith hirr hd2 hp_ndvd hns
    exact Or.inr hp1

/-- **(12.12) rep-theory bridge (conjugation form), `p ± 1` refinement.**  As in
`isCyclic_and_card_dvd_of_fpf_conj_elemAbelian`, but with the **non-scalar** input — no
nontrivial `e ∈ E` conjugates every `t ∈ T` to the same power `t^n` — which upgrades the
`|T| = p²` branch to `|E| ∣ p + 1` (Singer,
`isCyclic_and_card_dvd_add_one_of_two_dim_irreducible_nonscalar`); the reducible/`|T| = p`
branches give `|E| ∣ p − 1` outright (dichotomy core). -/
theorem isCyclic_and_card_dvd_sub_or_add_one_of_fpf_conj_elemAbelian
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T E : Subgroup G} (hT : IsElementaryAbelian p ↥T)
    (hEnorm : E ≤ Subgroup.normalizer (T : Set G))
    (hodd : Odd (Nat.card ↥E)) (hp_ndvd : ¬ p ∣ Nat.card ↥E)
    (hT_card : Nat.card ↥T = p ∨ Nat.card ↥T = p ^ 2)
    (hfpf : ∀ e : G, e ∈ E → e ≠ 1 → ∀ t : G, t ∈ T → e * t * e⁻¹ = t → t = 1)
    (hnonscalar : Nat.card ↥T = p ^ 2 →
      ∀ e : G, e ∈ E → (∃ n : ℕ, ∀ t : G, t ∈ T → e * t * e⁻¹ = t ^ n) → e = 1) :
    IsCyclic ↥E ∧ (Nat.card ↥E ∣ p - 1 ∨ Nat.card ↥E ∣ p + 1) := by
  classical
  letI : CommGroup ↥T := hT.subgroupCommGroup
  letI : Module (ZMod p) (Additive ↥T) := hT.subgroupZmodModule
  letI act : MulDistribMulAction ↥E ↥T :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (T : Set G))) ↥T
      (Subgroup.inclusion hEnorm)
  -- The conjugation action's coercion: `(ε • τ : G) = ε * τ * ε⁻¹`.
  have hsmul_coe : ∀ (ε : ↥E) (τ : ↥T), ((ε • τ : ↥T) : G) = (ε : G) * (τ : G) * (ε : G)⁻¹ :=
    fun _ _ => rfl
  -- `dim_{𝔽_p} (Additive T) ∈ {1, 2}` from `|T| ∈ {p, p²}`.
  have hcard_pow : p ^ Module.finrank (ZMod p) (Additive ↥T) = Nat.card ↥T := by
    rw [FiniteField.pow_finrank_eq_natCard p (Additive ↥T),
      Nat.card_congr (Additive.toMul (α := ↥T))]
  have h2le := (Fact.out (p := p.Prime)).two_le
  have hdim : Module.finrank (ZMod p) (Additive ↥T) = 1 ∨
      Module.finrank (ZMod p) (Additive ↥T) = 2 := by
    rcases hT_card with h | h
    · have e1 : p ^ Module.finrank (ZMod p) (Additive ↥T) = p ^ 1 := by rw [hcard_pow, h, pow_one]
      exact Or.inl (Nat.pow_right_injective h2le e1)
    · have e2 : p ^ Module.finrank (ZMod p) (Additive ↥T) = p ^ 2 := by rw [hcard_pow, h]
      exact Or.inr (Nat.pow_right_injective h2le e2)
  -- The conjugation FPF hypothesis, transported to the `MulDistribMulAction` form.
  have hfpfM : ∀ ε : ↥E, ε ≠ 1 → ∀ τ : ↥T, ε • τ = τ → τ = 1 := by
    intro ε hεne τ hτ
    have hc : (ε : G) * (τ : G) * (ε : G)⁻¹ = (τ : G) := by
      rw [← hsmul_coe]; exact congrArg Subtype.val hτ
    exact OneMemClass.coe_eq_one.mp
      (hfpf (ε : G) ε.2 (mt OneMemClass.coe_eq_one.mp hεne) (τ : G) τ.2 hc)
  -- The conjugation non-scalar hypothesis, transported to the `MulDistribMulAction` form.
  have hnsM : Module.finrank (ZMod p) (Additive ↥T) = 2 →
      ∀ ε : ↥E, (∃ n : ℕ, ∀ τ : ↥T, ε • τ = τ ^ n) → ε = 1 := by
    rintro hd2 ε ⟨n, hn⟩
    have hcardT : Nat.card ↥T = p ^ 2 := by rw [← hcard_pow, hd2]
    refine Subtype.ext (hnonscalar hcardT (ε : G) ε.2 ⟨n, fun t ht => ?_⟩)
    have hcoe := congrArg Subtype.val (hn ⟨t, ht⟩)
    rw [hsmul_coe] at hcoe
    simpa using hcoe
  exact isCyclic_and_card_dvd_sub_or_add_one_of_fpf_mulDistribMulAction hodd hp_ndvd hdim
    hfpfM hnsM

/-- **Peterfalvi (12.12), the `p + 1` refinement** (pinned sorried Singer/(12.11) obligation):
if the witness Frobenius complement's order `e = |E|` divides `p² − 1`, then it divides `p − 1`
or `p + 1`.

Peterfalvi's argument (the second half of the (12.12) proof): `E` is cyclic acting on
`T = Ω₁(P₀)` of order `p²`; identifying `T ⋊ E ↪ 𝔽_{p²} ⋊ 𝔽_{p²}^*` (Schur, as in (9.7.b)), the
subgroup `A ≤ E` of order `gcd(e, p−1)` lands in `𝔽_p^* `, so it normalizes every order-`p`
subgroup of `T` — in particular `⟨x⟩` for the (12.9) witness `x ∈ T`.  Then `A ⊆ N_G(⟨x⟩) ⊆ M`
by (12.9), so `A ⊆ M ∩ L ⊆ H` by (12.11), while `A ≤ E` meets `H` trivially — `A = 1`.  Hence
`gcd(e, p−1) = 1` and `e ∣ p + 1`.

**Genuinely still-missing**: the Singer-cyclic identification of the FPF action (the (9.7.b)
mechanism specialized to the witness) and the `x ∈ T` bookkeeping (`|T| = p²` forces
`T = Ω₁(P₀) ∋ x`) are not assembled; the (12.11) `A = 1` step is now proven
(`intersection_complement_structure`).  The statement is **sound**: it is Peterfalvi's genuine
(12.12) conclusion for the witness of `ctr` (tied via `data`/`frob`), packaged with the `T` data
the argument runs on (supplied by `exists_center_omega1_elemAbelian_fpf_of_witness`). -/
theorem witness_complement_dvd_p_sub_or_add_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (frob : TypeIFrobeniusData data.L)
    {T : Subgroup G} (hTelem : T.IsElementaryAbelian ctr.p) (hTP0 : T ≤ ctr.P0) (hTne : T ≠ ⊥)
    (hEnorm : frob.complement.map data.L.subtype ≤ Subgroup.normalizer (T : Set G))
    (hfpf : ∀ e : G, e ∈ frob.complement.map data.L.subtype → e ≠ 1 →
      ∀ t : G, t ∈ T → e * t * e⁻¹ = t → t = 1) :
    Nat.card ↥frob.complement ∣ ctr.p - 1 ∨ Nat.card ↥frob.complement ∣ ctr.p + 1 := by
  sorry

/-- **Peterfalvi (12.12), structural input from (12.9)/(12.10)/(12.11)** (pinned sorried §8/§9
obligation, hub 9003 Cluster A).  For the (12.9) witness `L` (type-I Frobenius, kernel `H = L_F`),
with `E := frob.complement.map L.subtype` the Frobenius complement realized in `G`, there is a
subgroup `T ≤ G` — Peterfalvi's `T = Ω₁Z(O_p(H))` — that is
* **elementary abelian** of order `p` or `p²` (`P₀` is abelian of rank `2` by (12.9), so `Ω₁Z(P)`
  has order `p` or `p²`);
* **normalized by `E`** (`E` normalizes `O_p(H)`, its center, and the `Ω₁`);
* on which `E` acts **fixed-point-freely by conjugation** (Peterfalvi (12.10): as `L` is Frobenius
  with kernel `H`, the complement `E` fixes no nonidentity element of `H`, a fortiori none of
  `T ⊆ H`),

and, encoding the `p+1` refinement of (12.12) (the (12.11) step `A ⊆ M ⟹ A = 1` for `A ≤ E` of
order dividing `p-1`), if `|E|` divides `p² - 1` then in fact `|E|` divides `p - 1` or `p + 1`.  We
also record `T ≤ H` (`Ω₁Z(O_p(H)) ⊆ H`), used to see `p ∣ |H|`.

**Assembly** (proven, modulo the `p+1` refinement pin): `P := O_p(H)` contains `P₀` (nilpotent
`H`), and `T := Ω₁(Z(P))` is elementary abelian (`omega1OfAbelian`).  The elided order bound is
the (12.9) control: `T ⊆ Z(P) ⊆ C_G(x) ≤ N_G(⟨x⟩) ≤ M` and `T` centralizes `P₀ ≤ P`, so the
abelian `p`-subgroup `T ⊔ P₀ ≤ M` lies in the full `p`-part `P₀`, whence `T ⊆ P₀` (abelian of
rank `2`) and `|T| ∈ {p, p²}` (`card_eq_prime_or_sq_of_isElementaryAbelian_le`).  `E` normalizes
`T` through the characteristic chain `N(H) ≤ N(O_p(H)) ≤ N(Z(O_p(H))) ≤ N(Ω₁(...))`, and acts
fixed-point-freely on `T ⊆ H` by the Frobenius structure.  The `p+1` refinement is the pinned
`witness_complement_dvd_p_sub_or_add_one`. -/
theorem exists_center_omega1_elemAbelian_fpf_of_witness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (frob : TypeIFrobeniusData data.L) :
    ∃ T : Subgroup G, IsElementaryAbelian ctr.p ↥T ∧
      (frob.complement.map data.L.subtype ≤ Subgroup.normalizer (T : Set G)) ∧
      (Nat.card ↥T = ctr.p ∨ Nat.card ↥T = ctr.p ^ 2) ∧
      T ≤ frob.typeI.typeF.H ∧
      (∀ e : G, e ∈ frob.complement.map data.L.subtype → e ≠ 1 →
        ∀ t : G, t ∈ T → e * t * e⁻¹ = t → t = 1) ∧
      (Nat.card ↥frob.complement ∣ ctr.p ^ 2 - 1 →
        Nat.card ↥frob.complement ∣ ctr.p - 1 ∨ Nat.card ↥frob.complement ∣ ctr.p + 1) := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- `H = L_F` is nilpotent and contains `P₀`; set `P := O_p(H) ⊇ P₀`.
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall data.L := frob.typeI.typeF.H_eq
  haveI hHnilp : Group.IsNilpotent ↥frob.typeI.typeF.H := by
    rw [hHeq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent data.L
  have hP0H : ctr.P0 ≤ frob.typeI.typeF.H := by
    rw [hHeq]; exact witness_P0_le_kernel hG data
  set P : Subgroup G := opiCoreInG ({ctr.p} : Set ℕ) frob.typeI.typeF.H with hPdef
  have hP0P : ctr.P0 ≤ P := pGroup_le_opiCoreInG_of_le_of_isNilpotent ctr.P0_pGroup hP0H
  have hPH : P ≤ frob.typeI.typeF.H := opiCoreInG_le _ _
  have hPp : IsPGroup ctr.p ↥P := isPGroup_opiCoreInG_singleton _
  -- `Z := Z(P)` in `G` (abelian), `T := Ω₁(Z)`.
  set Z : Subgroup G := (Subgroup.center ↥P).map P.subtype with hZdef
  have hZcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    ((Subgroup.mem_center_map_subtype_iff.mp hx).2 y
      (Subgroup.mem_center_map_subtype_iff.mp hy).1).symm
  set T : Subgroup G := OddOrder.GroupTheory.omega1OfAbelian G Z ctr.p hZcomm with hTdef
  have hTZ : T ≤ Z := OddOrder.GroupTheory.omega1OfAbelian_le
  have hZP : Z ≤ P := hZdef ▸ Subgroup.map_subtype_le _
  have hTH : T ≤ frob.typeI.typeF.H := hTZ.trans (hZP.trans hPH)
  have hTelem : T.IsElementaryAbelian ctr.p :=
    OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
  -- `T ≠ ⊥`: the nontrivial `p`-group `P` has nontrivial center, whose Cauchy `p`-element
  -- lies in `Ω₁(Z)`.
  have hP0ne : ctr.P0 ≠ ⊥ := fun h => ctr.P0_noncyclic (h ▸ inferInstance)
  have hPne : P ≠ ⊥ := fun h => hP0ne (le_bot_iff.mp (h ▸ hP0P))
  have hTne : T ≠ ⊥ := by
    haveI : Nontrivial ↥P := P.nontrivial_iff_ne_bot.mpr hPne
    haveI : Nontrivial (Subgroup.center ↥P) := hPp.center_nontrivial
    have hZne : Z ≠ ⊥ := by
      intro hbot
      obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center ↥P)
      refine hz1 (Subtype.ext (Subtype.ext ?_))
      have hzZ : ((z : ↥P) : G) ∈ Z := hZdef ▸ ⟨z, z.2, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hzZ
      exact hzZ
    have hZp : IsPGroup ctr.p ↥Z := hPp.to_le hZP
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    have hkpos : k ≠ 0 := by
      rintro rfl
      exact hZne (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
    haveI : Fintype ↥Z := Fintype.ofFinite _
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := ↥Z) ctr.p
      (by rw [← Nat.card_eq_fintype_card, hk]; exact dvd_pow_self _ hkpos)
    have hg_ord : orderOf (g : G) = ctr.p := by
      rw [← hg]; exact orderOf_injective Z.subtype Z.subtype_injective g
    have hgT : (g : G) ∈ T := ⟨g.2, by rw [← hg_ord]; exact pow_orderOf_eq_one _⟩
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hgT
    rw [hgT, orderOf_one] at hg_ord
    exact ctr.p_prime.one_lt.ne' hg_ord.symm
  -- The (12.9) control: `T ⊆ Z(P) ⊆ C_G(x) ≤ M`, and `T` centralizes `P₀`, so the abelian
  -- `p`-subgroup `T ⊔ P₀ ≤ M` lies in the full `p`-part `P₀`; hence `T ⊆ P₀` of rank `2`.
  have hxP : data.x ∈ P := hP0P data.x_mem_P0
  have hTCx : T ≤ Subgroup.centralizer ({data.x} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_center_map_subtype_iff.mp (hTZ ht)).2 data.x hxP).symm
  have hCM : Subgroup.centralizer ({data.x} : Set G) ≤ ctr.M := by
    refine le_trans ?_ data.normalizer_closure_x_le_M
    rw [← Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hTM : T ≤ ctr.M := hTCx.trans hCM
  have hTcent : T ≤ Subgroup.centralizer (ctr.P0 : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_center_map_subtype_iff.mp (hTZ ht)).2 w (hP0P hw)
  have hTp : IsPGroup ctr.p ↥T := hPp.to_le (hTZ.trans hZP)
  have hsup_p : IsPGroup ctr.p ↥(T ⊔ ctr.P0) :=
    IsPGroup.to_sup_of_normal_right' hTp ctr.P0_pGroup
      (hTcent.trans (Subgroup.centralizer_le_normalizer _))
  have hsup_eq : T ⊔ ctr.P0 = ctr.P0 := by
    have hle_M : T ⊔ ctr.P0 ≤ ctr.M := sup_le hTM ctr.P0_le_M
    obtain ⟨m, hm⟩ := hsup_p.exists_card_eq
    have hdvd_M : (ctr.p : ℕ) ^ m ∣ Nat.card ↥ctr.M := by
      rw [← hm]; exact Subgroup.card_dvd_of_le hle_M
    have hMsplit : Nat.card ↥ctr.M = Nat.card ↥ctr.P0 * ctr.P0.relIndex ctr.M := by
      rw [Subgroup.relIndex, ← Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe ctr.P0_le_M).toEquiv]
      exact ((ctr.P0.subgroupOf ctr.M).card_mul_index).symm
    have hcop : Nat.Coprime (ctr.p ^ m) (ctr.P0.relIndex ctr.M) :=
      Nat.Coprime.pow_left m
        (ctr.p_prime.coprime_iff_not_dvd.mpr ctr.P0_sylow)
    have hdvd_P0 : (ctr.p : ℕ) ^ m ∣ Nat.card ↥ctr.P0 :=
      hcop.dvd_of_dvd_mul_right (hMsplit ▸ hdvd_M)
    refine (Subgroup.eq_of_le_of_card_ge le_sup_right ?_).symm
    rw [hm]
    exact Nat.le_of_dvd Nat.card_pos hdvd_P0
  have hTP0 : T ≤ ctr.P0 := hsup_eq ▸ le_sup_left
  have hTcard : Nat.card ↥T = ctr.p ∨ Nat.card ↥T = ctr.p ^ 2 :=
    OddOrder.GroupTheory.card_eq_prime_or_sq_of_isElementaryAbelian_le hTelem hTP0
      (counterexample_P0_K_structure hG ctr).2.le hTne
  -- `E` normalizes `T`: through `N(H) ≤ N(O_p(H)) ≤ N(Z(O_p(H))) ≤ N(Ω₁(Z))`.
  have hEnorm : frob.complement.map data.L.subtype ≤ Subgroup.normalizer (T : Set G) := by
    have hchain : Subgroup.normalizer ((frob.typeI.typeF.H : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((T : Subgroup G) : Set G) := by
      intro g hg
      have hgP : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
        le_normalizer_opiCoreInG_of_le_normalizer ({ctr.p} : Set ℕ) le_rfl hg
      have hgZ : g ∈ Subgroup.normalizer ((Z : Subgroup G) : Set G) :=
        hZdef ▸ Subgroup.mem_normalizer_center_map_of_mem_normalizer hgP
      exact OddOrder.GroupTheory.mem_normalizer_omega1OfAbelian hgZ
    refine le_trans ?_ hchain
    intro e he
    obtain ⟨a, -, rfl⟩ := he
    have hLN : data.L ≤ Subgroup.normalizer ((frob.typeI.typeF.H : Subgroup G) : Set G) := by
      rw [hHeq]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer data.L
    exact hLN a.2
  -- Fixed-point-freeness on `T ⊆ H` from the Frobenius structure of `L`.
  have hfpf : ∀ e : G, e ∈ frob.complement.map data.L.subtype → e ≠ 1 →
      ∀ t : G, t ∈ T → e * t * e⁻¹ = t → t = 1 := by
    intro e he hene t ht hconj
    obtain ⟨a, haC, rfl⟩ := he
    have htH : t ∈ frob.typeI.typeF.H := hTH ht
    have htL : t ∈ data.L := frob.typeI.typeF.H_le htH
    by_contra htne
    have hane : a ≠ 1 := fun h => hene (by rw [h]; rfl)
    exact frob.frobenius.conj_frobenius a haC hane ⟨t, htL⟩
      (Subgroup.mem_subgroupOf.mpr htH) (fun h => htne (congrArg Subtype.val h))
      (Subtype.ext hconj)
  exact ⟨T, hTelem, hEnorm, hTcard, hTH, hfpf, fun _ =>
    witness_complement_dvd_p_sub_or_add_one hG data frob hTelem hTP0 hTne hEnorm hfpf⟩

/-- **Peterfalvi (12.12)**: the Frobenius complement `E` in the (12.9) witness subgroup `L` is
cyclic, with order `e = |E|` dividing `p - 1` or `p + 1`.

**Assembly** (`sorry`-free modulo the (12.9)/(12.10)/(12.11) structural package): from
`exists_center_omega1_elemAbelian_fpf_of_witness` we obtain `T = Ω₁Z(O_p(H))` — elementary abelian
of order `p` or `p²`, normalized by `E` (realized in `G` as `E' = frob.complement.map L.subtype`),
with `E'` acting fixed-point-freely on `T` by conjugation.  The proven rep-theory core
`isCyclic_and_card_dvd_of_fpf_conj_elemAbelian` then gives `IsCyclic E' ∧ (|E'| ∣ p-1 ∨ |E'| ∣ p²-1)`
(the `§8`-free Singer/Case-A+B mechanism).  Transporting cyclicity back along `L.subtype` (`E ≅ E'`)
and applying the packaged `p+1` refinement to the `p²-1` branch yields the (12.12) conclusion. -/
theorem complement_cyclic_order_dvd [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (frob : TypeIFrobeniusData data.L) :
    IsCyclic ↥frob.complement ∧
      ((Nat.card ↥frob.complement ∣ ctr.p - 1) ∨
        (Nat.card ↥frob.complement ∣ ctr.p + 1)) := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- The Frobenius complement, realized as a subgroup `E'` of the ambient `G`.
  set E' : Subgroup G := frob.complement.map data.L.subtype with hE'
  -- `E ≅ E'` (injective image), so cardinalities agree.
  have hEcard : Nat.card ↥E' = Nat.card ↥frob.complement :=
    Subgroup.card_map_of_injective (K := frob.complement) data.L.subtype_injective
  -- The (12.9)/(12.10)/(12.11) structural package for the witness complement.
  obtain ⟨T, hTelem, hEnorm, hTcard, hTleH, hfpf, hrefine⟩ :=
    exists_center_omega1_elemAbelian_fpf_of_witness hG data frob
  -- Odd order of `E'` (a subgroup of the odd-order `G`).
  have hodd : Odd (Nat.card ↥E') :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card E')
  -- `p ∤ |E'|`: `E'` is a Frobenius complement, coprime to the kernel `H ⊇ T` which has order
  -- divisible by `p` (`|T| = p` or `p²`).  Concretely `|T| ∣ |kernel|` and `p ∣ |T|`, while
  -- `Coprime |kernel| |complement|`, so `p ∤ |E'|`.
  have hp_ndvd : ¬ ctr.p ∣ Nat.card ↥E' := by
    -- `p ∣ |T|` (order `p` or `p²`).
    have hpT : ctr.p ∣ Nat.card ↥T := by
      rcases hTcard with h | h
      · rw [h]
      · rw [h]; exact dvd_pow_self ctr.p (by norm_num)
    -- `T ≤ H` (`T = Ω₁Z(O_p(H)) ⊆ H`); realize via the FPF hypothesis: `T`'s elements are moved by
    -- every nontrivial element of `E'`, and `E'`, `H` are Frobenius-coprime.  We use the abstract
    -- coprimality of the Frobenius pair on `↥L`.
    have hcopLL : Nat.Coprime (Nat.card ↥(frob.typeI.typeF.H.subgroupOf data.L))
        (Nat.card ↥frob.complement) := frob.frobenius.coprime_card_kernel_complement
    -- It suffices that `p ∣ |H|` and `Coprime |H| |E'|` (via `|E'| = |E|`), then `p ∤ |E'|`.
    -- `|H_L| = |H|` where `H_L = H.subgroupOf L`.
    have hHcard : Nat.card ↥(frob.typeI.typeF.H.subgroupOf data.L)
        = Nat.card ↥frob.typeI.typeF.H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe frob.typeI.typeF.H_le).toEquiv
    -- `p ∣ |H|`: `T ≤ H` (`hTleH`, from the package), and `p ∣ |T| ∣ |H|`.
    have hpH : ctr.p ∣ Nat.card ↥frob.typeI.typeF.H :=
      hpT.trans (Subgroup.card_dvd_of_le hTleH)
    have hpHL : ctr.p ∣ Nat.card ↥(frob.typeI.typeF.H.subgroupOf data.L) := by
      rw [hHcard]; exact hpH
    rw [hEcard]
    intro hpE
    exact ctr.p_prime.not_dvd_one (hcopLL ▸ Nat.dvd_gcd hpHL hpE)
  -- The proven rep-theory core: `E'` cyclic and `|E'| ∣ p-1 ∨ |E'| ∣ p²-1`.
  obtain ⟨hcycE', hdvdE'⟩ :=
    isCyclic_and_card_dvd_of_fpf_conj_elemAbelian hTelem hEnorm hodd (hEcard ▸ hp_ndvd) hTcard hfpf
  -- Transport cyclicity `E' ≅ E` back to `E`.
  have hcyc : IsCyclic ↥frob.complement :=
    isCyclic_of_surjective _
      (Subgroup.equivMapOfInjective frob.complement data.L.subtype
        data.L.subtype_injective).symm.surjective
  refine ⟨hcyc, ?_⟩
  -- Rewrite `|E'| = |E|` in the divisibility and apply the `p+1` refinement.
  rw [hEcard] at hdvdE'
  rcases hdvdE' with h | h
  · exact Or.inl h
  · exact hrefine h

end OddOrder.Peterfalvi.S14
