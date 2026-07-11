import OddOrder.Peterfalvi.S15_SAndT_Setup.DegreesFirstSplit

/-!
# Peterfalvi (13.5)-(13.10) — counting layer

Split from the former monolithic `OddOrder.Peterfalvi.S15_SAndT_Setup` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


section CountingLayer

open OddOrder.GroupTheory

/-- Under **Peterfalvi (13.1)**, the prime parameters are distinct: `W₁` and `W₂` are nontrivial
subgroups of the *cyclic* `W` with trivial intersection, so if `p = q` the `q`-element count of
`W` would exceed `φ(q)` (`IsCyclic.card_orderOf_eq_totient`): `W₁^#` supplies `q − 1` elements of
order `q` and `W₂^#` a further one outside `W₁`. -/
theorem Hypothesis.p_ne_q [Finite G] (hyp : Hypothesis (G := G)) : hyp.p ≠ hyp.q := by
  intro hpq
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hW2W : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  haveI : IsCyclic ↥hyp.W := hyp.W_cyclic
  haveI : Fintype ↥hyp.W := Fintype.ofFinite _
  classical
  set W1' : Subgroup ↥hyp.W := hyp.W1.subgroupOf hyp.W with hW1def
  set W2' : Subgroup ↥hyp.W := hyp.W2.subgroupOf hyp.W with hW2def
  have hc1 : Nat.card ↥W1' = hyp.q := by
    rw [hW1def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1W).toEquiv, ← hyp.q_eq_card_W1]
  have hc2 : Nat.card ↥W2' = hyp.q := by
    rw [hW2def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2W).toEquiv, ← hpq,
      ← hyp.p_eq_card_W2]
  have hinf : W1' ⊓ W2' = ⊥ := by
    ext a
    simp only [Subgroup.mem_inf, Subgroup.mem_bot, Subgroup.mem_subgroupOf, hW1def, hW2def]
    constructor
    · rintro ⟨h1, h2⟩
      have hmem : (a : G) ∈ hyp.W1 ⊓ hyp.W2 := ⟨h1, h2⟩
      rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hmem
      exact OneMemClass.coe_eq_one.mp hmem
    · rintro rfl; exact ⟨one_mem _, one_mem _⟩
  -- Nonidentity elements of an order-`q` subgroup have order `q`.
  have horder : ∀ (V : Subgroup ↥hyp.W), Nat.card ↥V = hyp.q →
      ∀ a : ↥hyp.W, a ∈ V → a ≠ 1 → orderOf a = hyp.q := by
    intro V hV a ha ha1
    have hdvd : orderOf a ∣ hyp.q := by
      have h1 : orderOf (⟨a, ha⟩ : ↥V) ∣ Nat.card ↥V := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk a ha, hV] at h1
    rcases (Nat.dvd_prime hyp.q_prime).mp hdvd with h1 | hq
    · exact absurd (orderOf_eq_one_iff.mp h1) ha1
    · exact hq
  -- The order-`q` element count of the cyclic `W` is `φ(q) = q − 1`.
  have hqdvd : hyp.q ∣ Fintype.card ↥hyp.W := by
    rw [← Nat.card_eq_fintype_card, ← hc1]
    exact Subgroup.card_subgroup_dvd_card W1'
  have htot := IsCyclic.card_orderOf_eq_totient (α := ↥hyp.W) hqdvd
  -- ... but `W₁^# ∪ {y}` (`y ∈ W₂^#`) already has `q` elements of order `q`.
  obtain ⟨y', hy'⟩ : ∃ y' : ↥W2', y' ≠ 1 := by
    haveI : Nontrivial ↥W2' := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [hc2]; exact hyp.q_prime.one_lt)
    exact exists_ne 1
  have hy1 : (y' : ↥hyp.W) ≠ 1 := by
    intro h
    exact hy' (OneMemClass.coe_eq_one.mp h)
  have hyW2 : (y' : ↥hyp.W) ∈ W2' := y'.2
  set F : Finset ↥hyp.W :=
    insert (y' : ↥hyp.W) ((Finset.univ.filter (· ∈ W1')).erase 1) with hFdef
  have hynotin : (y' : ↥hyp.W) ∉ (Finset.univ.filter (· ∈ W1')).erase 1 := by
    intro hmem
    have hyW1 : (y' : ↥hyp.W) ∈ W1' := (Finset.mem_filter.mp (Finset.mem_erase.mp hmem).2).2
    have : (y' : ↥hyp.W) ∈ W1' ⊓ W2' := ⟨hyW1, hyW2⟩
    rw [hinf] at this
    exact hy1 this
  have hW1card : (Finset.univ.filter (· ∈ W1')).card = hyp.q := by
    rw [← hc1, Nat.card_eq_fintype_card]
    simp [Fintype.card_subtype]
  have hFcard : F.card = hyp.q := by
    rw [hFdef, Finset.card_insert_of_notMem hynotin,
      Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, W1'.one_mem⟩),
      hW1card]
    have := hyp.q_prime.two_le
    omega
  have hFsub : F ⊆ Finset.univ.filter (fun a => orderOf a = hyp.q) := by
    intro a ha
    rw [hFdef, Finset.mem_insert] at ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases ha with rfl | ha
    · exact horder W2' hc2 _ hyW2 hy1
    · obtain ⟨ha1, hamem⟩ := Finset.mem_erase.mp ha
      exact horder W1' hc1 a (Finset.mem_filter.mp hamem).2 ha1
  have hle : hyp.q ≤ hyp.q.totient := by
    calc hyp.q = F.card := hFcard.symm
      _ ≤ (Finset.univ.filter (fun a => orderOf a = hyp.q)).card := Finset.card_le_card hFsub
      _ = hyp.q.totient := htot
  rw [Nat.totient_prime hyp.q_prime] at hle
  have := hyp.q_prime.two_le
  omega

/-- **`W₁ ≤ T'`** (local, pairing-free): the cyclic factor `W₁` (prime order `q`) lies in the derived
subgroup `T'`.  `W₁ ≤ W ≤ T`, `T' ⊴ T` with index `[T : T'] = |W₂| = p` (`W2_isComplement_T_deriv`),
and `q ≠ p` (`p_ne_q`); so the `q`-group `W₁` lands in the `p`-coprime-index normal `T'`
(`subgroup_le_of_normal_coprime_index_prime`).  Unlike the `T`-side `W₁ ≤ Q` (which needs the (8.4.d)
dual pairing), this containment is immediate from the abstract `Hypothesis` and feeds the `W₂`-side
centralizer localisation `W₁ ≤ T' ⊓ C(W₂)` used by `reconciled_typePData_T`. -/
theorem Hypothesis.W1_le_derivedInG_T [Finite G] (hyp : Hypothesis (G := G)) :
    hyp.W1 ≤ derivedInG hyp.T := by
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hWT : hyp.W ≤ hyp.T := by rw [hyp.W_eq_inter]; exact inf_le_right
  have hW2W : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  have hW2T : hyp.W2 ≤ hyp.T := hW2W.trans hWT
  -- `T' ⊴ T`
  have hid : (derivedInG hyp.T).subgroupOf hyp.T = commutator ↥hyp.T :=
    Subgroup.comap_map_eq_self_of_injective hyp.T.subtype_injective (commutator ↥hyp.T)
  haveI hM'norm : ((derivedInG hyp.T).subgroupOf hyp.T).Normal := by rw [hid]; infer_instance
  -- `[T : T'] = |W₂| = p`
  have hindex : ((derivedInG hyp.T).subgroupOf hyp.T).index = hyp.p := by
    rw [hyp.W2_isComplement_T_deriv.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2T).toEquiv, ← hyp.p_eq_card_W2]
  refine subgroup_le_of_normal_coprime_index_prime (p := hyp.q) (hW1W.trans hWT) hM'norm ?_ ?_
  · rw [hindex]
    exact (Nat.coprime_primes hyp.q_prime hyp.p_prime).mpr hyp.p_ne_q.symm
  · intro w hw
    have heq : orderOf (⟨w, hw⟩ : ↥hyp.W1) = orderOf w :=
      (orderOf_injective hyp.W1.subtype Subtype.coe_injective ⟨w, hw⟩).symm
    have h1 : orderOf (⟨w, hw⟩ : ↥hyp.W1) ∣ Nat.card ↥hyp.W1 := orderOf_dvd_natCard _
    rw [heq, ← hyp.q_eq_card_W1] at h1
    exact h1

/-- `Q = T_F` is nontrivial: any type-`P` witness on `T` (available from `T_nonI` via
`typePData_of_isTypeNonI`) records `H = T_F` noncyclic, and `⊥` is cyclic. -/
theorem Hypothesis.Q_ne_bot [Finite G] (hyp : Hypothesis (G := G)) : hyp.Q ≠ ⊥ := by
  obtain ⟨tpd⟩ := OddOrder.GroupTheory.typePData_of_isTypeNonI hyp.T_nonI
  intro hbot
  apply tpd.H_noncyclic
  rw [tpd.H_eq, ← hyp.Q_eq_TF, hbot]
  infer_instance

/-- **`N_G(Q) = T`** — the `T`-side mirror of the (8.5.a) normalizer identity: `Q = T_F` is a
nontrivial `T`-normal subgroup of the maximal `T` of the minimal simple `G`, hence
self-normalizing at `T` (`normalizer_eq_self_of_subgroupOf_normal_of_ne_bot`). -/
theorem normalizer_Q_eq_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.Q : Set G) = hyp.T := by
  refine OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG
    hyp.T_maximal ?_ ?_ hyp.Q_ne_bot
  · rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  · rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.T

/-- Elements of the set-normalizer of `(K : Set G)` stabilize the sharp `K^# = K − 1` under
conjugation — the `hstab` input shape of `IsTISubset.sum_conjClassSet`. -/
theorem conj_smul_sharpSubgroup_eq {K N : Subgroup G}
    (hnorm : Subgroup.normalizer (K : Set G) = N) {l : G} (hl : l ∈ N) :
    MulAut.conj l • sharpSubgroup K = sharpSubgroup K := by
  have hlnorm : l ∈ Subgroup.normalizer (K : Set G) := hnorm ▸ hl
  rw [Subgroup.mem_set_normalizer_iff] at hlnorm
  ext x
  simp only [Set.mem_smul_set, MulAut.smul_def, MulAut.conj_apply, sharpSubgroup, Set.mem_sdiff,
    Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨v, ⟨hvK, hv1⟩, rfl⟩
    refine ⟨(hlnorm v).mp hvK, fun heq => hv1 ?_⟩
    calc v = l⁻¹ * (l * v * l⁻¹) * l := by group
      _ = 1 := by rw [heq]; group
  · rintro ⟨hxK, hx1⟩
    refine ⟨l⁻¹ * x * l, ⟨?_, fun heq => hx1 ?_⟩, by group⟩
    · have := (hlnorm (l⁻¹ * x * l)).mpr
      rw [show l * (l⁻¹ * x * l) * l⁻¹ = x from by group] at this
      exact this hxK
    · calc x = l * (l⁻¹ * x * l) * l⁻¹ := by group
        _ = 1 := by rw [heq]; group

/-- **`N_G(H) = S`** (Peterfalvi (8.5.a)): `H = PC = F(S)` (`H_eq_fittingInG`) and
`N_G(F(S)) = S` (`normalizer_fittingInAmbient_eq_self`). -/
theorem normalizer_H_eq_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.H : Set G) = hyp.S := by
  have hHF : hyp.H = OddOrder.BG.Ch2.S08.fittingInG hyp.S := hyp.H_eq_fittingInG
  have hnorm : Subgroup.normalizer (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) = hyp.S :=
    OddOrder.BG.Ch4.S16.normalizer_fittingInAmbient_eq_self hG hyp.S_maximal
  rw [hHF]; exact hnorm

/-- **`V` is nilpotent** — the `U`-factor of `T`'s reconciled type-`P` datum.  `V` and any type-`P`
complement `tpd0.U` (from `typePData_of_isTypeNonI T_nonI`) both complement `Q = T_F` in `T' = QV`
(`derived_complement` / `Q_inf_V_eq_bot` + `T_deriv_eq_QV`), so Schur–Zassenhaus conjugacy inside
`↥T'` (`IsComplement'.exists_conj_of_coprime`, coprimality from `Q` being Hall in `T`) conjugates
`tpd0.U` onto `V`, transporting `Group.IsNilpotent` (`tpd0.U_nilpotent`).  Structurally the mirror of
the `S16` complement-conjugacy transport `isMulCommutative_typePData_U_of_V`.  Discharges the
`U_nilpotent` field of `reconciled_typePData_T` without matching the full `T`-side type-`P` datum. -/
theorem Hypothesis.isNilpotent_V [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : Group.IsNilpotent ↥hyp.V := by
  obtain ⟨tpd0⟩ := OddOrder.GroupTheory.typePData_of_isTypeNonI hyp.T_nonI
  have hQtpd : tpd0.H = hyp.Q := by rw [tpd0.H_eq, ← hyp.Q_eq_TF]
  have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
  have hU_le : tpd0.U ≤ derivedInG hyp.T := tpd0.U_le
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hQ_le_T : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  haveI hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
  -- `Q` complements `V` in `T'`.
  have hVcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (hyp.V.subgroupOf (derivedInG hyp.T)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
        OneMemClass.coe_one]
      refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
      have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) := ⟨hxQ, hxV⟩
      rwa [hyp.Q_inf_V_eq_bot, Subgroup.mem_bot] at hxQV
    · have hsup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
          (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.T_deriv_eq_QV.symm, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
        (hyp.V.subgroupOf (derivedInG hyp.T))
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  -- `Q` complements `tpd0.U` in `T'` (from `tpd0.derived_complement`, `tpd0.H = Q`).
  have hUcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (tpd0.U.subgroupOf (derivedInG hyp.T)) := by
    rw [← hQtpd]; exact tpd0.derived_complement
  have hcop : Nat.Coprime (Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)))
      ((hyp.Q.subgroupOf (derivedInG hyp.T)).index) := by
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.T
    rw [← hyp.Q_eq_TF] at hHall
    have h0 := OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_T).toEquiv] at h0
    have hcard : Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) = Nat.card ↥hyp.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv
    have hdvd : (hyp.Q.subgroupOf (derivedInG hyp.T)).index ∣
        (hyp.Q.subgroupOf hyp.T).index := by
      have htower : hyp.Q.relIndex (derivedInG hyp.T) *
          (derivedInG hyp.T).relIndex hyp.T = hyp.Q.relIndex hyp.T :=
        Subgroup.relIndex_mul_relIndex hyp.Q (derivedInG hyp.T) hyp.T hQ_le hM'_le_T
      show hyp.Q.relIndex (derivedInG hyp.T) ∣ hyp.Q.relIndex hyp.T
      exact ⟨(derivedInG hyp.T).relIndex hyp.T, htower.symm⟩
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right hdvd h0
  have hQ_lt_top : hyp.Q < ⊤ :=
    lt_of_le_of_lt hQ_le_T (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.T_maximal).1)
  haveI hQsolv : IsSolvable ↥hyp.Q := hG.solvable_of_lt_top hyp.Q hQ_lt_top
  have hsolv : IsSolvable ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) ∨
      IsSolvable (↥(derivedInG hyp.T) ⧸ hyp.Q.subgroupOf (derivedInG hyp.T)) :=
    Or.inl (solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQ_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQ_le).injective)
  -- Schur–Zassenhaus conjugates `tpd0.U` onto `V` inside `T'`; push nilpotency forward.
  obtain ⟨n, _hnQ, hn⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop hsolv hUcompl hVcompl
  haveI : Group.IsNilpotent ↥tpd0.U := tpd0.U_nilpotent
  have h1 : Group.IsNilpotent ↥(tpd0.U.subgroupOf (derivedInG hyp.T)) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hU_le).symm
  haveI := h1
  have h2 : Group.IsNilpotent
      ↥((tpd0.U.subgroupOf (derivedInG hyp.T)).map (MulAut.conj n).toMonoidHom) :=
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ (MulAut.conj n).injective)
  have h3 : Group.IsNilpotent ↥(hyp.V.subgroupOf (derivedInG hyp.T)) := hn ▸ h2
  haveI := h3
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hV_le)

/-- **A type-`P` datum on `T` whose complement is the abstract `V` (and whose kernel is `Q`).**
The §13-level producer `typePData_of_isTypeNonI T_nonI` gives *some* `tpd0 : TypePData T`; its
complement `tpd0.U` and the §16-chosen `V` both complement `Q = T_F` in `T' = QV`, so Schur–Zassenhaus
inside `↥T'` (`IsComplement'.exists_conj_of_coprime`) conjugates `tpd0.U` onto `V` by an element
`g ∈ T'` (hence `g ∈ T`).  Because `g ∈ T`, conjugation by `g` fixes both `T` and its normal
`Q = T_F`, so whole-datum conjugation `tpd0.conj (MulAut.conj g)` — which transports *every* field of
`TypePData` (including `fitting_eq` and `secondDerived_le_fitting`) — again lands on `T`, with its
`U`-field equal to `V` and its `H`-field equal to `Q`.  This is the honest engine behind the
`fitting_eq`/`secondDerived_le_fitting`/`U_nilpotent` fields of `reconciled_typePData_T`. -/
theorem Hypothesis.exists_typePData_U_eq_V [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ d : TypePData hyp.T, d.U = hyp.V ∧ d.H = hyp.Q := by
  obtain ⟨tpd0⟩ := OddOrder.GroupTheory.typePData_of_isTypeNonI hyp.T_nonI
  have hQtpd : tpd0.H = hyp.Q := by rw [tpd0.H_eq, ← hyp.Q_eq_TF]
  have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
  have hU_le : tpd0.U ≤ derivedInG hyp.T := tpd0.U_le
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hQ_le_T : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  haveI hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
  -- `Q` complements `V` in `T'` (verbatim from `isNilpotent_V`).
  have hVcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (hyp.V.subgroupOf (derivedInG hyp.T)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
        OneMemClass.coe_one]
      refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
      have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) := ⟨hxQ, hxV⟩
      rwa [hyp.Q_inf_V_eq_bot, Subgroup.mem_bot] at hxQV
    · have hsup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
          (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.T_deriv_eq_QV.symm, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
        (hyp.V.subgroupOf (derivedInG hyp.T))
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  have hUcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (tpd0.U.subgroupOf (derivedInG hyp.T)) := by
    rw [← hQtpd]; exact tpd0.derived_complement
  have hcop : Nat.Coprime (Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)))
      ((hyp.Q.subgroupOf (derivedInG hyp.T)).index) := by
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.T
    rw [← hyp.Q_eq_TF] at hHall
    have h0 := OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_T).toEquiv] at h0
    have hcard : Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) = Nat.card ↥hyp.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv
    have hdvd : (hyp.Q.subgroupOf (derivedInG hyp.T)).index ∣
        (hyp.Q.subgroupOf hyp.T).index := by
      have htower : hyp.Q.relIndex (derivedInG hyp.T) *
          (derivedInG hyp.T).relIndex hyp.T = hyp.Q.relIndex hyp.T :=
        Subgroup.relIndex_mul_relIndex hyp.Q (derivedInG hyp.T) hyp.T hQ_le hM'_le_T
      show hyp.Q.relIndex (derivedInG hyp.T) ∣ hyp.Q.relIndex hyp.T
      exact ⟨(derivedInG hyp.T).relIndex hyp.T, htower.symm⟩
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right hdvd h0
  have hQ_lt_top : hyp.Q < ⊤ :=
    lt_of_le_of_lt hQ_le_T (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.T_maximal).1)
  haveI hQsolv : IsSolvable ↥hyp.Q := hG.solvable_of_lt_top hyp.Q hQ_lt_top
  have hsolv : IsSolvable ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) ∨
      IsSolvable (↥(derivedInG hyp.T) ⧸ hyp.Q.subgroupOf (derivedInG hyp.T)) :=
    Or.inl (solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQ_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQ_le).injective)
  obtain ⟨n, _hnQ, hn⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop hsolv hUcompl hVcompl
  -- The conjugator, coerced to `G`.
  set g : G := (↑n : G) with hgdef
  have hg_mem_T' : g ∈ derivedInG hyp.T := n.2
  have hg_mem_T : g ∈ hyp.T := hM'_le_T hg_mem_T'
  -- Lift the `subgroupOf`-level conjugacy `hn` to a `G`-level equation `conj g • U = V`.
  have hcomp : (derivedInG hyp.T).subtype.comp (MulAut.conj n).toMonoidHom
      = (MulAut.conj g).toMonoidHom.comp (derivedInG hyp.T).subtype := by
    ext k
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hgdef, Subgroup.coe_mul, Subgroup.coe_inv]
  have hUmap : tpd0.U.map (MulAut.conj g).toMonoidHom = hyp.V := by
    have key := congrArg (Subgroup.map (derivedInG hyp.T).subtype) hn
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hU_le, Subgroup.map_subgroupOf_eq_of_le hV_le] at key
    exact key
  have hUV : (MulAut.conj g) • tpd0.U = hyp.V := by
    rw [pointwise_mulAut_smul_eq_map]; exact hUmap
  -- Conjugation by `g ∈ T` fixes `T` and its normal `Q`.
  have hgT : (MulAut.conj g) • hyp.T = hyp.T := Subgroup.conj_smul_eq_self_of_mem hg_mem_T
  have hgQ : (MulAut.conj g) • hyp.Q = hyp.Q := by
    have hgN : ∀ h, h ∈ hyp.Q ↔ g * h * g⁻¹ ∈ hyp.Q := by
      have := Subgroup.mem_set_normalizer_iff.mp (hT_le_NQ hg_mem_T)
      simpa only [SetLike.mem_coe] using this
    ext x
    rw [Subgroup.pointwise_smul_def, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hgN y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (hgN (g⁻¹ * x * g)).mpr ?_, ?_⟩
      · rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x from by group]
      · show MulAut.conj g (g⁻¹ * x * g) = x
        simp only [MulAut.conj_apply]; group
  -- Whole-datum conjugation, cast back to `TypePData T`.  The `.U`/`.H` projections have constant
  -- codomain `Subgroup G`, so they commute with the `▸` cast on the index (proved by `subst` on a
  -- fresh index variable — `hgT` itself has `T` on both sides, so casing it directly fails).
  have hcastU : ∀ {S : Subgroup G} (h : S = hyp.T) (d : TypePData S), (h ▸ d).U = d.U := by
    intro S h d; subst h; rfl
  have hcastH : ∀ {S : Subgroup G} (h : S = hyp.T) (d : TypePData S), (h ▸ d).H = d.H := by
    intro S h d; subst h; rfl
  refine ⟨hgT ▸ tpd0.conj (MulAut.conj g), ?_, ?_⟩
  · rw [hcastU hgT, show (tpd0.conj (MulAut.conj g)).U = (MulAut.conj g) • tpd0.U from rfl, hUV]
  · rw [hcastH hgT, show (tpd0.conj (MulAut.conj g)).H = (MulAut.conj g) • tpd0.H from rfl, hQtpd,
      hgQ]

/-- **`M'` is a Hall subgroup of a type-`P` maximal** (`Coprime |M'| [M:M']`).  A `κ(M)`-Hall `K`
exists (`exists_isHallSubgroup_kappa_ge`, `X := ⊥`), is cyclic (Theorem 14.7 `typeP_duality`:
`K ⊔ K*` cyclic) and complements `M'` (`typeP_derivedInG_isComplement_kappaHall`); then
`coprime_card_derived_kappaHall_of_isComplement'` gives `(|M'|, |K|) = 1` with `|K| = [M : M']`.

This is the coprimality behind the Schur–Zassenhaus conjugacy of complements to `M'` — it is
**ungated** (needs only `IsTypeP M`), so the earlier belief that `p ∤ |T'|` requires
`FieldNormalizerData` (via `W2_card_coprime_Q_card`/`Q_elementaryAbelian`) was too pessimistic: the
`κ`-Hall route supplies it directly.  Used to align a type-`P` datum's `κ`-factor to any given
complement of `M'` (e.g. the abstract `W₂` on `T`, `W2_isComplement_T_deriv`). -/
theorem coprime_card_derivedInG_index_of_isTypeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : OddOrder.BG.Ch4.S14.IsTypeP M) :
    Nat.Coprime (Nat.card ↥(derivedInG M)) ((derivedInG M).subgroupOf M).index := by
  classical
  obtain ⟨K, hKM, hKhall, -⟩ :=
    OddOrder.BG.Ch4.S14.exists_isHallSubgroup_kappa_ge hG hM (bot_le (a := M))
      (fun q hq => by rw [Subgroup.card_bot] at hq; simp at hq)
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstar
  haveI hKcyc : IsCyclic ↥K := by
    obtain ⟨_, _, _, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hM hP hKM hKhall hKstar
    haveI : IsCyclic ↥(K ⊔ Kstar) := hcyc
    exact Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  have hcompl :=
    OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hKhall
  have hcop :=
    OddOrder.BG.Ch4.S14.coprime_card_derived_kappaHall_of_isComplement' hKhall hcompl
  have h1 : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv
  have h2 : Nat.card ↥(K.subgroupOf M) = ((derivedInG M).subgroupOf M).index :=
    (hcompl.symm.index_eq_card).symm
  rwa [h1, h2] at hcop

/-- **Fact A: `W₂` is a `κ`-Hall of `T`** (ungated).  `W₂` complements `T'`
(`W2_isComplement_T_deriv`); a produced `κ(T)`-Hall `K` (`exists_isHallSubgroup_kappa_ge`, cyclic,
also complementing `T'`) is `T`-conjugate to `W₂` by Schur–Zassenhaus
(`IsComplement'.exists_conj_of_coprime`, coprimality `coprime_card_derivedInG_index_of_isTypeP`);
Hall-ness transfers along the conjugation (`IsHallSubgroup.mulAut_smul`).  This discharges the `hFactA`
residual of `reconciled_typePData_T` with no `FieldNormalizerData`/(14.9) input. -/
theorem Hypothesis.W2_isKappaHall_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa hyp.T)
      (hyp.W2.subgroupOf hyp.T) := by
  classical
  have hP := OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.T_maximal hyp.T_nonI
  obtain ⟨K, hKM, hKhall, -⟩ :=
    OddOrder.BG.Ch4.S14.exists_isHallSubgroup_kappa_ge hG hyp.T_maximal (bot_le (a := hyp.T))
      (fun q hq => by rw [Subgroup.card_bot] at hq; simp at hq)
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (K : Set G) with hKstar
  haveI hKcyc : IsCyclic ↥K := by
    obtain ⟨_, _, _, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hyp.T_maximal hP hKM hKhall hKstar
    haveI : IsCyclic ↥(K ⊔ Kstar) := hcyc
    exact Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  have hcomplK :=
    OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hyp.T_maximal hP hKM hKhall
  haveI : IsSolvable ↥hyp.T := hG.solvable_of_mem_maximalSubgroups hyp.T_maximal
  haveI hNnorm : ((derivedInG hyp.T).subgroupOf hyp.T).Normal := by
    rw [show (derivedInG hyp.T).subgroupOf hyp.T = commutator ↥hyp.T from
      Subgroup.comap_map_eq_self_of_injective hyp.T.subtype_injective (commutator ↥hyp.T)]
    infer_instance
  have hcop : Nat.Coprime (Nat.card ↥((derivedInG hyp.T).subgroupOf hyp.T))
      ((derivedInG hyp.T).subgroupOf hyp.T).index := by
    have hderivM_le : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
    have hcard : Nat.card ↥((derivedInG hyp.T).subgroupOf hyp.T) = Nat.card ↥(derivedInG hyp.T) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hderivM_le).toEquiv
    rw [hcard]
    exact coprime_card_derivedInG_index_of_isTypeP hG hyp.T_maximal hP
  obtain ⟨n, -, hn⟩ := Subgroup.IsComplement'.exists_conj_of_coprime hcop (Or.inl inferInstance)
    hcomplK hyp.W2_isComplement_T_deriv
  have hHall := hKhall.mulAut_smul (MulAut.conj n)
  rw [pointwise_mulAut_smul_eq_map] at hHall
  rw [show ((MulAut.conj n).toMonoidHom : ↥hyp.T →* ↥hyp.T) = ↑(MulAut.conj n) from rfl] at hn
  rwa [hn] at hHall

/-- **A complement of `M'` in a type-`P` maximal is a `κ(M)`-Hall subgroup** (ungated, generic).
Extracted from the `W₂`/`T` argument (`W2_isKappaHall_T`): a produced `κ(M)`-Hall `K` is cyclic and
complements `M'` (`typeP_derivedInG_isComplement_kappaHall`); Schur–Zassenhaus
(`coprime_card_derivedInG_index_of_isTypeP`) conjugates it onto any given complement `W` of `M'` in
`M`, and Hall-ness transfers along the conjugation (`IsHallSubgroup.mulAut_smul`).  Used for the
`S`-side Fact A (`W₁` κ-Hall of `S`, via the carried `Sdata.M_complement`). -/
theorem isKappaHall_of_isComplement_derivedInG [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M W : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : OddOrder.BG.Ch4.S14.IsTypeP M)
    (hWcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (W.subgroupOf M)) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (W.subgroupOf M) := by
  classical
  obtain ⟨K, hKM, hKhall, -⟩ :=
    OddOrder.BG.Ch4.S14.exists_isHallSubgroup_kappa_ge hG hM (bot_le (a := M))
      (fun q hq => by rw [Subgroup.card_bot] at hq; simp at hq)
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstar
  haveI hKcyc : IsCyclic ↥K := by
    obtain ⟨_, _, _, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hM hP hKM hKhall hKstar
    haveI : IsCyclic ↥(K ⊔ Kstar) := hcyc
    exact Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  have hcomplK :=
    OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hKhall
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  haveI hNnorm : ((derivedInG M).subgroupOf M).Normal := by
    rw [show (derivedInG M).subgroupOf M = commutator ↥M from
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)]
    infer_instance
  have hcop : Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M))
      ((derivedInG M).subgroupOf M).index := by
    have hderivM_le : derivedInG M ≤ M := Subgroup.map_subtype_le _
    have hcard : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hderivM_le).toEquiv
    rw [hcard]
    exact coprime_card_derivedInG_index_of_isTypeP hG hM hP
  obtain ⟨n, -, hn⟩ := Subgroup.IsComplement'.exists_conj_of_coprime hcop (Or.inl inferInstance)
    hcomplK hWcompl
  have hHall := hKhall.mulAut_smul (MulAut.conj n)
  rw [pointwise_mulAut_smul_eq_map] at hHall
  rw [show ((MulAut.conj n).toMonoidHom : ↥M →* ↥M) = ↑(MulAut.conj n) from rfl] at hn
  rwa [hn] at hHall

/-- **Fact A (`S`-side): `W₁` is a `κ`-Hall of `S`** (ungated).  `W₁` complements `S'`
(the carried `Sdata.M_complement`, reconciled to `W₁` via `Sdata_W1_eq`), so
`isKappaHall_of_isComplement_derivedInG` applies.  The `S`-side companion of `W2_isKappaHall_T`,
used to feed `typeP_duality`/`exists_partner`/`kappaHall_primes_subset_sigma_partner` on `S`. -/
theorem Hypothesis.W1_isKappaHall_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa hyp.S)
      (hyp.W1.subgroupOf hyp.S) := by
  have hPS := OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.S_maximal hyp.S_nonI
  have hW1compl : Subgroup.IsComplement' ((derivedInG hyp.S).subgroupOf hyp.S)
      (hyp.W1.subgroupOf hyp.S) := by
    have h := hyp.Sdata.M_complement
    rwa [hyp.Sdata_W1_eq] at h
  exact isKappaHall_of_isComplement_derivedInG hG hyp.S_maximal hPS hW1compl

/-- **Fact B (`S`-side): `M_σ(S) ⊓ C_G(W₁) = W₂`** (the (8.4.d) centralizer law for `S`, ungated).
`⊆`: `M_σ(S) ≤ S'` (`Msigma_le_derived`), then `S' ⊓ C(W₁) = W₂` is the carried datum
`Sdata.derivedInG_inf_centralizer_W1_eq` (reconciled via `Sdata_W1_eq`/`Sdata_W2_eq`).  `⊇`:
`W₂ = Sdata.W2 ≤ Sdata.H = M_F(S) = M_σ(S)` (type-II `S`, `maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II`)
and `W₂ ≤ C(W₁)` (`W1_commutes_W2`).  This is the `Kstar = W₂` identification that lets
`typeP_duality`/`typeP_partner_structure` on `S` output Fact B (`W₁ = M_σ(Mstar) ⊓ C(W₂)`) for the
partner. -/
theorem Hypothesis.Msigma_S_inf_centralizer_W1_eq_W2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.BG.Ch3.S10.Msigma hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G) = hyp.W2 := by
  classical
  have hSder : derivedInG hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G) = hyp.W2 := by
    have h := hyp.Sdata.derivedInG_inf_centralizer_W1_eq
    rw [hyp.Sdata_W1_eq, hyp.Sdata_W2_eq] at h
    exact h
  have hMFeq : maxNilpotentNormalHall hyp.S = OddOrder.BG.Ch3.S10.Msigma hyp.S :=
    OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG hyp.S_maximal
      (Or.inr (OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2))
  refine le_antisymm ?_ (le_inf ?_ ?_)
  · calc OddOrder.BG.Ch3.S10.Msigma hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G)
        ≤ derivedInG hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G) :=
          inf_le_inf_right _ (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hyp.S_maximal)
      _ = hyp.W2 := hSder
  · rw [← hMFeq]
    calc hyp.W2 = hyp.Sdata.W2 := hyp.Sdata_W2_eq.symm
      _ ≤ hyp.Sdata.H := le_trans hyp.Sdata.W2_le inf_le_left
      _ = maxNilpotentNormalHall hyp.S := hyp.Sdata.H_eq
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hyp.W1_commutes_W2 x hx y hy

/-- **`opiCoreInG` is conjugation-equivariant** (public form of the S14/S10 private helpers, needed
for the `Msigma` conjugation used in the `S15` pairing carve-out).  `φ • O_π(H) = O_π(φ • H)` via
`oPiCore.map_eq_of_mulEquiv` transported along the conjugation isomorphism `↥H ≃* ↥(φ • H)`. -/
theorem opiCoreInG_conj_smul [Finite G] (π : Set ℕ) (φ : MulAut G) (H : Subgroup G) :
    φ • OddOrder.GroupTheory.opiCoreInG π H
      = OddOrder.GroupTheory.opiCoreInG π (φ • H) := by
  have hHmap : H.map (φ : G →* G) = φ • H := (pointwise_mulAut_smul_eq_map φ H).symm
  let e : ↥H ≃* ↥(φ • H) :=
    (Subgroup.equivMapOfInjective H (φ : G →* G) φ.injective).trans
      (MulEquiv.subgroupCongr hHmap)
  have hcomp : (φ • H).subtype.comp (e : ↥H →* ↥(φ • H)) = (φ : G →* G).comp H.subtype := by
    ext x; rfl
  calc φ • OddOrder.GroupTheory.opiCoreInG π H
      = (OddOrder.GroupTheory.opiCoreInG π H).map (φ : G →* G) := pointwise_mulAut_smul_eq_map φ _
    _ = ((OddOrder.Isaacs.Ch03.oPiCore π ↥H).map H.subtype).map (φ : G →* G) := rfl
    _ = (OddOrder.Isaacs.Ch03.oPiCore π ↥H).map ((φ : G →* G).comp H.subtype) := by
        rw [Subgroup.map_map]
    _ = (OddOrder.Isaacs.Ch03.oPiCore π ↥H).map
          ((φ • H).subtype.comp (e : ↥H →* ↥(φ • H))) := by rw [hcomp]
    _ = ((OddOrder.Isaacs.Ch03.oPiCore π ↥H).map (e : ↥H →* ↥(φ • H))).map
          (φ • H).subtype := by rw [← Subgroup.map_map]
    _ = (OddOrder.Isaacs.Ch03.oPiCore π ↥(φ • H)).map (φ • H).subtype := by
        rw [OddOrder.Isaacs.Ch03.oPiCore.map_eq_of_mulEquiv]

/-- **`M_σ` is conjugation-equivariant** (`M_σ(Mᵍ) = M_σ(M)ᵍ`, public form).  From
`opiCoreInG_conj_smul` and `sigma_conj_smul_eq` (`σ(Mᵍ) = σ(M)`). -/
theorem Msigma_conj_smul_eq [Finite G] (g : G) (M : Subgroup G) :
    OddOrder.BG.Ch3.S10.Msigma (MulAut.conj g • M)
      = MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M := by
  simp only [OddOrder.BG.Ch3.S10.Msigma]
  rw [OddOrder.BG.Ch4.S14.sigma_conj_smul_eq, ← opiCoreInG_conj_smul]

/-- **Fact B (`T`-side): `W₁ = M_σ(T) ⊓ C_G(W₂)`** (the (8.4.d)-dual centralizer law for `T`, ungated
via the type-`P` pairing — Coq `PFsection8` `typeP_cent_compl`/`FTtypeP_pair_witness`).

This is the last residual of `reconciled_typePData_T` (issue 9073); it is genuine §13 pairing content
proved *without* assuming `(14.9)`/`IsTypeII T`, by descending to `S`'s type-`P` structure:

* Apply `typeP_duality`/`exists_partner`/`typeP_partner_structure` to `S` (`hKS` = Fact A for `S`,
  `hKstarSW2` = Fact B for `S`, `Kstar = W₂`): the partner `Mstar` satisfies Fact B *for* `Mstar`,
  `W₁ = M_σ(Mstar) ⊓ C(W₂)` (`hKeq`), plus `W₂` is a `κ`-Hall of `Mstar` and the pair is
  nonconjugate to `S`.
* `Mstar` is `G`-conjugate to `T`: `theorem88_caseB` at `Mstar` (type-`P`, non-`I`, `≁ S`) leaves
  only `∃g, Mstarᵍ = T`.
* `⊇`: `q ∈ σ(Mstar) = σ(T)` (`kappaHall_primes_subset_sigma_partner` + `sigma_conj_smul_eq`), so the
  `q`-group `W₁ ≤ T` lands in the normal Hall `σ(T)`-subgroup `M_σ(T)`
  (`sigma_subgroup_le_Msigma_of_isHall`), and `W₁ ≤ C(W₂)` (`W1_commutes_W2`).
* `⊆`/cardinality: a fix-`W` correction (`exists_conj_eq_of_isHall_subgroupOf`, matching the two
  `κ`-Halls `W₂` of `T`, `Mstar`) gives `n` with `Tⁿ = Mstar`, `W₂ⁿ = W₂`, whence
  `(M_σ(T) ⊓ C(W₂))ⁿ = M_σ(Mstar) ⊓ C(W₂) = W₁`, so `|M_σ(T) ⊓ C(W₂)| = |W₁|`; with `⊇` and
  `eq_of_le_of_card_ge` this forces equality. -/
theorem Hypothesis.W1_eq_Msigma_T_inf_centralizer_W2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.W1 = OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set G) := by
  classical
  -- `S`-side data.
  have hPS := OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.S_maximal hyp.S_nonI
  have hW1S : hyp.W1 ≤ hyp.S :=
    (by rw [hyp.W_eq_join]; exact le_sup_left : hyp.W1 ≤ hyp.W).trans
      (by rw [hyp.W_eq_inter]; exact inf_le_left)
  have hW2T : hyp.W2 ≤ hyp.T :=
    (by rw [hyp.W_eq_join]; exact le_sup_right : hyp.W2 ≤ hyp.W).trans
      (by rw [hyp.W_eq_inter]; exact inf_le_right)
  have hKS := hyp.W1_isKappaHall_S hG
  set KstarS : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G) with hKstarSdef
  have hKstarSW2 : KstarS = hyp.W2 := by
    rw [hKstarSdef]; exact hyp.Msigma_S_inf_centralizer_W1_eq_W2 hG
  haveI : IsSolvable ↥hyp.S := hG.solvable_of_mem_maximalSubgroups hyp.S_maximal
  obtain ⟨US, hUS'⟩ := OddOrder.Isaacs.Ch03.hall_E_exists (G := ↥hyp.S)
    ((OddOrder.BG.Ch4.S14.kappa hyp.S ∪ OddOrder.BG.Ch3.S10.sigma hyp.S)ᶜ)
  have hU_S : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa hyp.S ∪ OddOrder.BG.Ch3.S10.sigma hyp.S)ᶜ)
      ((US.map hyp.S.subtype).subgroupOf hyp.S) := by
    have hUSeq : (US.map hyp.S.subtype).subgroupOf hyp.S = US :=
      Subgroup.comap_map_eq_self_of_injective hyp.S.subtype_injective US
    rw [hUSeq]; exact hUS'
  -- Partner `Mstar` of `S` (Theorem 14.7), with Fact B *for* `Mstar`.
  obtain ⟨Mstar, hMstarne, hmem, hpart⟩ :=
    OddOrder.BG.Ch4.S14.exists_partner hG (OddOrder.BG.Ch4.S14.dummySigmaDecomposition G)
      hyp.S_maximal hPS hW1S hKS hKstarSdef hU_S
  obtain ⟨hMstarmax, hMstarP, hKstarleMstar, hKstar_hall, hKeq⟩ :=
    OddOrder.BG.Ch4.S14.typeP_partner_structure hG hyp.S_maximal hPS hW1S hKS hKstarSdef hU_S
      hmem hMstarne hpart
  rw [hKstarSW2] at hKeq hKstarleMstar hKstar_hall
  -- `hKeq : W₁ = M_σ(Mstar) ⊓ C(W₂)`; `hKstar_hall : W₂ κ-Hall of Mstar`; `W₂ ≤ Mstar`.
  have hncSMstar : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup hyp.S Mstar :=
    OddOrder.BG.Ch4.S14.typeP_family_pairwise_nonconjugate hG hyp.S_maximal hPS hW1S hKS
      hKstarSdef hU_S (Or.inl rfl) hmem (Ne.symm hMstarne)
  have hMstarNotI : ¬ OddOrder.GroupTheory.IsTypeI Mstar := by
    intro hI
    exact absurd ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hMstarmax).1.mp hI)
      (Set.nonempty_iff_ne_empty.mp hMstarP)
  -- `Mstar` is `G`-conjugate to `T`.
  obtain ⟨g, hg⟩ : ∃ g : G, MulAut.conj g • Mstar = hyp.T := by
    rcases hyp.theorem88_caseB Mstar hMstarmax with hI | hS | hT
    · exact absurd hI hMstarNotI
    · exact absurd
        (OddOrder.BG.Ch4.S14.IsConjugateSubgroup.symm
          (hS : OddOrder.BG.Ch4.S14.IsConjugateSubgroup Mstar hyp.S)) hncSMstar
    · exact hT
  -- `q ∈ σ(T)`, hence `W₁ ≤ M_σ(T)` (normal Hall `σ`-subgroup contains every `σ`-subgroup).
  have hqK : hyp.q ∣ Nat.card ↥hyp.W1 := ⟨1, by rw [mul_one]; exact hyp.q_eq_card_W1.symm⟩
  have hqMstar : hyp.q ∈ OddOrder.BG.Ch3.S10.sigma Mstar :=
    OddOrder.BG.Ch4.S14.kappaHall_primes_subset_sigma_partner hG hyp.S_maximal hPS hW1S hKS
      hKstarSdef hU_S hpart hyp.q_prime hqK
  have hqT : hyp.q ∈ OddOrder.BG.Ch3.S10.sigma hyp.T := by
    rw [← hg, OddOrder.BG.Ch4.S14.sigma_conj_smul_eq]; exact hqMstar
  have hW1T : hyp.W1 ≤ hyp.T :=
    (by rw [hyp.W_eq_join]; exact le_sup_left : hyp.W1 ≤ hyp.W).trans
      (by rw [hyp.W_eq_inter]; exact inf_le_right)
  have hW1piT : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup
      (OddOrder.BG.Ch3.S10.sigma hyp.T) hyp.W1 := by
    intro r hr
    have hpf : (Nat.card ↥hyp.W1).primeFactors = {hyp.q} := by
      rw [← hyp.q_eq_card_W1, Nat.Prime.primeFactors hyp.q_prime]
    rw [hpf, Finset.mem_singleton] at hr
    rw [hr]; exact hqT
  have hW1MsigmaT : hyp.W1 ≤ OddOrder.BG.Ch3.S10.Msigma hyp.T :=
    OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hyp.T_maximal) hW1T hW1piT
  have hSupset : hyp.W1 ≤ OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set G) :=
    le_inf hW1MsigmaT (by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hyp.W1_commutes_W2 x hx y hy).symm.eq)
  -- fix-`W` correction: a conjugator `n` with `Tⁿ = Mstar` and `W₂ⁿ = W₂`.
  have hg0 : MulAut.conj g⁻¹ • hyp.T = Mstar := by
    rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hW2hallT := hyp.W2_isKappaHall_T hG
  have hconjW2hall := OddOrder.BG.Ch4.S14.isHall_kappa_subgroupOf_conj g⁻¹ hg0 hW2T hW2hallT
  have hconjW2le : MulAut.conj g⁻¹ • hyp.W2 ≤ Mstar := by
    rw [← hg0]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hW2T
  haveI : IsSolvable ↥Mstar := hG.solvable_of_mem_maximalSubgroups hMstarmax
  obtain ⟨w, hwMstar, hw⟩ := OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf
    inferInstance hconjW2le hKstarleMstar hconjW2hall hKstar_hall
  set n : G := w * g⁻¹ with hn_def
  have hnW2 : MulAut.conj n • hyp.W2 = hyp.W2 := by
    rw [hn_def, map_mul, mul_smul]; exact hw
  have hnT : MulAut.conj n • hyp.T = Mstar := by
    rw [hn_def, map_mul, mul_smul, hg0]
    exact conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hwMstar)
  -- `(M_σ(T) ⊓ C(W₂))ⁿ = M_σ(Mstar) ⊓ C(W₂) = W₁`.
  have hconj_eq : MulAut.conj n •
      (OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set G)) = hyp.W1 := by
    rw [Subgroup.smul_inf, centralizer_pointwise_smul, ← coe_pointwise_smul, hnW2,
      ← Msigma_conj_smul_eq, hnT]
    exact hKeq.symm
  -- cardinality: `|M_σ(T) ⊓ C(W₂)| = |W₁|`, and with `⊇`, equality.
  have hcard : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓
      Subgroup.centralizer (hyp.W2 : Set G)) = Nat.card ↥hyp.W1 := by
    rw [← hconj_eq, Subgroup.pointwise_smul_def]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj n).injective).toEquiv
  exact Subgroup.eq_of_le_of_card_ge hSupset (le_of_eq hcard)

/-- **`reconciled_typePData_T` の 2 residual を pairing facts から** (Fact A ∧ Fact B → 両 field, 実証明).
`W₂` が `T` の `κ`-Hall (**Fact A**) かつ `W₁ = M_σ(T) ⊓ C(W₂)` (**Fact B**) — `typeP_partner_structure`
(`S14`) が `S` の partner に対して供給する 2 つの (8.4.d)-dual pairing facts — があれば、既存の一般
type-`P` 機構 (`typeP_kstar_in_mf` / `typeP_derivedInG_inf_centralizer_kappaElement_eq`, いずれも
`M := T`, `K := W₂`, `K* := W₁`) が `reconciled_typePData_T` の両 field を discharge する:
`W₁ ≤ Q ⊓ T''` (`W2_le` field) と `∀ x ∈ W₂#, T' ⊓ C(x) = W₁` (`centralizer_W1` field)。

これは gated-endpoint skeleton (issue 9073): 2 sorry を **精密な pairing 2 facts** (κ-Hall + Kstar 同定)
に還元し、その **十分性を実証明で verify**。残余 Fact A + Fact B は `typeP_partner_structure` を `S` に
適用 (κ-Hall `W₁`, `Kstar = M_σ(S)⊓C(W₁) = W₂`) すれば partner `Mstar = T` に対し供給される
(S-side κ-Hall setup + Z-family covering の wiring が次段)。 -/
theorem Hypothesis.reconciled_residuals_of_pairing_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hFactA : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa hyp.T)
      (hyp.W2.subgroupOf hyp.T))
    (hFactB : hyp.W1 = OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set G)) :
    hyp.W1 ≤ hyp.Q ⊓ secondDerivedInAmbient hyp.T ∧
      (∀ x ∈ hyp.W2, x ≠ 1 →
        derivedInG hyp.T ⊓ Subgroup.centralizer ({x} : Set G) = hyp.W1) := by
  have hW2T : hyp.W2 ≤ hyp.T :=
    (by rw [hyp.W_eq_join]; exact le_sup_right : hyp.W2 ≤ hyp.W).trans
      (by rw [hyp.W_eq_inter]; exact inf_le_right)
  have hP := OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.T_maximal hyp.T_nonI
  refine ⟨?_, ?_⟩
  · -- `W2_le`: `W₁ = K* ≤ M_F(T) ⊓ T''` from `typeP_kstar_in_mf` (Corollary 15.6).
    have hk := OddOrder.BG.Ch4.S15.typeP_kstar_in_mf hG hyp.T_maximal hP hW2T hFactA hFactB
    rw [hyp.Q_eq_TF]
    exact le_inf hk.2.2.1 hk.2.2.2.1
  · -- `centralizer_W1`: `T' ⊓ C(x) = K* = W₁` for `x ∈ W₂#` (Theorem A(5) + Dedekind).
    exact OddOrder.BG.Ch4.S16.typeP_derivedInG_inf_centralizer_kappaElement_eq
      hG hyp.T_maximal hP hW2T hFactA hFactB

/-- **T-side type-`P` structure reconciled to the abstract `V`/`W₂`** (the honest replacement for the
withdrawn `Tdata` spine carrier; HUB tick² 2026-06-30).  `T` is type non-I (`T_nonI`), hence type-`P`,
and the §16-chosen complement `V` (κ-Hall-invariant) / cyclic factor `W₂` form a type-`P`
decomposition of `T`: there is a `TypePData T` with `.U = V`, `.W1 = W₂`, and `.W2 = W₁` (the dual
cyclic factor `C_{T'}(W₂#)` of `T`'s type-`P` structure is exactly the shared `W₁`).

This is the genuine §13 reconciliation — **TRUE**, and the right §13-level statement: it asserts only
the *general* type-`P` structure of `T` (available from `T_nonI` at §13), reconciled to the abstract
`V`/`W₂`.  (The sharper `IsTypeP2 T` is *equivalent* to the (14.9) conclusion `IsTypeII T` by the BG
type dictionary `proposition_type_classification` — `IsTypeII M ↔ IsTypeP2 M` — but is not needed for
the reconciliation itself, so this stays a clean §13 obligation.)  It lives **off the FT spine**: the
`V`-side helpers cite this obligation, keeping `section16TypePStructure_of_isMinimalSimpleOdd`
sorry-free.  Gated on §13; declared sorried.  (Relocated from `S15_SAndT` for the (13.9)/(13.10)
counting layer — the type-V exclusion of `Q_sharp_isTISubset` and the `|T|` decomposition read it.) -/
theorem reconciled_typePData_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : TypePData hyp.T, data.U = hyp.V ∧ data.W1 = hyp.W2 ∧ data.W2 = hyp.W1 := by
  -- `W₂, W₁ ≤ W` from the (13.1) join `W = W₁ ⊔ W₂`, and `W ≤ T` from `W = S ⊓ T`.
  have hW2W : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hWT : hyp.W ≤ hyp.T := by rw [hyp.W_eq_inter]; exact inf_le_right
  haveI hWcyc : IsCyclic ↥hyp.W := hyp.W_cyclic
  -- Cyclic factors: a subgroup of the cyclic `W` is cyclic (transport along `subgroupOfEquivOfLe`).
  have hW2cyc : IsCyclic ↥hyp.W2 :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hW2W).surjective
  have hW1cyc : IsCyclic ↥hyp.W1 :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hW1W).surjective
  -- **(8.4.d)-dual pairing residuals** for the `W2_le`/`centralizer_W1` fields.  These are exactly the
  -- two facts `typeP_partner_structure` (applied to `S`) supplies for its partner `T`: `W₂` a `κ`-Hall
  -- of `T` (**Fact A**) and `W₁ = M_σ(T) ⊓ C(W₂)` (**Fact B**).  Their *sufficiency* is verified by
  -- `reconciled_residuals_of_pairing_facts` (via `typeP_kstar_in_mf` /
  -- `typeP_derivedInG_inf_centralizer_kappaElement_eq`); the two residuals are honestly gated on the
  -- §13 `typeP_partner` port (issue 9073) whose remaining step wires `typeP_partner_structure`'s inputs
  -- (S-side κ-Hall + Z-family covering) from the abstract `Hypothesis`.
  -- **Fact A** (`W₂` κ-Hall of `T`) is now proven ungated (`W2_isKappaHall_T`, via the produced
  -- κ-Hall + Schur–Zassenhaus).  **Fact B** (`W₁ = M_σ(T) ⊓ C(W₂)`) remains the sole residual — the
  -- reverse cyclic-factor identification, supplied by `typeP_partner_structure` applied to `S`.
  have hFactA := hyp.W2_isKappaHall_T hG
  have hFactB : hyp.W1 =
      OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set G) :=
    hyp.W1_eq_Msigma_T_inf_centralizer_W2 hG
  obtain ⟨hW2le_pf, hCentW1_pf⟩ := hyp.reconciled_residuals_of_pairing_facts hG hFactA hFactB
  refine ⟨{
    H := hyp.Q
    U := hyp.V
    W1 := hyp.W2
    W2 := hyp.W1
    W := hyp.W
    H_eq := hyp.Q_eq_TF
    H_le := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
    U_le := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
    W1_le := hW2W.trans hWT
    -- **Precise residual (`W2_le`, goal `hyp.W1 ≤ hyp.Q ⊓ secondDerivedInAmbient hyp.T`).**
    -- This is the T-side dual of the *carried* S-side field `Sdata.W2_le` (`W₂ ≤ P ⊓ S''`).  Both
    -- halves are `IsTypeP2 hyp.T` (≡ `IsTypeII hyp.T`, BG (14.9))-gated, which is unavailable at
    -- §13 (`IsTypeII hyp.T` lives in `S16` = import-downstream; see `T_typeII`):
    --   • `hyp.W1 ≤ hyp.Q`: needs `hyp.q ∣ Nat.card ↥hyp.Q`; every route (`card_Q_eq`,
    --     `exists_sylow_coe_eq_Q`, `pgroup_le_of_normal_coprime_index` dualizing `W2_le_P`) requires
    --     `IsTypeII hyp.T` — `q ∣ |Q|` is provably NOT derivable from `hG`+`hyp` alone.  (The S-side
    --     `W2_le_P` is likewise NOT type-free: it consumes `|P| = p^q` from `card_P_eq`, which uses
    --     the *carried* `S_typeP2` field.  `T` has no analogous carrier.)
    --   • `hyp.W1 ≤ secondDerivedInAmbient hyp.T`: needs the intrinsic identification
    --     `hyp.W1 = tpd.W2 = C_{T'}(W₂#)` for a type-`P` datum `tpd` whose `.W1 = W₂`.  The datum
    --     `d` from `exists_typePData_U_eq_V` only pins `d.U = V`, `d.H = Q` (the Schur–Zassenhaus
    --     conjugator controls the *complement*, not the cyclic factors), so `d.W1`/`d.W2` need not be
    --     the abstract `W₂`/`W₁`.  The alignment is the `typeP_pair` content (Coq PFsection8
    --     `FTtypeP_pair_witness`/`of_typeP_pair`: the shared `W = S ⊓ T` forces T's swapped
    --     decomposition `xdefW : W₂ \x W₁ = W`, whose (8.4.d) component gives `W₁ ⊆ H ⊓ T''`) —
    --     unported to Lean, and equivalent to supplying `IsTypeP2 hyp.T`.
    -- Discharged from the pairing residuals `hFactA`/`hFactB` via the verified reduction
    -- `reconciled_residuals_of_pairing_facts` (`typeP_kstar_in_mf`: `K* ≤ M_F ⊓ M''`).  See the
    -- preamble; the residual is now the precise Fact A + Fact B (`typeP_partner_structure` inputs).
    W2_le := hW2le_pf
    W_eq := by rw [hyp.W_eq_join, sup_comm]
    W_cyclic := hyp.W_cyclic
    W1_nontrivial := by
      intro h; have hp := hyp.p_prime.one_lt
      rw [hyp.p_eq_card_W2, h, Subgroup.card_bot] at hp; exact absurd hp (by norm_num)
    W2_nontrivial := by
      intro h; have hq := hyp.q_prime.one_lt
      rw [hyp.q_eq_card_W1, h, Subgroup.card_bot] at hq; exact absurd hq (by norm_num)
    W1_cyclic := hW2cyc
    W2_cyclic := hW1cyc
    -- `T = T' ⋊ W₂`: the honest field `W2_isComplement_T_deriv` (ungated, threaded from the §16
    -- `typeP_derivedInG_isComplement_kappaHall`).  No longer `sorry`.
    M_complement := hyp.W2_isComplement_T_deriv
    W1_normalizes_U := hyp.W2_normalizes_V
    U_nilpotent := hyp.isNilpotent_V hG
    -- `V` complements `Q = T_F` in `T'`: disjointness is the honest field `Q_inf_V_eq_bot`
    -- (ungated, threaded from the §16 `exists_kappaHall_invariant_complement_to_MF`); the join
    -- `Q ⊔ V = T'` is `T_deriv_eq_QV`.  No longer `sorry`.
    derived_complement := by
      have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
      have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
      have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
      have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
        rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
      haveI hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · rw [disjoint_iff]
        ext ⟨x, hx⟩
        simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
          OneMemClass.coe_one]
        refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
        have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) := ⟨hxQ, hxV⟩
        rwa [hyp.Q_inf_V_eq_bot, Subgroup.mem_bot] at hxQV
      · have hsup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
            (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
          rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.T_deriv_eq_QV.symm, Subgroup.subgroupOf_self]
        have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
          (hyp.V.subgroupOf (derivedInG hyp.T))
        rw [hsup, Subgroup.coe_top] at hmul
        exact hmul.symm
    H_noncyclic := by
      -- `H := Q = maxNilpotentNormalHall T` is the *intrinsic* Fitting Hall (choice-independent),
      -- so `¬ IsCyclic ↥Q` is read off any type-`P` datum on `T`.  The §13-level producer
      -- `typePData_of_isTypeNonI T_nonI` supplies one (no `T_typeII`/(14.9) needed, keeping this a
      -- clean §13 obligation): its `H_noncyclic` is `¬ IsCyclic` of the same subgroup `Q`.
      obtain ⟨tpd0⟩ := OddOrder.GroupTheory.typePData_of_isTypeNonI hyp.T_nonI
      have hHeq : tpd0.H = hyp.Q := by rw [tpd0.H_eq, hyp.Q_eq_TF]
      exact hHeq ▸ tpd0.H_noncyclic
    -- `T`-side (8.5.a) Fitting containment/identity, transported from *any* type-`P` datum on `T`
    -- whose complement is `V` and whose kernel is `Q` (`exists_typePData_U_eq_V`, honest whole-datum
    -- conjugation via `TypePData.conj`).  No longer gated: these are genuine consequences of `T_nonI`.
    secondDerived_le_fitting := by
      obtain ⟨d, hU, hH⟩ := hyp.exists_typePData_U_eq_V hG
      have := d.secondDerived_le_fitting; rwa [hH, hU] at this
    fitting_eq := by
      obtain ⟨d, hU, hH⟩ := hyp.exists_typePData_U_eq_V hG
      have := d.fitting_eq; rwa [hH, hU] at this
    -- **Precise residual (`centralizer_W1`, goal after instantiation `W1 := hyp.W2`, `W2 := hyp.W1`,
    -- `M := hyp.T`): `∀ x ∈ hyp.W2, x ≠ 1 → derivedInG hyp.T ⊓ Subgroup.centralizer ({x}) = hyp.W1`.**
    -- This is the dual cyclic-factor law `C_{T'}(W₂#) = W₁` (Coq (8.4.d) `{in W1^#, C_M'[·] = W2}`
    -- with the swapped `xdefW`).  It is the T-side reflection of the *carried* S-side field
    -- `Sdata.centralizer_W1` (`∀ x ∈ W₁#, S' ⊓ C(x) = W₂`; see its use in
    -- `normalizer_U_inf_W2_eq_bot_of_data`, which crucially also cites the carried `Sdata_W2_eq`).
    -- The ungated general-type-`P` centralizer law `typeP_centralizer_kappaElement_eq`
    -- (`M ⊓ C_G(k) = K ⊔ K*` for `k ∈ K#`, only `IsTypeP M`) would apply to `T` with `K := W₂`,
    -- but ONLY once `W₂` is known to be a κ-Hall of `T` and `K* = M_σ(T) ⊓ C(W₂) = W₁` — precisely
    -- the `typeP_pair` reconciliation (≡ `IsTypeP2 hyp.T`), which the abstract `Hypothesis` does not
    -- carry (no `Tdata`).  Discharged from `hFactA`/`hFactB` via the verified reduction
    -- `reconciled_residuals_of_pairing_facts` (`typeP_derivedInG_inf_centralizer_kappaElement_eq`).
    centralizer_W1 := hCentW1_pf
    normalizer_V := by
      -- The `W`-exceptional-set normalizer `N_G(X) = W` is symmetric in `W₁`/`W₂`, so it is read off
      -- the S-side carrier `Sdata.normalizer_V` (same fact as `base_W_normalizer_V`, inlined since S15
      -- is upstream of S16).  The exceptional set `W − (W₂ ∪ W₁) = W − (W₁ ∪ W₂)` is `union_comm`.
      have hWeq : hyp.Sdata.W = hyp.W := by
        rw [hyp.Sdata.W_eq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq]; exact hyp.W_eq_join.symm
      intro X hX hXsub
      rw [← hWeq]
      refine hyp.Sdata.normalizer_V X hX ?_
      rw [hWeq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq, Set.union_comm]
      exact hXsub
  }, rfl, rfl, rfl⟩

/-- **`Q^#` is a TI-subset of `G` with normalizer `T`** — the `T`-side mirror of
`H_sharp_isTISubset`, feeding the (13.10.2)/(13.10.3) `Q`-orbit counting.  For `T` of type
II/III/IV the TI property is the `TypePNontrivialCore` field of the type datum (Peterfalvi
(8.6.a)), with the bound pinned to `T` by `normalizer_Q_eq_T`; type V is excluded by `|V| ≠ 1`
(a type-V witness has `U = ⊥`, and `|V| = |tpd.U|` for the reconciled datum by the
witness-independence `card_U_eq_index`). -/
theorem Q_sharp_isTISubset [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    IsTISubset (sharpSubgroup hyp.Q) hyp.T := by
  classical
  have hQnorm : Subgroup.normalizer (hyp.Q : Set G) = hyp.T := normalizer_Q_eq_T hG hyp
  have hcore : ∀ tpd : TypePData hyp.T, TypePNontrivialCore hyp.T tpd →
      IsTISubset (sharpSubgroup hyp.Q) hyp.T := by
    intro tpd hcore
    have hTI := hcore.2.2
    rw [← hyp.Q_eq_TF] at hTI
    rwa [hQnorm] at hTI
  rcases hyp.T_nonI with h | h | h | h
  · exact hcore h.some.typeP h.some.common
  · exact hcore h.some.typeP h.some.common
  · exact hcore h.some.typeP h.some.common
  · -- Type V: excluded by `v·d = |V| ≠ 1`.
    exfalso
    obtain ⟨tpd, hU, -, -⟩ := reconciled_typePData_T hG hyp
    have vdata := h.some
    have hcardU : Nat.card ↥tpd.U = Nat.card ↥vdata.typeP.U := by
      rw [tpd.card_U_eq_index, vdata.typeP.card_U_eq_index]
    rw [hU, vdata.U_eq_bot, Subgroup.card_bot, hyp.card_V_eq_vd] at hcardU
    exact hvd hcardU

/-- **(13.2.a)-on-`T`, router form**: `T` is of type II, III or IV — the `T_nonI` classification
minus type V, which is excluded by `|V| = v·d ≠ 1` (a type-V witness has `U = ⊥`, and `|V| =
|tpd.U|` for the reconciled datum by the witness-independence `card_U_eq_index`; the same
exclusion as `Q_sharp_isTISubset`).  This is what the §9 machinery's `TypesIIIIIIVSetup.type_alt`
consumes — the finer (13.2.a) "II or III" (type-IV exclusion, Pf (11.9.b,c) on `T`) is not needed
for the router. -/
theorem Hypothesis.T_typeII_or_III_or_IV [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    IsTypeII hyp.T ∨ IsTypeIII hyp.T ∨ IsTypeIV hyp.T := by
  rcases hyp.T_nonI with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    obtain ⟨tpd, hU', -, -⟩ := reconciled_typePData_T hG hyp
    have vdata := h.some
    have hcardU : Nat.card ↥tpd.U = Nat.card ↥vdata.typeP.U := by
      rw [tpd.card_U_eq_index, vdata.typeP.card_U_eq_index]
    rw [hU', vdata.U_eq_bot, Subgroup.card_bot, hyp.card_V_eq_vd] at hcardU
    exact hvd hcardU

open scoped Classical in
/-- **The §9 setup on `T`** (the (13.4) gate-3 router, issue 9013): the `TypesIIIIIIVSetup T`
carrier assembled from the **reconciled** type-`P` datum (`reconciled_typePData_T`), so its
`U`/`W1`/`W2` are the hypothesis's `V`/`W₂`/`W₁` (companions `toTypesIIIIIIVSetupT_U_eq` etc.)
and its kernel is `H = T_F = Q` (`toTypesIIIIIIVSetupT_H_eq`).  Nontriviality: `U = V ≠ ⊥` from
`|V| = v·d ≠ 1`; `|W1| = |W₂| = p` prime; the `M_F`-TI component of `TypePNontrivialCore` is
datum-independent, read off any non-V type witness (`T_typeII_or_III_or_IV`).  Opens the §9
machinery ((9.7)–(9.9), `typeII_III_IV_order_relations`, the `hcPsi` degree analysis) on `T` —
the (13.3.b)-on-`T` route of the (13.4) θ-package.  Mirrors `toTypesIIIIIIVSetupS`; extracts the
inline construction of `Q_elementaryAbelian_T` (`S15_SAndT`) without its `IsTypeII` hypothesis. -/
noncomputable def Hypothesis.toTypesIIIIIIVSetupT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup hyp.T where
  maximal := hyp.T_maximal
  typeP := (reconciled_typePData_T hG hyp).choose
  nontrivial := by
    obtain ⟨hU, hW1, -⟩ := (reconciled_typePData_T hG hyp).choose_spec
    refine ⟨?_, ?_, ?_⟩
    · rw [hU]
      intro hbot
      apply hvd
      rw [← hyp.card_V_eq_vd, hbot, Subgroup.card_bot]
    · rw [hW1, ← hyp.p_eq_card_W2]
      exact hyp.p_prime
    · rcases hyp.T_typeII_or_III_or_IV hG hvd with h | h | h
      · exact h.some.common.2.2
      · exact h.some.common.2.2
      · exact h.some.common.2.2
  type_alt := hyp.T_typeII_or_III_or_IV hG hvd

theorem Hypothesis.toTypesIIIIIIVSetupT_U_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    (hyp.toTypesIIIIIIVSetupT hG hvd).U = hyp.V :=
  (reconciled_typePData_T hG hyp).choose_spec.1

theorem Hypothesis.toTypesIIIIIIVSetupT_W1_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    (hyp.toTypesIIIIIIVSetupT hG hvd).W1 = hyp.W2 :=
  (reconciled_typePData_T hG hyp).choose_spec.2.1

theorem Hypothesis.toTypesIIIIIIVSetupT_W2_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    (hyp.toTypesIIIIIIVSetupT hG hvd).W2 = hyp.W1 :=
  (reconciled_typePData_T hG hyp).choose_spec.2.2

theorem Hypothesis.toTypesIIIIIIVSetupT_H_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    ((hyp.toTypesIIIIIIVSetupT hG hvd).H : Subgroup G) = hyp.Q := by
  show (reconciled_typePData_T hG hyp).choose.H = hyp.Q
  rw [(reconciled_typePData_T hG hyp).choose.H_eq, hyp.Q_eq_TF]

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **§9 character data on `T`** (the T-mirror of `mkSection11CharacterDataS`, over the
`toTypesIIIIIIVSetupT` router; issue 9013 gate 3): `u = |V̄|` is rfl-pinned to the `V`-action
image on the chief factor of `Q`; `tau := hyp.tauT`; `H0CprimeSupport := ∅` and
`quotientSemidirectFrobenius := True` are the same documented count/degree-only placeholders as
the `S`-instance (NOT for coherence consumption).  Opens the §9 (9.8)/(9.9) counts — in
particular the (13.3.b) dichotomy glue `caseB_of_no_irreducible_sOf_H0Cprime` — on `T`. -/
noncomputable def Hypothesis.mkSection11CharacterDataT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    OddOrder.Peterfalvi.S11.Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief where
  u := Nat.card ↥(((quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
      (((hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U.subgroupOf
        ((hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U
          ⊔ (hyp.toTypesIIIIIIVSetupT hG hvd).typeP.W1)).subtype)).range)
  u_eq_card_quotient := rfl
  H0CprimeSupport := ∅
  tau := hyp.tauT
  quotientSemidirectFrobenius := True

/-- **Peterfalvi (13.3.b), dichotomy glue** (§9-generic, issue 9013 gate 3): if the §9 family
`𝒮(H₀C')` contains **no** irreducible character, then case (9.7.b) holds
(a `CliffordCaseBData` — carrying the Singer facts `Ū` cyclic, `u ∣ (p^q−1)/(p−1)`, irreducible
action), with `C = ⊥` and the full value `u = (p^q − 1)/(p − 1)`.

Assembly of the sorry-free §9 endpoints: `clifford_dichotomy` splits into the two Clifford cases;
in case (a) the (9.8.c) witness (`caseA_character_counts` conjunct (c)) is an irreducible member
of `𝒮(H₀C) ⊆ 𝒮(H₀C')` (`sOf_antitone`, `C' ≤ C`) — contradicting the hypothesis; in case (b) the
(9.9.c) conjunct (d) of `caseB_character_counts` delivers both values.  This is the C=1/u-full
half of (13.3.b); the "case (9.7.b) holds"半 is the returned `CliffordCaseBData` itself.  Stated
generically over `M` so both the `S`- and `T`-instances (via `toTypesIIIIIIVSetupS` /
`toTypesIIIIIIVSetupT`) can cite it — the T-instance is the (13.4) θ-package's (13.3.b)-on-`T`
input (contrapositive form). -/
theorem caseB_of_no_irreducible_sOf_H0Cprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M}
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData data}
    (chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief)
    (hno : ¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ) :
    ∃ _caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData chars,
      chars.C = ⊥ ∧ chars.u = (chief.p ^ data.q - 1) / (chief.p - 1) := by
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG chars with hA | hB
  · exfalso
    obtain ⟨caseA⟩ := hA
    obtain ⟨-, -, ⟨χ, hχmem, hχirr, -⟩, -⟩ :=
      OddOrder.Peterfalvi.S11.caseA_character_counts hG chars caseA
    exact hno ⟨χ,
      OddOrder.Peterfalvi.S11.sOf_antitone data
        (sup_le_sup_left chars.Cprime_le_C chief.H0) hχmem, hχirr⟩
  · obtain ⟨caseB⟩ := hB
    exact ⟨caseB,
      (OddOrder.Peterfalvi.S11.caseB_character_counts hG chars caseB).2.2.2 hno⟩

/-- **`q ∤ |H|`** — the order-theoretic core of the `(H^#)^G ∩ (Q^#)^G = ∅` disjointness:
`H = PC ≤ S' = PU` has order dividing `|P|·|U|` (`derived_complement`), `q ∤ |P| = p^q`
(`p ≠ q`), and `q ∤ |U|` (the `U W₁` Frobenius structure has coprime kernel and complement,
`|W₁| = q`). -/
theorem Hypothesis.q_not_dvd_card_H [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : ¬ hyp.q ∣ Nat.card ↥hyp.H := by
  intro hdvd
  -- `|H| ∣ |S'| = |P|·|U|`.
  have hHle : hyp.H ≤ derivedInG hyp.S := by
    show hyp.P ⊔ hyp.C ≤ derivedInG hyp.S
    rw [hyp.S_deriv_eq_PU]
    exact sup_le le_sup_left (le_trans (hyp.C_eq ▸ inf_le_left) le_sup_right)
  have hcard_deriv : Nat.card ↥hyp.P * Nat.card ↥hyp.U = Nat.card ↥(derivedInG hyp.S) := by
    have h := hyp.Sdata.derived_complement.card_mul
    have hPeq : hyp.Sdata.H = hyp.P := by rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPeq ▸ hyp.Sdata.H_le)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.U_le).toEquiv, hPeq,
      hyp.Sdata_U_eq] at h
  have hdvd' : hyp.q ∣ Nat.card ↥hyp.P * Nat.card ↥hyp.U := by
    rw [hcard_deriv]
    exact hdvd.trans (Subgroup.card_dvd_of_le hHle)
  rcases (Nat.Prime.dvd_mul hyp.q_prime).mp hdvd' with hq | hq
  · -- `q ∤ |P| = p^q` since `p ≠ q`.
    rw [hyp.card_P_eq hG hyp.Sdata_W2_eq] at hq
    have hqp : hyp.q ∣ hyp.p := Nat.Prime.dvd_of_dvd_pow hyp.q_prime hq
    exact hyp.p_ne_q ((Nat.prime_dvd_prime_iff_eq hyp.q_prime hyp.p_prime).mp hqp).symm
  · -- `q ∤ |U|`: `U W₁` Frobenius has coprime kernel/complement.
    -- `U ≠ ⊥` via the type-II witness on `S` (as in `basic_structure`).
    have hSII : IsTypeII hyp.S :=
      OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2
    have tdata : TypeIIData hyp.S := hSII.some
    have hSdataUne : hyp.Sdata.U ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ↥hyp.Sdata.U = Nat.card ↥tdata.typeP.U := by
        rw [hyp.Sdata.card_U_eq_index, tdata.typeP.card_U_eq_index]
      rw [hbot, Subgroup.card_bot] at h1
      exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
    have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
    have hcop := hfrob.coprime_card_kernel_complement
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
        hyp.Sdata.U ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
        hyp.Sdata.W1 ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv,
      hyp.Sdata_U_eq, hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1] at hcop
    exact hyp.q_prime.ne_one (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hq dvd_rfl))

/-- **`(H^#)^G` and `(Q^#)^G` are disjoint**: a common element would be conjugate both to a
nonidentity element of `H` (order dividing `|H|`, so prime to `q` by `q_not_dvd_card_H`) and to
a nonidentity element of `Q` (order a positive power of `q`, `|Q| = q^p`). -/
theorem disjoint_conjClassSet_sharp_H_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) :
    ∀ x : G, x ∈ conjClassSet (sharpSubgroup hyp.H) →
      x ∈ conjClassSet (sharpSubgroup hyp.Q) → False := by
  intro x hxH hxQ
  obtain ⟨a, ⟨haH, ha1⟩, g, rfl⟩ := mem_conjClassSet.mp hxH
  obtain ⟨b, ⟨hbQ, hb1⟩, h, hab⟩ := mem_conjClassSet.mp hxQ
  -- Conjugation preserves orders: `orderOf a = orderOf b`.
  have horder : orderOf a = orderOf b := by
    have h1 : orderOf (g * a * g⁻¹) = orderOf a := by
      rw [show g * a * g⁻¹ = (MulAut.conj g) a from rfl]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
    have h2 : orderOf (h * b * h⁻¹) = orderOf b := by
      rw [show h * b * h⁻¹ = (MulAut.conj h) b from rfl]
      exact orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective b
    rw [← h1, ← hab, h2]
  -- `orderOf b` is a positive power of `q`, so `q ∣ orderOf a ∣ |H|`.
  have hbdvd : orderOf b ∣ hyp.q ^ hyp.p := by
    have h1 : orderOf (⟨b, hbQ⟩ : ↥hyp.Q) ∣ Nat.card ↥hyp.Q := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk b hbQ, hcardQ] at h1
  obtain ⟨i, hip, hbord⟩ := (Nat.dvd_prime_pow hyp.q_prime).mp hbdvd
  have hi0 : i ≠ 0 := by
    intro hi0
    rw [hi0, pow_zero] at hbord
    exact hb1 (orderOf_eq_one_iff.mp hbord)
  have hqdvd_a : hyp.q ∣ orderOf a := by
    rw [horder, hbord]
    exact dvd_pow_self hyp.q hi0
  have hadvd : orderOf a ∣ Nat.card ↥hyp.H := by
    have h1 : orderOf (⟨a, SetLike.mem_coe.mp haH⟩ : ↥hyp.H) ∣ Nat.card ↥hyp.H :=
      orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk a (SetLike.mem_coe.mp haH)] at h1
  exact hyp.q_not_dvd_card_H hG (hqdvd_a.trans hadvd)

/-- Membership in the generic set `G₀`, unfolded: nonidentity and in neither saturation. -/
theorem Hypothesis.mem_G0_iff (hyp : Hypothesis (G := G)) (x : G) :
    x ∈ hyp.G0 ↔ x ≠ 1 ∧ x ∉ conjClassSet (sharpSubgroup hyp.H)
      ∧ x ∉ conjClassSet (sharpSubgroup hyp.Q) := by
  show x ∈ sharpSubgroup (⊤ : Subgroup G) \ _ ↔ _
  simp only [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_top, true_and, Set.mem_union, not_or]

open scoped Classical in
/-- **The four-piece split of a conjugation-invariant sum** (the (13.10) counting skeleton):
for a conjugation-invariant `f`,

  `∑_G f = f(1) + ∑_{G₀} f + [G:S]·∑_{H^#} f + [G:T]·∑_{Q^#} f`.

`G` is the disjoint union of `{1}`, `G₀`, `(H^#)^G`, and `(Q^#)^G` (the saturations are disjoint
by `disjoint_conjClassSet_sharp_H_Q` and miss `1`; `G₀` is *defined* as the complement), and each
saturation sum collapses by `IsTISubset.sum_conjClassSet` (issue 9011) via the proven TI
structure (`H_sharp_isTISubset` / `Q_sharp_isTISubset`).  Instantiations: `f = ‖χ(·)‖²` gives the
Parseval splits (13.10.1)/(13.10.2); `f = 1` the cover count (13.10.3). -/
theorem Hypothesis.sum_univ_split [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {M : Type*} [AddCommMonoid M] (f : G → M)
    (hf : ∀ g x : G, f (g * x * g⁻¹) = f x)
    (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) (hvd : hyp.v * hyp.d ≠ 1) :
    ∑ x : G, f x
      = f 1 + (∑ x ∈ hyp.G0Finset, f x)
        + hyp.S.index • ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, f x
        + hyp.T.index • ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, f x := by
  classical
  -- TI structure and stabilization on both sides.
  have hTIH : OddOrder.GroupTheory.IsTISubset (sharpSubgroup hyp.H) hyp.S :=
    H_sharp_isTISubset hG hyp
  have hTIQ : OddOrder.GroupTheory.IsTISubset (sharpSubgroup hyp.Q) hyp.T :=
    Q_sharp_isTISubset hG hyp hvd
  have hstabH : ∀ l ∈ hyp.S, MulAut.conj l • sharpSubgroup hyp.H = sharpSubgroup hyp.H :=
    fun l hl => conj_smul_sharpSubgroup_eq (normalizer_H_eq_S hG hyp) hl
  have hstabQ : ∀ l ∈ hyp.T, MulAut.conj l • sharpSubgroup hyp.Q = sharpSubgroup hyp.Q :=
    fun l hl => conj_smul_sharpSubgroup_eq (normalizer_Q_eq_T hG hyp) hl
  -- The four Finset pieces.
  set CH : Finset G := (Set.toFinite (conjClassSet (sharpSubgroup hyp.H))).toFinset with hCHdef
  set CQ : Finset G := (Set.toFinite (conjClassSet (sharpSubgroup hyp.Q))).toFinset with hCQdef
  have hmemCH : ∀ x : G, x ∈ CH ↔ x ∈ conjClassSet (sharpSubgroup hyp.H) := fun x =>
    (Set.toFinite _).mem_toFinset
  have hmemCQ : ∀ x : G, x ∈ CQ ↔ x ∈ conjClassSet (sharpSubgroup hyp.Q) := fun x =>
    (Set.toFinite _).mem_toFinset
  have hmemG0 : ∀ x : G, x ∈ hyp.G0Finset ↔ x ∈ hyp.G0 := fun x =>
    (Set.toFinite _).mem_toFinset
  -- Nonidentity: conjugates of nonidentity elements are nonidentity.
  have hne1 : ∀ (K : Subgroup G) (x : G), x ∈ conjClassSet (sharpSubgroup K) → x ≠ 1 := by
    rintro K x hx rfl
    obtain ⟨a, ⟨-, ha1⟩, g, hg⟩ := mem_conjClassSet.mp hx
    refine ha1 ?_
    show a = 1
    have ha : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [ha, hg]
    group
  have hne1H : ∀ x ∈ CH, x ≠ 1 := fun x hx => hne1 hyp.H x ((hmemCH x).mp hx)
  have hne1Q : ∀ x ∈ CQ, x ≠ 1 := fun x hx => hne1 hyp.Q x ((hmemCQ x).mp hx)
  -- `G₀` misses `1` and both saturations (definitional).
  have hG0iff := hyp.mem_G0_iff
  -- The partition: `univ = {1} ∪ G₀ ∪ CH ∪ CQ`, pairwise disjoint.
  have hcover : (Finset.univ : Finset G) = insert 1 (hyp.G0Finset ∪ CH ∪ CQ) := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, true_iff]
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · refine Or.inr ?_
      by_cases hxH : x ∈ conjClassSet (sharpSubgroup hyp.H)
      · exact Or.inl (Or.inr ((hmemCH x).mpr hxH))
      · by_cases hxQ : x ∈ conjClassSet (sharpSubgroup hyp.Q)
        · exact Or.inr ((hmemCQ x).mpr hxQ)
        · exact Or.inl (Or.inl ((hmemG0 x).mpr ((hG0iff x).mpr ⟨hx1, hxH, hxQ⟩)))
  have hdisjHQ : Disjoint CH CQ := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact disjoint_conjClassSet_sharp_H_Q hG hyp hcardQ x ((hmemCH x).mp hx) ((hmemCQ x).mp hx')
  have hdisjG0 : Disjoint hyp.G0Finset (CH ∪ CQ) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨-, hxH, hxQ⟩ := (hG0iff x).mp ((hmemG0 x).mp hx)
    rcases Finset.mem_union.mp hx' with h | h
    · exact hxH ((hmemCH x).mp h)
    · exact hxQ ((hmemCQ x).mp h)
  have hone_notin : (1 : G) ∉ hyp.G0Finset ∪ CH ∪ CQ := by
    intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact ((hG0iff 1).mp ((hmemG0 1).mp h')).1 rfl
      · exact hne1H 1 h' rfl
    · exact hne1Q 1 h rfl
  -- Assemble the split.
  rw [hcover, Finset.sum_insert hone_notin, Finset.union_assoc, Finset.sum_union hdisjG0,
    Finset.sum_union hdisjHQ, hCHdef, hCQdef,
    OddOrder.GroupTheory.IsTISubset.sum_conjClassSet f hTIH hstabH hf,
    OddOrder.GroupTheory.IsTISubset.sum_conjClassSet f hTIQ hstabQ hf]
  abel

/-- `|S'| = |P|·|U|` — the (13.1.b) `S' = P ⋊ U` order decomposition
(`Sdata.derived_complement`). -/
theorem Hypothesis.card_deriv_S_eq [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥(derivedInG hyp.S) = Nat.card ↥hyp.P * Nat.card ↥hyp.U := by
  have h := hyp.Sdata.derived_complement.card_mul
  have hPeq : hyp.Sdata.H = hyp.P := by rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.H_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.U_le).toEquiv, hPeq,
    hyp.Sdata_U_eq] at h
  exact h.symm

/-- `|S| = |S'|·q` — the (13.1.b) `S = S' ⋊ W₁` order decomposition (`Sdata.M_complement`). -/
theorem Hypothesis.card_S_eq_deriv_mul_q [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.S = Nat.card ↥(derivedInG hyp.S) * hyp.q := by
  have hle : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have h := hyp.Sdata.M_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.W1_le).toEquiv,
    hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1] at h
  exact h.symm

/-- **`|S| = p^q·(uc)·q`** — the (13.2)-level order value of `S`, assembling
`card_S_eq_deriv_mul_q`, `card_deriv_S_eq`, `card_P_eq` (`|P| = p^q`), and `|U| = uc`. -/
theorem Hypothesis.card_S_val [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.S = hyp.p ^ hyp.q * (hyp.u * hyp.c) * hyp.q := by
  rw [hyp.card_S_eq_deriv_mul_q, hyp.card_deriv_S_eq, hyp.card_P_eq hG hyp.Sdata_W2_eq,
    hyp.card_U_eq_uc]

/-- **`|H| = p^q · c`** (Peterfalvi (13.2)): `H = PC` with `P = S_F` elementary abelian of order
`p^q` and `C = C_U(P)` of order `c`, and `P ⊓ C = ⊥` (`P` a `p`-group, `C ≤ U` with `|U| = uc`
coprime to `p` by the Hall property of `P` in `S`).  So `|PC| = |P|·|C| = p^q·c` (the complement
`card_mul_card_of_complement_normal`, `P ◁ H`).  Feeds `[S:H] = uq` (`mu_j_isIndPC` degree) and the
(13.5) counting value `|H^#|/|S| = uq/(cp^q)`. -/
theorem Hypothesis.card_H_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.H = hyp.p ^ hyp.q * hyp.c := by
  have hP_le_S : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hC_le_S : hyp.C ≤ hyp.S := by
    have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    exact le_trans (hyp.C_eq ▸ inf_le_left) hUS
  have hPH : hyp.P ≤ hyp.H := le_sup_left
  have hCH : hyp.C ≤ hyp.H := le_sup_right
  have hPcard : Nat.card ↥hyp.P = hyp.p ^ hyp.q := hyp.card_P_eq hG hyp.Sdata_W2_eq
  -- `p ∤ c`: `P` Hall in `S`, `[S:P] = ucq`
  have hPScard : Nat.card ↥(hyp.P.subgroupOf hyp.S) = Nat.card ↥hyp.P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_S).toEquiv
  have hcop : Nat.Coprime (hyp.p ^ hyp.q) ((hyp.P.subgroupOf hyp.S).index) := by
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.S
    rw [← hyp.P_eq_SF] at hHall
    have h0 := Ch03.IsHallSubgroup.coprime_index hHall
    rw [hPScard, hPcard] at h0
    exact h0
  have hSPidx : (hyp.P.subgroupOf hyp.S).index = hyp.u * hyp.c * hyp.q := by
    have hm := Subgroup.card_mul_index (hyp.P.subgroupOf hyp.S)
    rw [hPScard, hPcard, hyp.card_S_val hG] at hm
    have hpq : (0 : ℕ) < hyp.p ^ hyp.q := pow_pos hyp.p_prime.pos hyp.q
    have hmm : hyp.p ^ hyp.q * (hyp.P.subgroupOf hyp.S).index
        = hyp.p ^ hyp.q * (hyp.u * hyp.c * hyp.q) := by rw [hm]; ring
    exact Nat.eq_of_mul_eq_mul_left hpq hmm
  have hpc : Nat.Coprime (hyp.p ^ hyp.q) hyp.c := by
    have hcdvd : hyp.c ∣ (hyp.P.subgroupOf hyp.S).index := by
      rw [hSPidx]; exact ⟨hyp.u * hyp.q, by ring⟩
    exact Nat.Coprime.coprime_dvd_right hcdvd hcop
  have hpc' : Nat.gcd (hyp.p ^ hyp.q) hyp.c = 1 := hpc
  -- `P ⊓ C = ⊥` from coprime orders
  have hdisj : hyp.P ⊓ hyp.C = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have hd1 : Nat.card ↥(hyp.P ⊓ hyp.C) ∣ hyp.p ^ hyp.q :=
      hPcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(hyp.P ⊓ hyp.C) ∣ hyp.c :=
      hyp.c_eq_card_C ▸ Subgroup.card_dvd_of_le inf_le_right
    exact Nat.dvd_one.mp (hpc' ▸ Nat.dvd_gcd hd1 hd2)
  -- `|H| = |P|·|C|` (complement `P ◁ H`)
  haveI hPnormalH : (hyp.P.subgroupOf hyp.H).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr ?_
    have hSnorm : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
      rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
    exact le_trans (hyp.H_le_S) hSnorm
  have hinf : hyp.P.subgroupOf hyp.H ⊓ hyp.C.subgroupOf hyp.H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
    have hmem : ((x : ↥hyp.H) : G) ∈ hyp.P ⊓ hyp.C :=
      ⟨Subgroup.mem_subgroupOf.mp hxP, Subgroup.mem_subgroupOf.mp hxC⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; exact Subtype.ext hmem
  have hsup : hyp.P.subgroupOf hyp.H ⊔ hyp.C.subgroupOf hyp.H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPH hCH]
    exact Subgroup.subgroupOf_self hyp.H
  have hcompl : Subgroup.IsComplement' (hyp.P.subgroupOf hyp.H) (hyp.C.subgroupOf hyp.H) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf)
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
  have hmul := hcompl.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv, hPcard,
    ← hyp.c_eq_card_C] at hmul
  exact hmul.symm

/-- **`[S : H] = uq`** (Peterfalvi (13.2)): the index of `H = PC` in `S`.  From
`|S| = p^q·(uc)·q` (`card_S_val`) and `|H| = p^q·c` (`card_H_eq`), `[S:H] = |S|/|H| = uq`.  The
degree index of `mu_j_isIndPC` (`μ_j(1) = [S:H]·θ(1) = uq`). -/
theorem Hypothesis.H_index_eq_uq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (hyp.H.subgroupOf hyp.S).index = hyp.u * hyp.q := by
  have hm := Subgroup.card_mul_index (hyp.H.subgroupOf hyp.S)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hyp.H_le_S)).toEquiv, hyp.card_H_eq hG,
    hyp.card_S_val hG] at hm
  have hpos : (0 : ℕ) < hyp.p ^ hyp.q * hyp.c :=
    Nat.mul_pos (pow_pos hyp.p_prime.pos hyp.q) (hyp.c_eq_card_C ▸ Nat.card_pos)
  have hmm : hyp.p ^ hyp.q * hyp.c * (hyp.H.subgroupOf hyp.S).index
      = hyp.p ^ hyp.q * hyp.c * (hyp.u * hyp.q) := by rw [hm]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos hmm

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a), degree**: each nonzero `μ`-column sum has degree `uq`.  Immediate from
`mu_j_isIndPC` (`μ_j = Ind_{PC} θ`, `θ` linear) and `H_index_eq_uq` (`[S:H] = uq`):
`μ_j(1) = [S:H]·θ(1) = uq·1 = uq`. -/
theorem Hypothesis.mu_j_degree [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    (∑ i : Fin hyp.q, hyp.mu i j) (1 : ↥hyp.S) = ((hyp.u * hyp.q : ℕ) : ℂ) := by
  haveI := hyp.finiteG
  obtain ⟨θ, hθirr, hθ1, hθeq⟩ := hyp.mu_j_isIndPC hG j hj
  rw [hθeq, ClassFunction.induce_apply_one, hθ1, mul_one, hyp.H_index_eq_uq hG]

open scoped FiniteInduce in
/-- **Column-constant degree** (Peterfalvi (13.1.e)/(4.3.c)): within a column `j`, all
`μ_{ij}(1)` are equal.  From `mu_definition` at `1`: the LHS `Ind_W^S(ω_{ij} − ω_{0j})(1)` is
`[S:W]·(ω_{ij}(1) − ω_{0j}(1)) = 0` (`omega_apply_one`: `ω`-grid linear), so the RHS
`δ_j·(μ_{ij}(1) − μ_{0j}(1)) = 0`, and `δ_j = ±1 ≠ 0` (`delta_pm_one`) gives the equality. -/
theorem Hypothesis.mu_apply_one_column_const [Finite G] (hyp : Hypothesis (G := G))
    (i : Fin hyp.q) (j : Fin hyp.p) :
    hyp.mu i j (1 : ↥hyp.S) = hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) := by
  haveI := hyp.finiteG
  have hdef := hyp.mu_definition i j
  have h1 := congrArg (fun f : ClassFunction ↥hyp.S ℂ => f (1 : ↥hyp.S)) hdef
  -- LHS(1) = 0
  rw [ClassFunction.induce_apply_one] at h1
  have homega0 : (ClassFunction.compHom
      (Subgroup.subgroupOfEquivOfLe ((le_of_eq hyp.W_eq_inter).trans inf_le_left)).toMonoidHom
        (hyp.omega i j - hyp.omega ⟨0, hyp.q_prime.pos⟩ j))
      (1 : ↥(hyp.W.subgroupOf hyp.S)) = 0 := by
    rw [ClassFunction.compHom_apply, map_one, ClassFunction.sub_apply,
      hyp.omega_apply_one, hyp.omega_apply_one, sub_self]
  rw [homega0, mul_zero] at h1
  -- RHS(1) = δ_j·(μ_{ij}(1) − μ_{0j}(1)) = 0, with δ_j ≠ 0
  have hδ : (hyp.delta j : ℂ) ≠ 0 := by
    rcases (hyp.delta_pm_one.1 j) with h | h <;> rw [h] <;> norm_num
  have hsub : hyp.mu i j (1 : ↥hyp.S) - hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) = 0 :=
    (mul_eq_zero.mp h1.symm).resolve_left hδ
  exact sub_eq_zero.mp hsub

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a), per-entry degree**: `μ_{ij}(1) = u` for `j ≥ 1`.  The column is
degree-constant (`mu_apply_one_column_const`), so the column sum `μ_j(1) = q·μ_{0j}(1)`; with
`μ_j(1) = uq` (`mu_j_degree`) and `q ≠ 0`, `μ_{0j}(1) = u`.  The `μ_{ij}(1) = u` that Peterfalvi
(13.3.c) feeds into the `(4.3.d)` congruence `u ≡ δ_j (mod q)` for `δ_j = 1`. -/
theorem Hypothesis.mu_apply_one_eq_u [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (i : Fin hyp.q) (j : Fin hyp.p)
    (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    hyp.mu i j (1 : ↥hyp.S) = ((hyp.u : ℕ) : ℂ) := by
  haveI := hyp.finiteG
  -- `∑ᵢ μ_{ij}(1) = q·μ_{0j}(1)` and `= uq`
  have hsum := hyp.mu_j_degree hG j hj
  rw [ClassFunction.finset_sum_apply] at hsum
  have hconst : ∑ k : Fin hyp.q, hyp.mu k j (1 : ↥hyp.S)
      = (hyp.q : ℂ) * hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) := by
    rw [Finset.sum_congr rfl (fun k _ => hyp.mu_apply_one_column_const k j),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hconst] at hsum
  have hq0 : (hyp.q : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact hyp.q_prime.pos.ne'
  have h0j : hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) = ((hyp.u : ℕ) : ℂ) := by
    have : (hyp.q : ℂ) * hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S)
        = (hyp.q : ℂ) * ((hyp.u : ℕ) : ℂ) := by rw [hsum]; push_cast; ring
    exact mul_left_cancel₀ hq0 this
  rw [hyp.mu_apply_one_column_const i j, h0j]

/-- **Peterfalvi `u ≡ 1 (mod q)`** (the (13.3.c) crux, (11.8.1) `|Ū| ≡ 1 mod q`).  The `S`-side
`U W₁` is a Frobenius group (`typeP_uW1_frobenius`), so for the conjugation homomorphism
`φ : U W₁ →* Aut(P)` the kernel-image `φ(U) = U/C_U(P) = Ū` satisfies `|Ū| ≡ 1 (mod |W₁|)`
(`IsFrobeniusGroup.card_range_comp_subtype_modEq_one`, Isaacs Lemma 6.1); with `|Ū| = u`
(`card_U_eq_uc`, `C = U ⊓ C_G(P)`) and `|W₁| = q` this is `u ≡ 1 (mod q)`.  Crucially **ungated**:
uses only the (proven) `U W₁` Frobenius structure, not the case-(b) Singer field model. -/
theorem Hypothesis.u_modEq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.u ≡ 1 [MOD hyp.q] := by
  haveI := hyp.finiteG
  have hSII : IsTypeII hyp.S :=
    OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2
  have tdata : TypeIIData hyp.S := hSII.some
  have hSdataUne : hyp.Sdata.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥hyp.Sdata.U = Nat.card ↥tdata.typeP.U := by
      rw [hyp.Sdata.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
  have hUW1leS : hyp.Sdata.U ⊔ hyp.Sdata.W1 ≤ hyp.S :=
    sup_le (hyp.Sdata.U_le.trans (Subgroup.map_subtype_le _)) hyp.Sdata.W1_le
  have hSnormP : hyp.S ≤ Subgroup.normalizer hyp.P := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hUW1normP : hyp.Sdata.U ⊔ hyp.Sdata.W1 ≤ Subgroup.normalizer hyp.P :=
    le_trans hUW1leS hSnormP
  letI : MulDistribMulAction ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1) ↥hyp.P :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer hyp.P)) ↥hyp.P
      (Subgroup.inclusion hUW1normP)
  set φ : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1) →* MulAut ↥hyp.P :=
    MulDistribMulAction.toMulAut ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1) ↥hyp.P with hφ
  have hmod := hfrob.card_range_comp_subtype_modEq_one φ
  have hAcard : Nat.card ↥(hyp.Sdata.W1.subgroupOf (hyp.Sdata.U ⊔ hyp.Sdata.W1)) = hyp.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
      hyp.Sdata.W1 ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv, hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
  have hφapply : ∀ (a : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1)) (p : ↥hyp.P),
      ((φ a p : ↥hyp.P) : G) = (a : G) * (p : G) * (a : G)⁻¹ := fun a p => rfl
  have hker_iff : ∀ a : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1),
      φ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (hyp.P : Set G) := by
    intro a
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h1 p hp
      have hcg := congrArg (fun e : MulAut ↥hyp.P => ((e ⟨p, hp⟩ : ↥hyp.P) : G)) h1
      simp only [hφapply, MulAut.one_apply] at hcg
      exact (mul_inv_eq_iff_eq_mul.mp hcg).symm
    · intro hc
      ext p
      simp only [hφapply, MulAut.one_apply]
      have hpc := hc (p : G) p.2
      rw [← hpc]; group
  set N := hyp.Sdata.U.subgroupOf (hyp.Sdata.U ⊔ hyp.Sdata.W1) with hN
  set ψ : ↥N →* MulAut ↥hyp.P := φ.comp N.subtype with hψ
  set ρ : ↥N →* G := (hyp.Sdata.U ⊔ hyp.Sdata.W1).subtype.comp N.subtype with hρ
  have hρinj : Function.Injective ρ :=
    (hyp.Sdata.U ⊔ hyp.Sdata.W1).subtype_injective.comp N.subtype_injective
  have hkermap : (ψ.ker).map ρ = hyp.C := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply] at hn
      have hgC : (ρ n : G) ∈ Subgroup.centralizer (hyp.P : Set G) := (hker_iff _).mp hn
      have hgU : (ρ n : G) ∈ hyp.Sdata.U := Subgroup.mem_subgroupOf.mp n.2
      have hgU' : (ρ n : G) ∈ hyp.U := by rw [← hyp.Sdata_U_eq]; exact hgU
      rw [hyp.C_eq]
      exact ⟨hgU', hgC⟩
    · intro hgC
      rw [hyp.C_eq, Subgroup.mem_inf] at hgC
      obtain ⟨hgU, hgc⟩ := hgC
      have hgUS : g ∈ hyp.Sdata.U := by rw [hyp.Sdata_U_eq]; exact hgU
      have hgUW1 : g ∈ hyp.Sdata.U ⊔ hyp.Sdata.W1 :=
        (le_sup_left : hyp.Sdata.U ≤ _) hgUS
      have hgN : (⟨g, hgUW1⟩ : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1)) ∈ N :=
        Subgroup.mem_subgroupOf.mpr hgUS
      refine ⟨⟨⟨g, hgUW1⟩, hgN⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply]
      exact (hker_iff _).mpr hgc
  have hkercard : Nat.card ↥(ψ.ker) = hyp.c := by
    rw [hyp.c_eq_card_C, ← hkermap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ ρ hρinj).toEquiv
  have hNcard : Nat.card ↥N = hyp.u * hyp.c := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
      hyp.Sdata.U ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv, hyp.Sdata_U_eq, hyp.card_U_eq_uc]
  have hrangecard : Nat.card ↥(ψ.range) = hyp.u := by
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hkercard, hNcard] at hsplit
    have hc0 : 0 < hyp.c := hyp.c_eq_card_C ▸ Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hc0 hsplit).symm
  have hru : Nat.card ↥((φ.comp N.subtype).range) = hyp.u := hrangecard
  rw [hru, hAcard] at hmod
  exact hmod

/-- **Peterfalvi (13.3.c), the `S`-side signs are `1`**: `δ_j = 1` for `j ≥ 1`.  The (4.3.d)
congruence `μ_{0j}(1) = δ_j + q·a` (`mu_degree_modEq_delta`) with `μ_{0j}(1) = u`
(`mu_apply_one_eq_u`) and `u ≡ 1 (mod q)` (`u_modEq_one`) gives `q ∣ δ_j − 1`; since `δ_j = ±1`
(`delta_pm_one`) and `q ≥ 3`, `δ_j = -1` would force `q ∣ 2`, so `δ_j = 1`. -/
theorem Hypothesis.delta_eq_one_of_ne_zero [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    hyp.delta j = 1 := by
  obtain ⟨a, ha⟩ := hyp.mu_degree_modEq_delta ⟨0, hyp.q_prime.pos⟩ j
  rw [hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩ j hj] at ha
  have haZ : (hyp.u : ℤ) = hyp.delta j + (hyp.q : ℤ) * a := by exact_mod_cast ha
  have hqu : (hyp.q : ℤ) ∣ (hyp.u : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd.mp (hyp.u_modEq_one hG))
    simpa using (dvd_neg.mpr h)
  have hqδ : (hyp.q : ℤ) ∣ hyp.delta j - 1 := by
    have hsub : hyp.delta j - 1 = ((hyp.u : ℤ) - 1) - (hyp.q : ℤ) * a := by
      rw [haZ]; ring
    rw [hsub]
    exact dvd_sub hqu (Dvd.intro a rfl)
  rcases hyp.delta_pm_one.1 j with h1 | hm1
  · exact h1
  · exfalso
    rw [hm1] at hqδ
    have hq2 : (hyp.q : ℤ) ∣ 2 := dvd_neg.mp (by simpa using hqδ)
    have hqle : hyp.q ≤ 2 := Nat.le_of_dvd (by norm_num) (by exact_mod_cast hq2)
    have h2le := hyp.q_prime.two_le
    have hodd := Nat.odd_iff.mp hyp.q_odd
    omega

/-- **Peterfalvi (13.3.c), the `S`-side signs are all `1`**: `δ_j = 1` for every `j`.  The
base `δ_0 = 1` is the (4.4) trivial-column anchor (`delta_zero_eq_one`); for `j ≥ 1` it is
`delta_eq_one_of_ne_zero` (the `u ≡ 1 (mod q)` route).  This is the `S`-half of the
`CharacterDegreeData.delta_eq_one` field. -/
theorem Hypothesis.delta_eq_one_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) : hyp.delta j = 1 := by
  by_cases hj : j = ⟨0, hyp.p_prime.pos⟩
  · rw [hj]; exact hyp.delta_zero_eq_one
  · exact hyp.delta_eq_one_of_ne_zero hG j hj

/-- **Peterfalvi (4.3.c)+(13.3.c), the `W₁#` `μ`-value**: `μ_{0j}(x) = 1` for `x ∈ W₁`,
`x ≠ 1`.  The (4.3.c) value identity `mu_apply_of_not_mem_W2` applies (`x ∉ W₂` since
`W₁ ⊓ W₂ = ⊥` and `x ≠ 1`), giving `μ_{0j}(x) = δ_j·ω_{0j}(x)`; then `δ_j = 1`
(`delta_eq_one_S`, Pf (13.3.c)) and the row-`0` `ω`-value `ω_{0j}|_{W₁} = 1`
(`omega_row_zero_apply_of_mem_W1`).  This is the `hmuW1` input of the (13.18.a) exact
`β`-support `betaGrid_support_sharpP_union_typePV_of_values` (`S16_NonExistenceG/TGapCross`)
and of the original support argument (Pf p.83 "`μ_{0j}(x) = ω_{0j}(x) = 1`"). -/
theorem Hypothesis.mu_row0_apply_eq_one_of_mem_W1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (x : ↥hyp.S) (hxW1 : (x : G) ∈ hyp.W1) (hx1 : x ≠ 1) :
    hyp.mu ⟨0, hyp.q_prime.pos⟩ j x = 1 := by
  have hxW : (x : G) ∈ hyp.W := by
    rw [hyp.W_eq_join]; exact Subgroup.mem_sup_left hxW1
  have hxW2 : (x : G) ∉ (hyp.W2 : Set G) := by
    intro hmem
    apply hx1
    have hinf : (x : G) ∈ hyp.W1 ⊓ hyp.W2 := ⟨hxW1, hmem⟩
    rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hinf
    exact Subtype.ext hinf
  have hval := hyp.mu_apply_of_not_mem_W2 ⟨0, hyp.q_prime.pos⟩ j (x : G) hxW x.2 hxW2
  rw [show (⟨(x : G), x.2⟩ : ↥hyp.S) = x from rfl] at hval
  rw [hval, hyp.delta_eq_one_S hG j,
    hyp.omega_row_zero_apply_of_mem_W1 j ⟨(x : G), hxW⟩ hxW1]
  norm_num

/-- `|T| = |Q|·(vd)·p` — the `T`-side order decomposition, read off the reconciled type-`P`
datum (`M_complement`/`derived_complement` of `reconciled_typePData_T`) with `|V| = vd` and
`|W₂| = p`. -/
theorem Hypothesis.card_T_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.T = Nat.card ↥hyp.Q * (hyp.v * hyp.d) * hyp.p := by
  obtain ⟨tpd, hU, hW1, -⟩ := reconciled_typePData_T hG hyp
  -- `|T| = |T'|·p`.
  have hle : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have h1 := tpd.M_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.W1_le).toEquiv,
    hW1, ← hyp.p_eq_card_W2] at h1
  -- `|T'| = |Q|·|V| = |Q|·(vd)`.
  have h2 := tpd.derived_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.H_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.U_le).toEquiv, tpd.H_eq, ← hyp.Q_eq_TF,
    hU, hyp.card_V_eq_vd] at h2
  rw [← h1, ← h2]

/-- `|T| = |T'|·p` — the `T`-side mirror of `card_S_eq_deriv_mul_q`
(`M_complement` of the reconciled type-`P` datum + `|W₂| = p`). -/
theorem Hypothesis.card_T_eq_deriv_mul_p [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.T = Nat.card ↥(derivedInG hyp.T) * hyp.p := by
  obtain ⟨tpd, -, hW1, -⟩ := reconciled_typePData_T hG hyp
  have hle : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have h := tpd.M_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.W1_le).toEquiv,
    hW1, ← hyp.p_eq_card_W2] at h
  exact h.symm

/-- **(13.2.e)-for-`T`, `K^# = (QD)^#` TI-centralizer gate** ((13.4) structural gate, issue 9013
追記⁶ (c)): every nonidentity element of `K = QD ⊆ A₀(T)` has its `G`-centralizer inside `T` —
the `A₀(T)` TI-subset property of (13.2.e) applied to the `K^#`-points.  The proven
`Q_sharp_isTISubset` is the `D = ⊥` special case; the general form (live in the (13.4)
contradiction branch, where `D` may be nontrivial) needs the `A₀(T)`-TI materialization. -/
theorem QD_sharp_centralizer_le_T [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∀ z : ↥hyp.T, (z : G) ∈ hyp.Q ⊔ hyp.D → z ≠ 1 →
      Subgroup.centralizer ({(z : G)} : Set G) ≤ hyp.T := by
  sorry

/-- **No conjugate of `P` fits inside `T`** ((13.4) structural gate, issue 9013 追記⁶ (c),
discharged type-free post-9073): `|P| = p^q` (13.2.b) exceeds the `p`-part `p = |W₂|` of
`|T| = |Q|·(v·d)·p` (`card_T_eq`): `p ∤ |Q|` because `Q = T_F` is a Hall subgroup of `T` whose
index `(v·d)·p` is divisible by `p`, and `p ∤ v·d = |V|` because `V ⋊ W₂` is a Frobenius group
(`|V| ≡ 1 (mod p)`; trivially if `V = ⊥`).  So `v_p(|T|) = 1 < q`, and a conjugate `P^w ≤ T`
would give `p^q ∣ |T|` by Lagrange — impossible. -/
theorem P_conj_forall_not_le_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∀ w : G, ¬ ∀ r ∈ hyp.P, w⁻¹ * r * w ∈ hyp.T := by
  intro w hall
  haveI := hyp.finiteG
  -- `|P| = p^q` (13.2.b).
  obtain ⟨-, -, -, hPcard, -, -⟩ := basic_structure hG hyp
  -- The conjugate `P^w = (conj w⁻¹)(P)` lies in `T` and has order `p^q`; Lagrange.
  set f : G →* G := (MulAut.conj w⁻¹).toMonoidHom with hf
  have hle : hyp.P.map f ≤ hyp.T := by
    rintro - ⟨r, hr, rfl⟩
    simpa [hf, MulAut.conj_apply] using hall r hr
  have hcardmap : Nat.card ↥(hyp.P.map f) = hyp.p ^ hyp.q := by
    rw [← hPcard]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective hyp.P f (MulAut.conj w⁻¹).injective).toEquiv).symm
  have hdvd : hyp.p ^ hyp.q ∣ Nat.card ↥hyp.T := by
    rw [← hcardmap]
    exact Subgroup.card_dvd_of_le hle
  rw [hyp.card_T_eq hG] at hdvd
  -- `p ∤ v·d = |V|`: Frobenius `V ⋊ W₂` gives `|V| ≡ 1 (mod p)` (trivial if `V = ⊥`).
  have hpV : ¬ hyp.p ∣ hyp.v * hyp.d := by
    rw [← hyp.card_V_eq_vd]
    by_cases hVbot : hyp.V = ⊥
    · rw [hVbot, Subgroup.card_bot]
      intro h
      exact hyp.p_prime.one_lt.ne' (Nat.dvd_one.mp h)
    · obtain ⟨tpd, htpdU, htpdW1, -⟩ := reconciled_typePData_T hG hyp
      have hUne : tpd.U ≠ ⊥ := by rw [htpdU]; exact hVbot
      have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd hUne
      rw [htpdU, htpdW1] at hfrob
      have hmod := hfrob.card_kernel_modEq_one
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (le_sup_left : hyp.V ≤ hyp.V ⊔ hyp.W2)).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (le_sup_right : hyp.W2 ≤ hyp.V ⊔ hyp.W2)).toEquiv,
          ← hyp.p_eq_card_W2] at hmod
      intro hpdvd
      have hV1 : 1 ≤ Nat.card ↥hyp.V := Nat.card_pos
      have hsub : hyp.p ∣ Nat.card ↥hyp.V - 1 := (Nat.modEq_iff_dvd' hV1).mp hmod.symm
      have hone : hyp.p ∣ 1 := by
        have := Nat.dvd_sub hpdvd hsub
        rwa [Nat.sub_sub_self hV1] at this
      exact hyp.p_prime.one_lt.ne' (Nat.dvd_one.mp hone)
  -- `p ∤ |Q|`: `Q = T_F` is Hall in `T` and `p` divides its index `(v·d)·p`.
  have hpQ : ¬ hyp.p ∣ Nat.card ↥hyp.Q := by
    have hQ_le_T : hyp.Q ≤ hyp.T := hyp.Q_eq_TF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.T
    rw [← hyp.Q_eq_TF] at hHall
    have hcard_eq : Nat.card ↥(hyp.Q.subgroupOf hyp.T) = Nat.card ↥hyp.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_T).toEquiv
    have hcopIdx : Nat.Coprime (Nat.card ↥hyp.Q) (hyp.Q.subgroupOf hyp.T).index :=
      hcard_eq ▸ OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
    -- `index · |Q| = |T| = |Q|·(v·d)·p ⟹ index = (v·d)·p`, so `p ∣ index`.
    have hidx : (hyp.Q.subgroupOf hyp.T).index * Nat.card ↥hyp.Q
        = Nat.card ↥hyp.Q * (hyp.v * hyp.d) * hyp.p := by
      rw [← hyp.card_T_eq hG, ← hcard_eq]
      exact Subgroup.index_mul_card _
    have hQpos : 0 < Nat.card ↥hyp.Q := Nat.card_pos
    have hidx' : (hyp.Q.subgroupOf hyp.T).index = hyp.v * hyp.d * hyp.p := by
      have h : (hyp.Q.subgroupOf hyp.T).index * Nat.card ↥hyp.Q
          = hyp.v * hyp.d * hyp.p * Nat.card ↥hyp.Q := by
        rw [hidx]; ring
      exact Nat.eq_of_mul_eq_mul_right hQpos h
    intro hpdvd
    have hpidx : hyp.p ∣ (hyp.Q.subgroupOf hyp.T).index := by
      rw [hidx']; exact dvd_mul_left hyp.p (hyp.v * hyp.d)
    have hp1 := Nat.dvd_gcd hpdvd hpidx
    rw [Nat.Coprime.gcd_eq_one hcopIdx] at hp1
    exact hyp.p_prime.one_lt.ne' (Nat.dvd_one.mp hp1)
  -- `p^q ∣ (|Q|·(v·d))·p` with `p` prime to `|Q|·(v·d)` forces `p ∣ |Q|·(v·d)` (`q ≥ 2`) — absurd.
  have hK : ¬ hyp.p ∣ Nat.card ↥hyp.Q * (hyp.v * hyp.d) := by
    intro h
    rcases (Nat.Prime.dvd_mul hyp.p_prime).mp h with h' | h'
    exacts [hpQ h', hpV h']
  have hpow : hyp.p ^ hyp.q = hyp.p ^ (hyp.q - 1) * hyp.p := by
    rw [← pow_succ]
    congr 1
    have := hyp.q_prime.two_le
    omega
  rw [hpow] at hdvd
  have hcancel : hyp.p ^ (hyp.q - 1) ∣ Nat.card ↥hyp.Q * (hyp.v * hyp.d) :=
    (Nat.mul_dvd_mul_iff_right hyp.p_prime.pos).mp hdvd
  have hq1 : hyp.q - 1 ≠ 0 := by
    have := hyp.q_prime.two_le
    omega
  exact hK (dvd_trans (dvd_pow_self hyp.p hq1) hcancel)

open scoped FiniteInduce in
/-- **(13.3.b,c)-for-`T` θ-package** ((13.4) character gate, issue 9013 追記⁶ (a)+(b)): if the
(13.4) conclusion fails, then by (13.3.b) applied to `T` the family `𝒯` contains an irreducible
character `θ` induced from a linear character of `K = QD`, and (13.3.c) for `T` writes the
`τ₁`-image of the distinguished `ν`-row sum as a signed `η`-row.  Packaged in the exact form the
(13.4) contradiction consumes:

* `θT − ν_r` is `K^#`-supported ((13.3.a) for `T`: both are `K`-induced of equal degree `vp`);
* its Dade image (`τ = Ind_T^G` by (13.2.e) for `T`) is `θ° − δ'·∑ⱼ η_{rj}` ((13.3.c) for `T`,
  `τ₁`-additivity);
* `θ° = θ^{τ₁}` is orthogonal to the `η`-grid and to `λ^{τ₁}` ((4.1) + (5.3.b) pairwise
  orthogonality of `η_{ij}`, `λ^{τ₁}`, `θ^{τ₁}`). -/
theorem tSide_theta_package_of_not_caseB [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp)
    (_hne : ¬ (hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p)) :
    ∃ (θT : ClassFunction ↥hyp.T ℂ) (r : Fin hyp.q) (δ' : ℤ) (θG : ClassFunction G ℂ),
      (δ' = 1 ∨ δ' = -1) ∧
      ((θT - ∑ j : Fin hyp.p, hyp.nu r j).support ⊆
        {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1}) ∧
      (ClassFunction.induce hyp.T (θT - ∑ j : Fin hyp.p, hyp.nu r j)
        = θG - (δ' : ℂ) • ∑ j : Fin hyp.p, hyp.eta r j) ∧
      (∀ (i : Fin hyp.q) (j : Fin hyp.p), ClassFunction.inner (hyp.eta i j) θG = 0) ∧
      ClassFunction.inner (chars.tau1S chars.lambda) θG = 0 := by
  sorry

open scoped FiniteInduce in
/-- **Peterfalvi (13.4)**: if `S` contains a degree-`u q` character induced
from a linear character of `P C`, then case (9.7.b) holds for `T`, with
`D = 1` and `v = (q^p - 1) / (q - 1)`.

The third conjunct `|Q| = q^p` is the kernel-order component of "case (9.7.b) holds for `T`"
(the (9.7.b) field model identifies `Q̄` with a field of cardinality `q^p`); it is what the
(13.10) counting reads off ((13.10.3) computes `|Q^#|/|T| = (q^p−1)/(pq^p v)`).

**Proof structure** (issue 9013 追記⁶, textbook 04.15 mmd:49-58): by contradiction.  The T-side
θ-package (`tSide_theta_package_of_not_caseB`, (13.3.b,c)-for-`T`) supplies `β = θ − ν_r` with
`K^#`-support and Dade image `θ° − δ'·∑ⱼ η_{rj}`; the carried S-side (13.3) data give
`α = λ − μ_{j₀}` with `H^#`-support (`H ⊴ S`, equal degrees) and Dade image `λ° − δ·∑ᵢ η_{i1}`.
`(H^#)^G ∩ (K^#)^G = ∅` (`P` centralizes `H`-points, the `K^#`-centralizers lie in `T`, and no
conjugate of `P` fits in `T`), so `(α^τ, β^τ) = 0` — but the bilinear expansion leaves the shared
grid entry `δδ'·⟨η_{r1}, η_{r1}⟩ = ±1`.  Contradiction (`eta_cross_expansion_ne_zero`). -/
theorem lambda_forces_T_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  haveI := hyp.finiteG
  by_contra hne
  -- T-side θ-package from the (13.3.b,c)-for-`T` gate.
  obtain ⟨θT, r, δ', θG, hδ', hβsupp, hβform, hηθ, hLamTheta⟩ :=
    tSide_theta_package_of_not_caseB hG chars hne
  -- S-side (13.3) data: `λ = Ind thetaL` and the distinguished `μ`-column `μ_{j₀} = Ind θlin` with
  -- `τ₁`-image `δ·∑ᵢ η_{i1}`.
  obtain ⟨thetaL, hthetaLirr, hthetaL1, hlamEq, -⟩ := chars.lambda_induced_from_PC_linear
  obtain ⟨j₀, δ, θlin, hδ, hθlinirr, hθlin1, hμeq, hμtau⟩ := chars.mu_col_tau1_eta_col_one
  -- `α = λ − μ_{j₀}` is supported on `H^#` (`H ⊴ S`; both terms `H`-induced of equal degree).
  have hαsupp : (chars.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀).support ⊆
      {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1} := by
    intro s hs
    have hs0 : (chars.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀) s ≠ 0 := hs
    refine ⟨?_, ?_⟩
    · by_contra hsH
      apply hs0
      have hsH' : s ∉ hyp.H.subgroupOf hyp.S := fun h => hsH (Subgroup.mem_subgroupOf.mp h)
      rw [ClassFunction.sub_apply, hlamEq, hμeq,
        ClassFunction.induce_eq_zero_of_not_mem_normal _ hsH',
        ClassFunction.induce_eq_zero_of_not_mem_normal _ hsH', sub_zero]
    · rintro rfl
      apply hs0
      rw [ClassFunction.sub_apply, hlamEq, hμeq, ClassFunction.induce_apply_one,
        ClassFunction.induce_apply_one, hthetaL1, hθlin1, sub_self]
  -- The conjugate closures of `H^#` and `K^#` are disjoint.
  have hdisj := disjoint_conjugatesIntoSet_of_centralizer
    (A_M := {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1})
    (A_N := {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1})
    (fun _y hy => hyp.P_le_centralizer_of_mem_H hG hy.1)
    (fun z hz => QD_sharp_centralizer_le_T hG hyp z hz.1 hz.2)
    (P_conj_forall_not_le_T hG hyp)
  -- Hence `(α^τ, β^τ) = 0`.
  have h0 : ClassFunction.inner
      (ClassFunction.induce hyp.S (chars.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀))
      (ClassFunction.induce hyp.T (θT - ∑ j : Fin hyp.p, hyp.nu r j)) = 0 :=
    inner_induce_induce_eq_zero_of_disjoint hαsupp hβsupp hdisj
  -- Rewrite `α^τ = λ° − δ·∑ᵢ η_{i1}` ((13.2.e)+τ₁-additivity + the (13.3.c) column formula).
  have hαform : ClassFunction.induce hyp.S (chars.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀)
      = chars.tau1S chars.lambda
        - (δ : ℂ) • ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ := by
    conv_lhs => rw [hlamEq, hμeq]
    rw [← chars.tau1S_apply_induce_sub thetaL θlin hthetaLirr hθlinirr, map_sub, ← hlamEq, ← hμeq, hμtau]
  -- The `λ°`-side grid orthogonality, flipped to the expansion brick's slot order.
  have hLamEta : ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (chars.tau1S chars.lambda) (hyp.eta i j) = 0 := by
    intro i j
    have h := chars.tau1S_induce_inner_eta i j thetaL hthetaLirr
    rw [← hlamEq] at h
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h, star_zero]
  -- The bilinear expansion is `δ·δ' ≠ 0` — contradiction.
  rw [hαform, hβform] at h0
  exact eta_cross_expansion_ne_zero hyp.eta (fun i k j l => hyp.eta_orthonormal i k j l)
    (chars.tau1S chars.lambda) θG r ⟨1, hyp.p_prime.one_lt⟩ hLamEta hηθ hLamTheta hδ hδ' h0

open scoped Classical in
/-- `|K^#| = |K| − 1`, `Finset` form. -/
theorem card_sharp_toFinset [Fintype G] (K : Subgroup G) :
    (Set.toFinite (sharpSubgroup K)).toFinset.card = Nat.card ↥K - 1 := by
  classical
  have h : (Set.toFinite (sharpSubgroup K)).toFinset
      = (Finset.univ.filter (· ∈ K)).erase 1 := by
    ext x
    rw [Set.Finite.mem_toFinset, Finset.mem_erase, Finset.mem_filter]
    show x ∈ (K : Set G) \ {1} ↔ _
    rw [Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  rw [h, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, K.one_mem⟩)]
  congr 1
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype]

/-- **Peterfalvi (13.10.3), ℕ form**: `|G| = 1 + |G₀| + [G:S]·|H^#| + [G:T]·|Q^#|` — the
`f = 1` instance of the four-piece split. -/
theorem Hypothesis.card_univ_split [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) (hvd : hyp.v * hyp.d ≠ 1) :
    Nat.card G = 1 + hyp.G0Finset.card
      + hyp.S.index * (Nat.card ↥hyp.H - 1) + hyp.T.index * (Nat.card ↥hyp.Q - 1) := by
  have h := hyp.sum_univ_split hG (fun _ => (1 : ℕ)) (fun _ _ => rfl) hcardQ hvd
  simp only [← Finset.card_eq_sum_ones, Finset.card_univ, smul_eq_mul,
    card_sharp_toFinset] at h
  rw [Nat.card_eq_fintype_card]
  exact h

/-- **`T` normalizes `Q^#`** — the `T`-side mirror of `S_normalizes_H_sharp`, via
`normalizer_Q_eq_T`. -/
theorem T_normalizes_Q_sharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ (l : hyp.T) ⦃a : G⦄, a ∈ OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) →
      (l : G) * a * (l : G)⁻¹ ∈ OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) := by
  have hnorm : Subgroup.normalizer (hyp.Q : Set G) = hyp.T := normalizer_Q_eq_T hG hyp
  intro l a ha
  rw [OddOrder.Peterfalvi.S04.mem_sharp] at ha ⊢
  obtain ⟨haQ, ha1⟩ := ha
  have hlnorm : (l : G) ∈ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hnorm]; exact l.2
  refine ⟨(Subgroup.mem_set_normalizer_iff.mp hlnorm a).mp haQ, ?_⟩
  intro heq
  refine ha1 ?_
  calc a = (l : G)⁻¹ * ((l : G) * a * (l : G)⁻¹) * (l : G) := by group
    _ = 1 := by rw [heq]; group

/-- **The (13.8)-for-`T` Dade hypothesis for the TI-subset `(T, Q^#)`** — the `T`-side mirror of
`H_sharp_dadeHypothesis`, from the proven `Q_sharp_isTISubset` (type V excluded by `vd ≠ 1`).
The foundation of the `T`-side (13.5) ρ-machinery consumed by `exists_caseB_data_eta10_T`. -/
noncomputable def Q_sharp_dadeHypothesis [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S04.Hypothesis G (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T := by
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  refine OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset ?_ ?_ (T_normalizes_Q_sharp hG hyp)
    (Q_sharp_isTISubset hG hyp hvd)
  · intro x hx
    exact OddOrder.Peterfalvi.S04.mem_sharp.mpr
      ⟨Set.mem_univ x, (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).2⟩
  · intro x hx
    exact hQT (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).1

/-- The `(T, Q^#)` Dade datum is conjugation-invariant (`H(a) = ⊥` for the TI construction). -/
theorem Q_sharp_hconj [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    (Q_sharp_dadeHypothesis hG hyp hvd).HConjInvariant :=
  OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl)

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The (7.1) ρ-hypothesis for `(T, Q^#)` — mirror of `H_sharp_hypothesis71`. -/
noncomputable def Q_sharp_hypothesis71 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S09.Hypothesis71 G (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T :=
  { hyp := Q_sharp_dadeHypothesis hG hyp hvd
    τ := ((Q_sharp_dadeHypothesis hG hyp hvd).fullDadeIsometryData
      (Q_sharp_hconj hG hyp hvd)).toDadeIsometryData.toDadeMap
    isDadeMap := ((Q_sharp_dadeHypothesis hG hyp hvd).fullDadeIsometryData
      (Q_sharp_hconj hG hyp hvd)).toDadeIsometryData.isDadeMap
    hConjInvariant := Q_sharp_hconj hG hyp hvd }

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The (7.6) coherent-family datum for `(T, Q^#)` — mirror of `H_sharp_hypothesis76`; the
datum on which the `T`-side (13.5.a) point formula is read off. -/
noncomputable def Q_sharp_hypothesis76 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S09.Hypothesis76 G
      (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T := by
  refine OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDade (Q_sharp_hypothesis71 hG hyp hvd)
    (((Q_sharp_dadeHypothesis hG hyp hvd).fullDadeIsometryData
      (Q_sharp_hconj hG hyp hvd)).toDadeIsometryData.isDadeIsometry) hyp.Q ?_ ?_ rfl
  · rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  · intro l h hh
    have := T_normalizes_Q_sharp hG hyp
    -- `T` normalizes `Q` itself (not just `Q^#`): via the normalizer identity.
    have hnorm : Subgroup.normalizer (hyp.Q : Set G) = hyp.T := normalizer_Q_eq_T hG hyp
    have hlnorm : (l : G) ∈ Subgroup.normalizer (hyp.Q : Set G) := by
      rw [hnorm]; exact l.2
    exact (Subgroup.mem_set_normalizer_iff.mp hlnorm h).mp hh

/-- **`G₀` is cyclic-closed**: closed under `x ↦ x^k` for `k` coprime to `|G|` — the hypothesis
shape of the Galois integrality `exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed` (and of
[Is] Lemma 3.14) that makes the (13.10) atoms `slam`/`seta` rational.  The coprime power is
undone by a further coprime power (Euler), so `x^k = 1` forces `x = 1`, and a conjugate of
`H^#`/`Q^#` hitting `x^k` pulls back to one hitting `x` (subgroups are power-closed). -/
theorem Hypothesis.G0Finset_cyclicClosed [Finite G] (hyp : Hypothesis (G := G)) :
    ∀ x ∈ hyp.G0Finset, ∀ k : ℕ, k.Coprime (Nat.card G) → x ^ k ∈ hyp.G0Finset := by
  intro x hx k hk
  rw [Hypothesis.G0Finset, Set.Finite.mem_toFinset] at hx ⊢
  obtain ⟨hx1, hxH, hxQ⟩ := (hyp.mem_G0_iff x).mp hx
  -- Euler round-trip: `(x^k)^(k^(φ(|G|)−1)) = x`.
  have hN0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  set t := (Nat.card G).totient with htdef
  have ht1 : 1 ≤ t := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)
  set m : ℕ := k ^ (t - 1) with hmdef
  have hround : (x ^ k) ^ m = x := by
    rw [hmdef, ← pow_mul]
    have hkt : k * k ^ (t - 1) = k ^ t := by rw [← pow_succ']; congr 1; omega
    rw [hkt]
    have hord : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
    have hmod : k ^ t ≡ 1 [MOD orderOf x] := (Nat.ModEq.pow_totient hk).of_dvd hord
    rw [pow_eq_pow_iff_modEq.mpr hmod, pow_one]
  -- Conjugates of `K^#` hitting `x^k` pull back to `x`.
  have hpull : ∀ K : Subgroup G, x ^ k ∈ conjClassSet (sharpSubgroup K) →
      x ∈ conjClassSet (sharpSubgroup K) := by
    intro K hmem
    obtain ⟨a, ⟨haK, ha1⟩, g, hg⟩ := mem_conjClassSet.mp hmem
    refine mem_conjClassSet.mpr ⟨a ^ m, ⟨?_, ?_⟩, g, ?_⟩
    · exact SetLike.mem_coe.mpr (pow_mem (SetLike.mem_coe.mp haK) m)
    · intro h1
      rw [Set.mem_singleton_iff] at h1
      refine hx1 ?_
      rw [← hround, ← hg, conj_pow, h1, mul_one, mul_inv_cancel]
    · rw [← conj_pow, hg, hround]
  refine (hyp.mem_G0_iff _).mpr ⟨?_, fun h => hxH (hpull _ h), fun h => hxQ (hpull _ h)⟩
  intro h1
  refine hx1 ?_
  rw [← hround, h1, one_pow]

/-- `|T'| = |Q|·(vd)` — the `T`-side derived-subgroup order decomposition
(`derived_complement` of the reconciled type-`P` datum). -/
theorem Hypothesis.card_deriv_T_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥(derivedInG hyp.T) = Nat.card ↥hyp.Q * (hyp.v * hyp.d) := by
  obtain ⟨tpd, hU, -, -⟩ := reconciled_typePData_T hG hyp
  have h2 := tpd.derived_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.H_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.U_le).toEquiv, tpd.H_eq, ← hyp.Q_eq_TF,
    hU, hyp.card_V_eq_vd] at h2
  exact h2.symm

open scoped FiniteInduce in
/-- **Global Parseval four-piece split** for a norm-`1` class function (the shared spine of the
Peterfalvi (13.10.1)/(13.10.2) estimates):

  `|G| = ‖φ(1)‖² + ∑_{G₀}‖φ‖² + [G:S]·∑_{H^#}‖φ‖² + [G:T]·∑_{Q^#}‖φ‖²`.

The total `∑_G ‖φ‖² = |G|·⟨φ,φ⟩ = |G|` (Parseval, `sum_normSq_eq_card_mul_inner`), split by the
four-piece decomposition `sum_univ_split` (the summand `‖φ(·)‖²` is conjugation-invariant since
`φ` is a class function). -/
theorem Hypothesis.global_normSq_split [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (φ : ClassFunction G ℂ)
    (hn : ClassFunction.inner φ φ = 1)
    (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) (hvd : hyp.v * hyp.d ≠ 1) :
    (Nat.card G : ℝ)
      = ‖φ 1‖ ^ 2 + (∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2)
        + hyp.S.index • (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖φ x‖ ^ 2)
        + hyp.T.index • (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖φ x‖ ^ 2) := by
  have hsplit := hyp.sum_univ_split hG (fun x => ‖φ x‖ ^ 2)
    (fun g x => by
      show ‖φ (g * x * g⁻¹)‖ ^ 2 = ‖φ x‖ ^ 2
      rw [ClassFunction.conj_eq φ x g]) hcardQ hvd
  have htotal : ((∑ x : G, ‖φ x‖ ^ 2 : ℝ) : ℂ) = (Nat.card G : ℂ) := by
    rw [sum_normSq_eq_card_mul_inner, hn, mul_one]
  have htotalR : ∑ x : G, ‖φ x‖ ^ 2 = (Nat.card G : ℝ) := by exact_mod_cast htotal
  rw [← htotalR, hsplit]

end CountingLayer

end OddOrder.Peterfalvi.S15
