/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Problems
import OddOrder.Isaacs.Ch03_SplitExtensions.Basic
import OddOrder.Isaacs.Ch04_Commutators.Main.BaerTrick

/-!
# Isaacs Problem 3C.4 (書籍 p. 90) — 自己中心化極小正規部分群は分裂する

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 3C.4 の形式化
(campaign issue 1055)。

**3C.4**: `M` が有限可解群 `G` の極小正規部分群で `M = C_G(M)` なら, `G` は `M` 上
分裂し, `M` の補元は全て共役。

## 証明 (書籍 Hint に沿う)

`M` は elementary abelian `p`-群 (Thm 3.11)。`M = ⊤` なら `⊥` が唯一の補元。
`M < ⊤` のとき `L/M` を `G/M` の極小正規にとると `q`-elementary abelian (Thm 3.11)。

* **`q ∤ |M|`** (すなわち `q ≠ p`): さもなくば `L` は `p`-群で, `p`-群 `L` の `p`-群 `M`
  への共役作用は非自明な固定点を持つ (Isaacs Lem 4.32 =
  `fixedPoints_ne_bot_of_pgroup_action_pgroup`)。すると `M ⊓ C_G(L)` が非自明な正規部分群
  となり `= M` (極小性), よって `L ≤ C_G(M) = M` で `M < L` に矛盾
  (`inf_centralizer_eq_bot_of_isMinimalNormal_lt`)。
* **分裂**: `Q ∈ Syl_q(L)` をとる。`q ∤ |M|` から `L = MQ`。Frattini 論法
  (`Sylow.normalizer_sup_eq_top`) で `G = L·N_G(Q) = M·N_G(Q)`。`H := N_G(Q)` について
  `M ⊓ H` は `Q` を正規化し `[M ⊓ H, Q] ≤ M ⊓ Q = 1`, また `M` 可換なので
  `M ⊓ H ≤ C_G(MQ) = C_G(L)`, ゆえに `M ⊓ H ≤ M ⊓ C_G(L) = ⊥`。よって `H` は補元。
* **共役性**: `K` を任意の補元とすると Dedekind 式に `L = M(L ⊓ K)` で
  `|L ⊓ K| = |L:M|` は `q`-冪, つまり `L ⊓ K ∈ Syl_q(L)`。Sylow 共役性で
  `(L ⊓ K)^x = Q` (`x ∈ L`) とすると `K^x` は `Q = L ⊓ K^x ⊴ K^x` を正規化するから
  `K^x ≤ H`, 位数が等しいので `K^x = H`。

## Main results

- `inf_centralizer_eq_bot_of_isMinimalNormal_lt` — `M < L ⊴ G` なら `M ⊓ C_G(L) = ⊥`。
- `not_isPGroup_of_isMinimalNormal_centralizer_lt` — `M < L ⊴ G` で `L` は `p`-群になれない。
- `exists_isComplement'_of_isMinimalNormal_centralizer_eq` — **Problem 3C.4 (分裂)**。
- `isComplement'_conj_of_isMinimalNormal_centralizer_eq` — **Problem 3C.4 (補元の共役性)**。
-/

namespace OddOrder.Isaacs.Ch03

open _root_.OddOrder.Isaacs.Ch03.Subgroup Pointwise

section /- 3C: Problem 3C.4 (p. 90) -/

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- `M` が極小正規で `C_G(M) = M`, `L ⊴ G` が `M` を真に含むなら `M ⊓ C_G(L) = ⊥`。

`M ⊓ C_G(L)` は正規部分群で `M` に含まれるから, 極小性で `⊥` か `M`。後者なら
`M ≤ C_G(L)`, 対称性 (`le_centralizer_iff`) で `L ≤ C_G(M) = M` となり `M < L` に矛盾。 -/
theorem inf_centralizer_eq_bot_of_isMinimalNormal_lt
    {M L : Subgroup G} (hmin : Ch02.IsMinimalNormal M)
    (hcent : Subgroup.centralizer (M : Set G) = M) [L.Normal] (hML : M < L) :
    M ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have := hmin.1
  rcases hmin.2.2 (M ⊓ Subgroup.centralizer (L : Set G)) inferInstance inf_le_left with h | h
  · exact h
  · exfalso
    have hMcent : M ≤ Subgroup.centralizer (L : Set G) := inf_eq_left.mp h
    have hLM : L ≤ M := hcent ▸ Subgroup.le_centralizer_iff.mp hMcent
    exact hML.2 hLM

/-- 3C.4 の Hint の核 (`q ∤ |M|` の実体): `M` が極小正規で `C_G(M) = M` のとき,
`M` を真に含む正規部分群 `L` は `p`-群になれない。

`p`-群 `L` の `p`-群 `M` への共役作用は非自明な固定点を持つ (Isaacs Lem 4.32) から
`M ⊓ C_G(L) ≠ ⊥` となり, `inf_centralizer_eq_bot_of_isMinimalNormal_lt` に矛盾。 -/
theorem not_isPGroup_of_isMinimalNormal_centralizer_lt
    {M L : Subgroup G} (hmin : Ch02.IsMinimalNormal M)
    (hcent : Subgroup.centralizer (M : Set G) = M) [L.Normal] (hML : M < L)
    {p : ℕ} [Fact p.Prime] (hL : IsPGroup p ↥L) : False := by
  have := hmin.1
  have : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hmin.2.1
  have hM : IsPGroup p ↥M := hL.to_le hML.le
  -- `L` の `M` への共役作用の固定点部分群は非自明
  have hfix := Ch04.fixedPoints_ne_bot_of_pgroup_action_pgroup hM hL
    (MulAut.conjNormal.comp L.subtype)
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hfix
  obtain ⟨⟨m, hm_fix⟩, hm_ne⟩ := hfix
  -- その固定点は `M ⊓ C_G(L)` の非自明元
  have hmem : (m : G) ∈ M ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨m.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have h1 : ((MulAut.conjNormal.comp L.subtype) ⟨l, hl⟩) m = m := hm_fix ⟨l, hl⟩
    have h2 : l * (m : G) * l⁻¹ = (m : G) := by
      have := congrArg (Subtype.val) h1
      simpa [MulAut.conjNormal_apply] using this
    calc l * (m : G) = l * (m : G) * l⁻¹ * l := by group
      _ = (m : G) * l := by rw [h2]
  rw [inf_centralizer_eq_bot_of_isMinimalNormal_lt hmin hcent hML,
    Subgroup.mem_bot] at hmem
  exact hm_ne (Subtype.ext (by simpa using hmem))

/-- 3C.4 の setup (書籍 Hint): `M < ⊤` のとき, `G/M` の極小正規 `L/M` の引き戻し `L` と
`Q ∈ Syl_q(L)` (`q` は `L/M` の素数) について, `q ∤ |M|`, `|Q| = q`-part of `|L|`,
`|Q| · |M| = |L|`, `M ⊔ Q = L` が全て成り立つ。 -/
private theorem exists_sylow_frattini_setup [Group.IsSolvable G]
    {M : Subgroup G} (hmin : Ch02.IsMinimalNormal M)
    (hcent : Subgroup.centralizer (M : Set G) = M) (hMtop : M ≠ ⊤) :
    ∃ (L : Subgroup G) (q : ℕ) (_ : q.Prime) (Q : Sylow q ↥L),
      L.Normal ∧ M < L ∧ ¬ q ∣ Nat.card ↥M ∧
      Nat.card ↥((Q : Subgroup ↥L).map L.subtype) =
        q ^ ((Nat.card ↥L).factorization q) ∧
      Nat.card ↥((Q : Subgroup ↥L).map L.subtype) * Nat.card ↥M = Nat.card ↥L ∧
      M ⊔ ((Q : Subgroup ↥L).map L.subtype) = L := by
  classical
  have := hmin.1
  -- `G/M` は非自明
  have : Nontrivial (G ⧸ M) := by
    obtain ⟨g, hg⟩ : ∃ g, g ∉ M := by
      by_contra h
      push Not at h
      exact hMtop (top_unique fun g _ => h g)
    exact ⟨QuotientGroup.mk g, 1, fun h => hg ((QuotientGroup.eq_one_iff g).mp h)⟩
  -- `G/M` の極小正規 `Lbar` を取り, elementary abelian `q`-群
  obtain ⟨Lbar, hLbar_min, -⟩ :=
    Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup (G ⧸ M)) top_ne_bot
  obtain ⟨q, hq, hLbar_ea⟩ := minimal_normal_isElementaryAbelian_of_isSolvable hLbar_min
  have : Fact q.Prime := ⟨hq⟩
  have hLbar_pgroup : IsPGroup q ↥Lbar := hLbar_ea.isPGroup
  obtain ⟨k, hLbar_card⟩ := (IsPGroup.iff_card (p := q)).mp hLbar_pgroup
  have := hLbar_min.1
  -- 引き戻し `L`
  set L : Subgroup G := Lbar.comap (QuotientGroup.mk' M) with hL_def
  have hL_normal : L.Normal := Subgroup.Normal.comap hLbar_min.1 _
  have hML_le : M ≤ L := fun m hm => Subgroup.mem_comap.mpr (by
    rw [show (QuotientGroup.mk' M) m = 1 from (QuotientGroup.eq_one_iff m).mpr hm]
    exact Lbar.one_mem)
  have hML : M < L := lt_of_le_of_ne hML_le fun hML_eq => hLbar_min.2.1 (by
    rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) Lbar,
      ← hL_def, ← hML_eq, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'])
  -- `|L| = |Lbar| · |M|`
  have hL_card : Nat.card ↥L = Nat.card ↥Lbar * Nat.card ↥M := by
    rw [hL_def, Subgroup.card_comap_eq_card_mul_card_ker _
      (QuotientGroup.mk'_surjective M) Lbar, QuotientGroup.ker_mk']
  -- `M` は `p`-群で `q ≠ p`, したがって `q ∤ |M|`
  have hqM : ¬ q ∣ Nat.card ↥M := by
    have : Group.IsSolvable ↥M := inferInstance
    obtain ⟨p, hp, hM_ea⟩ := minimal_normal_isElementaryAbelian_of_isSolvable hmin
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨a, hM_card⟩ := (IsPGroup.iff_card (p := p)).mp hM_ea.isPGroup
    intro hdvd
    have hqp : q = p := by
      rw [hM_card] at hdvd
      exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd)
    -- `q = p` なら `L` は `p`-群となり矛盾
    subst hqp
    have hL_pgroup : IsPGroup q ↥L := IsPGroup.of_card (by
      rw [hL_card, hLbar_card, hM_card]
      exact (pow_add q k a).symm)
    exact not_isPGroup_of_isMinimalNormal_centralizer_lt hmin hcent hML hL_pgroup
  -- `(|L|).factorization q = k`
  have hfactL : (Nat.card ↥L).factorization q = k := by
    rw [hL_card, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Finsupp.add_apply, hLbar_card, hq.factorization_pow,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hqM, add_zero]
  -- Sylow `q` of `L`
  obtain ⟨Q⟩ : Nonempty (Sylow q ↥L) := inferInstance
  set Qm : Subgroup G := (Q : Subgroup ↥L).map L.subtype with hQm_def
  have hQm_card : Nat.card ↥Qm = q ^ ((Nat.card ↥L).factorization q) := by
    rw [hQm_def, Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (Subgroup.subtype_injective L)).symm.toEquiv]
    exact Q.card_eq_multiplicity
  have hQm_mul : Nat.card ↥Qm * Nat.card ↥M = Nat.card ↥L := by
    rw [hQm_card, hfactL, hL_card, hLbar_card]
  refine ⟨L, q, hq, Q, hL_normal, hML, hqM, hQm_card, hQm_mul, ?_⟩
  -- `M ⊔ Qm = L`: `L` 内部で `Msub ⊔ Q = ⊤` を card で示して `map` で送る
  have hMsub_card : Nat.card ↥(M.subgroupOf L) = Nat.card ↥M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hML.le).toEquiv
  have hQ_card : Nat.card ↥(Q : Subgroup ↥L) = q ^ ((Nat.card ↥L).factorization q) :=
    Q.card_eq_multiplicity
  -- `Msub ⊓ Q = ⊥` (位数が互いに素)
  have hcop : Nat.Coprime (Nat.card ↥(M.subgroupOf L)) (Nat.card ↥(Q : Subgroup ↥L)) := by
    rw [hMsub_card, hQ_card]
    exact ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqM).symm.pow_right _
  have hbot : M.subgroupOf L ⊓ (Q : Subgroup ↥L) = ⊥ := by
    rw [← Subgroup.card_eq_one]
    exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  -- card で `Msub ⊔ Q = ⊤`
  have : (M.subgroupOf L).Normal := hmin.1.subgroupOf L
  have hsup_card : Nat.card ↥(M.subgroupOf L ⊔ (Q : Subgroup ↥L)) = Nat.card ↥L := by
    have hprod := Ch01.card_mul_card_inf (M.subgroupOf L) (Q : Subgroup ↥L)
    rw [hbot, Subgroup.card_bot, mul_one] at hprod
    have hcoe : ((M.subgroupOf L ⊔ (Q : Subgroup ↥L) : Subgroup ↥L) : Set ↥L) =
        (M.subgroupOf L : Set ↥L) * ((Q : Subgroup ↥L) : Set ↥L) :=
      Subgroup.normal_mul _ _
    rw [show Nat.card ↥(M.subgroupOf L ⊔ (Q : Subgroup ↥L)) =
        Nat.card ↥((M.subgroupOf L : Set ↥L) * ((Q : Subgroup ↥L) : Set ↥L)) from
      Nat.card_congr (Equiv.setCongr hcoe), hprod, hMsub_card, hQ_card,
      hfactL, hL_card, hLbar_card, mul_comm]
  have hsup_top : M.subgroupOf L ⊔ (Q : Subgroup ↥L) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ hsup_card
  -- `map L.subtype` で ambient へ
  have := congrArg (Subgroup.map L.subtype) hsup_top
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hML.le,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  exact this

omit [Finite G] in
/-- `MulAut` の pointwise 作用の `toMonoidEnd` は `MulEquiv.toMonoidHom` と一致する
(spelling 橋; `Subgroup.pointwise_smul_def` は左の形を吐く)。 -/
private theorem toMonoidHom_mulAut_conj (g : G) :
    ((MulDistribMulAction.toMonoidEnd (MulAut G) G) (MulAut.conj g) : G →* G) =
      (MulAut.conj g).toMonoidHom := rfl

omit [Finite G] in
/-- `map L.subtype` は共役写像と交換する (`x ∈ L` による共役)。 -/
private theorem map_conj_map_subtype {L : Subgroup G} (x : ↥L) (P : Subgroup ↥L) :
    (P.map (MulAut.conj x).toMonoidHom).map L.subtype =
      (P.map L.subtype).map (MulAut.conj (x : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

/-- 3C.4 の本体 (`M ≠ ⊤` の場合): `Q ∈ Syl_q(L)` の正規化群 `H = N_G(Q)` が `M` の補元で,
さらに `M` の任意の補元は `H` に共役。 -/
private theorem exists_complement_conj_normalizer [Group.IsSolvable G]
    {M : Subgroup G} (hmin : Ch02.IsMinimalNormal M)
    (hcent : Subgroup.centralizer (M : Set G) = M) (hMtop : M ≠ ⊤) :
    ∃ H : Subgroup G, Subgroup.IsComplement' M H ∧
      ∀ K : Subgroup G, Subgroup.IsComplement' M K →
        ∃ g : G, K.map (MulAut.conj g).toMonoidHom = H := by
  classical
  have := hmin.1
  obtain ⟨L, q, hq, Q, hL_normal, hML, hqM, hQm_card, hQm_mul, hMQL⟩ :=
    exists_sylow_frattini_setup hmin hcent hMtop
  have : Fact q.Prime := ⟨hq⟩
  set Qm : Subgroup G := (Q : Subgroup ↥L).map L.subtype with hQm_def
  set H : Subgroup G := Subgroup.normalizer (Qm : Set G) with hH_def
  -- `M ⊓ Qm = ⊥` (位数が互いに素)
  have hcopM : Nat.Coprime (Nat.card ↥M) (Nat.card ↥Qm) := by
    rw [hQm_card]
    exact ((hq.coprime_iff_not_dvd).mpr hqM).symm.pow_right _
  have hMQm_bot : M ⊓ Qm = ⊥ := by
    rw [← Subgroup.card_eq_one]
    exact Nat.dvd_one.mp (hcopM ▸ Nat.dvd_gcd
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  -- Frattini 論法: `G = M ⊔ H`
  have hFrattini : H ⊔ L = ⊤ := Sylow.normalizer_sup_eq_top Q
  have hMH_top : M ⊔ H = ⊤ := by
    calc M ⊔ H = H ⊔ M := sup_comm M H
      _ = (H ⊔ Qm) ⊔ M := by rw [sup_of_le_left Subgroup.le_normalizer]
      _ = H ⊔ (Qm ⊔ M) := sup_assoc H Qm M
      _ = H ⊔ (M ⊔ Qm) := by rw [sup_comm Qm M]
      _ = H ⊔ L := by rw [hMQL]
      _ = ⊤ := hFrattini
  -- `M ⊓ H` は `Qm` と `M` の両方を中心化するので `C_G(L)` に入り, `⊥`
  have hXcentQ : M ⊓ H ≤ Subgroup.centralizer (Qm : Set G) := by
    intro x hx
    obtain ⟨hxM, hxH⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : x * u * x⁻¹ ∈ Qm := (Subgroup.mem_normalizer_iff.mp hxH u).mp hu
    have h2 : x * u * x⁻¹ * u⁻¹ ∈ Qm := Qm.mul_mem h1 (Qm.inv_mem hu)
    have h3 : x * u * x⁻¹ * u⁻¹ ∈ M := by
      have hconj : u * x⁻¹ * u⁻¹ ∈ M := hmin.1.conj_mem x⁻¹ (M.inv_mem hxM) u
      have : x * (u * x⁻¹ * u⁻¹) ∈ M := M.mul_mem hxM hconj
      simpa [mul_assoc] using this
    have h4 : x * u * x⁻¹ * u⁻¹ ∈ M ⊓ Qm := ⟨h3, h2⟩
    rw [hMQm_bot, Subgroup.mem_bot] at h4
    have hxu : x * u = u * x := by
      have := mul_eq_one_iff_eq_inv.mp h4
      calc x * u = (x * u * x⁻¹ * u⁻¹) * (u * x) := by group
        _ = u * x := by rw [h4, one_mul]
    exact hxu.symm
  have hXcentL : M ⊓ H ≤ Subgroup.centralizer (L : Set G) := by
    rw [← hMQL, Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · exact Subgroup.le_centralizer_iff.mp (inf_le_left.trans (le_of_eq hcent.symm))
    · exact Subgroup.le_centralizer_iff.mp hXcentQ
  have hMH_bot : M ⊓ H = ⊥ := le_bot_iff.mp (by
    rw [← inf_centralizer_eq_bot_of_isMinimalNormal_lt hmin hcent hML]
    exact le_inf inf_le_left hXcentL)
  -- `H` は補元
  have hcompl : Subgroup.IsComplement' M H := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · exact disjoint_iff.mpr hMH_bot
    · rw [← Subgroup.normal_mul M H, hMH_top, Subgroup.coe_top]
  refine ⟨H, hcompl, fun K hK => ?_⟩
  -- 任意の補元 `K`: `L ⊓ K` は `Syl_q(L)`, Sylow 共役で `H` へ
  -- Dedekind: `↑M * ↑(L ⊓ K) = ↑L`
  have hdedekind : (M : Set G) * ((L ⊓ K : Subgroup G) : Set G) = (L : Set G) := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro x ⟨m, hm, k, ⟨hkL, _⟩, rfl⟩
      exact L.mul_mem (hML.le hm) hkL
    · -- `|L| ≤ |M| · |L ⊓ K|`: 各 `x ∈ L` は `x = m k` (補元分解) で `k ∈ L ⊓ K`
      have hsub : (L : Set G) ⊆ (M : Set G) * ((L ⊓ K : Subgroup G) : Set G) := by
        intro x hxL
        obtain ⟨⟨⟨m, hm⟩, ⟨k, hk⟩⟩, hmk⟩ := hK.existsUnique x
        refine ⟨m, hm, k, ⟨?_, hk⟩, hmk.1⟩
        have : k = m⁻¹ * x := by
          rw [← hmk.1]; group
        rw [this]
        exact L.mul_mem (L.inv_mem (hML.le hm)) hxL
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    · exact Set.toFinite _
  have hLK_card : Nat.card ↥(L ⊓ K) = Nat.card ↥Qm := by
    have hprod := Ch01.card_mul_card_inf M (L ⊓ K)
    have hinf : M ⊓ (L ⊓ K) = ⊥ := by
      rw [← inf_assoc, inf_of_le_left hML.le]
      exact disjoint_iff.mp hK.disjoint
    rw [hinf, Subgroup.card_bot, mul_one, hdedekind] at hprod
    -- `|L| = |M| · |L ⊓ K|` と `|Qm| · |M| = |L|` から cancel
    have hprod' : Nat.card ↥L = Nat.card ↥M * Nat.card ↥(L ⊓ K) := hprod
    have hkey : Nat.card ↥M * Nat.card ↥Qm = Nat.card ↥M * Nat.card ↥(L ⊓ K) := by
      rw [mul_comm (Nat.card ↥M) (Nat.card ↥Qm), hQm_mul, hprod']
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hkey).symm
  -- `(L ⊓ K).subgroupOf L ∈ Syl_q(L)` として Sylow 共役で `Q` へ
  have hLKsub_card : Nat.card ↥((L ⊓ K).subgroupOf L) =
      q ^ ((Nat.card ↥L).factorization q) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hLK_card, hQm_card]
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ↥L
    (Sylow.ofCard ((L ⊓ K).subgroupOf L) hLKsub_card) Q
  -- Sylow の共役等式を ambient の Subgroup 等式に落とす: `(L ⊓ K)^x = Qm`
  have hconj_LK : (L ⊓ K).map (MulAut.conj (x : G)).toMonoidHom = Qm := by
    have h0 : MulAut.conj x • ((L ⊓ K).subgroupOf L) = (Q : Subgroup ↥L) := by
      have := congrArg (fun P : Sylow q ↥L => (P : Subgroup ↥L)) hx
      simpa [Sylow.smul_def, Sylow.pointwise_smul_def, Sylow.coe_ofCard,
        Subgroup.inf_subgroupOf_right] using this
    rw [Subgroup.pointwise_smul_def, toMonoidHom_mulAut_conj] at h0
    have := congrArg (Subgroup.map L.subtype) h0
    rwa [map_conj_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left inf_le_left] at this
  -- `L` は共役で不変
  have hLconj : L.map (MulAut.conj (x : G)).toMonoidHom = L := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hL_normal.conj_mem z hz x
    · intro hy
      exact ⟨(x : G)⁻¹ * y * x, by
        simpa using hL_normal.conj_mem y hy (x : G)⁻¹, by simp [MulAut.conj_apply]; group⟩
  -- `K^x` は `M` の補元で `L ⊓ K^x = Qm`
  set Kx : Subgroup G := K.map (MulAut.conj (x : G)).toMonoidHom with hKx_def
  have hLKx : L ⊓ Kx = Qm := by
    have hmap := Subgroup.map_inf L K (MulAut.conj (x : G)).toMonoidHom
      (MulAut.conj (x : G)).injective
    rw [hLconj, hconj_LK] at hmap
    exact hmap.symm
  -- `Kx ≤ H = N_G(Qm)`
  have hKx_le : Kx ≤ H := by
    intro k hk
    rw [hH_def, Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [← hLKx] at hu ⊢
      exact ⟨hL_normal.conj_mem u hu.1 k, Kx.mul_mem (Kx.mul_mem hk hu.2) (Kx.inv_mem hk)⟩
    · intro hu
      rw [← hLKx] at hu ⊢
      refine ⟨?_, ?_⟩
      · have := hL_normal.conj_mem _ hu.1 k⁻¹
        simpa [mul_assoc] using this
      · have := Kx.mul_mem (Kx.mul_mem (Kx.inv_mem hk) hu.2) hk
        simpa [mul_assoc] using this
  -- 位数が等しいので `Kx = H`
  have hcardKH : Nat.card ↥Kx = Nat.card ↥H := by
    have h1 : Nat.card ↥Kx = Nat.card ↥K :=
      Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective
    have h2 : Nat.card ↥M * Nat.card ↥K = Nat.card ↥M * Nat.card ↥H := by
      rw [hK.card_mul_card, hcompl.card_mul_card]
    rw [h1]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
  refine ⟨(x : G), ?_⟩
  have hcard_le : (H : Set G).ncard ≤ (Kx : Set G).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact le_of_eq hcardKH.symm
  exact SetLike.coe_injective (Set.eq_of_subset_of_ncard_le hKx_le hcard_le (Set.toFinite _))

/-- **Isaacs Problem 3C.4, 分裂** (p. 90)。`M` が有限可解群 `G` の極小正規部分群で
`M = C_G(M)` なら, `G` は `M` 上分裂する (`M` の補元が存在する)。 -/
theorem exists_isComplement'_of_isMinimalNormal_centralizer_eq [Group.IsSolvable G]
    {M : Subgroup G} (hmin : Ch02.IsMinimalNormal M)
    (hcent : Subgroup.centralizer (M : Set G) = M) :
    ∃ K : Subgroup G, Subgroup.IsComplement' M K := by
  by_cases hMtop : M = ⊤
  · exact ⟨⊥, hMtop ▸ Subgroup.isComplement'_top_bot⟩
  · obtain ⟨H, hH, -⟩ := exists_complement_conj_normalizer hmin hcent hMtop
    exact ⟨H, hH⟩

/-- **Isaacs Problem 3C.4, 補元の共役性** (p. 90)。`M` が有限可解群 `G` の極小正規部分群で
`M = C_G(M)` なら, `M` の任意の 2 つの補元は共役。 -/
theorem isComplement'_conj_of_isMinimalNormal_centralizer_eq [Group.IsSolvable G]
    {M K K' : Subgroup G} (hmin : Ch02.IsMinimalNormal M)
    (hcent : Subgroup.centralizer (M : Set G) = M)
    (hK : Subgroup.IsComplement' M K) (hK' : Subgroup.IsComplement' M K') :
    ∃ g : G, K.map (MulAut.conj g).toMonoidHom = K' := by
  by_cases hMtop : M = ⊤
  · -- 補元は位数 1, つまり `⊥` しかない
    subst hMtop
    have hbot : ∀ {J : Subgroup G}, Subgroup.IsComplement' ⊤ J → J = ⊥ := by
      intro J hJ
      have h1 := hJ.card_mul_card
      rw [Subgroup.card_top] at h1
      exact Subgroup.card_eq_one.mp
        (Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans (mul_one _).symm))
    rw [hbot hK, hbot hK']
    exact ⟨1, Subgroup.map_bot _⟩
  · obtain ⟨H, -, huniq⟩ := exists_complement_conj_normalizer hmin hcent hMtop
    obtain ⟨g1, hg1⟩ := huniq K hK
    obtain ⟨g2, hg2⟩ := huniq K' hK'
    refine ⟨g2⁻¹ * g1, ?_⟩
    have hcomp : (MulAut.conj (g2⁻¹ * g1)).toMonoidHom =
        ((MulAut.conj g2⁻¹).toMonoidHom).comp (MulAut.conj g1).toMonoidHom := by
      ext y
      simp [mul_assoc]
    have hid : ((MulAut.conj g2⁻¹).toMonoidHom).comp (MulAut.conj g2).toMonoidHom =
        MonoidHom.id G := by
      ext y
      simp [mul_assoc]
    rw [hcomp, ← Subgroup.map_map, hg1, ← hg2, Subgroup.map_map, hid, Subgroup.map_id]

end -- Problem 3C.4

end OddOrder.Isaacs.Ch03
