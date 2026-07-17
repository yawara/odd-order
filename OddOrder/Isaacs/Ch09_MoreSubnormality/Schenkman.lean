/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Frattini
import OddOrder.Mathlib.Subgroup
import OddOrder.Isaacs.Ch09_MoreSubnormality.NilpotentResidual

/-!
# Isaacs Ch. 9 — §9B: Schenkman's theorem (Lemmas 9.19–9.20, Theorems 9.21–9.22, p. 282)

Wielandt automorphism tower theorem (Thm 9.10) の最終ピース. Schenkman の定理
(`C_G(S^∞) ≤ S^∞` for `S ◁ G` with `C_G(S) = 1`) と, それを支える 2 本の Frattini
補題からなる.

- **Lemma 9.19** (`isNilpotent_of_frattini_le_of_quotient_nilpotent`): `N ◁ G`,
  `N ≤ Φ(G)`, `G/N` nilpotent ⇒ `G` nilpotent.
- **Lemma 9.20** (`exists_nilpotent_sup_eq_top`): `N ◁ G`, `G/N` nilpotent ⇒
  nilpotent `H ≤ G` で `N ⊔ H = ⊤`.
- **Theorem 9.22** (`centralizer_nilpotentResidual_le_of_center_eq_bot`): `Z(G) = 1`
  ⇒ `C_G(G^∞) ≤ G^∞`.
- **Theorem 9.21** (Schenkman, `centralizer_nilpotentResidual_le_of_centralizer_eq_bot`):
  `S ◁ G`, `C_G(S) = 1` ⇒ `C_G(S^∞) ≤ S^∞`.

## 実装ノート

- 9.19: mathlib の `Group.isNilpotent_of_finite_tfae` の同値 (3)「全 coatom が normal」
  ⇒ (1)「nilpotent」を使う. 任意の coatom `M` について `N ≤ Φ(G) ≤ M`
  (`frattini_le_coatom`) ゆえ像 `M̄ = M.map (mk' N)` は `Ḡ = G/N` の coatom
  (`isCoatom_map_of_ker_le`; mathlib は `comap` 方向しか持たないので本ファイルで
  `map` 方向を補う). `Ḡ` nilpotent ⇒ `M̄ ◁ Ḡ` (`NormalizerCondition.normal_of_coatom`),
  `M = comap (mk' N) M̄` (`N ≤ M`) より `M ◁ G`.
- ⚠ mmd 抽出 (L5091, L5095) は 9.19/9.20 の仮定を正しく `N ◁ G` と抽出.
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup QuotientGroup

open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 9B: coatom transport 補助 (mathlib の map 方向補完) -/

/-- `IsCoatom` の `map` 方向 (kernel が coatom 以下): 全射 `φ` と coatom `M ⊇ ker φ`
に対し像 `M.map φ` も coatom. mathlib は `isCoatom_comap_of_surjective` (comap 方向) と
`MulEquiv` 版 `isCoatom_map` しか持たないため, 非同型全射に対する map 方向を補う. -/
theorem isCoatom_map_of_ker_le {H : Type*} [Group H] {φ : G →* H}
    (hφ : Function.Surjective φ) {M : Subgroup G} (hM : IsCoatom M) (hker : φ.ker ≤ M) :
    IsCoatom (M.map φ) := by
  refine ⟨?_, ?_⟩
  · intro htop
    refine hM.1 ?_
    have h : Subgroup.comap φ (M.map φ) = M := by
      rw [Subgroup.comap_map_eq, sup_eq_left.mpr hker]
    rw [htop, Subgroup.comap_top] at h
    exact h.symm
  · intro K' hK'
    rw [← Subgroup.comap_lt_comap_of_surjective hφ, Subgroup.comap_map_eq,
      sup_eq_left.mpr hker] at hK'
    have hcomapK : Subgroup.comap φ K' = ⊤ := hM.2 _ hK'
    calc K' = φ.range ⊓ K' := by
              rw [MonoidHom.range_eq_top_of_surjective φ hφ, top_inf_eq]
      _ = Subgroup.map φ (Subgroup.comap φ K') := (Subgroup.map_comap_eq φ K').symm
      _ = Subgroup.map φ ⊤ := by rw [hcomapK]
      _ = ⊤ := Subgroup.map_top_of_surjective φ hφ

end

section /- 9B: Lemma 9.19 (p. 282) -/

/-- **Isaacs Lemma 9.19** (p. 282): `N ◁ G`, `N ≤ Φ(G)`, `G/N` nilpotent ならば
`G` nilpotent. -/
theorem isNilpotent_of_frattini_le_of_quotient_nilpotent [Finite G] {N : Subgroup G}
    [hN : N.Normal] (hle : N ≤ frattini G) (hquot : Group.IsNilpotent (G ⧸ N)) :
    Group.IsNilpotent G := by
  haveI := hquot
  have hnc : NormalizerCondition (G ⧸ N) := Group.normalizerCondition_of_isNilpotent
  refine ((Group.isNilpotent_of_finite_tfae (G := G)).out 2 0).mp ?_
  intro M hM
  have hNM : N ≤ M := hle.trans (frattini_le_coatom hM)
  have hcoatom : IsCoatom (M.map (QuotientGroup.mk' N)) :=
    isCoatom_map_of_ker_le (QuotientGroup.mk'_surjective N) hM
      (by rw [QuotientGroup.ker_mk']; exact hNM)
  haveI hmapnormal : (M.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom _ hnc hcoatom
  have hMeq : M = Subgroup.comap (QuotientGroup.mk' N) (M.map (QuotientGroup.mk' N)) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNM]
  rw [hMeq]
  infer_instance

end

section /- 9B: Lemma 9.20 (p. 282) -/

/-- **Isaacs Lemma 9.20** (p. 282): `N ◁ G`, `G/N` nilpotent ならば nilpotent な
`H ≤ G` で `N ⊔ H = ⊤` (`NH = G`) が存在する.

証明: `{H | N ⊔ H = ⊤}` の極小元 `E` を取る (`⊤` が属すので非空; 有限). `E` が
nilpotent なことを Lemma 9.19 で示せばよい. `N' = N ⊓ E` について:
- `↥E ⧸ N' ≅ (E の G/N での像) ≤ G/N` は nilpotent (subgroup of nilpotent).
- `N' ≤ Φ(↥E)`: さもなくば coatom `M'` で `N' ⊄ M'`, すると `N' ⊔ M' = ⊤` を
  `G` に押し戻して `N ⊔ (M'.map subtype) = ⊤` かつ `M'.map subtype < E`, 極小性に矛盾. -/
theorem exists_nilpotent_sup_eq_top [Finite G] {N : Subgroup G} [hN : N.Normal]
    (hquot : Group.IsNilpotent (G ⧸ N)) :
    ∃ H : Subgroup G, Group.IsNilpotent ↥H ∧ N ⊔ H = ⊤ := by
  obtain ⟨E, hEmin⟩ :=
    exists_minimal_of_wellFoundedLT (fun H : Subgroup G => N ⊔ H = ⊤) ⟨⊤, by simp⟩
  refine ⟨E, ?_, hEmin.1⟩
  haveI hN'normal : (N.subgroupOf E).Normal := hN.subgroupOf E
  -- `↥E ⧸ N'` は G/N の部分群と同型 ⇒ nilpotent
  have hquotE : Group.IsNilpotent (↥E ⧸ N.subgroupOf E) := by
    set φ := (QuotientGroup.mk' N).comp E.subtype with hφ
    have hker : φ.ker = N.subgroupOf E := by
      rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
    have e : (↥E ⧸ N.subgroupOf E) ≃* ↥φ.range :=
      (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        (QuotientGroup.quotientKerEquivRange φ)
    haveI := hquot
    exact Group.nilpotent_of_mulEquiv e.symm
  -- `N' ≤ Φ(↥E)`
  have hNfrat : N.subgroupOf E ≤ frattini (↥E) := by
    simp only [frattini, Order.radical, le_iInf_iff, Set.mem_setOf_eq]
    intro M' hM'
    by_contra hnle
    -- `N' ⊔ M' = ⊤` (M' coatom, N' ⊄ M')
    have hlt : M' < N.subgroupOf E ⊔ M' :=
      lt_of_le_of_ne le_sup_right fun heq => hnle (le_sup_left.trans_eq heq.symm)
    have hsuptop : N.subgroupOf E ⊔ M' = ⊤ := hM'.2 _ hlt
    -- `G` に押し戻し: `(N ⊓ E) ⊔ (M'.map subtype) = E`
    have hmapsup : N ⊓ E ⊔ M'.map E.subtype = E := by
      have h := congrArg (Subgroup.map E.subtype) hsuptop
      rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h
    -- `N ⊔ (M'.map subtype) = ⊤`
    have hNMtop : N ⊔ M'.map E.subtype = ⊤ := by
      have key : N ⊔ M'.map E.subtype = N ⊔ E := by
        conv_rhs => rw [← hmapsup]
        rw [← sup_assoc, sup_eq_left.mpr (inf_le_left : N ⊓ E ≤ N)]
      rw [key, hEmin.1]
    -- `M'.map subtype < E`
    have hMltE : M'.map E.subtype < E := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le M') fun heq => hM'.1 ?_
      apply Subgroup.map_injective E.subtype_injective
      rw [heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact absurd (hEmin.2 hNMtop hMltE.le) (not_le_of_gt hMltE)
  exact isNilpotent_of_frattini_le_of_quotient_nilpotent hNfrat hquotE

end

section /- 9B: nilpotent 群の nontrivial normal は中心と交わる (9.22 補助) -/

/-- 冪零群の nontrivial な正規部分群は中心と非自明に交わる: `H` nilpotent, `K ◁ H`,
`K ≠ ⊥` ⇒ `K ⊓ Z(H) ≠ ⊥`. (Thm 9.22 で使う; mathlib は `center_ne_bot` (K=⊤) しか持たない.)

証明: upper central series `Z_i` は有限で `⊤` に達する (`nilpotent'`). `K ⊓ Z_i ≠ ⊥`
なら `K ⊓ Z_1 = K ⊓ Z(H) ≠ ⊥` を `i` の帰納法で示す. `K ⊓ Z_j = ⊥` の枝では
`x ∈ K ⊓ Z_{j+1}` (nontrivial) について `⁅x, g⁆ ∈ Z_j` (upper series の定義) かつ
`∈ K` (K 正規) ゆえ `⁅x, g⁆ ∈ K ⊓ Z_j = ⊥` で `x` は中心的. -/
theorem inf_center_ne_bot_of_normal_of_isNilpotent {H : Type*} [Group H]
    [Group.IsNilpotent H] {K : Subgroup H} [hKn : K.Normal] (hK : K ≠ ⊥) :
    K ⊓ Subgroup.center H ≠ ⊥ := by
  obtain ⟨n, hn⟩ := Group.IsNilpotent.nilpotent' (G := H)
  suffices h : ∀ i, K ⊓ Subgroup.upperCentralSeries H i ≠ ⊥ → K ⊓ Subgroup.center H ≠ ⊥ from
    h n (by rw [hn, inf_top_eq]; exact hK)
  intro i
  induction i with
  | zero => rw [Subgroup.upperCentralSeries_zero, inf_bot_eq]; exact fun h => absurd rfl h
  | succ j IH =>
    intro hne
    by_cases hj : K ⊓ Subgroup.upperCentralSeries H j = ⊥
    · obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      obtain ⟨hxK, hxU⟩ := Subgroup.mem_inf.mp a.2
      have hx1 : (a : H) ≠ 1 := fun h => ha1 (by ext; exact h)
      have hxcenter : (a : H) ∈ Subgroup.center H := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hcommU : ⁅(a : H), g⁆ ∈ Subgroup.upperCentralSeries H j :=
          Subgroup.mem_upperCentralSeries_succ_iff.mp hxU g
        have hcommK : ⁅(a : H), g⁆ ∈ K := by
          have heq : ⁅(a : H), g⁆ = (a : H) * (g * (a : H)⁻¹ * g⁻¹) := by
            rw [commutatorElement_def]; group
          rw [heq]
          exact K.mul_mem hxK (hKn.conj_mem (a : H)⁻¹ (K.inv_mem hxK) g)
        have hmem : ⁅(a : H), g⁆ ∈ K ⊓ Subgroup.upperCentralSeries H j :=
          Subgroup.mem_inf.mpr ⟨hcommK, hcommU⟩
        rw [hj, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at hmem
        exact (hmem.symm).eq
      exact Subgroup.ne_bot_iff_exists_ne_one.mpr
        ⟨⟨(a : H), Subgroup.mem_inf.mpr ⟨hxK, hxcenter⟩⟩, fun h => hx1 (congrArg Subtype.val h)⟩
    · exact IH hj

end

section /- 9B: Theorem 9.22 (Schenkman, Z(G) = 1 の場合, p. 282) -/

/-- **Isaacs Theorem 9.22** (p. 282): `Z(G) = 1` ならば `C_G(G^∞) ≤ G^∞`.
Schenkman の定理 (9.21) の `S = G` の場合. -/
theorem centralizer_nilpotentResidual_le_of_center_eq_bot [Finite G]
    (hZ : Subgroup.center G = ⊥) :
    Subgroup.centralizer (↑(nilpotentResidual (⊤ : Subgroup G)) : Set G)
      ≤ nilpotentResidual (⊤ : Subgroup G) := by
  set R := nilpotentResidual (⊤ : Subgroup G) with hR
  set C := Subgroup.centralizer (R : Set G) with hC
  haveI hRnormal : R.Normal := by rw [hR]; infer_instance
  haveI hCnormal : C.Normal := by rw [hC]; infer_instance
  haveI hCRnormal : (C ⊓ R).Normal := inferInstance
  -- G/R nilpotent
  have hGRnil : Group.IsNilpotent (G ⧸ R) := by
    have h := (nilpotentResidual_le_iff_isNilpotent_map (S := (⊤ : Subgroup G)) (N := R)).mp
      (hR ▸ le_rfl)
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
      Group.isNilpotent_top] at h
  -- Claim 1: nilpotent `H` で `R ⊔ H = ⊤` なら `C ⊓ H = ⊥`
  have hclaim1 : ∀ H : Subgroup G, Group.IsNilpotent ↥H → R ⊔ H = ⊤ → C ⊓ H = ⊥ := by
    intro H hHnil hHsup
    haveI := hHnil
    by_contra hne
    haveI hKn : (C.subgroupOf H).Normal := hCnormal.subgroupOf H
    have hKne : C.subgroupOf H ≠ ⊥ := by
      intro hbot
      refine hne ?_
      have h := congrArg (Subgroup.map H.subtype) hbot
      rwa [Subgroup.subgroupOf_map_subtype, Subgroup.map_bot] at h
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (inf_center_ne_bot_of_normal_of_isNilpotent hKne)
    obtain ⟨hwC, hwZ⟩ := Subgroup.mem_inf.mp w.2
    set z : G := ((w : ↥H) : G) with hz
    have hzC : z ∈ C := (Subgroup.mem_subgroupOf).mp hwC
    have hzne : z ≠ 1 := by
      intro h
      exact hw1 (by ext; exact h)
    -- `⊤ ≤ C_G({z})`
    have hcent : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [← hHsup]
      refine sup_le ?_ ?_
      · intro r hr
        rw [Subgroup.mem_centralizer_iff]
        rintro x hx
        rw [Set.mem_singleton_iff] at hx; subst hx
        exact (Subgroup.mem_centralizer_iff.mp hzC r (hR ▸ hr)).symm
      · intro h hh
        rw [Subgroup.mem_centralizer_iff]
        rintro x hx
        rw [Set.mem_singleton_iff] at hx; subst hx
        have hc := Subgroup.mem_center_iff.mp hwZ ⟨h, hh⟩
        have : h * z = z * h := by simpa [hz] using congrArg Subtype.val hc
        exact this.symm
    -- `z ∈ Z(G) = ⊥`, 矛盾
    have hzcenterG : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_top g)) z
        (Set.mem_singleton z)).symm
    rw [hZ, Subgroup.mem_bot] at hzcenterG
    exact hzne hzcenterG
  -- 9.20 で nilpotent `K`, `R ⊔ K = ⊤`
  obtain ⟨K, hKnil, hRK⟩ := exists_nilpotent_sup_eq_top hGRnil
  set T := C ⊔ K with hT
  have hCRT : C ⊓ R ≤ T := inf_le_left.trans le_sup_left
  -- `T^∞ ≤ C ⊓ R`
  have hTR : nilpotentResidual T ≤ R := nilpotentResidual_mono le_top
  have hTC : nilpotentResidual T ≤ C := by
    rw [nilpotentResidual_le_iff_isNilpotent_map]
    have hmap : T.map (QuotientGroup.mk' C) = K.map (QuotientGroup.mk' C) := by
      rw [hT, Subgroup.map_sup,
        (Subgroup.map_eq_bot_iff C).mpr (by rw [QuotientGroup.ker_mk']), bot_sup_eq]
    rw [hmap]
    exact isNilpotent_map _ hKnil
  have hTCR : nilpotentResidual T ≤ C ⊓ R := le_inf hTC hTR
  haveI hN2normal : ((C ⊓ R).subgroupOf T).Normal := hCRnormal.subgroupOf T
  -- `↥T ⧸ N₂` nilpotent
  have hN2nil : Group.IsNilpotent (↥T ⧸ (C ⊓ R).subgroupOf T) := by
    have hle : nilpotentResidual (⊤ : Subgroup ↥T) ≤ (C ⊓ R).subgroupOf T := by
      rw [← Subgroup.map_subtype_le_map_subtype, map_subtype_nilpotentResidual_top,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCRT]
      exact hTCR
    have h := (nilpotentResidual_le_iff_isNilpotent_map (S := (⊤ : Subgroup ↥T))).mp hle
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
      Group.isNilpotent_top] at h
  -- 9.20 を `↥T` で適用
  obtain ⟨H', hH'nil, hH'sup⟩ := exists_nilpotent_sup_eq_top hN2nil
  haveI := hH'nil
  haveI hHnil : Group.IsNilpotent ↥(H'.map T.subtype) :=
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective H' T.subtype T.subtype_injective)
  -- `(C ⊓ R) ⊔ H = T`
  have hCRH_T : (C ⊓ R) ⊔ H'.map T.subtype = T := by
    have h := congrArg (Subgroup.map T.subtype) hH'sup
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCRT,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  -- `R ⊔ H = ⊤` (T を rw で潰すと `H' : Subgroup ↥T` の型依存で motive が壊れるため
  -- hCRH_T は `.le` 経由で使い, join は lattice 補題で操作する)
  have hRH : R ⊔ H'.map T.subtype = ⊤ := by
    have hTle : T ≤ R ⊔ H'.map T.subtype :=
      hCRH_T.symm.le.trans (sup_le (inf_le_right.trans le_sup_left) le_sup_right)
    refine top_le_iff.mp ?_
    calc (⊤ : Subgroup G) = R ⊔ K := hRK.symm
      _ ≤ R ⊔ H'.map T.subtype := sup_le le_sup_left (le_sup_right.trans hTle)
  -- Dedekind: `C = (C ⊓ R) ⊔ (C ⊓ H)`
  have hCdedek : C = (C ⊓ R) ⊔ (C ⊓ H'.map T.subtype) := by
    have hd := Subgroup.inf_sup_eq_sup_inf_of_normal_of_le
      (M := C) (A := H'.map T.subtype) (inf_le_left : C ⊓ R ≤ C)
    rwa [hCRH_T, inf_eq_left.mpr (le_sup_left : C ≤ T)] at hd
  -- Claim 1 で `C ⊓ H = ⊥`
  have hCH_bot : C ⊓ H'.map T.subtype = ⊥ := hclaim1 _ hHnil hRH
  rw [hCH_bot, sup_bot_eq] at hCdedek
  rw [hCdedek]
  exact inf_le_right

end

end OddOrder.Isaacs.Ch09
