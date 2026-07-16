/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

/-!
# Isaacs Lemma 3.18: series characterization of π-separability (pp. 90-91)

`IsPiSeparable` (upper π-Fitting series が `⊤` に到達, `Theorem315.lean`) の
**series 特徴付け**を与える. 教科書 (Isaacs FGT p.90) は π-separable を
「π/π' 因子の正規列を持つ」で定義し, Lemma 3.18 で subnormal 列でも十分と
上げる. 本リポジトリは upper series を定義に採ったので, ここで両者を接続:

* `le_piFittingSeries_of_ladder` — **支配補題** (upper series は最速):
  全項 `G`-正規な増大列で各因子 (`relIndex` の素因子) が π-数 または π'-数
  なら, 第 `i` 項は `piFittingSeries π G i` に含まれる.
* `isPiSeparable_of_normal_ladder` — 系: そのような列が `⊤` に到達すれば
  `G` は π-separable.
* `isPiSeparable_of_isPiGroup` — π-群は π-separable (2 項 ladder).

因子条件は quotient 型でなく **`relIndex` の素因子集合**で表す
(`(K i).relIndex (K (i+1))` = 因子群の位数; 型的 instance 依存が消え,
ambient を移しても不変なので subnormal 版 (Lemma 3.18 本体) の帰納にそのまま
使える).

TODO (この leaf の続き): ladder 存在 (π-sep ⇒ normal π/π' ladder), 原子拡大
(π-群 `A ⊴ G` + `G/A` π-sep ⇒ π-sep), 拡大閉包, Lemma 3.18 (subnormal 版).
-/

namespace OddOrder.Isaacs.Ch03

open scoped Pointwise

section /- 3D: Lemma 3.18 series characterization (pp. 90-91) -/

variable {G : Type*} [Group G]

/-- **支配補題** (upper π-Fitting series は最速の π/π'-series): `K` を全項
`G`-正規な増大列で `K 0 = ⊥`, 各因子の位数 `(K i).relIndex (K (i+1))` の素因子が
全て π 内 or 全て π 外とする. このとき `K i ≤ piFittingSeries π G i`.

証明 (標準): `i` 帰納. `Fᵢ := piFittingSeries π G i ⊇ K i` のもとで
`K̄ := (K (i+1)).map (mk' Fᵢ)` は `G/Fᵢ` の正規部分群で, その位数は
`|K (i+1) : Fᵢ ∩ K (i+1)|` すなわち `Fᵢ.relIndex (K (i+1))` に等しく, これは
`K i ≤ Fᵢ` より因子位数 `(K i).relIndex (K (i+1))` を割る. よって `K̄` は
π-群 (or π'-群) となり `O_π(G/Fᵢ) ⊔ O_π'(G/Fᵢ)` に入るので,
`K (i+1) ≤ comap = Fᵢ₊₁`. -/
theorem le_piFittingSeries_of_ladder [Finite G] (π : Set ℕ) {K : ℕ → Subgroup G}
    (hnorm : ∀ i, (K i).Normal) (hbot : K 0 = ⊥)
    (hfac : ∀ i, (∀ p ∈ ((K i).relIndex (K (i + 1))).primeFactors, p ∈ π) ∨
      (∀ p ∈ ((K i).relIndex (K (i + 1))).primeFactors, p ∉ π)) :
    ∀ i, K i ≤ piFittingSeries π G i := by
  intro i
  induction i with
  | zero => rw [hbot, piFittingSeries_zero]
  | succ i ih =>
    set Fi : Subgroup G := piFittingSeries π G i with hFi
    haveI := hnorm (i + 1)
    -- 商での像 K̄ とその位数評価.
    set Kbar : Subgroup (G ⧸ Fi) := (K (i + 1)).map (QuotientGroup.mk' Fi) with hKbar
    haveI hKbarN : Kbar.Normal :=
      (hnorm (i + 1)).map (QuotientGroup.mk' Fi) (QuotientGroup.mk'_surjective Fi)
    have hcard_dvd : Nat.card ↥Kbar ∣ (K i).relIndex (K (i + 1)) := by
      have h1 : Nat.card ↥Kbar =
          Nat.card ((↥(K (i + 1))) ⧸ (Fi.subgroupOf (K (i + 1)))) :=
        (Subgroup.nat_card_quotient_subgroupOf_eq_card_map Fi (K (i + 1))).symm
      have h2 : Nat.card ((↥(K (i + 1))) ⧸ (Fi.subgroupOf (K (i + 1)))) =
          Fi.relIndex (K (i + 1)) := rfl
      rw [h1, h2]
      exact Subgroup.index_dvd_of_le
        (Subgroup.comap_mono (f := (K (i + 1)).subtype) ih)
    have hrel_ne : (K i).relIndex (K (i + 1)) ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    -- 因子の π/π' 性に応じて K̄ を O_π または O_π' に入れる.
    have hle_join : Kbar ≤ oPiCore π (G ⧸ Fi) ⊔ oPiCore {p | p ∉ π} (G ⧸ Fi) := by
      rcases hfac i with hpi | hpi'
      · refine le_trans ?_ le_sup_left
        exact Subgroup.IsPiGroup.le_oPiCore fun p hp =>
          hpi p (Nat.primeFactors_mono hcard_dvd hrel_ne hp)
      · refine le_trans ?_ le_sup_right
        exact Subgroup.IsPiGroup.le_oPiCore fun p hp =>
          hpi' p (Nat.primeFactors_mono hcard_dvd hrel_ne hp)
    calc K (i + 1)
        ≤ Subgroup.comap (QuotientGroup.mk' Fi) Kbar := by
          rw [hKbar]
          exact Subgroup.le_comap_map (f := QuotientGroup.mk' Fi) (K (i + 1))
      _ ≤ Subgroup.comap (QuotientGroup.mk' Fi)
            (oPiCore π (G ⧸ Fi) ⊔ oPiCore {p | p ∉ π} (G ⧸ Fi)) :=
          Subgroup.comap_mono hle_join
      _ = piFittingSeries π G (i + 1) := (piFittingSeries_succ π G i).symm

/-- **正規 π/π'-ladder ⇒ π-separable**: 全項 `G`-正規な増大列 `⊥ = K 0 ≤ ⋯ ≤ K r = ⊤`
で各因子位数の素因子が全て π 内 or 全て π 外なら `G` は π-separable.

Isaacs の定義 (p.90, normal series with π/π' factors) から本リポジトリの
upper-series 定義への橋 (Lemma 3.18 の all-normal 特殊形). -/
theorem isPiSeparable_of_normal_ladder [Finite G] (π : Set ℕ) {K : ℕ → Subgroup G}
    {r : ℕ} (hnorm : ∀ i, (K i).Normal)
    (hbot : K 0 = ⊥) (htop : K r = ⊤)
    (hfac : ∀ i, (∀ p ∈ ((K i).relIndex (K (i + 1))).primeFactors, p ∈ π) ∨
      (∀ p ∈ ((K i).relIndex (K (i + 1))).primeFactors, p ∉ π)) :
    IsPiSeparable π G := by
  refine ⟨r, ?_⟩
  have h1 : K r ≤ piFittingSeries π G r :=
    le_piFittingSeries_of_ladder π hnorm hbot hfac r
  rw [htop] at h1
  exact top_le_iff.mp h1

/-- **π-群は π-separable** (Isaacs p.90 冒頭の注意): 2 項 ladder `⊥ ≤ ⊤` の因子
`|G|` が π-数であることから従う. -/
theorem isPiSeparable_of_isPiGroup [Finite G] {π : Set ℕ} (hG : IsPiGroup π G) :
    IsPiSeparable π G := by
  set K : ℕ → Subgroup G := fun n => if n = 0 then ⊥ else ⊤ with hK
  have hnorm : ∀ i, (K i).Normal := by
    intro i
    rcases Nat.eq_zero_or_pos i with h | h
    · simp only [hK, h, if_pos]; infer_instance
    · simp only [hK, Nat.pos_iff_ne_zero.mp h, if_false]; infer_instance
  refine isPiSeparable_of_normal_ladder π (r := 1) hnorm ?_ ?_ ?_
  · simp [hK]
  · simp [hK]
  · intro i
    left
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      intro p hp
      simp only [hK, if_pos rfl, if_neg (by omega : ¬ (0 + 1 = 0)),
        Subgroup.relIndex_bot_left, Subgroup.card_top] at hp
      exact hG p hp
    · intro p hp
      simp only [hK, if_neg (Nat.pos_iff_ne_zero.mp h), if_neg (by omega : ¬ (i + 1 = 0)),
        Subgroup.relIndex_self, Nat.primeFactors_one] at hp
      exact absurd hp (Finset.notMem_empty p)

/-- 上部 π-Fitting series の **π-半段**: `Fₘ` と `Fₘ₊₁` の間に挟まる
`comap (mk' Fₘ) (O_π(G/Fₘ))`. ladder 構成 (`exists_normal_ladder_of_isPiSeparable`)
で `Fₘ₊₁/Fₘ = O_π ⊔ O_π'` (π-群でも π'-群でもない) を π/π' の 2 因子に割るために使う. -/
private def piHalfStep (π : Set ℕ) (G : Type*) [Group G] (m : ℕ) : Subgroup G :=
  Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G m))
    (oPiCore π (G ⧸ piFittingSeries π G m))

/-- **π-separable ⇒ 正規 π/π'-ladder が存在** (`isPiSeparable_of_normal_ladder` の逆):
`G` が π-separable なら, 全項 `G`-正規な増大列 `⊥ = K 0 ≤ ⋯ ≤ K r = ⊤` で各因子位数の
素因子が全て π 内 or 全て π 外のものが取れる.

構成: 上部列 `Fₘ` の各段を `Fₘ ≤ comap(O_π(G/Fₘ)) ≤ Fₘ₊₁` と 2 分割 (interleave).
第 1 因子 ≅ `O_π(G/Fₘ)` は π-群, 第 2 因子は第 2 同型定理で `O_π'(G/Fₘ)` の商ゆえ
π'-群. -/
theorem exists_normal_ladder_of_isPiSeparable [Finite G] (π : Set ℕ)
    [IsPiSeparable π G] :
    ∃ (K : ℕ → Subgroup G) (r : ℕ),
      (∀ i, (K i).Normal) ∧ (∀ i, K i ≤ K (i + 1)) ∧ K 0 = ⊥ ∧ K r = ⊤ ∧
      ∀ i, (∀ p ∈ ((K i).relIndex (K (i + 1))).primeFactors, p ∈ π) ∨
        (∀ p ∈ ((K i).relIndex (K (i + 1))).primeFactors, p ∉ π) := by
  classical
  obtain ⟨n, hn⟩ := IsPiSeparable.exists_top (π := π) (G := G)
  refine ⟨fun i => if i % 2 = 0 then piFittingSeries π G (i / 2)
      else piHalfStep π G (i / 2), 2 * n, ?_, ?_, ?_, ?_, ?_⟩
  · -- 正規性.
    intro i
    by_cases h : i % 2 = 0
    · simpa only [if_pos h] using piFittingSeries.normal π G (i / 2)
    · simp only [if_neg h]
      exact Subgroup.Normal.comap inferInstance _
  · -- 単調性.
    intro i
    by_cases h : i % 2 = 0
    · have h1 : (i + 1) % 2 ≠ 0 := by omega
      have h2 : (i + 1) / 2 = i / 2 := by omega
      simp only [if_pos h, if_neg h1, h2]
      -- Fₘ = ker (mk' Fₘ) ≤ comap (mk' Fₘ) (O_π).
      intro g hg
      rw [piHalfStep, Subgroup.mem_comap,
        show (QuotientGroup.mk' (piFittingSeries π G (i / 2)) g :
          G ⧸ piFittingSeries π G (i / 2)) = 1 from (QuotientGroup.eq_one_iff g).mpr hg]
      exact Subgroup.one_mem _
    · have h1 : (i + 1) % 2 = 0 := by omega
      have h2 : (i + 1) / 2 = i / 2 + 1 := by omega
      simp only [if_neg h, if_pos h1, h2]
      rw [piHalfStep, piFittingSeries_succ]
      exact Subgroup.comap_mono le_sup_left
  · -- K 0 = ⊥.
    simp [piFittingSeries_zero]
  · -- K (2n) = ⊤.
    have h1 : 2 * n % 2 = 0 := by omega
    have h2 : 2 * n / 2 = n := by omega
    simp only [if_pos h1, h2]
    exact hn
  · -- 因子の π/π' 性.
    intro i
    set m : ℕ := i / 2 with hm
    set f : G →* G ⧸ piFittingSeries π G m := QuotientGroup.mk' (piFittingSeries π G m)
      with hf
    have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective _
    by_cases h : i % 2 = 0
    · -- 因子 ≅ O_π(G/Fₘ): π-群.
      left
      have h1 : (i + 1) % 2 ≠ 0 := by omega
      have h2 : (i + 1) / 2 = m := by omega
      simp only [if_pos h, if_neg h1, h2]
      intro p hp
      have hcomp : piFittingSeries π G m = Subgroup.comap f ⊥ := by
        rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
      rw [hcomp, piHalfStep, Subgroup.relIndex_comap, Subgroup.relIndex_bot_left,
        Subgroup.map_comap_eq_self_of_surjective hf_surj] at hp
      exact oPiCore.isPiGroup π p hp
    · -- 因子 ≅ O_π ⊔ O_π' / O_π: π'-群の商ゆえ π'-群.
      right
      have h1 : (i + 1) % 2 = 0 := by omega
      have h2 : (i + 1) / 2 = m + 1 := by omega
      simp only [if_neg h, if_pos h1, h2]
      intro p hp
      set O : Subgroup (G ⧸ piFittingSeries π G m) :=
        oPiCore π (G ⧸ piFittingSeries π G m) with hO
      set O' : Subgroup (G ⧸ piFittingSeries π G m) :=
        oPiCore {q | q ∉ π} (G ⧸ piFittingSeries π G m) with hO'
      have hstep : piFittingSeries π G (m + 1) = Subgroup.comap f (O ⊔ O') :=
        piFittingSeries_succ π G m
      rw [piHalfStep, hstep, Subgroup.relIndex_comap,
        Subgroup.map_comap_eq_self_of_surjective hf_surj] at hp
      -- hp : p ∈ (O.relIndex (O ⊔ O')).primeFactors — 第 2 同型定理で |O'| を割る.
      have hcard : O.relIndex (O ⊔ O') = O.relIndex O' := by
        have he := QuotientGroup.quotientInfEquivProdNormalQuotient O' O
        have hcongr := Nat.card_congr he.toEquiv
        rw [sup_comm O' O] at hcongr
        exact hcongr.symm
      rw [hcard] at hp
      have hdvd : O.relIndex O' ∣ Nat.card ↥O' :=
        Subgroup.index_dvd_card (O.subgroupOf O')
      exact oPiCore.isPiGroup {q | q ∉ π} p
        (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hp)

/-- **原子拡大** (Lemma 3.18 への中間段): `A ⊴ G` が π-群 or π'-群で `G/A` が
π-separable なら `G` も π-separable.

証明: `G/A` の ladder (`exists_normal_ladder_of_isPiSeparable`) を `mk' A` で
引き戻し, 最下段に `⊥ ≤ A` を前置する. 因子は `relIndex_comap` +
`map_comap` (全射) で商側にそのまま移る. -/
theorem isPiSeparable_of_isPiGroup_normal_of_quotient [Finite G] {π : Set ℕ}
    {A : Subgroup G} [A.Normal]
    (hA : Subgroup.IsPiGroup π A ∨ Subgroup.IsPiGroup {p | p ∉ π} A)
    (hquot : IsPiSeparable π (G ⧸ A)) :
    IsPiSeparable π G := by
  haveI := hquot
  obtain ⟨S, r, hSnorm, hSmono, hSbot, hStop, hSfac⟩ :=
    exists_normal_ladder_of_isPiSeparable (G := G ⧸ A) π
  have hbase : Subgroup.comap (QuotientGroup.mk' A) (S 0) = A := by
    rw [hSbot, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  refine isPiSeparable_of_normal_ladder π
    (K := fun i => match i with
      | 0 => ⊥
      | i + 1 => Subgroup.comap (QuotientGroup.mk' A) (S i))
    (r := r + 1) ?_ rfl ?_ ?_
  · intro i
    match i with
    | 0 => infer_instance
    | i + 1 =>
      haveI := hSnorm i
      exact Subgroup.Normal.comap inferInstance _
  · change Subgroup.comap (QuotientGroup.mk' A) (S r) = ⊤
    rw [hStop]
    exact Subgroup.comap_top _
  · intro i
    match i with
    | 0 =>
      -- 最下段の因子 = |A|.
      have hrel : (⊥ : Subgroup G).relIndex
          (Subgroup.comap (QuotientGroup.mk' A) (S 0)) = Nat.card ↥A := by
        rw [hbase, Subgroup.relIndex_bot_left]
      change (∀ p ∈ ((⊥ : Subgroup G).relIndex
            (Subgroup.comap (QuotientGroup.mk' A) (S 0))).primeFactors, p ∈ π) ∨
          (∀ p ∈ ((⊥ : Subgroup G).relIndex
            (Subgroup.comap (QuotientGroup.mk' A) (S 0))).primeFactors, p ∉ π)
      rw [hrel]
      exact hA
    | i + 1 =>
      -- 上段の因子は商側の因子と一致.
      have heq : (Subgroup.comap (QuotientGroup.mk' A) (S i)).relIndex
          (Subgroup.comap (QuotientGroup.mk' A) (S (i + 1))) =
          (S i).relIndex (S (i + 1)) := by
        rw [Subgroup.relIndex_comap,
          Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective A)]
      change (∀ p ∈ ((Subgroup.comap (QuotientGroup.mk' A) (S i)).relIndex
            (Subgroup.comap (QuotientGroup.mk' A) (S (i + 1)))).primeFactors, p ∈ π) ∨
          (∀ p ∈ ((Subgroup.comap (QuotientGroup.mk' A) (S i)).relIndex
            (Subgroup.comap (QuotientGroup.mk' A) (S (i + 1)))).primeFactors, p ∉ π)
      rw [heq]
      exact hSfac i

/-- **`IsPiSeparable` は群同型で保存される**: ladder が同型でそのまま移送できる
(因子位数は `relIndex_map_map_of_injective` で不変). -/
theorem isPiSeparable_of_mulEquiv {H : Type*} [Group H] [Finite G] [Finite H]
    (e : G ≃* H) {π : Set ℕ} (hG : IsPiSeparable π G) :
    IsPiSeparable π H := by
  haveI := hG
  obtain ⟨K, r, hnorm, hmono, hbot, htop, hfac⟩ :=
    exists_normal_ladder_of_isPiSeparable (G := G) π
  refine isPiSeparable_of_normal_ladder π
    (K := fun i => (K i).map e.toMonoidHom) (r := r) ?_ ?_ ?_ ?_
  · intro i
    haveI := hnorm i
    exact (hnorm i).map e.toMonoidHom e.surjective
  · rw [hbot]
    exact Subgroup.map_bot e.toMonoidHom
  · rw [htop]
    exact Subgroup.map_top_of_surjective e.toMonoidHom e.surjective
  · intro i
    have heq : ((K i).map e.toMonoidHom).relIndex ((K (i + 1)).map e.toMonoidHom) =
        (K i).relIndex (K (i + 1)) :=
      Subgroup.relIndex_map_map_of_injective _ _ e.injective
    rw [heq]
    exact hfac i

/-! ### disjunction lemma の `[IsPiSeparable]` 版 -/

/-- If `O_π(G) = ⊥`, then also `O_π(G/⊥) = ⊥`.

This is the quotient-by-`⊥` bridge used to transfer the first nontrivial
`piFittingSeries` step back from `G ⧸ ⊥` to `G`. -/
private theorem oPiCore_quotient_bot_eq_bot_of_oPiCore_eq_bot
    {G : Type*} [Group G] [Finite G] (π : Set ℕ)
    (hbot : oPiCore π G = ⊥) :
    oPiCore π (G ⧸ (⊥ : Subgroup G)) = ⊥ := by
  let q : G →* G ⧸ (⊥ : Subgroup G) := QuotientGroup.mk' (⊥ : Subgroup G)
  have hq_surj : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hq_inj : Function.Injective q := by
    have hker : q.ker = ⊥ := by
      dsimp [q]
      exact QuotientGroup.ker_mk' (⊥ : Subgroup G)
    exact (MonoidHom.ker_eq_bot_iff q).mp hker
  apply Subgroup.comap_injective hq_surj
  apply le_antisymm
  · rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    exact (oPiCore.comap_le_of_injective π q hq_inj).trans (le_of_eq hbot)
  · rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    exact bot_le

/-- **π-separable disjunction**: a finite nontrivial π-separable group has a nontrivial
first π-Fitting layer, i.e. `O_π(G) ⊔ O_{π'}(G) ≠ ⊥`. -/
theorem oPiCore_sup_ne_bot_of_isPiSeparable
    {G : Type*} [Group G] [Finite G] (π : Set ℕ) [Nontrivial G] [IsPiSeparable π G] :
    (oPiCore π G ⊔ oPiCore {p | p ∉ π} G) ≠ ⊥ := by
  have hF1_ne_bot : piFittingSeries π G 1 ≠ ⊥ := by
    intro hF1
    obtain ⟨n, hn⟩ := IsPiSeparable.exists_top (π := π) (G := G)
    have hQsup_bot : (oPiCore π (G ⧸ (⊥ : Subgroup G)) ⊔
        oPiCore {p | p ∉ π} (G ⧸ (⊥ : Subgroup G))) = ⊥ := by
      apply Subgroup.comap_injective (QuotientGroup.mk'_surjective (⊥ : Subgroup G))
      rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
      -- `piFittingSeries π G 1` は定義 (`piFittingSeries_succ`/`_zero` とも `rfl`) より
      -- ちょうどこの comap (bump 後は simp 経由だと instance 経路がずれるので defeq で渡す).
      exact hF1
    have h_all_bot : ∀ n, piFittingSeries π G n = ⊥ := by
      intro n
      induction n with
      | zero =>
        exact piFittingSeries_zero π G
      | succ n ih =>
        let e : G ⧸ piFittingSeries π G n ≃* G ⧸ (⊥ : Subgroup G) :=
          QuotientGroup.quotientMulEquivOfEq ih
        let Sₙ : Subgroup (G ⧸ piFittingSeries π G n) :=
          oPiCore π (G ⧸ piFittingSeries π G n) ⊔
            oPiCore {p | p ∉ π} (G ⧸ piFittingSeries π G n)
        have hSₙ_map : Sₙ.map e.toMonoidHom =
            oPiCore π (G ⧸ (⊥ : Subgroup G)) ⊔
              oPiCore {p | p ∉ π} (G ⧸ (⊥ : Subgroup G)) := by
          dsimp [Sₙ, e]
          rw [Subgroup.map_sup, oPiCore.map_eq_of_mulEquiv π,
            oPiCore.map_eq_of_mulEquiv {p | p ∉ π}]
        have hSₙ_bot : Sₙ = ⊥ := by
          refine (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom)
            (H := Sₙ) e.injective).mp ?_
          rw [hSₙ_map, hQsup_bot]
        rw [piFittingSeries_succ]
        change Subgroup.comap (QuotientGroup.mk' (piFittingSeries π G n)) Sₙ = ⊥
        rw [hSₙ_bot, MonoidHom.comap_bot, QuotientGroup.ker_mk', ih]
    have htop_bot : (⊤ : Subgroup G) = ⊥ := by
      rw [← hn, h_all_bot n]
    exact top_ne_bot htop_bot
  have hF0_lt : piFittingSeries π G 0 < piFittingSeries π G 1 := by
    refine lt_of_le_of_ne (piFittingSeries_le_succ π G 0) ?_
    intro hEq
    exact hF1_ne_bot (by rw [← hEq, piFittingSeries_zero])
  have hQsup0 :=
    (piFittingSeries_lt_succ_iff π (G := G) 0).mp hF0_lt
  have hQsup : (oPiCore π (G ⧸ (⊥ : Subgroup G)) ⊔
      oPiCore {p | p ∉ π} (G ⧸ (⊥ : Subgroup G))) ≠ ⊥ := by
    -- `piFittingSeries π G 0 = ⊥` は `rfl` (bump 後は simp 経由だと instance 経路が
    -- ずれるので defeq で渡す).
    exact hQsup0
  intro hsup_bot
  have hπ_bot : oPiCore π G = ⊥ := by
    apply le_antisymm ?_ bot_le
    rw [← hsup_bot]
    exact le_sup_left
  have hπ'_bot : oPiCore {p | p ∉ π} G = ⊥ := by
    apply le_antisymm ?_ bot_le
    rw [← hsup_bot]
    exact le_sup_right
  have hQπ_bot : oPiCore π (G ⧸ (⊥ : Subgroup G)) = ⊥ :=
    oPiCore_quotient_bot_eq_bot_of_oPiCore_eq_bot π hπ_bot
  have hQπ'_bot : oPiCore {p | p ∉ π} (G ⧸ (⊥ : Subgroup G)) = ⊥ :=
    oPiCore_quotient_bot_eq_bot_of_oPiCore_eq_bot {p | p ∉ π} hπ'_bot
  exact hQsup (by rw [hQπ_bot, hQπ'_bot, bot_sup_eq])

/-- **π-separable disjunction**, split form:
`O_π(G) ≠ ⊥ ∨ O_{π'}(G) ≠ ⊥`. -/
theorem exists_oPiCore_ne_bot_or_oPi'Core_ne_bot_of_isPiSeparable
    {G : Type*} [Group G] [Finite G] (π : Set ℕ) [Nontrivial G] [IsPiSeparable π G] :
    oPiCore π G ≠ ⊥ ∨ oPiCore {p | p ∉ π} G ≠ ⊥ := by
  have hsup := oPiCore_sup_ne_bot_of_isPiSeparable (G := G) π
  by_cases hπ : oPiCore π G = ⊥
  · right
    intro hπ'
    exact hsup (by rw [hπ, hπ', bot_sup_eq])
  · exact Or.inl hπ

/-- **拡大閉包**: `N ⊴ G` で `↥N` も `G/N` も π-separable なら `G` も π-separable.

証明: `|G|` の強帰納法. `N = ⊥` なら `G ≅ G/⊥` で転送. さもなくば `↥N` の
`O_π(N)` か `O_π'(N)` の非自明な方 `A` を取る
(`oPiCore_sup_ne_bot_of_isPiSeparable`). `A` は `N` で characteristic ゆえ
`A' := A.map N.subtype ⊴ G` (`normal_of_characteristic_of_normal`).
`G/A'` では `N/A'` が π-separable (第 1 同型 + quotient 閉包) で
`(G/A')/(N/A') ≅ G/N` (第 3 同型) も π-separable なので帰納法で `G/A'` が
π-separable. `A'` は π-群 or π'-群なので原子拡大
(`isPiSeparable_of_isPiGroup_normal_of_quotient`) で `G` が π-separable. -/
theorem isPiSeparable_of_normal_of_quotient.{u} {G : Type u} [Group G] [Finite G]
    {π : Set ℕ} {N : Subgroup G} [N.Normal]
    (hN : IsPiSeparable π ↥N) (hQ : IsPiSeparable π (G ⧸ N)) :
    IsPiSeparable π G := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ (G' : Type u) [Group G'] [Finite G'], Nat.card G' = n →
      ∀ (N : Subgroup G') [N.Normal],
        IsPiSeparable π ↥N → IsPiSeparable π (G' ⧸ N) → IsPiSeparable π G'
  suffices hmain : motive (Nat.card G) by exact hmain G rfl N hN hQ
  refine Nat.strong_induction_on (Nat.card G) ?_
  intro n ih G' _ _ hcard N _ hN hQ
  by_cases hbot : N = ⊥
  · subst hbot
    exact isPiSeparable_of_mulEquiv (QuotientGroup.quotientBot (G := G')) hQ
  · haveI := hN
    haveI hNnt : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hbot
    have hsup := oPiCore_sup_ne_bot_of_isPiSeparable (G := ↥N) π
    -- 非自明な characteristic π-群 or π'-群 `A ≤ N` を選ぶ.
    obtain ⟨A, hA_pi, hA_ne, hA_char⟩ :
        ∃ A : Subgroup ↥N,
          (Subgroup.IsPiGroup π A ∨ Subgroup.IsPiGroup {p | p ∉ π} A) ∧
          A ≠ ⊥ ∧ A.Characteristic := by
      by_cases h1 : oPiCore π ↥N = ⊥
      · refine ⟨oPiCore {p | p ∉ π} ↥N, Or.inr (oPiCore.isPiGroup _), ?_, inferInstance⟩
        intro h2
        exact hsup (by rw [h1, h2, sup_idem])
      · exact ⟨oPiCore π ↥N, Or.inl (oPiCore.isPiGroup _), h1, inferInstance⟩
    haveI := hA_char
    haveI hA'_normal : (A.map N.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hA'_ne : A.map N.subtype ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff]
      exact hA_ne
    have hA'_pi : Subgroup.IsPiGroup π (A.map N.subtype) ∨
        Subgroup.IsPiGroup {p | p ∉ π} (A.map N.subtype) := by
      have hcardEq : Nat.card ↥(A.map N.subtype) = Nat.card ↥A :=
        Nat.card_congr
          (Subgroup.equivMapOfInjective A N.subtype N.subtype_injective).symm.toEquiv
      refine hA_pi.imp (fun h p hp => ?_) (fun h p hp => ?_)
      · rw [hcardEq] at hp; exact h p hp
      · rw [hcardEq] at hp; exact h p hp
    -- `N/A'` は π-separable (第 1 同型 + quotient 閉包).
    set f₀ : ↥N →* G' ⧸ A.map N.subtype :=
      (QuotientGroup.mk' (A.map N.subtype)).comp N.subtype with hf₀
    have hker : f₀.ker = A := by
      rw [hf₀, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective A
    have hrange : f₀.range = N.map (QuotientGroup.mk' (A.map N.subtype)) := by
      rw [hf₀, MonoidHom.range_comp, Subgroup.range_subtype]
    haveI hNsub_sep : IsPiSeparable π (↥N ⧸ f₀.ker) :=
      isPiSeparable_of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq hker.symm)
        (quotient_isPiSeparable π ↥N A)
    haveI hN'_normal : (N.map (QuotientGroup.mk' (A.map N.subtype))).Normal :=
      Subgroup.Normal.map ‹N.Normal› _ (QuotientGroup.mk'_surjective _)
    haveI hN'_sep : IsPiSeparable π ↥(N.map (QuotientGroup.mk' (A.map N.subtype))) :=
      isPiSeparable_of_mulEquiv
        ((QuotientGroup.quotientKerEquivRange f₀).trans
          (MulEquiv.subgroupCongr hrange)) hNsub_sep
    -- `(G/A')/(N/A') ≅ G/N` は π-separable (第 3 同型).
    haveI hQQ_sep : IsPiSeparable π
        ((G' ⧸ A.map N.subtype) ⧸ N.map (QuotientGroup.mk' (A.map N.subtype))) :=
      isPiSeparable_of_mulEquiv
        (QuotientGroup.quotientQuotientEquivQuotient (A.map N.subtype) N
          (Subgroup.map_subtype_le A)).symm hQ
    -- 帰納法で `G/A'` が π-separable → 原子拡大で締める.
    have hlt : Nat.card (G' ⧸ A.map N.subtype) < n := by
      haveI : Nontrivial ↥(A.map N.subtype) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hA'_ne
      calc Nat.card (G' ⧸ A.map N.subtype)
          < Nat.card (G' ⧸ A.map N.subtype) * Nat.card ↥(A.map N.subtype) :=
            (lt_mul_iff_one_lt_right Nat.card_pos).mpr Finite.one_lt_card
        _ = n := by
            rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup (A.map N.subtype),
              hcard]
    exact isPiSeparable_of_isPiGroup_normal_of_quotient hA'_pi
      (ih _ hlt (G' ⧸ A.map N.subtype) rfl _ hN'_sep hQQ_sep)

/-- **Isaacs Lemma 3.18**: `⊥ = K 0 ⊴ K 1 ⊴ ⋯ ⊴ K r = ⊤` を **subnormal 列**
(隣接項のみ正規: `(K i).subgroupOf (K (i+1))` が normal) とし, 各因子位数
`(K i).relIndex (K (i+1))` の素因子が全て π 内 or 全て π 外とする. このとき
`G` は π-separable.

教科書 (p.90) は「π-separable の characteristic 列で精密化」する証明だが,
ここでは列長 `r` の帰納 + 拡大閉包 (`isPiSeparable_of_normal_of_quotient`) で
組み立てる: `N := K r ⊴ G` に制限列 `(K (min i r)).subgroupOf N` を落として
帰納法で `↥N` が π-separable, 最上段因子 `|G:N|` は π-数 or π'-数なので
`G/N` は π-群 or π'-群 → π-separable, 拡大閉包で `G` が π-separable. -/
theorem isPiSeparable_of_subnormal_ladder.{u} {G : Type u} [Group G] [Finite G]
    (π : Set ℕ) {K : ℕ → Subgroup G} {r : ℕ}
    (hmono : ∀ i, K i ≤ K (i + 1))
    (hnorm : ∀ i, ((K i).subgroupOf (K (i + 1))).Normal)
    (hbot : K 0 = ⊥) (htop : K r = ⊤)
    (hfac : ∀ i, (∀ p ∈ ((K i).relIndex (K (i + 1))).primeFactors, p ∈ π) ∨
      (∀ p ∈ ((K i).relIndex (K (i + 1))).primeFactors, p ∉ π)) :
    IsPiSeparable π G := by
  classical
  suffices hmain : ∀ r : ℕ,
      ∀ (G' : Type u) [Group G'] [Finite G'] (K : ℕ → Subgroup G'),
        (∀ i, K i ≤ K (i + 1)) →
        (∀ i, ((K i).subgroupOf (K (i + 1))).Normal) →
        K 0 = ⊥ → K r = ⊤ →
        (∀ i, (∀ p ∈ ((K i).relIndex (K (i + 1))).primeFactors, p ∈ π) ∨
          (∀ p ∈ ((K i).relIndex (K (i + 1))).primeFactors, p ∉ π)) →
        IsPiSeparable π G' by
    exact hmain r G K hmono hnorm hbot htop hfac
  intro r
  induction r with
  | zero =>
    intro G' _ _ K _ _ hbot htop _
    exact ⟨0, (piFittingSeries_zero π G').trans (hbot ▸ htop)⟩
  | succ r ih =>
    intro G' _ _ K hmono hnorm hbot htop hfac
    have hchain : Monotone K := monotone_nat_of_le_succ hmono
    -- `N := K r` は `G'` で正規 (`K (r+1) = ⊤`).
    haveI hN_normal : (K r).Normal := by
      have hnr := hnorm r
      constructor
      intro n hn g
      have hg' : g ∈ K (r + 1) := by rw [htop]; trivial
      have hn'' : (⟨n, by rw [htop]; trivial⟩ : ↥(K (r + 1))) ∈
          (K r).subgroupOf (K (r + 1)) := by
        rw [Subgroup.mem_subgroupOf]; exact hn
      have hconj := hnr.conj_mem _ hn'' ⟨g, hg'⟩
      rw [Subgroup.mem_subgroupOf] at hconj
      exact hconj
    -- 制限列で `↥(K r)` は π-separable (帰納法).
    have hN_sep : IsPiSeparable π ↥(K r) := by
      refine ih ↥(K r) (fun i => (K (min i r)).subgroupOf (K r)) ?_ ?_ ?_ ?_ ?_
      · intro i
        exact Subgroup.comap_mono (hchain (by omega : min i r ≤ min (i + 1) r))
      · intro i
        by_cases h : i + 1 ≤ r
        · -- i + 1 ≤ r: 元の subnormality を iso 経由で転送.
          have h1 : min i r = i := by omega
          have h2 : min (i + 1) r = i + 1 := by omega
          rw [h1, h2]
          have hKN : K (i + 1) ≤ K r := hchain (by omega)
          have hset : ((K i).subgroupOf (K r)).subgroupOf
              ((K (i + 1)).subgroupOf (K r)) =
              ((K i).subgroupOf (K (i + 1))).comap
                (Subgroup.subgroupOfEquivOfLe hKN).toMonoidHom := by
            ext x
            exact Iff.rfl
          rw [hset]
          haveI := hnorm i
          exact Subgroup.Normal.comap inferInstance _
        · -- i ≥ r: 両項一致 (⊤) で自明.
          have h1 : min i r = r := by omega
          have h2 : min (i + 1) r = r := by omega
          rw [h1, h2, Subgroup.subgroupOf_self]
          infer_instance
      · rw [show min 0 r = 0 from by omega, hbot, Subgroup.bot_subgroupOf]
      · rw [min_self, Subgroup.subgroupOf_self]
      · intro i
        by_cases h : i + 1 ≤ r
        · have h1 : min i r = i := by omega
          have h2 : min (i + 1) r = i + 1 := by omega
          rw [h1, h2, Subgroup.relIndex_subgroupOf (hchain (by omega : i + 1 ≤ r))]
          exact hfac i
        · have h1 : min i r = r := by omega
          have h2 : min (i + 1) r = r := by omega
          rw [h1, h2]
          left
          intro p hp
          rw [Subgroup.relIndex_self, Nat.primeFactors_one] at hp
          exact absurd hp (Finset.notMem_empty p)
    -- 最上段因子 `|G' : K r|` は π-数 or π'-数 → `G'/K r` は π-separable.
    have hidx : (K r).relIndex (K (r + 1)) = (K r).index := by
      rw [htop, Subgroup.relIndex_top_right]
    have hQfac := hfac r
    rw [hidx] at hQfac
    have hQ_sep : IsPiSeparable π (G' ⧸ K r) := by
      have hcardQ : Nat.card (G' ⧸ K r) = (K r).index := rfl
      rcases hQfac with hπ | hπ'
      · exact isPiSeparable_of_isPiGroup fun p hp => hπ p (by rwa [hcardQ] at hp)
      · have h1 : IsPiSeparable {p | p ∉ π} (G' ⧸ K r) :=
          isPiSeparable_of_isPiGroup fun p hp => hπ' p (by rwa [hcardQ] at hp)
        have h2 := isPiSeparable_compl {p | p ∉ π} (G' ⧸ K r) h1
        have hππ : {p : ℕ | p ∉ {q : ℕ | q ∉ π}} = π := by
          ext p
          simp
        rwa [hππ] at h2
    -- 拡大閉包で締める.
    exact isPiSeparable_of_normal_of_quotient hN_sep hQ_sep

end -- 3D Lemma 3.18

end OddOrder.Isaacs.Ch03
