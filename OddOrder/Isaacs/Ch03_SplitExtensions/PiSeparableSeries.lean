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
    (hnorm : ∀ i, (K i).Normal) (hmono : ∀ i, K i ≤ K (i + 1)) (hbot : K 0 = ⊥)
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
    {r : ℕ} (hnorm : ∀ i, (K i).Normal) (hmono : ∀ i, K i ≤ K (i + 1))
    (hbot : K 0 = ⊥) (htop : K r = ⊤)
    (hfac : ∀ i, (∀ p ∈ ((K i).relIndex (K (i + 1))).primeFactors, p ∈ π) ∨
      (∀ p ∈ ((K i).relIndex (K (i + 1))).primeFactors, p ∉ π)) :
    IsPiSeparable π G := by
  refine ⟨r, ?_⟩
  have h1 : K r ≤ piFittingSeries π G r :=
    le_piFittingSeries_of_ladder π hnorm hmono hbot hfac r
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
  refine isPiSeparable_of_normal_ladder π (r := 1) hnorm ?_ ?_ ?_ ?_
  · intro i
    rcases Nat.eq_zero_or_pos i with h | h
    · simp [hK, h]
    · simp [hK, Nat.pos_iff_ne_zero.mp h]
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

end -- 3D Lemma 3.18

end OddOrder.Isaacs.Ch03
