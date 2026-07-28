/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Problems
import OddOrder.Isaacs.Ch03_SplitExtensions.Basic

/-!
# Isaacs Problems 3C (書籍 pp. 90–91) — Hall 部分群と Sylow system

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 3C の形式化
(campaign issue 1055)。

* **3C.1** (Hall D-定理) は `Ch03_SplitExtensions/Basic.lean` の `hall_D` として landing 済。
* **3C.2**: `π` の各素数 `p` について `p`-補元 (= Hall `{p}ᶜ`-部分群) `H_p` が存在するなら,
  それらの交わりは Hall `π'`-部分群。→ `isHallSubgroup_finset_inf_of_pComplement`。
* **3C.3**: **Sylow system** (各素因子の Sylow を 1 つずつ, 対ごとに集合積が可換な族)。
  (a) Sylow system を持てば全ての `π` に Hall `π`-部分群が存在
  (`IsSylowSystem.exists_isHallSubgroup`)。
  (b) 可解群は Sylow system を持つ (`exists_isSylowSystem`)。

## 3C.2 の証明

有限集合 `s` の帰納。`s = ∅` なら交わりは `⊤` で Hall `univ`。
`insert p t` では `X := H p ⊓ t.inf H` について

* **位数**: `X ≤ H p` と `X ≤ t.inf H` から `|X|` は両者の位数を割るので, その素因子は
  `p` も `t` の元も避ける。
* **指数**: `(H p).index` の素因子は `{p}` のみ, `(t.inf H).index` の素因子は `t` に入るので,
  `p ∉ t` より互いに素。したがって `X.index = (H p).index · (t.inf H).index`
  (`index_inf_eq_mul_of_coprime`) で, その素因子は `insert p t` に収まる。

## 3C.3 の証明

**(a)**: 集合積が可換な 2 部分群の積は部分群 (`mulSubgroupOfComm`)。素因子集合
`t ⊆ π` 上の `Finset` 帰納で積部分群 `K = ∏_{p ∈ t} P p` を組み立てる
(`sylowSystem_prod_aux`): 位数の素因子が `t` に収まること・族の他のメンバーとの
可換性が帰納で保たれる。Hall 性の指数側は「`r ∈ π` が `K.index` を割るなら
`P r ≤ K` から `K.index ∣ (P r).index`, これは Sylow 性 (`(P r).index` は `r` と
互いに素) に矛盾」で, 位数の数値計算なしに出る。

**(b)** (書籍 Hint): Hall E-定理で各素数 `q` の `q`-補元 `Hc q` を取り,
`P p := ⋂_{q ∈ pf(|G|) \ {p}} Hc q` (1 つを除く全部の交わり) と置く。3C.2 より
`P p` は Hall `(pf \ {p})ᶜ`-部分群, すなわち Sylow `p`-部分群。可換性は
`K := ⋂_{q ∈ pf \ {p,q}} Hc q` (2 つを除く交わり) について `P p · P q ⊆ K` と
`|K| = |P p| · |P q|` (両辺の素因数分解を `IsHallSubgroup.factorization_card_of_mem` /
`_of_notMem` で比較) から `P p · P q = K = P q · P p`。

## Main results

- `index_inf_eq_mul_of_coprime` — 指数が互いに素な 2 部分群の交わりの指数は積。
- `isHallSubgroup_finset_inf_of_pComplement` — **Problem 3C.2**。
- `IsHallSubgroup.factorization_card_of_mem` / `_of_notMem` — Hall 部分群の位数の付値。
- `mulSubgroupOfComm` — 集合積が可換な 2 部分群の積部分群。
- `IsSylowSystem` — Sylow system の定義。
- `IsSylowSystem.exists_isHallSubgroup` — **Problem 3C.3 (a)**。
- `exists_isSylowSystem` — **Problem 3C.3 (b)**。
-/

namespace OddOrder.Isaacs.Ch03

open Subgroup

section /- 3C: Problem 3C.2 (p. 90) -/

variable {G : Type*} [Group G] [Finite G]

/-- 指数が互いに素な 2 つの部分群について, 交わりの指数は指数の積。

`H.index ∣ (H ⊓ K).index` と `K.index ∣ (H ⊓ K).index` (指数は包含に沿って割る) から
互いに素性で `H.index · K.index ∣ (H ⊓ K).index`, 逆向きは `Subgroup.index_inf_le`。 -/
theorem index_inf_eq_mul_of_coprime {H K : Subgroup G}
    (hcop : Nat.Coprime H.index K.index) : (H ⊓ K).index = H.index * K.index := by
  have hHne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hKne : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hIne : (H ⊓ K).index ≠ 0 := Subgroup.index_inf_ne_zero hHne hKne
  have h1 : H.index ∣ (H ⊓ K).index := Subgroup.index_dvd_of_le inf_le_left
  have h2 : K.index ∣ (H ⊓ K).index := Subgroup.index_dvd_of_le inf_le_right
  have h3 : H.index * K.index ∣ (H ⊓ K).index := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2
  exact le_antisymm Subgroup.index_inf_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hIne) h3)

/-- **Isaacs Problem 3C.2** (p. 90)。素数の有限集合 `s` の各元 `p` について `p`-補元
(= Hall `{p}ᶜ`-部分群) `H p` が存在するなら, それらの交わりは Hall `(↑s)ᶜ`-部分群。

書籍は「素数の集合 `π`」で述べるが, Hall 性は `|G|` の素因子にしか依らないので
有限集合版で十分 (`π` のうち `|G|` を割らない素数の補元は `⊤` になる)。 -/
theorem isHallSubgroup_finset_inf_of_pComplement (s : Finset ℕ) (H : ℕ → Subgroup G)
    (hH : ∀ p ∈ s, IsHallSubgroup ({p}ᶜ : Set ℕ) (H p)) :
    IsHallSubgroup ((↑s : Set ℕ)ᶜ) (s.inf H) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun q _ => by simp, fun q hq => ?_⟩
    rw [Finset.inf_empty, Subgroup.index_top] at hq
    simp at hq
  | @insert p t hpt ih =>
    have hHp : IsHallSubgroup ({p}ᶜ : Set ℕ) (H p) := hH p (Finset.mem_insert_self _ _)
    have hHt : IsHallSubgroup ((↑t : Set ℕ)ᶜ) (t.inf H) :=
      ih (fun q hq => hH q (Finset.mem_insert_of_mem hq))
    rw [Finset.inf_insert]
    -- 指数の互いに素性
    have hcop : Nat.Coprime (H p).index (t.inf H).index := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
      have hqp : q ∈ (H p).index.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hq, hqd.trans (Nat.gcd_dvd_left _ _),
          Subgroup.index_ne_zero_of_finite⟩
      have hqt : q ∈ (t.inf H).index.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hq, hqd.trans (Nat.gcd_dvd_right _ _),
          Subgroup.index_ne_zero_of_finite⟩
      have h1 : q = p := by
        have := hHp.2 q hqp
        simpa using this
      have h2 : q ∈ t := by
        have := hHt.2 q hqt
        simpa using this
      exact hpt (h1 ▸ h2)
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · -- 位数の素因子は `insert p t` を避ける
      have hdvdp : Nat.card ↥(H p ⊓ t.inf H) ∣ Nat.card ↥(H p) :=
        Subgroup.card_dvd_of_le inf_le_left
      have hdvdt : Nat.card ↥(H p ⊓ t.inf H) ∣ Nat.card ↥(t.inf H) :=
        Subgroup.card_dvd_of_le inf_le_right
      have hp' : q ∈ ({p}ᶜ : Set ℕ) :=
        hHp.1 q (Nat.primeFactors_mono hdvdp Nat.card_pos.ne' hq)
      have ht' : q ∈ ((↑t : Set ℕ)ᶜ) :=
        hHt.1 q (Nat.primeFactors_mono hdvdt Nat.card_pos.ne' hq)
      simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_or]
      exact ⟨by simpa using hp', by simpa using ht'⟩
    · -- 指数の素因子は `insert p t` に入る
      rw [index_inf_eq_mul_of_coprime hcop] at hq
      rw [Nat.primeFactors_mul Subgroup.index_ne_zero_of_finite
        Subgroup.index_ne_zero_of_finite] at hq
      rcases Finset.mem_union.mp hq with h | h
      · have := hHp.2 q h
        simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_not]
        exact Or.inl (by simpa using this)
      · have := hHt.2 q h
        simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_not]
        exact Or.inr (by simpa using this)

end -- Problem 3C.2

section /- 3C: Problem 3C.3 (p. 90) — Sylow systems -/

open Pointwise

variable {G : Type*} [Group G] [Finite G]

/-- Hall `π`-部分群の位数の素数 `r` での付値は, `r ∈ π` なら `|G|` のそれに一致する
(`|H| · |G:H| = |G|` で, Hall 性から指数は `r` を割らない)。 -/
theorem IsHallSubgroup.factorization_card_of_mem {π : Set ℕ} {H : Subgroup G}
    (h : IsHallSubgroup π H) {r : ℕ} (hr : r ∈ π) :
    (Nat.card H).factorization r = (Nat.card G).factorization r := by
  have hidx : H.index.factorization r = 0 := by
    by_contra hne
    have : r ∈ H.index.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr hne
    exact h.2 r this hr
  have hG : (Nat.card G).factorization r =
      (Nat.card H).factorization r + H.index.factorization r := by
    rw [← Subgroup.card_mul_index H,
      Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply]
  omega

omit [Finite G] in
/-- Hall `π`-部分群の位数の素数 `r` での付値は, `r ∉ π` なら `0`
(位数の素因子は全て `π` に入るから)。 -/
theorem IsHallSubgroup.factorization_card_of_notMem {π : Set ℕ} {H : Subgroup G}
    (h : IsHallSubgroup π H) {r : ℕ} (hr : r ∉ π) :
    (Nat.card H).factorization r = 0 := by
  by_contra hne
  have : r ∈ (Nat.card H).primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr hne
  exact hr (h.1 r this)

/-- 集合積が可換 (`↑H * ↑K = ↑K * ↑H`) な 2 部分群の集合積を carrier とする部分群。
`H ⊔ K` と一致するが, carrier が `↑H * ↑K` に definitionally 等しい形で使う。 -/
def mulSubgroupOfComm (H K : Subgroup G)
    (hcomm : (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G)) : Subgroup G where
  carrier := (H : Set G) * (K : Set G)
  one_mem' := ⟨1, H.one_mem, 1, K.one_mem, one_mul 1⟩
  mul_mem' := by
    rintro x y ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
    have hmid : (k₁ : G) * h₂ ∈ (H : Set G) * (K : Set G) := by
      rw [hcomm]
      exact ⟨k₁, hk₁, h₂, hh₂, rfl⟩
    obtain ⟨h₃, hh₃, k₃, hk₃, hmid_eq⟩ := hmid
    have hmid_eq' : h₃ * k₃ = k₁ * h₂ := hmid_eq
    refine ⟨h₁ * h₃, H.mul_mem hh₁ hh₃, k₃ * k₂, K.mul_mem hk₃ hk₂, ?_⟩
    calc h₁ * h₃ * (k₃ * k₂) = h₁ * (h₃ * k₃) * k₂ := by group
      _ = h₁ * (k₁ * h₂) * k₂ := by rw [hmid_eq']
      _ = h₁ * k₁ * (h₂ * k₂) := by group
  inv_mem' := by
    rintro x ⟨h, hh, k, hk, rfl⟩
    have hmem : (k : G)⁻¹ * h⁻¹ ∈ (K : Set G) * (H : Set G) :=
      ⟨k⁻¹, K.inv_mem hk, h⁻¹, H.inv_mem hh, rfl⟩
    rw [← hcomm] at hmem
    simpa [mul_inv_rev] using hmem

omit [Finite G] in
@[simp]
theorem coe_mulSubgroupOfComm (H K : Subgroup G)
    (hcomm : (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G)) :
    (mulSubgroupOfComm H K hcomm : Set G) = (H : Set G) * (K : Set G) := rfl

/-- **Sylow system** (Isaacs Problem 3C.3, p. 90): `|G|` の各素因子 `p` について Sylow
`p`-部分群 (= Hall `{p}`-部分群) を 1 つずつ選んだ族で, どの 2 つも集合積が可換
(`PQ = QP`) なもの。

書籍は「Sylow 部分群の集合 `S`」として述べるが, 素因子で添字づけた族
`P : ℕ → Subgroup G` として形式化する (素因子以外での値は使わない)。 -/
def IsSylowSystem (P : ℕ → Subgroup G) : Prop :=
  (∀ p ∈ (Nat.card G).primeFactors, IsHallSubgroup {p} (P p)) ∧
  ∀ p ∈ (Nat.card G).primeFactors, ∀ q ∈ (Nat.card G).primeFactors,
    (P p : Set G) * (P q : Set G) = (P q : Set G) * (P p : Set G)

/-- 3C.3 (a) の帰納エンジン: Sylow system の部分族 `t` について, その積は部分群 `K` を成し,
`t` の各メンバーを含み, `|K|` の素因子は `t` に収まり, 族の他のメンバーとも集合積可換。 -/
private theorem sylowSystem_prod_aux {P : ℕ → Subgroup G}
    (hsyl : ∀ p ∈ (Nat.card G).primeFactors, IsHallSubgroup {p} (P p))
    (hperm : ∀ p ∈ (Nat.card G).primeFactors, ∀ q ∈ (Nat.card G).primeFactors,
      (P p : Set G) * (P q : Set G) = (P q : Set G) * (P p : Set G))
    (t : Finset ℕ) (ht : t ⊆ (Nat.card G).primeFactors) :
    ∃ K : Subgroup G, (∀ q ∈ t, P q ≤ K) ∧
      (Nat.card K).primeFactors ⊆ t ∧
      ∀ r ∈ (Nat.card G).primeFactors,
        (K : Set G) * (P r : Set G) = (P r : Set G) * (K : Set G) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨⊥, by simp, by simp, fun r _ => ?_⟩
    rw [Subgroup.coe_bot]
    exact (one_mul _).trans (mul_one _).symm
  | @insert p t hpt ih =>
    have hp : p ∈ (Nat.card G).primeFactors := ht (Finset.mem_insert_self _ _)
    obtain ⟨K, hK_le, hK_pf, hK_comm⟩ := ih fun q hq => ht (Finset.mem_insert_of_mem hq)
    -- 位数の互いに素性 (`|K|` の素因子 ⊆ `t`, `|P p|` の素因子 ⊆ `{p}`, `p ∉ t`)
    have hcop : Nat.Coprime (Nat.card K) (Nat.card ↥(P p)) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hne
      have h1 : r ∈ t := hK_pf (Nat.mem_primeFactors.mpr
        ⟨hr_prime, hr_dvd.trans (Nat.gcd_dvd_left _ _), Nat.card_pos.ne'⟩)
      have h2 : r = p := by
        have := (hsyl p hp).1 r (Nat.mem_primeFactors.mpr
          ⟨hr_prime, hr_dvd.trans (Nat.gcd_dvd_right _ _), Nat.card_pos.ne'⟩)
        simpa using this
      exact hpt (h2 ▸ h1)
    have hbot : K ⊓ P p = ⊥ := by
      rw [← Subgroup.card_eq_one]
      exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd
        (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
    have hcomm_p : (K : Set G) * (P p : Set G) = (P p : Set G) * (K : Set G) := hK_comm p hp
    refine ⟨mulSubgroupOfComm K (P p) hcomm_p, fun q hq => ?_, ?_, fun r hr => ?_⟩
    · rcases Finset.mem_insert.mp hq with rfl | hq'
      · exact fun x hx => ⟨1, K.one_mem, x, hx, one_mul x⟩
      · exact fun x hx => ⟨x, hK_le q hq' hx, 1, (P p).one_mem, mul_one x⟩
    · -- `|K'| = |K| · |P p|` (積公式 + 交わり自明) から素因子を評価
      have hcard : Nat.card ↥(mulSubgroupOfComm K (P p) hcomm_p) =
          Nat.card K * Nat.card ↥(P p) := by
        have hprod := Ch01.card_mul_card_inf K (P p)
        rw [hbot, Subgroup.card_bot, mul_one] at hprod
        exact hprod
      intro r hr
      rw [hcard, Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hr
      rcases Finset.mem_union.mp hr with h | h
      · exact Finset.mem_insert_of_mem (hK_pf h)
      · have := (hsyl p hp).1 r h
        simp only [Set.mem_singleton_iff] at this
        exact this ▸ Finset.mem_insert_self p t
    · change ((K : Set G) * (P p : Set G)) * (P r : Set G) =
        (P r : Set G) * ((K : Set G) * (P p : Set G))
      rw [mul_assoc, hperm p hp r hr, ← mul_assoc, hK_comm r hr, mul_assoc]

/-- **Isaacs Problem 3C.3 (a)** (p. 90)。Sylow system を持つ群は, 任意の素数集合 `π` に
対して Hall `π`-部分群を持つ。 -/
theorem IsSylowSystem.exists_isHallSubgroup {P : ℕ → Subgroup G} (hP : IsSylowSystem P)
    (π : Set ℕ) : ∃ H : Subgroup G, IsHallSubgroup π H := by
  classical
  obtain ⟨K, hK_le, hK_pf, -⟩ := sylowSystem_prod_aux hP.1 hP.2
    ((Nat.card G).primeFactors.filter (· ∈ π)) (Finset.filter_subset _ _)
  refine ⟨K, fun r hr => ?_, fun r hr hrπ => ?_⟩
  · exact (Finset.mem_filter.mp (hK_pf hr)).2
  · -- `r ∈ π` が `K.index` を割るなら `P r ≤ K` から `K.index ∣ (P r).index`, Sylow 性に矛盾
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hr_pf : r ∈ (Nat.card G).primeFactors := Nat.mem_primeFactors.mpr
      ⟨hr_prime, (Nat.dvd_of_mem_primeFactors hr).trans (Subgroup.index_dvd_card K),
        Nat.card_pos.ne'⟩
    have hle : P r ≤ K :=
      hK_le r (Finset.mem_filter.mpr ⟨hr_pf, hrπ⟩)
    have hmem : r ∈ (P r).index.primeFactors := Nat.mem_primeFactors.mpr
      ⟨hr_prime, (Nat.dvd_of_mem_primeFactors hr).trans (Subgroup.index_dvd_of_le hle),
        Subgroup.index_ne_zero_of_finite⟩
    exact (hP.1 r hr_pf).2 r hmem rfl

/-- 3C.3 (b) の部品: `p`-補元たちの「`p` を除く全部の交わり」は Sylow `p`-部分群
(= Hall `{p}`-部分群)。3C.2 の Hall 性を `π = (pf ∖ {p})ᶜ` から `{p}` に狭める。 -/
private theorem isHallSingleton_inf_erase {Hc : ℕ → Subgroup G}
    (hHc : ∀ q, IsHallSubgroup ({q}ᶜ : Set ℕ) (Hc q)) {p : ℕ} :
    IsHallSubgroup {p} (((Nat.card G).primeFactors.erase p).inf Hc) := by
  have hHall := isHallSubgroup_finset_inf_of_pComplement
    ((Nat.card G).primeFactors.erase p) Hc (fun q _ => hHc q)
  constructor
  · intro r hr
    have h1 : r ∉ (Nat.card G).primeFactors.erase p := by
      have := hHall.1 r hr
      rwa [Set.mem_compl_iff, Finset.mem_coe] at this
    have h2 : r ∈ (Nat.card G).primeFactors := Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hr,
        (Nat.dvd_of_mem_primeFactors hr).trans (Subgroup.card_subgroup_dvd_card _),
        Nat.card_pos.ne'⟩
    have : r = p := by
      by_contra hne
      exact h1 (Finset.mem_erase.mpr ⟨hne, h2⟩)
    simp [this]
  · intro r hr
    have h1 : r ∈ (Nat.card G).primeFactors.erase p := by
      have := hHall.2 r hr
      rwa [Set.mem_compl_iff, not_not, Finset.mem_coe] at this
    simp only [Set.mem_singleton_iff]
    exact (Finset.mem_erase.mp h1).1

/-- 3C.3 (b) の核: `p ≠ q` のとき, `p`-側と `q`-側の「1 つを除く交わり」の集合積は
「2 つを除く交わり」に一致する。包含は自明で, 濃度は素因数分解の付値比較
(`p`-付値・`q`-付値は双方 `|G|` のそれ, 他は `0`) で一致する。 -/
private theorem inf_erase_mul_inf_erase {Hc : ℕ → Subgroup G}
    (hHc : ∀ q, IsHallSubgroup ({q}ᶜ : Set ℕ) (Hc q)) {p q : ℕ}
    (hp : p ∈ (Nat.card G).primeFactors) (hq : q ∈ (Nat.card G).primeFactors)
    (hpq : p ≠ q) :
    ((((Nat.card G).primeFactors.erase p).inf Hc : Subgroup G) : Set G) *
      ((((Nat.card G).primeFactors.erase q).inf Hc : Subgroup G) : Set G) =
      ((((((Nat.card G).primeFactors.erase p).erase q).inf Hc : Subgroup G)) : Set G) := by
  classical
  set pf := (Nat.card G).primeFactors with hpf
  set Pp := (pf.erase p).inf Hc with hPp
  set Pq := (pf.erase q).inf Hc with hPq
  set K := ((pf.erase p).erase q).inf Hc with hK
  -- 包含: `Pp ≤ K`, `Pq ≤ K`
  have hPp_le : Pp ≤ K :=
    Finset.le_inf fun r hr => Finset.inf_le (Finset.mem_of_mem_erase hr)
  have hPq_le : Pq ≤ K := Finset.le_inf fun r hr => by
    have h1 := Finset.mem_erase.mp hr
    have h2 := Finset.mem_erase.mp h1.2
    exact Finset.inf_le (Finset.mem_erase.mpr ⟨h1.1, h2.2⟩)
  -- Hall 性 (3C.2)
  have hallPp : IsHallSubgroup {p} Pp := isHallSingleton_inf_erase hHc
  have hallPq : IsHallSubgroup {q} Pq := isHallSingleton_inf_erase hHc
  have hallK : IsHallSubgroup ((↑((pf.erase p).erase q) : Set ℕ))ᶜ K :=
    isHallSubgroup_finset_inf_of_pComplement ((pf.erase p).erase q) Hc (fun r _ => hHc r)
  -- 濃度: `|K| = |Pp| · |Pq|` (付値比較)
  have hcard_eq : Nat.card ↥K = Nat.card ↥Pp * Nat.card ↥Pq := by
    refine Nat.eq_of_factorization_eq Nat.card_pos.ne'
      (Nat.mul_pos Nat.card_pos Nat.card_pos).ne' fun r => ?_
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply]
    by_cases hrp : r = p
    · subst hrp
      rw [hallK.factorization_card_of_mem (fun h => (Finset.mem_erase.mp
          (Finset.mem_of_mem_erase (Finset.mem_coe.mp h))).1 rfl),
        hallPp.factorization_card_of_mem rfl,
        hallPq.factorization_card_of_notMem (by simpa using hpq), add_zero]
    · by_cases hrq : r = q
      · subst hrq
        rw [hallK.factorization_card_of_mem (fun h => (Finset.mem_erase.mp
            (Finset.mem_coe.mp h)).1 rfl),
          hallPq.factorization_card_of_mem rfl,
          hallPp.factorization_card_of_notMem (by simpa using (Ne.symm hpq)), zero_add]
      · -- `r ∉ {p, q}`: 3 者とも付値は `pf` 内なら `0`, `pf` 外なら `|G|` の付値 `= 0`
        by_cases hrpf : r ∈ pf
        · rw [hallK.factorization_card_of_notMem (fun hc => hc (Finset.mem_coe.mpr
              (Finset.mem_erase.mpr ⟨hrq, Finset.mem_erase.mpr ⟨hrp, hrpf⟩⟩))),
            hallPp.factorization_card_of_notMem (by simpa using hrp),
            hallPq.factorization_card_of_notMem (by simpa using hrq)]
        · have hG0 : (Nat.card G).factorization r = 0 := by
            rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
            exact hrpf
          rw [hallK.factorization_card_of_mem (fun h => hrpf (Finset.mem_of_mem_erase
              (Finset.mem_of_mem_erase (Finset.mem_coe.mp h)))),
            hallPp.factorization_card_of_notMem (by simpa using hrp),
            hallPq.factorization_card_of_notMem (by simpa using hrq), hG0]
  -- 交わり自明 (`p`-群と `q`-群, `p ≠ q`)
  have hbot : Pp ⊓ Pq = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have hcop : Nat.Coprime (Nat.card ↥Pp) (Nat.card ↥Pq) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hne
      have h1 := hallPp.1 r (Nat.mem_primeFactors.mpr
        ⟨hr_prime, hr_dvd.trans (Nat.gcd_dvd_left _ _), Nat.card_pos.ne'⟩)
      have h2 := hallPq.1 r (Nat.mem_primeFactors.mpr
        ⟨hr_prime, hr_dvd.trans (Nat.gcd_dvd_right _ _), Nat.card_pos.ne'⟩)
      simp only [Set.mem_singleton_iff] at h1 h2
      exact hpq (h1 ▸ h2)
    exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  -- 積公式から `|Pp · Pq| = |Pp| · |Pq|`
  have hprod := Ch01.card_mul_card_inf Pp Pq
  rw [hbot] at hprod
  simp only [Subgroup.card_bot, mul_one] at hprod
  -- 包含 + 濃度一致で集合として等しい
  have hsub : (Pp : Set G) * (Pq : Set G) ⊆ (K : Set G) := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact K.mul_mem (hPp_le ha) (hPq_le hb)
  refine Set.eq_of_subset_of_ncard_le hsub (le_of_eq ?_) (Set.toFinite _)
  calc ((K : Set G)).ncard = Nat.card ↥K := (Nat.card_coe_set_eq _).symm
    _ = Nat.card ↥Pp * Nat.card ↥Pq := hcard_eq
    _ = Nat.card ↥((Pp : Set G) * (Pq : Set G)) := hprod.symm
    _ = ((Pp : Set G) * (Pq : Set G)).ncard := Nat.card_coe_set_eq _

/-- **Isaacs Problem 3C.3 (b)** (p. 90)。可解群は Sylow system を持つ。

書籍 Hint のとおり: Hall E-定理 (`hall_E_exists`) で各素数 `q` の `q`-補元 `Hc q` を取り,
`P p := ⋂_{q ∈ pf(|G|), q ≠ p} Hc q` と置くと, 3C.2 からこれが Sylow `p`-部分群で,
`P p · P q = ⋂_{r ≠ p,q} Hc r = P q · P p` (`inf_erase_mul_inf_erase`) が可換性を与える。 -/
theorem exists_isSylowSystem [IsSolvable G] :
    ∃ P : ℕ → Subgroup G, IsSylowSystem P := by
  classical
  choose Hc hHc using fun q : ℕ => hall_E_exists (G := G) ({q}ᶜ : Set ℕ)
  refine ⟨fun p => ((Nat.card G).primeFactors.erase p).inf Hc,
    fun p _ => isHallSingleton_inf_erase hHc, fun p hp q hq => ?_⟩
  by_cases hpq : p = q
  · subst hpq; rfl
  · rw [inf_erase_mul_inf_erase hHc hp hq hpq,
      inf_erase_mul_inf_erase hHc hq hp (Ne.symm hpq), Finset.erase_right_comm]

end -- Problem 3C.3

end OddOrder.Isaacs.Ch03
