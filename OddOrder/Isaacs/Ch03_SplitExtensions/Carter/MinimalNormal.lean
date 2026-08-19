/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Carter.QuotientTransfer
import OddOrder.Isaacs.Ch03_SplitExtensions.HallNilpotent
import OddOrder.Isaacs.Ch01_Sylow.Problems

/-!
# Isaacs Problem 3C.7(b) — 極小正規部分群まわりの部品

3C.7(b) (Carter 部分群の共役性) の `|G|`-強帰納は、極小正規部分群 `N` を取って
`G ⧸ N` に降りる。帰納が閉じない唯一の場合が

> `C ⊔ N = D ⊔ N = ⊤` (`C`, `D` は Carter 部分群)

で、ここは帰納法の仮説を使わずに直接処理する。本ファイルはその直接処理に要る部品を置く
(帰納の骨格は `Carter.Conjugacy`)。

## 場合分けの構造

* `N ≤ C` なら `C = C ⊔ N = ⊤` ゆえ `G` 自身が冪零 (`isNilpotent_of_isCarterSubgroup_eq_top`)。
  冪零群の Carter 部分群は `⊤` だけなので `D = ⊤ = C`。
* そうでなければ `C ⊓ N ⊴ G` (`normal_inf_of_comm_of_sup_eq_top`) と `N` の極小性から
  `C ⊓ N = ⊥`, つまり `C` は `N` の補元。`D` も同様。
  このとき `G ⧸ N ≅ C` は冪零なので、`N` の属する素数 `p` について
  **`G` の Sylow `p`-部分群 `P` は正規** (`sylow_normal_of_isPGroup_of_isNilpotent_quotient`)。

## Main results

- `isNilpotent_of_isCarterSubgroup_eq_top` — Carter 部分群が `⊤` なら群は冪零。
- `normal_inf_of_comm_of_sup_eq_top` — 可換正規 `N` と `C ⊔ N = ⊤` から `C ⊓ N ⊴ G`。
- `sylow_normal_of_isPGroup_of_isNilpotent_quotient` — `p`-群 `N` で割った商が冪零なら
  Sylow `p` は正規。
- `exists_mem_normalizer_notMem_of_isNilpotent` — 冪零部分群 `X` の真部分群 `Y` に対し,
  `Y` を正規化する `X \ Y` の元が取れる (正規化条件の部分群版)。
- `sup_inf_eq_and_commute_of_isNilpotent` — 冪零 `C` の `π`/`π'` 分解。
- `inf_eq_centralizer_inf_of_isCarterSubgroup` — Carter 部分群の `p`-部分は `C_G(Q) ⊓ P`。
- `eq_of_isCarterSubgroup_of_hall_eq` — Hall `π'` 部分が一致する 2 つの Carter は等しい。
- `exists_conj_of_isCarterSubgroup_of_isComplement` — 補元の場合の共役性。
- `exists_conj_of_isCarterSubgroup_of_isMinimalNormal` — **step 4 の総括**。
-/

namespace OddOrder.Isaacs.Ch03

open _root_.OddOrder.Isaacs.Ch03.Subgroup Pointwise

section /- 3C.7(b): 極小正規部分群の場合 -/

variable {G : Type*} [Group G]

/-- Carter 部分群が `⊤` なら `G` 自身が冪零。 -/
theorem isNilpotent_of_isCarterSubgroup_eq_top {C : Subgroup G} (hC : IsCarterSubgroup C)
    (h : C = ⊤) : Group.IsNilpotent G := by
  subst h
  have := hC.1
  exact Group.nilpotent_of_mulEquiv Subgroup.topEquiv

/-- `N ⊴ G` が可換で `C ⊔ N = ⊤` なら `C ⊓ N ⊴ G`。

`C` は `N_G(C)` と `N_G(N) = ⊤` の両方に入るので `N_G(C ⊓ N)` に入り
(`Subgroup.inf_normalizer_le_normalizer_inf`), `N` の元は `N` の元を可換性で固定するので
やはり `C ⊓ N` を正規化する。`C ⊔ N = ⊤` より `N_G(C ⊓ N) = ⊤`。 -/
theorem normal_inf_of_comm_of_sup_eq_top {C N : Subgroup G} [N.Normal]
    (habel : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hCN : C ⊔ N = ⊤) :
    (C ⊓ N : Subgroup G).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hCN]
  refine sup_le (fun c hc => ?_) (fun n hn => ?_)
  · exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨C.le_normalizer hc, by rw [Subgroup.normalizer_eq_top (H := N)]; trivial⟩
  · -- `n ∈ N` は `N` の元を可換性で固定するので `C ⊓ N` を正規化する。
    have key : ∀ x ∈ N, n * x * n⁻¹ = x := by
      intro x hx
      rw [habel n hn x hx]
      group
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · rw [key h hh.2]
      exact hh
    · have hhN : h ∈ N := by
        have hconj := ‹N.Normal›.conj_mem _ hh.2 n⁻¹
        have hsimp : n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ = h := by group
        rwa [hsimp] at hconj
      rwa [key h hhN] at hh

/-- **正規化条件の部分群版**: `X` が冪零な部分群で `Y < X` なら, `Y` を正規化する
`X \ Y` の元が存在する。

`↥X` の中で正規化条件 (`Group.normalizerCondition_of_isNilpotent`) を使い,
`Subgroup.subgroupOf_normalizer_eq` で `G` の正規化子に翻訳する。 -/
theorem exists_mem_normalizer_notMem_of_isNilpotent {X Y : Subgroup G}
    (hX : Group.IsNilpotent ↥X) (hYX : Y ≤ X) (hne : Y ≠ X) :
    ∃ y ∈ X, y ∉ Y ∧ y ∈ Subgroup.normalizer (Y : Set G) := by
  have := hX
  have hlt : Y.subgroupOf X < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hne (le_antisymm hYX htop)
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (G := ↥X) _ hlt)
  rw [← Subgroup.subgroupOf_normalizer_eq hYX, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  exact ⟨(t : G), t.2, ht_not, ht_norm⟩

/-- **`p`-群で割った商が冪零なら Sylow `p`-部分群は正規**。

`G ⧸ N` の Sylow `p`-部分群 `P̄` は冪零性から正規。`mk' N` の核 `N` は `p`-群なので
`P̄` の引き戻しは `G` の Sylow `p`-部分群 (`Sylow.comapOfKerIsPGroup`) であり,
正規部分群の引き戻しなので正規。正規な Sylow は一意 (`Sylow.unique_of_normal`) なので
任意の Sylow `p`-部分群がそれに一致する。 -/
theorem sylow_normal_of_isPGroup_of_isNilpotent_quotient [Finite G] {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hN : IsPGroup p ↥N)
    (hnil : Group.IsNilpotent (G ⧸ N)) (P : Sylow p G) : (P : Subgroup G).Normal := by
  have := hnil
  obtain ⟨Pbar⟩ : Nonempty (Sylow p (G ⧸ N)) := inferInstance
  have hPbarNormal : (Pbar : Subgroup (G ⧸ N)).Normal :=
    Sylow.normal_of_normalizerCondition Group.normalizerCondition_of_isNilpotent Pbar
  have hker : IsPGroup p ↥(QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    exact hN
  have hrange : (Pbar : Subgroup (G ⧸ N)) ≤ (QuotientGroup.mk' N).range := fun x _ =>
    MonoidHom.mem_range.mpr (QuotientGroup.mk'_surjective N x)
  have hP'Normal : ((Pbar : Subgroup (G ⧸ N)).comap (QuotientGroup.mk' N)).Normal :=
    hPbarNormal.comap _
  have : Unique (Sylow p G) :=
    Sylow.unique_of_normal (Pbar.comapOfKerIsPGroup (QuotientGroup.mk' N) hker hrange) hP'Normal
  have hPe : P = Pbar.comapOfKerIsPGroup (QuotientGroup.mk' N) hker hrange :=
    Subsingleton.elim _ _
  rw [hPe]
  exact hP'Normal

/-- **冪零部分群の `π`/`π'` 分解**: `C` が冪零で `P ⊴ G` が `π`-Hall, `Q ≤ C` が `π'`-Hall なら
`C = (C ⊓ P) ⊔ Q` かつ `C ⊓ P` と `Q` は元ごとに可換。

`↥C` の中で `P.subgroupOf C` は `π`-Hall (`isHallSubgroup_subgroupOf_of_normal_left`),
`Q.subgroupOf C` は `π'`-Hall (`isHallSubgroup_subgroupOf_of_le`) で、両者は
`sup_eq_top_of_isHallSubgroup_compl` により `↥C` を生成し、`C` の冪零性から
`commute_of_isHallSubgroup_of_isHallSubgroup_compl` で可換。 -/
theorem sup_inf_eq_and_commute_of_isNilpotent [Finite G] {π : Set ℕ} {C P Q : Subgroup G}
    [P.Normal] (hPhall : IsHallSubgroup π P) (hCnil : Group.IsNilpotent ↥C)
    (hQ : IsHallSubgroup πᶜ Q) (hQC : Q ≤ C) :
    (C ⊓ P) ⊔ Q = C ∧ ∀ x ∈ C ⊓ P, ∀ y ∈ Q, Commute x y := by
  have := hCnil
  have hS : IsHallSubgroup π (P.subgroupOf C) := isHallSubgroup_subgroupOf_of_normal_left hPhall
  have hL : IsHallSubgroup πᶜ (Q.subgroupOf C) := isHallSubgroup_subgroupOf_of_le hQ hQC
  refine ⟨?_, ?_⟩
  · have htop : (P.subgroupOf C) ⊔ (Q.subgroupOf C) = ⊤ :=
      sup_eq_top_of_isHallSubgroup_compl hS hL
    have hmap := congrArg (Subgroup.map C.subtype) htop
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hQC, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      inf_comm P C] at hmap
    exact hmap
  · intro x hx y hy
    have hcomm := commute_of_isHallSubgroup_of_isHallSubgroup_compl (G := ↥C) hS hL
      ⟨x, hx.1⟩ (Subgroup.mem_subgroupOf.mpr hx.2) ⟨y, hQC hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
    have hval : (x : G) * y = y * x := by
      have := congrArg (Subtype.val : ↥C → G) hcomm
      simpa using this
    exact hval

/-- **Carter 部分群の `p`-部分は `π'`-Hall 部分の中心化群で決まる**:
`C ⊓ P = C_G(Q) ⊓ P`。

`⊆` は `C ⊓ P` と `Q` が可換なこと。`⊇` は背理法: `X := C_G(Q) ⊓ P` は `p`-群なので
`C ⊓ P < X` なら正規化条件 (`exists_mem_normalizer_notMem_of_isNilpotent`) で
`C ⊓ P` を正規化する `y ∈ X \ (C ⊓ P)` が取れる。`y` は `Q` を中心化するので `Q` も正規化し、
したがって `C = (C ⊓ P) ⊔ Q` を正規化する。`C` は自己正規化なので `y ∈ C`, また `y ∈ P` ゆえ
`y ∈ C ⊓ P` で矛盾。 -/
theorem inf_eq_centralizer_inf_of_isCarterSubgroup [Finite G] {p : ℕ} [Fact p.Prime]
    {C P Q : Subgroup G} (hC : IsCarterSubgroup C) (hPp : IsPGroup p ↥P)
    (hCQ : (C ⊓ P) ⊔ Q = C) (hcomm : ∀ x ∈ C ⊓ P, ∀ y ∈ Q, Commute x y) :
    C ⊓ P = Subgroup.centralizer (Q : Set G) ⊓ P := by
  set X : Subgroup G := Subgroup.centralizer (Q : Set G) ⊓ P with hXdef
  have hXP : X ≤ P := inf_le_right
  have hsub : C ⊓ P ≤ X := fun x hx =>
    ⟨Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm x hx y hy).symm, hx.2⟩
  by_contra hne
  obtain ⟨y, hyX, hyNot, hyNorm⟩ := exists_mem_normalizer_notMem_of_isNilpotent
    (X := X) (Y := C ⊓ P) (hPp.to_le hXP).isNilpotent hsub hne
  have hyQnorm : y ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.centralizer_le_normalizer _ hyX.1
  have hyCnorm : y ∈ Subgroup.normalizer (C : Set G) := by
    rw [← hCQ]
    exact Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hyNorm, hyQnorm⟩
  rw [hC.normalizer_eq] at hyCnorm
  exact hyNot ⟨hyCnorm, hXP hyX⟩

/-- **3C.7(b) step 4 の核**: 2 つの Carter 部分群が同じ `π'`-Hall 部分 `Q` を含み、
どちらも `(· ⊓ P) ⊔ Q` に分解するなら等しい。

両者の `p`-部分がともに `C_G(Q) ⊓ P` に等しい
(`inf_eq_centralizer_inf_of_isCarterSubgroup`) ので、分解式から直ちに従う。 -/
theorem eq_of_isCarterSubgroup_of_hall_eq [Finite G] {p : ℕ} [Fact p.Prime]
    {C D P Q : Subgroup G} (hPp : IsPGroup p ↥P)
    (hC : IsCarterSubgroup C) (hD : IsCarterSubgroup D)
    (hCQ : (C ⊓ P) ⊔ Q = C) (hDQ : (D ⊓ P) ⊔ Q = D)
    (hcommC : ∀ x ∈ C ⊓ P, ∀ y ∈ Q, Commute x y)
    (hcommD : ∀ x ∈ D ⊓ P, ∀ y ∈ Q, Commute x y) : C = D := by
  rw [← hCQ, ← hDQ, inf_eq_centralizer_inf_of_isCarterSubgroup hC hPp hCQ hcommC,
    inf_eq_centralizer_inf_of_isCarterSubgroup hD hPp hDQ hcommD]

/-- **3C.7(b) step 4, `N` が補われる場合**: `N ⊴ G` が `p`-群で `C`, `D` がともに `N` の
補元となる Carter 部分群なら, `C` と `D` は共役。

1. `C ⊔ N = ⊤` と `C` の冪零性から `G ⧸ N` は冪零, よって `G` の Sylow `p`-部分群 `P` は正規。
2. `C ⊓ N = ⊥` から `[G:C] = |N|` は `p`-冪なので, `C` の Hall `p'`-部分群 `Q_C` は
   `G` の Hall `p'`-部分群 (`IsHallSubgroup.map_subtype_of_index_no_pi`)。`D` も同様。
3. 可解群の Hall 共役性 (`hall_C`) で `Q_C^x = Q_D` にでき, `C^x` と `D` は同じ
   `Q_D` を Hall `p'` 部分に持つ。
4. `eq_of_isCarterSubgroup_of_hall_eq` で `C^x = D`。 -/
theorem exists_conj_of_isCarterSubgroup_of_isComplement [Finite G] [Group.IsSolvable G] {p : ℕ}
    [Fact p.Prime] {C D N : Subgroup G} [N.Normal] (hC : IsCarterSubgroup C)
    (hD : IsCarterSubgroup D) (hNp : IsPGroup p ↥N)
    (hCN : C ⊔ N = ⊤) (hCiN : C ⊓ N = ⊥) (hDN : D ⊔ N = ⊤) (hDiN : D ⊓ N = ⊥) :
    ∃ g : G, C.map (MulAut.conj g).toMonoidHom = D := by
  -- (1) `N` の補元の指数は `|N|`, すなわち `p`-冪。
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hNp
  have hindex : ∀ {K : Subgroup G}, K ⊔ N = ⊤ → K ⊓ N = ⊥ →
      ∀ q ∈ K.index.primeFactors, q = p := by
    intro K hKN hKiN q hq
    have hprod : Nat.card G * 1 = Nat.card ↥K * Nat.card ↥N := by
      have h := Subgroup.card_HK_mul_card_inf_eq_card_mul_card K N
      rw [← Subgroup.mul_normal K N, hKN, hKiN] at h
      simpa using h
    have hidx : K.index = Nat.card ↥N := by
      refine Nat.eq_of_mul_eq_mul_left (n := Nat.card ↥K) Nat.card_pos ?_
      rw [Subgroup.card_mul_index K, ← hprod, mul_one]
    rw [hidx, hn, Nat.mem_primeFactors] at hq
    exact (Nat.prime_dvd_prime_iff_eq hq.1 Fact.out).mp (hq.1.dvd_of_dvd_pow hq.2.1)
  -- (2) `G ⧸ N` は冪零。
  have hquot : Group.IsNilpotent (G ⧸ N) := by
    have h1 : Group.IsNilpotent ↥((C ⊔ N).map (QuotientGroup.mk' N)) := by
      rw [sup_map_mk'_eq_map_mk']
      exact isNilpotent_map_of_isNilpotent hC.1 _
    rw [hCN, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
    have := h1
    exact Group.nilpotent_of_mulEquiv Subgroup.topEquiv
  -- (3) `G` の Sylow `p`-部分群 `P` は正規。
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hPnormal : (P : Subgroup G).Normal :=
    sylow_normal_of_isPGroup_of_isNilpotent_quotient hNp hquot P
  have hPhall : IsHallSubgroup ({p} : Set ℕ) (P : Subgroup G) :=
    Ch01.sylow_isHallSubgroup_singleton P
  -- (4) `N` の補元の中に `G` の Hall `p'`-部分群がある。
  have hHallOf : ∀ {K : Subgroup G}, (∀ q ∈ K.index.primeFactors, q = p) →
      ∃ Q : Subgroup G, Q ≤ K ∧ IsHallSubgroup (({p} : Set ℕ)ᶜ) Q := by
    intro K hKidx
    obtain ⟨L, hL⟩ := hall_E_exists (G := ↥K) (({p} : Set ℕ)ᶜ)
    exact ⟨L.map K.subtype, Subgroup.map_subtype_le L,
      IsHallSubgroup.map_subtype_of_index_no_pi hL fun q hq hqc => hqc (hKidx q hq)⟩
  obtain ⟨QC, hQC_le, hQC_hall⟩ := hHallOf (hindex hCN hCiN)
  obtain ⟨QD, hQD_le, hQD_hall⟩ := hHallOf (hindex hDN hDiN)
  -- (5) Hall 共役性で `Q_C^x = Q_D`。
  obtain ⟨x, hx⟩ := hall_C hQC_hall hQD_hall
  refine ⟨x, ?_⟩
  -- (6) `C^x` は Carter で `Q_D` を含み, 指数は `C` と同じ。
  have hC' : IsCarterSubgroup (C.map (MulAut.conj x).toMonoidHom) := hC.map_conj x
  have hQD_le_C' : QD ≤ C.map (MulAut.conj x).toMonoidHom := by
    rw [← hx]
    exact Subgroup.map_mono hQC_le
  -- (7) 両者を `(· ⊓ P) ⊔ Q_D` に分解して比較。
  obtain ⟨hCQ, hcommC⟩ :=
    sup_inf_eq_and_commute_of_isNilpotent hPhall hC'.1 hQD_hall hQD_le_C'
  obtain ⟨hDQ, hcommD⟩ :=
    sup_inf_eq_and_commute_of_isNilpotent hPhall hD.1 hQD_hall hQD_le
  exact eq_of_isCarterSubgroup_of_hall_eq P.isPGroup' hC' hD hCQ hDQ hcommC hcommD

/-- **3C.7(b) step 4**: `N` が極小正規で `C ⊔ N = D ⊔ N = ⊤` なら `C` と `D` は共役。

`N` は可換 (`minimal_normal_isAbelian_of_isSolvable`) なので `C ⊓ N ⊴ G`, 極小性から
`C ⊓ N` は `⊥` か `N`。`N ≤ C` なら `C = ⊤` で `G` 自身が冪零, ゆえに `D = ⊤ = C`
(`IsCarterSubgroup.eq_top_of_isNilpotent`)。`D` 側も同様。
残るのは `C`, `D` がともに `N` の補元の場合で,
`exists_conj_of_isCarterSubgroup_of_isComplement` が処理する。 -/
theorem exists_conj_of_isCarterSubgroup_of_isMinimalNormal [Finite G] [Group.IsSolvable G]
    {C D N : Subgroup G} (hC : IsCarterSubgroup C) (hD : IsCarterSubgroup D)
    (hN : Ch02.IsMinimalNormal N) (hCN : C ⊔ N = ⊤) (hDN : D ⊔ N = ⊤) :
    ∃ g : G, C.map (MulAut.conj g).toMonoidHom = D := by
  have := hN.1
  have habel := minimal_normal_isAbelian_of_isSolvable hN
  -- 極小性から `K ⊓ N` は `⊥` か `N`。
  have hdicho : ∀ {K : Subgroup G}, K ⊔ N = ⊤ → K ⊓ N = ⊥ ∨ N ≤ K := by
    intro K hKN
    have := normal_inf_of_comm_of_sup_eq_top (C := K) habel hKN
    rcases hN.2.2 (K ⊓ N) inferInstance inf_le_right with h | h
    · exact Or.inl h
    · exact Or.inr (h ▸ (inf_le_left : K ⊓ N ≤ K))
  rcases hdicho hCN with hCiN | hNC
  · rcases hdicho hDN with hDiN | hND
    · -- `C`, `D` はともに `N` の補元。
      obtain ⟨p, hp, hNel⟩ := minimal_normal_isElementaryAbelian_of_isSolvable hN
      have : Fact p.Prime := ⟨hp⟩
      have hNp : IsPGroup p ↥N := fun g => ⟨1, by simpa using hNel.2 g⟩
      exact exists_conj_of_isCarterSubgroup_of_isComplement hC hD hNp hCN hCiN hDN hDiN
    · -- `N ≤ D` ⟹ `D = ⊤` ⟹ `G` 冪零 ⟹ `C = ⊤ = D`。
      have hDtop : D = ⊤ := by rw [← hDN, sup_eq_left.mpr hND]
      have := isNilpotent_of_isCarterSubgroup_eq_top hD hDtop
      exact ⟨1, by rw [map_conj_one, hC.eq_top_of_isNilpotent, hDtop]⟩
  · -- `N ≤ C` ⟹ `C = ⊤` ⟹ `G` 冪零 ⟹ `D = ⊤ = C`。
    have hCtop : C = ⊤ := by rw [← hCN, sup_eq_left.mpr hNC]
    have := isNilpotent_of_isCarterSubgroup_eq_top hC hCtop
    exact ⟨1, by rw [map_conj_one, hCtop, hD.eq_top_of_isNilpotent]⟩

end -- 3C.7(b): 極小正規部分群の場合

end OddOrder.Isaacs.Ch03
