/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import OddOrder.GroupTheory.ElementaryAbelian
import OddOrder.Isaacs.Ch02_Subnormality.Main

open scoped commutatorElement Pointwise

/-!
# Ch.4 → Ch.2 forward dependencies

このファイルは **Isaacs FGT Ch.2 §2D Thm 2.20 (Lucchini)** を完全形式化する場所.
論理的には Ch.2 の定理だが, **K = ⊥ case の証明が Ch.4 §4A-§4B (lower central series
加法性) に依存**するため, owner chapter (Ch.4) ディレクトリに置く.

## このファイルの構造

1. **補助補題群** (旧 Main.lean §4B から移動): `iterCommutator` infrastructure +
   `le_centralizer_of_isMinimalNormal` (Z(F(G)) absorbs G-minimal normal) +
   minimal normal nilpotent ⇒ elem abelian の variants + Lucchini K=⊥ Step 1 集約
   (`exists_isMinimalNormal_le_fitting_le_centralizer_fitting`).
   循環 import 回避のため Main.lean ではなくここに置く
   (Main.lean は Ch.3 → ForwardFromCh02 を経由するため transitive アクセス可).

2. `lucchini_K_bot_aux` — Lucchini の K = ⊥ case (private theorem).

3. `lucchini_aux` — `|G|`-induction wrapper (private).
   * K = ⊥ branch: `lucchini_K_bot_aux` を呼ぶ.
   * K > ⊥ branch: Ch.2 の `lucchini_K_pos_reduction` (subgroup correspondence のみ)
     + IH on G/K.

4. `lucchini_index_normalCore_lt_index` — **Isaacs Thm 2.20 本体** (theorem).
   `lucchini_aux (Nat.card G) le_rfl ...` で呼ぶ.

## namespace 設計

書籍上は Ch.2 の定理だが, Lean 上は物理的に Ch.4 dir にいるため
`OddOrder.Isaacs.Ch04` namespace を使う. docstring に book 番号 (Thm 2.20) を明示.

## 関連ノート

- [`notes/meta/forward_dep_policy.md`](../../../notes/meta/forward_dep_policy.md):
  forward dep の所在規則.
- [`notes/isaacs/ch02_subnormality.md`](../../../notes/isaacs/ch02_subnormality.md):
  Ch.2 内 `lucchini_K_pos_reduction` (構造補題) との分担.
- [`notes/isaacs/ch04_commutators.md`](../../../notes/isaacs/ch04_commutators.md):
  §4A-§4B 補助補題の inventory.
-/

namespace OddOrder.Isaacs.Ch04

variable {G : Type*} [Group G]

/-! ## 補助補題群: iterCommutator + minimal normal nilpotent variants

旧 `OddOrder/Isaacs/Ch04_Commutators/Main.lean` §4B 後半 (L1699-2024) から移動.
Lucchini K=⊥ 証明で使用する補題群. 循環 import 回避のため Main.lean ではなく本ファイルに置く. -/

/-! ### iterated right commutator infrastructure

Lucchini K = ⊥ case の「Z(F(G)) absorbs G-minimal normal」補題等で使用する.
`E, F ≤ G` に対し `iter E F n = ⁅...⁅E, F⁆, F⁆..., F⁆` (`n` 回右から `F`). -/

/-- **Iterated right commutator**: `iterCommutator E F n = ⁅...⁅E, F⁆, F⁆..., F⁆`. -/
def iterCommutator (E F : Subgroup G) : ℕ → Subgroup G
  | 0 => E
  | n + 1 => ⁅iterCommutator E F n, F⁆

@[simp]
theorem iterCommutator_zero (E F : Subgroup G) :
    iterCommutator E F 0 = E := rfl

@[simp]
theorem iterCommutator_succ (E F : Subgroup G) (n : ℕ) :
    iterCommutator E F (n + 1) = ⁅iterCommutator E F n, F⁆ := rfl

/-- **iterCommutator は F の lcs 経由で押し込められる**: `E ≤ F` ⇒
`iterCommutator E F n ≤ ((⊤ : Subgroup ↥F).lowerCentralSeries n).map F.subtype`.

特に `F` が冪零 (Group.IsNilpotent ↥F) なら, 十分大きな `n` で `lcs ↥F n = ⊥`,
よって `iterCommutator E F n = ⊥`. これが Lucchini K = ⊥ case の核心 (Z(F(G))
absorbs G-minimal). -/
theorem iterCommutator_le_lowerCentralSeries_map
    {E F : Subgroup G} (hE : E ≤ F) (n : ℕ) :
    iterCommutator E F n ≤ ((⊤ : Subgroup ↥F).lowerCentralSeries n).map F.subtype := by
  induction n with
  | zero =>
    simp only [iterCommutator_zero, Subgroup.lowerCentralSeries_zero]
    rw [← MonoidHom.range_eq_map, F.range_subtype]
    exact hE
  | succ n ih =>
    rw [iterCommutator_succ]
    have hRange : (⊤ : Subgroup ↥F).map F.subtype = F := by
      rw [← MonoidHom.range_eq_map]; exact F.range_subtype
    have hMapLcs : ((⊤ : Subgroup ↥F).lowerCentralSeries (n + 1)).map F.subtype =
        ⁅(((⊤ : Subgroup ↥F).lowerCentralSeries n).map F.subtype), F⁆ := by
      change ⁅(⊤ : Subgroup ↥F).lowerCentralSeries n, (⊤ : Subgroup ↥F)⁆.map F.subtype = _
      rw [Subgroup.map_commutator, hRange]
    rw [hMapLcs]
    exact Subgroup.commutator_mono ih le_rfl

/-- **iterCommutator は ambient G の lcs に押し込められる**: 任意 `E, F ⊆ G` で
`iterCommutator E F n ≤ (⊤ : Subgroup G).lowerCentralSeries n`. `E ≤ F` 不要
(E, F は ⊤ ≤ G で挟まれる).

`E ≤ ⊤` と `F ≤ ⊤` 経由で `iterCommutator E F n ≤ iterCommutator ⊤ ⊤ n = lcs G n`. -/
theorem iterCommutator_le_lowerCentralSeries (E F : Subgroup G) (n : ℕ) :
    iterCommutator E F n ≤ (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero =>
    simp only [iterCommutator_zero, Subgroup.lowerCentralSeries_zero]
    exact le_top
  | succ n ih =>
    rw [iterCommutator_succ, Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mono ih le_top

/-- **ambient G 冪零 ⇒ iterCommutator は最終的に ⊥** (任意 E, F).
`E ≤ F` 制約のない一般版 (上の `iterCommutator_eq_bot_of_isNilpotent` は `E ≤ F` 必要). -/
theorem iterCommutator_eq_bot_of_isNilpotent_ambient
    [Group.IsNilpotent G] (E F : Subgroup G) :
    ∃ n, iterCommutator E F n = ⊥ := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp ‹_›
  refine ⟨n, le_antisymm ?_ bot_le⟩
  exact (iterCommutator_le_lowerCentralSeries E F n).trans (le_of_eq hn)

/-- **冪零 ambient G + nontrivial normal E ⇒ ⁅E, F⁆ < E**: 厳密降下.

`⁅E, F⁆ = E` なら iterCommutator E F は定常 (induction で各 n で = E). しかし
`iterCommutator_eq_bot_of_isNilpotent_ambient` で ∃ n, iter = ⊥. ⇒ E = ⊥ 矛盾. -/
theorem commutator_lt_self_of_isNilpotent_ambient
    [Group.IsNilpotent G] {E F : Subgroup G} [E.Normal] (hE : E ≠ ⊥) :
    ⁅E, F⁆ < E := by
  refine lt_of_le_of_ne (Subgroup.commutator_le_left E F) ?_
  intro heq
  have hconst : ∀ n, iterCommutator E F n = E := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iterCommutator_succ, ih]
      exact heq
  obtain ⟨n, hn⟩ := iterCommutator_eq_bot_of_isNilpotent_ambient E F
  rw [hconst n] at hn
  exact hE hn

/-- **iterCommutator は normal を保つ**. `E, F ⊴ G` ⇒ `iter E F n ⊴ G`. -/
theorem iterCommutator_normal {E F : Subgroup G} [E.Normal] [F.Normal] (n : ℕ) :
    (iterCommutator E F n).Normal := by
  induction n with
  | zero => exact ‹E.Normal›
  | succ n ih =>
    haveI := ih
    rw [iterCommutator_succ]
    infer_instance

/-- **iterCommutator は antitone (decreasing)**. `E, F ⊴ G` ⇒
`iter E F (n+1) ≤ iter E F n`.

(直観: `iter E F n ⊴ G ⊇ F` で `F` は `iter E F n` を normalize するので
`⁅iter, F⁆ ≤ iter`.) -/
theorem iterCommutator_succ_le_self {E F : Subgroup G} [E.Normal] [F.Normal] (n : ℕ) :
    iterCommutator E F (n + 1) ≤ iterCommutator E F n := by
  haveI : (iterCommutator E F n).Normal := iterCommutator_normal n
  rw [iterCommutator_succ]
  exact Subgroup.commutator_le_left (iterCommutator E F n) F

/-- **F 冪零 ⇒ iterCommutator は最終的に ⊥**: `E ≤ F` + `F` (as group `↥F`) が冪零
⇒ ∃ n, `iter E F n = ⊥`. -/
theorem iterCommutator_eq_bot_of_isNilpotent
    {E F : Subgroup G} (hE : E ≤ F) [hF : Group.IsNilpotent ↥F] :
    ∃ n, iterCommutator E F n = ⊥ := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hF
  refine ⟨n, le_antisymm ?_ bot_le⟩
  calc iterCommutator E F n
      ≤ ((⊤ : Subgroup ↥F).lowerCentralSeries n).map F.subtype :=
        iterCommutator_le_lowerCentralSeries_map hE n
    _ ≤ ⊥ := by rw [hn]; exact (Subgroup.map_bot F.subtype).le

/-- **iterCommutator は E 内に留まる**: `E, F ⊴ G ⇒ iter E F n ≤ E`. -/
theorem iterCommutator_le_self {E F : Subgroup G} [E.Normal] [F.Normal] (n : ℕ) :
    iterCommutator E F n ≤ E := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact (iterCommutator_succ_le_self n).trans ih

/-- **Z(F(G)) absorbs G-minimal normal in F(G)** ⭐ (Lucchini K=⊥ aux 解消の核補題):
`E ⊴ G` minimal normal, `E ≤ F`, `F ⊴ G` 冪零 ⇒ `E ≤ centralizer F`.

**証明** (Isaacs §4A lcs 経路):
1. `iterCommutator E F` の降下列を考える. 各項は G-normal (`iterCommutator_normal`),
   decreasing (`iterCommutator_succ_le_self`), `E` 内 (`iterCommutator_le_self`).
2. `F` 冪零 で `iter n = ⊥` for some `n` (`iterCommutator_eq_bot_of_isNilpotent`).
3. 最小 `k` で `iter k = ⊥` を取る. `k = 0` だと `E = ⊥` で `E` minimal 仮定と矛盾.
4. `k = j + 1` で, `iter j ≠ ⊥`, `iter j ⊴ G`, `iter j ≤ E`. **E の minimality**
   より `iter j = E`.
5. `⁅E, F⁆ = ⁅iter j, F⁆ = iter (j+1) = iter k = ⊥`. 故に `E ≤ centralizer F`.

**下流**: Ch.2 §2D Lucchini K=⊥ aux. -/
theorem le_centralizer_of_isMinimalNormal {E F : Subgroup G}
    (hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal E) (hEF : E ≤ F)
    [F.Normal] [Group.IsNilpotent ↥F] :
    E ≤ Subgroup.centralizer (F : Set G) := by
  classical
  haveI hE_norm : E.Normal := hMin.1
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  -- Find smallest k with iter E F k = ⊥.
  have hExists : ∃ k, iterCommutator E F k = ⊥ :=
    iterCommutator_eq_bot_of_isNilpotent hEF
  set k := Nat.find hExists with hk_def
  have hk_iter : iterCommutator E F k = ⊥ := Nat.find_spec hExists
  -- k = 0 ⇒ E = ⊥, 矛盾.
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · exfalso
    rw [hk0, iterCommutator_zero] at hk_iter
    exact hMin.2.1 hk_iter
  -- k = j + 1, j minimality に達しない.
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk_pos.ne'
  have hIter_j_ne : iterCommutator E F j ≠ ⊥ := fun h => by
    have hjk : j < k := hj ▸ Nat.lt_succ_self j
    exact absurd (Nat.find_min' hExists h) (not_le.mpr hjk)
  haveI : (iterCommutator E F j).Normal := iterCommutator_normal j
  have hIter_j_le : iterCommutator E F j ≤ E := iterCommutator_le_self j
  rcases hMin.2.2 _ inferInstance hIter_j_le with h_bot | h_eq_E
  · exact absurd h_bot hIter_j_ne
  · -- iter j = E, hence ⁅E, F⁆ = iter (j+1) = iter k = ⊥.
    rw [← h_eq_E, ← iterCommutator_succ,
        show j + 1 = k from hj.symm]
    exact hk_iter

/-- **Helper**: 部分群 `E` で `↥E` 冪零 + 非自明 ⇒ `⁅E, E⁆ < E`.

mathlib `IsSolvable.commutator_lt_of_ne_bot` の冪零部分群版 (ambient `G` の可解性は不要).
証明は mathlib 版を mirror: `IsSolvable ↥E ← IsNilpotent ↥E` + `map_subtype_lt_map_subtype`. -/
theorem commutator_lt_self_of_isNilpotent_subtype
    {G : Type*} [Group G]
    (E : Subgroup G) [Group.IsNilpotent ↥E] [Nontrivial ↥E] :
    ⁅E, E⁆ < E := by
  haveI : IsSolvable ↥E := IsNilpotent.to_isSolvable
  rw [← E.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
      Subgroup.map_subtype_lt_map_subtype]
  exact IsSolvable.commutator_lt_top_of_nontrivial ↥E

/-- **Variant of Thm 3.11 part 1** (minimal normal nilpotent ⇒ abelian):
`E ⊴ G` minimal normal + `↥E` 冪零 ⇒ `E` abelian.

`solvable_minimal_normal_isAbelian` の `[IsSolvable G]` 仮定を `[Group.IsNilpotent ↥E]`
に弱めた版. Lucchini K=⊥ で E ≤ F(G) (G は solvable と限らない) の場合に有用. -/
theorem isCommutative_of_isMinimalNormal_of_isNilpotent_subtype
    {G : Type*} [Group G] [Finite G]
    {E : Subgroup G} (hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal E)
    [Group.IsNilpotent ↥E] :
    ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
  haveI hEnormal : E.Normal := hMin.1
  haveI hE_NT : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hMin.2.1
  have hcomm_lt : ⁅E, E⁆ < E := commutator_lt_self_of_isNilpotent_subtype E
  have hCommNormal : (⁅E, E⁆ : Subgroup G).Normal := inferInstance
  have hcomm_eq_bot : ⁅E, E⁆ = ⊥ := by
    rcases hMin.2.2 ⁅E, E⁆ hCommNormal hcomm_lt.le with h | h
    · exact h
    · exact absurd h hcomm_lt.ne
  intro x hx y hy
  have hcomm_xy : ⁅x, y⁆ ∈ ⁅E, E⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [hcomm_eq_bot, Subgroup.mem_bot] at hcomm_xy
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm_xy

/-- **Variant of Thm 3.11**: minimal normal subgroup of finite group with `↥E` nilpotent
⇒ E is elementary abelian p-group for some prime p.

`solvable_minimal_normal_isElementaryAbelian` の `[IsSolvable G]` 仮定を
`[Group.IsNilpotent ↥E]` に弱めた版. 証明は Ch.3 既存版とほぼ同じだが abelianness 取得を
`isCommutative_of_isMinimalNormal_of_isNilpotent_subtype` に置換.

**Lucchini K=⊥ 用途**: E ≤ F(G) で `↥E` 冪零 (F(G) 冪零の部分群経由) かつ minimal normal の
場合に, E が elementary abelian p-group であることを示す. -/
theorem isElementaryAbelian_of_isMinimalNormal_of_isNilpotent_subtype
    {G : Type*} [Group G] [Finite G]
    {E : Subgroup G} (hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal E)
    [Group.IsNilpotent ↥E] :
    ∃ p : ℕ, p.Prime ∧ E.IsElementaryAbelian p := by
  haveI hEnormal : E.Normal := hMin.1
  have hE_ne_bot : E ≠ ⊥ := hMin.2.1
  have habel := isCommutative_of_isMinimalNormal_of_isNilpotent_subtype hMin
  haveI hEcomm : IsMulCommutative ↥E :=
    ⟨⟨fun a b => Subtype.ext (habel a a.2 b b.2)⟩⟩
  haveI hEnt : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hE_ne_bot
  have hE_card_pos : 1 < Nat.card ↥E := Finite.one_lt_card
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hE_card_pos.ne'
  refine ⟨p, hp_prime, ?_⟩
  haveI hpFact : Fact p.Prime := ⟨hp_prime⟩
  -- T = {x : ↥E | x^p = 1} as Subgroup ↥E.
  let T : Subgroup ↥E :=
    { carrier := {x | x ^ p = 1}
      one_mem' := one_pow p
      mul_mem' := by
        intro a b ha hb
        change (a * b) ^ p = 1
        change a ^ p = 1 at ha
        change b ^ p = 1 at hb
        -- rc2: `mul_pow` needs `CommMonoid ↥E`; derive `Commute a b` from `habel`.
        have hcomm : Commute a b := Subtype.ext (habel a a.2 b b.2)
        rw [hcomm.mul_pow, ha, hb, one_mul]
      inv_mem' := by
        intro a ha
        change a⁻¹ ^ p = 1
        change a ^ p = 1 at ha
        rw [inv_pow, ha, inv_one] }
  haveI hT_char : T.Characteristic := by
    rw [Subgroup.characteristic_iff_le_comap]
    intro φ x hx
    rw [Subgroup.mem_comap]
    change (φ x) ^ p = 1
    change x ^ p = 1 at hx
    rw [← map_pow, hx, map_one]
  obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) p hp_dvd
  have hx_pow : x ^ p = 1 := by
    rw [← hx_ord]; exact pow_orderOf_eq_one x
  have hx_ne_one : x ≠ 1 := by
    intro heq
    rw [heq, orderOf_one] at hx_ord
    exact hp_prime.ne_one hx_ord.symm
  have hT_ne_bot : T ≠ ⊥ := by
    intro hbot
    have hx_T : x ∈ T := hx_pow
    rw [hbot, Subgroup.mem_bot] at hx_T
    exact hx_ne_one hx_T
  haveI hTE_normal : (T.map E.subtype).Normal := inferInstance
  have hTE_le_E : T.map E.subtype ≤ E := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  rcases hMin.2.2 (T.map E.subtype) hTE_normal hTE_le_E with hTE_bot | hTE_eq
  · exfalso
    have hT_eq_bot : T = ⊥ := by
      have : T.map E.subtype = (⊥ : Subgroup ↥E).map E.subtype := by
        rw [hTE_bot, Subgroup.map_bot]
      exact Subgroup.map_injective E.subtype_injective this
    exact hT_ne_bot hT_eq_bot
  · refine ⟨fun a b => Subtype.ext (habel a a.2 b b.2), fun y => ?_⟩
    have hy_TE : (y : G) ∈ T.map E.subtype := by
      rw [hTE_eq]; exact y.2
    obtain ⟨z, hz_T, hz_eq⟩ := hy_TE
    have hzy : z = y := Subtype.ext hz_eq
    exact hzy ▸ hz_T

/-- **Lucchini K=⊥ 1st step (with elem abelian conclusion)**: G 非自明有限, A abelian,
`|A| ≥ |G:A|` ⇒ ∃ `E ⊴ G` minimal normal で:
- `E ≤ F(G)`
- `E ≤ centralizer F(G)` (Z(F(G)) absorbs)
- `E` elementary abelian `p`-group (for some prime `p`)

書籍 p.62 の Lucchini K=⊥ proof の最初の **4 ステップ** を 1 補題に集約:
1. **Cor 2.19** で `F(G) ≠ ⊥`.
2. **`exists_isMinimalNormal_le_of_normal`** で minimal normal `E ≤ F(G)` を取得.
3. **`le_centralizer_of_isMinimalNormal`** (Z(F(G)) absorbs lemma) で
   `E ≤ centralizer F(G)`.
4. **`isElementaryAbelian_of_isMinimalNormal_of_isNilpotent_subtype`** で `E` elem
   abelian p-group. `↥E` 冪零性は `E ≤ F(G)` + `fitting.isNilpotent` +
   `subgroupOfEquivOfLe` 経由.

下流: Lucchini K=⊥ 残 2 case (M abelian/non-abelian) でこの E を使う. -/
theorem exists_isMinimalNormal_le_fitting_le_centralizer_fitting
    {G : Type*} [Group G] [Finite G] [Nontrivial G]
    {A : Subgroup G}
    (hA_ab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCard : A.index ≤ Nat.card A) :
    ∃ (E : Subgroup G) (p : ℕ), p.Prime ∧
      OddOrder.Isaacs.Ch02.IsMinimalNormal E ∧
      E ≤ OddOrder.Isaacs.Ch01.fitting G ∧
      E ≤ Subgroup.centralizer ((OddOrder.Isaacs.Ch01.fitting G : Subgroup G) : Set G) ∧
      E.IsElementaryAbelian p := by
  -- F(G) ≠ ⊥ via Cor 2.19.
  have hFne : OddOrder.Isaacs.Ch01.fitting G ≠ ⊥ := by
    intro hF
    have h := OddOrder.Isaacs.Ch02.inf_fitting_ne_bot_of_abelian_card_ge_index hA_ab hCard
    apply h
    rw [hF, inf_bot_eq]
  obtain ⟨E, hMin, hEle⟩ :=
    OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal _ hFne
  -- ↥E nilpotent via E ≤ F(G) + subgroupOfEquivOfLe.
  haveI hFNilp : Group.IsNilpotent ↥(OddOrder.Isaacs.Ch01.fitting G) :=
    OddOrder.Isaacs.Ch01.fitting.isNilpotent
  haveI hENilp : Group.IsNilpotent ↥E :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEle)
  -- E elem abelian p-group.
  obtain ⟨p, hp_prime, hElem⟩ :=
    isElementaryAbelian_of_isMinimalNormal_of_isNilpotent_subtype hMin
  refine ⟨E, p, hp_prime, hMin, hEle, ?_, hElem⟩
  exact le_centralizer_of_isMinimalNormal hMin hEle

/-! ## Lucchini K = ⊥ aux + 本体 -/

/-- **Lucchini K=⊥ Step 5/6 共通 helper**: M ⊴ G で M ⊆ A ⊓ A.normalCore = ⊥ への直接
適用. K = ⊥ かつ M ⊆ A かつ M ⊴ G ⇒ M = ⊥. -/
private theorem eq_bot_of_le_normalCore_bot {A M : Subgroup G}
    (hK_bot : A.normalCore = ⊥) [M.Normal] (hMA : M ≤ A) : M = ⊥ := by
  have h : M ≤ A.normalCore := Subgroup.normal_le_normalCore.mpr hMA
  rw [hK_bot, le_bot_iff] at h
  exact h

/-- Every subgroup of a cyclic group is characteristic.

This proof uses a generator directly: an automorphism sends the generator to another power of the
generator, so it sends each element `x` of a subgroup to an integral power of `x`, still in that
subgroup. -/
theorem characteristic_of_subgroup_of_isCyclic
    {C : Type*} [Group C] [IsCyclic C] (H : Subgroup C) :
    H.Characteristic := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  rw [Subgroup.mem_comap]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg (φ g))
  have hφx : φ x = x ^ m := by
    calc
      φ x = φ (g ^ n) := by rw [hn]
      _ = (φ g) ^ n := by rw [map_zpow]
      _ = (g ^ m) ^ n := by rw [hm]
      _ = g ^ (m * n) := by rw [← zpow_mul]
      _ = g ^ (n * m) := by rw [mul_comm]
      _ = (g ^ n) ^ m := by rw [zpow_mul]
      _ = x ^ m := by rw [hn]
  change φ x ∈ H
  rw [hφx]
  exact H.zpow_mem hx m

/-- A subgroup contained in a cyclic center is characteristic in the ambient group. -/
private theorem characteristic_of_le_center_of_isCyclic_center
    {C : Type*} [Group C] {H : Subgroup C}
    (hH_le_center : H ≤ Subgroup.center C) [IsCyclic (Subgroup.center C)] :
    H.Characteristic := by
  let Z : Subgroup C := Subgroup.center C
  let HZ : Subgroup Z := H.subgroupOf Z
  have hHZ_char : HZ.Characteristic := characteristic_of_subgroup_of_isCyclic HZ
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  rw [Subgroup.mem_comap]
  have hZ_map : Z.map (φ : C →* C) = Z :=
    (Subgroup.characteristic_iff_map_eq.mp (inferInstance : Z.Characteristic)) φ
  let φZ : Z ≃* Z :=
    (φ.subgroupMap Z).trans (MulEquiv.subgroupCongr hZ_map)
  have hxHZ : (⟨x, hH_le_center hx⟩ : Z) ∈ HZ := hx
  have hφxHZ : φZ ⟨x, hH_le_center hx⟩ ∈ HZ := by
    exact (Subgroup.characteristic_iff_le_comap.mp hHZ_char φZ) hxHZ
  change ((φZ ⟨x, hH_le_center hx⟩ : Z) : C) ∈ H at hφxHZ
  simpa [φZ, HZ, Z] using hφxHZ

/-- **Isaacs Thm 2.20 (Lucchini) — `|G|`-induction wrapper** (private).

K=⊥ branch を **inline** で実装 (Step 1-6 を IH 直接適用込みで展開).
K>⊥ branch は Ch.2 `lucchini_K_pos_reduction` + IH on G/K.

K=⊥ case の inline 実装は書籍 p.62-63 に沿う:
1. Cor 2.19 で `A ∩ F(G) ≠ ⊥`, よって `F(G) ≠ ⊥`. minimal normal `E ⊆ F(G)`.
2. `E ⊆ Z(F(G))`, elementary abelian p-group
   (`exists_isMinimalNormal_le_fitting_le_centralizer_fitting`).
3. AE < G (E が `A ∩ F(G)` を中心化 → `A ∩ F(G) ⊴ AE`, K = ⊥ で contradict if AE = G).
4. G/E に IH 適用 → `M = comap (mk' E) (Ā.normalCore)` で `|AE:M| < |G:AE|`.
5. `B = A ∩ M` cyclic + 算術 ⇒ `|M:B| < |B|`.
6. M abelian sub-case: `x ↦ x^p` hom + Dedekind M=EB + `φ(M) ⊴ G ⊆ A` ⇒ M = ⊥ ⇒ E = ⊥, 矛盾.
7. M non-abelian sub-case: `Z(M)` cyclic + `B ∩ F(M) ⊴ G ⊆ A` nontrivial ⇒ K > ⊥, 矛盾. -/
private theorem lucchini_aux : ∀ n : ℕ,
    ∀ {G : Type*} [Group G] [Finite G] {A : Subgroup G},
      Nat.card G ≤ n →
      A < ⊤ →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∃ g : G, A = Subgroup.zpowers g) →
      (A.normalCore.subgroupOf A).index < A.index := by
  intro n
  induction n with
  | zero =>
    intro G _ _ A hcard _ _ _
    exact absurd hcard (Nat.not_le_of_lt Nat.card_pos)
  | succ n ih =>
    intro G _ _ A hcard hAprop hAab hAcyc
    by_cases hsmall : Nat.card G ≤ n
    · exact ih hsmall hAprop hAab hAcyc
    -- |G| = n+1 exactly.
    set K := A.normalCore with hKdef
    haveI hKnormal : K.Normal := A.normalCore_normal
    have hK_le_A : K ≤ A := Subgroup.normalCore_le A
    by_cases hK_bot : K = ⊥
    · -- K = ⊥ case: inline Step 1-6 proof.
      -- 目標を rewrite: K = ⊥ で LHS = |A|.
      have h_idx : (K.subgroupOf A).index = Nat.card ↥A := by
        rw [hK_bot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
      change (K.subgroupOf A).index < A.index
      rw [h_idx]
      -- 以下 |A| < |G:A| を by_contra で示す.
      by_contra hNotLt
      push Not at hNotLt
      -- hNotLt : A.index ≤ Nat.card ↥A.
      -- G nontrivial: A < ⊤ より.
      haveI hGnontrivial : Nontrivial G := by
        by_contra hcon
        rw [not_nontrivial_iff_subsingleton] at hcon
        haveI := hcon
        have hAtop : A = ⊤ := by
          ext x
          refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
          have hx1 : x = 1 := Subsingleton.elim _ _
          rw [hx1]; exact A.one_mem
        exact hAprop.ne hAtop
      -- Step 1-2: Get minimal normal E ≤ F(G), E ≤ Z(F(G)), E elem abelian p-group.
      obtain ⟨E, p, hp_prime, hMinE, hE_le_fit, hE_le_cent_fit, hE_elemAb⟩ :=
        exists_isMinimalNormal_le_fitting_le_centralizer_fitting hAab hNotLt
      haveI hEnormal : E.Normal := hMinE.1
      have hE_ne_bot : E ≠ ⊥ := hMinE.2.1
      haveI hEnontrivial : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hE_ne_bot
      have hp_pos : 0 < p := hp_prime.pos
      haveI hp_fact : Fact p.Prime := ⟨hp_prime⟩
      -- A ∩ F(G) ≠ ⊥ via Cor 2.19.
      have hAcapF_ne : A ⊓ OddOrder.Isaacs.Ch01.fitting G ≠ ⊥ :=
        OddOrder.Isaacs.Ch02.inf_fitting_ne_bot_of_abelian_card_ge_index hAab hNotLt
      -- Step 3: AE < G.
      -- 主張: E ≤ centralizer F(G) ⇒ E normalizes A ⊓ F(G). A also normalizes A ⊓ F(G).
      -- So A ⊓ F(G) ⊴ AE. If AE = G then A ⊓ F(G) ⊴ G ⊆ A ⇒ K ≠ ⊥, contradiction.
      have hAE_lt : A ⊔ E < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro hAEtop
        -- A ⊓ F(G) ⊴ AE = G. Each element of A ⊓ F(G) centralized by E and by A.
        -- ⇒ A ⊓ F(G) ⊴ G ⊆ A ⇒ A ⊓ F(G) ⊆ A.normalCore = K = ⊥ ⇒ A ⊓ F(G) = ⊥, contradiction.
        -- A ⊓ F(G) ≤ A: trivial.
        have hAF_le_A : A ⊓ OddOrder.Isaacs.Ch01.fitting G ≤ A := inf_le_left
        -- Construct normality of A ⊓ F(G) in G = AE = ⊤.
        -- Show A ⊓ F(G) ⊴ G by: every g ∈ G writes as a·e (a ∈ A, e ∈ E); both normalize A ⊓ F(G).
        -- A normalizes A ⊓ F(G): A abelian ⇒ A normalizes A; A normalizes F(G) (char).
        -- E centralizes F(G) so normalizes F(G); E ⊆ F(G) ⊆ centralizer of A ⊓ F(G).
        -- We'll show: A ⊓ F(G) ⊴ G via direct verification.
        have hAFnormal : (A ⊓ OddOrder.Isaacs.Ch01.fitting G).Normal := by
          refine ⟨fun x hx g => ?_⟩
          -- g ∈ G = AE. Write g = a·e? Need element decomposition. Use sup_eq_top first.
          have hgAE : g ∈ (⊤ : Subgroup G) := Subgroup.mem_top g
          rw [← hAEtop] at hgAE
          -- A ⊔ E as a set = A · E (since E ⊴ G, mul_normal applies).
          have hAE_set : ((A ⊔ E : Subgroup G) : Set G) = (A : Set G) * (E : Set G) :=
            Subgroup.mul_normal A E
          rw [← SetLike.mem_coe, hAE_set] at hgAE
          obtain ⟨a, ha, e, he, hg_eq⟩ := hgAE
          subst hg_eq
          rw [Subgroup.mem_inf] at hx
          obtain ⟨hxA, hxF⟩ := hx
          -- Goal: (a * e) * x * (a * e)⁻¹ ∈ A ⊓ F(G).
          rw [Subgroup.mem_inf]
          -- Compute: (a*e) * x * (a*e)⁻¹ = a*(e*x*e⁻¹)*a⁻¹.
          have heCentX : e * x = x * e := by
            have : e ∈ Subgroup.centralizer
                ((OddOrder.Isaacs.Ch01.fitting G : Subgroup G) : Set G) := hE_le_cent_fit he
            rw [Subgroup.mem_centralizer_iff] at this
            exact (this x hxF).symm
          have heq : (a * e) * x * (a * e)⁻¹ = a * x * a⁻¹ := by
            have : (a * e) * x * (a * e)⁻¹ = a * (e * x * e⁻¹) * a⁻¹ := by group
            rw [this]
            have hex_inv : e * x * e⁻¹ = x := by
              rw [heCentX]
              group
            rw [hex_inv]
          rw [heq]
          refine ⟨?_, ?_⟩
          · -- a * x * a⁻¹ ∈ A: x ∈ A, A abelian (so conjugation preserves A).
            -- Actually we need A.Normal here? Not necessarily. But A abelian + x ∈ A + a ∈ A
            -- ⇒ a * x * a⁻¹ = x ∈ A.
            have hcomm : a * x = x * a := hAab a ha x hxA
            have : a * x * a⁻¹ = x := by rw [hcomm]; group
            rw [this]
            exact hxA
          · -- a * x * a⁻¹ ∈ F(G): F(G) ⊴ G.
            exact ((OddOrder.Isaacs.Ch01.fitting.normal G).conj_mem _ hxF a)
        -- A ⊓ F(G) normal in G, ≤ A ⇒ ≤ A.normalCore = K = ⊥.
        have h_inf_le_K : A ⊓ OddOrder.Isaacs.Ch01.fitting G ≤ K :=
          Subgroup.normal_le_normalCore.mpr hAF_le_A
        rw [hK_bot, le_bot_iff] at h_inf_le_K
        exact hAcapF_ne h_inf_le_K
      -- Step 4: G/E に IH 適用.
      let f : G →* G ⧸ E := QuotientGroup.mk' E
      have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective E
      have hf_ker : f.ker = E := QuotientGroup.ker_mk' E
      set Ā : Subgroup (G ⧸ E) := A.map f with hĀ_def
      -- Ā < ⊤.
      have hĀ_proper : Ā < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro h_eq
        have h1 : Subgroup.comap f Ā = ⊤ := by rw [h_eq]; exact Subgroup.comap_top _
        have h2 : Subgroup.comap f Ā = E ⊔ A := by
          rw [hĀ_def, QuotientGroup.comap_map_mk']
        rw [h2, sup_comm] at h1
        exact hAE_lt.ne h1
      -- Ā cyclic.
      have hĀ_cyc : ∃ ĝ : G ⧸ E, Ā = Subgroup.zpowers ĝ := by
        obtain ⟨g, hg⟩ := hAcyc
        refine ⟨f g, ?_⟩
        rw [hĀ_def, hg, f.map_zpowers]
      -- Ā abelian.
      have hĀ_ab : ∀ x ∈ Ā, ∀ y ∈ Ā, x * y = y * x := by
        intro x hx y hy
        obtain ⟨a, haA, hfa⟩ := hx
        obtain ⟨b, hbA, hfb⟩ := hy
        rw [← hfa, ← hfb, ← map_mul, ← map_mul, hAab a haA b hbA]
      -- |G/E| ≤ n.
      have hE_card_ge : 2 ≤ Nat.card ↥E := Finite.one_lt_card
      have hquot_card : Nat.card (G ⧸ E) ≤ n := by
        have heq : Nat.card G = Nat.card (G ⧸ E) * Nat.card ↥E :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup E
        have h1 : Nat.card (G ⧸ E) * 2 ≤ Nat.card G := by
          rw [heq]; exact Nat.mul_le_mul_left _ hE_card_ge
        have h2 : Nat.card G ≤ n + 1 := hcard
        omega
      -- IH on G/E.
      have hIH_quot : (Ā.normalCore.subgroupOf Ā).index < Ā.index :=
        ih hquot_card hĀ_proper hĀ_ab hĀ_cyc
      -- Define M = comap (mk' E) (Ā.normalCore).
      set Mbar := Ā.normalCore with hMbar_def
      set M : Subgroup G := Subgroup.comap f Mbar with hM_def
      haveI hMbar_norm : Mbar.Normal := Subgroup.normalCore_normal Ā
      haveI hM_norm : M.Normal := hMbar_norm.comap f
      -- E ≤ M.
      have hE_le_M : E ≤ M := by
        intro x hxE
        rw [hM_def, Subgroup.mem_comap]
        have : f x = 1 := by
          rw [← hf_ker] at hxE
          exact hxE
        rw [this]
        exact one_mem _
      -- M ≤ A ⊔ E (i.e., M ≤ AE).
      have hM_le_AE : M ≤ A ⊔ E := by
        have h1 : M ≤ Subgroup.comap f Ā := Subgroup.comap_mono (Subgroup.normalCore_le Ā)
        rw [hĀ_def, QuotientGroup.comap_map_mk', sup_comm] at h1
        exact h1
      -- A ⊔ M = A ⊔ E (since E ≤ M ≤ A ⊔ E).
      have hAM_eq_AE : A ⊔ M = A ⊔ E := by
        apply le_antisymm
        · exact sup_le le_sup_left hM_le_AE
        · exact sup_le le_sup_left (hE_le_M.trans le_sup_right)
      -- B = A ⊓ M.
      set B : Subgroup G := A ⊓ M with hB_def
      -- B ≤ A.
      have hB_le_A : B ≤ A := inf_le_left
      have hB_le_M : B ≤ M := inf_le_right
      haveI hA_cyclic_subtype : IsCyclic A := by
        obtain ⟨g, hg⟩ := hAcyc
        rw [hg]
        infer_instance
      haveI hB_cyclic : IsCyclic B := Subgroup.isCyclic_of_le hB_le_A
      have hM_le_EA : M ≤ E ⊔ A := by
        simpa [sup_comm] using hM_le_AE
      -- Dedekind: `M ≤ E ⊔ A` and `E ≤ M` give `M = E ⊔ (M ⊓ A) = E ⊔ B`.
      have hM_eq_EB : M = E ⊔ B := by
        rw [hB_def]
        simpa [inf_comm] using
          Subgroup.eq_sup_inf_of_le_sup_of_normal_of_le
            (E := E) (A := A) (M := M) hE_le_M hM_le_EA
      haveI hE_subM_normal : (E.subgroupOf M).Normal := hEnormal.subgroupOf M
      let qM : M →* M ⧸ E.subgroupOf M := QuotientGroup.mk' (E.subgroupOf M)
      haveI hB_subM_cyclic : IsCyclic (B.subgroupOf M) := by
        rw [(Subgroup.subgroupOfEquivOfLe hB_le_M).isCyclic]
        infer_instance
      have hqB_surj : Function.Surjective (qM.comp (B.subgroupOf M).subtype) := by
        intro y
        refine QuotientGroup.induction_on y ?_
        intro m
        have hm_EB : (m : G) ∈ E ⊔ B := by
          rw [← hM_eq_EB]
          exact m.property
        obtain ⟨e, he, b, hb, hmb⟩ := Subgroup.mem_sup_of_normal_left.mp hm_EB
        refine ⟨⟨⟨b, hB_le_M hb⟩, hb⟩, ?_⟩
        dsimp [qM]
        rw [QuotientGroup.eq]
        change ((b⁻¹ * (m : G)) ∈ E)
        rw [← hmb]
        simpa [mul_assoc] using hEnormal.conj_mem' e he b
      haveI hM_mod_E_cyclic : IsCyclic (M ⧸ E.subgroupOf M) :=
        isCyclic_of_surjective (qM.comp (B.subgroupOf M).subtype) hqB_surj
      have hM_comm_of_E_central
          (hE_cent : E.subgroupOf M ≤ Subgroup.center M) :
          ∀ x y : M, x * y = y * x := by
        have hcomm := qM.isMulCommutative_of_isCyclic_of_ker_le_center (by
          rw [QuotientGroup.ker_mk']
          exact hE_cent)
        exact fun x y => hcomm.is_comm.comm x y
      -- E ≤ M but A ⊓ E ⊆ A.normalCore (need E ⊓ A normal in A? actually we use E.Normal).
      -- Translation: Ā.index = (A ⊔ E).index.
      have hĀ_index_eq : Ā.index = (A ⊔ E).index := by
        rw [hĀ_def]
        -- Ā = A.map f. By index_map_eq with ker f = E ≤ A ⊔ E.
        -- But A.map f has index (A.map f).index. We need (A ⊔ E).index.
        -- Use: Subgroup.comap f Ā = A ⊔ E (via QuotientGroup.comap_map_mk' + sup_comm).
        -- And (Subgroup.comap f Ā).index = Ā.index by index_comap_of_surjective.
        have h1 : Subgroup.comap f (A.map f) = E ⊔ A := QuotientGroup.comap_map_mk' E A
        have h2 : (Subgroup.comap f (A.map f)).index = (A.map f).index :=
          (A.map f).index_comap_of_surjective hf_surj
        rw [h1, sup_comm] at h2
        exact h2.symm
      -- (Mbar.subgroupOf Ā).index = (M.subgroupOf (A ⊔ E)).index via correspondence.
      have hMbar_idx_eq : (Mbar.subgroupOf Ā).index = (M.subgroupOf (A ⊔ E)).index := by
        -- relIndex Mbar Ā = relIndex (comap f Mbar) (A ⊔ E).
        -- Use: (Mbar.subgroupOf Ā).index = Mbar.relIndex Ā.
        -- relIndex (comap f Mbar) (A ⊔ E) := (M.subgroupOf (A ⊔ E)).index.
        -- relIndex_comap: relIndex (comap f H) K = relIndex H (map f K).
        -- With H = Mbar, K = A ⊔ E: relIndex M (A⊔E) = relIndex Mbar (map f (A⊔E)).
        -- map f (A ⊔ E) = (map f A) ⊔ (map f E) = Ā ⊔ ⊥ = Ā.
        have h_map_AE : Subgroup.map f (A ⊔ E) = Ā := by
          rw [Subgroup.map_sup, hĀ_def]
          have hmap_E : Subgroup.map f E = ⊥ := by
            rw [eq_bot_iff]
            rintro _ ⟨x, hxE, rfl⟩
            have : f x = 1 := by rw [← hf_ker] at hxE; exact hxE
            rw [this]
            exact Subgroup.mem_bot.mpr rfl
          rw [hmap_E, sup_bot_eq]
        have hcomap : (Mbar.subgroupOf Ā).index = (M.subgroupOf (A ⊔ E)).index := by
          change Mbar.relIndex Ā = M.relIndex (A ⊔ E)
          rw [hM_def, Subgroup.relIndex_comap, h_map_AE]
        exact hcomap
      -- Step 4 conclusion: |A⊔E : M| < |G : A⊔E|.
      have hStep4 : (M.subgroupOf (A ⊔ E)).index < (A ⊔ E).index := by
        rw [← hMbar_idx_eq, ← hĀ_index_eq]; exact hIH_quot
      -- Step 5: |M:B| < |B|.
      have hA_le_AE : A ≤ A ⊔ E := le_sup_left
      have hB_relIdx_A : B.relIndex A = M.relIndex A := by
        rw [hB_def, Subgroup.inf_relIndex_left]
      -- |A : B| = |A ⊔ M : M| via 2nd iso (M normal).
      -- relIndex_sup_right (K normal): K.relIndex (H ⊔ K) = K.relIndex H. So M.relIndex (A⊔M)
      -- = M.relIndex A.
      have h_M_relIdx : M.relIndex (A ⊔ M) = M.relIndex A := Subgroup.relIndex_sup_right A M
      -- (M.subgroupOf (A⊔E)).index = M.relIndex (A⊔E) = M.relIndex (A⊔M) = M.relIndex A
      --   = B.relIndex A.
      have hStep4_via_B : B.relIndex A < (A ⊔ E).index := by
        rw [hB_relIdx_A, ← h_M_relIdx, hAM_eq_AE]
        exact hStep4
      -- Tower: A.index = (A ⊔ E).index * A.relIndex (A ⊔ E).
      have hTower_GA : (A ⊔ E).index * A.relIndex (A ⊔ E) = A.index := by
        rw [Nat.mul_comm]
        exact Subgroup.relIndex_mul_index hA_le_AE
      -- |A| = |B| * |A:B| (Lagrange in A).
      have hLag_A : Nat.card ↥A = Nat.card ↥B * B.relIndex A := by
        have hB_card : Nat.card ↥(B.subgroupOf A) = Nat.card ↥B :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_A).toEquiv
        have h := (B.subgroupOf A).card_mul_index
        rw [hB_card] at h
        exact h.symm
      -- |M| = |B| * |M:B| (Lagrange in M, B ≤ M).
      have hLag_M : Nat.card ↥M = Nat.card ↥B * B.relIndex M := by
        have hB_card : Nat.card ↥(B.subgroupOf M) = Nat.card ↥B :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_M).toEquiv
        have h := (B.subgroupOf M).card_mul_index
        rw [hB_card] at h
        exact h.symm
      -- Card(A⊔E) = Nat.card A * |A⊔E:A| = Nat.card M * |A⊔E:M|.
      have hcard_AE_A : Nat.card ↥A * A.relIndex (A ⊔ E) = Nat.card ↥(A ⊔ E : Subgroup G) := by
        have hA_card : Nat.card ↥(A.subgroupOf (A ⊔ E)) = Nat.card ↥A :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_AE).toEquiv
        have h := (A.subgroupOf (A ⊔ E)).card_mul_index
        rw [hA_card] at h
        exact h
      have hcard_AE_M : Nat.card ↥M * M.relIndex (A ⊔ E) = Nat.card ↥(A ⊔ E : Subgroup G) := by
        have hM_card : Nat.card ↥(M.subgroupOf (A ⊔ E)) = Nat.card ↥M :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM_le_AE).toEquiv
        have h := (M.subgroupOf (A ⊔ E)).card_mul_index
        rw [hM_card] at h
        exact h
      have hcard_eq : Nat.card ↥A * A.relIndex (A ⊔ E) =
          Nat.card ↥M * M.relIndex (A ⊔ E) := by
        rw [hcard_AE_A, hcard_AE_M]
      -- M.relIndex (A⊔E) = B.relIndex A (from previous).
      have h_M_AE_eq : M.relIndex (A ⊔ E) = B.relIndex A := by
        rw [← hAM_eq_AE, h_M_relIdx, hB_relIdx_A]
      -- Substitute: b·|A:B| · |A⊔E:A| = b·|M:B| · |A:B|.
      rw [hLag_A, hLag_M, h_M_AE_eq] at hcard_eq
      -- hcard_eq : b * |A:B| * |A⊔E:A| = b * |M:B| * |A:B|
      have hb_pos : 0 < Nat.card ↥B := Nat.card_pos
      have hAB_ne : (A ⊔ E).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hAE_pos : 0 < (A ⊔ E).index := Nat.pos_of_ne_zero hAB_ne
      have hAB_pos : 0 < B.relIndex A := by
        change 0 < (B.subgroupOf A).index
        exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      -- From hcard_eq: divide by b·|A:B| (both positive).
      have hAEA_eq_MB : A.relIndex (A ⊔ E) = B.relIndex M := by
        have h : Nat.card ↥B * B.relIndex A * A.relIndex (A ⊔ E) =
            Nat.card ↥B * B.relIndex A * B.relIndex M := by
          rw [hcard_eq]; ring
        have hbAB_pos : 0 < Nat.card ↥B * B.relIndex A := Nat.mul_pos hb_pos hAB_pos
        exact Nat.eq_of_mul_eq_mul_left hbAB_pos h
      -- A.index = (A⊔E).index · B.relIndex M (substituting).
      have hAidx_factor : A.index = (A ⊔ E).index * B.relIndex M := by
        rw [← hTower_GA, hAEA_eq_MB]
      -- hNotLt: A.index ≤ Nat.card ↥A = b · |A:B|.
      have hAidx_bd : (A ⊔ E).index * B.relIndex M ≤ Nat.card ↥B * B.relIndex A := by
        rw [← hAidx_factor, ← hLag_A]; exact hNotLt
      -- IH gives |A:B| < (A⊔E).index. Multiply by b:
      -- b · |A:B| < b · (A⊔E).index. Combined with hAidx_bd:
      -- (A⊔E).index · |M:B| ≤ b · |A:B| < b · (A⊔E).index.
      have hCalc2 : Nat.card ↥B * B.relIndex A < Nat.card ↥B * (A ⊔ E).index := by
        exact Nat.mul_lt_mul_of_pos_left hStep4_via_B hb_pos
      have hCalc3 : (A ⊔ E).index * B.relIndex M < Nat.card ↥B * (A ⊔ E).index :=
        Nat.lt_of_le_of_lt hAidx_bd hCalc2
      rw [mul_comm (Nat.card ↥B)] at hCalc3
      have hStep5 : B.relIndex M < Nat.card ↥B :=
        Nat.lt_of_mul_lt_mul_left hCalc3
      -- Step 6: M abelian / nonabelian split.
      by_cases hM_ab : ∀ x y : M, x * y = y * x
      · -- Abelian case: the `p`-power image is normal in `G` and lies in `A`, hence is trivial.
        letI : CommGroup M := { (inferInstance : Group M) with
          mul_comm := hM_ab }
        let φ : M →* M := powMonoidHom p
        let R : Subgroup M := φ.range
        haveI hR_char : R.Characteristic := by
          dsimp [R, φ]
          infer_instance
        haveI hR_map_normal : (R.map M.subtype).Normal := inferInstance
        have hR_map_le_A : R.map M.subtype ≤ A := by
          rintro x ⟨m, hmR, rfl⟩
          obtain ⟨m0, hm0⟩ := hmR
          dsimp [φ] at hm0
          have hm0_EB : (m0 : G) ∈ E ⊔ B := by
            rw [← hM_eq_EB]
            exact m0.property
          obtain ⟨e, he, b, hb, hmb⟩ := Subgroup.mem_sup_of_normal_left.mp hm0_EB
          have he_pow : (e : G) ^ p = 1 := by
            have heE : (⟨e, he⟩ : E) ^ p = 1 := hE_elemAb.2 ⟨e, he⟩
            exact congrArg (fun z : E => (z : G)) heE
          rw [← hm0]
          change ((m0 : G) ^ p) ∈ A
          rw [← hmb]
          have heb_comm : e * b = b * e := by
            have hcomm := hM_ab ⟨e, hE_le_M he⟩ ⟨b, hB_le_M hb⟩
            exact congrArg (fun z : M => (z : G)) hcomm
          rw [((commute_iff_eq e b).mpr heb_comm).mul_pow, he_pow, one_mul]
          exact A.pow_mem (hB_le_A hb) p
        have hR_map_bot : R.map M.subtype = ⊥ :=
          eq_bot_of_le_normalCore_bot hK_bot hR_map_le_A
        have hR_bot : R = ⊥ := by
          have hmap : R.map M.subtype = (⊥ : Subgroup M).map M.subtype := by
            rw [hR_map_bot, Subgroup.map_bot]
          exact Subgroup.map_injective M.subtype_injective hmap
        have hB_pow_p : ∀ b : B, b ^ p = 1 := by
          intro b
          let m : M := ⟨(b : G), hB_le_M b.property⟩
          have hmR : m ^ p ∈ R := by
            refine ⟨m, ?_⟩
            rfl
          rw [hR_bot, Subgroup.mem_bot] at hmR
          apply Subtype.ext
          change ((b : G) ^ p = 1)
          exact congrArg (fun z : M => (z : G)) hmR
        have hB_card_le_p : Nat.card ↥B ≤ p := by
          obtain ⟨b0, hb0⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
            (inferInstance : IsCyclic B)
          have hb0_pow : b0 ^ p = 1 := hB_pow_p b0
          have h_ord_dvd : orderOf b0 ∣ p := orderOf_dvd_of_pow_eq_one hb0_pow
          have h_ord_le : orderOf b0 ≤ p := Nat.le_of_dvd hp_pos h_ord_dvd
          rw [← orderOf_eq_card_of_zpowers_eq_top hb0]
          exact h_ord_le
        haveI hB_subM_normal : (B.subgroupOf M).Normal := inferInstance
        let qB : M →* M ⧸ B.subgroupOf M := QuotientGroup.mk' (B.subgroupOf M)
        have hE_pgroup : IsPGroup p E := by
          intro e
          refine ⟨1, ?_⟩
          simpa using hE_elemAb.2 e
        have hE_subM_pgroup : IsPGroup p (E.subgroupOf M) :=
          hE_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hE_le_M).symm
        have hqE_surj : Function.Surjective (qB.comp (E.subgroupOf M).subtype) := by
          intro y
          refine QuotientGroup.induction_on y ?_
          intro m
          have hm_EB : (m : G) ∈ E ⊔ B := by
            rw [← hM_eq_EB]
            exact m.property
          obtain ⟨e, he, b, hb, hmb⟩ := Subgroup.mem_sup_of_normal_left.mp hm_EB
          refine ⟨⟨⟨e, hE_le_M he⟩, he⟩, ?_⟩
          dsimp [qB]
          rw [QuotientGroup.eq]
          change ((e⁻¹ * (m : G)) ∈ B)
          rw [← hmb]
          simpa [mul_assoc] using hb
        have hM_mod_B_pgroup : IsPGroup p (M ⧸ B.subgroupOf M) :=
          hE_subM_pgroup.of_surjective (qB.comp (E.subgroupOf M).subtype) hqE_surj
        obtain ⟨k, hk_card⟩ := (IsPGroup.iff_card (p := p) (G := M ⧸ B.subgroupOf M)).mp
          hM_mod_B_pgroup
        have hquot_card_eq : Nat.card (M ⧸ B.subgroupOf M) = B.relIndex M := by
          change Nat.card (M ⧸ B.subgroupOf M) = (B.subgroupOf M).index
          exact (Subgroup.index_eq_card (B.subgroupOf M)).symm
        have hrel_lt_p : B.relIndex M < p := lt_of_lt_of_le hStep5 hB_card_le_p
        have hk_zero : k = 0 := by
          cases k with
          | zero => rfl
          | succ k =>
              have hp_le_pow : p ≤ p ^ (k + 1) :=
                Nat.le_of_dvd (Nat.pow_pos hp_pos : 0 < p ^ (k + 1))
                  (dvd_pow_self p (Nat.succ_ne_zero k))
              have : p ^ (k + 1) < p := by
                rw [← hk_card, hquot_card_eq]
                exact hrel_lt_p
              omega
        have hrel_eq_one : B.relIndex M = 1 := by
          rw [← hquot_card_eq, hk_card, hk_zero, pow_zero]
        have hM_le_B : M ≤ B := Subgroup.relIndex_eq_one.mp hrel_eq_one
        have hM_eq_B : M = B := le_antisymm hM_le_B hB_le_M
        have hM_le_A : M ≤ A := hM_eq_B.trans_le hB_le_A
        have hM_bot : M = ⊥ := eq_bot_of_le_normalCore_bot hK_bot hM_le_A
        have hE_bot : E = ⊥ := le_bot_iff.mp (hE_le_M.trans (le_of_eq hM_bot))
        exact hE_ne_bot hE_bot
      · -- Nonabelian case: if `E ≤ Z(M)`, then `M/E` cyclic forces M abelian.
        have hE_not_le_center : ¬ E.subgroupOf M ≤ Subgroup.center M := by
          intro hE_cent
          exact hM_ab (hM_comm_of_E_central hE_cent)
        let ZM : Subgroup M := Subgroup.center M
        have hEinfZ_bot : E.subgroupOf M ⊓ ZM = ⊥ := by
          let ZG : Subgroup G := ZM.map M.subtype
          let C : Subgroup G := E ⊓ ZG
          haveI hZG_normal : ZG.Normal := inferInstance
          haveI hC_normal : C.Normal := inferInstance
          have hC_le_E : C ≤ E := inf_le_left
          rcases hMinE.2.2 C hC_normal hC_le_E with hC_bot | hC_eq_E
          · apply le_bot_iff.mp
            intro x hx
            have hxC : (x : G) ∈ C := by
              exact ⟨Subgroup.mem_subgroupOf.mp hx.1, ⟨x, hx.2, rfl⟩⟩
            rw [hC_bot, Subgroup.mem_bot] at hxC
            exact Subgroup.mem_bot.mpr (Subtype.ext hxC)
          · exfalso
            have hE_le_ZG : E ≤ ZG := by
              intro x hx
              have hxC : x ∈ C := by
                rw [hC_eq_E]
                exact hx
              exact hxC.2
            have hE_subM_le_Z : E.subgroupOf M ≤ ZM := by
              intro x hx
              have hxZG : (x : G) ∈ ZG := hE_le_ZG (Subgroup.mem_subgroupOf.mp hx)
              obtain ⟨z, hzZ, hzx⟩ := hxZG
              have hzx' : z = x := Subtype.ext hzx
              rwa [← hzx']
            exact hE_not_le_center hE_subM_le_Z
        let qZ : ZM →* M ⧸ E.subgroupOf M := qM.comp ZM.subtype
        have hqZ_inj : Function.Injective qZ := by
          rw [← MonoidHom.ker_eq_bot_iff]
          apply le_bot_iff.mp
          intro z hz
          rw [MonoidHom.mem_ker] at hz
          have hzE : (z : M) ∈ E.subgroupOf M := by
            change qM (z : M) = 1 at hz
            dsimp [qM] at hz
            exact (QuotientGroup.eq_one_iff (N := E.subgroupOf M) (z : M)).mp hz
          have hzInf : (z : M) ∈ E.subgroupOf M ⊓ ZM := ⟨hzE, z.property⟩
          rw [hEinfZ_bot, Subgroup.mem_bot] at hzInf
          exact Subgroup.mem_bot.mpr (Subtype.ext hzInf)
        haveI hZM_cyclic : IsCyclic ZM := isCyclic_of_injective qZ hqZ_inj
        have hM_ne_bot : M ≠ ⊥ := by
          intro hM_bot
          exact hE_ne_bot (le_bot_iff.mp (hE_le_M.trans (le_of_eq hM_bot)))
        haveI hM_nontrivial : Nontrivial M :=
          (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
        let H : Subgroup M := B.subgroupOf M ⊓ OddOrder.Isaacs.Ch01.fitting M
        have hBsubM_ab : ∀ a ∈ B.subgroupOf M, ∀ b ∈ B.subgroupOf M, a * b = b * a := by
          intro a ha b hb
          apply Subtype.ext
          change (a : G) * (b : G) = (b : G) * (a : G)
          exact hAab (a : G) (hB_le_A (Subgroup.mem_subgroupOf.mp ha))
            (b : G) (hB_le_A (Subgroup.mem_subgroupOf.mp hb))
        have hBM_card_ge_index : (B.subgroupOf M).index ≤ Nat.card (B.subgroupOf M) := by
          change B.relIndex M ≤ Nat.card (B.subgroupOf M)
          rw [show Nat.card (B.subgroupOf M) = Nat.card B from
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_M).toEquiv]
          exact le_of_lt hStep5
        have hH_ne_bot : H ≠ ⊥ :=
          OddOrder.Isaacs.Ch02.inf_fitting_ne_bot_of_abelian_card_ge_index
            (G := M) (A := B.subgroupOf M) hBsubM_ab hBM_card_ge_index
        have hH_le_center : H ≤ ZM := by
          intro x hx
          rw [Subgroup.mem_center_iff]
          intro m
          have hxB : (x : G) ∈ B := Subgroup.mem_subgroupOf.mp hx.1
          have hxFitG : (x : G) ∈ OddOrder.Isaacs.Ch01.fitting G := by
            exact OddOrder.Isaacs.Ch01.fitting_map_subtype_le_fitting
              ⟨x, hx.2, rfl⟩
          have hm_EB : (m : G) ∈ E ⊔ B := by
            rw [← hM_eq_EB]
            exact m.property
          obtain ⟨e, he, b, hb, hmb⟩ := Subgroup.mem_sup_of_normal_left.mp hm_EB
          have he_comm_x : e * (x : G) = (x : G) * e := by
            have he_cent : e ∈ Subgroup.centralizer
                ((OddOrder.Isaacs.Ch01.fitting G : Subgroup G) : Set G) :=
              hE_le_cent_fit he
            rw [Subgroup.mem_centralizer_iff] at he_cent
            exact (he_cent (x : G) hxFitG).symm
          have hb_comm_x : b * (x : G) = (x : G) * b :=
            hAab b (hB_le_A hb) (x : G) (hB_le_A hxB)
          apply Subtype.ext
          change (m : G) * (x : G) = (x : G) * (m : G)
          rw [← hmb]
          calc
            (e * b) * (x : G) = e * (b * (x : G)) := by group
            _ = e * ((x : G) * b) := by rw [hb_comm_x]
            _ = (e * (x : G)) * b := by group
            _ = ((x : G) * e) * b := by rw [he_comm_x]
            _ = (x : G) * (e * b) := by group
        haveI hH_char : H.Characteristic :=
          characteristic_of_le_center_of_isCyclic_center hH_le_center
        haveI hH_map_normal : (H.map M.subtype).Normal := inferInstance
        have hH_map_le_A : H.map M.subtype ≤ A := by
          rintro x ⟨y, hy, rfl⟩
          exact hB_le_A (Subgroup.mem_subgroupOf.mp hy.1)
        have hH_map_bot : H.map M.subtype = ⊥ :=
          eq_bot_of_le_normalCore_bot hK_bot hH_map_le_A
        have hH_bot : H = ⊥ := by
          have hmap : H.map M.subtype = (⊥ : Subgroup M).map M.subtype := by
            rw [hH_map_bot, Subgroup.map_bot]
          exact Subgroup.map_injective M.subtype_injective hmap
        exact hH_ne_bot hH_bot
    · -- K > ⊥ case: invoke IH on G/K + Ch.2 reduction lemma.
      let f : G →* G ⧸ K := QuotientGroup.mk' K
      have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective K
      set Ā : Subgroup (G ⧸ K) := A.map f with hĀ_def
      -- Ā < ⊤: from A < ⊤ and K ≤ A.
      have hĀ_proper : Ā < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro h_eq
        have h1 : Subgroup.comap f Ā = ⊤ := by rw [h_eq]; exact Subgroup.comap_top _
        have h2 : Subgroup.comap f Ā = K ⊔ A := by
          rw [hĀ_def, QuotientGroup.comap_map_mk']
        have h3 : K ⊔ A = A := sup_of_le_right hK_le_A
        rw [h2, h3] at h1
        exact ne_of_lt hAprop h1
      -- Ā cyclic.
      have hĀ_cyc : ∃ ĝ : G ⧸ K, Ā = Subgroup.zpowers ĝ := by
        obtain ⟨g, hg⟩ := hAcyc
        refine ⟨f g, ?_⟩
        rw [hĀ_def, hg, f.map_zpowers]
      -- Ā abelian.
      have hĀ_ab : ∀ x ∈ Ā, ∀ y ∈ Ā, x * y = y * x := by
        intro x hx y hy
        obtain ⟨a, haA, hfa⟩ := hx
        obtain ⟨b, hbA, hfb⟩ := hy
        rw [← hfa, ← hfb, ← map_mul, ← map_mul, hAab a haA b hbA]
      -- |G/K| ≤ n.
      have hKnonbot_card : 2 ≤ Nat.card ↥K := by
        haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK_bot
        exact Finite.one_lt_card
      have hquot_card : Nat.card (G ⧸ K) ≤ n := by
        have heq : Nat.card G = Nat.card (G ⧸ K) * Nat.card ↥K :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup K
        have h1 : Nat.card (G ⧸ K) * 2 ≤ Nat.card G := by
          rw [heq]; exact Nat.mul_le_mul_left _ hKnonbot_card
        have h2 : Nat.card G ≤ n + 1 := hcard
        omega
      -- Apply IH on G/K with Ā.
      have hIH : (Ā.normalCore.subgroupOf Ā).index < Ā.index :=
        ih hquot_card hĀ_proper hĀ_ab hĀ_cyc
      -- Apply Ch.2 K > ⊥ reduction lemma.
      exact OddOrder.Isaacs.Ch02.lucchini_K_pos_reduction hAprop hK_bot hIH

/-- **Isaacs Thm 2.20 (Lucchini) K = ⊥ case (private)**.

`G` 有限群, `A` cyclic abelian 真部分群, `K = core_G(A) = ⊥` ならば `|A| < |G:A|`.

`lucchini_aux` の K=⊥ specialization として derive. -/
private theorem lucchini_K_bot_aux [Finite G] {A : Subgroup G}
    (hA_proper : A < ⊤)
    (hA_ab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA_isCyclic : ∃ g : G, A = Subgroup.zpowers g)
    (hK_bot : A.normalCore = ⊥) :
    Nat.card ↥A < A.index := by
  have h := lucchini_aux (Nat.card G) le_rfl hA_proper hA_ab hA_isCyclic
  rwa [hK_bot, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h

/-- **Isaacs Thm 2.20 (Lucchini)**: `G` 有限群, `A` cyclic 真部分群, `K = core_G(A)`.
ならば `|A:K| < |G:A|`. 特に `|A| ≥ |G:A|` なら `K > 1`.

書籍 p.62-63 の証明 (induction on `|G|`):
* K > ⊥: G/K に IH 適用 (Ch.2 `lucchini_K_pos_reduction` 経由).
* K = ⊥: inline 実装 (Step 1-6).

**この定理は書籍上 Ch.2 だが, Lean 上は Ch.4 dir にいる** — K = ⊥ case が Ch.4 領域に
依存するため. owner chapter 規則による配置. 詳細は
[`notes/meta/forward_dep_policy.md`](../../../notes/meta/forward_dep_policy.md). -/
theorem lucchini_index_normalCore_lt_index [Finite G] {A : Subgroup G}
    (hA_proper : A < ⊤)
    (hA_ab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA_isCyclic : ∃ g : G, A = Subgroup.zpowers g) :
    (A.normalCore.subgroupOf A).index < A.index :=
  lucchini_aux (Nat.card G) le_rfl hA_proper hA_ab hA_isCyclic

end OddOrder.Isaacs.Ch04
