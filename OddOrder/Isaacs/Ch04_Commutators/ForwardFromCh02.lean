import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import OddOrder.GroupTheory.ElementaryAbelian
import OddOrder.Isaacs.Ch02_Subnormality

open scoped commutatorElement

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
`iterCommutator E F n ≤ (lowerCentralSeries (↥F) n).map F.subtype`.

特に `F` が冪零 (Group.IsNilpotent ↥F) なら, 十分大きな `n` で `lcs ↥F n = ⊥`,
よって `iterCommutator E F n = ⊥`. これが Lucchini K = ⊥ case の核心 (Z(F(G))
absorbs G-minimal). -/
theorem iterCommutator_le_lowerCentralSeries_map
    {E F : Subgroup G} (hE : E ≤ F) (n : ℕ) :
    iterCommutator E F n ≤ (lowerCentralSeries (↥F) n).map F.subtype := by
  induction n with
  | zero =>
    simp only [iterCommutator_zero, lowerCentralSeries_zero]
    rw [← MonoidHom.range_eq_map, F.range_subtype]
    exact hE
  | succ n ih =>
    rw [iterCommutator_succ]
    have hRange : (⊤ : Subgroup ↥F).map F.subtype = F := by
      rw [← MonoidHom.range_eq_map]; exact F.range_subtype
    have hMapLcs : (lowerCentralSeries (↥F) (n + 1)).map F.subtype =
        ⁅((lowerCentralSeries (↥F) n).map F.subtype), F⁆ := by
      change ⁅lowerCentralSeries (↥F) n, (⊤ : Subgroup ↥F)⁆.map F.subtype = _
      rw [Subgroup.map_commutator, hRange]
    rw [hMapLcs]
    exact Subgroup.commutator_mono ih le_rfl

/-- **iterCommutator は ambient G の lcs に押し込められる**: 任意 `E, F ⊆ G` で
`iterCommutator E F n ≤ lowerCentralSeries G n`. `E ≤ F` 不要 (E, F は ⊤ ≤ G で挟まれる).

`E ≤ ⊤` と `F ≤ ⊤` 経由で `iterCommutator E F n ≤ iterCommutator ⊤ ⊤ n = lcs G n`. -/
theorem iterCommutator_le_lowerCentralSeries (E F : Subgroup G) (n : ℕ) :
    iterCommutator E F n ≤ lowerCentralSeries G n := by
  induction n with
  | zero =>
    simp only [iterCommutator_zero, lowerCentralSeries_zero]
    exact le_top
  | succ n ih =>
    rw [iterCommutator_succ, lowerCentralSeries_succ]
    exact Subgroup.commutator_mono ih le_top

/-- **ambient G 冪零 ⇒ iterCommutator は最終的に ⊥** (任意 E, F).
`E ≤ F` 制約のない一般版 (上の `iterCommutator_eq_bot_of_isNilpotent` は `E ≤ F` 必要). -/
theorem iterCommutator_eq_bot_of_isNilpotent_ambient
    [Group.IsNilpotent G] (E F : Subgroup G) :
    ∃ n, iterCommutator E F n = ⊥ := by
  obtain ⟨n, hn⟩ := nilpotent_iff_lowerCentralSeries.mp ‹_›
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
  obtain ⟨n, hn⟩ := nilpotent_iff_lowerCentralSeries.mp hF
  refine ⟨n, le_antisymm ?_ bot_le⟩
  calc iterCommutator E F n
      ≤ (lowerCentralSeries (↥F) n).map F.subtype :=
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
        rw [mul_pow, ha, hb, one_mul]
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
    nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEle)
  -- E elem abelian p-group.
  obtain ⟨p, hp_prime, hElem⟩ :=
    isElementaryAbelian_of_isMinimalNormal_of_isNilpotent_subtype hMin
  refine ⟨E, p, hp_prime, hMin, hEle, ?_, hElem⟩
  exact le_centralizer_of_isMinimalNormal hMin hEle

/-! ## Lucchini K = ⊥ aux + 本体 -/

/-- **Isaacs Thm 2.20 (Lucchini) K = ⊥ case (private)**.

`G` 有限群, `A` cyclic abelian 真部分群, `K = core_G(A) = ⊥` ならば `|A| < |G:A|`.

これは Lucchini の核心部 (induction base). 証明 (Isaacs FGT p.62-63):
* Cor 2.19 で `A ∩ F(G) ≠ ⊥`, よって `F(G) ≠ ⊥`. minimal normal
  `E ⊆ F(G)`. さらに `E ⊆ Z(F(G))`, elementary abelian p-group.
* `AE < G` (E が `A ∩ F(G)` を中心化 → `A ∩ F(G) ⊴ AE`, K = ⊥ で contradict if AE = G).
* G/E に IH 適用 → `M = comap (Ā.normalCore)` で `|AE:M| < |G:AE|`.
* `B = A ∩ M` cyclic + 算術 ⇒ `|M:B| < |B|`.
* M abelian sub-case: `x ↦ x^p` hom + Dedekind M=EB + `φ(M) ⊴ G ⊆ A` + K = ⊥ ⇒ M = ⊥ ⇒ E = ⊥, 矛盾.
* M non-abelian sub-case: `Z(M)` cyclic + `B ∩ F(M) ⊴ G ⊆ A` nontrivial ⇒ K > ⊥, 矛盾.

**TODO** (issue #0001): 本体を実装中. 現状 `sorry`. -/
private theorem lucchini_K_bot_aux [Finite G] {A : Subgroup G}
    (_hA_proper : A < ⊤)
    (_hA_ab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (_hA_isCyclic : ∃ g : G, A = Subgroup.zpowers g)
    (_hK_bot : A.normalCore = ⊥) :
    Nat.card ↥A < A.index := by
  sorry

/-- **Lucchini `|G|`-induction wrapper** (private).
* K = ⊥ branch: `lucchini_K_bot_aux` (private theorem; was axiom, sorry-free 化中).
* K > ⊥ branch: Ch.2 `lucchini_K_pos_reduction` + IH on G/K. -/
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
    · -- K = ⊥ case: use narrower theorem (was axiom).
      have h_idx : (K.subgroupOf A).index = Nat.card ↥A := by
        rw [hK_bot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
      change (K.subgroupOf A).index < A.index
      rw [h_idx]
      exact lucchini_K_bot_aux hAprop hAab hAcyc hK_bot
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

/-- **Isaacs Thm 2.20 (Lucchini)**: `G` 有限群, `A` cyclic 真部分群, `K = core_G(A)`.
ならば `|A:K| < |G:A|`. 特に `|A| ≥ |G:A|` なら `K > 1`.

書籍 p.62-63 の証明 (induction on `|G|`):
* K > ⊥: G/K に IH 適用 (Ch.2 `lucchini_K_pos_reduction` 経由).
* K = ⊥: `lucchini_K_bot_aux` (private theorem; issue #0001 で sorry-free 化中).

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
