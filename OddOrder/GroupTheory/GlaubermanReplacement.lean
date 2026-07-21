/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.ThompsonSubgroupAbelian

/-!
# Glauberman Replacement Theorem (Gorenstein Thm 2.7)

Gorenstein, *Finite Groups* (1968), Ch.8 §2, **Theorem 2.7** (pp. 273-275):
`P` 有限 p-群 (p odd), `B ⊴ P` class ≤ 2 with `B' ≤ Z(J(P))`, `A ∈ A(P)` が
`B` に正規化されないとき, `A* ∈ A(P)` で `A ∩ B < A* ∩ B` かつ `A* ≤ N(A)` なる
ものが存在する。`ThompsonSubgroupAbelian.lean` (定義 + Lem 2.1-2.6, 2.8) の続き。
Issue 9403 (証明分解は同 issue の「Thm 2.7 の完全分解」節)。

## 実装状況

- `commutator_sup_le_of_centralizer` — 共通 wrap-up エンジン
  (`⁅M ⊔ C, Y⁆ ≤ T` の十分条件; `A* = M ⊔ C_A(M) ≤ N(A)` の核)。
- `exists_not_le_centralizer_elementCommutator` — `x` の選択補題
  (Case 1 の `x ∈ [B,A;r-3]`, Case 2 の `x ∈ B` に共通)。
- Case 1 / Case 2 本体と組立は後続 (issue 9403)。

p odd は Case 2 (`[[x,u],[x,v]]² = 1 ⟹ = 1`) でのみ使用 — `Odd (Nat.card G)`
の形で受ける (Gorenstein 自身が p = 2 でも `[B,A;3] ≠ 1` なら成立と注記)。
-/

namespace Subgroup

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

/-- **`A* ≤ N(A)` の核となる評価**: `C` が `M` と `Y` を中心化し, `⁅M,Y⁆ ≤ T` で
`C` が `T` を正規化するなら `⁅M ⊔ C, Y⁆ ≤ T`.

分解 `↑(C ⊔ M) = C·M` (中心化 ⟹ 正規化) の good-elements 計算:
`⁅cm, y⁆ = c ⁅m,y⁆ c⁻¹` (`⁅c,y⁆ = 1`) で, `T` の `c`-共役不変性から従う.
Gorenstein Thm 2.7 の `[A*,A] = [MC_A(M),A] ⊆ [B,A;r-1]` step の一般形. -/
theorem commutator_sup_le_of_centralizer {M C Y T : Subgroup G}
    (hCM : C ≤ centralizer (M : Set G)) (hCY : C ≤ centralizer (Y : Set G))
    (hMT : ⁅M, Y⁆ ≤ T) (hCT : C ≤ normalizer (T : Set G)) :
    ⁅M ⊔ C, Y⁆ ≤ T := by
  rw [commutator_le]
  intro g hg y hy
  have hCnormM : C ≤ normalizer (M : Set G) :=
    hCM.trans (centralizer_le_normalizer _)
  have hset : ((C ⊔ M : Subgroup G) : Set G) = (C : Set G) * (M : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right C M hCnormM
  have hg' : g ∈ (C : Set G) * (M : Set G) := by
    rw [← hset]
    have : g ∈ C ⊔ M := by rwa [sup_comm C M]
    exact this
  obtain ⟨c, hc, m, hm, heq⟩ := hg'
  subst heq
  have hcy : ⁅c, y⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr
    ((mem_centralizer_iff.mp (hCY hc) y hy).symm)
  have key : ⁅c * m, y⁆ = c * ⁅m, y⁆ * c⁻¹ * ⁅c, y⁆ := by group
  rw [key, hcy, mul_one]
  have hmT : ⁅m, y⁆ ∈ T := hMT (commutator_mem_commutator hm hy)
  exact (mem_normalizer_iff.mp (hCT hc) ⁅m, y⁆).mp hmT

/-- **`x` の選択補題** (Gorenstein Thm 2.7 Case 1/2 共通):
`⁅⁅X,A⁆,A⁆ ≠ ⊥` なら, `x ∈ X` で `A` が `[x,A]` を中心化しないものが存在する
(さもなくば `⁅X,A⁆` の全生成元が `A` に中心化される). -/
theorem exists_not_le_centralizer_elementCommutator {X A : Subgroup G}
    (h : ⁅⁅X, A⁆, A⁆ ≠ ⊥) :
    ∃ x ∈ X, ¬ (A ≤ centralizer (elementCommutator x A : Set G)) := by
  by_contra hall
  push Not at hall
  apply h
  rw [commutator_eq_bot_iff_le_centralizer, commutator_le]
  intro x hx a ha
  exact le_centralizer_iff.mp (hall x hx)
    (commutatorElement_mem_elementCommutator ha)

open OddOrder.Isaacs.Ch04 in
/-- **Thm 2.7 の共通 wrap-up** (Case 1/2 の合流点): `x ∈ B` で `M := [x,A]` が
abelian かつ `A` に中心化されず, `M ≤ R` で `⁅⁅R,A⁆,A⁆ = ⊥` なら,
`A* := M ⊔ C_A(M)` が Glauberman replacement の結論を満たす.

- `A* ∈ A(⊤)` は **Thm 2.4**; `A∩B ≤ C_A(M)` は three-subgroup lemma
  (`⁅B,A∩B⁆ ≤ B' ≤ Z` と `⁅A∩B,A⁆ ≤ ⁅A,A⁆ = ⊥` から `⁅⁅A,B⁆,A∩B⁆ = ⊥`);
- 真性 witness は `M ⊄ A` (さもなくば `A` abelian が `M` を中心化);
- `A* ≤ N(A)` は `⁅A*,A⁆ ≤ ⁅R,A⁆` (`commutator_sup_le_of_centralizer`) +
  `⁅⁅R,A⁆,A⁆ = ⊥` + **Lem 2.3**. -/
theorem replacement_of_elementCommutator [Finite G] {B A : Subgroup G} [B.Normal]
    (hB' : ⁅B, B⁆ ≤ center G) (hA : A ∈ maxAbelianIn (⊤ : Subgroup G))
    {x : G} (hxB : x ∈ B)
    (hMcomm : IsMulCommutative (elementCommutator x A))
    (hMnc : ¬ A ≤ centralizer (elementCommutator x A : Set G))
    {R : Subgroup G} (hMR : elementCommutator x A ≤ R)
    (h3 : ⁅⁅R, A⁆, A⁆ = ⊥) :
    ∃ A' ∈ maxAbelianIn (⊤ : Subgroup G),
      A ⊓ B < A' ⊓ B ∧ A' ≤ normalizer (A : Set G) := by
  set M := elementCommutator x A with hMdef
  set C := A ⊓ centralizer (M : Set G) with hCdef
  have hMBA : M ≤ ⁅B, A⁆ := by
    refine (closure_le _).mpr ?_
    rintro m ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe]
    exact commutator_mem_commutator hxB ha
  have hMB : M ≤ B := hMBA.trans (commutator_le_left B A)
  have hAstar := thompson_mem_maxAbelianIn hA (mem_top x) hMcomm
  refine ⟨M ⊔ C, hAstar, ?_, ?_⟩
  · rw [SetLike.lt_iff_le_and_exists]
    constructor
    · -- `A ⊓ B ≤ C` (three-subgroup lemma)
      have hAA : ⁅A, A⁆ = (⊥ : Subgroup G) :=
        commutator_eq_bot_iff_le_centralizer.mpr
          (le_centralizer_iff_isMulCommutative.mpr hA.2.1)
      have hthree : ⁅⁅A, B⁆, A ⊓ B⁆ = ⊥ := by
        refine commutator_commutator_eq_bot_of_rotate ?_ ?_
        · refine le_bot_iff.mp ?_
          calc ⁅⁅B, A ⊓ B⁆, A⁆
              ≤ ⁅⁅B, B⁆, A⁆ :=
                commutator_mono (commutator_mono le_rfl inf_le_right) le_rfl
            _ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
                (hB'.trans (center_le_centralizer _))
        · refine le_bot_iff.mp ?_
          calc ⁅⁅A ⊓ B, A⁆, B⁆
              ≤ ⁅⁅A, A⁆, B⁆ :=
                commutator_mono (commutator_mono inf_le_left le_rfl) le_rfl
            _ = ⁅(⊥ : Subgroup G), B⁆ := by rw [hAA]
            _ = ⊥ := by
                refine le_bot_iff.mp ?_
                rw [commutator_le]
                intro g hg b _
                rw [Subgroup.mem_bot.mp hg]
                simp
      have hABC : A ⊓ B ≤ C := by
        refine le_inf inf_le_left ?_
        have h5 : A ⊓ B ≤ centralizer ((⁅A, B⁆ : Subgroup G) : Set G) :=
          le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hthree)
        refine h5.trans (centralizer_le ?_)
        exact SetLike.coe_subset_coe.mpr
          (hMBA.trans (le_of_eq (commutator_comm B A)))
      exact le_inf (hABC.trans le_sup_right) inf_le_right
    · -- 真性 witness: `m ∈ M \ A`
      have hMnotA : ¬ M ≤ A := by
        intro hle
        exact hMnc ((le_centralizer_iff_isMulCommutative.mpr hA.2.1).trans
          (centralizer_le (SetLike.coe_subset_coe.mpr hle)))
      obtain ⟨m, hm, hmA⟩ := SetLike.not_le_iff_exists.mp hMnotA
      exact ⟨m, ⟨mem_sup_left hm, hMB hm⟩, fun hc => hmA hc.1⟩
  · -- `A* ≤ N(A)` (Lem 2.3)
    rw [le_normalizer_iff_commutator_commutator_eq_bot_of_mem_maxAbelianIn hA le_top]
    refine le_bot_iff.mp ?_
    have hstar : ⁅M ⊔ C, A⁆ ≤ ⁅R, A⁆ :=
      commutator_sup_le_of_centralizer inf_le_right
        (inf_le_left.trans (le_centralizer_iff_isMulCommutative.mpr hA.2.1))
        (commutator_mono hMR le_rfl)
        (inf_le_left.trans (le_normalizer_commutator_right R A))
    calc ⁅⁅M ⊔ C, A⁆, A⁆ ≤ ⁅⁅R, A⁆, A⁆ := commutator_mono hstar le_rfl
      _ = ⊥ := h3

open OddOrder.Isaacs.Ch04 in
/-- **Gorenstein Thm 2.7 Case 1** (`[B,A;n+1] ≠ ⊥`): `r` を最小の `[B,A;r] = ⊥`
とすると `r ≥ n + 2 ≥ 3` で, `x ∈ [B,A;r-3]` に `A` が `[x,A]` を中心化しない
ものがあり (さもなくば `[B,A;r-1] = ⊥`), `M = [x,A] ≤ [B,A;r-2] ≤ [B,A;n]` は
abelian. wrap-up (`R := [B,A;r-2]`, `⁅⁅R,A⁆,A⁆ = [B,A;r] = ⊥`) で結論. -/
theorem glauberman_replacement_case_one [Finite G] [Group.IsNilpotent G]
    {B A : Subgroup G} [B.Normal]
    (hB' : ⁅B, B⁆ ≤ center G) (hA : A ∈ maxAbelianIn (⊤ : Subgroup G))
    {n : ℕ} (hn_pos : 0 < n) (hn_comm : IsMulCommutative (iterCommutator B A n))
    (hcase : iterCommutator B A (n + 1) ≠ ⊥) :
    ∃ A' ∈ maxAbelianIn (⊤ : Subgroup G),
      A ⊓ B < A' ⊓ B ∧ A' ≤ normalizer (A : Set G) := by
  classical
  have hex : ∃ k, iterCommutator B A k = ⊥ :=
    iterCommutator_eq_bot_of_isNilpotent_ambient B A
  set r := Nat.find hex with hrdef
  have hrbot : iterCommutator B A r = ⊥ := Nat.find_spec hex
  have hrge : n + 2 ≤ r := by
    by_contra h
    push Not at h
    exact hcase (le_bot_iff.mp
      ((iterCommutator_le_of_le A (show r ≤ n + 1 by omega)).trans hrbot.le))
  have hchain : ⁅⁅iterCommutator B A (r - 3), A⁆, A⁆ = iterCommutator B A (r - 1) := by
    rw [← iterCommutator_succ, show r - 3 + 1 = r - 2 by omega,
      ← iterCommutator_succ, show r - 2 + 1 = r - 1 by omega]
  have hne : ⁅⁅iterCommutator B A (r - 3), A⁆, A⁆ ≠ ⊥ := by
    rw [hchain]
    exact Nat.find_min hex (show r - 1 < r by omega)
  obtain ⟨x, hxR3, hnc⟩ := exists_not_le_centralizer_elementCommutator hne
  have hMR : elementCommutator x A ≤ iterCommutator B A (r - 2) := by
    refine (closure_le _).mpr ?_
    rintro m ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, show r - 2 = (r - 3) + 1 by omega, iterCommutator_succ]
    exact commutator_mem_commutator hxR3 ha
  have hMcomm : IsMulCommutative (elementCommutator x A) :=
    isMulCommutative_of_le hn_comm
      (hMR.trans (iterCommutator_le_of_le A (show n ≤ r - 2 by omega)))
  have h3 : ⁅⁅iterCommutator B A (r - 2), A⁆, A⁆ = ⊥ := by
    rw [← iterCommutator_succ, show r - 2 + 1 = r - 1 by omega,
      ← iterCommutator_succ, show r - 1 + 1 = r by omega]
    exact hrbot
  exact replacement_of_elementCommutator hB' hA
    (iterCommutator_le_base A (r - 3) hxR3) hMcomm hnc hMR h3

/-! ### Case 2 (Gorenstein (2.11)-(2.19)) の element 部品

Hall–Witt 恒等式 (mathlib 慣習形, sympy 自由群で検証済) を `(a,b,c) := (u,x,⁅x,v⁆)`
に適用すると (2.11)-(2.14) が一撃で潰れる: 第 2 因子は内側が `B'` 中心的で 1,
第 3 因子は共役が落ち, 第 1 因子は `⁅⁅x,u⁆,⁅x,v⁆⁆⁻¹` に等しくなり,
`⁅⁅x,u⁆,⁅x,v⁆⁆ = ⁅⁅u⁻¹,⁅x,v⁆⁆, x⁆` が出る. -/

/-- **Hall–Witt 恒等式** (mathlib 慣習 `⁅a,b⁆ = aba⁻¹b⁻¹` での形; 自由恒等式). -/
theorem hall_witt_identity (a b c : G) :
    (b * ⁅⁅b⁻¹, a⁆, c⁆ * b⁻¹) * (c * ⁅⁅c⁻¹, b⁆, a⁆ * c⁻¹)
      * (a * ⁅⁅a⁻¹, c⁆, b⁆ * a⁻¹) = 1 := by
  group

/-- 中心元は右スロットで吸収される (element 形). -/
theorem commutatorElement_central_right {k y z : G} (hz : ∀ w : G, z * w = w * z) :
    ⁅k, y * z⁆ = ⁅k, y⁆ := by
  have h1 : z * k⁻¹ * z⁻¹ = k⁻¹ := by rw [hz k⁻¹]; group
  calc ⁅k, y * z⁆ = k * y * (z * k⁻¹ * z⁻¹) * y⁻¹ := by group
    _ = k * y * k⁻¹ * y⁻¹ := by rw [h1]
    _ = ⁅k, y⁆ := by group

/-- 中心元は左スロットで吸収される (element 形). -/
theorem commutatorElement_central_left {k y z : G} (hz : ∀ w : G, z * w = w * z) :
    ⁅k * z, y⁆ = ⁅k, y⁆ := by
  have h1 : z * y * z⁻¹ = y := by rw [hz y]; group
  calc ⁅k * z, y⁆ = k * (z * y * z⁻¹) * k⁻¹ * y⁻¹ := by group
    _ = ⁅k, y⁆ := by rw [h1]; group

/-- **Case 2 Step 1** (Gorenstein (2.11)-(2.14) 相当の一撃形): `B ⊴ G`,
`B' ≤ Z(G)`, `x ∈ B` のとき `⁅⁅x,u⁆, ⁅x,v⁆⁆ = ⁅⁅u⁻¹, ⁅x,v⁆⁆, x⁆` (`u, v` 任意).

Hall–Witt を `(a,b,c) := (u, x, ⁅x,v⁆)` に適用し, `B'`-中心性で 3 因子を潰す. -/
theorem commutator_commutator_eq_of_normal {B : Subgroup G} [B.Normal]
    (hB' : ⁅B, B⁆ ≤ center G) {x : G} (hx : x ∈ B) (u v : G) :
    ⁅⁅x, u⁆, ⁅x, v⁆⁆ = ⁅⁅u⁻¹, ⁅x, v⁆⁆, x⁆ := by
  have hBc : ∀ g ∈ (⁅B, B⁆ : Subgroup G), ∀ w : G, g * w = w * g := fun g hg w =>
    (Subgroup.mem_center_iff.mp (hB' hg) w).symm
  have hmemB : ∀ y : G, ⁅x, y⁆ ∈ B := by
    intro y
    have h1 : y * x⁻¹ * y⁻¹ ∈ B := ‹B.Normal›.conj_mem _ (B.inv_mem hx) y
    have h2 : x * (y * x⁻¹ * y⁻¹) ∈ B := B.mul_mem hx h1
    rwa [show x * (y * x⁻¹ * y⁻¹) = ⁅x, y⁆ by group] at h2
  have hd : ⁅x, v⁆ ∈ B := hmemB v
  have hc0 : ⁅x, u⁆ ∈ B := hmemB u
  have hE : ⁅u⁻¹, ⁅x, v⁆⁆ ∈ B := by
    have h1 : u⁻¹ * ⁅x, v⁆ * u ∈ B := by
      have h0 := ‹B.Normal›.conj_mem _ hd u⁻¹
      simpa using h0
    have h2 : (u⁻¹ * ⁅x, v⁆ * u) * ⁅x, v⁆⁻¹ ∈ B := B.mul_mem h1 (B.inv_mem hd)
    rwa [show (u⁻¹ * ⁅x, v⁆ * u) * ⁅x, v⁆⁻¹ = ⁅u⁻¹, ⁅x, v⁆⁆ by group] at h2
  have HW := hall_witt_identity (G := G) u x ⁅x, v⁆
  -- 第 2 因子 = 1
  have hf2 : ⁅⁅⁅x, v⁆⁻¹, x⁆, u⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr
      (hBc _ (commutator_mem_commutator (B.inv_mem hd) hx) u)
  -- 第 3 因子: 共役が落ちる
  have hf3 : u * ⁅⁅u⁻¹, ⁅x, v⁆⁆, x⁆ * u⁻¹ = ⁅⁅u⁻¹, ⁅x, v⁆⁆, x⁆ := by
    rw [show u * ⁅⁅u⁻¹, ⁅x, v⁆⁆, x⁆ = ⁅⁅u⁻¹, ⁅x, v⁆⁆, x⁆ * u from
      (hBc _ (commutator_mem_commutator hE hx) u).symm]
    group
  -- 第 1 因子 = ⁅⁅x,u⁆,⁅x,v⁆⁆⁻¹
  have hf1 : x * ⁅⁅x⁻¹, u⁆, ⁅x, v⁆⁆ * x⁻¹ = ⁅⁅x, u⁆, ⁅x, v⁆⁆⁻¹ := by
    have e1 : x * ⁅⁅x⁻¹, u⁆, ⁅x, v⁆⁆ * x⁻¹
        = ⁅⁅x, u⁆⁻¹, x * ⁅x, v⁆ * x⁻¹⁆ := by group
    have e2 : x * ⁅x, v⁆ * x⁻¹ = ⁅x, v⁆ * ⁅⁅x, v⁆⁻¹, x⁆ := by group
    have e3 : ⁅⁅x, u⁆⁻¹, ⁅x, v⁆ * ⁅⁅x, v⁆⁻¹, x⁆⁆ = ⁅⁅x, u⁆⁻¹, ⁅x, v⁆⁆ :=
      commutatorElement_central_right
        (hBc _ (commutator_mem_commutator (B.inv_mem hd) hx))
    have hzc : ∀ w : G, ⁅⁅x, u⁆, ⁅x, v⁆⁆⁻¹ * w = w * ⁅⁅x, u⁆, ⁅x, v⁆⁆⁻¹ :=
      hBc _ ((⁅B, B⁆ : Subgroup G).inv_mem (commutator_mem_commutator hc0 hd))
    have e4 : ⁅⁅x, u⁆⁻¹, ⁅x, v⁆⁆ = ⁅⁅x, u⁆, ⁅x, v⁆⁆⁻¹ := by
      have h1 : ⁅⁅x, u⁆⁻¹, ⁅x, v⁆⁆
          = ⁅x, u⁆⁻¹ * ⁅⁅x, u⁆, ⁅x, v⁆⁆⁻¹ * ⁅x, u⁆ := by group
      rw [h1, mul_assoc, hzc ⁅x, u⁆]
      group
    rw [e1, e2, e3, e4]
  rw [hf2, hf1, hf3] at HW
  -- HW : ⁅⁅x,u⁆,⁅x,v⁆⁆⁻¹ * (⁅x,v⁆ * 1 * ⁅x,v⁆⁻¹) * ⁅⁅u⁻¹,⁅x,v⁆⁆,x⁆ = 1
  have h2 : ⁅⁅x, u⁆, ⁅x, v⁆⁆⁻¹ * ⁅⁅u⁻¹, ⁅x, v⁆⁆, x⁆ = 1 := by
    calc ⁅⁅x, u⁆, ⁅x, v⁆⁆⁻¹ * ⁅⁅u⁻¹, ⁅x, v⁆⁆, x⁆
        = ⁅⁅x, u⁆, ⁅x, v⁆⁆⁻¹ * (⁅x, v⁆ * 1 * ⁅x, v⁆⁻¹)
          * ⁅⁅u⁻¹, ⁅x, v⁆⁆, x⁆ := by group
      _ = 1 := HW
  calc ⁅⁅x, u⁆, ⁅x, v⁆⁆
      = ⁅⁅x, u⁆, ⁅x, v⁆⁆ * (⁅⁅x, u⁆, ⁅x, v⁆⁆⁻¹ * ⁅⁅u⁻¹, ⁅x, v⁆⁆, x⁆) := by
        rw [h2, mul_one]
    _ = ⁅⁅u⁻¹, ⁅x, v⁆⁆, x⁆ := by group

end Subgroup
