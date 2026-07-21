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

/-- `⁅⊥, H⁆ = ⊥`. -/
theorem commutator_bot_left_eq (H : Subgroup G) :
    (⁅(⊥ : Subgroup G), H⁆ : Subgroup G) = ⊥ := by
  refine le_bot_iff.mp ?_
  rw [commutator_le]
  intro g hg b _
  rw [Subgroup.mem_bot.mp hg]
  simp

/-- 生成元が pairwise 可換なら closure は abelian. -/
theorem isMulCommutative_closure_of_forall_commute {S : Set G}
    (h : ∀ a ∈ S, ∀ b ∈ S, Commute a b) : IsMulCommutative (closure S) := by
  rw [← le_centralizer_iff_isMulCommutative]
  have h1 : ∀ g ∈ S, closure S ≤ centralizer ({g} : Set G) := by
    intro g hg
    refine (closure_le _).mpr ?_
    intro a ha
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.mp hw]
    exact ((h a ha g hg).symm.eq)
  refine (closure_le _).mpr ?_
  intro g hg
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro m hm
  have h2 : m ∈ centralizer ({g} : Set G) := h1 g hg hm
  exact (mem_centralizer_iff.mp h2 g (Set.mem_singleton g)).symm

/-- **G Lem 2.5(ii) の半分** (element 形): `⁅k,α⁆` が `k` と可換なら
`⁅k⁻¹, α⁆ = ⁅k, α⁆⁻¹`. -/
theorem commutatorElement_inv_left_eq {k α : G} (h : Commute ⁅k, α⁆ k) :
    ⁅k⁻¹, α⁆ = ⁅k, α⁆⁻¹ := by
  have h1 : ⁅k⁻¹, α⁆ = k⁻¹ * ⁅k, α⁆⁻¹ * k := by group
  rw [h1, mul_assoc, show ⁅k, α⁆⁻¹ * k = k * ⁅k, α⁆⁻¹ from (h.inv_left.eq)]
  group

/-- `⁅e,α⁆` が `α` と可換なら `⁅α⁻¹, e⁆ = ⁅e, α⁆` (Gorenstein (2.15) の exact 半分). -/
theorem commutatorElement_inv_swap_eq {e α : G} (hcomm : Commute ⁅e, α⁆ α) :
    ⁅α⁻¹, e⁆ = ⁅e, α⁆ := by
  have h1 : ⁅α⁻¹, e⁆ = α⁻¹ * ⁅e, α⁆ * α := by group
  rw [h1, mul_assoc, show ⁅e, α⁆ * α = α * ⁅e, α⁆ from hcomm.eq]
  group

/-- **Case 2 の核心** (Gorenstein (2.11)-(2.19)): `B ⊴ G`, `B' ≤ Z(G)`, `A` abelian,
`[B,A;3] = ⊥` のとき, 奇数位数条件 (`g² = 1 ⟹ g = 1`) の下で
`⁅x,u⁆` と `⁅x,v⁆` は可換 (`x ∈ B`, `u v ∈ A`) — つまり `[x,A]` は abelian.

Step 1 で `z := ⁅⁅x,u⁆,⁅x,v⁆⁆ = ⁅⁅u⁻¹,⁅x,v⁆⁆,x⁆`; exact 変形で内側を
`⁅⁅x,v⁆,u⁆` に直し, 商 `G/B'` で 2.5(i) 対称性 (`commutatorElement_inv_rotate`)
から `⁅⁅x,v⁆,u⁆ ≡ ⁅⁅x,u⁆,v⁆ (mod B')`, 中心的誤差は `⁅·,x⁆` の左スロットで
吸収され `z = z⁻¹` ⟹ `z² = 1` ⟹ `z = 1`. -/
theorem case_two_commute {B A : Subgroup G} [B.Normal]
    (hB' : ⁅B, B⁆ ≤ center G) (hAcomm : IsMulCommutative A)
    (h3 : ⁅⁅⁅B, A⁆, A⁆, A⁆ = ⊥)
    (hodd : ∀ g : G, g ^ 2 = 1 → g = 1)
    {x u v : G} (hx : x ∈ B) (hu : u ∈ A) (hv : v ∈ A) :
    Commute ⁅x, u⁆ ⁅x, v⁆ := by
  haveI := hAcomm
  have hBc : ∀ g ∈ (⁅B, B⁆ : Subgroup G), ∀ w : G, g * w = w * g := fun g hg w =>
    (Subgroup.mem_center_iff.mp (hB' hg) w).symm
  have hmemB : ∀ b ∈ B, ∀ y : G, ⁅b, y⁆ ∈ B := by
    intro b hb y
    have h1 : y * b⁻¹ * y⁻¹ ∈ B := ‹B.Normal›.conj_mem _ (B.inv_mem hb) y
    have h2 : b * (y * b⁻¹ * y⁻¹) ∈ B := B.mul_mem hb h1
    rwa [show b * (y * b⁻¹ * y⁻¹) = ⁅b, y⁆ by group] at h2
  have hK2cent : (⁅⁅B, A⁆, A⁆ : Subgroup G) ≤ centralizer (A : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp h3
  -- exact 変形: ⁅u'⁻¹, ⁅x,v'⁆⁆ = ⁅⁅x,v'⁆, u'⁆
  have ha : ∀ u' ∈ A, ∀ v' ∈ A, ⁅u'⁻¹, ⁅x, v'⁆⁆ = ⁅⁅x, v'⁆, u'⁆ := by
    intro u' hu' v' hv'
    refine commutatorElement_inv_swap_eq ?_
    have hk2 : ⁅⁅x, v'⁆, u'⁆ ∈ (⁅⁅B, A⁆, A⁆ : Subgroup G) :=
      commutator_mem_commutator (commutator_mem_commutator hx hv') hu'
    exact ((mem_centralizer_iff.mp (hK2cent hk2) u' hu').symm)
  -- 商 Q = G/B' での対称性
  haveI hBcN : (⁅B, B⁆ : Subgroup G).Normal := normal_of_le_center' hB'
  set π := QuotientGroup.mk' (⁅B, B⁆ : Subgroup G) with hπdef
  have hQB : ∀ b₁ ∈ B, ∀ b₂ ∈ B, Commute (π b₁) (π b₂) := by
    intro b₁ hb₁ b₂ hb₂
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (commutator_mem_commutator hb₁ hb₂)
  have hQsym : π ⁅⁅x, v⁆, u⁆ = π ⁅⁅x, u⁆, v⁆ := by
    have hcv : Commute ⁅⁅π x, π v⁆, π u⁆ ⁅π x, π v⁆ := by
      have h1 := hQB _ (hmemB _ (hmemB x hx v) u) _ (hmemB x hx v)
      simpa only [map_commutatorElement] using h1
    have hcu : Commute ⁅⁅π x, π u⁆, π v⁆ ⁅π x, π u⁆ := by
      have h1 := hQB _ (hmemB _ (hmemB x hx u) v) _ (hmemB x hx u)
      simpa only [map_commutatorElement] using h1
    have hQvu : Commute (π v) (π u) := by
      have h1 : Commute v u := setLike_mul_comm hv hu
      exact h1.map π
    have hQxvxu : Commute ⁅π x, π v⁆ ⁅π x, π u⁆ := by
      have h1 := hQB _ (hmemB x hx v) _ (hmemB x hx u)
      simpa only [map_commutatorElement] using h1
    have hrot := commutatorElement_inv_rotate (x := π x) hQvu hQxvxu
    simp only [map_commutatorElement]
    calc ⁅⁅π x, π v⁆, π u⁆
        = (⁅⁅π x, π v⁆⁻¹, π u⁆)⁻¹ := by
          rw [commutatorElement_inv_left_eq hcv]; group
      _ = (⁅⁅π x, π u⁆⁻¹, π v⁆)⁻¹ := by rw [hrot]
      _ = ⁅⁅π x, π u⁆, π v⁆ := by
          rw [commutatorElement_inv_left_eq hcu]; group
  -- 引き戻し: 中心的誤差 z₀ を左スロットで吸収
  have hpull : ⁅⁅⁅x, v⁆, u⁆, x⁆ = ⁅⁅⁅x, u⁆, v⁆, x⁆ := by
    have hz0 : ⁅⁅x, v⁆, u⁆⁻¹ * ⁅⁅x, u⁆, v⁆ ∈ (⁅B, B⁆ : Subgroup G) := by
      have h1 : π (⁅⁅x, v⁆, u⁆⁻¹ * ⁅⁅x, u⁆, v⁆) = 1 := by
        rw [map_mul, map_inv, hQsym]
        group
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hz0c : ∀ w : G,
        (⁅⁅x, v⁆, u⁆⁻¹ * ⁅⁅x, u⁆, v⁆) * w = w * (⁅⁅x, v⁆, u⁆⁻¹ * ⁅⁅x, u⁆, v⁆) :=
      hBc _ hz0
    have hdecomp : ⁅⁅x, u⁆, v⁆
        = ⁅⁅x, v⁆, u⁆ * (⁅⁅x, v⁆, u⁆⁻¹ * ⁅⁅x, u⁆, v⁆) := by group
    conv_rhs => rw [hdecomp]
    rw [commutatorElement_central_left hz0c]
  -- Step 1 + 対称性 ⟹ z = z⁻¹ ⟹ z² = 1 ⟹ z = 1
  have hstep1uv := commutator_commutator_eq_of_normal hB' hx u v
  have hstep1vu := commutator_commutator_eq_of_normal hB' hx v u
  rw [ha u hu v hv] at hstep1uv
  rw [ha v hv u hu] at hstep1vu
  have hzinv : ⁅⁅x, u⁆, ⁅x, v⁆⁆⁻¹ = ⁅⁅x, u⁆, ⁅x, v⁆⁆ := by
    calc ⁅⁅x, u⁆, ⁅x, v⁆⁆⁻¹
        = ⁅⁅x, v⁆, ⁅x, u⁆⁆ := commutatorElement_inv _ _
      _ = ⁅⁅⁅x, u⁆, v⁆, x⁆ := hstep1vu
      _ = ⁅⁅⁅x, v⁆, u⁆, x⁆ := hpull.symm
      _ = ⁅⁅x, u⁆, ⁅x, v⁆⁆ := hstep1uv.symm
  have hsq : ⁅⁅x, u⁆, ⁅x, v⁆⁆ ^ 2 = 1 := by
    have h2 := congrArg (· * ⁅⁅x, u⁆, ⁅x, v⁆⁆) hzinv
    simp only [inv_mul_cancel] at h2
    rw [sq, ← h2]
  exact commutatorElement_eq_one_iff_commute.mp (hodd _ hsq)

open OddOrder.Isaacs.Ch04 in
/-- **Gorenstein Thm 2.7 Case 2** (`[B,A;n+1] = ⊥`): Lem 2.8(iii) と
`[B,A;2] ≠ ⊥` (Lem 2.3 の対偶) から `n = 2`, `[B,A;3] = ⊥`; Hall–Witt 論法
(`case_two_commute`) で全 `x ∈ B` の `[x,A]` が abelian になり, `x` を
`A` が `[x,A]` を中心化しないように選んで wrap-up (`R := ⁅B,A⁆`). -/
theorem glauberman_replacement_case_two [Finite G] {B A : Subgroup G} [B.Normal]
    (hsup : B ⊔ A = ⊤) (hB' : ⁅B, B⁆ ≤ center G)
    (hA : A ∈ maxAbelianIn (⊤ : Subgroup G))
    (hBnA : ¬ B ≤ normalizer (A : Set G))
    (hodd : ∀ g : G, g ^ 2 = 1 → g = 1)
    {n : ℕ} (hn_pos : 0 < n)
    (hmin : ∀ k, 0 < k → IsMulCommutative (iterCommutator B A k) → n ≤ k)
    (hcase : iterCommutator B A (n + 1) = ⊥) :
    ∃ A' ∈ maxAbelianIn (⊤ : Subgroup G),
      A ⊓ B < A' ⊓ B ∧ A' ≤ normalizer (A : Set G) := by
  obtain ⟨hn2, -⟩ :=
    iterCommutator_min_abelian_le_two hsup hB' hA.2.1 hn_pos hmin hcase
  have hiter2 : (⁅⁅B, A⁆, A⁆ : Subgroup G) = iterCommutator B A 2 := by
    rw [iterCommutator_succ, iterCommutator_succ, iterCommutator_zero]
  have h2ne : (⁅⁅B, A⁆, A⁆ : Subgroup G) ≠ ⊥ := by
    intro hbot
    refine hBnA ?_
    rw [le_normalizer_iff_commutator_commutator_eq_bot_of_mem_maxAbelianIn hA le_top]
    exact hbot
  have hn_eq : n = 2 := by
    rcases Nat.lt_or_ge n 2 with h | h
    · exfalso
      have hn1 : n = 1 := by omega
      subst hn1
      exact h2ne (by rw [hiter2]; exact hcase)
    · omega
  subst hn_eq
  have h3 : (⁅⁅⁅B, A⁆, A⁆, A⁆ : Subgroup G) = ⊥ := by
    have e : (⁅⁅⁅B, A⁆, A⁆, A⁆ : Subgroup G) = iterCommutator B A 3 := by
      rw [iterCommutator_succ, iterCommutator_succ, iterCommutator_succ,
        iterCommutator_zero]
    rw [e]
    exact hcase
  obtain ⟨x, hxB, hnc⟩ := exists_not_le_centralizer_elementCommutator
    (by rw [hiter2] at h2ne ⊢; exact h2ne)
  have hMcomm : IsMulCommutative (elementCommutator x A) := by
    refine isMulCommutative_closure_of_forall_commute ?_
    rintro - ⟨a, ha, rfl⟩ - ⟨b, hb, rfl⟩
    exact case_two_commute hB' hA.2.1 h3 hodd hxB ha hb
  have hMR : elementCommutator x A ≤ ⁅B, A⁆ := by
    refine (closure_le _).mpr ?_
    rintro m ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe]
    exact commutator_mem_commutator hxB ha
  exact replacement_of_elementCommutator hB' hA hxB hMcomm hnc hMR h3

open OddOrder.Isaacs.Ch04 in
/-- **Gorenstein Theorem 2.7 (Glauberman Replacement Theorem)** — core 形
(`P = AB` 簡約後の型レベル): `G` 有限冪零, `⊤ = B ⊔ A`, `B ⊴ G` with
`B' ≤ Z(G)`, `A ∈ A(G)`, `B` が `A` を正規化せず, 位数が奇 (`g² = 1 ⟹ g = 1`)
のとき, `A* ∈ A(G)` で `A ∩ B < A* ∩ B` かつ `A* ≤ N(A)`. -/
theorem glauberman_replacement_aux [Finite G] [Group.IsNilpotent G]
    {B A : Subgroup G} [B.Normal] (hsup : B ⊔ A = ⊤)
    (hB' : ⁅B, B⁆ ≤ center G) (hA : A ∈ maxAbelianIn (⊤ : Subgroup G))
    (hBnA : ¬ B ≤ normalizer (A : Set G))
    (hodd : ∀ g : G, g ^ 2 = 1 → g = 1) :
    ∃ A' ∈ maxAbelianIn (⊤ : Subgroup G),
      A ⊓ B < A' ⊓ B ∧ A' ≤ normalizer (A : Set G) := by
  classical
  have hex : ∃ k, 0 < k ∧ IsMulCommutative (iterCommutator B A k) := by
    obtain ⟨k, hk⟩ := iterCommutator_eq_bot_of_isNilpotent_ambient B A
    refine ⟨k + 1, Nat.succ_pos k, ?_⟩
    have hbot : iterCommutator B A (k + 1) = ⊥ := by
      rw [iterCommutator_succ, hk]
      exact commutator_bot_left_eq A
    rw [hbot]
    exact bot_isMulCommutative
  set n := Nat.find hex with hndef
  obtain ⟨hn_pos, hn_comm⟩ := Nat.find_spec hex
  have hmin : ∀ k, 0 < k → IsMulCommutative (iterCommutator B A k) → n ≤ k :=
    fun k hk hcomm => Nat.find_min' hex ⟨hk, hcomm⟩
  by_cases hcase : iterCommutator B A (n + 1) = ⊥
  · exact glauberman_replacement_case_two hsup hB' hA hBnA hodd hn_pos hmin hcase
  · exact glauberman_replacement_case_one hB' hA hn_pos hn_comm hcase

/-- normalizer の subgroupOf 転送: `X, Y ≤ Q` で `X.subgroupOf Q` が
`Y.subgroupOf Q` を正規化するなら ambient でも `X ≤ N(Y)`
(逆共役で `Q`-membership を回収する). -/
theorem le_normalizer_of_subgroupOf_le_normalizer {Q X Y : Subgroup G}
    (hXQ : X ≤ Q) (hYQ : Y ≤ Q)
    (h : X.subgroupOf Q ≤ normalizer ((Y.subgroupOf Q : Subgroup ↥Q) : Set ↥Q)) :
    X ≤ normalizer (Y : Set G) := by
  intro x hx
  have hxin : (⟨x, hXQ hx⟩ : ↥Q) ∈ X.subgroupOf Q := by
    rw [mem_subgroupOf]
    exact hx
  have hnorm := mem_normalizer_iff.mp (h hxin)
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have h1 := (hnorm ⟨a, hYQ ha⟩).mp (by rw [mem_subgroupOf]; exact ha)
    rw [mem_subgroupOf] at h1
    simpa using h1
  · intro ha
    have haQ : a ∈ Q := by
      have h1 : x⁻¹ * (x * a * x⁻¹) * x ∈ Q :=
        Q.mul_mem (Q.mul_mem (Q.inv_mem (hXQ hx)) (hYQ ha)) (hXQ hx)
      rwa [show x⁻¹ * (x * a * x⁻¹) * x = a by group] at h1
    have h2 := (hnorm ⟨a, haQ⟩).mpr (by rw [mem_subgroupOf]; simpa using ha)
    rw [mem_subgroupOf] at h2
    exact h2

open OddOrder.Isaacs.Ch04 in
/-- **Gorenstein Theorem 2.7 (Glauberman Replacement Theorem)** — subgroup-level:
`P` 有限 `p`-群 (`p` 奇素数), `B ⊴ P` (`P ≤ N(B)`) が class ≤ 2
(`⁅B,B⁆ ≤ C(B)`) かつ `B' ≤ Z(J_a(P))` (encoding
`⁅B,B⁆ ≤ C(J_a(P)) ⊓ J_a(P)`), `A ∈ A(P)` が `B` に正規化されないとき,
`A* ∈ A(P)` で `A ∩ B < A* ∩ B` かつ `A* ≤ N(A)` なるものが存在する.

`Q := A ⊔ B` に core (`glauberman_replacement_aux`) を instantiate する.
`B' ≤ Z(Q)` は `Z(J_a(P)) ≤ A` (Lem 2.1) と class ≤ 2 から. -/
theorem glauberman_replacement [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P B A : Subgroup G} (hP : IsPGroup p ↥P)
    (hBP : B ≤ P) (hPnB : P ≤ normalizer (B : Set G))
    (hclass2 : ⁅B, B⁆ ≤ centralizer (B : Set G))
    (hBZJ : ⁅B, B⁆ ≤ centralizer (thompsonJAbelian P : Set G) ⊓ thompsonJAbelian P)
    (hA : A ∈ maxAbelianIn P) (hBnA : ¬ B ≤ normalizer (A : Set G)) :
    ∃ A' ∈ maxAbelianIn P, A ⊓ B < A' ⊓ B ∧ A' ≤ normalizer (A : Set G) := by
  classical
  set Q := A ⊔ B with hQdef
  have hAQ : A ≤ Q := le_sup_left
  have hBQ : B ≤ Q := le_sup_right
  have hQP : Q ≤ P := sup_le hA.1 hBP
  -- `Z(J_a(P)) ≤ A` (Lem 2.1), ゆえに `B' ≤ A` と `Q ≤ C(B')`
  have hZJA : centralizer (thompsonJAbelian P : Set G) ⊓ thompsonJAbelian P ≤ A := by
    intro z hz
    refine (eq_inf_centralizer_of_mem_maxAbelianIn hA).ge ⟨?_, ?_⟩
    · exact (thompsonJAbelian_le P) hz.2
    · exact centralizer_le (SetLike.coe_subset_coe.mpr
        (le_thompsonJAbelian_of_mem_maxAbelianIn hA)) hz.1
  have hB'A : ⁅B, B⁆ ≤ A := hBZJ.trans hZJA
  have hQcentB' : Q ≤ centralizer ((⁅B, B⁆ : Subgroup G) : Set G) := by
    refine sup_le ?_ (le_centralizer_iff.mpr hclass2)
    exact le_centralizer_iff.mpr
      (hB'A.trans (le_centralizer_iff_isMulCommutative.mpr hA.2.1))
  -- ↥Q の instance 群
  have hpQ : IsPGroup p ↥Q :=
    (hP.to_subgroup (Q.subgroupOf P)).of_equiv (Subgroup.subgroupOfEquivOfLe hQP)
  haveI : Group.IsNilpotent ↥Q := hpQ.isNilpotent
  haveI hBinN : (B.subgroupOf Q).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hQP.trans hPnB)
  have hodd : ∀ g : ↥Q, g ^ 2 = 1 → g = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hpQ g
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, pow_zero] at hk
      exact orderOf_eq_one_iff.mp hk
    · exfalso
      have hpdvd : p ∣ orderOf g := hk ▸ dvd_pow_self p hpos.ne'
      have hdvd2 : p ∣ 2 := hpdvd.trans (orderOf_dvd_of_pow_eq_one hg)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd2)
  -- `⊤ = B-in ⊔ A-in`
  have htop : (⊤ : Subgroup ↥Q).map Q.subtype = Q := by
    rw [← MonoidHom.range_eq_map, Q.range_subtype]
  have hsupQ : B.subgroupOf Q ⊔ A.subgroupOf Q = ⊤ := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hBQ,
      Subgroup.map_subgroupOf_eq_of_le hAQ, htop]
    exact (sup_comm B A).trans hQdef.symm
  -- `B'-in ≤ Z(↥Q)`
  have hB'Q : ⁅B.subgroupOf Q, B.subgroupOf Q⁆ ≤ center ↥Q := by
    rw [commutator_le]
    intro b₁ hb₁ b₂ hb₂
    rw [Subgroup.mem_center_iff]
    intro q
    have hmem : ⁅(b₁ : G), (b₂ : G)⁆ ∈ (⁅B, B⁆ : Subgroup G) :=
      commutator_mem_commutator (mem_subgroupOf.mp hb₁) (mem_subgroupOf.mp hb₂)
    have hcomm : ⁅(b₁ : G), (b₂ : G)⁆ * (q : G) = (q : G) * ⁅(b₁ : G), (b₂ : G)⁆ :=
      mem_centralizer_iff.mp (hQcentB' q.2) _ hmem
    refine Subtype.ext ?_
    have hc1 : ((q * ⁅b₁, b₂⁆ : ↥Q) : G) = (q : G) * ⁅(b₁ : G), (b₂ : G)⁆ := by
      simp [commutatorElement_def]
    have hc2 : ((⁅b₁, b₂⁆ * q : ↥Q) : G) = ⁅(b₁ : G), (b₂ : G)⁆ * (q : G) := by
      simp [commutatorElement_def]
    rw [hc1, hc2, hcomm]
  -- `A-in ∈ A(⊤)`
  have hAin : A.subgroupOf Q ∈ maxAbelianIn (⊤ : Subgroup ↥Q) := by
    have h1 : A ∈ maxAbelianIn ((⊤ : Subgroup ↥Q).map Q.subtype) := by
      rw [htop]
      exact ⟨hAQ, hA.2.1, fun B₀ hB₀ hB₀c => hA.2.2 B₀ (hB₀.trans hQP) hB₀c⟩
    exact (comap_mem_maxAbelianIn_of_injective Q.subtype_injective h1).1
  -- `¬ B-in ≤ N(A-in)`
  have hBnAin : ¬ B.subgroupOf Q
      ≤ normalizer ((A.subgroupOf Q : Subgroup ↥Q) : Set ↥Q) := fun hle =>
    hBnA (le_normalizer_of_subgroupOf_le_normalizer hBQ hAQ hle)
  -- core 適用
  obtain ⟨A'in, hA'mem, hA'lt, hA'norm⟩ :=
    glauberman_replacement_aux hsupQ hB'Q hAin hBnAin hodd
  -- 引き上げ
  set A' := A'in.map Q.subtype with hA'def
  have hA'Q : A' ≤ Q := by
    rw [hA'def]
    exact (Subgroup.map_le_range _ _).trans (le_of_eq Q.range_subtype)
  have hA'in_eq : A'.subgroupOf Q = A'in := by
    rw [hA'def]
    exact Subgroup.comap_map_eq_self_of_injective Q.subtype_injective A'in
  have hA'P : A' ∈ maxAbelianIn P := by
    refine maxAbelianIn_subset_of_le hQP hA hAQ ?_
    have h1 := map_mem_maxAbelianIn_of_injective Q.subtype_injective
      (P := (⊤ : Subgroup ↥Q)) hA'mem
    rwa [htop] at h1
  -- inf の transport
  have hinf_eq : ∀ X : Subgroup G, X ≤ Q →
      X.subgroupOf Q ⊓ B.subgroupOf Q = (X ⊓ B).subgroupOf Q := by
    intro X hXQ
    ext g
    simp [mem_subgroupOf]
  have hAB : (A.subgroupOf Q ⊓ B.subgroupOf Q).map Q.subtype = A ⊓ B := by
    rw [hinf_eq A hAQ, Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hAQ)]
  have hA'B : (A'in ⊓ B.subgroupOf Q).map Q.subtype = A' ⊓ B := by
    rw [← hA'in_eq, hinf_eq A' hA'Q,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hA'Q)]
  refine ⟨A', hA'P, ?_, ?_⟩
  · have hmono : Monotone (Subgroup.map Q.subtype) := fun _ _ h => Subgroup.map_mono h
    have hsm : StrictMono (Subgroup.map Q.subtype) :=
      hmono.strictMono_of_injective (Subgroup.map_injective Q.subtype_injective)
    have hlt := hsm hA'lt
    rwa [hAB, hA'B] at hlt
  · refine le_normalizer_of_subgroupOf_le_normalizer hA'Q hAQ ?_
    rw [hA'in_eq]
    exact hA'norm

/-- **Gorenstein Theorem 2.9**: Thm 2.7 の仮定の下で, `B` が正規化する
`A ∈ A(P)` が存在する (`|A ⊓ B|` 最大の `A` を取れば replacement が適用不能). -/
theorem exists_mem_maxAbelianIn_normalizer_of_class_two [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {P B : Subgroup G} (hP : IsPGroup p ↥P)
    (hBP : B ≤ P) (hPnB : P ≤ normalizer (B : Set G))
    (hclass2 : ⁅B, B⁆ ≤ centralizer (B : Set G))
    (hBZJ : ⁅B, B⁆ ≤ centralizer (thompsonJAbelian P : Set G) ⊓ thompsonJAbelian P) :
    ∃ A ∈ maxAbelianIn P, B ≤ normalizer (A : Set G) := by
  classical
  obtain ⟨A, hAmem, hAmax⟩ := Set.exists_max_image (maxAbelianIn P)
    (fun A => Nat.card ↥(A ⊓ B))
    (Set.finite_univ.subset fun _ _ => Set.mem_univ _)
    (maxAbelianIn_nonempty P)
  refine ⟨A, hAmem, ?_⟩
  by_contra hBnA
  obtain ⟨A', hA'mem, hlt, -⟩ :=
    glauberman_replacement hp2 hP hBP hPnB hclass2 hBZJ hAmem hBnA
  have hle : Nat.card ↥(A' ⊓ B) ≤ Nat.card ↥(A ⊓ B) := hAmax A' hA'mem
  have hstrict : Nat.card ↥(A ⊓ B) < Nat.card ↥(A' ⊓ B) := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hlt.le) ?_
    intro heq
    exact hlt.ne (eq_of_le_of_card_ge hlt.le heq.ge)
  omega

end Subgroup




