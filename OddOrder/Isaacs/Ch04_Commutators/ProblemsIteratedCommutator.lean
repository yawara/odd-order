/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.Isaacs.Ch09_MoreSubnormality.NilpotentResidual

/-!
# Isaacs Chapter 4 — Problem 4A.9 (反復交換子系列と部分正規性)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4A.9 (書籍 p. 124)。

`G = NA` (`N ⊴ G`, `A ≤ G`) で `M` を系列 `N ⊇ ⁅N,A⁆ ⊇ ⁅N,A,A⁆ ⊇ ⋯` の最終項とすると

* **(a)** `A ◁◁ G` ⟺ `M ⊆ A`
* **(b)** `M ⊆ A` なら `M ⊆ A^∞`

⚠ (a) の左辺は **subnormal** (`⊲⊲`; PDF ページ画像で確認済) であって normal ではない。

## 方針

`⟸` は部分正規鎖 `A = L_k ⊔ A ≤ ⋯ ≤ L_1 ⊔ A ≤ L_0 ⊔ A = ⊤` を直接構成する
(`L_i` = `commIterate N A i`)。各段の正規性は `⁅H, K ⊔ L⁆` の分配 (**偽**) を避け,
normalizer に移して generator ごとに確かめる。

`⟹` は部分正規性の defect 版 `∃ d, ⁅⊤, A, …, A⁆ ≤ A`
(`exists_commIterate_top_le_of_isSubnormal`) を `IsSubnormal` の構造帰納で示し,
`M = ⁅M, A⁆` を `d` 回反復する。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

section /- Problem 4A.9: 反復交換子系列 (p. 124) -/

variable {G : Type*} [Group G]

/-! ### 反復交換子系列 `⁅N, A, …, A⁆` -/

/-- **反復交換子系列** `N ⊇ ⁅N,A⁆ ⊇ ⁅N,A,A⁆ ⊇ ⋯` の第 `i` 項 (Problem 4A.9)。

mathlib の `Subgroup.lowerCentralSeries` は始点と交換相手が同じ部分群だが,
こちらは始点 `N` と交換相手 `A` が別 (`Subgroup.lowerCentralSeries A = commIterate A A`)。 -/
def commIterate (N A : Subgroup G) : ℕ → Subgroup G
  | 0 => N
  | (i + 1) => ⁅commIterate N A i, A⁆

@[simp]
theorem commIterate_zero (N A : Subgroup G) : commIterate N A 0 = N := rfl

@[simp]
theorem commIterate_succ (N A : Subgroup G) (i : ℕ) :
    commIterate N A (i + 1) = ⁅commIterate N A i, A⁆ := rfl

theorem commIterate_mono_left {N N' : Subgroup G} (A : Subgroup G) (h : N ≤ N') (i : ℕ) :
    commIterate N A i ≤ commIterate N' A i := by
  induction i with
  | zero => exact h
  | succ i ih => exact Subgroup.commutator_mono ih le_rfl

theorem commIterate_mono_right (N : Subgroup G) {A A' : Subgroup G} (h : A ≤ A') (i : ℕ) :
    commIterate N A i ≤ commIterate N A' i := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact Subgroup.commutator_mono ih h

/-- `commIterate` は添字について加法的: `⁅N, A; i+j⁆ = ⁅⁅N, A; i⁆, A; j⁆`. -/
theorem commIterate_add (N A : Subgroup G) (i j : ℕ) :
    commIterate N A (i + j) = commIterate (commIterate N A i) A j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [← Nat.add_assoc, commIterate_succ, ih, commIterate_succ]

/-- `A ≤ N_G(N)` なら系列は `N` の中に留まる. -/
theorem commIterate_le_base {N A : Subgroup G} (hA : A ≤ Subgroup.normalizer (N : Set G))
    (i : ℕ) : commIterate N A i ≤ N := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    exact le_trans (Subgroup.commutator_mono ih le_rfl) (commutator_le_of_le_normalizer hA)

/-! ### `⁅H, K⁆` は両因子で正規化される -/

/-- 共役が片側の包含を保てば normalizer に入る (部分群なので `x⁻¹` で逆向きも出る). -/
theorem le_normalizer_of_forall_conj_mem {S T : Subgroup G}
    (h : ∀ x ∈ S, ∀ z ∈ T, x * z * x⁻¹ ∈ T) : S ≤ Subgroup.normalizer (T : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  refine fun z => ⟨fun hz => h x hx z hz, fun hz => ?_⟩
  have hz' := h x⁻¹ (S.inv_mem hx) _ hz
  have hcancel : x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z := by group
  rwa [hcancel] at hz'

/-- **`⁅H, K⁆` は左因子 `H` で正規化される**.

`⁅hx, y⁆ = h⁅x,y⁆h⁻¹ · ⁅h,y⁆` (`commutatorElement_mul_left_eq_conj_mul`) を
`h⁅x,y⁆h⁻¹ = ⁅hx,y⁆ · ⁅h,y⁆⁻¹` と読み替えると, `hx, h ∈ H` から右辺が `⁅H,K⁆` に入る. -/
theorem le_normalizer_commutator_left (H K : Subgroup G) :
    H ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  refine le_normalizer_of_forall_conj_mem fun h hh => ?_
  have hgen : (⁅H, K⁆ : Subgroup G)
      ≤ (⁅H, K⁆ : Subgroup G).comap (MulAut.conj h).toMonoidHom := by
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    rw [Subgroup.mem_comap]
    have happ : (MulAut.conj h).toMonoidHom ⁅x, y⁆ = ⁅h * x, y⁆ * ⁅h, y⁆⁻¹ := by
      change h * ⁅x, y⁆ * h⁻¹ = ⁅h * x, y⁆ * ⁅h, y⁆⁻¹
      simp only [commutatorElement_def]
      group
    rw [happ]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (H.mul_mem hh hx) hy)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hh hy))
  exact fun z hz => hgen hz

/-- **`⁅H, K⁆` は右因子 `K` でも正規化される** (`⁅H,K⁆ = ⁅K,H⁆` と左版). -/
theorem le_normalizer_commutator_right (H K : Subgroup G) :
    K ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.commutator_comm]
  exact le_normalizer_commutator_left K H

/-- `A` は系列の全項を正規化する (`i = 0` は仮定, `i ≥ 1` は交換子の右因子). -/
theorem le_normalizer_commIterate {N A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (N : Set G)) (i : ℕ) :
    A ≤ Subgroup.normalizer ((commIterate N A i : Subgroup G) : Set G) := by
  cases i with
  | zero => exact hA
  | succ i => exact le_normalizer_commutator_right _ _

/-- 系列は単調減少. -/
theorem commIterate_succ_le {N A : Subgroup G} (hA : A ≤ Subgroup.normalizer (N : Set G))
    (i : ℕ) : commIterate N A (i + 1) ≤ commIterate N A i :=
  commutator_le_of_le_normalizer (le_normalizer_commIterate hA i)

/-- **最終項 `M` の存在**: 有限群では減少列 `N ⊇ ⁅N,A⁆ ⊇ ⋯` は必ず安定する.

真に減るたびに位数が真に減るので, `|N|` 歩以内に停止する. -/
theorem exists_commIterate_stable [Finite G] {N A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (N : Set G)) :
    ∃ k, commIterate N A (k + 1) = commIterate N A k := by
  by_contra hcon
  have hne : ∀ k, commIterate N A (k + 1) ≠ commIterate N A k := fun k hk => hcon ⟨k, hk⟩
  have hstrict : ∀ k, ((commIterate N A (k + 1) : Subgroup G) : Set G).ncard
      < ((commIterate N A k : Subgroup G) : Set G).ncard := fun k =>
    Set.Finite.card_lt_card (Set.toFinite _)
      (SetLike.coe_ssubset_coe.mpr (lt_of_le_of_ne (commIterate_succ_le hA k) (hne k)))
  have hdec : ∀ k, ((commIterate N A k : Subgroup G) : Set G).ncard + k
      ≤ ((commIterate N A 0 : Subgroup G) : Set G).ncard := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => have := hstrict k; omega
  have hbig := hdec (((commIterate N A 0 : Subgroup G) : Set G).ncard + 1)
  have hpos : 0 < ((commIterate N A (((commIterate N A 0 : Subgroup G) : Set G).ncard + 1) :
      Subgroup G) : Set G).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨1, one_mem _⟩
  omega

/-! ### 系列の各段は部分正規段 -/

/-- **系列の各段が部分正規段**: `L_{i+1} ⊔ A ⊴ L_i ⊔ A` の normalizer 形.

`A` 側は `A ≤ W` から `⁅W, A⁆ ≤ ⁅W,W⁆ ≤ W`。`L_i` 側は generator ごとに:
`⁅L_i,A⁆` は `le_normalizer_commutator_left` で不変, `x a x⁻¹ = ⁅x,a⁆·a ∈ ⁅L_i,A⁆·A`。 -/
theorem sup_le_normalizer_commIterate_succ_sup (N A : Subgroup G) (i : ℕ) :
    commIterate N A i ⊔ A
      ≤ Subgroup.normalizer ((commIterate N A (i + 1) ⊔ A : Subgroup G) : Set G) := by
  set L := commIterate N A i with hL
  set W : Subgroup G := ⁅L, A⁆ ⊔ A with hW
  refine sup_le (le_normalizer_of_forall_conj_mem fun x hx => ?_) ?_
  · have hgen : W ≤ W.comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun w hw => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_comap]
        exact (le_sup_left : (⁅L, A⁆ : Subgroup G) ≤ W)
          (((Subgroup.mem_normalizer_iff.mp (le_normalizer_commutator_left L A hx)) w).mp hw)
      · rw [Subgroup.mem_comap]
        have happ : (MulAut.conj x).toMonoidHom a = ⁅x, a⁆ * a := by
          change x * a * x⁻¹ = ⁅x, a⁆ * a
          simp only [commutatorElement_def]
          group
        rw [happ]
        exact Subgroup.mul_mem _
          ((le_sup_left : (⁅L, A⁆ : Subgroup G) ≤ W) (Subgroup.commutator_mem_commutator hx ha))
          ((le_sup_right : A ≤ W) ha)
    exact fun z hz => hgen hz
  · refine le_normalizer_of_commutator_le ?_
    exact le_trans (Subgroup.commutator_mono le_rfl (le_sup_right : A ≤ W))
      (Subgroup.commutator_le_self W)

/-! ### Problem 4A.9(a) -/

/-- **4A.9(a) `⟸`**: 系列がいずれ `A` に入れば `A ◁◁ G`.

`⊤ = N ⊔ A = L_0 ⊔ A ▷ L_1 ⊔ A ▷ ⋯ ▷ L_k ⊔ A = A` が部分正規鎖. -/
theorem isSubnormal_sup_commIterate {N A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (N : Set G)) (hNA : N ⊔ A = ⊤) (j : ℕ) :
    (commIterate N A j ⊔ A).IsSubnormal := by
  induction j with
  | zero => exact hNA ▸ Subgroup.IsSubnormal.top
  | succ j ih =>
    have hle : commIterate N A (j + 1) ⊔ A ≤ commIterate N A j ⊔ A :=
      sup_le_sup_right (commIterate_succ_le hA j) A
    exact Subgroup.IsSubnormal.step _ _ hle ih
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
        (sup_le_normalizer_commIterate_succ_sup N A j))

/-- **4A.9(a) `⟸`** (主張の形): `⁅N,A;k⁆ ⊆ A` なら `A ◁◁ G`. -/
theorem isSubnormal_of_commIterate_le {N A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (N : Set G)) (hNA : N ⊔ A = ⊤) {k : ℕ}
    (hk : commIterate N A k ≤ A) : A.IsSubnormal := by
  have h := isSubnormal_sup_commIterate hA hNA k
  rwa [sup_eq_right.mpr hk] at h

/-- **部分正規性の defect 形**: `A ◁◁ G` なら `⁅⊤, A, …, A⁆ ≤ A` となる長さ `d` がある.

`IsSubnormal` の構造帰納. `A ⊴ K ◁◁ G` で `K` の defect `d` に対し
`⁅⊤,A;d⁆ ≤ ⁅⊤,K;d⁆ ≤ K` (第 2 引数の単調性) ゆえ `⁅⊤,A;d+1⁆ ≤ ⁅K,A⁆ ≤ A`. -/
theorem exists_commIterate_top_le_of_isSubnormal {A : Subgroup G} (h : A.IsSubnormal) :
    ∃ d : ℕ, commIterate ⊤ A d ≤ A := by
  induction h with
  | top => exact ⟨0, le_rfl⟩
  | step H K hle _ hN ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨d + 1, ?_⟩
    have hstep : commIterate (⊤ : Subgroup G) H d ≤ K :=
      le_trans (commIterate_mono_right ⊤ hle d) hd
    have hKH : (⁅K, H⁆ : Subgroup G) ≤ H := by
      rw [Subgroup.commutator_comm]
      exact commutator_le_of_le_normalizer
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN)
    exact le_trans (Subgroup.commutator_mono hstep le_rfl) hKH

/-- 系列が `k` で安定していれば, その先どこまで交換子を取っても変わらない. -/
theorem commIterate_stable {N A : Subgroup G} {k : ℕ}
    (hM : commIterate N A (k + 1) = commIterate N A k) (j : ℕ) :
    commIterate (commIterate N A k) A j = commIterate N A k := by
  induction j with
  | zero => rfl
  | succ j ih => rw [commIterate_succ, ih]; exact hM

/-- **4A.9(a) `⟹`**: `A ◁◁ G` なら系列の最終項 `M` は `A` に入る.

`M = ⁅M, A; d⁆ ≤ ⁅⊤, A; d⁆ ≤ A` (`d` は `A` の defect). -/
theorem commIterate_le_of_isSubnormal {N A : Subgroup G} (h : A.IsSubnormal) {k : ℕ}
    (hM : commIterate N A (k + 1) = commIterate N A k) : commIterate N A k ≤ A := by
  obtain ⟨d, hd⟩ := exists_commIterate_top_le_of_isSubnormal h
  calc commIterate N A k = commIterate (commIterate N A k) A d := (commIterate_stable hM d).symm
    _ ≤ commIterate ⊤ A d := commIterate_mono_left A le_top d
    _ ≤ A := hd

/-- **Isaacs Problem 4A.9(a)**: `G = NA` で `M` が系列 `N ⊇ ⁅N,A⁆ ⊇ ⋯` の最終項のとき

`A ◁◁ G ⟺ M ⊆ A`. -/
theorem isSubnormal_iff_commIterate_le {N A : Subgroup G} [hN : N.Normal] (hNA : N ⊔ A = ⊤)
    {k : ℕ} (hM : commIterate N A (k + 1) = commIterate N A k) :
    A.IsSubnormal ↔ commIterate N A k ≤ A :=
  ⟨fun h => commIterate_le_of_isSubnormal h hM,
    isSubnormal_of_commIterate_le
      (le_normalizer_of_commutator_le (Subgroup.commutator_le_left N A)) hNA⟩

/-! ### Problem 4A.9(b) -/

/-- **Isaacs Problem 4A.9(b)**: `M ⊆ A` なら `M ⊆ A^∞` (`A` の冪零剰余).

`M = ⁅M,A⁆` を反復すると `M ≤ ⁅A, A; i⁆ = A` の下降中心列の第 `i` 項 (∀ `i`), ゆえに交わりに入る. -/
theorem commIterate_le_nilpotentResidual {N A : Subgroup G} {k : ℕ}
    (hM : commIterate N A (k + 1) = commIterate N A k) (hk : commIterate N A k ≤ A) :
    commIterate N A k ≤ OddOrder.Isaacs.Ch09.nilpotentResidual A := by
  refine le_iInf fun i => ?_
  induction i with
  | zero => exact hk
  | succ i ih =>
    rw [Subgroup.lowerCentralSeries_succ, ← hM, commIterate_succ]
    exact Subgroup.commutator_mono ih le_rfl

end

end OddOrder.Isaacs.Ch04
