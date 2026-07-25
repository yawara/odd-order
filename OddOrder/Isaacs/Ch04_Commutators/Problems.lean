/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.GroupTheory.IsExtraspecial

/-!
# Isaacs Chapter 4 — Problems §4A (Commutators)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 4 "Commutators" の章末演習 §4A
(pp. 123-125)。

方針は Ch.1-Ch.3 の `Problems*.lean` と同じ (ラッパーは書かず実証明; 教科書番号は docstring)。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

universe u

section /- Problems 4A: commutators (pp. 123-125) -/

/-! ### Problem 4A.1 — `G = AB` (`A`, `B` abelian) なら `G' = ⁅A, B⁆` -/

/-- **Isaacs Problem 4A.1** (書籍 p. 123): `G = AB` で `A`, `B` が abelian な部分群なら
`G' = ⁅A, B⁆`.

`⁅A, B⁆` は `A` と `B` の両方に正規化されるので `A ⊔ B = ⊤` から `G` で正規
(Lem 4.1 系 `commutator_normal_of_sup_eq_top`). 商 `G / ⁅A, B⁆` では `A` の像と `B` の像が
可換で, どちらも abelian, かつ `G = AB` より全体を覆うので商は abelian, したがって
`G' ≤ ⁅A, B⁆`. 逆向きは自明. -/
theorem commutator_eq_commutator_of_mul_eq_top {G : Type*} [Group G] {A B : Subgroup G}
    [hA : IsMulCommutative A] [hB : IsMulCommutative B] (hsup : A ⊔ B = ⊤)
    (hprod : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, a * b = g) :
    commutator G = ⁅A, B⁆ := by
  haveI hnormal : (⁅A, B⁆ : Subgroup G).Normal := commutator_normal_of_sup_eq_top hsup
  refine le_antisymm ?_ (Subgroup.commutator_mono le_top le_top)
  refine Subgroup.Normal.quotient_commutative_iff_commutator_le.mp ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hprod x
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hprod y
  -- 商では `A` の像と `B` の像が可換 (`⁅B, A⁆ = ⁅A, B⁆` が消えるから).
  have hab : ∀ a ∈ A, ∀ b ∈ B,
      Commute (QuotientGroup.mk a : G ⧸ (⁅A, B⁆ : Subgroup G)) (QuotientGroup.mk b) := by
    intro a ha b hb
    have hmem : (a * b)⁻¹ * (b * a) ∈ (⁅A, B⁆ : Subgroup G) := by
      have heq : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [heq, ← Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (B.inv_mem hb) (A.inv_mem ha)
    have : (QuotientGroup.mk (a * b) : G ⧸ (⁅A, B⁆ : Subgroup G)) = QuotientGroup.mk (b * a) :=
      (QuotientGroup.eq).mpr hmem
    simpa [Commute, SemiconjBy, QuotientGroup.mk_mul] using this
  -- `A`, `B` はそれぞれ abelian.
  have haa : ∀ a ∈ A, ∀ a' ∈ A,
      Commute (QuotientGroup.mk a : G ⧸ (⁅A, B⁆ : Subgroup G)) (QuotientGroup.mk a') := by
    intro a ha a' ha'
    have : a * a' = a' * a := congrArg Subtype.val (hA.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨a', ha'⟩)
    simpa [Commute, SemiconjBy, ← QuotientGroup.mk_mul] using congrArg
      (QuotientGroup.mk (s := (⁅A, B⁆ : Subgroup G))) this
  have hbb : ∀ b ∈ B, ∀ b' ∈ B,
      Commute (QuotientGroup.mk b : G ⧸ (⁅A, B⁆ : Subgroup G)) (QuotientGroup.mk b') := by
    intro b hb b' hb'
    have : b * b' = b' * b := congrArg Subtype.val (hB.is_comm.comm (⟨b, hb⟩ : ↥B) ⟨b', hb'⟩)
    simpa [Commute, SemiconjBy, ← QuotientGroup.mk_mul] using congrArg
      (QuotientGroup.mk (s := (⁅A, B⁆ : Subgroup G))) this
  -- `mk (a₁b₁)` と `mk (a₂b₂)` は可換.
  have hkey : Commute ((QuotientGroup.mk a₁ : G ⧸ (⁅A, B⁆ : Subgroup G)) * QuotientGroup.mk b₁)
      ((QuotientGroup.mk a₂ : G ⧸ (⁅A, B⁆ : Subgroup G)) * QuotientGroup.mk b₂) :=
    Commute.mul_left (Commute.mul_right (haa a₁ ha₁ a₂ ha₂) (hab a₁ ha₁ b₂ hb₂))
      (Commute.mul_right (hab a₂ ha₂ b₁ hb₁).symm (hbb b₁ hb₁ b₂ hb₂))
  simpa [QuotientGroup.mk_mul] using hkey.eq

/-! ### Problem 4A.4 — extraspecial なら `P / Z(P)` は elementary abelian -/

/-- 類 2 の群 (`G' ≤ Z(G)`) では `⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n`. -/
theorem commutatorElement_pow_left_of_commutator_le_center {G : Type*} [Group G]
    (h : commutator G ≤ Subgroup.center G) (x y : G) (n : ℕ) : ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  have hcen : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.center G := fun a b =>
    h (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  induction n with
  | zero => simp
  | succ n ih =>
    have hx : x ^ (n + 1) = x ^ n * x := pow_succ x n
    rw [hx, commutatorElement_mul_left_eq_conj_mul, ih]
    have hc : x ^ n * ⁅x, y⁆ * (x ^ n)⁻¹ = ⁅x, y⁆ := by
      have hcm := Subgroup.mem_center_iff.mp (hcen x y) (x ^ n)
      rw [hcm]
      group
    rw [hc, pow_succ']

/-- **Isaacs Problem 4A.4** (書籍 p. 123): `P` が extraspecial (`P' = Z(P)` かつ `|Z(P)| = p`)
なら `P / Z(P)` は **elementary abelian**.

`P' = Z(P)` から商は abelian, さらに類 2 なので `⁅x^p, y⁆ = ⁅x, y⁆^p` で,
`⁅x, y⁆ ∈ Z(P)` の位数は `p` を割るから `⁅x^p, y⁆ = 1`, すなわち `x^p ∈ Z(P)`.
⟹ 商は指数 `p` の abelian 群.

書籍が併記する「同値な形 `Z(P) = P' = Φ(P)`」のうち `Φ(P) ≤ Z(P)` は `p`-群での
`Φ(P) = P' P^p` (⊆ 方向) が要る — repo には現在 ⊇ 方向
(`commutator_sup_pow_closure_le_frattini`) しか無いので, ここでは本問の主形
「`P/Z(P)` が elementary abelian」を形式化する.

⚠ `p` の素数性はこの向きには不要 (`|Z(P)| = p` から `Z(P)` の元の位数が `p` を割ることしか
使わない) ので仮定していない. -/
theorem isElementaryAbelian_quotient_center_of_commutator_eq_center {p : ℕ}
    {P : Type*} [Group P] [Finite P] (hcomm : commutator P = Subgroup.center P)
    (hcard : Nat.card (Subgroup.center P) = p) :
    OddOrder.GroupTheory.IsElementaryAbelian p (P ⧸ Subgroup.center P) := by
  have hle : commutator P ≤ Subgroup.center P := le_of_eq hcomm
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · -- abelian: `P' ≤ Z(P)`.
    haveI : IsMulCommutative (P ⧸ Subgroup.center P) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hle
    exact (IsMulCommutative.is_comm (M := P ⧸ Subgroup.center P)).comm x y
  · -- 指数 `p`: `x^p ∈ Z(P)`.
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    have hcompow : ⁅g ^ p, y⁆ = ⁅g, y⁆ ^ p :=
      commutatorElement_pow_left_of_commutator_le_center hle g y p
    have hmem : ⁅g, y⁆ ∈ Subgroup.center P :=
      hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top y))
    have hone : ⁅g, y⁆ ^ p = 1 := by
      have hdvd : orderOf (⟨⁅g, y⁆, hmem⟩ : ↥(Subgroup.center P)) ∣ p := by
        rw [← hcard]
        exact orderOf_dvd_natCard _
      have : (⟨⁅g, y⁆, hmem⟩ : ↥(Subgroup.center P)) ^ p = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp hdvd
      exact congrArg Subtype.val this
    rw [hone] at hcompow
    exact (commutatorElement_eq_one_iff_commute.mp hcompow).symm

end

end OddOrder.Isaacs.Ch04
