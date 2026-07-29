/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.Schenkman

/-!
# Isaacs §10A の演習 (書籍 pp. 307-308)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 10A。

* **10A.1** `isRegularPGroup_two_iff_commute` — **2-群は regular ⟺ 可換**。

## regular `p`-群の定義について

Isaacs は p. 297 で「`p`-群 `P` が **regular** とは, 任意の `x, y ∈ P` に対し
`⟨x, y⟩` の導来部分群の元 `c` があって `(xy)^p = x^p y^p c^p` となること」と定義する
(`C_p ≀ C_p` が準同型像にならないための十分条件として導入される)。定義と statement は
ページ画像 `references/isaacs/pages/isaacs-p297-310.png` / `isaacs-p308-321.png` で確定。

導来部分群は subtype を避けて ambient の `⁅⟨x,y⟩, ⟨x,y⟩⁆` で書く。

## 10A.1 の証明

`⟸` は可換なら `c = 1` で済む。`⟹` は書籍 hint どおり `|P|` の極小反例:

* regular 性は**商に遺伝する** (`IsRegularPGroup.quotient`)。よって極小反例 `P` の真の商は
  すべて可換 ⟹ `P' ≤ N` (すべての非自明な `N ◁ P`)。
* `P' ≠ 1` (`P` 非可換) と `P` 冪零から `P' ⊓ Z(P) ≠ 1`。`1 ≠ z` をそこから取ると
  `⟨z⟩ ◁ P` (中心的) なので `P' ≤ ⟨z⟩`。さらに `z² ≠ 1` なら `P' ≤ ⟨z²⟩` から
  `z ∈ ⟨z²⟩`, すなわち `⟨z⟩ = ⟨z²⟩` となり位数が半分になって矛盾 ⟹ **`z² = 1`**。
  ゆえに `P'` の元はすべて中心的で 2 乗すると `1`。
* `⁅x, y⁆ ≠ 1` なる `x, y` について, 類 2 の恒等式から `(xy)² = ⁅y,x⁆ x² y²`。一方
  regular 性の `c` は `⟨x,y⟩' ≤ P'` にあるので `c² = 1`, つまり `(xy)² = x² y²`。
  合わせて `⁅y,x⁆ = 1` となり矛盾。
-/

namespace OddOrder.Isaacs.Ch10

open Subgroup

open scoped commutatorElement

variable {P : Type*} [Group P]

section /- 10A.1: 2-群は regular ⟺ 可換 (p. 308) -/

/-- **regular `p`-群** (Isaacs p. 297): 任意の `x, y` に対し `⟨x, y⟩` の導来部分群の元 `c`
で `(xy)^p = x^p y^p c^p` となるものが存在する。

Isaacs はこれを「`C_p ≀ C_p` が準同型像にならない」ための十分条件として導入する。 -/
def IsRegularPGroup (p : ℕ) (P : Type*) [Group P] : Prop :=
  ∀ x y : P, ∃ c ∈ ⁅Subgroup.closure ({x, y} : Set P), Subgroup.closure ({x, y} : Set P)⁆,
    (x * y) ^ p = x ^ p * y ^ p * c ^ p

/-- 可換群は (任意の `p` について) regular (`c = 1` でよい)。 -/
theorem isRegularPGroup_of_commute (p : ℕ) (h : ∀ x y : P, x * y = y * x) :
    IsRegularPGroup p P := fun x y =>
  ⟨1, one_mem _, by rw [one_pow, mul_one]; exact Commute.mul_pow (h x y) p⟩

/-- **regular 性は商に遺伝する**: `⟨x, y⟩'` の像は `⟨x̄, ȳ⟩'` に入るので, 持ち上げた `c` の
像がそのまま使える。 -/
theorem IsRegularPGroup.quotient {p : ℕ} (hP : IsRegularPGroup p P) (N : Subgroup P)
    [N.Normal] : IsRegularPGroup p (P ⧸ N) := by
  intro u v
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
  obtain ⟨c, hc, hcpow⟩ := hP x y
  refine ⟨(c : P ⧸ N), ?_, ?_⟩
  · have hmap : (Subgroup.closure ({x, y} : Set P)).map (QuotientGroup.mk' N)
        = Subgroup.closure ({(x : P ⧸ N), (y : P ⧸ N)} : Set (P ⧸ N)) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext z
      simp [Set.mem_image, eq_comm]
    have hle := Subgroup.map_commutator (H₁ := Subgroup.closure ({x, y} : Set P))
      (H₂ := Subgroup.closure ({x, y} : Set P)) (QuotientGroup.mk' N)
    rw [hmap] at hle
    exact hle ▸ Subgroup.mem_map_of_mem _ hc
  · have h := congrArg (QuotientGroup.mk' N) hcpow
    simpa using h

/-- 中心に含まれる部分群は正規。 -/
private theorem normal_of_le_center {H : Subgroup P} (h : H ≤ Subgroup.center P) : H.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hc := Subgroup.mem_center_iff.mp (h hn) g
  have hrw : g * n * g⁻¹ = n := by rw [hc]; group
  rw [hrw]
  exact hn

/-- **10A.1 の核**: 極小反例の 2-群では `P'` の元は中心的で 2 乗が `1`。 -/
private theorem commutator_sq_eq_one_of_quotient_commutative {P : Type*} [Group P] [Finite P]
    (hp : IsPGroup 2 P) (hquot : ∀ N : Subgroup P, N.Normal → N ≠ ⊥ → commutator P ≤ N)
    (hncomm : commutator P ≠ ⊥) :
    ∀ c ∈ commutator P, c ^ 2 = 1 ∧ c ∈ Subgroup.center P := by
  haveI : Group.IsNilpotent P := hp.isNilpotent
  -- `P' ⊓ Z(P) ≠ 1` から中心的な `z ≠ 1` を取る
  have hcz := Ch09.inf_center_ne_bot_of_normal_of_isNilpotent (K := commutator P) hncomm
  haveI : Nontrivial ↥(commutator P ⊓ Subgroup.center P) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hcz
  obtain ⟨w, hwne⟩ := exists_ne (1 : ↥(commutator P ⊓ Subgroup.center P))
  obtain ⟨z, hzmem⟩ := w
  have hz1 : z ≠ 1 := fun h => hwne (Subtype.ext h)
  have hzc : z ∈ Subgroup.center P := hzmem.2
  haveI : (Subgroup.zpowers z).Normal := normal_of_le_center (Subgroup.zpowers_le.mpr hzc)
  have hPz : commutator P ≤ Subgroup.zpowers z := by
    refine hquot _ inferInstance fun h => hz1 ?_
    have hm := Subgroup.mem_zpowers z
    rw [h, Subgroup.mem_bot] at hm
    exact hm
  -- `z ^ 2 = 1`
  have hz2 : z ^ 2 = 1 := by
    by_contra hne
    haveI : (Subgroup.zpowers (z ^ 2)).Normal :=
      normal_of_le_center (Subgroup.zpowers_le.mpr (pow_mem hzc 2))
    have hz2le : commutator P ≤ Subgroup.zpowers (z ^ 2) := by
      refine hquot _ inferInstance fun h => hne ?_
      have hm := Subgroup.mem_zpowers (z ^ 2)
      rw [h, Subgroup.mem_bot] at hm
      exact hm
    have hmem : z ∈ Subgroup.zpowers (z ^ 2) := hz2le hzmem.1
    -- `⟨z⟩ = ⟨z²⟩` なので位数が等しいが, 2-群では `orderOf (z²) = orderOf z / 2`
    have heq : Subgroup.zpowers (z ^ 2) = Subgroup.zpowers z :=
      le_antisymm (Subgroup.zpowers_le.mpr (pow_mem (Subgroup.mem_zpowers z) 2))
        (Subgroup.zpowers_le.mpr hmem)
    have hcard : orderOf (z ^ 2) = orderOf z := by
      rw [← Nat.card_zpowers, ← Nat.card_zpowers, heq]
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hp z
    have hjpos : j ≠ 0 := fun h0 => hz1 (orderOf_eq_one_iff.mp (by rw [hj, h0, pow_zero]))
    have h2dvd : 2 ∣ orderOf z := by rw [hj]; exact dvd_pow_self 2 hjpos
    have hpos : 0 < orderOf z := orderOf_pos z
    have hkill : (z ^ 2) ^ (orderOf z / 2) = 1 := by
      rw [← pow_mul, Nat.mul_div_cancel' h2dvd, pow_orderOf_eq_one]
    have hdvd := orderOf_dvd_of_pow_eq_one hkill
    rw [hcard] at hdvd
    have hle := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hpos h2dvd) two_pos) hdvd
    omega
  refine fun c hc => ⟨?_, ?_⟩
  · obtain ⟨m, rfl⟩ := hPz hc
    rw [← zpow_natCast (z ^ m) 2, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
  · obtain ⟨m, rfl⟩ := hPz hc
    exact zpow_mem hzc m

/-- 10A.1 の帰納核: `Nat.card P ≤ n` の 2-群が regular なら可換。 -/
private theorem commute_of_isRegularPGroup_two_aux.{u} (n : ℕ) :
    ∀ (P : Type u) [Group P] [Finite P], Nat.card P ≤ n → IsPGroup 2 P →
      IsRegularPGroup 2 P → ∀ x y : P, x * y = y * x := by
  induction n with
  | zero =>
    intro P _ _ hcard
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ n IH =>
    intro P _ _ hcard hp hreg x y
    by_contra hxy
    -- 真の商はすべて可換 ⟹ `P' ≤ N`
    have hquot : ∀ N : Subgroup P, N.Normal → N ≠ ⊥ → commutator P ≤ N := by
      intro N hN hNbot
      haveI := hN
      refine Subgroup.Normal.quotient_commutative_iff_commutator_le.mp ⟨⟨fun a b => ?_⟩⟩
      have hsmall : Nat.card (P ⧸ N) ≤ n := by
        have hmul := Subgroup.card_mul_index N
        have hidx : N.index = Nat.card (P ⧸ N) := (Subgroup.index_eq_card N).symm
        have h2 : 2 ≤ Nat.card ↥N := by
          have h1 : Nat.card ↥N ≠ 1 := fun h => hNbot (Subgroup.card_eq_one.mp h)
          have := Nat.card_pos (α := ↥N)
          omega
        have hqpos : 0 < Nat.card (P ⧸ N) := Nat.card_pos
        rw [hidx] at hmul
        have hbound : 2 * Nat.card (P ⧸ N) ≤ Nat.card P := by
          rw [← hmul]
          exact Nat.mul_le_mul_right _ h2
        omega
      exact IH (P ⧸ N) hsmall (hp.to_quotient N) (hreg.quotient N) a b
    -- `P` 非可換
    have hncomm : commutator P ≠ ⊥ := by
      intro hbot
      refine hxy (commutatorElement_eq_one_iff_commute.mp ?_)
      have : ⁅x, y⁆ ∈ commutator P :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have hkey := commutator_sq_eq_one_of_quotient_commutative hp hquot hncomm
    -- 類 2 の恒等式: `(xy)² = ⁅y,x⁆ x² y²`
    have hyx : ⁅y, x⁆ ∈ commutator P :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x)
    have hcen : ⁅y, x⁆ ∈ Subgroup.center P := (hkey _ hyx).2
    have hclass2 : (x * y) ^ 2 = ⁅y, x⁆ * x ^ 2 * y ^ 2 := by
      have hcx : ⁅y, x⁆ * x = x * ⁅y, x⁆ := (Subgroup.mem_center_iff.mp hcen x).symm
      have hyxeq : y * x = ⁅y, x⁆ * (x * y) := by
        rw [commutatorElement_def]; group
      calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
        _ = x * (⁅y, x⁆ * (x * y)) * y := by rw [hyxeq]
        _ = (x * ⁅y, x⁆) * (x * y * y) := by group
        _ = (⁅y, x⁆ * x) * (x * y * y) := by rw [← hcx]
        _ = ⁅y, x⁆ * x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]; group
    -- regular 性の `c` は `P'` に入るので `c² = 1`
    obtain ⟨c, hc, hcpow⟩ := hreg x y
    have hcP : c ∈ commutator P := by
      refine Subgroup.commutator_mono le_top le_top hc
    rw [(hkey c hcP).1, mul_one] at hcpow
    rw [hclass2] at hcpow
    -- `⁅y,x⁆ x² y² = x² y²` ⟹ `⁅y,x⁆ = 1`
    have hone : ⁅y, x⁆ = 1 := by
      have h1 : ⁅y, x⁆ * x ^ 2 * y ^ 2 = 1 * x ^ 2 * y ^ 2 := by rw [one_mul]; exact hcpow
      exact mul_right_cancel (mul_right_cancel h1)
    exact hxy (commutatorElement_eq_one_iff_commute.mp hone).symm

/-- **Isaacs Problem 10A.1** (書籍 p. 308) ⭐: 2-群は **regular ⟺ 可換**。 -/
theorem isRegularPGroup_two_iff_commute [Finite P] (hp : IsPGroup 2 P) :
    IsRegularPGroup 2 P ↔ ∀ x y : P, x * y = y * x :=
  ⟨fun hreg => commute_of_isRegularPGroup_two_aux (Nat.card P) P le_rfl hp hreg,
    isRegularPGroup_of_commute 2⟩

end -- 10A.1

end OddOrder.Isaacs.Ch10
