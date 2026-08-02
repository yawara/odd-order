/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.Isaacs.Ch02_Subnormality.Basic
import OddOrder.GroupTheory.FrattiniPGroup
import OddOrder.Isaacs.Ch10_MoreTransfer.WreathRecognition
import Mathlib.GroupTheory.IndexNormal
import OddOrder.Isaacs.Ch09_MoreSubnormality.Schenkman

/-!
# Isaacs §10A の演習 (書籍 pp. 307-308)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 10A。

* **10A.1** `isRegularPGroup_two_iff_commute` — **2-群は regular ⟺ 可換**。
* **10A.2** `pow_mul_eq_one_of_isRegularPGroup` — **regular `p`-群では `{x | x^p = 1}` が
  部分群** (`omegaOneOfIsRegularPGroup` がその部分群)。
* **10A.5** `exists_injective_hom_regularWreath_of_index_sq` — `|P : Q| = p²` かつ
  `Q ∩ Z(P) = 1` なら `P` は `C_p ≀ C_p` の部分群と同型。
* **10A.3 (前半)** `exists_injective_hom_regularWreath_of_center_isComplement` — `|Z(P)| = p`,
  `A` 可換で指数 `p`, `Z(P)` が `A` の直積因子なら `P ↪ C_p ≀ C_p` (10A.5 に帰着)。
  後半「`A` は基本可換」= `pow_eq_one_of_center_isComplement` ✅。
* **10A.6** `isTwoTransitive_iff_exists_doubleCoset` — 推移的作用の点安定化群 `H` について
  **2-推移的 ⟺ ある `g` で `G = H ∪ HgH`**。
* **10A.7** `exists_surjective_wreath_of_mem_compl_orders` — `A ◁ P` が基本可換で指数 `p`,
  `P ∖ A` に位数 `p` の元と位数 `p²` の元があれば `C_p ≀ C_p` は `P` の準同型像。
* **10B.2 の骨格** `le_socle_of_exists_normal_complement` — `Soc(G) ⊓ E` に `G`-不変な補元が
  取れれば `E ≤ Soc(G)`。10B.2 は残り Maschke (`E` の完全可約性) だけ。

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

section /- 10A.2: regular p-群では p-乗して 1 の元が部分群をなす (p. 308) -/

/-- **regular 性は部分群に遺伝する** (書籍 hint の第 1 段)。 -/
theorem IsRegularPGroup.subgroup {p : ℕ} (hP : IsRegularPGroup p P) (H : Subgroup P) :
    IsRegularPGroup p ↥H := by
  intro x y
  obtain ⟨c, hc, hcpow⟩ := hP (x : P) (y : P)
  have hmapclose : (Subgroup.closure ({x, y} : Set ↥H)).map H.subtype
      = Subgroup.closure ({(x : P), (y : P)} : Set P) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext z
    simp [Set.mem_image, eq_comm]
  have hmapc := Subgroup.map_commutator (H₁ := Subgroup.closure ({x, y} : Set ↥H))
    (H₂ := Subgroup.closure ({x, y} : Set ↥H)) H.subtype
  rw [hmapclose] at hmapc
  rw [← hmapc] at hc
  obtain ⟨c', hc', hceq⟩ := hc
  refine ⟨c', hc', Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_pow]
  rw [show ((c' : ↥H) : P) = c from hceq]
  exact hcpow

/-- 可換な 2 元で生成される群は可換。 -/
private theorem commute_of_closure_pair {H : Type*} [Group H] {a b : H}
    (htop : Subgroup.closure ({a, b} : Set H) = ⊤) (hab : a * b = b * a) (u v : H) :
    u * v = v * u := by
  -- まず `a` と `b` はそれぞれ `closure {a, b}` の全ての元と可換
  have key : ∀ w ∈ ({a, b} : Set H),
      Subgroup.closure ({a, b} : Set H) ≤ Subgroup.centralizer ({w} : Set H) := by
    intro w hw
    refine (Subgroup.closure_le _).mpr ?_
    intro t ht
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rcases hw with rfl | rfl <;> rcases ht with rfl | rfl
    · rfl
    · exact hab
    · exact hab.symm
    · rfl
  -- ゆえに `closure {a, b}` は自分自身の中心化群に含まれる
  have hsub : Subgroup.closure ({a, b} : Set H)
      ≤ Subgroup.centralizer (Subgroup.closure ({a, b} : Set H) : Set H) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro w hw
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp (key w hw ht) w rfl).symm
  have hu := hsub (htop ▸ Subgroup.mem_top u)
  exact (Subgroup.mem_centralizer_iff.mp hu v (htop ▸ Subgroup.mem_top v)).symm

/-- 10A.2 の帰納核。 -/
private theorem pow_mul_eq_one_of_isRegularPGroup_aux.{u} (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∀ (P : Type u) [Group P] [Finite P], Nat.card P ≤ n → IsPGroup p P →
      IsRegularPGroup p P → ∀ x y : P, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1 := by
  induction n with
  | zero =>
    intro P _ _ hcard
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ n IH =>
    intro P _ _ hcard hp hreg x y hx hy
    -- 真部分群へ降りる道具
    have hsub : ∀ H : Subgroup P, H ≠ ⊤ → ∀ u v : P, u ∈ H → v ∈ H →
        u ^ p = 1 → v ^ p = 1 → (u * v) ^ p = 1 := by
      intro H hH u v hu hv hu1 hv1
      have hcardH : Nat.card ↥H ≤ n := by
        have hne : Nat.card ↥H ≠ Nat.card P := fun h => hH (Subgroup.eq_top_of_card_eq _ h)
        have hle := Subgroup.card_le_card_group H
        omega
      have hkey := IH ↥H hcardH (hp.to_subgroup H) (hreg.subgroup H) ⟨u, hu⟩ ⟨v, hv⟩
        (Subtype.ext (by simpa using hu1)) (Subtype.ext (by simpa using hv1))
      simpa using congrArg Subtype.val hkey
    by_cases htop : Subgroup.closure ({x, y} : Set P) = ⊤
    swap
    · exact hsub _ htop x y (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)) hx hy
    by_cases hab : ∀ a b : P, a * b = b * a
    · rw [Commute.mul_pow (hab x y), hx, hy, one_mul]
    -- 以下 `P` は非可換で `P = ⟨x, y⟩`
    have hab : ∃ a b : P, a * b ≠ b * a := by
      by_contra hcon
      exact ‹¬ ∀ a b : P, a * b = b * a› fun a b => not_not.mp fun h => hcon ⟨a, b, h⟩
    -- `Φ(P) ≠ ⊤`
    have hfr : frattini P ≠ ⊤ := by
      intro h
      obtain ⟨a, b, hne⟩ := hab
      have hbot : (⊥ : Subgroup P) = ⊤ := frattini_nongenerating (by rw [h, bot_sup_eq])
      refine hne ?_
      have ha : a = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top a)
      have hb : b = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top b)
      rw [ha, hb]
    have hcommne : commutator P ≠ ⊤ := by
      intro h
      refine hfr (eq_top_iff.mpr ?_)
      rw [← h]
      exact Subgroup.commutator_le.mpr fun g₁ _ g₂ _ =>
        OddOrder.GroupTheory.IsPGroup.commutator_mem_frattini hp g₁ g₂
    -- **Step A**: `a^p = 1` なら `⁅a, g⁆^p = 1`
    have hstepA : ∀ a g : P, a ^ p = 1 → ⁅a, g⁆ ^ p = 1 := by
      intro a g ha
      have hb1 : (g * a * g⁻¹) ^ p = 1 := by
        rw [conj_pow, ha]; group
      have hcomm : ⁅a, g⁆ = a * (g * a * g⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      by_cases hK : Subgroup.closure ({a, g * a * g⁻¹} : Set P) = ⊤
      · exfalso
        -- `g a g⁻¹ ∈ ⟨a⟩ ⊔ Φ(P)` なので `⟨a⟩ ⊔ Φ(P) = ⊤`, つまり `P = ⟨a⟩` は可換
        have hmem : g * a * g⁻¹ ∈ Subgroup.zpowers a ⊔ frattini P := by
          have hsplit : g * a * g⁻¹ = a * ⁅a⁻¹, g⁆ := by rw [commutatorElement_def]; group
          rw [hsplit]
          refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
            (Subgroup.mem_sup_right ?_)
          exact OddOrder.GroupTheory.IsPGroup.commutator_mem_frattini hp a⁻¹ g
        have hsup : Subgroup.zpowers a ⊔ frattini P = ⊤ := by
          rw [eq_top_iff, ← hK]
          refine Subgroup.closure_le _ |>.mpr ?_
          intro w hw
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with hw | hw
          · rw [hw]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
          · rw [hw]; exact hmem
        have hz : Subgroup.zpowers a = ⊤ := frattini_nongenerating hsup
        obtain ⟨u, v, huv⟩ := hab
        refine huv ?_
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hz ▸ Subgroup.mem_top u)
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hz ▸ Subgroup.mem_top v)
        rw [← hm, ← hk, zpow_mul_comm]
      · rw [hcomm]
        exact hsub _ hK a (g * a * g⁻¹)⁻¹ (Subgroup.subset_closure (by simp))
          (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))) ha
          (by rw [inv_pow, hb1, inv_one])
    -- **Step B**: `P'` の元はすべて `p` 乗で `1`
    -- ⚠ `let` で定義すると elaborator が本体を展開し続けて heartbeat 超過するので
    -- `obtain` で不透明に取り出す。
    obtain ⟨Ω, hΩ⟩ : ∃ Ω : Subgroup P, ∀ c : P, c ∈ Ω ↔ (c ∈ commutator P ∧ c ^ p = 1) :=
      ⟨{ carrier := {c | c ∈ commutator P ∧ c ^ p = 1}
         one_mem' := ⟨one_mem _, one_pow p⟩
         mul_mem' := fun {u v} hu hv =>
           ⟨mul_mem hu.1 hv.1, hsub (commutator P) hcommne u v hu.1 hv.1 hu.2 hv.2⟩
         inv_mem' := fun {u} hu => ⟨inv_mem hu.1, by rw [inv_pow, hu.2, inv_one]⟩ },
       fun _ => Iff.rfl⟩
    haveI hΩnorm : Ω.Normal := by
      refine ⟨fun m hm gg => (hΩ _).mpr ⟨?_, ?_⟩⟩
      · exact (inferInstance : (commutator P).Normal).conj_mem m ((hΩ m).mp hm).1 gg
      · rw [conj_pow, ((hΩ m).mp hm).2]; group
    have hxyΩ : ⁅x, y⁆ ∈ Ω := (hΩ _).mpr
      ⟨Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y),
        hstepA x y hx⟩
    have hP'Ω : commutator P ≤ Ω := by
      refine Subgroup.Normal.quotient_commutative_iff_commutator_le.mp ⟨⟨fun u v => ?_⟩⟩
      have htopQ : Subgroup.closure
          ({(x : P ⧸ Ω), (y : P ⧸ Ω)} : Set (P ⧸ Ω)) = ⊤ := by
        rw [eq_top_iff]
        rintro w -
        obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective w
        have hmap : (Subgroup.closure ({x, y} : Set P)).map (QuotientGroup.mk' Ω)
            = Subgroup.closure ({(x : P ⧸ Ω), (y : P ⧸ Ω)} : Set (P ⧸ Ω)) := by
          rw [MonoidHom.map_closure]
          congr 1
          ext z
          simp [Set.mem_image, eq_comm]
        rw [← hmap]
        exact ⟨w', htop ▸ Subgroup.mem_top w', rfl⟩
      have hcomm : (x : P ⧸ Ω) * (y : P ⧸ Ω) = (y : P ⧸ Ω) * (x : P ⧸ Ω) := by
        refine commutatorElement_eq_one_iff_commute.mp ?_
        have hone : ((⁅x, y⁆ : P) : P ⧸ Ω) = 1 := (QuotientGroup.eq_one_iff _).mpr hxyΩ
        simpa [commutatorElement_def] using hone
      exact commute_of_closure_pair htopQ hcomm u v
    -- 仕上げ: regular 性の `c` は `P'` にあるので `c^p = 1`
    obtain ⟨c, hc, hcpow⟩ := hreg x y
    have hcP : c ∈ commutator P := Subgroup.commutator_mono le_top le_top hc
    rw [hcpow, hx, hy, ((hΩ c).mp (hP'Ω hcP)).2, one_mul, one_mul]

/-- **Isaacs Problem 10A.2** (書籍 p. 308) ⭐: regular `p`-群では `p` 乗して `1` になる元の
集合は積で閉じている (したがって部分群をなす)。 -/
theorem pow_mul_eq_one_of_isRegularPGroup [Finite P] {p : ℕ} [Fact p.Prime] (hp : IsPGroup p P)
    (hreg : IsRegularPGroup p P) {x y : P} (hx : x ^ p = 1) (hy : y ^ p = 1) :
    (x * y) ^ p = 1 :=
  pow_mul_eq_one_of_isRegularPGroup_aux p (Nat.card P) P le_rfl hp hreg x y hx hy

/-- **Isaacs Problem 10A.2** (部分群版): regular `p`-群の `p` 捩れ元は部分群をなす。 -/
def omegaOneOfIsRegularPGroup [Finite P] {p : ℕ} [Fact p.Prime] (hp : IsPGroup p P)
    (hreg : IsRegularPGroup p P) : Subgroup P where
  carrier := {x | x ^ p = 1}
  one_mem' := one_pow p
  mul_mem' hu hv := pow_mul_eq_one_of_isRegularPGroup hp hreg hu hv
  inv_mem' {u} hu := by
    simp only [Set.mem_setOf_eq] at hu ⊢
    rw [inv_pow, hu, inv_one]

end -- 10A.2

section /- 10A.5: 指数 p² の core-free 部分群があれば C_p ≀ C_p に埋め込める (p. 308) -/

/-- **Isaacs Problem 10A.5** (書籍 p. 308) ⭐: `P` を `p`-群, `Q ≤ P` を `|P : Q| = p²` かつ
`Q ∩ Z(P) = 1` とすると, `P` は `C_p ≀ C_p` の部分群と同型 (= 単射準同型が存在)。

`Q ⊓ Z(P) = 1` から `core_P(Q) = 1` (`p`-群の非自明な正規部分群は中心と交わる) なので
`P` の `P ⧸ Q` (`p²` 点) への作用は忠実。像は `Sym(p²)` の `p`-部分群なので Sylow
`p`-部分群 `S` に含まれ, mathlib の `Sylow.mulEquivIteratedWreathProduct` で
`S ≃* C_p ≀ C_p`。 -/
theorem exists_injective_hom_regularWreath_of_index_sq [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) {Q : Subgroup P} (hidx : Q.index = p ^ 2)
    (hQZ : Q ⊓ Subgroup.center P = ⊥) :
    ∃ f : P →* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)), Function.Injective f := by
  classical
  -- `core_P(Q) = ⊥`
  have hcore : Q.normalCore = ⊥ := by
    by_contra hne
    obtain ⟨x, hxN, hxZ, hxne⟩ :=
      OddOrder.GroupTheory.exists_mem_center_of_normal_ne_bot hP (K := Q.normalCore) hne
    have hmem : x ∈ Q ⊓ Subgroup.center P := ⟨Q.normalCore_le hxN, hxZ⟩
    rw [hQZ, Subgroup.mem_bot] at hmem
    exact hxne hmem
  -- `P ⧸ Q` (`p²` 点) への忠実な作用
  have hf_inj : Function.Injective (MulAction.toPermHom P (P ⧸ Q)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
    exact hcore
  have hquot : Nat.card (P ⧸ Q) = p ^ 2 := by rw [← Subgroup.index_eq_card, hidx]
  -- 像は `p`-部分群なので Sylow に含まれる
  have hrange : IsPGroup p ↥(MulAction.toPermHom P (P ⧸ Q)).range :=
    hP.of_surjective _ (MulAction.toPermHom P (P ⧸ Q)).rangeRestrict_surjective
  obtain ⟨S, hS⟩ := hrange.exists_le_sylow
  have e := Sylow.mulEquivIteratedWreathProduct p 2 (P ⧸ Q) hquot (Multiplicative (ZMod p))
    (by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]) S
  refine ⟨(((iteratedWreathProductTwoMulEquiv (Multiplicative (ZMod p))).toMonoidHom.comp
    e.toMonoidHom).comp (Subgroup.inclusion hS)).comp
      (MulAction.toPermHom P (P ⧸ Q)).rangeRestrict, fun a b hab => ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at hab
  have h1 := (iteratedWreathProductTwoMulEquiv (Multiplicative (ZMod p))).injective hab
  have h2 := e.injective h1
  have h3 := Subgroup.inclusion_injective hS h2
  have h4 : (MulAction.toPermHom P (P ⧸ Q)) a = (MulAction.toPermHom P (P ⧸ Q)) b :=
    congrArg Subtype.val h3
  exact hf_inj h4

end -- 10A.5

section /- 10A.3 (後半への準備): 指数が素数の可換部分群 -/

/-- 指数が素数 `p` の部分群は極大: `A ≤ H` なら `H = A` か `H = ⊤`. -/
theorem eq_of_le_of_index_prime [Finite P] {p : ℕ} (hp : p.Prime) {A H : Subgroup P}
    (hidx : A.index = p) (hAH : A ≤ H) : H = A ∨ H = ⊤ := by
  have hmul := Subgroup.relIndex_mul_index hAH
  rw [hidx] at hmul
  rcases hp.eq_one_or_self_of_dvd H.index ⟨A.relIndex H, by rw [← hmul]; ring⟩ with h | h
  · exact Or.inr (Subgroup.index_eq_one.mp h)
  · refine Or.inl ?_
    rw [h] at hmul
    have hrel : A.relIndex H = 1 :=
      Nat.eq_of_mul_eq_mul_right hp.pos (by rw [hmul, one_mul])
    exact ((Subgroup.relIndex_eq_one).mp hrel).antisymm hAH

/-- **10A.3 後半の鍵**: `A` が可換で指数が素数 `p`, `Z(P) ≤ A`, `u ∈ P ∖ A` のとき,
`A` の元が `Z(P)` に入る ⟺ `u` と可換.

`A` は極大 (`eq_of_le_of_index_prime`) なので `u ∉ A` から `A ⊔ ⟨u⟩ = ⊤`; `A` 可換なので
`u` とも可換な `a ∈ A` は `P` 全体を中心化する. -/
theorem mem_center_iff_commute_of_index_prime [Finite P] {p : ℕ} (hp : p.Prime)
    {A : Subgroup P} [IsMulCommutative ↥A] (hidx : A.index = p)
    {u : P} (hu : u ∉ A) {a : P} (ha : a ∈ A) :
    a ∈ Subgroup.center P ↔ a * u = u * a := by
  constructor
  · intro haz
    exact (Subgroup.mem_center_iff.mp haz u).symm
  · intro hau
    have hsup : A ⊔ Subgroup.closure {u} = ⊤ := by
      rcases eq_of_le_of_index_prime hp hidx (le_sup_left : A ≤ A ⊔ Subgroup.closure {u})
        with h | h
      · exact absurd (h ▸ (le_sup_right : Subgroup.closure {u} ≤ _)
          (Subgroup.mem_closure_singleton_self u)) hu
      · exact h
    have hle : A ⊔ Subgroup.closure {u} ≤ Subgroup.centralizer {a} := by
      refine sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr ?_)
        (Subgroup.closure_le _ |>.mpr ?_)
      · rintro h rfl
        exact congrArg Subtype.val
          (IsMulCommutative.is_comm.comm (⟨h, ha⟩ : ↥A) ⟨x, hx⟩)
      · rintro x rfl
        exact Subgroup.mem_centralizer_iff.mpr (by rintro h rfl; exact hau)
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.mp (hle (hsup ▸ Subgroup.mem_top g)) a rfl).symm

end

/-- `A = Z × K` (可換群の直積分解) で `Z` の指数が `p` を割るなら `A^p ≤ K`.

`a = z * k` と書くと `a ^ p = z ^ p * k ^ p = k ^ p ∈ K`. -/
theorem pow_mem_of_isComplement' {A : Type*} [CommGroup A] {Z K : Subgroup A}
    (h : Subgroup.IsComplement' Z K) {p : ℕ} (hZ : ∀ z ∈ Z, z ^ p = 1) (a : A) :
    a ^ p ∈ K := by
  have hmem : a ∈ (↑(Z ⊔ K) : Set A) := by rw [h.sup_eq_top]; trivial
  rw [Subgroup.normal_mul] at hmem
  obtain ⟨z, hz, k, hk, rfl⟩ := hmem
  rw [mul_pow, hZ z hz, one_mul]
  exact K.pow_mem hk p

open scoped IsMulCommutative in
/-- **Isaacs Problem 10A.3 の後半** (書籍 p. 308) ⭐: 前半と同じ仮定
(`|Z(P)| = p`, `A` 可換で指数 `p`, `Z(P)` が `A` の直積因子) のもとで **`A` は基本可換**.

`A^p := {a^p | a ∈ A}` は `A ◁ P` (指数 = 最小素因数) と `(gag⁻¹)^p = g a^p g⁻¹` から
`P` に正規。直積分解 `A = Z(P) × K` と `|Z(P)| = p` から `A^p ≤ K`
(`pow_mem_of_isComplement'`)。もし `A^p ≠ 1` なら, `p`-群の非自明正規部分群は中心と
非自明に交わる (Isaacs Thm 1.19 = `IsPGroup.normal_inf_center_nontrivial`) ので
`1 ≠ z ∈ A^p ⊓ Z(P) ≤ K ⊓ Z(P) = 1` となって矛盾。 -/
theorem pow_eq_one_of_center_isComplement [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) {A : Subgroup P} [IsMulCommutative ↥A] (hidx : A.index = p)
    (hZ : Nat.card (Subgroup.center P) = p) (_hZle : Subgroup.center P ≤ A)
    {K : Subgroup ↥A} (hK : Subgroup.IsComplement' ((Subgroup.center P).subgroupOf A) K)
    {a : P} (ha : a ∈ A) : a ^ p = 1 := by
  have hp : p.Prime := Fact.out
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : ↥A) ⟨y, hy⟩)
  -- `A ◁ P`: 指数 `p` は `|P|` の最小素因数
  have hcardP : ∃ n : ℕ, Nat.card P = p ^ n := (IsPGroup.iff_card).mp hP
  obtain ⟨n, hn⟩ := hcardP
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hn
    have hmul := Subgroup.card_mul_index A
    rw [hidx, hn] at hmul
    have h1 := hp.one_lt
    have h2 : p = 1 := Nat.eq_one_of_dvd_one (Dvd.intro_left _ hmul)
    omega
  haveI : A.Normal := by
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    rw [hidx, hn, hp.pow_minFac hn0]
  -- `A^p` は `P` の正規部分群
  set Ap : Subgroup P :=
    { carrier := {y : P | ∃ x ∈ A, x ^ p = y}
      one_mem' := ⟨1, A.one_mem, one_pow p⟩
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, A.mul_mem hx hy, Commute.mul_pow (hcommA x hx y hy) p⟩
      inv_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x⁻¹, A.inv_mem hx, by rw [inv_pow]⟩ } with hApdef
  haveI : Ap.Normal := by
    refine ⟨fun y hy g => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨g * x * g⁻¹, ‹A.Normal›.conj_mem x hx g, by rw [conj_pow]⟩
  -- `A^p ≤ K` (の `P` への像)
  have hZp : ∀ z ∈ (Subgroup.center P).subgroupOf A, z ^ p = 1 := by
    intro z hz
    have h1 : ((z : P)) ∈ Subgroup.center P := hz
    have h2 : orderOf (⟨(z : P), h1⟩ : ↥(Subgroup.center P)) ∣ p := hZ ▸ orderOf_dvd_natCard _
    have h3 := orderOf_dvd_iff_pow_eq_one.mp h2
    refine Subtype.ext ?_
    have h4 : ((⟨(z : P), h1⟩ : ↥(Subgroup.center P)) ^ p : P) = 1 := congrArg Subtype.val h3
    simpa using h4
  have hApK : ∀ (x : P) (hx : x ∈ A), (⟨x ^ p, A.pow_mem hx p⟩ : ↥A) ∈ K := by
    intro x hx
    have := pow_mem_of_isComplement' hK hZp (⟨x, hx⟩ : ↥A)
    simpa using this
  -- `A^p ⊓ Z(P)` の元は `1`
  have hkey : ∀ z : P, z ∈ Ap ⊓ Subgroup.center P → z = 1 := by
    rintro z ⟨⟨x, hx, rfl⟩, hzc⟩
    have hxpA : x ^ p ∈ A := A.pow_mem hx p
    have h1 : (⟨x ^ p, hxpA⟩ : ↥A) ∈ K := hApK x hx
    have h2 : (⟨x ^ p, hxpA⟩ : ↥A) ∈ (Subgroup.center P).subgroupOf A := hzc
    exact congrArg Subtype.val (Subgroup.mem_bot.mp (hK.disjoint.le_bot ⟨h2, h1⟩))
  -- `A^p = 1`
  by_contra hcon
  haveI : Nontrivial ↥Ap :=
    ⟨⟨1, ⟨a ^ p, ⟨a, ha, rfl⟩⟩, fun h => hcon (congrArg Subtype.val h).symm⟩⟩
  haveI := Ch01.IsPGroup.normal_inf_center_nontrivial (P := P) hP (N := Ap) inferInstance
  obtain ⟨⟨z, hz⟩, ⟨w, hw⟩, hzw⟩ :=
    exists_pair_ne ↥((Ap ⊓ Subgroup.center P : Subgroup P))
  exact hzw (Subtype.ext ((hkey z hz).trans (hkey w hw).symm))

section /- 10A.3 (前半): Z(P) が A の直積因子なら C_p ≀ C_p に埋め込める (p. 308) -/

/-- **Isaacs Problem 10A.3 の前半** (書籍 p. 308) ⭐: `P` を `p`-群, `|Z(P)| = p`,
`A ≤ P` を指数 `p` の可換部分群とし, `Z(P)` が `A` の直積因子 (= `↥A` の中で補元 `K` を
もつ) とすると, `P` は `C_p ≀ C_p` の部分群と同型。

`Q := K` を `P` に押し出すと `|P : Q| = |P : A| · |A : K| = p · |Z(P)| = p²` かつ
`Q ∩ Z(P) = 1` なので **10A.5** (`exists_injective_hom_regularWreath_of_index_sq`)
がそのまま使える。

後半「`A` は基本可換」は `pow_eq_one_of_center_isComplement`。 -/
theorem exists_injective_hom_regularWreath_of_center_isComplement [Finite P] {p : ℕ}
    [Fact p.Prime] (hP : IsPGroup p P) {A : Subgroup P} (hidx : A.index = p)
    (hZ : Nat.card (Subgroup.center P) = p) (hZle : Subgroup.center P ≤ A)
    {K : Subgroup ↥A} (hK : Subgroup.IsComplement' ((Subgroup.center P).subgroupOf A) K) :
    ∃ f : P →* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)), Function.Injective f := by
  refine exists_injective_hom_regularWreath_of_index_sq hP
    (Q := K.map A.subtype) ?_ ?_
  · -- 指数の計算: `|A| = p · |K|`, `|P| = p · |A|`, `|Q| = |K|`
    have hcardZA : Nat.card ((Subgroup.center P).subgroupOf A) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv, hZ]
    have hmulA : p * Nat.card K = Nat.card ↥A := by
      have h := hK.card_mul
      rwa [hcardZA] at h
    have hQK : Nat.card ↥(K.map A.subtype) = Nat.card K :=
      (Nat.card_congr (Subgroup.equivMapOfInjective K A.subtype A.subtype_injective).toEquiv).symm
    have hPA : Nat.card ↥A * p = Nat.card P := by
      have h := Subgroup.card_mul_index A
      rwa [hidx] at h
    have hPQ := Subgroup.card_mul_index (K.map A.subtype)
    rw [hQK] at hPQ
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have hcalc : Nat.card K * (K.map A.subtype).index = Nat.card K * p ^ 2 := by
      rw [hPQ, ← hPA, ← hmulA]; ring
    exact Nat.eq_of_mul_eq_mul_left hKpos hcalc
  · -- `Q ∩ Z(P) = 1`
    rw [eq_bot_iff]
    rintro x ⟨hxQ, hxZ⟩
    obtain ⟨y, hyK, hyx⟩ := Subgroup.mem_map.mp hxQ
    have hyZA : y ∈ (Subgroup.center P).subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      show (y : P) ∈ Subgroup.center P
      rw [show ((y : P)) = x from hyx]
      exact hxZ
    have hy_bot : y ∈ ((Subgroup.center P).subgroupOf A) ⊓ K := ⟨hyZA, hyK⟩
    rw [disjoint_iff.mp hK.disjoint, Subgroup.mem_bot] at hy_bot
    rw [Subgroup.mem_bot, ← hyx, hy_bot]
    rfl

end -- 10A.3 (前半)

section /- 10A.6: 2-推移性 ⟺ G = H ∪ HgH (p. 308) -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- **Isaacs Problem 10A.6** (書籍 p. 308) ⭐: `G` が `Ω` に推移的に作用し `H` を点
`α` の安定化群とすると, **`G` が `Ω` に 2-推移的 ⟺ ある `g ∈ G` で `G = H ∪ HgH`**。

`H`-軌道と `(H, H)`-両側剰余類の対応がそのまま中身: 「両側剰余類が高々 2 個」は
「`H` が `Ω ∖ {α}` に推移的」と同じこと。 -/
theorem isTwoTransitive_iff_exists_doubleCoset [MulAction.IsPretransitive G Ω] (α : Ω) :
    (∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : G, g • a = c ∧ g • b = d) ↔
      ∃ g : G, ∀ x : G, x ∈ MulAction.stabilizer G α ∨
        ∃ h₁ ∈ MulAction.stabilizer G α, ∃ h₂ ∈ MulAction.stabilizer G α,
          x = h₁ * g * h₂ := by
  constructor
  · intro h2t
    by_cases hβ : ∃ β : Ω, β ≠ α
    · obtain ⟨β, hβα⟩ := hβ
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G α β
      refine ⟨g, fun x => ?_⟩
      by_cases hx : x ∈ MulAction.stabilizer G α
      · exact Or.inl hx
      · refine Or.inr ?_
        -- `x • α ≠ α` なので 2-推移性で `h • (g • α) = x • α` なる `h ∈ H` がある
        have hxα : x • α ≠ α := hx
        obtain ⟨h, hh1, hh2⟩ := h2t α (g • α) α (x • α) (fun hc => hβα (hg ▸ hc.symm))
          (fun hc => hxα hc.symm)
        have hhH : h ∈ MulAction.stabilizer G α := hh1
        refine ⟨h, hhH, (h * g)⁻¹ * x, ?_, by group⟩
        change ((h * g)⁻¹ * x) • α = α
        rw [mul_smul, inv_smul_eq_iff, mul_smul]
        exact hh2.symm
    · -- `Ω` が 1 点なら `H = G`
      refine ⟨1, fun x => Or.inl (show x • α = α from ?_)⟩
      by_contra hc
      exact hβ ⟨x • α, hc⟩
  · rintro ⟨g, hg⟩ a b c d hab hcd
    -- まず `H` が `Ω ∖ {α}` に推移的であること
    have hHtrans : ∀ β γ : Ω, β ≠ α → γ ≠ α →
        ∃ h : G, h ∈ MulAction.stabilizer G α ∧ h • β = γ := by
      intro β γ hβ hγ
      obtain ⟨u, hu⟩ := MulAction.exists_smul_eq G α β
      obtain ⟨v, hv⟩ := MulAction.exists_smul_eq G α γ
      have hunotH : u ∉ MulAction.stabilizer G α := fun h => hβ (hu ▸ h)
      have hvnotH : v ∉ MulAction.stabilizer G α := fun h => hγ (hv ▸ h)
      obtain ⟨h₁, hh₁, h₂, hh₂, hueq⟩ := (hg u).resolve_left hunotH
      obtain ⟨k₁, hk₁, k₂, hk₂, hveq⟩ := (hg v).resolve_left hvnotH
      refine ⟨k₁ * h₁⁻¹, Subgroup.mul_mem _ hk₁ (Subgroup.inv_mem _ hh₁), ?_⟩
      have hβ' : β = h₁ • (g • α) := by
        rw [← hu, hueq, mul_smul, mul_smul, show h₂ • α = α from hh₂]
      have hγ' : γ = k₁ • (g • α) := by
        rw [← hv, hveq, mul_smul, mul_smul, show k₂ • α = α from hk₂]
      rw [hβ', hγ', mul_smul, inv_smul_smul]
    -- `a`, `c` を `α` に移してから `H`-推移性を使う
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq G a α
    obtain ⟨v, hv⟩ := MulAction.exists_smul_eq G c α
    have hub : u • b ≠ α := by
      intro hc
      exact hab (MulAction.injective u (hc.trans hu.symm)).symm
    have hvd : v • d ≠ α := by
      intro hc
      exact hcd (MulAction.injective v (hc.trans hv.symm)).symm
    obtain ⟨h, hh, hhb⟩ := hHtrans (u • b) (v • d) hub hvd
    refine ⟨v⁻¹ * h * u, ?_, ?_⟩
    · rw [mul_smul, mul_smul, hu, show h • α = α from hh, inv_smul_eq_iff, hv]
    · rw [mul_smul, mul_smul, hhb, inv_smul_eq_iff]

end -- 10A.6

section /- 10A.7: P − A に位数 p と p² の元があれば C_p ≀ C_p は準同型像 (p. 308) -/

/-- `(a w)^n = (∏_{i<n} w^i a w^{-i}) · w^n` (`w` による共役の積への展開)。 -/
private theorem mul_pow_eq_conj_list_prod {H : Type*} [Group H] (a w : H) : ∀ n : ℕ,
    (a * w) ^ n = ((List.range n).map (fun i => w ^ i * a * (w ^ i)⁻¹)).prod * w ^ n
  | 0 => by simp
  | (n + 1) => by
    rw [pow_succ, mul_pow_eq_conj_list_prod a w n, List.range_succ, List.map_append,
      List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    group

/-- **Isaacs Problem 10A.7** (書籍 p. 308) ⭐: `A ◁ P` が基本可換 `p`-群で `|P : A| = p`,
`P ∖ A` が位数 `p` の元と位数 `p²` の元をともに含むなら, `C_p ≀ C_p` は `P` の準同型像。

位数 `p²` の元 `v` を `v = a w` (`a ∈ A`, `w = u^j ∉ A`, `w^p = 1`) と書くと
`v^p = ∏_{i<p} w^i a w^{-i}` なので **共役類積 ≠ 1** が出る。`a` が中心的なら
その積は `a^p = 1` になってしまうので `a ∉ Z(P)`。あとは repo の Cor 10.5
(`exists_surjective_wreath_of_conj_list_prod_ne_one`) がそのまま使える。 -/
theorem exists_surjective_wreath_of_mem_compl_orders [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) {A : Subgroup P} [A.Normal] (hidx : A.index = p)
    (hEA : A.IsElementaryAbelian p) {u : P} (huA : u ∉ A) (hup : u ^ p = 1)
    {v : P} (hv : orderOf v = p ^ 2) :
    ∃ φ : P →* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)), Function.Surjective φ := by
  have hp_prime : p.Prime := Fact.out
  have hEA' : OddOrder.GroupTheory.IsElementaryAbelian p ↥A := hEA
  -- `v ^ p ≠ 1`, したがって `v ∉ A`
  have hvp : v ^ p ≠ 1 := by
    intro h
    have hdvd : orderOf v ∣ p := orderOf_dvd_of_pow_eq_one h
    rw [hv] at hdvd
    have hle := Nat.le_of_dvd hp_prime.pos hdvd
    nlinarith [hp_prime.two_le]
  have hvA : v ∉ A := by
    intro hmem
    refine hvp ?_
    simpa using congrArg Subtype.val (hEA'.pow_eq_one (⟨v, hmem⟩ : ↥A))
  -- `P ⧸ A` は位数 `p` の巡回群で `u` の像が生成元
  have hcardQ : Nat.card (P ⧸ A) = p := by rw [← Subgroup.index_eq_card, hidx]
  have hune : (QuotientGroup.mk u : P ⧸ A) ≠ 1 := fun h => huA ((QuotientGroup.eq_one_iff u).mp h)
  have hgen : Subgroup.zpowers (QuotientGroup.mk u : P ⧸ A) = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_zpowers, hcardQ]
    have hdvd : orderOf (QuotientGroup.mk u : P ⧸ A) ∣ p := by
      rw [← hcardQ]; exact orderOf_dvd_natCard _
    rcases hp_prime.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hune
    · exact h1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgen ▸ Subgroup.mem_top
    (QuotientGroup.mk v : P ⧸ A))
  -- `w := u ^ j`, `a := v * w⁻¹ ∈ A`
  set w : P := u ^ j with hw_def
  have hwq : (QuotientGroup.mk w : P ⧸ A) = QuotientGroup.mk v := by
    rw [hw_def, ← hj]
    exact map_zpow (QuotientGroup.mk' A) u j
  have haA : v * w⁻¹ ∈ A := by
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk v : P ⧸ A) * (QuotientGroup.mk w)⁻¹ = 1
    rw [hwq, mul_inv_cancel]
  have hwp : w ^ p = 1 := by
    rw [hw_def, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hup, one_zpow]
  have hwA : w ∉ A := by
    intro hmem
    exact hvA ((QuotientGroup.eq_one_iff v).mp (hwq ▸ (QuotientGroup.eq_one_iff w).mpr hmem))
  -- 共役類積 = `v ^ p ≠ 1`
  have hlist : ((List.range p).map (fun i => w ^ i * (v * w⁻¹) * (w ^ i)⁻¹)).prod ≠ 1 := by
    intro h
    refine hvp ?_
    have hva : v = (v * w⁻¹) * w := by group
    rw [hva, mul_pow_eq_conj_list_prod, h, hwp, one_mul]
  -- `a ∉ Z(P)` (中心的なら積は `a ^ p = 1` になってしまう)
  have haZ : v * w⁻¹ ∉ Subgroup.center P := by
    intro hcent
    refine hlist ?_
    have hconst : ((List.range p).map (fun i => w ^ i * (v * w⁻¹) * (w ^ i)⁻¹))
        = List.replicate p (v * w⁻¹) := by
      rw [show List.replicate p (v * w⁻¹) = (List.range p).map (fun _ => v * w⁻¹) by
        rw [List.map_const', List.length_range]]
      refine List.map_congr_left fun i _ => ?_
      rw [Subgroup.mem_center_iff.mp hcent (w ^ i)]
      group
    rw [hconst, List.prod_replicate]
    simpa using congrArg Subtype.val (hEA'.pow_eq_one (⟨v * w⁻¹, haA⟩ : ↥A))
  exact exists_surjective_wreath_of_conj_list_prod_ne_one hP hidx hEA haA haZ hwA hlist

end -- 10A.7

section /- 10B.2 の骨格: 補元が取れれば socle に入る (p. 312) -/

/-- **10B.2 の骨格** ⭐: `E` の中で `Soc(G) ⊓ E` が `G`-不変な補元をもてば `E ≤ Soc(G)`。

帰納法は要らない: 補元 `M` が非自明なら `M` は `G` の極小正規部分群 `M₀` を含み,
`M₀ ≤ Soc(G) ⊓ E ⊓ M = ⊥` で矛盾。よって `M = ⊥` すなわち `E = Soc(G) ⊓ E`。

Isaacs Problem 10B.2 (`E ◁ G` 基本可換, `p ∤ |G : C_G(E)|` ⟹ `E ⊆ Soc(G)`) は
これに **Maschke** (`p′`-群 `G/C_G(E)` の `p`-群 `E` への作用が完全可約) を合わせれば従う。
Maschke 側 (`Additive ↥E` の `ZMod p`-加群化 + 表現 + `MonoidAlgebra.Submodule.exists_isCompl`)
は未実装 (issue 1055 に設計を記録)。 -/
theorem le_socle_of_exists_normal_complement {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hcompl : ∃ M : Subgroup G, M.Normal ∧ M ≤ E ∧
      (Ch02.socle G ⊓ E) ⊓ M = ⊥ ∧ (Ch02.socle G ⊓ E) ⊔ M = E) :
    E ≤ Ch02.socle G := by
  obtain ⟨M, hMnorm, hME, hinf, hsup⟩ := hcompl
  haveI := hMnorm
  have hMbot : M = ⊥ := by
    by_contra hne
    obtain ⟨M₀, hM₀min, hM₀M⟩ := Ch02.exists_isMinimalNormal_le_of_normal M hne
    have hM₀ : M₀ ≤ (Ch02.socle G ⊓ E) ⊓ M :=
      le_inf (le_inf (Ch02.isMinimalNormal_le_socle hM₀min) (hM₀M.trans hME)) hM₀M
    rw [hinf, le_bot_iff] at hM₀
    exact hM₀min.2.1 hM₀
  rw [hMbot, sup_bot_eq] at hsup
  rw [← hsup]
  exact inf_le_left

end -- 10B.2 の骨格

end OddOrder.Isaacs.Ch10
