/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
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

/-! ### Problem 4A.2 — `⁅H, K, L⁆` は元 `⁅h, k, l⁆` たちで生成されるとは限らない -/

/-- 位数 2 の部分群は `{1, h}`: 非単位元がちょうど 1 つ. -/
private lemma exists_eq_one_or_eq_of_card_eq_two {G : Type*} [Group G] {H : Subgroup G}
    (hH : Nat.card H = 2) : ∃ h ∈ H, h ≠ 1 ∧ ∀ x ∈ H, x = 1 ∨ x = h := by
  obtain ⟨y, hy1, hyu⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hH
  refine ⟨(y : G), y.2, fun hcon => hy1 (Subtype.ext (by simpa using hcon)), fun x hx => ?_⟩
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · exact Or.inr (congrArg Subtype.val
      (hyu ⟨x, hx⟩ fun hcon => hx1 (by simpa using congrArg Subtype.val hcon)))

/-- `a ^ 2 = 1` なら `⟨a⟩ = {1, a}`. -/
private lemma eq_one_or_eq_of_mem_zpowers_of_sq_eq_one {G : Type*} [Group G] {a x : G}
    (ha : a ^ 2 = 1) (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  have ha2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact ha
  obtain ⟨k, rfl⟩ := hx
  change a ^ k = 1 ∨ a ^ k = a
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact Or.inl (by rw [hm, show m + m = 2 * m by ring, zpow_mul, ha2, one_zpow])
  · exact Or.inr (by rw [hm, zpow_add, zpow_mul, ha2, one_zpow, one_mul, zpow_one])

/-- 対合 `a`, `b` の生成する部分群同士の交換子部分群は `⁅a, b⁆` の生成する巡回群.

`⟨a⟩ = {1, a}`, `⟨b⟩ = {1, b}` なので生成集合 `{⁅x, y⁆ | x ∈ ⟨a⟩, y ∈ ⟨b⟩}` は `{1, ⁅a, b⁆}`. -/
theorem commutator_zpowers_eq_zpowers_commutatorElement {G : Type*} [Group G] {a b : G}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    ⁅Subgroup.zpowers a, Subgroup.zpowers b⁆ = Subgroup.zpowers ⁅a, b⁆ := by
  refine le_antisymm (Subgroup.commutator_le.2 fun x hx y hy => ?_) ?_
  · rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one ha hx with rfl | rfl
    · simp
    · rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one hb hy with rfl | rfl
      · simp
      · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers b)

/-- **Isaacs Problem 4A.2** (前半, 書籍 p. 122): `H`, `K`, `L` が位数 2 の部分群なら,
三重交換子の**元**の集合 `{⁅⁅x, y⁆, w⁆ | x ∈ H, y ∈ K, w ∈ L}` は非単位元を高々 1 つしか
含まず, したがって巡回群を生成する.

`H = {1, h}` 等なので, 3 つの引数のどれかが `1` なら三重交換子は `1`. 残るのは
`z = ⁅⁅h, k⁆, m⁆` ただ 1 つ. 生成する部分群はちょうど `⟨z⟩`. -/
theorem exists_closure_commutatorTriple_eq_zpowers {G : Type*} [Group G] {H K L : Subgroup G}
    (hH : Nat.card H = 2) (hK : Nat.card K = 2) (hL : Nat.card L = 2) :
    ∃ z : G, (∀ x ∈ H, ∀ y ∈ K, ∀ w ∈ L, ⁅⁅x, y⁆, w⁆ = 1 ∨ ⁅⁅x, y⁆, w⁆ = z) ∧
      Subgroup.closure {g : G | ∃ x ∈ H, ∃ y ∈ K, ∃ w ∈ L, ⁅⁅x, y⁆, w⁆ = g}
        = Subgroup.zpowers z := by
  obtain ⟨h, hhH, -, hHmem⟩ := exists_eq_one_or_eq_of_card_eq_two hH
  obtain ⟨k, hkK, -, hKmem⟩ := exists_eq_one_or_eq_of_card_eq_two hK
  obtain ⟨m, hmL, -, hLmem⟩ := exists_eq_one_or_eq_of_card_eq_two hL
  have hpair : ∀ x ∈ H, ∀ y ∈ K, ∀ w ∈ L, ⁅⁅x, y⁆, w⁆ = 1 ∨ ⁅⁅x, y⁆, w⁆ = ⁅⁅h, k⁆, m⁆ := by
    intro x hx y hy w hw
    rcases hHmem x hx with rfl | rfl
    · simp
    rcases hKmem y hy with rfl | rfl
    · simp
    rcases hLmem w hw with rfl | rfl
    · simp
    · exact Or.inr rfl
  refine ⟨⁅⁅h, k⁆, m⁆, hpair, le_antisymm (Subgroup.closure_le _ |>.2 ?_) ?_⟩
  · rintro g ⟨x, hx, y, hy, w, hw, rfl⟩
    rcases hpair x hx y hy w hw with hg | hg
    · exact hg ▸ one_mem _
    · exact hg ▸ Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure ⟨h, hhH, k, hkK, m, hmL, rfl⟩

section /- Problem 4A.2 の後半: `G = A₅` での実例 -/

open Equiv Equiv.Perm

/-- 5-サイクル `(0 1 2 3 4)`. -/
private def rot5 : Perm (Fin 5) := finRotate 5

/-- 対合 `(1 4)(2 3)`: `rot5` を反転する折り返し (`⟨rot5⟩` を正規化する). -/
private def invol0 : Perm (Fin 5) := swap 1 4 * swap 2 3

/-- 対合 `(0 2)(3 4) = rot5 · invol0 · rot5⁻¹`: `⟨rot5⟩` を正規化する別の折り返し. -/
private def invol1 : Perm (Fin 5) := swap 0 2 * swap 3 4

/-- 対合 `(0 1)(2 3)`: `⟨rot5⟩` を正規化しない. -/
private def invol2 : Perm (Fin 5) := swap 0 1 * swap 2 3

private def rot5A : alternatingGroup (Fin 5) := ⟨rot5, mem_alternatingGroup.2 (by decide)⟩
private def invol0A : alternatingGroup (Fin 5) := ⟨invol0, mem_alternatingGroup.2 (by decide)⟩
private def invol1A : alternatingGroup (Fin 5) := ⟨invol1, mem_alternatingGroup.2 (by decide)⟩
private def invol2A : alternatingGroup (Fin 5) := ⟨invol2, mem_alternatingGroup.2 (by decide)⟩

private lemma invol0A_sq : invol0A ^ 2 = 1 := Subtype.ext (by decide)
private lemma invol1A_sq : invol1A ^ 2 = 1 := Subtype.ext (by decide)
private lemma invol2A_sq : invol2A ^ 2 = 1 := Subtype.ext (by decide)

private lemma invol0A_ne_one : invol0A ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)
private lemma invol1A_ne_one : invol1A ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)
private lemma invol2A_ne_one : invol2A ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)

/-- `⁅invol0, invol1⁆ = rot5`: 二面体群 `D₁₀` の 2 つの折り返しの積は回転. -/
private lemma commutatorElement_invol0A_invol1A : ⁅invol0A, invol1A⁆ = rot5A :=
  Subtype.ext (by decide)

private lemma card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num
  decide

set_option maxRecDepth 8000 in
private lemma orderOf_commutatorElement_rot5A_invol2A : orderOf ⁅rot5A, invol2A⁆ = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine orderOf_eq_prime (Subtype.ext ?_) fun h => absurd (congrArg Subtype.val h) ?_
  · change ⁅rot5, invol2⁆ ^ 5 = 1
    decide
  · change ¬ (⁅rot5, invol2⁆ = 1)
    decide

set_option maxRecDepth 8000 in
private lemma orderOf_commutatorElement_rot5A_sq_invol2A : orderOf ⁅rot5A ^ 2, invol2A⁆ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine orderOf_eq_prime (Subtype.ext ?_) fun h => absurd (congrArg Subtype.val h) ?_
  · change ⁅rot5 ^ 2, invol2⁆ ^ 3 = 1
    decide
  · change ¬ (⁅rot5 ^ 2, invol2⁆ = 1)
    decide

set_option maxRecDepth 8000 in
private lemma orderOf_commutatorElement_mul :
    orderOf (⁅rot5A, invol2A⁆ * ⁅rot5A ^ 2, invol2A⁆) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (Subtype.ext ?_) fun h => absurd (congrArg Subtype.val h) ?_
  · change (⁅rot5, invol2⁆ * ⁅rot5 ^ 2, invol2⁆) ^ 2 = 1
    decide
  · change ¬ (⁅rot5, invol2⁆ * ⁅rot5 ^ 2, invol2⁆ = 1)
    decide

/-- `⁅⟨rot5⟩, ⟨invol2⟩⁆ = A₅`.

`N := ⁅⟨rot5⟩, ⟨invol2⟩⁆` は位数 5, 3, 2 の元 (`⁅rot5, invol2⁆`, `⁅rot5², invol2⁆` と
その積) を含むので `30 ∣ |N|`, また `|N| ∣ 60`. `|N| = 30` なら指数 2 = `(60).minFac` ゆえ
`N ⊴ A₅` となり, `A₅` の単純性に反する. よって `|N| = 60`, すなわち `N = ⊤`. -/
private lemma commutator_zpowers_rot5A_invol2A_eq_top :
    ⁅Subgroup.zpowers rot5A, Subgroup.zpowers invol2A⁆ = ⊤ := by
  set N := ⁅Subgroup.zpowers rot5A, Subgroup.zpowers invol2A⁆ with hNdef
  have hp : ⁅rot5A, invol2A⁆ ∈ N :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
  have hq : ⁅rot5A ^ 2, invol2A⁆ ∈ N :=
    Subgroup.commutator_mem_commutator (pow_mem (Subgroup.mem_zpowers _) 2) (Subgroup.mem_zpowers _)
  have h5 : (5 : ℕ) ∣ Nat.card N := by
    have hdvd := orderOf_dvd_natCard (⟨_, hp⟩ : ↥N)
    rwa [Subgroup.orderOf_mk, orderOf_commutatorElement_rot5A_invol2A] at hdvd
  have h3 : (3 : ℕ) ∣ Nat.card N := by
    have hdvd := orderOf_dvd_natCard (⟨_, hq⟩ : ↥N)
    rwa [Subgroup.orderOf_mk, orderOf_commutatorElement_rot5A_sq_invol2A] at hdvd
  have h2 : (2 : ℕ) ∣ Nat.card N := by
    have hdvd := orderOf_dvd_natCard (⟨_, mul_mem hp hq⟩ : ↥N)
    rwa [Subgroup.orderOf_mk, orderOf_commutatorElement_mul] at hdvd
  have h30 : (30 : ℕ) ∣ Nat.card N :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3) h5
  have h60 : Nat.card N ∣ 60 := by
    have := Subgroup.card_subgroup_dvd_card N
    rwa [card_alternatingGroup_five] at this
  have hcard : Nat.card N = 60 := by
    obtain ⟨j, hj⟩ := h30
    have hle : Nat.card N ≤ 60 := Nat.le_of_dvd (by norm_num) h60
    have hpos : 0 < Nat.card N := Nat.card_pos
    have hj2 : j ≤ 2 := by omega
    interval_cases j
    · omega
    · -- `|N| = 30` は指数 2, すなわち正規部分群になり単純性に反する
      exfalso
      have hcard30 : Nat.card N = 30 := by omega
      have hindex : N.index = 2 := by
        have hmul := Subgroup.index_mul_card N
        rw [hcard30, card_alternatingGroup_five] at hmul
        omega
      haveI : N.Normal := by
        refine Subgroup.normal_of_index_eq_minFac_card ?_
        rw [hindex, card_alternatingGroup_five]
        decide
      haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N inferInstance with hbot | htop
      · rw [hbot, Subgroup.card_bot] at hcard30; omega
      · rw [htop, Subgroup.card_top, card_alternatingGroup_five] at hcard30; omega
    · omega
  exact Subgroup.eq_top_of_card_eq _ (by rw [hcard, card_alternatingGroup_five])

/-- **Isaacs Problem 4A.2** (後半, 書籍 pp. 122-123): `G = A₅` には位数 2 の部分群
`H`, `K`, `L` で `⁅H, K, L⁆ = G` となるものが存在する. 一方 (前半より)
元の集合 `{⁅⁅x, y⁆, w⁆}` が生成する部分群は巡回群なので `G` にはならない.

⟹ **`⁅H, K, L⁆` は `⁅h, k, l⁆` の形の元で生成されるとは限らない** (書籍の Note).

取り方 (書籍の Hint どおり): `P = ⟨(0 1 2 3 4)⟩` (位数 5) の正規化群
`N_{A₅}(P) ≅ D₁₀` の中の相異なる 2 つの折り返し `H = ⟨(1 4)(2 3)⟩`, `K = ⟨(0 2)(3 4)⟩` を取ると
`⁅H, K⁆ = P` (折り返し 2 つの積は回転). `L = ⟨(0 1)(2 3)⟩` は `P` を正規化しないので
`⁅P, L⁆ ≠ 1` で, 実際 `⁅P, L⁆` は位数 5, 3, 2 の元を含み `A₅` の単純性から `= A₅`. -/
theorem exists_card_two_subgroups_commutator_triple_eq_top :
    ∃ H K L : Subgroup (alternatingGroup (Fin 5)),
      Nat.card H = 2 ∧ Nat.card K = 2 ∧ Nat.card L = 2 ∧ ⁅⁅H, K⁆, L⁆ = ⊤ ∧
      Subgroup.closure {g | ∃ x ∈ H, ∃ y ∈ K, ∃ w ∈ L, ⁅⁅x, y⁆, w⁆ = g} ≠ ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : ∀ a : alternatingGroup (Fin 5), a ^ 2 = 1 → a ≠ 1 →
      Nat.card (Subgroup.zpowers a) = 2 := by
    intro a ha ha1
    rw [Nat.card_zpowers, orderOf_eq_prime ha ha1]
  have hH := hcard invol0A invol0A_sq invol0A_ne_one
  have hK := hcard invol1A invol1A_sq invol1A_ne_one
  have hL := hcard invol2A invol2A_sq invol2A_ne_one
  refine ⟨_, _, _, hH, hK, hL, ?_, ?_⟩
  · rw [commutator_zpowers_eq_zpowers_commutatorElement invol0A_sq invol1A_sq,
      commutatorElement_invol0A_invol1A]
    exact commutator_zpowers_rot5A_invol2A_eq_top
  · intro htop
    obtain ⟨z, -, hz⟩ := exists_closure_commutatorTriple_eq_zpowers hH hK hL
    rw [hz] at htop
    have hmem : ∀ x : alternatingGroup (Fin 5), x ∈ Subgroup.zpowers z := by
      intro x; rw [htop]; exact Subgroup.mem_top x
    have hcyc : IsCyclic (alternatingGroup (Fin 5)) := ⟨z, hmem⟩
    have hle := alternatingGroup.isCyclic_iff_card_le_three.mp hcyc
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hle
    omega

end

/-! ### Problem 4A.3 — quasiquaternion 群の Schur 乗数は自明 -/

/-- 群 `Q` が **quasiquaternion** (Isaacs Problem 4A.3, 書籍 p. 123): `Q = CU` で
`C`, `U` は巡回部分群, `C ⊴ Q`, かつ `C ∩ U = Z(Q)`.

書籍の注意: 一般四元数群と半二面体群はこの条件を満たす.
`C ⊴ Q` ゆえ「`Q = CU` (積集合)」は `C ⊔ U = ⊤` と同値だが, ここでは書籍どおり積の形で書く. -/
def IsQuasiquaternion (Q : Type*) [Group Q] : Prop :=
  ∃ C U : Subgroup Q, C.Normal ∧ IsCyclic C ∧ IsCyclic U ∧
    (∀ q : Q, ∃ c ∈ C, ∃ u ∈ U, c * u = q) ∧ C ⊓ U = Subgroup.center Q

/-- 巡回部分群の生成元を, 部分群の元でなく群の元として取り出す. -/
private lemma exists_generator_mem {Q : Type*} [Group Q] {S : Subgroup Q} (hS : IsCyclic S) :
    ∃ s ∈ S, ∀ x ∈ S, ∃ n : ℤ, s ^ n = x := by
  obtain ⟨⟨s, hs⟩, hgen⟩ := hS.exists_generator
  refine ⟨s, hs, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hgen ⟨x, hx⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

/-- `S ≤ G ⧸ Z` の生成元 `s` を `g` に持ち上げておくと, `S` の引き戻しの元は `z * g ^ n`
(`z ∈ Z`) の形に書ける. -/
private lemma exists_mem_mul_zpow_of_mem_comap {G : Type*} [Group G] {Z : Subgroup G} [Z.Normal]
    {S : Subgroup (G ⧸ Z)} {s : G ⧸ Z} (hgen : ∀ y ∈ S, ∃ n : ℤ, s ^ n = y)
    {g : G} (hg : QuotientGroup.mk' Z g = s) {x : G} (hx : x ∈ S.comap (QuotientGroup.mk' Z)) :
    ∃ z ∈ Z, ∃ n : ℤ, x = z * g ^ n := by
  obtain ⟨n, hn⟩ := hgen _ (Subgroup.mem_comap.mp hx)
  refine ⟨x * (g ^ n)⁻¹, ?_, n, by group⟩
  rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hg, hn,
    mul_inv_cancel]

/-- 引き戻し部分群の位数は `|Z|` 倍: `|φ⁻¹(S)| = |S| · |Z|` (`φ : G ↠ G ⧸ Z`). -/
theorem card_comap_mk'_eq_mul {G : Type*} [Group G] [Finite G] {Z : Subgroup G} [Z.Normal]
    (S : Subgroup (G ⧸ Z)) :
    Nat.card (S.comap (QuotientGroup.mk' Z)) = Nat.card S * Nat.card Z := by
  have hsurj : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have h1 : Nat.card (S.comap (QuotientGroup.mk' Z)) * S.index = Nat.card G := by
    rw [← Subgroup.index_comap_of_surjective S hsurj]
    exact Subgroup.card_mul_index _
  have h2 : Nat.card S * S.index = Z.index := by
    rw [Subgroup.index_eq_card (H := Z)]
    exact Subgroup.card_mul_index S
  have h3 : Nat.card Z * Z.index = Nat.card G := Subgroup.card_mul_index Z
  have hne : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) ?_
  rw [h1, ← h3, ← h2]
  ring

/-- **Isaacs Problem 4A.3** (書籍 p. 123): `Z ≤ G' ∩ Z(G)` で `G ⧸ Z` が quasiquaternion なら
`Z = 1` — すなわち **quasiquaternion 群の Schur 乗数は自明** (書籍 Note).

証明 (書籍 Hint): `Ḡ = G ⧸ Z` の定義に現れる `C`, `U` の引き戻しを `A`, `B` とする.
- `A ⧸ Z ≅ C` は巡回で `Z ≤ Z(G)` なので `A = Z⟨a₀⟩`, したがって `A` は abelian (同様に `B`).
- `Ḡ = CU` を持ち上げて `G = AB`. ゆえに `A ⊓ B = Z(G)`: `A ⊓ B` の元は `A` とも `B` とも
  可換なので `G = AB` 全体と可換; 逆は中心の像が商の中心 `C ⊓ U` に入ることから.
- `A ⊴ G` は abelian で `G ⧸ A` は巡回 (`Ḡ ⧸ C` が `U` の像で生成される) なので Lem 4.6:
  `|G'| · |A ⊓ Z(G)| = |A|`, ここで `Z(G) = A ⊓ B ≤ A` ゆえ `|G'| · |Z(G)| = |A|`.
  同じことを `Ḡ` と `C` に適用して `|Ḡ'| · |Z(Ḡ)| = |C|`.
- 引き戻しの位数は `|Z|` 倍 (`A = comap C`, `Z(G) = comap Z(Ḡ)`, `G' = comap Ḡ'` — 最後は
  `Z ≤ G'` を使う) なので `|C| |Z| = (|Ḡ'| |Z|) (|Z(Ḡ)| |Z|) = |C| |Z|²`, ゆえに `|Z| = 1`. -/
theorem eq_bot_of_isQuasiquaternion_quotient {G : Type*} [Group G] [Finite G]
    (Z : Subgroup G) [Z.Normal] (hZcomm : Z ≤ commutator G)
    (hZcent : Z ≤ Subgroup.center G) (hQ : IsQuasiquaternion (G ⧸ Z)) : Z = ⊥ := by
  obtain ⟨C, U, hCnorm, hCcyc, hUcyc, hprod, hinf⟩ := hQ
  haveI := hCnorm
  set φ := QuotientGroup.mk' Z with hφ
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective Z
  set A := C.comap φ with hA
  set B := U.comap φ with hB
  haveI hAnorm : A.Normal := hCnorm.comap φ
  -- `Z` は `A`, `B` に含まれる (ker φ ≤ 引き戻し)
  have hZA : Z ≤ A := fun z hz => by
    simp only [hA, Subgroup.mem_comap]
    rw [show φ z = 1 by rw [hφ, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hz]
    exact one_mem C
  have hZB : Z ≤ B := fun z hz => by
    simp only [hB, Subgroup.mem_comap]
    rw [show φ z = 1 by rw [hφ, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hz]
    exact one_mem U
  -- 中心の元はすべての元と可換
  have hcent : ∀ z ∈ Z, ∀ y : G, Commute z y := fun z hz y =>
    (Subgroup.mem_center_iff.mp (hZcent hz) y).symm
  -- 生成元とその持ち上げ
  obtain ⟨c₀, hc₀C, hc₀gen⟩ := exists_generator_mem hCcyc
  obtain ⟨u₀, hu₀U, hu₀gen⟩ := exists_generator_mem hUcyc
  obtain ⟨a₀, ha₀⟩ := hsurj c₀
  obtain ⟨b₀, hb₀⟩ := hsurj u₀
  -- `A`, `B` の元の形
  have hAform : ∀ x ∈ A, ∃ z ∈ Z, ∃ n : ℤ, x = z * a₀ ^ n := fun x hx =>
    exists_mem_mul_zpow_of_mem_comap hc₀gen ha₀ hx
  have hBform : ∀ x ∈ B, ∃ z ∈ Z, ∃ n : ℤ, x = z * b₀ ^ n := fun x hx =>
    exists_mem_mul_zpow_of_mem_comap hu₀gen hb₀ hx
  -- `Z⟨g⟩` の形の元同士は可換
  have hcomm_form : ∀ (g : G) (z₁ z₂ : G), z₁ ∈ Z → z₂ ∈ Z → ∀ m n : ℤ,
      (z₁ * g ^ m) * (z₂ * g ^ n) = (z₂ * g ^ n) * (z₁ * g ^ m) := by
    intro g z₁ z₂ hz₁ hz₂ m n
    exact (Commute.mul_left (hcent z₁ hz₁ _)
      (Commute.mul_right (hcent z₂ hz₂ (g ^ m)).symm ((Commute.refl g).zpow_zpow m n))).eq
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    obtain ⟨z₁, hz₁, m, rfl⟩ := hAform x hx
    obtain ⟨z₂, hz₂, n, rfl⟩ := hAform y hy
    exact hcomm_form a₀ z₁ z₂ hz₁ hz₂ m n
  have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨z₁, hz₁, m, rfl⟩ := hBform x hx
    obtain ⟨z₂, hz₂, n, rfl⟩ := hBform y hy
    exact hcomm_form b₀ z₁ z₂ hz₁ hz₂ m n
  -- `G = AB`
  have hGAB : ∀ g : G, ∃ x ∈ A, ∃ y ∈ B, x * y = g := by
    intro g
    obtain ⟨c, hc, u, hu, hcu⟩ := hprod (φ g)
    obtain ⟨x, hx⟩ := hsurj c
    obtain ⟨y, hy⟩ := hsurj u
    have hxA : x ∈ A := by simp only [hA, Subgroup.mem_comap, hx]; exact hc
    have hyB : y ∈ B := by simp only [hB, Subgroup.mem_comap, hy]; exact hu
    have hz : g * (x * y)⁻¹ ∈ Z := by
      rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, ← hφ, map_mul, map_inv, map_mul, hx, hy,
        hcu, mul_inv_cancel]
    exact ⟨g * (x * y)⁻¹ * x, A.mul_mem (hZA hz) hxA, y, hyB, by group⟩
  -- `A ⊓ B = Z(G)`
  have hABcenter : A ⊓ B = Subgroup.center G := by
    refine le_antisymm (fun x hx => Subgroup.mem_center_iff.mpr fun g => ?_) (fun x hx => ?_)
    · obtain ⟨a, ha, b, hb, rfl⟩ := hGAB g
      rw [mul_assoc, hBab b hb x hx.2, ← mul_assoc, hAab a ha x hx.1, mul_assoc]
    · have hxc : φ x ∈ Subgroup.center (G ⧸ Z) := by
        refine Subgroup.mem_center_iff.mpr fun q => ?_
        obtain ⟨y, rfl⟩ := hsurj q
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
      rw [← hinf] at hxc
      exact ⟨Subgroup.mem_comap.mpr hxc.1, Subgroup.mem_comap.mpr hxc.2⟩
  -- `G ⧸ A` は巡回
  have hGAcyc : IsCyclic (G ⧸ A) := by
    refine ⟨(b₀ : G ⧸ A), fun x => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨a, ha, b, hb, rfl⟩ := hGAB g
    obtain ⟨z, hz, n, rfl⟩ := hBform b hb
    refine ⟨n, ?_⟩
    change ((b₀ : G ⧸ A)) ^ n = ((a * (z * b₀ ^ n) : G) : G ⧸ A)
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
    have : (b₀ ^ n)⁻¹ * (a * (z * b₀ ^ n)) = (b₀ ^ n)⁻¹ * (a * z) * b₀ ^ n := by group
    rw [this]
    exact hAnorm.conj_mem' _ (A.mul_mem ha (hZA hz)) _
  -- `Ḡ ⧸ C` は巡回
  have hGCcyc : IsCyclic ((G ⧸ Z) ⧸ C) := by
    refine ⟨(u₀ : (G ⧸ Z) ⧸ C), fun x => ?_⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨c, hc, u, hu, rfl⟩ := hprod q
    obtain ⟨n, rfl⟩ := hu₀gen u hu
    refine ⟨n, ?_⟩
    change ((u₀ : (G ⧸ Z) ⧸ C)) ^ n = ((c * u₀ ^ n : G ⧸ Z) : (G ⧸ Z) ⧸ C)
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
    have : (u₀ ^ n)⁻¹ * (c * u₀ ^ n) = (u₀ ^ n)⁻¹ * c * u₀ ^ n := by group
    rw [this]
    exact hCnorm.conj_mem' _ hc _
  -- Lem 4.6 を `G` と `Ḡ` に適用
  have hlem1 : Nat.card (commutator G) * Nat.card (Subgroup.center G) = Nat.card A := by
    have h := card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient
      (A := A) hAab hGAcyc
    rwa [show A ⊓ Subgroup.center G = Subgroup.center G by
      rw [← hABcenter]; exact inf_eq_right.mpr inf_le_left] at h
  have hlem2 : Nat.card (commutator (G ⧸ Z)) * Nat.card (Subgroup.center (G ⧸ Z))
      = Nat.card C := by
    have hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
      intro x hx y hy
      obtain ⟨m, rfl⟩ := hc₀gen x hx
      obtain ⟨n, rfl⟩ := hc₀gen y hy
      exact ((Commute.refl c₀).zpow_zpow m n).eq
    have h := card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient
      (A := C) hCab hGCcyc
    rwa [show C ⊓ Subgroup.center (G ⧸ Z) = Subgroup.center (G ⧸ Z) by
      rw [← hinf]; exact inf_eq_right.mpr inf_le_left] at h
  -- 引き戻しの位数関係
  have hcardA : Nat.card A = Nat.card C * Nat.card Z := card_comap_mk'_eq_mul C
  have hcardZG : Nat.card (Subgroup.center G)
      = Nat.card (Subgroup.center (G ⧸ Z)) * Nat.card Z := by
    rw [← card_comap_mk'_eq_mul (Subgroup.center (G ⧸ Z)), ← hinf, Subgroup.comap_inf, hABcenter]
  have hcardG' : Nat.card (commutator G) = Nat.card (commutator (G ⧸ Z)) * Nat.card Z := by
    rw [← card_comap_mk'_eq_mul (commutator (G ⧸ Z))]
    congr 1
    have hmap : (commutator G).map φ = commutator (G ⧸ Z) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hsurj, ← commutator_def]
    rw [← hmap, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZcomm]
  -- 位数の勘定
  have hkey : Nat.card C * Nat.card Z = Nat.card C * (Nat.card Z * Nat.card Z) := by
    calc Nat.card C * Nat.card Z = Nat.card A := hcardA.symm
      _ = Nat.card (commutator G) * Nat.card (Subgroup.center G) := hlem1.symm
      _ = (Nat.card (commutator (G ⧸ Z)) * Nat.card Z)
            * (Nat.card (Subgroup.center (G ⧸ Z)) * Nat.card Z) := by rw [hcardG', hcardZG]
      _ = (Nat.card (commutator (G ⧸ Z)) * Nat.card (Subgroup.center (G ⧸ Z)))
            * (Nat.card Z * Nat.card Z) := by ring
      _ = Nat.card C * (Nat.card Z * Nat.card Z) := by rw [hlem2]
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hZ1 : Nat.card Z = 1 := by
    have := Nat.eq_of_mul_eq_mul_left hCpos hkey
    nlinarith
  exact Subgroup.card_eq_one.mp hZ1

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

書籍が併記する同値形 `Z(P) = P' = Φ(P)` は下の
`frattini_eq_center_of_commutator_eq_center` (本結果 + Lem 4.5).

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

/-- **Isaacs Problem 4A.4** (書籍併記の同値形, p. 123): `P' = Z(P)` が位数 `p` の
`p`-群では `Φ(P) = Z(P)`, すなわち `Z(P) = P' = Φ(P)`.

`⊆`: 本問の主形 (`P/Z(P)` が elementary abelian) に Lem 4.5 forward
(`frattini_le_of_isElementaryAbelian_quotient_of_pgroup`) を適用.
`⊇`: `Z(P) = P' ≤ Φ(P)` (`commutator_le_frattini_of_pgroup`). -/
theorem frattini_eq_center_of_commutator_eq_center {p : ℕ} [Fact p.Prime]
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    (hcomm : commutator P = Subgroup.center P)
    (hcard : Nat.card (Subgroup.center P) = p) :
    frattini P = Subgroup.center P :=
  le_antisymm
    (frattini_le_of_isElementaryAbelian_quotient_of_pgroup hP
      (isElementaryAbelian_quotient_center_of_commutator_eq_center hcomm hcard))
    (hcomm ▸ commutator_le_frattini_of_pgroup hP)

/-- Isaacs の extraspecial の定義 (`p`-群で `P' = Z(P)` の位数が `p`) から, repo の
`OddOrder.GroupTheory.IsExtraspecial` 構造 (`Φ(P) = Z(P)` を field に持つ) を得る.

Problem 4A.4 (`frattini_eq_center_of_commutator_eq_center`) がちょうど不足フィールドを与える. -/
theorem isExtraspecial_of_commutator_eq_center {p : ℕ} [Fact p.Prime]
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    (hcomm : commutator P = Subgroup.center P)
    (hcard : Nat.card (Subgroup.center P) = p) :
    OddOrder.GroupTheory.IsExtraspecial p P :=
  { isPGroup := hP
    commutator_eq_center := hcomm
    frattini_eq_center := frattini_eq_center_of_commutator_eq_center hP hcomm hcard
    center_card := hcard }

end

end OddOrder.Isaacs.Ch04
