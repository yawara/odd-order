/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.ProblemsSupersolvable
import OddOrder.Isaacs.Ch04_Commutators.Mann

/-!
# Isaacs Chapter 4 — Problem 4B.5 (超可解群の `M(G)`)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4B.5 (書籍 p. 131)。

`G` が超可解なら **`M(G)` は冪零で類は `3` 以下**
(`nilpotencyClass_mannSubgroup_le_of_isSupersolvable`)。

Mann の **Theorem 4.15** (`nilpotencyClass_mannSubgroup_le_of_centralizer_eq_self`) は
「`G` が自己中心化する正規部分群 `K` (`C_G(K) = K`) を持つ」ことしか使わないので,
本問は **超可解群がそのような `K` を持つ**ことに帰着する
(`exists_normal_centralizer_eq_self_of_isSupersolvable`)。

## 超可解群の極大可換正規部分群は自己中心化

`A` を可換正規部分群のうち極大に取り `C := C_G(A)` とする。`A < C` なら `G ⧸ A` の中で
`C/A` に含まれる minimal normal 部分群 `M̄` を取ると, **超可解性から `|M̄|` は素数**
(Problem 3B.7(a)) なので `M̄` は巡回。その引き戻し `B` は `A ≤ Z(B)` (∵ `B ≤ C_G(A)`) かつ
`B/A ≅ M̄` 巡回ゆえ**可換** (`isMulCommutative_of_isCyclic_of_ker_le_center`) で
`A < B ⊴ G` — `A` の極大性に矛盾。
-/

namespace OddOrder.Isaacs.Ch04

open OddOrder.Isaacs.Ch03

open scoped commutatorElement

section /- Problem 4B.5 (p. 131) -/

variable {G : Type*} [Group G]

set_option backward.isDefEq.respectTransparency false in
/-- **超可解群の極大可換正規部分群は自己中心化する**.

したがって超可解群は Theorem 4.15 の仮説を満たす. -/
theorem exists_normal_centralizer_eq_self_of_isSupersolvable [Finite G]
    (hG : Ch03.IsSupersolvable G) :
    ∃ A : Subgroup G, A.Normal ∧ Subgroup.centralizer (A : Set G) = A := by
  classical
  -- 可換正規部分群のうち極大なもの
  obtain ⟨A, -, hAmax⟩ := Finite.exists_le_maximal (α := Subgroup G)
    (p := fun A : Subgroup G => A.Normal ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (a := ⊥) ⟨inferInstance, by simp⟩
  obtain ⟨hAnorm, hAab⟩ := hAmax.prop
  have := hAnorm
  refine ⟨A, hAnorm, ?_⟩
  set C : Subgroup G := Subgroup.centralizer (A : Set G) with hCdef
  have hCnorm : C.Normal := by
    rw [hCdef]
    exact Subgroup.normal_centralizer
  have hAC : A ≤ C := by
    rw [hCdef]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr fun b hb => (hAab b hb a ha)
  refine le_antisymm ?_ hAC
  by_contra hlt
  -- `C/A ≠ 1`
  have hne : C.map (QuotientGroup.mk' A) ≠ ⊥ := by
    intro hbot
    refine hlt ?_
    intro x hx
    have : (QuotientGroup.mk' A) x = 1 := by
      have hmem : (QuotientGroup.mk' A) x ∈ C.map (QuotientGroup.mk' A) := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  -- `C/A` 内の minimal normal 部分群
  obtain ⟨Mbar, hMmin, hMle⟩ :=
    Ch02.exists_isMinimalNormal_le_of_normal (C.map (QuotientGroup.mk' A)) hne
  have hMnorm : Mbar.Normal := hMmin.1
  have hprime : (Nat.card ↥Mbar).Prime :=
    Ch03.card_prime_of_isMinimalNormal_of_isSupersolvable (hG.quotient A) hMmin
  have : Fact (Nat.card ↥Mbar).Prime := ⟨hprime⟩
  have hMcyc : IsCyclic ↥Mbar := isCyclic_of_prime_card (p := Nat.card ↥Mbar) rfl
  -- 引き戻し `B`
  set B : Subgroup G := Mbar.comap (QuotientGroup.mk' A) with hBdef
  have hBnorm : B.Normal := by rw [hBdef]; infer_instance
  have hAB : A ≤ B := by
    rw [hBdef]
    intro a ha
    refine Subgroup.mem_comap.mpr ?_
    have h1 : (QuotientGroup.mk' A) a = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ha
    rw [h1]
    exact Subgroup.one_mem _
  have hBC : B ≤ C := by
    rw [hBdef]
    intro x hx
    have hxm : (QuotientGroup.mk' A) x ∈ C.map (QuotientGroup.mk' A) := hMle hx
    obtain ⟨c, hc, hceq⟩ := hxm
    have : c⁻¹ * x ∈ A := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, hceq]
      simp
    have := C.mul_mem hc (hAC this)
    simpa using this
  -- `B` は可換
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    have hker : ((QuotientGroup.mk' A).domRestrict B).ker ≤ Subgroup.center ↥B := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hxA : (x : G) ∈ A := by
        rwa [MonoidHom.domRestrict_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      rw [Subgroup.mem_center_iff]
      intro y
      refine Subtype.ext ?_
      have hy : (y : G) ∈ C := hBC y.2
      exact ((Subgroup.mem_centralizer_iff.mp (hCdef ▸ hy)) (x : G) hxA).symm
    have hcod : ∀ b : ↥B, ((QuotientGroup.mk' A).domRestrict B) b ∈ Mbar := fun b => b.2
    -- `B ⧸ A` は `M̄` の中に入るので巡回, かつ核 `A` は `Z(B)` に入る
    set f : ↥B →* ↥Mbar := ((QuotientGroup.mk' A).domRestrict B).codRestrict Mbar hcod with hfdef
    have hfker : f.ker ≤ Subgroup.center ↥B := by
      intro x hx
      refine hker ?_
      rw [MonoidHom.mem_ker] at hx ⊢
      exact congrArg Subtype.val hx
    have hcomm : IsMulCommutative ↥B :=
      f.isMulCommutative_of_isCyclic_of_ker_le_center hfker
    intro a ha b hb
    have := hcomm.is_comm.comm (⟨a, ha⟩ : ↥B) ⟨b, hb⟩
    exact congrArg Subtype.val this
  -- 極大性に矛盾
  have hBA : B ≤ A := hAmax.le_of_ge ⟨hBnorm, hBab⟩ hAB
  -- しかし `B/A = M̄ ≠ 1`
  have hMbot : Mbar = ⊥ := by
    have : Mbar = B.map (QuotientGroup.mk' A) := by
      rw [hBdef, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective A)]
    rw [this]
    refine le_bot_iff.mp ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hBA hx
  rw [hMbot] at hprime
  simp only [Subgroup.card_bot] at hprime
  exact Nat.not_prime_one hprime

/-- **Isaacs Problem 4B.5**: `G` が超可解なら `M(G)` は冪零で類は `3` 以下.

Theorem 4.15 は「自己中心化する正規部分群の存在」しか要らず, 超可解群では極大可換正規部分群が
それを与える (`exists_normal_centralizer_eq_self_of_isSupersolvable`). -/
theorem nilpotencyClass_mannSubgroup_le_of_isSupersolvable [Finite G]
    (hG : Ch03.IsSupersolvable G) :
    Group.nilpotencyClass ↥(mannSubgroup G) ≤ 3 := by
  obtain ⟨A, hAnorm, hself⟩ := exists_normal_centralizer_eq_self_of_isSupersolvable hG
  have := hAnorm
  exact nilpotencyClass_mannSubgroup_le_of_centralizer_eq_self hself

/-- **Isaacs Problem 4B.5** (冪零性): `G` 超可解なら `M(G)` は冪零. -/
theorem isNilpotent_mannSubgroup_of_isSupersolvable [Finite G]
    (hG : Ch03.IsSupersolvable G) :
    Group.IsNilpotent ↥(mannSubgroup G) := by
  obtain ⟨A, hAnorm, hself⟩ := exists_normal_centralizer_eq_self_of_isSupersolvable hG
  have := hAnorm
  exact isNilpotent_mannSubgroup_of_centralizer_eq_self hself

end

end OddOrder.Isaacs.Ch04
