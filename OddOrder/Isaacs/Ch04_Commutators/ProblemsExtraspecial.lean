/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.Problems

/-!
# Isaacs Chapter 4 — Problem 4A.5 (extraspecial `p`-群の構造)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4A.5 (書籍 pp. 123-124)。

`P` を extraspecial `p`-群, `x, y ∈ P` を `xy ≠ yx` なる元とし, `U = ⟨x, y⟩`,
`V = C_P(U)` とおく:

* (a) `|P : C_P(x)| = p`
* (b) `|U| = p³`
* (c) `|P : V| = p²`
* (d) `P > U` なら `Z(V) = Z(P)` かつ `V` は extraspecial
* (e) `|P : Z(P)| = p^{2e}` (ある整数 `e`)

道具立ての中心は **類 2 の交換子準同型** `g ↦ ⁅x, g⁆` (`commutatorLeftHom`): 核が `C_P(x)`,
像が `Z(P)` (位数 `p`) の部分群なので (a) が出る。中心積分解
`P = V · U` (`exists_mem_centralizer_mul_mem_closure_pair`) が (c)(d) の要で、
(d) の `Z(V) = Z(P)` はこれだけから (位数勘定なしで) 従う。

⚠ (a) は書籍の `xy ≠ yx` でなく `x ∉ Z(P)` を仮定 (同値だが一般形)、(d) の `Z(V) = Z(P)` も
`P > U` を使わずに成り立つ (書籍の仮定は後半の extraspecial 性のみで要る)。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement Pointwise

universe u

section /- Problem 4A.5: extraspecial p-groups (pp. 123-124) -/

variable {p : ℕ} {P : Type u} [Group P]

/-! ### 準備: 類 2 の群での交換子準同型 `g ↦ ⁅x, g⁆` -/

/-- **類 2 の左 commutator hom**: `P' ≤ Z(P)` のとき, `x` を固定した `g ↦ ⁅x, g⁆` は
準同型 `P →* P`.

`⁅x, g h⁆ = ⁅x, g⁆ · g ⁅x, h⁆ g⁻¹` (`commutatorElement_mul_right_eq_mul_conj`) で,
`⁅x, h⁆` は中心にあるから共役が消える. (既存の `commutatorRightHom` は逆側 `a ↦ ⁅a, g⁆`.) -/
def commutatorLeftHom (hcl : commutator P ≤ Subgroup.center P) (x : P) : P →* P where
  toFun g := ⁅x, g⁆
  map_one' := commutatorElement_one_right x
  map_mul' g h := by
    have hcen : ⁅x, h⁆ ∈ Subgroup.center P :=
      hcl (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top h))
    have hconj : g * ⁅x, h⁆ * g⁻¹ = ⁅x, h⁆ := by
      rw [Subgroup.mem_center_iff.mp hcen g, mul_assoc, mul_inv_cancel, mul_one]
    rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc, mul_assoc, ← mul_assoc g, hconj]

@[simp]
theorem commutatorLeftHom_apply (hcl : commutator P ≤ Subgroup.center P) (x g : P) :
    commutatorLeftHom hcl x g = ⁅x, g⁆ := rfl

/-- 左 commutator hom の核は `C_P(x)`. -/
theorem ker_commutatorLeftHom (hcl : commutator P ≤ Subgroup.center P) (x : P) :
    (commutatorLeftHom hcl x).ker = Subgroup.centralizer {x} := by
  ext g
  rw [MonoidHom.mem_ker, commutatorLeftHom_apply, commutatorElement_eq_one_iff_commute,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm.eq, fun h => Commute.symm h⟩

/-- 左 commutator hom の像は `P'` に含まれる. -/
theorem range_commutatorLeftHom_le_commutator (hcl : commutator P ≤ Subgroup.center P) (x : P) :
    (commutatorLeftHom hcl x).range ≤ commutator P := by
  rintro _ ⟨g, rfl⟩
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top g)

/-- 類 2 の群での右分配則 `⁅a, b c⁆ = ⁅a, b⁆ ⁅a, c⁆`. -/
theorem commutatorElement_mul_right_of_commutator_le_center
    (hcl : commutator P ≤ Subgroup.center P) (a b c : P) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ :=
  map_mul (commutatorLeftHom hcl a) b c

/-- 類 2 の群での `⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹`. -/
theorem commutatorElement_inv_right_of_commutator_le_center
    (hcl : commutator P ≤ Subgroup.center P) (a b : P) : ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ :=
  map_inv (commutatorLeftHom hcl a) b

/-- 類 2 の群での `⁅a, b ^ n⁆ = ⁅a, b⁆ ^ n` (`n : ℤ`). -/
theorem commutatorElement_zpow_right_of_commutator_le_center
    (hcl : commutator P ≤ Subgroup.center P) (a b : P) (n : ℤ) : ⁅a, b ^ n⁆ = ⁅a, b⁆ ^ n :=
  map_zpow (commutatorLeftHom hcl a) b n

/-! ### (a) `|P : C_P(x)| = p` -/

/-- **Isaacs Problem 4A.5(a)** (書籍 p. 123): `P` が extraspecial で `x ∉ Z(P)` なら
`|P : C_P(x)| = p`.

`g ↦ ⁅x, g⁆` の核は `C_P(x)`, 像は `P' = Z(P)` (位数 `p`) の部分群で, `x ∉ Z(P)` ゆえ
自明でない. 位数 `p` は素数なので像はちょうど `Z(P)`, したがって指数は `p`. -/
theorem index_centralizer_eq_of_not_mem_center [Finite P] [Fact p.Prime]
    (hP : OddOrder.GroupTheory.IsExtraspecial p P) {x : P} (hx : x ∉ Subgroup.center P) :
    (Subgroup.centralizer {x}).index = p := by
  have hcl : commutator P ≤ Subgroup.center P := le_of_eq hP.commutator_eq_center
  have hdvd : Nat.card (commutatorLeftHom hcl x).range ∣ p := by
    rw [← hP.center_card, ← hP.commutator_eq_center]
    exact Subgroup.card_dvd_of_le (range_commutatorLeftHom_le_commutator hcl x)
  have hne : Nat.card (commutatorLeftHom hcl x).range ≠ 1 := by
    intro hone
    apply hx
    have hbot : (commutatorLeftHom hcl x).range = ⊥ := Subgroup.card_eq_one.mp hone
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    have : ⁅x, g⁆ = 1 := by
      have hmem : ⁅x, g⁆ ∈ (commutatorLeftHom hcl x).range := ⟨g, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    exact ((commutatorElement_eq_one_iff_commute.mp this).symm).eq
  rw [← ker_commutatorLeftHom hcl x, Subgroup.index_ker]
  exact ((Nat.Prime.eq_one_or_self_of_dvd Fact.out _ hdvd).resolve_left hne)

/-! ### (b) `|U| = p³` -/

/-- 中心の非単位元は `Z(P)` を生成する (`|Z(P)| = p` が素数だから). -/
private theorem zpowers_eq_center_of_mem_of_ne_one [Finite P] [Fact p.Prime]
    (hcard : Nat.card (Subgroup.center P) = p) {c : P} (hc : c ∈ Subgroup.center P)
    (hc1 : c ≠ 1) : Subgroup.zpowers c = Subgroup.center P := by
  have hle : Subgroup.zpowers c ≤ Subgroup.center P := Subgroup.zpowers_le.mpr hc
  have hdvd : Nat.card (Subgroup.zpowers c) ∣ p := hcard ▸ Subgroup.card_dvd_of_le hle
  have hne : Nat.card (Subgroup.zpowers c) ≠ 1 := fun h =>
    Subgroup.zpowers_eq_bot.mp (Subgroup.card_eq_one.mp h) |> hc1
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, (Nat.Prime.eq_one_or_self_of_dvd Fact.out _ hdvd).resolve_left hne]

/-- `P` の商 `P ⧸ Z(P)` での位数 `p` の元: `x ∉ Z(P)` なら `⟨x̄⟩` の位数は `p`. -/
private theorem orderOf_mk_eq_of_not_mem_center [Finite P] [Fact p.Prime]
    (hP : OddOrder.GroupTheory.IsExtraspecial p P) {x : P} (hx : x ∉ Subgroup.center P) :
    orderOf ((x : P ⧸ Subgroup.center P)) = p := by
  have helem := isElementaryAbelian_quotient_center_of_commutator_eq_center
    hP.commutator_eq_center hP.center_card
  refine orderOf_eq_prime (helem.pow_eq_one _) ?_
  rw [Ne, QuotientGroup.eq_one_iff]
  exact hx

/-- **Isaacs Problem 4A.5(b)** (書籍 p. 123): `P` が extraspecial で `xy ≠ yx` なら
`|⟨x, y⟩| = p³`.

`c = ⁅x, y⁆ ≠ 1` は `P' = Z(P)` の非単位元ゆえ `Z(P) = ⟨c⟩ ≤ U`. 商 `P ⧸ Z(P)` は
elementary abelian で, `x̄`, `ȳ` はどちらも位数 `p`, かつ `⟨x̄⟩ ∩ ⟨ȳ⟩ = 1`
(`x̄ ∈ ⟨ȳ⟩` なら `x ∈ ⟨y⟩ Z(P)` となり `x`, `y` が可換). ゆえに `U` の像は位数 `p²`,
引き戻して `|U| = p³`. -/
theorem card_closure_pair_eq [Finite P] [Fact p.Prime]
    (hP : OddOrder.GroupTheory.IsExtraspecial p P) {x y : P} (hxy : x * y ≠ y * x) :
    Nat.card (Subgroup.closure {x, y}) = p ^ 3 := by
  have helem := isElementaryAbelian_quotient_center_of_commutator_eq_center
    hP.commutator_eq_center hP.center_card
  set Z := Subgroup.center P with hZ
  set U := Subgroup.closure ({x, y} : Set P) with hU
  have hxZ : x ∉ Z := fun h => hxy (Subgroup.mem_center_iff.mp h y).symm
  have hyZ : y ∉ Z := fun h => hxy (Subgroup.mem_center_iff.mp h x)
  -- `Z ≤ U`
  have hc1 : ⁅x, y⁆ ≠ 1 := fun h => hxy (commutatorElement_eq_one_iff_commute.mp h).eq
  have hcZ : ⁅x, y⁆ ∈ Z := by
    rw [hZ, ← hP.commutator_eq_center]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  have hcU : ⁅x, y⁆ ∈ U := by
    have hxU : x ∈ U := Subgroup.subset_closure (by simp)
    have hyU : y ∈ U := Subgroup.subset_closure (by simp)
    exact U.mul_mem (U.mul_mem (U.mul_mem hxU hyU) (U.inv_mem hxU)) (U.inv_mem hyU)
  have hZU : Z ≤ U := by
    rw [hZ, ← zpowers_eq_center_of_mem_of_ne_one (P := P) hP.center_card hcZ hc1,
      Subgroup.zpowers_le]
    exact hcU
  -- 商での像
  have hUsup : U = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [hU, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.singleton_union]
  have hmapU : U.map (QuotientGroup.mk' Z)
      = Subgroup.zpowers ((x : P ⧸ Z)) ⊔ Subgroup.zpowers ((y : P ⧸ Z)) := by
    rw [hUsup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    simp only [QuotientGroup.mk'_apply]
  have hcardx : Nat.card (Subgroup.zpowers ((x : P ⧸ Z))) = p := by
    rw [Nat.card_zpowers, orderOf_mk_eq_of_not_mem_center hP hxZ]
  have hcardy : Nat.card (Subgroup.zpowers ((y : P ⧸ Z))) = p := by
    rw [Nat.card_zpowers, orderOf_mk_eq_of_not_mem_center hP hyZ]
  -- `⟨x̄⟩ ⊓ ⟨ȳ⟩ = ⊥`
  have hinf : Subgroup.zpowers ((x : P ⧸ Z)) ⊓ Subgroup.zpowers ((y : P ⧸ Z)) = ⊥ := by
    by_contra hcon
    have hdvd : Nat.card (Subgroup.zpowers ((x : P ⧸ Z)) ⊓ Subgroup.zpowers ((y : P ⧸ Z)) :
        Subgroup (P ⧸ Z)) ∣ p := hcardx ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne1 : Nat.card (Subgroup.zpowers ((x : P ⧸ Z)) ⊓ Subgroup.zpowers ((y : P ⧸ Z)) :
        Subgroup (P ⧸ Z)) ≠ 1 := fun h => hcon (Subgroup.card_eq_one.mp h)
    have hcard_inf : Nat.card (Subgroup.zpowers ((x : P ⧸ Z)) ⊓ Subgroup.zpowers ((y : P ⧸ Z)) :
        Subgroup (P ⧸ Z)) = p :=
      (Nat.Prime.eq_one_or_self_of_dvd Fact.out _ hdvd).resolve_left hne1
    have heq : Subgroup.zpowers ((x : P ⧸ Z)) ⊓ Subgroup.zpowers ((y : P ⧸ Z))
        = Subgroup.zpowers ((x : P ⧸ Z)) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardx, hcard_inf])
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (Subgroup.zpowers_le.mp (heq ▸ (inf_le_right :
        Subgroup.zpowers ((x : P ⧸ Z)) ⊓ Subgroup.zpowers ((y : P ⧸ Z))
          ≤ Subgroup.zpowers ((y : P ⧸ Z)))))
    -- `x̄ = ȳ ^ n` ⟹ `x (y^n)⁻¹ ∈ Z(P)` ⟹ `x`, `y` は可換
    have hxz : x * (y ^ n)⁻¹ ∈ Z := by
      rw [hZ, ← QuotientGroup.eq_one_iff]
      have hone : ((x : P ⧸ Z)) * (((y : P ⧸ Z)) ^ n)⁻¹ = 1 := by rw [hn, mul_inv_cancel]
      simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow] using hone
    apply hxy
    have hcomm : Commute (x * (y ^ n)⁻¹) y := (Subgroup.mem_center_iff.mp hxz y).symm
    have hxeq : x = x * (y ^ n)⁻¹ * y ^ n := by group
    calc x * y = (x * (y ^ n)⁻¹ * y ^ n) * y := by rw [← hxeq]
      _ = y * (x * (y ^ n)⁻¹ * y ^ n) :=
          (Commute.mul_left hcomm ((Commute.refl y).zpow_left n)).eq
      _ = y * x := by rw [← hxeq]
  -- 位数を数える
  have hcardmap : Nat.card (U.map (QuotientGroup.mk' Z)) = p ^ 2 := by
    have hnormy : (Subgroup.zpowers ((y : P ⧸ Z))).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hgn : g * n * g⁻¹ = n := by rw [helem.comm g n, mul_assoc, mul_inv_cancel, mul_one]
      rwa [hgn]
    have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card
      (Subgroup.zpowers ((x : P ⧸ Z))) (Subgroup.zpowers ((y : P ⧸ Z)))
    rw [hinf, Subgroup.card_bot, mul_one, hcardx, hcardy] at hprod
    have hsetcard : Nat.card (U.map (QuotientGroup.mk' Z))
        = Nat.card ((Subgroup.zpowers ((x : P ⧸ Z)) : Set (P ⧸ Z)) *
            (Subgroup.zpowers ((y : P ⧸ Z)) : Set (P ⧸ Z))) := by
      rw [hmapU, ← Subgroup.mul_normal]
      rfl
    rw [hsetcard, hprod]
    ring
  have hcomapU : (U.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) = U := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZU]
  calc Nat.card U = Nat.card ((U.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z)) := by
        rw [hcomapU]
    _ = Nat.card (U.map (QuotientGroup.mk' Z)) * Nat.card Z := card_comap_mk'_eq_mul _
    _ = p ^ 3 := by rw [hcardmap, hZ, hP.center_card]; ring

/-! ### `V = C_P(U)` と中心積分解 `P = V · U` -/

/-- `C_P(⟨x, y⟩) = C_P(x) ⊓ C_P(y)`. -/
theorem centralizer_closure_pair (x y : P) :
    Subgroup.centralizer ((Subgroup.closure {x, y} : Subgroup P) : Set P)
      = Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y} := by
  rw [Subgroup.centralizer_closure]
  ext g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨(h x (by simp)).symm, (h y (by simp)).symm⟩
  · rintro ⟨hx, hy⟩ h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl
    · exact hx.symm
    · exact hy.symm

/-- **中心積分解** `P = V · U` (`U = ⟨x, y⟩`, `V = C_P(U)`).

`⁅x, g⁆ = c^i` (`c = ⁅x, y⁆` が `Z(P)` を生成) となる `i` を取ると `g (y^i)⁻¹ ∈ C_P(x)`,
さらに `⁅y, g (y^i)⁻¹⁆ = c^j` から `g (y^i)⁻¹ x^j ∈ C_P(x) ⊓ C_P(y) = V`. -/
theorem exists_mem_centralizer_mul_mem_closure_pair [Finite P] [Fact p.Prime]
    (hP : OddOrder.GroupTheory.IsExtraspecial p P) {x y : P} (hxy : x * y ≠ y * x) (g : P) :
    ∃ v ∈ Subgroup.centralizer ((Subgroup.closure {x, y} : Subgroup P) : Set P),
      ∃ u ∈ Subgroup.closure ({x, y} : Set P), v * u = g := by
  have hcl : commutator P ≤ Subgroup.center P := le_of_eq hP.commutator_eq_center
  have hc1 : ⁅x, y⁆ ≠ 1 := fun h => hxy (commutatorElement_eq_one_iff_commute.mp h).eq
  have hcZ : ⁅x, y⁆ ∈ Subgroup.center P := by
    rw [← hP.commutator_eq_center]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  have hzp : Subgroup.zpowers ⁅x, y⁆ = Subgroup.center P :=
    zpowers_eq_center_of_mem_of_ne_one hP.center_card hcZ hc1
  have hmemZ : ∀ a b : P, ⁅a, b⁆ ∈ Subgroup.zpowers ⁅x, y⁆ := fun a b => by
    rw [hzp, ← hP.commutator_eq_center]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  -- `⁅x, g⁆ = c ^ i`
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hmemZ x g)
  set g₁ := g * (y ^ i)⁻¹ with hg₁
  have hxg₁ : ⁅x, g₁⁆ = 1 := by
    rw [hg₁, commutatorElement_mul_right_of_commutator_le_center hcl x g (y ^ i)⁻¹,
      commutatorElement_inv_right_of_commutator_le_center hcl x (y ^ i),
      commutatorElement_zpow_right_of_commutator_le_center hcl x y i, ← hi, mul_inv_cancel]
  -- `⁅y, g₁⁆ = c ^ j`
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hmemZ y g₁)
  set v := g₁ * x ^ j with hv
  have hxv : ⁅x, v⁆ = 1 := by
    rw [hv, commutatorElement_mul_right_of_commutator_le_center hcl x g₁ (x ^ j), hxg₁,
      commutatorElement_zpow_right_of_commutator_le_center hcl x x j, commutatorElement_self,
      one_zpow, mul_one]
  have hyv : ⁅y, v⁆ = 1 := by
    have hyx : ⁅y, x⁆ = ⁅x, y⁆⁻¹ := (commutatorElement_inv x y).symm
    rw [hv, commutatorElement_mul_right_of_commutator_le_center hcl y g₁ (x ^ j), ← hj,
      commutatorElement_zpow_right_of_commutator_le_center hcl y x j, hyx, inv_zpow,
      mul_inv_cancel]
  refine ⟨v, ?_, (x ^ j)⁻¹ * y ^ i, ?_, by rw [hv, hg₁]; group⟩
  · rw [centralizer_closure_pair, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨((commutatorElement_eq_one_iff_commute.mp hxv).symm).eq,
      ((commutatorElement_eq_one_iff_commute.mp hyv).symm).eq⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _
      (Subgroup.subset_closure (by simp)) j))
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) i)

/-- `U ⊓ V = Z(P)`: `U` と `V = C_P(U)` の共通部分はちょうど中心 (`P = V · U` を使う). -/
theorem inf_centralizer_closure_pair_eq_center [Finite P] [Fact p.Prime]
    (hP : OddOrder.GroupTheory.IsExtraspecial p P) {x y : P} (hxy : x * y ≠ y * x) :
    (Subgroup.closure ({x, y} : Set P))
        ⊓ Subgroup.centralizer ((Subgroup.closure {x, y} : Subgroup P) : Set P)
      = Subgroup.center P := by
  refine le_antisymm (fun w hw => Subgroup.mem_center_iff.mpr fun g => ?_) (fun z hz => ?_)
  · obtain ⟨v, hvV, u, huU, rfl⟩ := exists_mem_centralizer_mul_mem_closure_pair hP hxy g
    -- `w ∈ U` は `v ∈ V = C_P(U)` と可換, `w ∈ V` は `u ∈ U` と可換
    have hwv : v * w = w * v := (hvV w hw.1).symm
    have hwu : u * w = w * u := hw.2 u huU
    rw [mul_assoc, hwu, ← mul_assoc, hwv, mul_assoc]
  · have hzU : z ∈ Subgroup.closure ({x, y} : Set P) := by
      have hc1 : ⁅x, y⁆ ≠ 1 := fun h => hxy (commutatorElement_eq_one_iff_commute.mp h).eq
      have hcZ : ⁅x, y⁆ ∈ Subgroup.center P := by
        rw [← hP.commutator_eq_center]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      have hzp := zpowers_eq_center_of_mem_of_ne_one hP.center_card hcZ hc1
      rw [← hzp] at hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact Subgroup.zpow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))) n
    exact ⟨hzU, fun h _ => (Subgroup.mem_center_iff.mp hz h)⟩

/-! ### (c) `|P : V| = p²` -/

/-- **Isaacs Problem 4A.5(c)** (書籍 p. 123): `|P : C_P(U)| = p²`.

`P = V · U` (集合として) と `U ⊓ V = Z(P)` (位数 `p`), `|U| = p³` (b) を
`|VU| · |V ⊓ U| = |V| · |U|` に入れると `|P| = |V| p²`. -/
theorem index_centralizer_closure_pair_eq [Finite P] [Fact p.Prime]
    (hP : OddOrder.GroupTheory.IsExtraspecial p P) {x y : P} (hxy : x * y ≠ y * x) :
    (Subgroup.centralizer ((Subgroup.closure {x, y} : Subgroup P) : Set P)).index = p ^ 2 := by
  set U := Subgroup.closure ({x, y} : Set P) with hU
  set V := Subgroup.centralizer ((Subgroup.closure {x, y} : Subgroup P) : Set P) with hV
  have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card V U
  -- `V · U = P` (集合)
  have hset : ((V : Set P) * (U : Set P)) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨v, hvV, u, huU, rfl⟩ := exists_mem_centralizer_mul_mem_closure_pair hP hxy g
    exact ⟨v, hvV, u, huU, rfl⟩
  have hinfZ : V ⊓ U = Subgroup.center P := by
    rw [inf_comm]; exact inf_centralizer_closure_pair_eq_center hP hxy
  rw [hset, hinfZ, hP.center_card, card_closure_pair_eq hP hxy] at hprod
  have hcardP : Nat.card (Set.univ : Set P) = Nat.card P := Nat.card_congr (Equiv.Set.univ P)
  rw [hcardP] at hprod
  -- `|P| · p = |V| · p³` ⟹ `|P| = |V| · p²`
  have hVindex : Nat.card V * V.index = Nat.card P := Subgroup.card_mul_index V
  have hp0 : 0 < p := Nat.Prime.pos Fact.out
  have hcancel : Nat.card V * V.index = Nat.card V * p ^ 2 := by
    rw [hVindex]
    have : Nat.card P * p = Nat.card V * p ^ 2 * p := by rw [hprod]; ring
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  have hVpos : 0 < Nat.card V := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hVpos hcancel

/-! ### (d) `Z(V) = Z(P)` と `V` の extraspecial 性 -/

/-- **Isaacs Problem 4A.5(d)** (前半, 書籍 p. 123): `Z(C_P(U)) = Z(P)`.

`P = V · U` なので, `V` の中心の元は `V` とも `U` とも可換, ゆえに `P` の中心にある.
逆に `Z(P) ≤ V` で, それは `V` の中心に入る. (`P > U` は不要.) -/
theorem map_center_centralizer_eq_center [Finite P] [Fact p.Prime]
    (hP : OddOrder.GroupTheory.IsExtraspecial p P) {x y : P} (hxy : x * y ≠ y * x) :
    (Subgroup.center (Subgroup.centralizer
        ((Subgroup.closure {x, y} : Subgroup P) : Set P))).map
      (Subgroup.centralizer ((Subgroup.closure {x, y} : Subgroup P) : Set P)).subtype
      = Subgroup.center P := by
  set V := Subgroup.centralizer ((Subgroup.closure {x, y} : Subgroup P) : Set P) with hV
  refine le_antisymm ?_ (fun z hz => ?_)
  · rintro _ ⟨w, hw, rfl⟩
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨v, hvV, u, huU, rfl⟩ := exists_mem_centralizer_mul_mem_closure_pair hP hxy g
    have hwv : v * (w : P) = (w : P) * v := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hw ⟨v, hvV⟩)
    have hwu : u * (w : P) = (w : P) * u := w.2 u huU
    change v * u * (w : P) = (w : P) * (v * u)
    rw [mul_assoc, hwu, ← mul_assoc, hwv, mul_assoc]
  · -- `Z(P) ≤ V` かつ `V` の中心に入る
    have hzV : z ∈ V := fun h _ => (Subgroup.mem_center_iff.mp hz h)
    refine ⟨⟨z, hzV⟩, Subgroup.mem_center_iff.mpr fun w => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz (w : P))

/-- **Isaacs Problem 4A.5(d)** (後半, 書籍 p. 123): `P > U` なら `V = C_P(U)` も extraspecial.

`V` は `p`-群で `Z(V) = Z(P)` は位数 `p`. `V` が abelian なら `V ≤ Z(V) = Z(P) ≤ U` となり
`P = V·U = U` で `P > U` に矛盾するので `V' ≠ 1`. `V' ≤ P' = Z(P) = Z(V)` は位数 `p` の
素数位数群ゆえ `V' = Z(V)`. -/
theorem isExtraspecial_centralizer_closure_pair [Finite P] [Fact p.Prime]
    (hP : OddOrder.GroupTheory.IsExtraspecial p P) {x y : P} (hxy : x * y ≠ y * x)
    (hlt : Subgroup.closure ({x, y} : Set P) ≠ ⊤) :
    OddOrder.GroupTheory.IsExtraspecial p
      (Subgroup.centralizer ((Subgroup.closure {x, y} : Subgroup P) : Set P)) := by
  set U := Subgroup.closure ({x, y} : Set P) with hU
  set V := Subgroup.centralizer ((Subgroup.closure {x, y} : Subgroup P) : Set P) with hV
  have hmapZ := map_center_centralizer_eq_center hP hxy
  -- `|Z(V)| = p`
  have hcardZV : Nat.card (Subgroup.center V) = p := by
    have : Nat.card ((Subgroup.center V).map V.subtype) = Nat.card (Subgroup.center V) :=
      Nat.card_congr (Equiv.Set.image _ _ Subtype.val_injective).symm
    rw [← hP.center_card, ← hmapZ, this]
  -- `V' ≤ Z(V)`
  have hVcomm_le : commutator V ≤ Subgroup.center V := by
    rw [← Subgroup.map_le_map_iff_of_injective (f := V.subtype) Subtype.val_injective, hmapZ,
      ← hP.commutator_eq_center]
    rw [Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_mono le_top le_top
  -- `V` は abelian でない
  have hVcomm_ne : commutator V ≠ ⊥ := by
    intro hbot
    apply hlt
    -- `V ≤ Z(P)` ⟹ `V ≤ U` ⟹ `P = V·U = U`
    have hVZ : ∀ v : V, (v : P) ∈ Subgroup.center P := by
      intro v
      have hvc : v ∈ Subgroup.center V := by
        refine Subgroup.mem_center_iff.mpr fun w => ?_
        have hmem : ⁅w, v⁆ ∈ commutator V :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top w) (Subgroup.mem_top v)
        rw [hbot, Subgroup.mem_bot] at hmem
        exact (commutatorElement_eq_one_iff_commute.mp hmem).eq
      have hmemmap : (v : P) ∈ (Subgroup.center V).map V.subtype := ⟨v, hvc, rfl⟩
      rwa [hmapZ] at hmemmap
    have hZU : Subgroup.center P ≤ U := by
      rw [← inf_centralizer_closure_pair_eq_center hP hxy]
      exact inf_le_left
    refine eq_top_iff.mpr fun g _ => ?_
    obtain ⟨v, hvV, u, huU, rfl⟩ := exists_mem_centralizer_mul_mem_closure_pair hP hxy g
    exact Subgroup.mul_mem _ (hZU (hVZ ⟨v, hvV⟩)) huU
  -- `V' = Z(V)`
  have hVcomm : commutator V = Subgroup.center V := by
    refine Subgroup.eq_of_le_of_card_ge hVcomm_le ?_
    have hdvd : Nat.card (commutator V) ∣ p :=
      hcardZV ▸ Subgroup.card_dvd_of_le hVcomm_le
    have hne : Nat.card (commutator V) ≠ 1 := fun h => hVcomm_ne (Subgroup.card_eq_one.mp h)
    rw [hcardZV, (Nat.Prime.eq_one_or_self_of_dvd Fact.out _ hdvd).resolve_left hne]
  exact isExtraspecial_of_commutator_eq_center (hP.isPGroup.to_subgroup V) hVcomm hcardZV

/-! ### (e) `|P : Z(P)| = p^{2e}` -/

/-- (e) の帰納法本体: `|Q| = n` に関する強帰納法. -/
private theorem exists_index_center_eq_aux [Fact p.Prime] (n : ℕ) :
    ∀ {Q : Type u} [Group Q] [Finite Q], Nat.card Q = n →
      OddOrder.GroupTheory.IsExtraspecial p Q →
      ∃ e : ℕ, (Subgroup.center Q).index = p ^ (2 * e) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q _ _ hcard hQ
    -- `Q` は非可換: `Q' = Z(Q)` は位数 `p > 1`
    obtain ⟨x, y, hxy⟩ : ∃ x y : Q, x * y ≠ y * x := by
      by_contra hcon
      have hcomm : ∀ a b : Q, a * b = b * a := fun a b => by
        by_contra hab
        exact hcon ⟨a, b, hab⟩
      have hbot : commutator Q = ⊥ := by
        rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact fun g _ h _ => hcomm h g
      have hone := hQ.center_card
      rw [← hQ.commutator_eq_center, hbot, Subgroup.card_bot] at hone
      exact (Nat.Prime.one_lt (Fact.out : p.Prime)).ne hone
    have hpcard : Nat.card (Subgroup.center Q) = p := hQ.center_card
    have hp1 : 1 < p := Nat.Prime.one_lt Fact.out
    by_cases hU : Subgroup.closure ({x, y} : Set Q) = ⊤
    · -- `Q = ⟨x, y⟩`: (b) より `|Q| = p³`, ゆえに指数は `p² = p^(2·1)`
      refine ⟨1, ?_⟩
      have hcube : Nat.card Q = p ^ 3 := by
        rw [← card_closure_pair_eq hQ hxy, hU, Subgroup.card_top]
      have hmul := Subgroup.card_mul_index (Subgroup.center Q)
      rw [hpcard, hcube] at hmul
      have hcancel : p * (Subgroup.center Q).index = p * p ^ 2 := by rw [hmul]; ring
      rw [Nat.eq_of_mul_eq_mul_left (Nat.Prime.pos Fact.out) hcancel]
    · -- `Q > ⟨x, y⟩`: `V = C_Q(U)` は extraspecial で `|V| < |Q|`
      set V := Subgroup.centralizer ((Subgroup.closure {x, y} : Subgroup Q) : Set Q) with hV
      have hVex : OddOrder.GroupTheory.IsExtraspecial p V :=
        isExtraspecial_centralizer_closure_pair hQ hxy hU
      have hVindex : V.index = p ^ 2 := index_centralizer_closure_pair_eq hQ hxy
      have hVmul : Nat.card V * p ^ 2 = Nat.card Q := by
        rw [← hVindex]; exact Subgroup.card_mul_index V
      have hVlt : Nat.card V < n := by
        rw [← hcard, ← hVmul]
        have hVpos : 0 < Nat.card V := Nat.card_pos
        nlinarith [Nat.one_lt_pow (n := 2) (by norm_num) hp1]
      obtain ⟨e, he⟩ := ih (Nat.card V) hVlt rfl hVex
      refine ⟨e + 1, ?_⟩
      -- `p · [Q : Z(Q)] = |Q| = |V| p² = (p · p^{2e}) p²`
      have hVcard : Nat.card V = p * p ^ (2 * e) := by
        have := Subgroup.card_mul_index (Subgroup.center V)
        rw [hVex.center_card, he] at this
        exact this.symm
      have hmul := Subgroup.card_mul_index (Subgroup.center Q)
      rw [hpcard, ← hVmul, hVcard] at hmul
      have : p * (Subgroup.center Q).index = p * p ^ (2 * (e + 1)) := by
        rw [hmul]; ring
      exact Nat.eq_of_mul_eq_mul_left (Nat.Prime.pos Fact.out) this

/-- **Isaacs Problem 4A.5(e)** (書籍 p. 124): extraspecial `p`-群では `|P : Z(P)| = p^{2e}`.

`|P|` に関する強帰納法 (書籍 Hint). `P = ⟨x, y⟩` (`xy ≠ yx`) なら (b) より `|P| = p³` で
指数は `p²`. そうでなければ (d) より `V = C_P(U)` が extraspecial, (c) より `[P : V] = p²`,
`Z(V) = Z(P)` なので `[P : Z(P)] = p² · [V : Z(V)]` と帰納法. -/
theorem exists_index_center_eq_prime_pow_two_mul [Finite P] [Fact p.Prime]
    (hP : OddOrder.GroupTheory.IsExtraspecial p P) :
    ∃ e : ℕ, (Subgroup.center P).index = p ^ (2 * e) :=
  exists_index_center_eq_aux _ rfl hP

end

end OddOrder.Isaacs.Ch04
