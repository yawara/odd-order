/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CyclicSubgroupUniqueness
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroupsCoprime

/-!
# Isaacs Chapter 4 — Problem 4D.7 の準備 (巡回 Sylow と正規 Sylow)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4D.7 (書籍 p. 146) の
hint 「`O_{p'}(G) = 1` のときは `G` が正規 Sylow `p`-部分群を持つことを示せ」の部分。

`G` が `p`-可分 (repo では `Ch03.IsPiSeparable {p} G`) で `O_{p'}(G) = 1`,
`O_p(G)` が巡回のとき:

* `centralizer_oPiCore_eq` — `C_G(O_p(G)) = O_p(G)` (Hall–Higman 1.2.3 + `O_p(G)` 可換)
* `commutator_le_oPiCore_of_isCyclic` — `G' ≤ O_p(G)`, すなわち `G / O_p(G)` は可換
* `exists_sylow_coe_eq_oPiCore_of_isCyclic` — したがって `O_p(G)` 自身が (正規) Sylow `p`-部分群

`Aut` が可換になるのは `O_p(G)` が巡回だから (`mulAut_mul_comm_of_isCyclic`,
mathlib `IsCyclic.mulAutMulEquiv : MulAut P ≃* (ZMod |P|)ˣ` の引き戻し)。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

section /- Problem 4D.7 準備 (p. 146) -/

/-- **巡回群の自己同型群は可換**: `MulAut P ≃* (ZMod |P|)ˣ` (mathlib
`IsCyclic.mulAutMulEquiv`) を単射で引き戻す。 -/
theorem mulAut_mul_comm_of_isCyclic {P : Type*} [Group P] [IsCyclic P] (f g : MulAut P) :
    f * g = g * f :=
  (IsCyclic.mulAutMulEquiv (G := P)).injective (by rw [map_mul, map_mul, mul_comm])

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- `MulAut.conjNormal : G →* MulAut ↥N` の核は `C_G(N)`. -/
theorem ker_conjNormal_eq_centralizer (N : Subgroup G) [N.Normal] :
    (MulAut.conjNormal (H := N)).ker = Subgroup.centralizer (N : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    have := congrArg Subtype.val (congrFun (congrArg (fun f : MulAut ↥N => (f : ↥N → ↥N)) h)
      (⟨x, hx⟩ : ↥N))
    rw [MulAut.conjNormal_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  · intro h
    ext x
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← h (x : G) x.2]
    group

/-- `p`-可分 + `O_{p'}(G) = 1` + `O_p(G)` 巡回 ⟹ `C_G(O_p(G)) = O_p(G)`。

`⊆` は **Hall–Higman 1.2.3** (`Ch03.hall_higman_1_2_3`), `⊇` は `O_p(G)` が巡回=可換だから。 -/
theorem centralizer_oPiCore_eq (p : ℕ) [Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hp' : Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥)
    (hcyc : IsCyclic ↥(Ch03.oPiCore ({p} : Set ℕ) G)) :
    Subgroup.centralizer ((Ch03.oPiCore ({p} : Set ℕ) G : Subgroup G) : Set G) =
      Ch03.oPiCore ({p} : Set ℕ) G := by
  refine le_antisymm (Ch03.hall_higman_1_2_3 ({p} : Set ℕ) hp') ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  letI := hcyc.commGroup
  have := mul_comm (⟨y, hy⟩ : ↥(Ch03.oPiCore ({p} : Set ℕ) G)) ⟨x, hx⟩
  exact congrArg Subtype.val this

/-- `p`-可分 + `O_{p'}(G) = 1` + `O_p(G)` 巡回 ⟹ `G / O_p(G)` は可換 (`G' ≤ O_p(G)`)。

`C_G(O_p(G)) = O_p(G)` (`centralizer_oPiCore_eq`) と, 巡回群の `MulAut` が可換であること
(`mulAut_mul_comm_of_isCyclic`) から `G → MulAut (O_p(G))` の像が可換, その核が
`C_G(O_p(G)) = O_p(G)`。 -/
theorem commutator_le_oPiCore_of_isCyclic (p : ℕ) [Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hp' : Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥)
    (hcyc : IsCyclic ↥(Ch03.oPiCore ({p} : Set ℕ) G)) :
    _root_.commutator G ≤ Ch03.oPiCore ({p} : Set ℕ) G := by
  have hcent := centralizer_oPiCore_eq p hp' hcyc
  rw [commutator_def]
  refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
  have hker : ⁅x, y⁆ ∈ (MulAut.conjNormal (H := Ch03.oPiCore ({p} : Set ℕ) G)).ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr
      (mulAut_mul_comm_of_isCyclic (MulAut.conjNormal x) (MulAut.conjNormal y))
  rw [ker_conjNormal_eq_centralizer, hcent] at hker
  exact hker

/-- **Isaacs Problem 4D.7 の hint 部分**: `p`-可分 + `O_{p'}(G) = 1` + `O_p(G)` 巡回なら
`O_p(G)` 自身が (正規な) Sylow `p`-部分群。

`G' ≤ O_p(G)` (`commutator_le_oPiCore_of_isCyclic`) より `O_p(G)` を含む部分群はすべて正規。
`O_p(G)` を含む Sylow `p`-部分群 `Q` は正規な `p`-部分群なので `Q ≤ O_p(G)`
(`Subgroup.IsPiGroup.le_oPiCore`), したがって `Q = O_p(G)`。 -/
theorem exists_sylow_coe_eq_oPiCore_of_isCyclic (p : ℕ) [Fact p.Prime]
    [Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hp' : Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥)
    (hcyc : IsCyclic ↥(Ch03.oPiCore ({p} : Set ℕ) G)) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = Ch03.oPiCore ({p} : Set ℕ) G := by
  have hOp : IsPGroup p ↥(Ch03.oPiCore ({p} : Set ℕ) G) :=
    Ch03.Subgroup.isPiGroup_singleton_iff_isPGroup.mp (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))
  obtain ⟨Q, hQ⟩ := hOp.exists_le_sylow
  have hcomm := commutator_le_oPiCore_of_isCyclic p hp' hcyc
  haveI hQnormal : (Q : Subgroup G).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine top_le_iff.mp (le_normalizer_of_commutator_le ?_)
    refine le_trans (Subgroup.commutator_mono le_top le_rfl) (hcomm.trans hQ)
  exact ⟨Q, le_antisymm
    (Ch03.Subgroup.IsPiGroup.le_oPiCore
      (Ch03.Subgroup.isPiGroup_singleton_iff_isPGroup.mpr Q.2)) hQ⟩

/-! ### 巡回 `p`-群の部分群束 -/

/-- 非自明な `p`-部分群には位数 `p` の元がある (Cauchy). -/
theorem exists_orderOf_eq_prime_of_ne_bot {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] (hP : IsPGroup p P) {N : Subgroup P} (hN : N ≠ ⊥) :
    ∃ x : P, x ∈ N ∧ orderOf x = p := by
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := ↥N)).mp (hP.to_subgroup N)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr ‹Nontrivial ↥N›).ne' hk
  have hdvd : p ∣ Nat.card ↥N := by
    rw [hk]
    exact dvd_pow_self p hk0
  haveI : Fintype ↥N := Fintype.ofFinite _
  have hdvd' : p ∣ Fintype.card ↥N := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥N) p hdvd'
  have hne : (x : P) ≠ 1 := by
    intro h
    have hx1 : x = 1 := Subtype.ext h
    rw [hx1, orderOf_one] at hx
    exact (Fact.out : p.Prime).one_lt.ne hx
  refine ⟨(x : P), x.2, ?_⟩
  have hpow : ((x : P)) ^ p = 1 := by
    have hp1 := pow_orderOf_eq_one x
    rw [hx] at hp1
    exact congrArg Subtype.val hp1
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hpow) with h1 | h1
  · exact absurd (orderOf_eq_one_iff.mp h1) hne
  · exact h1

/-- **巡回 `p`-群では非自明な部分群 2 つは非自明に交わる**: 位数 `p` の部分群が唯一だから
(`OddOrder.GroupTheory.cyclic_subgroup_eq_of_card_eq`)。 -/
theorem inf_ne_bot_of_isCyclic_of_isPGroup {P : Type*} [Group P] [Finite P] [IsCyclic P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) {H K : Subgroup P}
    (hH : H ≠ ⊥) (hK : K ≠ ⊥) : H ⊓ K ≠ ⊥ := by
  obtain ⟨x, hxH, hxo⟩ := exists_orderOf_eq_prime_of_ne_bot hP hH
  obtain ⟨y, hyK, hyo⟩ := exists_orderOf_eq_prime_of_ne_bot hP hK
  have heq : Subgroup.zpowers x = Subgroup.zpowers y :=
    OddOrder.GroupTheory.cyclic_subgroup_eq_of_card_eq
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hyo])
  have hxK : x ∈ K := by
    have hmem : x ∈ Subgroup.zpowers y := heq ▸ Subgroup.mem_zpowers x
    exact (Subgroup.zpowers_le.mpr hyK) hmem
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨x, hxH, hxK⟩, ?_⟩
  intro h
  have : x = 1 := congrArg Subtype.val h
  rw [this, orderOf_one] at hxo
  exact (Fact.out : p.Prime).one_lt.ne hxo

end

end OddOrder.Isaacs.Ch04
