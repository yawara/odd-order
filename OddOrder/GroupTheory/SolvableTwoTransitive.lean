/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh02

/-!
# Huppert II Satz 3.2 (Galois–Burnside): 2-transitive 群の可解正規核

Huppert, *Endliche Gruppen I*, Kapitel II, Satz 3.2 の repo 形 (issue 9404):
有限群 `G` が `Ω` に faithful かつ 2-transitive に作用し、非自明な可解正規部分群
`N ⊴ G` を持てば、`N` は elementary abelian で `Ω` 上 regular
(transitive + 固定点自由) な `G`-正規部分群 `F` を含む。

Peterfalvi App.C Proposition 1 (`Peterfalvi/Appendices/NearFields.lean`
`rankOne_affine_nearField`) の前提 (iii)。`G = F ⋊ Stab(ω)` の complement 分解は
regular 性 (transitive + `stabilizer ⊓ F = ⊥`) から consumer 側で標準的に得られる。

証明 (Burnside/Galois の標準論法):
1. 2-transitive ⟹ primitive (`MulAction.isPreprimitive_of_is_two_pretransitive`)。
2. primitive ⟹ 固定点を持たない正規部分群は transitive (Wielandt Thm 7.1,
   mathlib `MulAction.IsQuasiPreprimitive`)。faithful + 非自明で固定点条件は自動。
3. `G`-minimal normal `F ≤ N` (`exists_isMinimalNormal_le_of_normal`) は可解ゆえ
   abelian (`⁅F,F⁆ ⊴ G` が真に小さい + minimality)、さらに exponent-`p` 部分群の
   正規性と minimality で elementary abelian。
4. abelian + transitive + faithful ⟹ 固定点自由: `ω` の固定元 `x ∈ F` は
   `F`-軌道の各点 `n • ω` も `x • (n • ω) = n • (x • ω) = n • ω` で固定するので
   `x = 1`。
-/

namespace OddOrder.GroupTheory

open MulAction Subgroup

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- **abelian transitive 部分群の作用は固定点自由** (regular の free 半分):
`F` abelian が `Ω` に transitive に作用するなら、各点の `G`-stabilizer と `F` の
交わりは自明. -/
theorem stabilizer_inf_eq_bot_of_isMulCommutative_of_isPretransitive
    [FaithfulSMul G Ω] {F : Subgroup G} (hcomm : IsMulCommutative ↥F)
    (htrans : MulAction.IsPretransitive F Ω) (ω : Ω) :
    MulAction.stabilizer G ω ⊓ F = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxstab, hxF⟩
  rw [mem_bot]
  refine FaithfulSMul.eq_of_smul_eq_smul (fun ω' : Ω => ?_)
  rw [one_smul]
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq F ω ω'
  have hxn : x * (n : G) = (n : G) * x :=
    congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hxF⟩ : ↥F) n)
  calc x • ω' = x • ((n : G) • ω) := by rw [← hn]; rfl
    _ = (x * (n : G)) • ω := (mul_smul _ _ _).symm
    _ = ((n : G) * x) • ω := by rw [hxn]
    _ = (n : G) • (x • ω) := mul_smul _ _ _
    _ = (n : G) • ω := by rw [mem_stabilizer_iff.mp hxstab]
    _ = ω' := by rw [← hn]; rfl

/-- **Huppert II Satz 3.2** (Galois–Burnside): `G` 有限, `Ω` への作用が faithful かつ
2-transitive, `N ⊴ G` 非自明可解なら, `N` は elementary abelian
(`p`-群 + abelian + exponent `p`) で `Ω` 上 regular (transitive + 固定点自由) な
`G`-正規部分群 `F` を含む. -/
theorem exists_elementaryAbelian_regular_normal_of_isMultiplyPretransitive
    [Finite G] [FaithfulSMul G Ω]
    (h2 : MulAction.IsMultiplyPretransitive G Ω 2)
    {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) (hsolv : IsSolvable ↥N) :
    ∃ (p : ℕ) (F : Subgroup G), p.Prime ∧ F.Normal ∧ F ≤ N ∧ F ≠ ⊥ ∧
      IsMulCommutative ↥F ∧ (∀ x ∈ F, x ^ p = 1) ∧ IsPGroup p ↥F ∧
      MulAction.IsPretransitive F Ω ∧
      ∀ ω : Ω, MulAction.stabilizer G ω ⊓ F = ⊥ := by
  classical
  haveI hprim : IsPreprimitive G Ω := isPreprimitive_of_is_two_pretransitive h2
  -- `G`-minimal normal `F ≤ N`.
  obtain ⟨F, ⟨hFnormal, hFne, hFmin⟩, hFN⟩ :=
    OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal N hN
  haveI := hFnormal
  haveI : Nontrivial ↥F := (Subgroup.nontrivial_iff_ne_bot F).mpr hFne
  -- `↥F` は可解 (`F ≤ N`, `↥N` 可解).
  haveI : IsSolvable ↥F :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hFN)
  -- abelian: `⁅F,F⁆ ⊴ G` は `F` より真に小さいので minimality で `⊥`.
  have hFF : ⁅F, F⁆ = ⊥ := by
    have hlt := OddOrder.Isaacs.Ch04.commutator_lt_self_of_isSolvable_subtype F
    exact (hFmin ⁅F, F⁆ inferInstance hlt.le).resolve_right hlt.ne
  have hcomm : IsMulCommutative ↥F :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hFF)
  -- 素数 `p ∣ |F|`.
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
    (fun h1 => hFne (Subgroup.eq_bot_of_card_eq F h1))
  haveI : Fact p.Prime := ⟨hp⟩
  -- exponent-`p` 部分群 `Fp := {x ∈ F | x^p = 1}` (`F` abelian ゆえ部分群).
  set Fp : Subgroup G :=
    { carrier := {x | x ∈ F ∧ x ^ p = 1}
      one_mem' := ⟨F.one_mem, one_pow p⟩
      mul_mem' := fun {a b} ha hb => by
        refine ⟨F.mul_mem ha.1 hb.1, ?_⟩
        have hab : Commute a b := by
          have := congrArg Subtype.val
            (hcomm.is_comm.comm (⟨a, ha.1⟩ : ↥F) ⟨b, hb.1⟩)
          exact this
        rw [hab.mul_pow, ha.2, hb.2, one_mul]
      inv_mem' := fun {a} ha => ⟨F.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
    with hFpdef
  have hFpF : Fp ≤ F := fun x hx => hx.1
  haveI hFpnormal : Fp.Normal := by
    constructor
    intro n hn g
    exact ⟨hFnormal.conj_mem n hn.1 g, by
      rw [conj_pow, hn.2, mul_one, mul_inv_cancel]⟩
  -- Cauchy: `p ∣ |F|` から位数 `p` の元 ⟹ `Fp ≠ ⊥` ⟹ minimality で `Fp = F`.
  have hFpne : Fp ≠ ⊥ := by
    haveI : Fintype ↥F := Fintype.ofFinite _
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥F) p
      (by rwa [← Nat.card_eq_fintype_card])
    intro hbot
    have hxFp : (x : G) ∈ Fp := by
      refine ⟨x.2, ?_⟩
      have : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      exact congrArg Subtype.val this
    rw [hbot, mem_bot] at hxFp
    have : orderOf x = 1 := by
      rw [← orderOf_coe, hxFp, orderOf_one]
    rw [hx] at this
    exact hp.one_lt.ne' this
  have hFpeq : Fp = F := (hFmin Fp hFpnormal hFpF).resolve_left hFpne
  have hexp : ∀ x ∈ F, x ^ p = 1 := fun x hx => (hFpeq ▸ hx : x ∈ Fp).2
  -- `F` は `p`-群 (全元の位数が `1` か `p`).
  have hFpgroup : IsPGroup p ↥F := by
    intro g
    have hgp : g ^ p = 1 := by
      have := hexp (g : G) g.2
      exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact this)
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hgp) with h1 | hpord
    · exact ⟨0, by rw [pow_zero, ← h1, pow_orderOf_eq_one]⟩
    · exact ⟨1, by rw [pow_one, ← hpord, pow_orderOf_eq_one]⟩
  -- transitivity: primitive ⟹ 固定点を持たない正規部分群は transitive.
  have hfix : fixedPoints F Ω ≠ Set.univ := by
    obtain ⟨x, hxne⟩ := exists_ne (1 : ↥F)
    have : ∃ ω : Ω, (x : G) • ω ≠ ω := by
      by_contra hall
      push Not at hall
      have : (x : G) = 1 := FaithfulSMul.eq_of_smul_eq_smul
        (fun ω => by rw [hall ω, one_smul])
      exact hxne (Subtype.ext this)
    obtain ⟨ω, hω⟩ := this
    intro huniv
    exact hω ((huniv ▸ Set.mem_univ ω : ω ∈ fixedPoints F Ω) x)
  haveI htrans : MulAction.IsPretransitive F Ω :=
    IsQuasiPreprimitive.isPretransitive_of_normal hfix
  exact ⟨p, F, hp, hFnormal, hFN, hFne, hcomm, hexp, hFpgroup, htrans,
    stabilizer_inf_eq_bot_of_isMulCommutative_of_isPretransitive hcomm htrans⟩

end OddOrder.GroupTheory
