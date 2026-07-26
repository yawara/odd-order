/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.Main
import OddOrder.Isaacs.Ch05_Transfer.Problems5D5

/-!
# Isaacs Problem 5D.6 — `A^p(G) ∩ P = P'` かつ `P'` 可換 (書籍 p. 170)

**主張**: `P ∈ Syl_p(G)`, `A := A^p(G)` が `A ∩ P = P'` を満たし **`P'` が可換**なら,
(Tate の定理を使わずに) `G` は正規 `p`-補群をもつ。

**証明** (書籍 hint =「`N := N_G(P')` が仮定を満たすことを見て `A` の中で Burnside」):

1. `P ≤ N := N_G(P')` (`le_normalizer_commutator_self`), ゆえに `P ∈ Syl_p(N)`, `P' ⊴ N`。
2. `N` は **5D.5 の仮定を満たす**: `A^p(N) ⊇ ⁅N,N⁆ ⊇ P'` かつ
   `A^p(N) ≤ A ∩ N` (`APrime_le_subgroupOf_APrime_of_sylow_le`) から `A^p(N) ∩ P = P'`,
   また `P' ⊴ N` から `P' ⊴ A^p(N)`。⟹ **`N` は正規 `p`-補群をもつ**。
3. `T := A ∩ N` は `N` の部分群なので `T` も正規 `p`-補群をもつ
   (`hasNormalPComplement_of_subgroup`)。`P'` は `A` の Sylow `p`-部分群ゆえ `T` のそれでもあり,
   `P' ⊴ N` から `T` で正規。正規 `p`-補群と正規 Sylow は互いに中心化するので
   `P'` 可換とあわせ **`T = N_A(P') ≤ C_G(P')`**。
4. よって `A` の中で **Burnside** が使え, `A` は正規 `p`-補群 `K` をもつ。`K` は正規 `p`-補群の
   一意性 (`map_mulAut_of_normal_pcomplement`) から `A` に characteristic, `A ⊴ G` ゆえ `K ⊴ G`。
   `p ∤ |K|` と `|G:K| = |G:A|·|A:K|` が `p`-冪 ⟹ 結論。
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise
open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 5D.6: `A^p(G) ∩ P = P'` かつ `P'` 可換 (p. 170) -/

/-- 正規 `p`-補群をもつ群で **正規な** Sylow `p`-部分群は中心化される: `L ⊴ H` が Sylow
`p`-部分群なら `H ≤ C_H(L)`(可換 `L` のとき `L ≤ Z(H)`)。

正規 `p`-補群 `K` と `L` はともに正規で交わりが自明ゆえ交換し, `H = K·L`。 -/
theorem le_centralizer_of_normal_sylow_of_hasNormalPComplement {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hH : HasNormalPComplement p H) (S : Sylow p H)
    [hSnorm : (S : Subgroup H).Normal] (hab : ∀ x y : ↥(S : Subgroup H), x * y = y * x) :
    ∀ h : H, ∀ x ∈ (S : Subgroup H), h * x = x * h := by
  classical
  obtain ⟨K, hKnormal, hKcompl⟩ := hH
  haveI := hKnormal
  have hcompl := hKcompl S
  -- `[K, S] = 1` (ともに正規で交わり自明)
  have hcomm : ∀ k ∈ K, ∀ x ∈ (S : Subgroup H), k * x = x * k := by
    intro k hk x hx
    have h1 : k * x * k⁻¹ * x⁻¹ ∈ (S : Subgroup H) :=
      Subgroup.mul_mem _ (hSnorm.conj_mem x hx k) (Subgroup.inv_mem _ hx)
    have h2 : k * x * k⁻¹ * x⁻¹ ∈ K := by
      have : k * (x * k⁻¹ * x⁻¹) ∈ K :=
        Subgroup.mul_mem _ hk (hKnormal.conj_mem k⁻¹ (Subgroup.inv_mem _ hk) x)
      simpa [mul_assoc] using this
    have hbot : k * x * k⁻¹ * x⁻¹ = 1 := by
      have := hcompl.disjoint.le_bot (⟨h2, h1⟩ : _ ∈ K ⊓ (S : Subgroup H))
      simpa using this
    have : k * x * k⁻¹ = x := by
      have h3 := congrArg (· * x) hbot
      simpa using h3
    calc k * x = k * x * k⁻¹ * k := by group
      _ = x * k := by rw [this]
  -- `H = K · S`
  intro h x hx
  have hmul : ((⊤ : Subgroup H) : Set H) = (K : Set H) * ((S : Subgroup H) : Set H) := by
    have hs := Subgroup.normal_mul K (S : Subgroup H)
    rw [hcompl.sup_eq_top] at hs
    exact hs
  have hhin : h ∈ (K : Set H) * ((S : Subgroup H) : Set H) := by
    rw [← hmul]; exact Subgroup.mem_top h
  obtain ⟨k, hk, s, hs, rfl⟩ := hhin
  have hsx : s * x = x * s := congrArg Subtype.val (hab ⟨s, hs⟩ ⟨x, hx⟩)
  calc k * s * x = k * (s * x) := by group
    _ = k * (x * s) := by rw [hsx]
    _ = (k * x) * s := by group
    _ = (x * k) * s := by rw [hcomm k hk x hx]
    _ = x * (k * s) := by group

/-- 部分群 `H` は自分の交換子群 `⁅H,H⁆` を正規化する。 -/
theorem le_normalizer_commutator_self (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  intro x hx
  have hHfix : MulAut.conj x • H = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer hx)
  have key : MulAut.conj x • (⁅H, H⁆ : Subgroup G) = ⁅H, H⁆ := by
    rw [Subgroup.pointwise_smul_def, Subgroup.map_commutator, ← Subgroup.pointwise_smul_def,
      hHfix]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr key

/-- 正規 `p`-補群の性質は同型で移る (位数と指数の橋渡しで示す)。 -/
theorem hasNormalPComplement_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A]
    {p : ℕ} [Fact p.Prime] (e : A ≃* B) (hA : HasNormalPComplement p A) :
    HasNormalPComplement p B := by
  classical
  haveI : Finite B := Finite.of_equiv A e.toEquiv
  obtain ⟨N, hNnormal, hNcompl⟩ := hA
  haveI := hNnormal
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p A))
  have hpN : ¬ p ∣ Nat.card ↥N := not_dvd_card_of_isComplement'_sylow Q (hNcompl Q)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hNidx : N.index = p ^ a := by rw [(hNcompl Q).symm.index_eq_card, ha]
  haveI : (N.map (e : A →* B)).Normal := hNnormal.map _ e.surjective
  refine hasNormalPComplement_of_normal_of_index_eq_pow (X := N.map (e : A →* B)) (a := a) ?_ ?_
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hpN
  · rw [Subgroup.index_map_equiv _ e]
    exact hNidx

/-- 正規 `p`-補群は部分群に遺伝する (ambient `G` の部分群の形で). -/
theorem hasNormalPComplement_of_le [Finite G] {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hHK : H ≤ K) (hK : HasNormalPComplement p ↥K) : HasNormalPComplement p ↥H :=
  hasNormalPComplement_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHK)
    (hasNormalPComplement_of_subgroup hK (H.subgroupOf K))

/-- **Isaacs Problem 5D.6** (p. 170) ⭐: `P ∈ Syl_p(G)` と `A := A^p(G)` が `A ∩ P = ⁅P,P⁆` を
満たし `⁅P,P⁆` が**可換**なら, `G` は正規 `p`-補群をもつ (Tate の定理は使わない)。 -/
theorem hasNormalPComplement_of_APrime_inf_sylow_eq_commutator_of_abelian
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hAP : APrime p G ⊓ (P : Subgroup G) = ⁅(P : Subgroup G), (P : Subgroup G)⁆)
    (hab : ∀ x y : ↥(⁅(P : Subgroup G), (P : Subgroup G)⁆ : Subgroup G), x * y = y * x) :
    HasNormalPComplement p G := by
  classical
  set L : Subgroup G := ⁅(P : Subgroup G), (P : Subgroup G)⁆ with hLdef
  set A : Subgroup G := APrime p G with hAdef
  have hLP : L ≤ (P : Subgroup G) := by
    rw [hLdef, ← Subgroup.map_subtype_commutator]
    exact Subgroup.map_subtype_le _
  have hLA : L ≤ A := by rw [← hAP]; exact inf_le_left
  set N : Subgroup G := Subgroup.normalizer (L : Set G) with hNdef
  have hPN : (P : Subgroup G) ≤ N := le_normalizer_commutator_self _
  have hLN : L ≤ N := hLP.trans hPN
  -- `L` は `A` の `{p}`-Hall 部分群 (= Sylow)
  have hLsubA : L.subgroupOf A = (P : Subgroup G).subgroupOf A := by
    rw [← hAP, Subgroup.inf_subgroupOf_left]
  have hhallA : Ch03.IsHallSubgroup ({p} : Set ℕ) (L.subgroupOf A) := by
    rw [hLsubA]
    exact Ch03.isHallSubgroup_subgroupOf_of_normal (Ch01.sylow_isHallSubgroup_singleton P)
  -- Step 2: `N` は 5D.5 の仮定を満たす
  have hNcompl : HasNormalPComplement p ↥N := by
    have hPNcoe : ((P.subtype hPN : Sylow p ↥N) : Subgroup ↥N) = (P : Subgroup G).subgroupOf N :=
      rfl
    have hcommN : (⁅((P.subtype hPN : Sylow p ↥N) : Subgroup ↥N),
        ((P.subtype hPN : Sylow p ↥N) : Subgroup ↥N)⁆ : Subgroup ↥N) = L.subgroupOf N := by
      refine Subgroup.map_injective (Subgroup.subtype_injective N) ?_
      rw [Subgroup.map_commutator, hPNcoe, Subgroup.subgroupOf_map_subtype,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPN, inf_eq_left.mpr hLN, hLdef]
    have hANle : APrime p ↥N ≤ A.subgroupOf N :=
      APrime_le_subgroupOf_APrime_of_sylow_le P hPN
    have hkey : APrime p ↥N ⊓ ((P.subtype hPN : Sylow p ↥N) : Subgroup ↥N)
        = ⁅((P.subtype hPN : Sylow p ↥N) : Subgroup ↥N),
            ((P.subtype hPN : Sylow p ↥N) : Subgroup ↥N)⁆ := by
      rw [hcommN]
      refine le_antisymm (fun z hz => ?_) (le_inf ?_ ?_)
      · obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
        rw [hPNcoe] at hz2
        rw [Subgroup.mem_subgroupOf, ← hAP]
        exact ⟨Subgroup.mem_subgroupOf.mp (hANle hz1), Subgroup.mem_subgroupOf.mp hz2⟩
      · rw [← hcommN]
        refine le_trans (Subgroup.commutator_mono le_top le_top) ?_
        rw [← _root_.commutator_def]
        exact commutator_le_APrime p ↥N
      · rw [hPNcoe]
        exact Subgroup.comap_mono hLP
    have hLNnormal : (L.subgroupOf N).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (le_of_eq hNdef)
    have hnorm2 : ((⁅((P.subtype hPN : Sylow p ↥N) : Subgroup ↥N),
        ((P.subtype hPN : Sylow p ↥N) : Subgroup ↥N)⁆ : Subgroup ↥N).subgroupOf
          (APrime p ↥N)).Normal := by
      rw [hcommN]
      exact Subgroup.Normal.subgroupOf hLNnormal _
    exact hasNormalPComplement_of_APrime_inf_sylow_eq_commutator (P.subtype hPN) hkey hnorm2
  -- Step 3: `A ⊓ N ≤ C_G(L)`
  have hcent : ∀ h ∈ A ⊓ N, ∀ x ∈ L, h * x = x * h := by
    have hTcompl : HasNormalPComplement p ↥(A ⊓ N) :=
      hasNormalPComplement_of_le inf_le_right hNcompl
    have hhallT : Ch03.IsHallSubgroup ({p} : Set ℕ) (L.subgroupOf (A ⊓ N)) := by
      refine ⟨fun q hq => ?_, fun q hq => ?_⟩
      · refine hhallA.1 q ?_
        have e1 : Nat.card ↥(L.subgroupOf (A ⊓ N)) = Nat.card ↥L :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_inf hLA hLN)).toEquiv
        have e2 : Nat.card ↥(L.subgroupOf A) = Nat.card ↥L :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLA).toEquiv
        rwa [e1, ← e2] at hq
      · refine hhallA.2 q (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hq).1, ?_,
          Subgroup.index_ne_zero_of_finite⟩)
        have hmul : L.relIndex (A ⊓ N) * (A ⊓ N).relIndex A = L.relIndex A :=
          Subgroup.relIndex_mul_relIndex L (A ⊓ N) A (le_inf hLA hLN) inf_le_left
        exact (Nat.mem_primeFactors.mp hq).2.1.trans (Dvd.intro _ hmul)
    obtain ⟨S, hS⟩ := Ch01.exists_sylow_coe_eq_of_isHallSubgroup_singleton hhallT
    haveI hSnorm : (S : Subgroup ↥(A ⊓ N)).Normal := by
      rw [hS]
      exact Subgroup.normal_subgroupOf_of_le_normalizer (inf_le_right.trans (le_of_eq hNdef))
    have habS : ∀ x y : ↥(S : Subgroup ↥(A ⊓ N)), x * y = y * x := by
      intro x y
      have hx : ((x : ↥(A ⊓ N)) : G) ∈ L := Subgroup.mem_subgroupOf.mp (hS.le x.2)
      have hy : ((y : ↥(A ⊓ N)) : G) ∈ L := Subgroup.mem_subgroupOf.mp (hS.le y.2)
      have hGeq : (((x : ↥(A ⊓ N)) : G)) * (((y : ↥(A ⊓ N)) : G))
          = (((y : ↥(A ⊓ N)) : G)) * (((x : ↥(A ⊓ N)) : G)) :=
        congrArg Subtype.val (hab ⟨_, hx⟩ ⟨_, hy⟩)
      exact Subtype.ext (Subtype.ext hGeq)
    have hkey := le_centralizer_of_normal_sylow_of_hasNormalPComplement hTcompl S habS
    intro h hh x hx
    have hxS : (⟨x, le_inf hLA hLN hx⟩ : ↥(A ⊓ N)) ∈ (S : Subgroup ↥(A ⊓ N)) := by
      rw [hS]
      exact Subgroup.mem_subgroupOf.mpr hx
    exact congrArg Subtype.val (hkey ⟨h, hh⟩ _ hxS)
  -- Step 4: `↥A` で Burnside
  obtain ⟨SA, hSA⟩ := Ch01.exists_sylow_coe_eq_of_isHallSubgroup_singleton hhallA
  have hAcompl : HasNormalPComplement p ↥A := by
    refine hasNormalPComplement_of_sylow_normalizer_le_centralizer SA (fun z hz => ?_)
    have hz' : z ∈ Subgroup.normalizer ((L.subgroupOf A : Subgroup ↥A) : Set ↥A) := by
      rw [← hSA]; exact hz
    rw [← Subgroup.subgroupOf_normalizer_eq hLA] at hz'
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ L.subgroupOf A := by rw [← hSA]; exact hy
    have hzAN : ((z : ↥A) : G) ∈ A ⊓ N := ⟨z.2, Subgroup.mem_subgroupOf.mp hz'⟩
    exact Subtype.ext (hcent _ hzAN _ (Subgroup.mem_subgroupOf.mp hy')).symm
  obtain ⟨K', hK'normal, hK'compl⟩ := hAcompl
  haveI := hK'normal
  haveI : K'.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro ψ
    exact map_mulAut_of_normal_pcomplement (hK'compl SA) ψ
  haveI hKnormal : (K'.map A.subtype).Normal := Ch01.characteristic_map_subtype_normal K'
  have hpK : ¬ p ∣ Nat.card ↥(K'.map A.subtype) := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective A)]
    exact not_dvd_card_of_isComplement'_sylow SA (hK'compl SA)
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp SA.isPGroup'
  obtain ⟨a, ha⟩ := APrime_index_isPGroup p G
  refine hasNormalPComplement_of_normal_of_index_eq_pow (X := K'.map A.subtype)
    (a := c + a) hpK ?_
  have hrel : (K'.map A.subtype).relIndex A * A.index = (K'.map A.subtype).index :=
    Subgroup.relIndex_mul_index (Subgroup.map_subtype_le _)
  have hrel2 : (K'.map A.subtype).relIndex A = K'.index := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective A)]
  rw [← hrel, hrel2, (hK'compl SA).symm.index_eq_card, hc, ha, pow_add]


end

end OddOrder.Isaacs.Ch05
