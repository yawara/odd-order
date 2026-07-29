/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.NilpotentInjector.Structure
import OddOrder.Isaacs.Ch01_Sylow.Problems

/-!
# Isaacs Problem 3C.8 — injector の `{p}`-部分は `C(p)` の Sylow `p`-部分群

Mann の構造定理の主要部分:

> `I` が nilpotent injector なら, その `{p}`-部分 `I_p` は `C(p) = C_G(F_{p'})` の
> Sylow `p`-部分群である。

これで共役性が「素数ごとの `C(p)` 内 Sylow 共役性」に帰着する。

## 証明の骨格

`I_p ≤ S` なる `C(p)` の Sylow `p`-部分群 `S` を取り, `S ≤ I` を示す (極大性から `S = I_p`)。

1. `F` の `{p}`-部分 `F_p` は `I_p` に入るので, `I` の `{p}ᶜ`-部分 `I_{p'}` は
   `F_p` を中心化する: `I_{p'} ≤ C_G(F_p) =: D`。
2. `D ⊓ C(p) ≤ C_G(F_p ⊔ F_{p'}) = C_G(F)` なので, **Mann の核心補題 (一般形)** が
   `I_{p'} ≤ N_G(S)` を与える。
3. すると `y ∈ I_{p'}`, `s ∈ S` の交換子は `W := S ⊓ C_G(F)` に入る。`W` は `p`-群で
   しかも `I_{p'}` に中心化される (`W ≤ F ≤ I` かつ `W` が `p`-群だから `W ≤ I_p`) ので,
   位数の互いに素性から交換子は自明 (`eq_one_of_conj_mul_inv_mem_of_coprime`)。
4. よって `S ⊔ I_{p'}` は冪零 (`isNilpotent_sup_of_commute`) で `I` を含むから,
   `I` の極大性より `S ⊔ I_{p'} = I`, とくに `S ≤ I`。

## Main results

- `isNilpotent_sup_of_commute` — 元ごとに可換な 2 つの冪零部分群の join は冪零。
- `eq_one_of_conj_mul_inv_mem_of_coprime` — 交換子消去の位数論法。
- `isHallPart_pCentralizer_of_isNilpotentInjector` — 上記の主張。
-/

namespace OddOrder.Isaacs.Ch03

open Subgroup Pointwise

section /- 3C.8: injector の {p}-部分 -/

variable {G : Type*} [Group G]

/-- `{p}`-群 (`IsPiGroup` 版) は `p`-群 (`IsPGroup` 版)。 -/
theorem isPGroup_of_isPiGroup_singleton [Finite G] {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (h : Subgroup.IsPiGroup ({p} : Set ℕ) A) : IsPGroup p ↥A :=
  IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdvd =>
    h d (Nat.mem_primeFactors.mpr ⟨hd, hdvd, Nat.card_pos.ne'⟩))

/-- `p`-部分群を含む `{p}`-Hall 部分 (= Sylow `p`-部分群) が取れる。 -/
theorem exists_isHallPart_singleton_ge [Finite G] {p : ℕ} [Fact p.Prime] {K A : Subgroup G}
    (hAK : A ≤ K) (hA : IsPGroup p ↥A) :
    ∃ S : Subgroup G, IsHallPart K S ({p} : Set ℕ) ∧ IsPGroup p ↥S ∧ A ≤ S := by
  have hAsub : IsPGroup p ↥(A.subgroupOf K) :=
    hA.of_injective (Subgroup.subgroupOfEquivOfLe hAK).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAK).injective
  obtain ⟨Q, hQ⟩ := hAsub.exists_le_sylow
  refine ⟨(Q : Subgroup ↥K).map K.subtype, ⟨Subgroup.map_subtype_le _, ?_⟩, ?_, ?_⟩
  · rw [show ((Q : Subgroup ↥K).map K.subtype).subgroupOf K = (Q : Subgroup ↥K) from
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _]
    exact Ch01.sylow_isHallSubgroup_singleton Q
  · exact Q.isPGroup'.map K.subtype
  · intro a ha
    exact ⟨⟨a, hAK ha⟩, hQ (Subgroup.mem_subgroupOf.mpr ha), rfl⟩

/-- **交換子消去の位数論法**: `y` が `W` を中心化し, `y` のすべての冪と `s` の交換子が
`W` に入り, `y` の位数と `|W|` が互いに素なら, `y` は `s` と可換。

`z k := yᵏ s y⁻ᵏ s⁻¹` とおくと `z (k+1) = z k · z 1` (`y` は `z k ∈ W` を中心化する)、
よって `z k = (z 1)ᵏ`。`k = orderOf y` で `z k = 1` なので `(z 1)^(orderOf y) = 1`,
一方 `z 1 ∈ W` の位数は `|W|` を割るので互いに素性から `z 1 = 1`。 -/
theorem eq_one_of_conj_mul_inv_mem_of_coprime [Finite G] {W : Subgroup G} {y s : G}
    (hmem : ∀ k : ℕ, y ^ k * s * (y ^ k)⁻¹ * s⁻¹ ∈ W)
    (hcent : ∀ w ∈ W, y * w = w * y)
    (hcop : Nat.Coprime (orderOf y) (Nat.card ↥W)) :
    y * s * y⁻¹ = s := by
  set z : ℕ → G := fun k => y ^ k * s * (y ^ k)⁻¹ * s⁻¹ with hzdef
  have hz1 : z 1 = y * s * y⁻¹ * s⁻¹ := by simp [hzdef]
  have hstep : ∀ k : ℕ, z (k + 1) = z k * z 1 := by
    intro k
    have hfix : y * z k * y⁻¹ = z k := by
      have h := hcent (z k) (hmem k)
      rw [h]
      group
    have hexp : y ^ (k + 1) * s * (y ^ (k + 1))⁻¹ = y * (y ^ k * s * (y ^ k)⁻¹) * y⁻¹ := by
      rw [pow_succ']
      group
    have hzk : y ^ k * s * (y ^ k)⁻¹ = z k * s := by
      simp only [hzdef]
      group
    calc z (k + 1) = y ^ (k + 1) * s * (y ^ (k + 1))⁻¹ * s⁻¹ := rfl
      _ = y * (z k * s) * y⁻¹ * s⁻¹ := by rw [hexp, hzk]
      _ = (y * z k * y⁻¹) * (y * s * y⁻¹ * s⁻¹) := by group
      _ = z k * z 1 := by rw [hfix, hz1]
  have hpow : ∀ k : ℕ, z k = z 1 ^ k := by
    intro k
    induction k with
    | zero => simp [hzdef]
    | succ n ih => rw [hstep n, ih, pow_succ]
  have hord : z 1 ^ orderOf y = 1 := by
    rw [← hpow]
    simp [hzdef, pow_orderOf_eq_one]
  have hmemW : z 1 ∈ W := by
    rw [hz1]
    simpa using hmem 1
  have hdvd1 : orderOf (z 1) ∣ orderOf y := orderOf_dvd_of_pow_eq_one hord
  have hdvd2 : orderOf (z 1) ∣ Nat.card ↥W := W.orderOf_dvd_natCard hmemW
  have hone : orderOf (z 1) = 1 := by
    have hgcd := Nat.dvd_gcd hdvd1 hdvd2
    rwa [hcop, Nat.dvd_one] at hgcd
  have hz1eq : z 1 = 1 := orderOf_eq_one_iff.mp hone
  rw [hz1] at hz1eq
  exact mul_inv_eq_one.mp hz1eq

/-- **元ごとに可換な 2 つの冪零部分群の join は冪零**。

両者は join の中で正規なので Fitting 部分群に含まれ, join 全体が自身の Fitting 部分群に
一致する。Fitting 部分群は冪零。 -/
theorem isNilpotent_sup_of_commute [Finite G] {A B : Subgroup G}
    (hA : Group.IsNilpotent ↥A) (hB : Group.IsNilpotent ↥B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) : Group.IsNilpotent ↥(A ⊔ B) := by
  have hAK : A ≤ A ⊔ B := le_sup_left
  have hBK : B ≤ A ⊔ B := le_sup_right
  have hAnorm : A ⊔ B ≤ Subgroup.normalizer (A : Set G) :=
    sup_le Subgroup.le_normalizer fun b hb =>
      Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha b hb)
  have hBnorm : A ⊔ B ≤ Subgroup.normalizer (B : Set G) :=
    sup_le (fun a ha => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hcomm a ha b hb).symm))
      Subgroup.le_normalizer
  haveI : (A.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mpr hAnorm
  haveI : (B.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBK).mpr hBnorm
  haveI hAn : Group.IsNilpotent ↥(A.subgroupOf (A ⊔ B)) :=
    haveI := hA; Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAK).symm
  haveI hBn : Group.IsNilpotent ↥(B.subgroupOf (A ⊔ B)) :=
    haveI := hB; Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBK).symm
  have hAfit : A.subgroupOf (A ⊔ B) ≤ Ch01.fitting ↥(A ⊔ B) := Ch01.nilpotent_normal_le_fitting
  have hBfit : B.subgroupOf (A ⊔ B) ≤ Ch01.fitting ↥(A ⊔ B) := Ch01.nilpotent_normal_le_fitting
  have hsup : A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) = ⊤ := by
    apply Subgroup.map_injective (A ⊔ B).subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hAK, inf_eq_left.mpr hBK, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have htop : Ch01.fitting ↥(A ⊔ B) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hsup]
    exact sup_le hAfit hBfit
  haveI : Group.IsNilpotent ↥(⊤ : Subgroup ↥(A ⊔ B)) :=
    htop ▸ Ch01.fitting.isNilpotent (G := ↥(A ⊔ B))
  exact Group.nilpotent_of_mulEquiv Subgroup.topEquiv

/-- `C_G(F_p) ⊓ C(p) ≤ C_G(F(G))` (`F = F_p ⊔ F_{p'}` だから)。 -/
theorem centralizer_nilPiPart_inf_pCentralizer_le [Finite G] [IsSolvable G] (p : ℕ) :
    Subgroup.centralizer ((nilPiPart (Ch01.fitting G) ({p} : Set ℕ) : Subgroup G) : Set G)
        ⊓ pCentralizer G p
      ≤ Subgroup.centralizer ((Ch01.fitting G : Subgroup G) : Set G) := by
  have hsup : nilPiPart (Ch01.fitting G) ({p} : Set ℕ) ⊔ fittingPPrimePart G p
      = Ch01.fitting G :=
    IsHallPart.sup_eq (isHallPart_nilPiPart _ inferInstance) (isHallPart_fittingPPrimePart p)
  refine le_trans (centralizer_inf_le_centralizer_sup _ _) (Subgroup.centralizer_le ?_)
  rw [hsup]

/-- **Mann の構造定理 (主要部分)**: nilpotent injector `I` の `{p}`-部分は
`C(p) = C_G(F_{p'})` の Sylow `p`-部分群である。 -/
theorem isHallPart_pCentralizer_of_isNilpotentInjector [Finite G] [IsSolvable G]
    {I : Subgroup G} (hI : IsNilpotentInjector I) {p : ℕ} [Fact p.Prime] :
    IsHallPart (pCentralizer G p) (nilPiPart I ({p} : Set ℕ)) ({p} : Set ℕ) := by
  have hIpPart := isHallPart_nilPiPart (N := I) ({p} : Set ℕ) hI.1
  have hIp'Part := isHallPart_nilPiPart (N := I) (({p} : Set ℕ)ᶜ) hI.1
  have hIpC : nilPiPart I ({p} : Set ℕ) ≤ pCentralizer G p :=
    nilPiPart_singleton_le_pCentralizer hI.1 hI.2.1 p
  obtain ⟨S, hS, hSp, hIpS⟩ :=
    exists_isHallPart_singleton_ge hIpC (isPGroup_of_isPiGroup_singleton hIpPart.isPiGroup)
  -- `S ≤ I` を示せば, 極大性から `S = I_p`。
  suffices hSI : S ≤ I by
    have hSIp : S ≤ nilPiPart I ({p} : Set ℕ) :=
      le_nilPiPart_of_isPiGroup hI.1 hSI hS.isPiGroup
    rw [(le_antisymm hSIp hIpS).symm]
    exact hS
  -- (1) `I_{p'} ≤ C_G(F_p)`
  have hFpPart := isHallPart_nilPiPart (N := Ch01.fitting G) ({p} : Set ℕ) inferInstance
  have hFpIp : nilPiPart (Ch01.fitting G) ({p} : Set ℕ) ≤ nilPiPart I ({p} : Set ℕ) :=
    le_nilPiPart_of_isPiGroup hI.1 (hFpPart.1.trans hI.2.1) hFpPart.isPiGroup
  have hcommI := IsHallPart.commute hI.1 hIpPart hIp'Part
  haveI : (nilPiPart (Ch01.fitting G) ({p} : Set ℕ)).Normal := nilPiPart_normal inferInstance _
  haveI : (Subgroup.centralizer
      ((nilPiPart (Ch01.fitting G) ({p} : Set ℕ) : Subgroup G) : Set G)).Normal :=
    normal_centralizer inferInstance
  have hIp'D : nilPiPart I (({p} : Set ℕ)ᶜ)
      ≤ Subgroup.centralizer ((nilPiPart (Ch01.fitting G) ({p} : Set ℕ) : Subgroup G) : Set G) :=
    fun y hy => Subgroup.mem_centralizer_iff.mpr fun a ha => hcommI a (hFpIp ha) y hy
  -- (2) Mann の核心補題 (一般形) で `I_{p'}` は `S` を正規化する
  have hnorm : ∀ y ∈ nilPiPart I (({p} : Set ℕ)ᶜ), S.map (MulAut.conj y).toMonoidHom = S :=
    fun y hy => map_conj_eq_self_of_normal_of_inf_le
      (centralizer_nilPiPart_inf_pCentralizer_le p) hS (hIp'D hy)
  have hconj_mem : ∀ y ∈ nilPiPart I (({p} : Set ℕ)ᶜ), ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro y hy s hs
    have hy' := hnorm y hy
    rw [← hy']
    exact ⟨s, hs, by simp [MulAut.conj_apply]⟩
  -- (3) 交換子は `W := S ⊓ C_G(F)` に入り, `I_{p'}` に中心化される
  have hWIp : S ⊓ Subgroup.centralizer ((Ch01.fitting G : Subgroup G) : Set G)
      ≤ nilPiPart I ({p} : Set ℕ) := by
    refine le_nilPiPart_of_isPiGroup hI.1
      ((inf_le_right.trans OddOrder.GroupTheory.centralizer_fitting_le_fitting).trans hI.2.1) ?_
    exact Subgroup.IsPiGroup.le inf_le_left hS.isPiGroup
  have hcommutator : ∀ y ∈ nilPiPart I (({p} : Set ℕ)ᶜ), ∀ s ∈ S,
      y * s * y⁻¹ * s⁻¹ ∈ S ⊓ Subgroup.centralizer ((Ch01.fitting G : Subgroup G) : Set G) := by
    intro y hy s hs
    refine Subgroup.mem_inf.mpr ⟨mul_mem (hconj_mem y hy s hs) (inv_mem hs), ?_⟩
    exact commutator_mem_centralizer_fitting (centralizer_nilPiPart_inf_pCentralizer_le p)
      (hIp'D hy) (hS.1 hs)
  -- (4) 位数論法で `[S, I_{p'}] = 1`
  have hcommSI : ∀ s ∈ S, ∀ y ∈ nilPiPart I (({p} : Set ℕ)ᶜ), Commute s y := by
    intro s hs y hy
    have hcop : Nat.Coprime (orderOf y)
        (Nat.card ↥(S ⊓ Subgroup.centralizer ((Ch01.fitting G : Subgroup G) : Set G))) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hSp.to_le (inf_le_left :
        S ⊓ Subgroup.centralizer ((Ch01.fitting G : Subgroup G) : Set G) ≤ S))
      rw [hn]
      refine Nat.Coprime.pow_right _ ?_
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
      intro hdvd
      exact hIp'Part.isPiGroup p (Nat.mem_primeFactors.mpr
        ⟨Fact.out, hdvd.trans ((nilPiPart I (({p} : Set ℕ)ᶜ)).orderOf_dvd_natCard hy),
          Nat.card_pos.ne'⟩) rfl
    have hys : y * s * y⁻¹ = s :=
      eq_one_of_conj_mul_inv_mem_of_coprime
        (fun k => hcommutator (y ^ k) (pow_mem hy k) s hs)
        (fun w hw => (hcommI w (hWIp hw) y hy).symm) hcop
    have hys' : y * s = s * y := by
      have h := congrArg (fun t => t * y) hys
      simpa [mul_assoc] using h
    exact hys'.symm
  -- (5) `S ⊔ I_{p'}` は冪零で `I` を含む
  have hKnil : Group.IsNilpotent ↥(S ⊔ nilPiPart I (({p} : Set ℕ)ᶜ)) :=
    isNilpotent_sup_of_commute hSp.isNilpotent (isNilpotent_of_le hI.1 hIp'Part.1) hcommSI
  have hdec : nilPiPart I ({p} : Set ℕ) ⊔ nilPiPart I (({p} : Set ℕ)ᶜ) = I :=
    IsHallPart.sup_eq hIpPart hIp'Part
  have hIK : I ≤ S ⊔ nilPiPart I (({p} : Set ℕ)ᶜ) :=
    hdec.ge.trans (sup_le_sup_right hIpS _)
  have heq := hI.2.2 (S ⊔ nilPiPart I (({p} : Set ℕ)ᶜ)) hIK hKnil
  exact le_sup_left.trans heq.le

end -- 3C.8: injector の {p}-部分

end OddOrder.Isaacs.Ch03
