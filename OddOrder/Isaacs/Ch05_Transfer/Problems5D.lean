/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.Problems5C13

/-!
# Isaacs Problems 5D — `A^p(G)` と p-transfer 制御 (書籍 pp. 169-170)

## 5D.1

`P ∈ Syl_p(G)` が可換で `P ⊆ H ⊆ G`, `H` が `G` の `p`-transfer を制御する
(Isaacs の定義: `A^p(H) = H ∩ A^p(G)`) とする。`H` が正規 `p`-補群をもつなら `G` ももつ。

**鍵**: 可換 Sylow `P` に対して

> `G` が正規 `p`-補群をもつ ⟺ `A^p(G) ⊓ P = ⊥`

(`⟸` は focal subgroup 定理 `A^p(G) ⊓ P = Foc_G(P) = G' ⊓ P` と Problem 5C.1、
`⟹` は「商が `P` の像で可換」+ `APrime_le`)。この同値を `H` 側で使って
`A^p(H) ⊓ P = ⊥` を得, 仮説で `A^p(G) ⊓ P = ⊥` に移し, `G` 側で使い直す。
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise
open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 5D.1: p-transfer 制御と正規 `p`-補群 (p. 169) -/

/-- 可換 Sylow `p`-部分群をもつ有限群が正規 `p`-補群をもつなら `A^p(G) ⊓ P = ⊥`。

正規 `p`-補群 `N` に対し `G/N` は `P` の像で可換なので `commutator G ≤ N`、
また `|G:N| = |P|` は `p`-冪なので `A^p(G) ≤ N` (`APrime_le`)。
`N` と `P` は補群対ゆえ交わりが自明。 -/
theorem APrime_inf_sylow_eq_bot_of_hasNormalPComplement [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [hPab : IsMulCommutative ↥(P : Subgroup G)]
    (hG : HasNormalPComplement p G) :
    APrime p G ⊓ (P : Subgroup G) = ⊥ := by
  classical
  obtain ⟨N, hNnormal, hNcompl⟩ := hG
  have := hNnormal
  have hcompl := hNcompl P
  -- `commutator G ≤ N`: `G = N · P` と `P` 可換から `G/N` は可換
  have hcomm : _root_.commutator G ≤ N := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have hmul : ((N ⊔ (P : Subgroup G) : Subgroup G) : Set G) = (N : Set G) * (P : Subgroup G) :=
      Subgroup.normal_mul N (P : Subgroup G)
    have htop : ((⊤ : Subgroup G) : Set G) = (N : Set G) * (P : Subgroup G) := by
      rw [← hmul, hcompl.sup_eq_top]
    have hain : a ∈ (N : Set G) * ((P : Subgroup G) : Set G) := by
      rw [← htop]; exact Subgroup.mem_top a
    have hbin : b ∈ (N : Set G) * ((P : Subgroup G) : Set G) := by
      rw [← htop]; exact Subgroup.mem_top b
    obtain ⟨n₁, hn₁, x, hx, rfl⟩ := hain
    obtain ⟨n₂, hn₂, y, hy, rfl⟩ := hbin
    have hxy : (⟨x, hx⟩ : ↥(P : Subgroup G)) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
      hPab.is_comm.comm _ _
    have hxycomm : x * y = y * x := congrArg Subtype.val hxy
    have hn₁' : (QuotientGroup.mk' N) n₁ = 1 := (QuotientGroup.eq_one_iff _).mpr hn₁
    have hn₂' : (QuotientGroup.mk' N) n₂ = 1 := (QuotientGroup.eq_one_iff _).mpr hn₂
    have hkey : (QuotientGroup.mk' N) ⁅n₁ * x, n₂ * y⁆ = 1 := by
      rw [map_commutatorElement, map_mul, map_mul, hn₁', hn₂', one_mul, one_mul,
        commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul, hxycomm]
    exact (QuotientGroup.eq_one_iff _).mp hkey
  -- `N.index = |P|` は `p`-冪
  have hidx : ∃ k : ℕ, N.index = p ^ k := by
    refine ⟨(Nat.card G).factorization p, ?_⟩
    rw [hcompl.symm.index_eq_card, P.card_eq_multiplicity]
  obtain ⟨k, hk⟩ := hidx
  have hAle : APrime p G ≤ N := APrime_le hNnormal hcomm hk
  refine le_antisymm ?_ bot_le
  calc APrime p G ⊓ (P : Subgroup G) ≤ N ⊓ (P : Subgroup G) := inf_le_inf hAle le_rfl
    _ = ⊥ := hcompl.disjoint.eq_bot

/-- 可換 Sylow `p`-部分群 `P` に対し `A^p(G) ⊓ P = ⊥` なら `G` は正規 `p`-補群をもつ
(`APrime_inf_sylow_eq_bot_of_hasNormalPComplement` の逆)。

focal subgroup 定理 (`A^p(G) ⊓ P = Foc_G(P) = G' ⊓ P`) で Problem 5C.1 に落とす。 -/
theorem hasNormalPComplement_of_APrime_inf_sylow_eq_bot [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (h : APrime p G ⊓ (P : Subgroup G) = ⊥) :
    HasNormalPComplement p G := by
  refine hasNormalPComplement_of_commutator_inf_sylow_eq_bot P ?_
  rw [Subgroup.commutator_inf_eq_focalSubgroup P, ← APrime_inf_sylow_eq_focalSubgroup P]
  exact h

/-- **Isaacs Problem 5D.1** (p. 169) ⭐: `P ∈ Syl_p(G)` が可換で `P ≤ H ≤ G`,
`H` が `G` の `p`-transfer を制御する (`A^p(H) = H ∩ A^p(G)`) とする。
`H` が正規 `p`-補群をもつなら `G` ももつ。

`p`-transfer 制御の仮説は Isaacs の定義そのまま (`A^p(H) = (A^p G).subgroupOf H`) で述べた。
Cor 5.22 (`APrime_eq_subgroupOf_APrime_of_controlsFusionIn`) はこの仮説の十分条件を与える。 -/
theorem hasNormalPComplement_of_controlsPTransfer [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [IsMulCommutative ↥(P : Subgroup G)] {H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H)
    (hcontrol : APrime p ↥H = (APrime p G).subgroupOf H)
    (hH : HasNormalPComplement p ↥H) :
    HasNormalPComplement p G := by
  classical
  have hPHab : IsMulCommutative ↥((P.subtype hPH : Sylow p ↥H) : Subgroup ↥H) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    have hGeq : (((x : ↥H) : G)) * (((y : ↥H) : G)) = (((y : ↥H) : G)) * (((x : ↥H) : G)) :=
      congrArg Subtype.val
        (‹IsMulCommutative ↥(P : Subgroup G)›.is_comm.comm
          ⟨((x : ↥H) : G), x.2⟩ ⟨((y : ↥H) : G), y.2⟩)
    exact Subtype.ext (Subtype.ext hGeq)
  have hHbot : APrime p ↥H ⊓ ((P.subtype hPH : Sylow p ↥H) : Subgroup ↥H) = ⊥ :=
    APrime_inf_sylow_eq_bot_of_hasNormalPComplement (P.subtype hPH) hH
  rw [hcontrol, Sylow.coe_subtype, Subgroup.subgroupOf, Subgroup.subgroupOf,
    ← Subgroup.comap_inf] at hHbot
  refine hasNormalPComplement_of_APrime_inf_sylow_eq_bot P ?_
  have hle : APrime p G ⊓ (P : Subgroup G) ≤ H := inf_le_right.trans hPH
  refine le_antisymm (fun g hg => ?_) bot_le
  have hgH : g ∈ H := hle hg
  have hmem : (⟨g, hgH⟩ : ↥H) ∈ Subgroup.comap H.subtype (APrime p G ⊓ (P : Subgroup G)) := hg
  rw [hHbot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hmem))

end

section /- 5D.2: 中心的 Sylow と正規 `p`-補群 (p. 169) -/

/-- **Isaacs Problem 5D.2** (p. 169) ⭐: `P ∈ Syl_p(G)` が `Z(G)` に含まれるなら
`G` は正規 `p`-補群をもつ。

**Burnside の正規 `p`-補群定理も transfer 理論も使わない**: `P ≤ Z(G)` から `P ⊴ G` で
`|P|` と `|G:P|` は互いに素なので **Schur–Zassenhaus** が補群 `K` を与える。`P` が中心的
なので `G = P·K` の共役は `K` を保ち `K ⊴ G`、すなわち `K` が正規 `p`-補群。 -/
theorem hasNormalPComplement_of_sylow_le_center [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hZ : (P : Subgroup G) ≤ Subgroup.center G) :
    HasNormalPComplement p G := by
  classical
  have hPnormal : (P : Subgroup G).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hc : g * n = n * g := Subgroup.mem_center_iff.mp (hZ hn) g
    have hfix : g * n * g⁻¹ = n := by rw [hc]; group
    rw [hfix]
    exact hn
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hcop : Nat.Coprime (Nat.card ↥(P : Subgroup G)) (P : Subgroup G).index := by
    rw [hm]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr P.not_dvd_index)
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hmul : ((⊤ : Subgroup G) : Set G) = ((P : Subgroup G) : Set G) * (K : Set G) := by
    have h := Subgroup.normal_mul (N := (P : Subgroup G)) (H := K)
    rw [hK.sup_eq_top] at h
    exact h
  have hKnormal : K.Normal := by
    refine ⟨fun y hy g => ?_⟩
    have hgin : g ∈ ((P : Subgroup G) : Set G) * (K : Set G) := by
      rw [← hmul]; exact Subgroup.mem_top g
    obtain ⟨x, hx, k, hk, rfl⟩ := hgin
    have hxc : ∀ h : G, h * x = x * h := Subgroup.mem_center_iff.mp (hZ hx)
    have heq : x * k * y * (x * k)⁻¹ = k * y * k⁻¹ := by
      calc x * k * y * (x * k)⁻¹ = x * (k * y * k⁻¹) * x⁻¹ := by group
        _ = k * y * k⁻¹ * x * x⁻¹ := by rw [← hxc (k * y * k⁻¹)]
        _ = k * y * k⁻¹ := by group
    rw [heq]
    exact K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk)
  refine hasNormalPComplement_of_normal_of_index_eq_pow (X := K) (a := m) ?_ ?_
  · rw [← hK.symm.index_eq_card]
    exact P.not_dvd_index
  · rw [hK.index_eq_card, hm]

/-- **5D.2 の後半 (Burnside の別証明)**: `P ⊆ Z(N_G(P))` から `G` の正規 `p`-補群を、
Burnside の定理 (Thm 5.13, transfer 経由) を使わずに導く。

`N := N_G(P)` の中で `P` は中心的なので **5D.2 前半** (Schur–Zassenhaus のみ) が
`N` の正規 `p`-補群を与える。`P` は可換なので **Cor 5.23**
(`APrime_normalizer_eq_subgroupOf_APrime_of_isMulCommutative_sylow`) が `N` の `p`-transfer
制御を与え、**Problem 5D.1** で `G` に持ち上がる。

⚠ statement 自体は既存の `hasNormalPComplement_of_sylow_normalizer_le_centralizer`
(Thm 5.13) と同一なので、ラッパー方針に従い定理としては再掲せず `example` で導出のみ検証する。 -/
example [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((P : Subgroup G) : Set G)) :
    HasNormalPComplement p G := by
  classical
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  have hPab : IsMulCommutative ↥(P : Subgroup G) := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    exact Subgroup.mem_centralizer_iff.mp (hP (hPN y.2)) _ x.2
  -- `N_G(P)` の中で `P` は中心的
  have hcentral : ((P.subtype hPN : Sylow p ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)))
      : Subgroup ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)))
      ≤ Subgroup.center ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
    intro x hx
    refine Subgroup.mem_center_iff.mpr fun n => Subtype.ext ?_
    exact (Subgroup.mem_centralizer_iff.mp (hP n.2) _ hx).symm
  exact hasNormalPComplement_of_controlsPTransfer P hPN
    (APrime_normalizer_eq_subgroupOf_APrime_of_isMulCommutative_sylow P)
    (hasNormalPComplement_of_sylow_le_center (P.subtype hPN) hcentral)

end

end OddOrder.Isaacs.Ch05
