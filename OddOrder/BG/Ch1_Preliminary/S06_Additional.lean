/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.Main
import OddOrder.GroupTheory.ThompsonSubgroup

/-!
# BG §6: Additional Results — the normal-J hub (FT critical)

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §6 (pp. 49-66), mmd `references/bg/local-analysis.mmd`
L1957-2128, **7 結果** (Thm 6.1, 6.2, 6.3, 6.4, 6.7 + Lem 6.5, 6.6).

§6 は局所解析の「道具袋」で、特に **Thm 6.2 `Z(J(S))·O_{p'}(G) ⊴ G`** が §7-§9
(Uniqueness) と App.A-C で **7+ 箇所**引用される FT クリティカルパスの核心。

## BG "**G**" 引用 → Isaacs FGT / mathlib / shared module 対応

CLAUDE.md no-wrapper policy 準拠: 完成済 Isaacs Ch.7 を直接呼ぶ。教科書間対応は本表に記録。

| BG | 内容 | Isaacs FGT / repo | 状態 |
|---|---|---|---|
| **Thm 6.1** | G solvable odd, S∈Syl_p ⇒ `O_{p',p}(G)` が S の全 abelian normal 部分群を含む | Thm 3.21 (Hall-Higman 1.2.3) `hall_higman_1_2_3` の系 / `normal_J` 中間補題 | core 完成 (本ファイル), 一般形 TODO |
| **Thm 6.2** | (normal-J) G solvable odd, S∈Syl_p ⇒ `Z(J(S))·O_{p'}(G) ⊴ G` | **Thm 7.6** `OddOrder.Isaacs.Ch07.normal_J` (odd-order 等価) | core 完成 (本ファイル, reduced case), 一般形 (O_{p'} 簡約) TODO |
| 6.3-6.7, 6.5-6.6 | solvable + p-length 1 + Frobenius factorization | Isaacs Ch.5/Ch.7 | TODO |

## このコミット (core results)

`OddOrder.Isaacs.Ch07.normal_J` は `P = C_G(Z(P))` + `O_{p'}(G) = ⊥` の **reduced
case** で `J(P) ⊴ G` を与える。本ファイルでは、その awkward な仮説のうち **奇数位数で
自動充足する 2 つ** を discharge する:

- `h2abelian` (Sylow-2 が可換) — 奇数位数では 2-部分群が自明 (`comm_of_isPGroup_two_of_odd`)。
- `h_pSolvable` (p-separable) — `[IsSolvable G]` から `isPiSeparable_of_solvable` instance で自動。

残る `O_{p'}(G) = ⊥` と `P = C_G(Z(P))` は reduced case の条件。BG Thm 6.2 の一般形
(`Z(J(S))·O_{p'}(G) ⊴ G`, 任意 S) は `O_{p'}(G)` で商を取り reduced case に簡約する
ステップが要る — 後続コミットで対応。
-/

namespace OddOrder.BG.Ch1.S06

open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-- 奇数位数群では `2`-部分群は自明、特に可換。

`OddOrder.Isaacs.Ch07.normal_J` の `h2abelian` 仮説 (Sylow-2 abelian) を奇数位数の下で
discharge するためのヘルパ。`IsPGroup 2 S` なら `|S| = 2^n` が奇数 `|G|` を割るので `n = 0`、
すなわち `S` は自明。 -/
private theorem comm_of_isPGroup_two_of_odd [Finite G]
    (hodd : Odd (Nat.card G)) :
    ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S hS x y
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hS
  have hdvd : Nat.card ↥S ∣ Nat.card G := S.card_subgroup_dvd_card
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hcard : Nat.card ↥S = 1 := by rw [hn, pow_zero]
    haveI : Subsingleton ↥S := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact Subsingleton.elim _ _
  · exfalso
    have h2dvd : (2 : ℕ) ∣ Nat.card G :=
      (dvd_pow_self 2 hnpos.ne').trans (hn ▸ hdvd)
    rw [Nat.odd_iff] at hodd
    omega

/-- **BG Thm 6.1 (core / reduced case)** = Isaacs Thm 7.6 中間結果の奇数位数特殊化。

奇数位数 solvable `G`、`p ≠ 2`、`P ∈ Syl_p(G)` で `O_{p'}(G) = ⊥` かつ `P = C_G(Z(P))`
のとき、Thompson 部分群 `J(P)` は `O_p(G)` に含まれる。

`O_{p'}(G) = ⊥` の下では `O_{p',p}(G) = O_p(G)` なので、これは BG Thm 6.1
(`O_{p',p}(G) ⊇` S の abelian normal 部分群) の `J(P)` インスタンス (reduced case)。 -/
theorem thompsonJ_le_opCore_of_odd [Finite G]
    (hodd : Odd (Nat.card G)) [IsSolvable G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hp2 : p ≠ 2)
    (h_oPiPrime_trivial : Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
      Subgroup.centralizer
        (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
        = (P : Subgroup G)) :
    Subgroup.thompsonJ (P : Subgroup G) p ≤ Ch01.opCore p G :=
  Ch07.thompsonJ_le_opCore_of_normal_J_hypotheses P hp2 inferInstance
    (comm_of_isPGroup_two_of_odd hodd) h_oPiPrime_trivial h_centralizer_center

/-- **BG Thm 6.2 (core / reduced case)** = Isaacs Thm 7.6 (`normal_J`) の奇数位数特殊化。

奇数位数 solvable `G`、`p ≠ 2`、`P ∈ Syl_p(G)` で `O_{p'}(G) = ⊥` かつ `P = C_G(Z(P))`
のとき、`J(P) ⊴ G`。

BG Thm 6.2 (`Z(J(S))·O_{p'}(G) ⊴ G`, 任意 S) の reduced case。一般形は `O_{p'}(G)` で商を
取り本定理に簡約する (後続コミット)。 -/
theorem normalJ_normal_of_odd [Finite G]
    (hodd : Odd (Nat.card G)) [IsSolvable G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hp2 : p ≠ 2)
    (h_oPiPrime_trivial : Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
      Subgroup.centralizer
        (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
        = (P : Subgroup G)) :
    (Subgroup.thompsonJ (P : Subgroup G) p).Normal :=
  Ch07.normal_J P hp2 inferInstance
    (comm_of_isPGroup_two_of_odd hodd) h_oPiPrime_trivial h_centralizer_center

end OddOrder.BG.Ch1.S06
