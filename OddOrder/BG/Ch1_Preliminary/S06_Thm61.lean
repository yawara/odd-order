/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppA_PStability

/-!
# BG §6: Theorem 6.1 (P. Hall & G. Higman) — 全素数版

Bender–Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
Chapter I §6 (p. 49), mmd `references/bg/local-analysis.mmd` L1986。

> **Theorem 6.1 (P. Hall & G. Higman).** Suppose `G` is a solvable group of odd order,
> `p` is a prime, and `S` is a Sylow `p`-subgroup of `G`. Then `O_{p',p}(G)` contains
> every abelian normal subgroup of `S`.

**本体は App.A に在る**: BG 自身が App.A で "Note that Theorem A.4(b) is just
Theorem 6.1" (mmd L4627) と述べており, 証明済みの `OddOrder.BG.AppA.thmA4b` が
そのまま本定理である。App.A は「主として Theorem 6.1 を証明するための付録」
(mmd L4595) なので, この依存方向 (§6 → App.A) は教科書どおり。

本ファイルが足すのは **`p ≠ 2` 仮定の除去**のみ: `thmA4b` は `p ≠ 2` を仮定するが,
教科書の Theorem 6.1 は「`p` is a prime」と任意素数で述べている。奇数位数群では
Sylow `2`-部分群が自明ゆえ `p = 2` の場合は `A = ⊥` で自明に成立する。よって本ファイルの
定理は教科書の文言どおりの全素数版であり, §6 側の名前で引用できるようにしたもの。
-/

namespace OddOrder.BG.Ch1.S06

open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-- **BG Theorem 6.1** (P. Hall & G. Higman; mmd L1986): `G` を奇数位数の可解群,
`p` を**任意の**素数, `S ∈ Syl_p(G)` とする。このとき `O_{p',p}(G)` は `S` の任意の
abelian normal 部分群を含む。

「`A` は `S` の abelian normal 部分群」は `A ≤ S` (`hA_le`) と `S ≤ N_G(A)` (`hA_norm`),
および `[IsMulCommutative A]` で表現している。

**証明**: `p ≠ 2` の場合はそのまま `OddOrder.BG.AppA.thmA4b` (BG 自身が mmd L4627 で
"Theorem A.4(b) is just Theorem 6.1" と同一視する App.A の本体定理)。`p = 2` の場合は
`|G|` が奇数ゆえ Sylow `2`-部分群 `S` が自明で, `A ≤ S = ⊥` より自明に成立。
`thmA4b` が担う数学的内容はすべて App.A 側にあり, 本定理はその `p ≠ 2` 仮定を
教科書どおり任意素数へ外したもの。 -/
theorem le_oPiPrimePiCore_of_abelian_normal_in_sylow [Finite G]
    (hsolv : IsSolvable G) (hodd : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) {A : Subgroup G}
    (hA_le : A ≤ (S : Subgroup G))
    (hA_norm : (S : Subgroup G) ≤ Subgroup.normalizer (A : Set G))
    [IsMulCommutative A] :
    A ≤ Ch03.oPiPrimePiCore ({p} : Set ℕ) G := by
  rcases eq_or_ne p 2 with rfl | hp2
  · -- `|G|` odd ⇒ the Sylow `2`-subgroup is trivial ⇒ `A = ⊥`.
    have hbot : (S : Subgroup G) = ⊥ := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp S.2
      have hdvd : Nat.card ↥(S : Subgroup G) ∣ Nat.card G :=
        (S : Subgroup G).card_subgroup_dvd_card
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · exact Subgroup.eq_bot_of_card_eq _ (by rw [hn, hn0, pow_zero])
      · exfalso
        have h2dvd : (2 : ℕ) ∣ Nat.card G := (dvd_pow_self 2 hnpos.ne').trans (hn ▸ hdvd)
        rw [Nat.odd_iff] at hodd
        omega
    rw [hbot] at hA_le
    exact hA_le.trans bot_le
  · exact AppA.thmA4b hp2 hsolv hodd S hA_le hA_norm

end OddOrder.BG.Ch1.S06
