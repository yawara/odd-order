/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S02_Representations

/-!
# BG §4: p-Groups of Small Rank

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §4 (pp. 33-43), mmd
`references/bg/local-analysis.mmd` L1359-1788, **20 結果** (Lemma/Prop/Thm/Cor
4.1-4.20).

## 構造 (BG §4)

- **§4A** class ≤ 2/3 の冪・交換子 (Lemma 4.1-4.3)
- **§4B** SCN・normal `E_{p²}` の存在 (Prop 4.4-4.6)
- **§4C** rank ↔ SCN₃, `Ω₁` 構造 (Lemma 4.7-4.10)
- **§4D** Huppert metacyclic 判定 + operator (Prop 4.11, Thm 4.12)
- **§4E** `Aut R` の位数制約 + extraspecial (Lemma 4.13-4.15)
- **§4F** Blackburn 分類 (Thm 4.16)
- **§4G** solvable operator の導来部分群 (Lemma 4.17)
- **§4H** solvable odd group の構造定理 (Thm 4.18, Cor 4.19, Thm 4.20)

## Current status

本ファイルは §4 の **§4G (Lemma 4.17) の証明で必要な再利用補題**から着手する。
Lemma 4.17 (`A` solvable `p'`-operator, `r(R) ≤ 2`, `|A|` odd ⇒ `A'` は `p`-群)
の BG 原証明 (mmd L1706-1732) は次の 4 部品を組む:

1. (4.16) `C_A(H)` が `p`-群 (`H` = Thompson critical の `Ω₁(C)`).
   利用可能: `thompson_critical_omega` (`S01_Solvable`) が
   `IsPGroup p (autCentralizer H)` を供給する。
2. (4.17) `|H| ≤ p³` (Prop 4.8 — `r(R) ≤ 2` + exponent `p`).
   **未実装** (rank 理論 `pRank`/`m` が `OddOrder.GroupTheory.PRank` で def のみ)。
3. (4.18) `C := C_A(H/Φ(H))` が `p`-群 (Burnside Thm 1.8 で `C/C_A(H)` が `p`-群).
   Burnside は `burnside_operator` (`S01_Solvable`) で利用可能。
4. `m(V) = 2` のとき `Aut V ≅ GL(2,p)` で `(A/C)'` が `p`-群 (BG Thm 2.6).
   **本ファイルで供給** (`isPGroup_commutator_of_faithful_two_dim_charP`).

現状のゲートは (2) の Prop 4.8 + `m(V) ≤ 2` を与える rank 機構 (設計書 Wave 0)。
本ファイルでは部品 (4) = Blackburn 4.16 / Lemma 4.17 の `m(V) = 2` 分岐エンジン
であり Cor 4.19 でも直接引かれる「2 次元 faithful 表現 ⇒ 導来部分群が `p`-群」
を切り出して実装する。Lemma 4.17 本体は rank 機構の整備後に本ファイルへ追加する。

## References

- BG mmd `references/bg/local-analysis.mmd` L1359-1788 (Lemma 4.17 L1706-1732,
  Thm 2.6 L774-793, Cor 4.19 L1750-1762).
- Section note: `notes/bg/s04_pgroups_small_rank.md`,
  `notes/bg/s04_implementation_plan_2026_05_30.md`.
- BG Thm 2.6 (2 次元 faithful 表現): `OddOrder.BG.Ch1.S02.odd_two_dim_abelian`,
  `OddOrder.BG.Ch1.S02.odd_two_dim_sylow_abelian`
  (`OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`).
- BG Thm 1.13 (Thompson critical): `OddOrder.BG.Ch1.thompson_critical_omega`.
- BG Thm 1.8 (Burnside operator): `OddOrder.BG.Ch1.burnside_operator`.
-/

namespace OddOrder.BG.Ch1.S04

open OddOrder.BG.Ch1.S02

/-! ## §4F/§4G: 2 次元 faithful 表現の導来部分群 (Blackburn 4.16 / Lemma 4.17 の
`GL(2,p)` 分岐エンジン)

BG Theorem 4.16 の証明 (mmd L1732) と Lemma 4.17 の `m(V) = 2` の場合は
「`Aut V ≅ GL(2,p)` かつ `A/C` が `V` に faithful に作用するから, Theorem 2.6
により `(A/C)'` は `p`-群」と進む。Corollary 4.19 (mmd L1758) でも
「`G/C` が `U/V` に faithful かつ irreducible に作用するから `(G/C)'` は `p`-群」
として同じ帰結を用いる。

ここでは BG Thm 2.6(b) (`odd_two_dim_sylow_abelian`) を直接の再利用形
「奇数位数 `G` が標数 `p` の体上 2 次元 faithful 表現を持てば `G'` は `p`-群」
に整える。BG が `(A/C)'` を `p`-群と断ずる箇所はすべてこの形で読み替えられる。
-/

/-- **BG Theorem 2.6(b) の導来部分群形** (Blackburn 4.16 / Lemma 4.17 の `m(V)=2`
分岐エンジン, Cor 4.19 のエンジン).

奇数位数の有限群 `G` が標数 `p`(`p ∣ |G|`)の体 `F` 上で `2` 次元の faithful な
表現 `ρ` を持つとき, 導来部分群 `G'` (`commutator G`) は `p`-群である。

BG 原文では Lemma 4.17 (mmd L1732) と Cor 4.19 (mmd L1758) で
「`Aut V ≅ GL(2,p)` (resp. faithful irreducible on `U/V`) ゆえ Theorem 2.6 により
`(A/C)'` (resp. `(G/C)'`) は `p`-群」と一言で済ませる部分にあたる。

証明: Thm 2.6(b) (`odd_two_dim_sylow_abelian`) より, `p`-Sylow `P` は abelian で
`G' ≤ P` を満たす。`P` は `p`-群 (`Sylow.isPGroup'`) なので, その部分群
`G'` も `p`-群 (`IsPGroup.to_le`)。`Finite (Sylow p G)` は有限群から従う。 -/
theorem isPGroup_commutator_of_faithful_two_dim_charP
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (hdim : Module.finrank F V = 2) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    {p : ℕ} [Fact p.Prime] (hp_dvd : p ∣ Nat.card G) (hchar : CharP F p) :
    IsPGroup p (commutator G) := by
  -- 標準的な `p`-Sylow を取り Thm 2.6(b) を適用する。
  let P : Sylow p G := default
  obtain ⟨_hPab, hcomm_le⟩ :=
    odd_two_dim_sylow_abelian hodd hdim ρ hfaithful hp_dvd hchar P
  -- `P` は `p`-群, ゆえに `G' ≤ P` も `p`-群。
  exact P.isPGroup'.to_le hcomm_le

end OddOrder.BG.Ch1.S04
