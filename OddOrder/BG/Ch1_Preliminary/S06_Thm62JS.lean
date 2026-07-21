/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S06_Additional
import OddOrder.BG.AppB_Thm62
import OddOrder.BG.AppA_PStability
import OddOrder.GroupTheory.GlaubermanZJ

/-!
# BG Theorem 6.2 一般形 (literal Thompson `J(S)`): `Z(J(S))·O_{p'}(G) ⊴ G` の `O_{p'}` 簡約

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §6, **Thm 6.2** (mmd L1990): `G` solvable odd, `p` prime,
`S ∈ Syl_p(G)` ⟹ `Z(J(S))·O_{p'}(G) ⊴ G` (literal Thompson `J(S)`). Issue 3017.

ここでは `Z(J(S))` を `C_G(J(S)) ⊓ J(S)` (= `J(S)` の中心の `G`-realization) で符号化する
(AppB の `zCenterLOdd = C_G(L(S)) ⊓ L(S)` と同じ符号化).

## このファイルの成果 (Part 1: `O_{p'}` 簡約, 条件付き)

`zCenterThompsonJ_sup_oPiCore_normal_of_reduced` — **BG Thm 6.2 一般形の `O_{p'}` 簡約**を
sorry-free の**条件付き補題**として与える: `Ḡ = G/O_{p'}(G)` へ商を取り, その `O_{p'}=1`
特殊化 (`hZJ`, 下記) を全 odd solvable G へ持ち上げる. これは L(S) 版
`OddOrder.BG.AppB.zCenter_lOdd_sup_oPiCore_normal` (`AppB_Thm62.lean`) の簡約を J(S) で
構造的にミラーしたもの. 使う共変性は既存:

* `Subgroup.thompsonJ_map_of_coprime_kernel` (Isaacs Ch07, S7B2) — `J` の `p'`-商共変性
  `J(S̄) = mk(J(S))` (`S ∩ O_{p'} = ⊥` ゆえ `mk` は `S` 上単射).
* `OddOrder.BG.AppB.map_centralizer_inf` — `C_G(L) ⊓ L` の単射 hom 共変性 (任意 `L` で成立)。

## ✅ 本定理 (2026-07-21 完成): `zCenterThompsonJAbelian_sup_oPiCore_normal`

**BG Thm 6.2 一般形は無条件で完成** — literal `J(S)` は Gorenstein 版 abelian
Thompson subgroup `Subgroup.thompsonJAbelian` (issue 9403 の設計裁定; BG は `J` を
自前定義せず "**G**" を引用するのみ) で, Glauberman `Z(J)`-定理本体
(`GroupTheory/GlaubermanZJ.lean`, Gorenstein Ch.8 §2 の完全形式化) に商の
p-stability (`AppA.isPStableOp_of_odd_solvable`) + p-constraint (Hall-Higman) を
供給して閉じた. 以下の elementary-`thompsonJ` 版の条件付き補題は歴史的経緯
(elementary 版では Gorenstein Lem 2.1 が偽で `hZJ` は discharge 不能).

## (歴史) 未充足の前提 `hZJ` (= Glauberman `Z(J)`-定理, elementary 版符号)

`hZJ` は **`O_{p'}(H)=1` の odd solvable `H` に対する `Z(J(T)) ⊴ H` (T ∈ Syl_p)** で,
これは **Glauberman の `Z(J)`-定理そのもの**である. Isaacs FGT はこれを**明示的に省く**
(Isaacs p.217; だからこそ本リポジトリは Puig の L(S) 代替 `AppB` を構築した).

repo の既存 J-エントリ `OddOrder.Isaacs.Ch07.normal_J` は **`J(P) ⊴ G`** を結論するが,
**`C_G(Z(P)) = P`** (P self-centralizing) を要求する. この仮説は `O_{p'}=1` odd solvable G で
**自動でない** (P が非可換だと `Z(P) < P` で `C_G(Z(P))` が真に大きくなり得る; 反例:
`G = P ⋊ C_r`, `P` extraspecial exponent-`p` order `p³`, `C_r ≤ SL(2,p)` が `Z(P)` を
点ごとに固定 ⟹ `C_G(Z(P)) = G ≠ P`). ゆえに reduced J-case `S06_Additional.normalJ_normal_of_odd`
からは Thm 6.2 一般形 (`C_G(Z(P))=P` 無し) を導けない. `hZJ` を discharge するには
`C_G(O_p(G)) ≤ O_p(G)` (= p-constrained; `O_{p'}=1` solvable で成立, 既存
`Isaacs.Ch07.centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot`) + p-stability (odd) を用いた
**Glauberman ZJ 本体**を新規形式化する必要がある (major; book 推奨代替 = L(S) 版は既に完了).
-/

namespace OddOrder.BG.Ch1.S06

open OddOrder.Isaacs.Ch03

universe u

variable {G : Type u} [Group G]

/-- **BG Theorem 6.2 一般形 (literal `J(S)`) の `O_{p'}` 簡約 (条件付き)**.

`hZJ` = **`O_{p'}(H)=1` 特殊化** (`Z(J(T)) ⊴ H` for odd solvable `H`, `T ∈ Syl_p(H)`;
`Z(J(T))` は `C_H(J(T)) ⊓ J(T)`) を仮定すると, 任意 odd solvable `G`, `S ∈ Syl_p(G)` に対し
`Z(J(S))·O_{p'}(G) ⊴ G` (積を `⊔` で符号化) が従う.

証明は `Ḡ = G/O_{p'}(G)` への商 (L(S) 版 `AppB.zCenter_lOdd_sup_oPiCore_normal` の
構造的ミラー): `O_{p'}(Ḡ)=1` (`oPiCore_quotient_self_eq_bot`), `S̄ = mk(S) ≅ S`
(∵ `S ∩ O_{p'} = ⊥`) ゆえ `J(S̄) = mk(J(S))` (`thompsonJ_map_of_coprime_kernel`) かつ
`Z(J(S̄)) = mk(Z(J(S)))` (`map_centralizer_inf`). `hZJ` で `Z(J(S̄)) ⊴ Ḡ`, その `mk⁻¹` が
`Z(J(S))·O_{p'} = mk⁻¹(Z(J(S̄)))` (`comap` が正規性を保つ).

`hZJ` は Glauberman の `Z(J)`-定理そのもの (Isaacs FGT が省く未形式化前提; ファイル冒頭 docstring 参照). -/
theorem zCenterThompsonJ_sup_oPiCore_normal_of_reduced [Finite G] {p : ℕ} [Fact p.Prime]
    (_hp_odd : p ≠ 2) (hsolv : IsSolvable G) (hodd : Odd (Nat.card G)) (S : Sylow p G)
    (hZJ : ∀ (H : Type u) [Group H] [Finite H], IsSolvable H → Odd (Nat.card H) →
      oPiCore {q | q ≠ p} H = ⊥ → ∀ (T : Sylow p H),
        (Subgroup.centralizer (Subgroup.thompsonJ (T : Subgroup H) p : Set H) ⊓
          Subgroup.thompsonJ (T : Subgroup H) p).Normal) :
    (Subgroup.centralizer (Subgroup.thompsonJ (S : Subgroup G) p : Set G) ⊓
        Subgroup.thompsonJ (S : Subgroup G) p ⊔ oPiCore {q | q ≠ p} G).Normal := by
  haveI : IsSolvable G := hsolv
  set N := oPiCore {q | q ≠ p} G with hN_def
  haveI hN_normal : N.Normal := by rw [hN_def]; infer_instance
  set J := Subgroup.thompsonJ (S : Subgroup G) p with hJ_def
  -- `¬ p ∣ |N|` (N は `p'`-群)
  have hpN : ¬ p ∣ Nat.card ↥N := fun hd =>
    (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup {q | q ≠ p} p
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩)) rfl
  -- `S ∩ N = ⊥` (p-群 ∩ p'-群)
  have hSN : (↑S : Subgroup G) ⊓ N = ⊥ := by
    have hpg : IsPGroup p ↥((↑S : Subgroup G) ⊓ N) := S.2.to_inf_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
    have hdvd : Nat.card ↥((↑S : Subgroup G) ⊓ N) ∣ Nat.card ↥N := by
      rw [← Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : (↑S : Subgroup G) ⊓ N ≤ N)).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    rw [Subgroup.eq_bot_iff_card, hk]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero]
    · exact absurd (dvd_trans (dvd_pow_self p hkpos.ne') (hk ▸ hdvd)) hpN
  -- `mk` は `S` 上単射
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp (↑S : Subgroup G).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : G) ∈ N := by rw [← QuotientGroup.ker_mk' N]; exact hx
    have hxSN : (x : G) ∈ (↑S : Subgroup G) ⊓ N := ⟨x.2, hxN⟩
    rw [hSN, Subgroup.mem_bot] at hxSN
    exact Subtype.ext hxSN
  -- `mk` は `J = J(S) ≤ S` 上単射
  have hJ_le_S : J ≤ (↑S : Subgroup G) := hJ_def ▸ Subgroup.thompsonJ_le _ _
  have hinjJ : Function.Injective ((QuotientGroup.mk' N).comp J.subtype) := by
    have heq : (QuotientGroup.mk' N).comp J.subtype
        = ((QuotientGroup.mk' N).comp (↑S : Subgroup G).subtype).comp
            (Subgroup.inclusion hJ_le_S) := by
      ext x; rfl
    rw [heq]; exact hinj.comp (Subgroup.inclusion_injective _)
  -- `S̄ ∈ Syl_p(Ḡ)`, `↑S̄ = mk(S)`
  set Sbar : Sylow p (G ⧸ N) := S.mapSurjective (QuotientGroup.mk'_surjective N) with hSbar_def
  have hSbar_coe : (↑Sbar : Subgroup (G ⧸ N)) = (↑S : Subgroup G).map (QuotientGroup.mk' N) := rfl
  -- `J` の共変性: `J(S̄) = mk(J(S))`
  have hJimg : J.map (QuotientGroup.mk' N) = Subgroup.thompsonJ (↑Sbar : Subgroup (G ⧸ N)) p := by
    rw [hSbar_coe, hJ_def, OddOrder.Isaacs.Ch07.thompsonJ_map_of_coprime_kernel hpN S.2]
  -- `Ḡ` は odd
  have hoddbar : Odd (Nat.card (G ⧸ N)) := by
    obtain ⟨c, hc⟩ := N.index_dvd_card
    rw [hc] at hodd
    exact (Nat.odd_mul.mp hodd).1
  -- `Z(J(S̄)) ⊴ Ḡ` (仮説 `hZJ` を `Ḡ`, `S̄` へ適用; `O_{p'}(Ḡ)=1`)
  have hZbar : (Subgroup.centralizer
        (Subgroup.thompsonJ (↑Sbar : Subgroup (G ⧸ N)) p : Set (G ⧸ N)) ⊓
        Subgroup.thompsonJ (↑Sbar : Subgroup (G ⧸ N)) p).Normal :=
    hZJ (G ⧸ N) inferInstance hoddbar (oPiCore_quotient_self_eq_bot {q | q ≠ p}) Sbar
  -- 中心の共変性: `mk(Z(J(S))) = Z(J(S̄))`
  have hcov : (Subgroup.centralizer (J : Set G) ⊓ J).map (QuotientGroup.mk' N)
      = Subgroup.centralizer (Subgroup.thompsonJ (↑Sbar : Subgroup (G ⧸ N)) p : Set (G ⧸ N)) ⊓
          Subgroup.thompsonJ (↑Sbar : Subgroup (G ⧸ N)) p := by
    rw [OddOrder.BG.AppB.map_centralizer_inf (QuotientGroup.mk' N) hinjJ, hJimg]
  -- `Z(J(S))·O_{p'} = mk⁻¹(Z(J(S̄)))`, ゆえ正規
  have hassemble : Subgroup.centralizer (J : Set G) ⊓ J ⊔ N
      = (Subgroup.centralizer (Subgroup.thompsonJ (↑Sbar : Subgroup (G ⧸ N)) p : Set (G ⧸ N)) ⊓
          Subgroup.thompsonJ (↑Sbar : Subgroup (G ⧸ N)) p).comap (QuotientGroup.mk' N) := by
    rw [← hcov, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  rw [hassemble]
  exact hZbar.comap (QuotientGroup.mk' N)

/-! ### BG Thm 6.2 一般形 (literal `J(S)` = Gorenstein 版 `J_a`, 無条件)

BG の literal `J(S)` は **Gorenstein 版 abelian Thompson subgroup**
`Subgroup.thompsonJAbelian` である (BG は `J` を自前定義せず "**G**, Thm 6.5.1 /
8.2.11" を引用するのみ — 記号表 p.170; issue 9403 の設計裁定)。Glauberman
`Z(J)`-定理本体 (`GroupTheory/GlaubermanZJ.lean`, Gorenstein Ch.8 §2) の完成により
無条件で閉じる。上の elementary-`thompsonJ` 版条件付き補題 (`hZJ` 付き) は
BG literal との符号ミスマッチがあり (elementary 版では Gorenstein Lem 2.1 が偽で
`hZJ` を discharge できない)、こちらが本物。 -/

open Subgroup in
/-- **BG Theorem 6.2 一般形 (literal Thompson `J(S)`, 無条件)**: `G` odd solvable,
`p` odd prime, `S ∈ Syl_p(G)` ⟹ `Z(J(S))·O_{p'}(G) ⊴ G` (`⊔` 符号化,
`J = thompsonJAbelian`).

証明 = Gorenstein Thm 8.2.11 の引き戻し形
(`Subgroup.zCenter_thompsonJAbelian_sup_oPiCorePrime_normal`) へ商
`Ḡ = G/O_{p'}(G)` の p-stability (`AppA.isPStableOp_of_odd_solvable` =
Gorenstein 6.5.3 / BG Thm A.4 系) と p-constraint (Hall-Higman
`hall_higman_solvable_specialization` = BG Prop 1.15(a)) を供給。
Issue 3017/3024/9403. -/
theorem zCenterThompsonJAbelian_sup_oPiCore_normal [Finite G] {p : ℕ} [Fact p.Prime]
    (hp_odd : p ≠ 2) (hsolv : IsSolvable G) (hodd : Odd (Nat.card G)) (S : Sylow p G) :
    (Subgroup.centralizer (Subgroup.thompsonJAbelian (S : Subgroup G) : Set G)
        ⊓ Subgroup.thompsonJAbelian (S : Subgroup G)
      ⊔ oPiCore {q | q ≠ p} G).Normal := by
  haveI : IsSolvable G := hsolv
  set N := oPiCore {q | q ≠ p} G with hN_def
  have hoddbar : Odd (Nat.card (G ⧸ N)) := by
    obtain ⟨c, hc⟩ := N.index_dvd_card
    rw [hc] at hodd
    exact (Nat.odd_mul.mp hodd).1
  -- p-stability on `Ḡ` (Gorenstein 6.5.3)
  have hstable : Subgroup.IsPStableOp p (G ⧸ N) :=
    OddOrder.BG.AppA.isPStableOp_of_odd_solvable hp_odd inferInstance hoddbar
  -- p-constraint on `Ḡ` (Hall-Higman; `O_{p'}(Ḡ) = ⊥`)
  have hset : {q | q ∉ ({p} : Set ℕ)} = {q | q ≠ p} := by ext q; simp
  have hconstr := OddOrder.BG.Ch1.S01.hall_higman_solvable_specialization
    (p := p) (G := G ⧸ N)
    (by rw [hset]; exact oPiCore_quotient_self_eq_bot {q | q ≠ p})
  rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore] at hconstr
  exact Subgroup.zCenter_thompsonJAbelian_sup_oPiCorePrime_normal hp_odd hstable
    hconstr S

end OddOrder.BG.Ch1.S06
