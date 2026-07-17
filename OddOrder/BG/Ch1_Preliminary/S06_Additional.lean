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
import OddOrder.GroupTheory.NarrowPGroup
import OddOrder.BG.Ch1_Preliminary.PLength
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Commutator

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
| **Lem 6.3(a)** | G solvable, H ⊴ G normal Hall 補群 K, H⊆G' ⇒ `⁅H,K⁆ = H` (∧ C_H(K)⊆H') | `commutator_eq_self_of_isComplement'_le_commutator` (§6.3, 本ファイル) | 第 1 結論 ✅ (Thm 10.6/Cor 10.7(a)/§15 が引用); C_H(K)⊆H' は §10 critical path 外で TODO |
| 6.3(b)-6.4, 6.7 | solvable + p-length 1 + Frobenius factorization | Isaacs Ch.5/Ch.7 | TODO |

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
open scoped commutatorElement

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

/-- **(infra)** `O_p(G) ≤ O_{p',p}(G)`: 正規 `p`-core は第 2 Fitting 層に含まれる。

BG Thm 6.1/6.2 が含意を `O_{p',p}(G)` で述べるための再利用可能な橋。`O_p(G)` の
`G ⧸ O_{p'}(G)` への像は正規 `{p}`-群なので `O_p(G ⧸ O_{p'}(G)) = O_{q∉{p}}(...)` に含まれ、
引き戻すと `O_{p',p}(G)`。 -/
theorem opCore_le_oPiPrimePiCore [Finite G] (p : ℕ) [Fact p.Prime] :
    Ch01.opCore p G ≤ Ch03.oPiPrimePiCore {p} G := by
  have hmap_le : (Ch01.opCore p G).map
      (QuotientGroup.mk' (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G)) ≤
      Ch03.oPiCore {p} (G ⧸ Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G) := by
    haveI : ((Ch01.opCore p G).map
        (QuotientGroup.mk' (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G))).Normal :=
      (Ch01.opCore.normal p G).map _ (QuotientGroup.mk'_surjective _)
    apply Ch03.Subgroup.IsPiGroup.le_oPiCore
    have hpg : IsPGroup p ((Ch01.opCore p G).map
        (QuotientGroup.mk' (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G))) :=
      (Ch01.opCore_isPGroup p G).map _
    intro q hq
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
    rw [hn, Nat.mem_primeFactors] at hq
    have hqp : q = p :=
      (Nat.prime_dvd_prime_iff_eq hq.1 Fact.out).mp (hq.1.dvd_of_dvd_pow hq.2.1)
    rw [hqp]
    exact Set.mem_singleton p
  exact Subgroup.map_le_iff_le_comap.mp hmap_le

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

/-- **BG Thm 6.1 (J(P)-instance, O_{p',p} 形)**: `thompsonJ_le_opCore_of_odd` を橋
`opCore_le_oPiPrimePiCore` で `O_{p',p}(G)` 形に持ち上げたもの。

奇数 solvable `G`、`p ≠ 2`、`P ∈ Syl_p`、`O_{p'}(G) = ⊥`、`P = C_G(Z(P))` で
`J(P) ≤ O_{p',p}(G)`。BG Thm 6.1 (任意 abelian normal 部分群 ⊆ `O_{p',p}`) の `J(P)`
特殊形 (reduced case)。一般形は別途 (notes/bg/s06_additional.md 残課題 3)。 -/
theorem thompsonJ_le_oPiPrimePiCore_of_odd [Finite G]
    (hodd : Odd (Nat.card G)) [IsSolvable G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hp2 : p ≠ 2)
    (h_oPiPrime_trivial : Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
      Subgroup.centralizer
        (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
        = (P : Subgroup G)) :
    Subgroup.thompsonJ (P : Subgroup G) p ≤ Ch03.oPiPrimePiCore {p} G :=
  (thompsonJ_le_opCore_of_odd hodd P hp2 h_oPiPrime_trivial h_centralizer_center).trans
    (opCore_le_oPiPrimePiCore p)

/-- `G = KU` (`K ⊴ G`) のとき `G' ≤ K · U'`: 商 `G/K` は `U` の像で生成され,
その像は可換 (`U'` が消える) なので `G/K` の commutator は像の commutator に一致。
(§6.3 と §6.5(a) の共有 helper。) -/
private theorem commutator_le_sup_commutator {K U : Subgroup G} [K.Normal]
    (hKU : K ⊔ U = ⊤) : commutator G ≤ K ⊔ ⁅U, U⁆ := by
  set q := QuotientGroup.mk' K with hq
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective K
  have hkerq : q.ker = K := by rw [hq, QuotientGroup.ker_mk']
  have hmapK : K.map q = ⊥ := (Subgroup.map_eq_bot_iff K).mpr hkerq.ge
  have hmapU : U.map q = ⊤ := by
    have h := congrArg (Subgroup.map q) hKU
    rwa [Subgroup.map_sup, hmapK, bot_sup_eq, Subgroup.map_top_of_surjective _ hsurj] at h
  -- 両辺の `q`-像が `⁅⊤,⊤⁆` で一致
  have hmapeq : (commutator G).map q = (K ⊔ ⁅U, U⁆).map q := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ hsurj, Subgroup.map_sup, hmapK,
      bot_sup_eq, Subgroup.map_commutator, hmapU]
  -- `K = ker q ≤ K ⊔ ⁅U,U⁆` ゆえ comap-map で復元
  calc commutator G ≤ Subgroup.comap q ((commutator G).map q) := Subgroup.le_comap_map _ _
    _ = Subgroup.comap q ((K ⊔ ⁅U, U⁆).map q) := by rw [hmapeq]
    _ = K ⊔ ⁅U, U⁆ := Subgroup.comap_map_eq_self (by rw [hkerq]; exact le_sup_left)

/-! ### 共役作用 bridge (Prop 1.6(d) の subgroup-共役版インターフェース)

`Prop 1.6(d)` (`S01.fixedPoints_isComplement_actionCommutator_of_abelian`) は抽象作用
`φ : A →* MulAut G` に対する命題。下の 2 bridge は `K ≤ N_Γ(P)` の `P` への共役作用について、
action commutator を ambient の `⁅P, K⁆` に、fixed points を `C_Γ(K) ⊓ P` に同定する。
Lemma 6.3(a) 第 2 結論 (本ファイル) と BG Lemma 12.1(f) (§12) で使用。 -/

section ConjugationActionBridges

variable {Γ : Type*} [Group Γ]

/-- Push-forward of the conjugation-action commutator: for `K ≤ N_Γ(P)`, the
`actionCommutator` of the conjugation action of `K` on `P` realizes the ambient
subgroup commutator `⁅P, K⁆`. -/
theorem actionCommutator_conj_map_subtype {P K : Subgroup Γ}
    (hKP : K ≤ Subgroup.normalizer (P : Set Γ)) :
    (Ch04.actionCommutator
        ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP))).map P.subtype
      = ⁅P, K⁆ := by
  rw [Ch04.actionCommutator, MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    refine ⟨(g : Γ), g.2, (a : Γ), a.2, ?_⟩
    rw [commutatorElement_def]
    have hcoe : (P.subtype
          (g * ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP)) a g⁻¹) : Γ)
        = (g : Γ) * ((a : Γ) * (g : Γ)⁻¹ * (a : Γ)⁻¹) := rfl
    rw [hcoe]
    group
  · rintro ⟨g, hg, a, ha, rfl⟩
    refine ⟨(⟨g, hg⟩ : ↥P) *
      ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP)) ⟨a, ha⟩ ⟨g, hg⟩⁻¹,
      ⟨⟨g, hg⟩, ⟨a, ha⟩, rfl⟩, ?_⟩
    rw [commutatorElement_def]
    have hcoe : (P.subtype
          ((⟨g, hg⟩ : ↥P) *
            ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP)) ⟨a, ha⟩
              (⟨g, hg⟩ : ↥P)⁻¹) : Γ)
        = g * (a * g⁻¹ * a⁻¹) := rfl
    rw [hcoe]
    group

/-- Push-forward of the conjugation-action fixed points: `C_Γ(K) ⊓ P`. -/
theorem fixedPointsOfMulAut_conj_map_subtype {P K : Subgroup Γ}
    (hKP : K ≤ Subgroup.normalizer (P : Set Γ)) :
    (Subgroup.fixedPointsOfMulAut
        ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP))).map P.subtype
      = Subgroup.centralizer (K : Set Γ) ⊓ P := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun k hk => ?_, x.2⟩
    have hfix := Subgroup.mem_fixedPointsOfMulAut.mp hx ⟨k, hk⟩
    have hcoe : k * (x : Γ) * k⁻¹ = (x : Γ) := congrArg Subtype.val hfix
    calc k * (x : Γ) = (k * x * k⁻¹) * k := by group
    _ = (x : Γ) * k := by rw [hcoe]
  · rintro ⟨hy, hyP⟩
    refine ⟨⟨y, hyP⟩, Subgroup.mem_fixedPointsOfMulAut.mpr fun a => Subtype.ext ?_, rfl⟩
    change (a : Γ) * y * (a : Γ)⁻¹ = y
    rw [hy (a : Γ) a.2]
    group

end ConjugationActionBridges

/-! ## 6.3: 可解群の normal Hall 補群と commutator (pp. 63-64, mmd L1981)

**Lemma 6.3(a)**: `G` 可解, `H ⊴ G` が補群 `K` を持ち (`H.IsComplement' K`), `H ⊆ G'` のとき
`H = ⁅H, K⁆` (かつ coprime 仮定の下で `C_H(K) ⊆ H'`)。Thm 10.6 Step 4 (`M_α = ⁅M_α, K⁆`),
Cor 10.7(a) (`⁅P, V⁆ = P`), §15 (`⁅M_σ, K⁆ = M_σ`) で第 1 結論を引用。第 1 結論には coprime
性は不要; 第 2 結論 `C_H(K) ⊆ H'` (`centralizer_inf_le_derivedInG_of_isComplement'`) は
`H/H'` への coprime 直積分解 (Prop 1.6(d)) を要し、Lemma 12.17 で引用。 -/

section /- 6.3 -/

/-- 共役 `x ↦ gxg⁻¹` (`g ∈ H ∪ K`, `H ⊴ G`) は `⁅H, K⁆` を保つ。`⁅H,K⁆` の `comap` への引き戻しは
全生成子 `⁅h,k⁆` を含む部分群: `g ∈ H` では `g⁅h,k⁆g⁻¹ = ⁅gh,k⁆·⁅g,k⁆⁻¹`, `g ∈ K` では
`conjugate_commutatorElement` (`H ⊴ G` で `ghg⁻¹ ∈ H`)。 -/
private theorem conj_mem_commutator_of_mem_sup {H K : Subgroup G} [hHN : H.Normal]
    {g : G} (hg : g ∈ H ∨ g ∈ K) {n : G} (hn : n ∈ ⁅H, K⁆) :
    g * n * g⁻¹ ∈ ⁅H, K⁆ := by
  have hsub : (⁅H, K⁆ : Subgroup G) ≤ (⁅H, K⁆).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro h hh k hk
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hg with hgH | hgK
    · have hid : g * ⁅h, k⁆ * g⁻¹ = ⁅g * h, k⁆ * ⁅g, k⁆⁻¹ := by group
      rw [hid]
      exact Subgroup.mul_mem _
        (Subgroup.commutator_mem_commutator (H.mul_mem hgH hh) hk)
        (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hgH hk))
    · rw [conjugate_commutatorElement]
      exact Subgroup.commutator_mem_commutator (hHN.conj_mem h hh g)
        (K.mul_mem (K.mul_mem hgK hk) (K.inv_mem hgK))
  have hmem := hsub hn
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmem

/-- `⁅H, K⁆ ⊴ G`, when `H ⊴ G` と `H ⊔ K = ⊤`: `H` と `K` の両方が `⁅H,K⁆` を正規化し
(`conj_mem_commutator_of_mem_sup`), 両者で `G` を生成する。 -/
private theorem commutator_normal_of_normal_sup_eq_top {H K : Subgroup G} [H.Normal]
    (hsup : H ⊔ K = ⊤) : (⁅H, K⁆ : Subgroup G).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup, sup_le_iff]
  have key : ∀ g : G, (g ∈ H ∨ g ∈ K) → g ∈ Subgroup.normalizer (⁅H, K⁆ : Subgroup G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => conj_mem_commutator_of_mem_sup hg hn, fun hn => ?_⟩
    have hg' : g⁻¹ ∈ H ∨ g⁻¹ ∈ K := hg.imp H.inv_mem K.inv_mem
    have h2 := conj_mem_commutator_of_mem_sup (g := g⁻¹) hg' hn
    have heq : g⁻¹ * (g * n * g⁻¹) * (g⁻¹)⁻¹ = n := by group
    rwa [heq] at h2
  exact ⟨fun g hg => key g (Or.inl hg), fun g hg => key g (Or.inr hg)⟩

/-- **BG Lemma 6.3(a)** (first conclusion, mmd L1981): `G` solvable, `H ⊴ G` with complement
`K` (`H.IsComplement' K`), and `H ⊆ G'`. Then `⁅H, K⁆ = H`.

Proof (BG): `N = ⁅H,K⁆ ⊴ G` (`N ≤ H`). In `Ḡ = G/N` the images `H̄, K̄` centralise each other
(`⁅H̄,K̄⁆ = 1`) and complement each other, so `K̄ ⊴ Ḡ`. From `H ⊆ G'` we get `H̄ ⊆ Ḡ'`, and
`Ḡ' ≤ K̄ ⊔ ⁅H̄,H̄⁆` (`commutator_le_sup_commutator`); the modular law plus `H̄ ⊓ K̄ = 1` gives
`H̄ ≤ ⁅H̄,H̄⁆`, i.e. `H̄` is perfect, hence trivial (`G/N` solvable). Thus `H ≤ N = ⁅H,K⁆`. -/
theorem commutator_eq_self_of_isComplement'_le_commutator [IsSolvable G]
    {H K : Subgroup G} [H.Normal] (hHK : H.IsComplement' K) (hH : H ≤ commutator G) :
    ⁅H, K⁆ = H := by
  have hsup : H ⊔ K = ⊤ := hHK.isCompl.sup_eq_top
  have hdisj : Disjoint H K := hHK.isCompl.disjoint
  haveI hN : (⁅H, K⁆ : Subgroup G).Normal := commutator_normal_of_normal_sup_eq_top hsup
  refine le_antisymm (Subgroup.commutator_le_left H K) ?_
  set q : G →* G ⧸ ⁅H, K⁆ := QuotientGroup.mk' ⁅H, K⁆ with hq
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  haveI hGsolv : IsSolvable (G ⧸ ⁅H, K⁆) := solvable_of_surjective hqsurj
  set Hbar : Subgroup (G ⧸ ⁅H, K⁆) := H.map q with hHbar
  set Kbar : Subgroup (G ⧸ ⁅H, K⁆) := K.map q with hKbar
  -- `⁅H̄,K̄⁆ = ⊥` (`⁅H,K⁆ = ker q`)
  have hcomm_bot : ⁅Hbar, Kbar⁆ = ⊥ := by
    rw [hHbar, hKbar, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hq,
      QuotientGroup.ker_mk']
  -- `Ḡ = H̄ ⊔ K̄`
  have hsupbar : Hbar ⊔ Kbar = ⊤ := by
    rw [hHbar, hKbar, ← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective q hqsurj]
  -- `K̄ ⊴ Ḡ` (正規化群 `⊇ H̄ ⊔ K̄ = ⊤`; `H̄` は中心化ゆえ正規化)
  haveI hKbarN : Kbar.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsupbar, sup_le_iff]
    refine ⟨le_trans ?_ (Subgroup.centralizer_le_normalizer _), Subgroup.le_normalizer⟩
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]; exact hcomm_bot
  -- `H̄ ⊓ K̄ = ⊥`
  have hdisjbar : Hbar ⊓ Kbar = ⊥ := by
    rw [eq_bot_iff]
    intro ybar hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨h, hhH, hhy⟩ := Subgroup.mem_map.mp (hHbar ▸ hy.1)
    obtain ⟨k, hkK, hky⟩ := Subgroup.mem_map.mp (hKbar ▸ hy.2)
    have hqeq : q h = q k := hhy.trans hky.symm
    have hmem : h * k⁻¹ ∈ (⁅H, K⁆ : Subgroup G) := by
      have h2 : q (h * k⁻¹) = 1 := by rw [map_mul, map_inv, hqeq, mul_inv_cancel]
      rwa [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have hkH : k ∈ H := by
      have hhk : h * k⁻¹ ∈ H := Subgroup.commutator_le_left H K hmem
      have hkinv : k⁻¹ ∈ H := by
        have := H.mul_mem (H.inv_mem hhH) hhk
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
      simpa using H.inv_mem hkinv
    have hk1 : k = 1 := by
      have : k ∈ (⊥ : Subgroup G) := hdisj.le_bot (Subgroup.mem_inf.mpr ⟨hkH, hkK⟩)
      simpa using this
    rw [Subgroup.mem_bot, ← hky, hk1, map_one]
  -- `H̄ ≤ commutator Ḡ`
  have hHbarle : Hbar ≤ commutator (G ⧸ ⁅H, K⁆) := by
    have hmap : (commutator G).map q = commutator (G ⧸ ⁅H, K⁆) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ hqsurj, ← commutator_def]
    calc Hbar = H.map q := hHbar
      _ ≤ (commutator G).map q := Subgroup.map_mono hH
      _ = commutator (G ⧸ ⁅H, K⁆) := hmap
  -- `commutator Ḡ ≤ K̄ ⊔ ⁅H̄,H̄⁆`
  have hcomm_le : commutator (G ⧸ ⁅H, K⁆) ≤ Kbar ⊔ ⁅Hbar, Hbar⁆ :=
    commutator_le_sup_commutator (by rw [sup_comm]; exact hsupbar)
  -- `H̄ ≤ ⁅H̄,H̄⁆`: 任意 `x ∈ H̄ ≤ K̄·⁅H̄,H̄⁆` を `x = k·c` (`k ∈ K̄`, `c ∈ ⁅H̄,H̄⁆ ≤ H̄`) と分解;
  -- `k = x·c⁻¹ ∈ H̄` ゆえ `k ∈ H̄ ⊓ K̄ = ⊥`, よって `x = c ∈ ⁅H̄,H̄⁆`。
  have hHbar_perfect : Hbar ≤ ⁅Hbar, Hbar⁆ := by
    intro x hx
    have hx2 : x ∈ Kbar ⊔ ⁅Hbar, Hbar⁆ := hcomm_le (hHbarle hx)
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hx2
    obtain ⟨k, hk, c, hc, hkc⟩ := hx2
    have hcH : c ∈ Hbar := Subgroup.commutator_le_left Hbar Hbar hc
    have hkH : k ∈ Hbar := by
      have hkeq : k = x * c⁻¹ := by rw [← hkc]; group
      rw [hkeq]; exact Hbar.mul_mem hx (Hbar.inv_mem hcH)
    have hk1 : k = 1 := by
      have hmem : k ∈ Hbar ⊓ Kbar := Subgroup.mem_inf.mpr ⟨hkH, hk⟩
      rw [hdisjbar] at hmem; simpa using hmem
    rw [← hkc, hk1]; simpa using hc
  -- 可解 ⟹ `H̄ = ⊥` ⟹ `H ≤ ⁅H,K⁆`
  have hHbar_bot : Hbar = ⊥ := by
    by_contra hne
    exact absurd (lt_of_le_of_lt hHbar_perfect (IsSolvable.commutator_lt_of_ne_bot hne))
      (lt_irrefl _)
  have hmap_bot : H.map q = ⊥ := hHbar ▸ hHbar_bot
  rwa [Subgroup.map_eq_bot_iff, hq, QuotientGroup.ker_mk'] at hmap_bot

open OddOrder.GroupTheory in
/-- **BG Lemma 6.3(a)** (second conclusion, mmd L1981): with the first conclusion's hypotheses
plus coprimality `(|H|, |K|) = 1`, the fixed points `C_H(K)` lie in `H' = derivedInG H`.

Proof (BG): pass to `Ḡ = G/H'`, where `H̄ = H/H'` is abelian and `K̄` acts on it coprimely by
conjugation. The action commutator is `⁅H̄, K̄⁆ = (⁅H,K⁆)‾ = H̄` (first conclusion), i.e. the
whole of `H̄`; Prop 1.6(d) (`fixedPoints_isComplement_actionCommutator_of_abelian`) then makes
the fixed points `C_Ḡ(K̄) ⊓ H̄` trivial. Any `x ∈ C_H(K)` maps into these fixed points, so
`x̄ = 1`, i.e. `x ∈ H'`. -/
theorem centralizer_inf_le_derivedInG_of_isComplement' [Finite G] [IsSolvable G]
    {H K : Subgroup G} [H.Normal] (hHK : H.IsComplement' K) (hH : H ≤ commutator G)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥K)) :
    Subgroup.centralizer (K : Set G) ⊓ H ≤ derivedInG H := by
  classical
  have hNeq : derivedInG H = ⁅H, H⁆ := Subgroup.map_subtype_commutator H
  rw [hNeq]
  set N : Subgroup G := ⁅H, H⁆ with hNdef
  haveI hNnorm : N.Normal := by rw [hNdef]; infer_instance
  set q : G →* G ⧸ N := QuotientGroup.mk' N with hq
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hkerq : (q : G →* G ⧸ N).ker = N := QuotientGroup.ker_mk' N
  set Hbar : Subgroup (G ⧸ N) := H.map q with hHbar
  set Kbar : Subgroup (G ⧸ N) := K.map q with hKbar
  haveI hHbarN : Hbar.Normal := by
    rw [hHbar]; exact (inferInstance : H.Normal).map q hqsurj
  -- `H̄` is abelian: `⁅H̄, H̄⁆ = (⁅H,H⁆)‾ = N‾ = ⊥`.
  have hHbar_comm : ⁅Hbar, Hbar⁆ = ⊥ := by
    rw [hHbar, ← Subgroup.map_commutator, ← hNdef, Subgroup.map_eq_bot_iff, hkerq]
  letI : CommGroup ↥Hbar :=
    { (inferInstance : Group ↥Hbar) with
      mul_comm := fun a b => Subtype.ext (by
        have hmem : ⁅(a : G ⧸ N), (b : G ⧸ N)⁆ = 1 := by
          have h := Subgroup.commutator_mem_commutator (G := G ⧸ N) a.2 b.2
          rwa [hHbar_comm, Subgroup.mem_bot] at h
        exact (commutatorElement_eq_one_iff_commute.mp hmem).eq) }
  -- `K̄ ≤ N_Ḡ(H̄) = ⊤`.
  have hKbarnorm : Kbar ≤ Subgroup.normalizer (Hbar : Set (G ⧸ N)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hHbarN]; exact le_top
  -- `actionCommutator = ⊤` because `⁅H̄, K̄⁆ = (⁅H,K⁆)‾ = H̄` (first conclusion).
  have hac : Ch04.actionCommutator
      ((Subgroup.normalizerMonoidHom Hbar).comp (Subgroup.inclusion hKbarnorm)) = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective Hbar)
    rw [actionCommutator_conj_map_subtype hKbarnorm,
      show Subgroup.map Hbar.subtype ⊤ = Hbar from by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype],
      hHbar, hKbar, ← Subgroup.map_commutator,
      commutator_eq_self_of_isComplement'_le_commutator hHK hH]
  -- Prop 1.6(d): fixed points complement `⊤`, hence are trivial.
  have hcop' : Nat.Coprime (Nat.card ↥Kbar) (Nat.card ↥Hbar) :=
    (hcop.symm.coprime_dvd_left (K.card_map_dvd q)).coprime_dvd_right (H.card_map_dvd q)
  have h16d := OddOrder.BG.Ch1.S01.fixedPoints_isComplement_actionCommutator_of_abelian
    (φ := (Subgroup.normalizerMonoidHom Hbar).comp (Subgroup.inclusion hKbarnorm)) hcop'
  rw [hac] at h16d
  have hfpbot : Subgroup.fixedPointsOfMulAut
      ((Subgroup.normalizerMonoidHom Hbar).comp (Subgroup.inclusion hKbarnorm)) = ⊥ :=
    Subgroup.isComplement'_top_right.mp h16d
  have hcentbot : Subgroup.centralizer (Kbar : Set (G ⧸ N)) ⊓ Hbar = ⊥ := by
    rw [← fixedPointsOfMulAut_conj_map_subtype hKbarnorm, hfpbot, Subgroup.map_bot]
  -- Transfer: `x ∈ C_H(K) ↦ x̄ ∈ C_Ḡ(K̄) ⊓ H̄ = ⊥`, so `x ∈ ker q = N = H'`.
  intro x hx
  obtain ⟨hxC, hxH⟩ := hx
  have hqx : q x ∈ Subgroup.centralizer (Kbar : Set (G ⧸ N)) ⊓ Hbar := by
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, Subgroup.mem_map_of_mem q hxH⟩
    intro gb hgb
    rw [SetLike.mem_coe, hKbar, Subgroup.mem_map] at hgb
    obtain ⟨k, hkK, rfl⟩ := hgb
    have hcomm : k * x = x * k := Subgroup.mem_centralizer_iff.mp hxC k hkK
    rw [← map_mul, ← map_mul, hcomm]
  rw [hcentbot, Subgroup.mem_bot] at hqx
  have hxker : x ∈ (q : G →* G ⧸ N).ker := by rw [MonoidHom.mem_ker]; exact hqx
  rwa [hkerq] at hxker

end /- 6.3 -/

/-! ## 6.5: 可解群の N/C 分解 (pp. 64-65, mmd L2048-2088)

**Lemma 6.5**: `K, U, H ≤ G` 可解, `K ⊴ G`, `G = KU`, `H ⊆ U`, `(|H|, |K|) = 1` のとき
(a) `H ∩ G' = H ∩ U'`, (b) `N_G(H) = C_K(H)·N_U(H)`, (c) `H^g ⊆ U ⇒ g = cu`
(`c ∈ C_K(H)`, `u ∈ U`)。§8 (`N_G(P)=LC_K(P)`), §10, §13, Thm 7.4(d) で多用。
原文どおり (b) は (c) から従い, (c) が本体 (Hall π-部分群の共役)。 -/

section /- 6.5 -/

open scoped Pointwise

variable [Finite G]

omit [Finite G] in
/-- 互いに素な位数の部分群は自明な交わりを持つ (`|H ⊓ K|` は `gcd(|H|, |K|) = 1` を割る)。 -/
private theorem inf_eq_bot_of_coprime_card {H K : Subgroup G}
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) : H ⊓ K = ⊥ := by
  have h1 : Nat.card ↥(H ⊓ K) ∣ Nat.card H := Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(H ⊓ K) ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_right
  have hone : Nat.card ↥(H ⊓ K) = 1 :=
    Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  exact Subgroup.card_eq_one.mp hone


omit [Finite G] in
/-- **BG Lemma 6.5(a)** (mmd L2054): `G` 可解, `K ⊴ G`, `G = KU`, `H ≤ U`,
`(|H|, |K|) = 1` のとき `H ∩ G' = H ∩ U'`。 -/
theorem inf_commutator_eq_of_coprime [IsSolvable G] {K U H : Subgroup G} [K.Normal]
    (hKU : K ⊔ U = ⊤) (hHU : H ≤ U)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    H ⊓ commutator G = H ⊓ ⁅U, U⁆ := by
  refine le_antisymm (le_inf inf_le_left ?_)
    (inf_le_inf_left H (Subgroup.commutator_mono le_top le_top))
  -- 残: `H ⊓ G' ≤ ⁅U,U⁆`。`d ∈ H ⊓ G'` を取り `d = k·b` (k ∈ U⊓K, b ∈ U') に分解,
  -- `U/U'` での像の位数が `|H|` と `|K|` の両方を割る ⟹ 1 ⟹ `d ∈ U'`。
  intro d hd
  rw [Subgroup.mem_inf] at hd
  obtain ⟨hdH, hdC⟩ := hd
  have hdU : d ∈ U := hHU hdH
  have hdKU : d ∈ K ⊔ ⁅U, U⁆ := commutator_le_sup_commutator hKU hdC
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hdKU
  obtain ⟨k, hkK, b, hbUU, hkb⟩ := hdKU
  have hbU : b ∈ U := Subgroup.commutator_le_self U hbUU
  have hkU : k ∈ U := by
    have hk_eq : k = d * b⁻¹ := by rw [← hkb]; group
    rw [hk_eq]; exact U.mul_mem hdU (U.inv_mem hbU)
  set φ := QuotientGroup.mk' (commutator ↥U) with hφ
  have hbcomm : (⟨b, hbU⟩ : ↥U) ∈ commutator ↥U := by
    rw [← Subgroup.map_subtype_commutator U] at hbUU
    obtain ⟨x, hx, hxb⟩ := hbUU
    have hxeq : x = ⟨b, hbU⟩ := Subtype.ext hxb
    rwa [hxeq] at hx
  have hφb : φ ⟨b, hbU⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hbcomm
  have hdkb : (⟨d, hdU⟩ : ↥U) = ⟨k, hkU⟩ * ⟨b, hbU⟩ := Subtype.ext hkb.symm
  have hφd : φ ⟨d, hdU⟩ = φ ⟨k, hkU⟩ := by rw [hdkb, map_mul, hφb, mul_one]
  have hord_d : orderOf (φ ⟨d, hdU⟩) ∣ Nat.card H := by
    refine (orderOf_map_dvd φ _).trans ?_
    rw [Subgroup.orderOf_mk]
    exact H.orderOf_dvd_natCard hdH
  have hord_k : orderOf (φ ⟨d, hdU⟩) ∣ Nat.card K := by
    rw [hφd]
    refine (orderOf_map_dvd φ _).trans ?_
    rw [Subgroup.orderOf_mk]
    exact K.orderOf_dvd_natCard hkK
  have hone : orderOf (φ ⟨d, hdU⟩) = 1 :=
    Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hord_d hord_k)
  have hdcomm : (⟨d, hdU⟩ : ↥U) ∈ commutator ↥U :=
    (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hone)
  rw [← Subgroup.map_subtype_commutator U]
  exact ⟨⟨d, hdU⟩, hdcomm, rfl⟩

/-- **Hall π-部分群の `↥V` 内共役** (BG Lem 6.5(c)/Thm 7.4(d) 共有 engine): `V` 可解で
`H₁, H₂ ≤ V` がともに `↥V` の `π`-Hall 部分群 (`subgroupOf` 形) なら、ある `w ∈ V` で
`w H₁ w⁻¹ = H₂` (pointwise 共役)。Isaacs Thm 3.21 (`Ch03.hall_C`, 可解群の π-Hall 共役性) を
`↥V → G` の `subtype` 像で `G` レベルへ持ち上げたもの。§7 Thm 7.4(d) と §6 Lem 6.5(c) の両方で使用。 -/
theorem exists_conj_eq_of_isHall_subgroupOf {V : Subgroup G}
    (hVsolv : IsSolvable ↥V) {π : Set ℕ} {H₁ H₂ : Subgroup G} (hH₁V : H₁ ≤ V) (hH₂V : H₂ ≤ V)
    (hH₁ : Ch03.IsHallSubgroup π (H₁.subgroupOf V))
    (hH₂ : Ch03.IsHallSubgroup π (H₂.subgroupOf V)) :
    ∃ w ∈ V, MulAut.conj w • H₁ = H₂ := by
  haveI := hVsolv
  obtain ⟨w, hw⟩ := Ch03.hall_C hH₁ hH₂
  refine ⟨(w : G), w.2, ?_⟩
  have hcomp : V.subtype.comp (MulAut.conj w).toMonoidHom
      = (MulAut.conj (w : G)).toMonoidHom.comp V.subtype := by
    ext x
    simp [MulAut.conj_apply]
  have h := congrArg (Subgroup.map V.subtype) hw
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hH₁V, Subgroup.map_subgroupOf_eq_of_le hH₂V] at h
  rw [Subgroup.pointwise_smul_def]
  exact h

omit [Finite G] in
/-- **(infra)** `x ∈ H.comap (MulAut.conj a) ↔ a*x*a⁻¹ ∈ H`. -/
private theorem mem_comap_conj {a x : G} {H : Subgroup G} :
    x ∈ H.comap (MulAut.conj a).toMonoidHom ↔ a * x * a⁻¹ ∈ H := by
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

omit [Finite G] in
/-- **(infra)** pointwise 共役 `MulAut.conj w • H` を comap 形 `H.comap (MulAut.conj w⁻¹)`
へ変換する橋。`exists_conj_eq_of_isHall_subgroupOf` の出力 (`smul`) を `comap` 計算へ載せる。 -/
private theorem conj_smul_eq_comap_conj_inv (w : G) (H : Subgroup G) :
    MulAut.conj w • H = H.comap (MulAut.conj w⁻¹).toMonoidHom := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
    mem_comap_conj]
  simp only [inv_inv]

omit [Finite G] in
/-- **(infra)** `H.comap (MulAut.conj (a*b)) = (H.comap (MulAut.conj a)).comap (MulAut.conj b)`. -/
private theorem comap_conj_mul (a b : G) (H : Subgroup G) :
    H.comap (MulAut.conj (a * b)).toMonoidHom
      = (H.comap (MulAut.conj a).toMonoidHom).comap (MulAut.conj b).toMonoidHom := by
  rw [Subgroup.comap_comap]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
/-- **(infra)** 共役同型による `comap` は位数を保つ: `|H.comap (conj k)| = |H|`. -/
private theorem card_comap_conj (k : G) (H : Subgroup G) :
    Nat.card (H.comap (MulAut.conj k).toMonoidHom) = Nat.card H := by
  rw [Subgroup.comap_equiv_eq_map_symm' (MulAut.conj k) H]
  exact Subgroup.card_map_of_injective (f := (MulAut.conj k).symm.toMonoidHom)
    (MulAut.conj k).symm.injective

omit [Finite G] in
/-- **(infra)** `a ∈ H` なら `H.comap (MulAut.conj a) = H` (`H` 内元による共役は `H` を保つ). -/
private theorem comap_conj_self_of_mem {a : G} {H : Subgroup G} (ha : a ∈ H) :
    H.comap (MulAut.conj a).toMonoidHom = H := by
  have h := Subgroup.conj_smul_eq_self_of_mem (H := H) (h := a⁻¹) (H.inv_mem ha)
  rw [conj_smul_eq_comap_conj_inv, inv_inv] at h
  exact h

omit [Finite G] in
/-- **(infra)** `K ⊴ G`, `H ⊓ K = ⊥` のとき `|H ⊔ K| = |H| · |K|` (第二同型). -/
private theorem card_sup_eq_of_inf_bot {H K : Subgroup G} [K.Normal]
    (hHKbot : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  -- Lagrange for `K.subgroupOf (H⊔K)` inside `↥(H⊔K)`.
  have hlag := Subgroup.card_mul_index (K.subgroupOf (H ⊔ K))
  -- `|K.subgroupOf (H⊔K)| = |K|`.
  have hcardK : Nat.card (K.subgroupOf (H ⊔ K)) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv
  -- `(K.subgroupOf (H⊔K)).index = K.relIndex (H⊔K) = K.relIndex H`.
  have hidx : (K.subgroupOf (H ⊔ K)).index = Nat.card H := by
    have h1 : (K.subgroupOf (H ⊔ K)).index = K.relIndex (H ⊔ K) := rfl
    rw [h1, Subgroup.relIndex_sup_right]
    -- `K.relIndex H = (K.subgroupOf H).index`, and `K.subgroupOf H = ⊥`.
    have hbot : K.subgroupOf H = ⊥ :=
      Subgroup.subgroupOf_eq_bot.mpr (by rw [disjoint_iff, inf_comm]; exact hHKbot)
    change (K.subgroupOf H).index = Nat.card H
    rw [hbot, Subgroup.index_bot]
  rw [hcardK, hidx] at hlag
  -- `hlag : |K| * |H| = |H⊔K|`
  rw [← hlag, mul_comm]

/-- **(infra)** `W ≤ V := (H⊔K)⊓U` で `|W| = |H|` なら, `W.subgroupOf V` は
`π := primeFactors|H|`-Hall (内側 `↥V`)。両端 `H` と `g⁻¹Hg` をこの一本で処理する。 -/
private theorem isHall_subgroupOf_of_card_eq {K U H W : Subgroup G} [K.Normal]
    (hHKbot : H ⊓ K = ⊥) (hcop : Nat.Coprime (Nat.card H) (Nat.card K))
    (hWV : W ≤ (H ⊔ K) ⊓ U) (hWcard : Nat.card W = Nat.card H) :
    Ch03.IsHallSubgroup {p | p ∈ (Nat.card H).primeFactors}
      (W.subgroupOf ((H ⊔ K) ⊓ U)) := by
  set V : Subgroup G := (H ⊔ K) ⊓ U with hV
  have hWHK : W ≤ H ⊔ K := hWV.trans inf_le_left
  have hVHK : V ≤ H ⊔ K := inf_le_left
  -- `|W.subgroupOf V| = |W| = |H|`.
  have hcardWV : Nat.card (W.subgroupOf V) = Nat.card H := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWV).toEquiv, hWcard]
  -- `W.relIndex (H⊔K) = |K|`.
  have hWrelHK : W.relIndex (H ⊔ K) = Nat.card K := by
    have hlag := Subgroup.card_mul_index (W.subgroupOf (H ⊔ K))
    have hc : Nat.card (W.subgroupOf (H ⊔ K)) = Nat.card H := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWHK).toEquiv, hWcard]
    have hidx : (W.subgroupOf (H ⊔ K)).index = W.relIndex (H ⊔ K) := rfl
    rw [hc, hidx, card_sup_eq_of_inf_bot hHKbot] at hlag
    -- `hlag : |H| * W.relIndex (H⊔K) = |H| * |K|`
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hlag
  -- `W.relIndex V ∣ W.relIndex (H⊔K) = |K|`.
  have hdvd : W.relIndex V ∣ Nat.card K := by
    have hmul := Subgroup.relIndex_mul_relIndex W V (H ⊔ K) hWV hVHK
    rw [hWrelHK] at hmul
    exact ⟨V.relIndex (H ⊔ K), hmul.symm⟩
  refine ⟨?_, ?_⟩
  · -- cond1: primeFactors of |W.subgroupOf V| ⊆ π
    intro p hp
    rw [hcardWV] at hp
    exact hp
  · -- cond2: primeFactors of index ∉ π
    intro p hp hpπ
    have hidxV : (W.subgroupOf V).index = W.relIndex V := rfl
    rw [hidxV, Nat.mem_primeFactors] at hp
    -- `p ∣ |K|`
    have hpK : p ∣ Nat.card K := hp.2.1.trans hdvd
    -- `p ∣ |H|` from `p ∈ π`
    simp only [Set.mem_setOf_eq, Nat.mem_primeFactors] at hpπ
    have hpH : p ∣ Nat.card H := hpπ.2.1
    -- contradiction with coprimality
    have : p ∣ Nat.gcd (Nat.card H) (Nat.card K) := Nat.dvd_gcd hpH hpK
    rw [hcop.gcd_eq_one] at this
    exact hp.1.one_lt.ne' (Nat.dvd_one.mp this)

/-- **BG Lemma 6.5(c)** (mmd L2056): 上記仮定で, `g ∈ G` が `H^g = g⁻¹Hg ≤ U` を満たすなら
`g = c·u` (`c ∈ C_K(H)`, `u ∈ U`) と分解できる。`H^g` は BG 規約 `g⁻¹Hg`
(= `H.comap (MulAut.conj g)`)。 -/
theorem exists_mem_centralizerK_mul_of_conj_le [IsSolvable G] {K U H : Subgroup G} [K.Normal]
    (hKU : K ⊔ U = ⊤) (hHU : H ≤ U)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K))
    {g : G} (hg : H.comap (MulAut.conj g).toMonoidHom ≤ U) :
    ∃ c ∈ Subgroup.centralizer (H : Set G) ⊓ K, ∃ u ∈ U, g = c * u := by
  classical
  -- `H ⊓ K = ⊥` from coprimality.
  have hHKbot : H ⊓ K = ⊥ := inf_eq_bot_of_coprime_card hcop
  -- Step 1: decompose `g = k * v`, `k ∈ K`, `v ∈ U`.
  have hgmem : g ∈ K ⊔ U := by rw [hKU]; exact Subgroup.mem_top g
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hgmem
  obtain ⟨k, hkK, v, hvU, hkv0⟩ := hgmem
  have hkv : k * v = g := hkv0
  -- abbreviation `Hk = k⁻¹Hk` (BG convention `comap (conj k)`)
  let Hk : Subgroup G := H.comap (MulAut.conj k).toMonoidHom
  have hHk : Hk = H.comap (MulAut.conj k).toMonoidHom := rfl
  -- Step 2: `Hk ≤ U`.  From `hg` with `g = k*v`: `Hk.comap (conj v) ≤ U`, then de-conjugate.
  have hgkv : H.comap (MulAut.conj g).toMonoidHom
      = Hk.comap (MulAut.conj v).toMonoidHom := by
    rw [hHk, ← comap_conj_mul, hkv]
  have hg' : Hk.comap (MulAut.conj v).toMonoidHom ≤ U := hgkv ▸ hg
  have hkU : Hk ≤ U := by
    intro z hz
    have hx : MulAut.conj v (v⁻¹ * z * v) ∈ Hk := by
      rw [MulAut.conj_apply]
      have heq : v * (v⁻¹ * z * v) * v⁻¹ = z := by group
      rwa [heq]
    have hzU' : v⁻¹ * z * v ∈ U := hg' (mem_comap_conj.mpr hx)
    have heq : z = v * (v⁻¹ * z * v) * v⁻¹ := by group
    rw [heq]; exact U.mul_mem (U.mul_mem hvU hzU') (U.inv_mem hvU)
  -- Step 3: `Hk ≤ H ⊔ K`. Each element of `Hk` is `k⁻¹ h k` with `h ∈ H ≤ H⊔K`, `k ∈ K ≤ H⊔K`.
  have hkHK : Hk ≤ H ⊔ K := by
    intro z hz
    rw [hHk, mem_comap_conj] at hz
    -- `k*z*k⁻¹ ∈ H`, so `z = k⁻¹*(k*z*k⁻¹)*k ∈ H⊔K`.
    have hzeq : z = k⁻¹ * (k * z * k⁻¹) * k := by group
    rw [hzeq]
    exact (H ⊔ K).mul_mem ((H ⊔ K).mul_mem
      ((H ⊔ K).inv_mem (Subgroup.mem_sup_right hkK)) (Subgroup.mem_sup_left hz))
      (Subgroup.mem_sup_right hkK)
  -- `H ≤ H ⊔ K`
  have hHHK : H ≤ H ⊔ K := le_sup_left
  -- Set `V := (H⊔K) ⊓ U`, and verify `H, Hk ≤ V`.
  set V : Subgroup G := (H ⊔ K) ⊓ U with hV
  have hHV : H ≤ V := le_inf hHHK hHU
  have hHkV : Hk ≤ V := le_inf hkHK hkU
  -- `|Hk| = |H|`
  have hcardHk : Nat.card Hk = Nat.card H := card_comap_conj k H
  -- Both `H` and `Hk` are π-Hall of `V`.
  have hHallH : Ch03.IsHallSubgroup {p | p ∈ (Nat.card H).primeFactors} (H.subgroupOf V) :=
    isHall_subgroupOf_of_card_eq hHKbot hcop hHV rfl
  have hHallHk : Ch03.IsHallSubgroup {p | p ∈ (Nat.card H).primeFactors} (Hk.subgroupOf V) :=
    isHall_subgroupOf_of_card_eq hHKbot hcop hHkV hcardHk
  -- Step 6: apply the conjugacy engine inside the solvable subgroup `↥V`.
  obtain ⟨w₀, hw₀V, hconj⟩ :=
    exists_conj_eq_of_isHall_subgroupOf (inferInstance : IsSolvable ↥V) hHV hHkV hHallH hHallHk
  -- `hconj : MulAut.conj w₀ • H = Hk`, i.e. in comap form `H.comap (conj w₀⁻¹) = Hk`.
  rw [conj_smul_eq_comap_conj_inv] at hconj
  -- so with `w := w₀⁻¹ ∈ V`: `H.comap (conj w) = Hk`.
  set w : G := w₀⁻¹ with hw
  have hwV : w ∈ V := V.inv_mem hw₀V
  have hconjw : H.comap (MulAut.conj w).toMonoidHom = Hk := hconj
  -- Step 8: reduce `w` to `K ⊓ U`. `↑V = ↑H * ↑(K ⊓ U)` (Dedekind), so `w = h₀ * c₀`.
  have hwmem : w ∈ (H : Set G) * (K ⊓ U : Subgroup G) := by
    have hVcoe : (V : Set G) = (H : Set G) * (K ⊓ U : Subgroup G) := by
      rw [Subgroup.mul_inf_assoc H K U hHU, ← Subgroup.mul_normal H K, hV, Subgroup.coe_inf]
    rw [← hVcoe]; exact hwV
  rw [Set.mem_mul] at hwmem
  obtain ⟨h₀, hh₀H, c₀, hc₀, hw_eq⟩ := hwmem
  rw [SetLike.mem_coe] at hh₀H hc₀
  -- `H.comap (conj c₀) = H.comap (conj w) = Hk` because `h₀ ∈ H` ⟹ `comap (conj h₀) H = H`.
  have hc₀conj : H.comap (MulAut.conj c₀).toMonoidHom = Hk := by
    rw [← hconjw, ← hw_eq, comap_conj_mul, comap_conj_self_of_mem hh₀H]
  -- `c₀ ∈ K` and `c₀ ∈ U`.
  have hc₀K : c₀ ∈ K := (Subgroup.mem_inf.mp hc₀).1
  have hc₀U : c₀ ∈ U := (Subgroup.mem_inf.mp hc₀).2
  -- Step 9: build `c := k * c₀⁻¹` and `u := c₀ * v`.
  refine ⟨k * c₀⁻¹, ?_, c₀ * v, U.mul_mem hc₀U hvU, ?_⟩
  · -- `c = k * c₀⁻¹ ∈ centralizer (H) ⊓ K`.
    rw [Subgroup.mem_inf]
    refine ⟨?_, K.mul_mem hkK (K.inv_mem hc₀K)⟩
    -- First: `c` normalizes `H`, i.e. `H.comap (conj c) = H`.
    -- `H.comap (conj k) = H.comap (conj c₀)` (= Hk), so conjugating back by `c₀⁻¹` fixes `H`.
    have hcNorm : H.comap (MulAut.conj (k * c₀⁻¹)).toMonoidHom = H := by
      have hkc₀ : H.comap (MulAut.conj k).toMonoidHom = H.comap (MulAut.conj c₀).toMonoidHom :=
        (hc₀conj.trans hHk).symm
      rw [comap_conj_mul, hkc₀, ← comap_conj_mul]
      -- now `H.comap (conj (c₀ * c₀⁻¹)) = H`
      have h1 : c₀ * c₀⁻¹ = (1 : G) := mul_inv_cancel c₀
      rw [h1]
      ext x; rw [mem_comap_conj]; simp
    -- `c⁻¹ H c = H` as well (apply `hcNorm` with `c⁻¹`).
    have hcNormInv : H.comap (MulAut.conj (k * c₀⁻¹)⁻¹).toMonoidHom = H := by
      have h2 := comap_conj_mul (k * c₀⁻¹) (k * c₀⁻¹)⁻¹ H
      rw [mul_inv_cancel, hcNorm] at h2
      -- `h2 : H.comap (conj 1) = H.comap (conj (k*c₀⁻¹)⁻¹)`
      have h3 : H.comap (MulAut.conj (1 : G)).toMonoidHom = H := by
        ext x; rw [mem_comap_conj]; simp
      rw [h3] at h2; exact h2.symm
    -- Now show centralizer membership.
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    -- `d := c⁻¹ * h * c * h⁻¹ ∈ H ⊓ K = ⊥`.
    set c : G := k * c₀⁻¹ with hc
    -- `c⁻¹ * h * c ∈ H` from `hcNormInv`.
    have hconjH : c⁻¹ * h * c ∈ H := by
      have : h ∈ H.comap (MulAut.conj c⁻¹).toMonoidHom := by rw [hcNormInv]; exact hh
      rw [mem_comap_conj] at this
      -- `this : c⁻¹ * h * (c⁻¹)⁻¹ ∈ H`
      rwa [inv_inv] at this
    have hdH : c⁻¹ * h * c * h⁻¹ ∈ H := H.mul_mem hconjH (H.inv_mem hh)
    -- `d ∈ K`: `c ∈ K`, `K` normal ⟹ `h * c * h⁻¹ ∈ K`, so `c⁻¹ * (h*c*h⁻¹) ∈ K`.
    have hcK : c ∈ K := K.mul_mem hkK (K.inv_mem hc₀K)
    have hdK : c⁻¹ * h * c * h⁻¹ ∈ K := by
      have hconjK : h * c * h⁻¹ ∈ K := by
        have := (‹K.Normal›.conj_mem c hcK h)
        simpa [mul_assoc] using this
      have heq : c⁻¹ * h * c * h⁻¹ = c⁻¹ * (h * c * h⁻¹) := by group
      rw [heq]; exact K.mul_mem (K.inv_mem hcK) hconjK
    -- `d = 1`.
    have hd1 : c⁻¹ * h * c * h⁻¹ = 1 := by
      have : c⁻¹ * h * c * h⁻¹ ∈ H ⊓ K := Subgroup.mem_inf.mpr ⟨hdH, hdK⟩
      rw [hHKbot, Subgroup.mem_bot] at this
      exact this
    -- conclude `h * c = c * h`.
    have : c⁻¹ * h * c = h := by
      have := mul_eq_one_iff_eq_inv.mp hd1
      -- `this : c⁻¹ * h * c = (h⁻¹)⁻¹ = h`
      rwa [inv_inv] at this
    -- so `h * c = c * h`
    have hgoal : h * c = c * h := by
      have h4 : c * (c⁻¹ * h * c) = c * h := by rw [this]
      calc h * c = c * (c⁻¹ * h * c) := by group
        _ = c * h := by rw [this]
    exact hgoal
  · -- `g = c * u`: `(k * c₀⁻¹) * (c₀ * v) = k * v = g`.
    rw [← hkv]; group

omit [Finite G] in
/-- 集合 `H` の中心化群は `H` (部分群) の正規化群に含まれる (`c` が各 `h∈H` と可換 ⟹
`c·h·c⁻¹ = h ∈ H`)。 -/
private theorem centralizer_set_le_normalizer (H : Subgroup G) :
    Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer H := by
  intro c hc
  have hcomm : ∀ h ∈ H, h * c = c * h := fun h hh =>
    Subgroup.mem_centralizer_iff.mp hc h hh
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have he : c * h * c⁻¹ = h := by rw [← hcomm h hh]; group
    rw [he]; exact hh
  · intro hh
    have he : h = c * h * c⁻¹ := by
      have h2 : c * h = c * (c * h * c⁻¹) := by rw [← hcomm _ hh]; group
      exact mul_left_cancel h2
    rw [he]; exact hh

/-- **BG Lemma 6.5(b)** (mmd L2055): 上記仮定で `N_G(H) = C_K(H)·N_U(H)` (集合等式)。
原文どおり (c) から従う: `n ∈ N_G(H)` は `n⁻¹Hn = H ≤ U` で (c) を満たし `n = cu`,
`u = c⁻¹n ∈ N_G(H) ⊓ U = N_U(H)`。逆は両因子が `N_G(H)` 内ゆえ自明。 -/
theorem normalizer_eq_centralizerK_mul_normalizerU [IsSolvable G] {K U H : Subgroup G}
    [K.Normal] (hKU : K ⊔ U = ⊤) (hHU : H ≤ U)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    SetLike.coe (Subgroup.normalizer H)
      = SetLike.coe (Subgroup.centralizer (H : Set G) ⊓ K)
        * SetLike.coe (Subgroup.normalizer H ⊓ U) := by
  apply Set.Subset.antisymm
  · intro n hn
    rw [SetLike.mem_coe] at hn
    have hcn : H.comap (MulAut.conj n).toMonoidHom ≤ U := by
      intro x hx
      rw [Subgroup.mem_comap] at hx
      exact hHU (((Subgroup.mem_normalizer_iff.mp hn) x).mpr hx)
    obtain ⟨c, hc, u, hu, hnu⟩ := exists_mem_centralizerK_mul_of_conj_le hKU hHU hcop hcn
    have hcN : c ∈ Subgroup.normalizer H := centralizer_set_le_normalizer H (Subgroup.mem_inf.mp
        hc).1
    have huN : u ∈ Subgroup.normalizer H := by
      have hue : u = c⁻¹ * n := by rw [hnu]; group
      rw [hue]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcN) hn
    rw [Set.mem_mul]
    exact ⟨c, SetLike.mem_coe.mpr hc, u,
      SetLike.mem_coe.mpr (Subgroup.mem_inf.mpr ⟨huN, hu⟩), hnu.symm⟩
  · rintro x hx
    rw [Set.mem_mul] at hx
    obtain ⟨c, hc, u, hu, rfl⟩ := hx
    rw [SetLike.mem_coe] at hc hu ⊢
    exact Subgroup.mul_mem _ (centralizer_set_le_normalizer H (Subgroup.mem_inf.mp hc).1)
      (Subgroup.mem_inf.mp hu).1

end

/-! ## 6.6: p-length 1 characterization (pp. 65-66, mmd L2089-2128)

**Lemma 6.6** (BG p.65): `G` 可解で `p`-length 1, `S ∈ Syl_p(G)`. 書く `M = O_{p'}(G)`,
`N = O_{p',p}(G)`。`p`-length 1 ⟺ `G/N` が `p'`-群。このとき:

- **(foundation)** `N = M · S` (= `O_{p'}(G) ⊔ S`): `S` の `G/M` への像は `G/M` の `p`-Hall
  (= `O_p(G/M)` を含む正規 `p`-群と一致) ゆえ `O_p(G/M) ≤ SM/M`, 引き戻して `N ≤ MS`;
  逆は `M ≤ N` (下層) と `S ≤ N` (`G/N` が `p'` ⟹ `S` の `G/N` 像は自明)。
- **(1b)** `G = O_{p'}(G) · N_G(S)` (Frattini, `N` の中の Sylow `S` に適用 + `N = MS`)。
- **(2)** `S ≤ G' ⟹ S ≤ N_G(S)'` (Lem 6.5(a), `K = M`, `U = N_G(S)`)。
- **(3)** `Y ⊆ S`, `Y^x ⊆ S` ⟹ `x = c·g` (`c ∈ C_G(Y)`, `g ∈ N_G(S)`) (Lem 6.5(c))。
- **(4)** `Q` `p`-部分群 ⟹ `∃ x ∈ C_G(Q ⊓ S)`, `Q^x ⊆ S` (`Q ≤ N`, `N` 内 Sylow 共役)。

§8 (`N_G(P) = L·C_K(P)`), §10, §13 で `p`-length 1 の局所構造として多用。 -/

section /- 6.6 -/

open scoped Pointwise

open OddOrder.BG.Ch1 (hasPLengthOne)

variable [Finite G] [IsSolvable G] {p : ℕ} [Fact p.Prime]

omit [IsSolvable G] in
/-- `M := O_{p'}(G)` は `p'`-群: `|M|` は `p` と互いに素 (`oPiCore.isPiGroup` で
全素因子が `≠ p`)。`inf_eq_bot_of_pGroup_coprime` 等への入力。 -/
private theorem card_oPiPrimeCore_coprime_prime :
    (Nat.card (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G)).Coprime p := by
  have hpi : Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)}
      (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G) := Ch03.oPiCore.isPiGroup _
  have hndvd : ¬ p ∣ Nat.card (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G) := by
    intro hdvd
    have hmem : p ∈ (Nat.card (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩
    exact (hpi p hmem) rfl
  exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hndvd))

omit [IsSolvable G] in
/-- `S ∈ Syl_p` と `M = O_{p'}(G)` の位数は互いに素 (`p`-群 vs `p'`-群)。 -/
private theorem sylow_card_coprime_oPiPrimeCore (S : Sylow p G) :
    Nat.Coprime (Nat.card (S : Subgroup G))
      (Nat.card (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G)) := by
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  rw [hn]
  exact (card_oPiPrimeCore_coprime_prime (p := p) (G := G)).symm.pow_left n

omit [IsSolvable G] in
/-- `S ∈ Syl_p` と `M = O_{p'}(G)` は交わらない (`S` は `p`-群, `M` は `p'`-群)。 -/
private theorem sylow_inf_oPiPrimeCore_eq_bot (S : Sylow p G) :
    (S : Subgroup G) ⊓ Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥ :=
  inf_eq_bot_of_coprime_card (sylow_card_coprime_oPiPrimeCore S)

omit [Finite G] [IsSolvable G] in
/-- 商写像 `mk' M` による像の位数は不変, ただし `T ⊓ M = ⊥` のとき: `|T.map (mk' M)| = |T|`。
`relIndex_ker` (`ker (mk' M) = M`) で `|T.map q| = M.relIndex T = (M.subgroupOf T).index`,
`T ⊓ M = ⊥ ⟹ M.subgroupOf T = ⊥` ゆえ index = `|T|`。 -/
private theorem card_map_mk'_eq_of_inf_bot {M T : Subgroup G} [M.Normal]
    (hbot : T ⊓ M = ⊥) :
    Nat.card (T.map (QuotientGroup.mk' M)) = Nat.card T := by
  have hker : (QuotientGroup.mk' M).ker = M := QuotientGroup.ker_mk' M
  have h1 : Nat.card (T.map (QuotientGroup.mk' M)) = M.relIndex T := by
    rw [← Subgroup.relIndex_ker, hker]
  have hbot' : M.subgroupOf T = ⊥ :=
    Subgroup.subgroupOf_eq_bot.mpr (by rw [disjoint_iff, inf_comm]; exact hbot)
  rw [h1]
  change (M.subgroupOf T).index = Nat.card T
  rw [hbot', Subgroup.index_bot]

omit [IsSolvable G] in
/-- `p`-length 1 のもとで, 任意の `p`-部分群は `N = O_{p',p}(G)` に含まれる。
`Q` の `G/N` への像は `p`-群かつ `|G/N|` (= `p` と互いに素, by `hpl1`) を割るので自明 ⟹
`Q ≤ ker (mk' N) = N`。`S ≤ N` (foundation/Frattini) と `Q ≤ N` (Lem 6.6(4)) で共有。 -/
private theorem pGroup_le_oPiPrimePiCore {Q : Subgroup G} (hQ : IsPGroup p Q)
    (hpl1 : hasPLengthOne p G) :
    Q ≤ Ch03.oPiPrimePiCore {p} G := by
  set N : Subgroup G := Ch03.oPiPrimePiCore {p} G with hN
  set q : G →* G ⧸ N := QuotientGroup.mk' N with hq
  -- `Q.map q` is a `p`-group whose card divides `|G/N|`, which is coprime to `p`.
  have hpg : IsPGroup p (Q.map q) := hQ.map q
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hdvd : Nat.card (Q.map q) ∣ Nat.card (G ⧸ N) :=
    Subgroup.card_subgroup_dvd_card (Q.map q)
  have hcop : Nat.Coprime (Nat.card (Q.map q)) (Nat.card (G ⧸ N)) := by
    rw [hn]
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpl1).pow_left n
  have hcard1 : Nat.card (Q.map q) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
  have hmapbot : Q.map q = ⊥ := Subgroup.card_eq_one.mp hcard1
  have hle : Q ≤ q.ker := (Subgroup.map_eq_bot_iff Q).mp hmapbot
  rwa [hq, QuotientGroup.ker_mk'] at hle

omit [IsSolvable G] in
/-- **BG Lemma 6.6 (foundation)**: `p`-length 1 のもとで `O_{p',p}(G) = O_{p'}(G) · S`
(= `O_{p'}(G) ⊔ S`)。

`⊇`: `O_{p'}(G) ≤ N` (下層), `S ≤ N` (`pGroup_le_oPiPrimePiCore`)。
`⊆`: `S` の `G/M` への像 (`M = O_{p'}(G)`) は `p`-Hall (= `p`-群 + index が `p` と互いに素;
後者は `|S| = |S.map q|` (∵ `S ⊓ M = ⊥`) が `|G|` の `p`-part, `p ∤ S.index`)。ゆえ
`O_p(G/M) ≤ S.map q` (`normal_le_hall`), 引き戻して `N = (O_p(G/M)).comap q ≤ S ⊔ M`. -/
theorem oPiPrimePiCore_eq_oPiPrimeCore_sup_sylow (S : Sylow p G)
    (hpl1 : OddOrder.BG.Ch1.hasPLengthOne p G) :
    Ch03.oPiPrimePiCore {p} G
      = Ch03.oPiCore {q | q ∉ ({p}:Set ℕ)} G ⊔ (S : Subgroup G) := by
  set M : Subgroup G := Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G with hM
  set N : Subgroup G := Ch03.oPiPrimePiCore {p} G with hN
  set q : G →* G ⧸ M := QuotientGroup.mk' M with hq
  have hqker : q.ker = M := by rw [hq, QuotientGroup.ker_mk']
  -- `S ⊓ M = ⊥`
  have hSMbot : (S : Subgroup G) ⊓ M = ⊥ := sylow_inf_oPiPrimeCore_eq_bot S
  -- `S ≤ N` (from `p`-length 1)
  have hSN : (S : Subgroup G) ≤ N := pGroup_le_oPiPrimePiCore S.isPGroup' hpl1
  refine le_antisymm ?_ ?_
  · -- ⊆ direction: `N ≤ M ⊔ S`
    -- `S.map q` is a `p`-Hall subgroup of `G/M`.
    have hpg : IsPGroup p ((S : Subgroup G).map q) := S.isPGroup'.map q
    -- card of `S.map q` equals card S.
    have hcardSmap : Nat.card ((S : Subgroup G).map q) = Nat.card (S : Subgroup G) :=
      card_map_mk'_eq_of_inf_bot hSMbot
    -- cond1: prime factors ⊆ {p}
    have hcond1 : ∀ r ∈ (Nat.card ((S : Subgroup G).map q)).primeFactors, r ∈ ({p} : Set ℕ) := by
      intro r hr
      obtain ⟨n, hn⟩ := hpg.exists_card_eq
      rw [hn, Nat.mem_primeFactors] at hr
      have hrp : r = p :=
        (Nat.prime_dvd_prime_iff_eq hr.1 Fact.out).mp (hr.1.dvd_of_dvd_pow hr.2.1)
      rw [hrp]; exact Set.mem_singleton p
    -- cond2: `p ∤ (S.map q).index`
    have hidx_dvd : ((S : Subgroup G).map q).index ∣ (S : Subgroup G).index := by
      -- `card(S.map q) * (S.map q).index = card(G/M)`,  `card(G/M) * card M = card G`,
      -- `card S * S.index = card G`,  `card(S.map q) = card S`.
      have hA : Nat.card ((S : Subgroup G).map q) * ((S : Subgroup G).map q).index
          = Nat.card (G ⧸ M) := Subgroup.card_mul_index _
      have hB : Nat.card (G ⧸ M) * Nat.card M = Nat.card G := by
        have h := M.card_mul_index
        rw [Subgroup.index_eq_card, mul_comm] at h
        exact h
      have hC : Nat.card (S : Subgroup G) * (S : Subgroup G).index = Nat.card G :=
        Subgroup.card_mul_index _
      -- combine: `card S * ((S.map q).index * card M) = card S * S.index`
      refine ⟨Nat.card M, ?_⟩
      have hkey : Nat.card (S : Subgroup G) * (((S : Subgroup G).map q).index * Nat.card M)
          = Nat.card (S : Subgroup G) * (S : Subgroup G).index := by
        have step1 : Nat.card (S : Subgroup G) * ((S : Subgroup G).map q).index
            = Nat.card (G ⧸ M) := by rw [← hcardSmap]; exact hA
        calc Nat.card (S : Subgroup G) * (((S : Subgroup G).map q).index * Nat.card M)
            = (Nat.card (S : Subgroup G) * ((S : Subgroup G).map q).index) * Nat.card M := by
              rw [mul_assoc]
          _ = Nat.card (G ⧸ M) * Nat.card M := by rw [step1]
          _ = Nat.card G := hB
          _ = Nat.card (S : Subgroup G) * (S : Subgroup G).index := hC.symm
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hkey.symm
    have hcond2 : ∀ r ∈ ((S : Subgroup G).map q).index.primeFactors, r ∉ ({p} : Set ℕ) := by
      intro r hr hrp
      rw [Set.mem_singleton_iff] at hrp
      rw [Nat.mem_primeFactors] at hr
      have hpidxS : p ∣ (S : Subgroup G).index := (hrp ▸ hr.2.1).trans hidx_dvd
      exact S.not_dvd_index hpidxS
    have hHall : Ch03.IsHallSubgroup ({p} : Set ℕ) ((S : Subgroup G).map q) := ⟨hcond1, hcond2⟩
    -- `O_p(G/M) ≤ S.map q`
    have hOple : Ch03.oPiCore ({p} : Set ℕ) (G ⧸ M) ≤ (S : Subgroup G).map q :=
      Ch03.Subgroup.IsPiGroup.normal_le_hall (Ch03.oPiCore.isPiGroup _) hHall
    -- `N = (O_p(G/M)).comap q`
    have hNdef : N = (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ M)).comap q := rfl
    rw [hNdef]
    calc (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ M)).comap q
        ≤ ((S : Subgroup G).map q).comap q := Subgroup.comap_mono hOple
      _ = (S : Subgroup G) ⊔ q.ker := Subgroup.comap_map_eq q (S : Subgroup G)
      _ = (S : Subgroup G) ⊔ M := by rw [hqker]
      _ = M ⊔ (S : Subgroup G) := sup_comm _ _
  · -- ⊇ direction: `M ⊔ S ≤ N`
    refine sup_le ?_ hSN
    rw [hM, hN]
    exact Ch03.oPiCore_compl_le_oPiPrimePiCore {p} G

omit [IsSolvable G] in
/-- **BG Lemma 6.6(1b)** (mmd L2092): `p`-length 1 で `G = O_{p'}(G) · N_G(S)`.

Frattini を `N = O_{p',p}(G)` の中の Sylow `S` に適用すると `N_G(S) · N = G`。foundation で
`N = M ⊔ S`, `S ≤ N_G(S)` ゆえ `S` は吸収され `N_G(S) ⊔ M ⊔ S = N_G(S) ⊔ M = G`。 -/
theorem top_eq_oPiPrimeCore_sup_normalizer_sylow (S : Sylow p G)
    (hpl1 : OddOrder.BG.Ch1.hasPLengthOne p G) :
    (⊤ : Subgroup G)
      = Ch03.oPiCore {q | q ∉ ({p}:Set ℕ)} G ⊔ Subgroup.normalizer (S : Subgroup G) := by
  set M : Subgroup G := Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G with hM
  -- `S ≤ N`, so Frattini in `G` (with `N = O_{p',p}(G)` normal) applies.
  have hSN : (S : Subgroup G) ≤ Ch03.oPiPrimePiCore {p} G :=
    pGroup_le_oPiPrimePiCore S.isPGroup' hpl1
  have hFrattini : Subgroup.normalizer (S : Subgroup G) ⊔ Ch03.oPiPrimePiCore {p} G = ⊤ :=
    Sylow.normalizer_sup_eq_top' S hSN
  -- rewrite `N = M ⊔ S`
  rw [oPiPrimePiCore_eq_oPiPrimeCore_sup_sylow S hpl1, ← hM] at hFrattini
  -- `N_G(S) ⊔ (M ⊔ S) = N_G(S) ⊔ M` because `S ≤ N_G(S)`.
  have hSnorm : (S : Subgroup G) ≤ Subgroup.normalizer (S : Subgroup G) := Subgroup.le_normalizer
  have habsorb : Subgroup.normalizer (S : Subgroup G) ⊔ (M ⊔ (S : Subgroup G))
      = Subgroup.normalizer (S : Subgroup G) ⊔ M := by
    rw [sup_comm M (S : Subgroup G), ← sup_assoc, sup_eq_left.mpr hSnorm]
  rw [habsorb] at hFrattini
  rw [← hFrattini, sup_comm]

/-- **BG Lemma 6.6(2)** (mmd L2096): `p`-length 1 で `S ≤ G' ⟹ S ≤ N_G(S)'`.

Lem 6.5(a) を `K = O_{p'}(G)`, `U = N_G(S)`, `H = S` に適用すると
`S ∩ G' = S ∩ N_G(S)'`。仮定 `S ≤ G'` で左辺 `= S` ゆえ `S ≤ N_G(S)'`。 -/
theorem sylow_le_commutator_normalizer_of_le_commutator (S : Sylow p G)
    (hpl1 : OddOrder.BG.Ch1.hasPLengthOne p G)
    (hS : (S : Subgroup G) ≤ commutator G) :
    (S : Subgroup G)
      ≤ ⁅(Subgroup.normalizer (S : Subgroup G) : Subgroup G),
          (Subgroup.normalizer (S : Subgroup G) : Subgroup G)⁆ := by
  set M : Subgroup G := Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G with hM
  -- `M ⊔ N_G(S) = ⊤` from (1b).
  have hKU : M ⊔ Subgroup.normalizer (S : Subgroup G) = ⊤ :=
    (top_eq_oPiPrimeCore_sup_normalizer_sylow S hpl1).symm
  have hHU : (S : Subgroup G) ≤ Subgroup.normalizer (S : Subgroup G) := Subgroup.le_normalizer
  have hcop : Nat.Coprime (Nat.card (S : Subgroup G)) (Nat.card M) :=
    sylow_card_coprime_oPiPrimeCore S
  -- Lem 6.5(a): `S ⊓ G' = S ⊓ ⁅N_G(S), N_G(S)⁆`.
  have hinf := inf_commutator_eq_of_coprime (H := (S : Subgroup G)) hKU hHU hcop
  -- `S ⊓ G' = S` since `S ≤ G'`, so `S = S ⊓ ⁅N,N⁆ ≤ ⁅N,N⁆`.
  rw [inf_eq_left.mpr hS] at hinf
  exact le_of_eq hinf |>.trans inf_le_right

/-- **BG Lemma 6.6(3)** (mmd L2098): `p`-length 1, `Y ⊆ S` 非空, `Y^x ⊆ S` (= `x⁻¹Yx ⊆ S`)
ならば `x = c·g` (`c ∈ C_G(Y)`, `g ∈ N_G(S)`)。

Lem 6.5(c) を `K = O_{p'}(G)`, `U = N_G(S)`, `H = ⟨Y⟩`, `g = x` に適用。`⟨Y⟩ ≤ S ≤ N_G(S)`,
`⟨Y⟩^x = ⟨x⁻¹Yx⟩ ≤ S ≤ N_G(S)` (`hYx`)。出力 `c ∈ C_G(⟨Y⟩) ⊓ M ≤ C_G(Y)`。 -/
theorem exists_mem_centralizer_mul_normalizer_of_conj_subset_sylow (S : Sylow p G)
    (hpl1 : OddOrder.BG.Ch1.hasPLengthOne p G)
    {Y : Set G} (_hYne : Y.Nonempty) (hYS : Y ⊆ (S : Subgroup G))
    {x : G} (hYx : ∀ y ∈ Y, x⁻¹ * y * x ∈ (S : Subgroup G)) :
    ∃ c ∈ Subgroup.centralizer Y, ∃ g ∈ Subgroup.normalizer (S : Subgroup G), c * g = x := by
  set M : Subgroup G := Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G with hM
  set H : Subgroup G := Subgroup.closure Y with hH
  -- `H ≤ S`
  have hHS : H ≤ (S : Subgroup G) := Subgroup.closure_le _ |>.mpr hYS
  -- `M ⊔ N_G(S) = ⊤`
  have hKU : M ⊔ Subgroup.normalizer (S : Subgroup G) = ⊤ :=
    (top_eq_oPiPrimeCore_sup_normalizer_sylow S hpl1).symm
  -- `H ≤ N_G(S)`
  have hHU : H ≤ Subgroup.normalizer (S : Subgroup G) := hHS.trans Subgroup.le_normalizer
  -- coprimality: `H ≤ S` is a `p`-group ⟹ card is `p`-power coprime to card M.
  have hHpg : IsPGroup p H := S.isPGroup'.to_le hHS
  have hcop : Nat.Coprime (Nat.card H) (Nat.card M) := by
    obtain ⟨n, hn⟩ := hHpg.exists_card_eq
    rw [hn]
    exact (card_oPiPrimeCore_coprime_prime (p := p) (G := G)).symm.pow_left n
  -- `H.comap (conj x) ≤ N_G(S)`: in fact `≤ S`.
  have hconj : H.comap (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (S : Subgroup G) := by
    refine le_trans ?_ Subgroup.le_normalizer
    -- `H.comap (conj x) = H.map (conj x).symm = closure ((conj x).symm '' Y) ≤ S`.
    rw [hH, Subgroup.comap_equiv_eq_map_symm', MonoidHom.map_closure]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro z ⟨y, hy, rfl⟩
    -- `(conj x).symm y = x⁻¹ * y * x ∈ S`
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply]
    exact hYx y hy
  -- apply Lem 6.5(c)
  obtain ⟨c, hc, u, hu, hxcu⟩ := exists_mem_centralizerK_mul_of_conj_le hKU hHU hcop hconj
  -- `c ∈ centralizer Y` from `c ∈ centralizer (closure Y) ⊓ M`.
  have hcCent : c ∈ Subgroup.centralizer Y := by
    have hc1 : c ∈ Subgroup.centralizer (H : Set G) := (Subgroup.mem_inf.mp hc).1
    rwa [hH, Subgroup.centralizer_closure] at hc1
  exact ⟨c, hcCent, u, hu, hxcu.symm⟩

omit [IsSolvable G] in
/-- `p`-length 1 のもとで, `p`-部分群 `Q` の `S`-共役: ある `g ∈ N = O_{p',p}(G)` で
`g Q g⁻¹ ≤ S` (`MulAut.conj g • Q ≤ S`)。`Q ≤ N` (`pGroup_le_oPiPrimePiCore`), `S` は `↥N` の
Sylow `p`, `Q.subgroupOf N` を含む Sylow へ Sylow II 共役 (`MulAction.exists_smul_eq`), 戻して
`g Q g⁻¹ ≤ S`。Lem 6.6(4) の共役元供給。 -/
private theorem exists_mem_oPiPrimePiCore_conj_le_sylow (S : Sylow p G)
    (hpl1 : hasPLengthOne p G) {Q : Subgroup G} (hQ : IsPGroup p Q) :
    ∃ g ∈ Ch03.oPiPrimePiCore {p} G, MulAut.conj g • Q ≤ (S : Subgroup G) := by
  set N : Subgroup G := Ch03.oPiPrimePiCore {p} G with hN
  -- `Q ≤ N`, `S ≤ N`.
  have hQN : Q ≤ N := pGroup_le_oPiPrimePiCore hQ hpl1
  have hSN : (S : Subgroup G) ≤ N := pGroup_le_oPiPrimePiCore S.isPGroup' hpl1
  -- `S` as a Sylow `p` of `↥N`.
  let S' : Sylow p ↥N := S.subtype hSN
  -- `Q.subgroupOf N` is a `p`-group of `↥N`, contained in some Sylow `Q'` of `↥N`.
  have hQsub_pg : IsPGroup p (Q.subgroupOf N) :=
    hQ.of_injective (Subgroup.subgroupOfEquivOfLe hQN).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQN).injective
  obtain ⟨Q', hQ'⟩ := hQsub_pg.exists_le_sylow
  -- Sylow II in `↥N`: `∃ h, h • Q' = S'`.
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (↥N) Q' S'
  refine ⟨(h : G), h.2, ?_⟩
  -- `h • (Q.subgroupOf N) ≤ h • Q' = S' = S.subgroupOf N`.
  have hstep1 : MulAut.conj h • (Q.subgroupOf N) ≤ S'.toSubgroup := by
    have hle : MulAut.conj h • (Q.subgroupOf N) ≤ MulAut.conj h • Q'.toSubgroup :=
      (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr hQ'
    have heq : MulAut.conj h • Q'.toSubgroup = S'.toSubgroup := by
      have := congrArg Sylow.toSubgroup hh
      rwa [Sylow.coe_subgroup_smul] at this
    rwa [heq] at hle
  -- Translate to `G`: `(MulAut.conj ↑h • Q).subgroupOf N ≤ S.subgroupOf N`.
  have hS'eq : S'.toSubgroup = (S : Subgroup G).subgroupOf N := S.coe_subtype hSN
  rw [Subgroup.conj_smul_subgroupOf hQN, hS'eq] at hstep1
  -- Reflect `subgroupOf` order: map via `N.subtype`.
  have hmapped : (MulAut.conj (h : G) • Q) ⊓ N ≤ (S : Subgroup G) ⊓ N := by
    have h2 := Subgroup.map_mono (f := N.subtype) hstep1
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype] at h2
  -- `MulAut.conj ↑h • Q ≤ N` (h ∈ N, Q ≤ N), so `(conj ↑h • Q) ⊓ N = conj ↑h • Q`.
  have hconjQN : MulAut.conj (h : G) • Q ≤ N := by
    rintro - ⟨a, ha, rfl⟩
    exact N.mul_mem (N.mul_mem h.2 (hQN ha)) (N.inv_mem h.2)
  rw [inf_of_le_left hconjQN, inf_of_le_left hSN] at hmapped
  exact hmapped

omit [IsSolvable G] in
/-- **BG Lemma 6.6(4)** (mmd L2103): `p`-length 1 で, `p`-部分群 `Q` に対し
`∃ x ∈ C_G(Q ⊓ S)`, `Q^x ⊆ S` (`Q.comap (conj x) ≤ S`, = `x⁻¹Qx ⊆ S`)。

`Q ≤ N = M ⊔ S`, `↑N = ↑S · ↑M`。共役 `g ∈ N` で `gQg⁻¹ ≤ S`
(`exists_mem_oPiPrimePiCore_conj_le_sylow`)。`g = s₀·m` (`s₀ ∈ S`, `m ∈ M`) ⟹
`m Q m⁻¹ ≤ s₀⁻¹ S s₀ = S`。`x := m⁻¹ ∈ M`: `Q.comap (conj x) = mQm⁻¹ ≤ S`,
かつ `m ∈ M` 正規 + `S ⊓ M = ⊥` で `x` が `Q ⊓ S` を中心化。 -/
theorem exists_mem_centralizer_inf_conj_le_sylow (S : Sylow p G)
    (hpl1 : OddOrder.BG.Ch1.hasPLengthOne p G) {Q : Subgroup G} (hQ : IsPGroup p Q) :
    ∃ x ∈ Subgroup.centralizer ((Q ⊓ (S : Subgroup G) : Subgroup G) : Set G),
      Q.comap (MulAut.conj x).toMonoidHom ≤ (S : Subgroup G) := by
  set M : Subgroup G := Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G with hM
  set N : Subgroup G := Ch03.oPiPrimePiCore {p} G with hN
  -- `S ⊓ M = ⊥`, `N = M ⊔ S`.
  have hSMbot : (S : Subgroup G) ⊓ M = ⊥ := sylow_inf_oPiPrimeCore_eq_bot S
  have hNMS : N = M ⊔ (S : Subgroup G) := oPiPrimePiCore_eq_oPiPrimeCore_sup_sylow S hpl1
  -- conjugate `g ∈ N` with `g Q g⁻¹ ≤ S`.
  obtain ⟨g, hgN, hgconj⟩ := exists_mem_oPiPrimePiCore_conj_le_sylow S hpl1 hQ
  -- decompose `g = s₀ * m`, `s₀ ∈ S`, `m ∈ M` (using `N = S ⊔ M`, `M` normal).
  have hgSM : g ∈ (S : Subgroup G) ⊔ M := by
    rw [sup_comm, ← hNMS]; exact hgN
  obtain ⟨s₀, hs₀, m, hmM, hg_eq⟩ := Subgroup.mem_sup_of_normal_right.mp hgSM
  -- `m Q m⁻¹ ≤ S`: from `g Q g⁻¹ ≤ S` and `s₀` normalizing `S`.
  have hmQ : MulAut.conj m • Q ≤ (S : Subgroup G) := by
    intro z hz
    -- `z = m q m⁻¹` with `q ∈ Q`; then `s₀ z s₀⁻¹ = g q g⁻¹ ∈ S`, and `s₀⁻¹ S s₀ = S`.
    obtain ⟨q, hq, rfl⟩ := hz
    have hgq : MulAut.conj g • Q ≤ (S : Subgroup G) := hgconj
    have hmem : (g : G) * q * (g : G)⁻¹ ∈ (S : Subgroup G) := hgq ⟨q, hq, rfl⟩
    -- `g q g⁻¹ = s₀ (m q m⁻¹) s₀⁻¹`.
    have hrw : (g : G) * q * (g : G)⁻¹
        = s₀ * (MulAut.conj m q) * s₀⁻¹ := by
      rw [MulAut.conj_apply, ← hg_eq]; group
    rw [hrw] at hmem
    -- `s₀⁻¹ (g q g⁻¹) s₀ = m q m⁻¹ ∈ S`.
    have hconjback : s₀⁻¹ * (s₀ * (MulAut.conj m q) * s₀⁻¹) * s₀ ∈ (S : Subgroup G) :=
      (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hs₀) hmem) hs₀
    have hsimp : s₀⁻¹ * (s₀ * (MulAut.conj m q) * s₀⁻¹) * s₀ = MulAut.conj m q := by group
    rwa [hsimp] at hconjback
  -- set `x := m⁻¹ ∈ M`. `Q.comap (conj x) = m Q m⁻¹ ≤ S`.
  refine ⟨m⁻¹, ?_, ?_⟩
  · -- `x = m⁻¹ ∈ centralizer (Q ⊓ S)`.
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_inf] at hz
    obtain ⟨hzQ, hzS⟩ := hz
    -- `d := (m⁻¹)⁻¹ z (m⁻¹) z⁻¹ = m z m⁻¹ z⁻¹ ∈ S ⊓ M = ⊥`.
    -- `m z m⁻¹ ∈ m Q m⁻¹ ≤ S` (since z ∈ Q), `z⁻¹ ∈ S`.
    have hmzm_S : m * z * m⁻¹ ∈ (S : Subgroup G) := by
      have hmem : m * z * m⁻¹ ∈ MulAut.conj m • Q := by
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
        have : m⁻¹ * (m * z * m⁻¹) * m = z := by group
        rw [this]; exact hzQ
      exact hmQ hmem
    have hd_S : m * z * m⁻¹ * z⁻¹ ∈ (S : Subgroup G) :=
      (S : Subgroup G).mul_mem hmzm_S ((S : Subgroup G).inv_mem hzS)
    -- `m z m⁻¹ z⁻¹ ∈ M` (m ∈ M normal).
    have hd_M : m * z * m⁻¹ * z⁻¹ ∈ M := by
      haveI : M.Normal := Ch03.oPiCore.normal _ _
      have hconjM : z * m⁻¹ * z⁻¹ ∈ M := by
        have := ‹M.Normal›.conj_mem m⁻¹ (M.inv_mem hmM) z
        simpa [mul_assoc] using this
      have heq : m * z * m⁻¹ * z⁻¹ = m * (z * m⁻¹ * z⁻¹) := by group
      rw [heq]; exact M.mul_mem hmM hconjM
    -- `d ∈ S ⊓ M = ⊥`, so `d = 1`, giving `m z m⁻¹ = z`, i.e. `z * m⁻¹ = m⁻¹ * z`.
    have hd1 : m * z * m⁻¹ * z⁻¹ = 1 := by
      have : m * z * m⁻¹ * z⁻¹ ∈ (S : Subgroup G) ⊓ M := Subgroup.mem_inf.mpr ⟨hd_S, hd_M⟩
      rw [hSMbot, Subgroup.mem_bot] at this
      exact this
    -- conclude `z * m⁻¹ = m⁻¹ * z`.
    have hmzm : m * z * m⁻¹ = z := by
      have := mul_eq_one_iff_eq_inv.mp hd1
      rw [inv_inv] at this; exact this
    -- `z * m⁻¹ = m⁻¹ * z`
    have : z * m⁻¹ = m⁻¹ * z := by
      have h4 : m⁻¹ * (m * z * m⁻¹) = m⁻¹ * z := by rw [hmzm]
      calc z * m⁻¹ = m⁻¹ * (m * z * m⁻¹) := by group
        _ = m⁻¹ * z := by rw [hmzm]
    exact this
  · -- `Q.comap (conj m⁻¹) = m Q m⁻¹ ≤ S`.
    intro z hz
    rw [mem_comap_conj, inv_inv] at hz
    -- `hz : m⁻¹ * z * m ∈ Q`.
    -- want `z ∈ S`. `z ∈ m Q m⁻¹ ≤ S`.
    have hzmem : z ∈ MulAut.conj m • Q := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
      exact hz
    exact hmQ hzmem

end


section /- 6.7 -/

open scoped Pointwise IsMulCommutative

open OddOrder.BG.Ch1 (hasPLengthOne)
open OddOrder.GroupTheory
open OddOrder.BG.Ch1.S01 (corollary_1_12 hall_higman_solvable_specialization
  inf_eq_bot_of_pGroup_coprime)

variable [Finite G] [IsSolvable G] {p : ℕ} [Fact p.Prime]

omit [IsSolvable G] in
/-- `O_p(G) ≤ O_{p',p}(G)`: the `p`-radical sits inside the `O_{p',p}` layer.
(`Ch03.oPiCore {p} G = Ch01.opCore p G` and `Ch01.opCore p G ≤ O_{p',p}(G)`.) -/
private theorem oPiCore_singleton_le_oPiPrimePiCore :
    Ch03.oPiCore ({p} : Set ℕ) G ≤ Ch03.oPiPrimePiCore {p} G := by
  rw [Ch04.oPiCore_singleton_eq_opCore]
  exact opCore_le_oPiPrimePiCore p

omit [IsSolvable G] [Finite G] in
/-- `⟨x⟩` is `p`-elementary abelian when `x ^ p = 1`. -/
private theorem zpowers_isElementaryAbelian_of_pow_eq_one {x : G} (hxp : x ^ p = 1) :
    (Subgroup.zpowers x).IsElementaryAbelian p := by
  letI : IsMulCommutative (Subgroup.zpowers x) := Subgroup.zpowers_isMulCommutative x
  refine ⟨?_, ?_⟩
  · intro a b
    exact Subtype.ext (congrArg Subtype.val (mul_comm a b))
  · intro a
    apply Subtype.ext
    change (a : G) ^ p = 1
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    rw [← hi, ← zpow_natCast (x ^ i) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hxp, one_zpow]

omit [IsSolvable G] in
/-- **E*(S) characterization (membership form)**: if `E` is a maximal elementary abelian
`p`-subgroup, then every order-`p` element of `C_G(E)` already lies in `E`. (Apply
`IsMaximalElementaryAbelian.le_of_le_centralizer` to `F = ⟨x⟩`.) -/
private theorem mem_of_mem_centralizer_pow_eq_one
    {E : Subgroup G} (hE : OddOrder.GroupTheory.IsMaximalElementaryAbelian p E)
    {x : G} (hxC : x ∈ Subgroup.centralizer (E : Set G)) (hxp : x ^ p = 1) :
    x ∈ E := by
  have hX : (Subgroup.zpowers x).IsElementaryAbelian p :=
    zpowers_isElementaryAbelian_of_pow_eq_one hxp
  have hEcent : E ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hy
    obtain ⟨i, hi⟩ := hy
    have hxe : Commute x e := (Subgroup.mem_centralizer_iff.mp hxC e he).symm
    have : Commute y e := by rw [← hi]; exact hxe.zpow_left i
    exact this.eq
  exact (hE.le_of_le_centralizer hX hEcent) (Subgroup.mem_zpowers x)

omit [IsSolvable G] [Fact (Nat.Prime p)] in
/-- **O_{p'}(G) = ⊥ ⟹ O_{p',p}(G) = O_p(G)**: if the lower `p'`-layer is trivial, the
`O_{p',p}` layer collapses to the `p`-radical. (`oPiPrimePiCore π G = comap (mk' M) (oPiCore π
(G/M))` with `M = ⊥`; `mk' ⊥` is the inverse of `quotientBot`, and `oPiCore` transports.) -/
private theorem oPiPrimePiCore_eq_oPiCore_of_compl_bot
    (h : Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥) :
    Ch03.oPiPrimePiCore {p} G = Ch03.oPiCore ({p} : Set ℕ) G := by
  have key : ∀ (M : Subgroup G) [M.Normal], M = ⊥ →
      Subgroup.comap (QuotientGroup.mk' M) (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ M))
        = Ch03.oPiCore ({p} : Set ℕ) G := by
    intro M _ hM
    subst hM
    rw [show (QuotientGroup.mk' (⊥ : Subgroup G))
        = (QuotientGroup.quotientBot (G := G)).symm.toMonoidHom from rfl]
    rw [Subgroup.comap_equiv_eq_map_symm']
    simp only [MulEquiv.symm_symm]
    exact Ch03.oPiCore.map_eq_of_mulEquiv ({p} : Set ℕ) (QuotientGroup.quotientBot (G := G))
  exact key _ h

-- (B1) reduced case: O_{p'}(G) = ⊥
private theorem thm67_reduced (hp_odd : p ≠ 2)
    (hK : Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥)
    (hpl1 : OddOrder.BG.Ch1.hasPLengthOne p G)
    {E : Subgroup G} (hE : OddOrder.GroupTheory.IsMaximalElementaryAbelian p E)
    {L : Subgroup G} (hLp' : ¬ p ∣ Nat.card L) (hEL : E ≤ Subgroup.normalizer L) :
    L = ⊥ := by
  classical
  -- Step 1: a Sylow `p`-subgroup `S ⊇ E`.
  obtain ⟨S, hES⟩ := (hE.isElementaryAbelian.isPGroup).exists_le_sylow
  -- Step 2: `O_{p',p}(G) = S`.
  have hN : Ch03.oPiPrimePiCore {p} G = (S : Subgroup G) := by
    rw [oPiPrimePiCore_eq_oPiPrimeCore_sup_sylow S hpl1, hK, bot_sup_eq]
  -- Step 3: `S ⊴ G`.
  haveI hSnorm : (S : Subgroup G).Normal := hN ▸ Ch03.oPiPrimePiCore.normal {p} G
  -- Step 4: `S = O_p(G)`.
  have hS_eq_Op : (S : Subgroup G) = Ch03.oPiCore ({p} : Set ℕ) G := by
    refine le_antisymm ?_ ?_
    · apply Ch03.Subgroup.IsPiGroup.le_oPiCore
      intro r hr
      obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
      rw [hn, Nat.mem_primeFactors] at hr
      have : r = p := (Nat.prime_dvd_prime_iff_eq hr.1 Fact.out).mp (hr.1.dvd_of_dvd_pow hr.2.1)
      rw [this]; exact Set.mem_singleton p
    · calc Ch03.oPiCore ({p} : Set ℕ) G ≤ Ch03.oPiPrimePiCore {p} G :=
            oPiCore_singleton_le_oPiPrimePiCore
        _ = (S : Subgroup G) := hN
  -- `L ⊓ S = ⊥` (`L` a `p'`-group, `S` a `p`-group).
  have hScopL : Nat.Coprime (Nat.card (S : Subgroup G)) (Nat.card L) := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hLp').pow_left n
  have hLSbot : L ⊓ (S : Subgroup G) = ⊥ := inf_eq_bot_of_coprime_card hScopL.symm
  -- Step 5: `L` centralizes `E`.
  have hLcentE : ∀ l ∈ L, ∀ e ∈ E, l * e = e * l := by
    intro l hl e he
    have heS : e ∈ (S : Subgroup G) := hES he
    have hcomm_S : l * e * l⁻¹ * e⁻¹ ∈ (S : Subgroup G) := by
      have hleS : l * e * l⁻¹ ∈ (S : Subgroup G) := by
        have := hSnorm.conj_mem e heS l
        simpa [mul_assoc] using this
      exact (S : Subgroup G).mul_mem hleS ((S : Subgroup G).inv_mem heS)
    have hcomm_L : l * e * l⁻¹ * e⁻¹ ∈ L := by
      have hconjL : e * l⁻¹ * e⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hEL he) l⁻¹).mp (L.inv_mem hl)
      have heq : l * e * l⁻¹ * e⁻¹ = l * (e * l⁻¹ * e⁻¹) := by group
      rw [heq]; exact L.mul_mem hl hconjL
    have hcomm1 : l * e * l⁻¹ * e⁻¹ = 1 := by
      have : l * e * l⁻¹ * e⁻¹ ∈ L ⊓ (S : Subgroup G) :=
        Subgroup.mem_inf.mpr ⟨hcomm_L, hcomm_S⟩
      rw [hLSbot, Subgroup.mem_bot] at this; exact this
    have h1 : l * e * l⁻¹ = e := mul_inv_eq_one.mp hcomm1
    calc l * e = (l * e * l⁻¹) * l := by group
      _ = e * l := by rw [h1]
  -- Step 6+7: Cor 1.12 (conjugation form). `L ≤ N_G(S) = ⊤`; set up `φ : ↥L → Aut ↥S`.
  have hLnormS : L ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top (S : Subgroup G)]; exact le_top
  set φ : ↥L →* MulAut ↥(S : Subgroup G) :=
    (S : Subgroup G).normalizerMonoidHom.comp (Subgroup.inclusion hLnormS) with hφ
  have hφcoe : ∀ (a : ↥L) (g : ↥(S : Subgroup G)),
      ((φ a) g : G) = (a : G) * (g : G) * (a : G)⁻¹ := by
    intro a g; rw [hφ]; rfl
  have hEsub : (E.subgroupOf (S : Subgroup G)).IsElementaryAbelian p := by
    refine Subgroup.IsElementaryAbelian.of_map (S : Subgroup G).subtype_injective ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hES]
    exact hE.isElementaryAbelian
  have h_fix : ∀ g : ↥(S : Subgroup G),
      g ∈ Subgroup.centralizer ((E.subgroupOf (S : Subgroup G) :
        Subgroup ↥(S : Subgroup G)) : Set ↥(S : Subgroup G)) →
      g ^ p = 1 → ∀ a : ↥L, (φ a) g = g := by
    intro g hg hgp a
    have hgcentE : (g : G) ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyS : y ∈ (S : Subgroup G) := hES hy
      have hy' : (⟨y, hyS⟩ : ↥(S : Subgroup G)) ∈
          (E.subgroupOf (S : Subgroup G) : Subgroup ↥(S : Subgroup G)) := by
        rw [Subgroup.mem_subgroupOf]; exact hy
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg ⟨y, hyS⟩ hy')
    have hgp' : (g : G) ^ p = 1 := by
      have := congrArg (fun x : ↥(S : Subgroup G) => (x : G)) hgp
      simpa using this
    have hgE : (g : G) ∈ E := mem_of_mem_centralizer_pow_eq_one hE hgcentE hgp'
    refine Subtype.ext ?_
    rw [hφcoe, hLcentE (a : G) a.2 (g : G) hgE, mul_assoc, mul_inv_cancel, mul_one]
  have htriv := corollary_1_12 (A := ↥L) (G := ↥(S : Subgroup G)) hp_odd S.isPGroup'
    (by simpa using hLp') φ hEsub h_fix
  have hLcentS : L ≤ Subgroup.centralizer (S : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hco := congrArg Subtype.val (htriv ⟨l, hl⟩ ⟨s, hs⟩)
    rw [hφcoe] at hco
    have h1 : l * s * l⁻¹ = s := hco
    calc s * l = (l * s * l⁻¹) * l := by rw [h1]
      _ = l * s := by group
  -- Step 8: Prop 1.15(a): `C_G(O_p) ≤ O_p`, so `L ≤ S`; with `L ⊓ S = ⊥`, `L = ⊥`.
  have hHH : Subgroup.centralizer (Ch03.oPiCore ({p} : Set ℕ) G : Set G) ≤
      Ch03.oPiCore ({p} : Set ℕ) G := hall_higman_solvable_specialization hK
  have hL_le_S : L ≤ (S : Subgroup G) := by
    rw [hS_eq_Op]
    exact le_trans hLcentS (hS_eq_Op ▸ hHH)
  have : L ≤ L ⊓ (S : Subgroup G) := le_inf le_rfl hL_le_S
  rw [hLSbot, le_bot_iff] at this
  exact this

omit [IsSolvable G] in
/-- **(B2) lift**: the image of a maximal elementary abelian `p`-subgroup under a quotient by
a normal `p'`-subgroup `K` is again maximal elementary abelian. The maximality is the crux:
a larger elementary abelian `Fbar` lifts to `F = Fbar.comap (mk' K)`, whose Sylow-`p`
subgroup `PF` is elementary abelian (`PF ⊓ K = ⊥` with `F/K` abelian of exponent `p`) and
contains `E`, so `PF = E` by maximality, and `PF` maps onto `Fbar`. -/
private theorem isMaximalElementaryAbelian_map_mk'
    (K : Subgroup G) [K.Normal] (hKp' : (Nat.card K).Coprime p)
    {E : Subgroup G} (hE : OddOrder.GroupTheory.IsMaximalElementaryAbelian p E) :
    OddOrder.GroupTheory.IsMaximalElementaryAbelian p (E.map (QuotientGroup.mk' K)) := by
  classical
  set q : G →* G ⧸ K := QuotientGroup.mk' K with hqdef
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective K
  have hqker : q.ker = K := QuotientGroup.ker_mk' K
  -- `E ⊓ K = ⊥` ⟹ `q` injective on `E`.
  have hEKbot : E ⊓ K = ⊥ := by
    have hEcop : Nat.Coprime (Nat.card E) (Nat.card K) := by
      obtain ⟨n, hn⟩ := hE.isElementaryAbelian.isPGroup.exists_card_eq
      rw [hn]; exact (hKp'.symm.pow_left n)
    exact inf_eq_bot_of_coprime_card hEcop
  have hqinjE : Function.Injective (q.comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype] at hx
    have hxK : (x : G) ∈ K := by
      rw [hqdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx; exact hx
    have hxEK : (x : G) ∈ E ⊓ K := Subgroup.mem_inf.mpr ⟨x.2, hxK⟩
    rw [hEKbot, Subgroup.mem_bot] at hxEK
    exact Subtype.ext hxEK
  refine ⟨?_, ?_⟩
  · -- `E.map q` elementary abelian.
    have hmap_eq : E.map q = (⊤ : Subgroup E).map (q.comp (Subgroup.subtype E)) := by
      rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hmap_eq]
    have htop : (⊤ : Subgroup E).IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.topEquiv).symm hE.isElementaryAbelian
    exact htop.map hqinjE
  · -- maximality.
    intro Fbar hFbar hEFbar
    set F : Subgroup G := Fbar.comap q with hFdef
    have hKF : K ≤ F := by
      intro k hk
      rw [hFdef, Subgroup.mem_comap]
      have : q k = 1 := by rw [← MonoidHom.mem_ker, hqker]; exact hk
      rw [this]; exact Fbar.one_mem
    have hFmapq : F.map q = Fbar := by
      rw [hFdef]; exact Subgroup.map_comap_eq_self_of_surjective hqsurj Fbar
    have hFbarpg : IsPGroup p Fbar := hFbar.isPGroup
    have hEF : E ≤ F := by
      intro e he; rw [hFdef, Subgroup.mem_comap]; exact hEFbar (Subgroup.mem_map_of_mem q he)
    have hEsubF : IsPGroup p (E.subgroupOf F) := by
      have hmap : (E.subgroupOf F).map F.subtype = E ⊓ F := Subgroup.subgroupOf_map_subtype E F
      have hiso := Subgroup.equivMapOfInjective (E.subgroupOf F) F.subtype F.subtype_injective
      rw [hmap, inf_eq_left.mpr hEF] at hiso
      exact hE.isElementaryAbelian.isPGroup.of_equiv hiso.symm
    obtain ⟨PFsub, hEsub_le⟩ := hEsubF.exists_le_sylow
    set PF : Subgroup G := (PFsub : Subgroup ↥F).map F.subtype with hPFdef
    have hPF_le_F : PF ≤ F := by rw [hPFdef]; exact Subgroup.map_subtype_le _
    have hE_le_PF : E ≤ PF := by
      rw [hPFdef]; intro e he
      exact ⟨⟨e, hEF he⟩, hEsub_le (by rw [Subgroup.mem_subgroupOf]; exact he), rfl⟩
    have hPF_pg : IsPGroup p PF := by rw [hPFdef]; exact PFsub.2.map F.subtype
    have hPFKbot : PF ⊓ K = ⊥ :=
      OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hPF_pg hKp'
    have hPF_elem : PF.IsElementaryAbelian p := by
      refine ⟨?_, ?_⟩
      · intro a b
        refine Subtype.ext ?_
        change (a : G) * (b : G) = (b : G) * (a : G)
        have hcomm_K : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ K := by
          rw [← hqker, MonoidHom.mem_ker]
          have haF : q (a : G) ∈ Fbar := by
            rw [← hFmapq]; exact Subgroup.mem_map_of_mem q (hPF_le_F a.2)
          have hbF : q (b : G) ∈ Fbar := by
            rw [← hFmapq]; exact Subgroup.mem_map_of_mem q (hPF_le_F b.2)
          have habcomm : q (a:G) * q (b:G) = q (b:G) * q (a:G) :=
            congrArg Subtype.val (hFbar.comm ⟨_, haF⟩ ⟨_, hbF⟩)
          simp only [map_mul, map_inv]
          rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, habcomm]
        have hcomm_PF : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ PF :=
          PF.mul_mem (PF.mul_mem (PF.mul_mem a.2 b.2) (PF.inv_mem a.2)) (PF.inv_mem b.2)
        have hcomm1 : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ = 1 := by
          have : _ ∈ PF ⊓ K := Subgroup.mem_inf.mpr ⟨hcomm_PF, hcomm_K⟩
          rw [hPFKbot, Subgroup.mem_bot] at this; exact this
        have h1 : (a : G) * (b : G) * (a : G)⁻¹ = (b : G) := mul_inv_eq_one.mp hcomm1
        calc (a : G) * (b : G) = ((a : G) * (b : G) * (a : G)⁻¹) * (a : G) := by group
          _ = (b : G) * (a : G) := by rw [h1]
      · intro x
        refine Subtype.ext ?_
        change (x : G) ^ p = 1
        have hxp_K : (x : G) ^ p ∈ K := by
          rw [← hqker, MonoidHom.mem_ker, map_pow]
          have hxF : q (x : G) ∈ Fbar := by
            rw [← hFmapq]; exact Subgroup.mem_map_of_mem q (hPF_le_F x.2)
          exact congrArg Subtype.val (hFbar.pow_eq_one ⟨_, hxF⟩)
        have hxp_PF : (x : G) ^ p ∈ PF := PF.pow_mem x.2 p
        have : (x : G) ^ p ∈ PF ⊓ K := Subgroup.mem_inf.mpr ⟨hxp_PF, hxp_K⟩
        rw [hPFKbot, Subgroup.mem_bot] at this; exact this
    have hPF_eq_E : PF = E := hE.eq_of_le hPF_elem hE_le_PF
    have hPFmapq : PF.map q = Fbar := by
      have hle : PF.map q ≤ Fbar := by rw [← hFmapq]; exact Subgroup.map_mono hPF_le_F
      have hcard_eq : Nat.card (PF.map q) = Nat.card PF := by
        have h1 : Nat.card (PF.map q) = K.relIndex PF := by rw [← Subgroup.relIndex_ker, hqker]
        have hbot' : K.subgroupOf PF = ⊥ :=
          Subgroup.subgroupOf_eq_bot.mpr (by rw [disjoint_iff, inf_comm]; exact hPFKbot)
        rw [h1]; change (K.subgroupOf PF).index = Nat.card PF
        rw [hbot', Subgroup.index_bot]
      have hcardKsub : Nat.card (K.subgroupOf F) = Nat.card K := by
        have hm : (K.subgroupOf F).map F.subtype = K ⊓ F := Subgroup.subgroupOf_map_subtype K F
        have hiso := Subgroup.equivMapOfInjective (K.subgroupOf F) F.subtype F.subtype_injective
        rw [hm, inf_eq_left.mpr hKF] at hiso
        exact Nat.card_congr hiso.toEquiv
      have hcardF : Nat.card (F.map q) * Nat.card K = Nat.card F := by
        have h1 : Nat.card (F.map q) = K.relIndex F := by rw [← Subgroup.relIndex_ker, hqker]
        have h2 : Nat.card ↥F = K.relIndex F * Nat.card (K.subgroupOf F) := by
          rw [Subgroup.relIndex]
          exact Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf F)
        rw [hcardKsub] at h2
        rw [h1]; exact h2.symm
      have hcardPF_idx : Nat.card PF * (PFsub : Subgroup ↥F).index = Nat.card F := by
        have h1 : Nat.card PF = Nat.card (PFsub : Subgroup ↥F) := by
          rw [hPFdef]
          exact (Nat.card_congr (Subgroup.equivMapOfInjective _ F.subtype
            F.subtype_injective).toEquiv).symm
        rw [h1]; exact (PFsub : Subgroup ↥F).card_mul_index
      have hidx_p' : ¬ p ∣ (PFsub : Subgroup ↥F).index := PFsub.not_dvd_index
      have hcardPF_cop_K : Nat.Coprime (Nat.card PF) (Nat.card K) := by
        obtain ⟨b, hb⟩ := hPF_pg.exists_card_eq
        rw [hb]; exact hKp'.symm.pow_left b
      have hcardFbar_cop_idx : Nat.Coprime (Nat.card Fbar) ((PFsub : Subgroup ↥F).index) := by
        obtain ⟨a, ha⟩ := hFbarpg.exists_card_eq
        rw [ha]; exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hidx_p').pow_left a
      have hcardFbar : Nat.card Fbar = Nat.card (F.map q) := by rw [hFmapq]
      have hPF_dvd : Nat.card PF ∣ Nat.card Fbar := by
        have hdvd : Nat.card PF ∣ Nat.card (F.map q) * Nat.card K := by
          rw [hcardF]; exact ⟨(PFsub : Subgroup ↥F).index, hcardPF_idx.symm⟩
        rw [hcardFbar]; exact hcardPF_cop_K.dvd_of_dvd_mul_right hdvd
      have hFbar_dvd : Nat.card Fbar ∣ Nat.card PF := by
        have hdvd : Nat.card Fbar ∣ Nat.card PF * (PFsub : Subgroup ↥F).index := by
          rw [hcardPF_idx, hcardFbar]; exact ⟨Nat.card K, hcardF.symm⟩
        exact hcardFbar_cop_idx.dvd_of_dvd_mul_right hdvd
      have hcardPF_eq : Nat.card PF = Nat.card Fbar := Nat.dvd_antisymm hPF_dvd hFbar_dvd
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [hcard_eq, hcardPF_eq]
    rw [← hPFmapq, hPF_eq_E]

-- (B2) general form. CONCLUSION = L ≤ O_{p'}(G).
theorem le_oPiPrimeCore_of_normalized_by_maximalElementaryAbelian (hp_odd : p ≠ 2)
    {E : Subgroup G} (hE : OddOrder.GroupTheory.IsMaximalElementaryAbelian p E)
    {L : Subgroup G} (hLp' : ¬ p ∣ Nat.card L) (hEL : E ≤ Subgroup.normalizer L)
    (hpl1 : OddOrder.BG.Ch1.hasPLengthOne p G) :
    L ≤ Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G := by
  classical
  set K : Subgroup G := Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G with hKdef
  haveI : K.Normal := Ch03.oPiCore.normal _ G
  set q : G →* G ⧸ K := QuotientGroup.mk' K with hqdef
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective K
  have hKp' : (Nat.card K).Coprime p := card_oPiPrimeCore_coprime_prime
  -- (a) `O_{p'}(G/K) = ⊥`.
  have hKq : Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} (G ⧸ K) = ⊥ :=
    Ch03.oPiCore_quotient_self_eq_bot _
  -- (b) `E.map q` is maximal elementary abelian in `G/K`.
  have hEbar : OddOrder.GroupTheory.IsMaximalElementaryAbelian p (E.map q) :=
    isMaximalElementaryAbelian_map_mk' K hKp' hE
  -- (c) `L.map q` is a `p'`-group.
  have hLbar_p' : ¬ p ∣ Nat.card (L.map q) := fun hdvd =>
    hLp' (hdvd.trans (Subgroup.card_map_dvd L q))
  -- (d) `E.map q` normalizes `L.map q`.
  have hELbar : E.map q ≤ Subgroup.normalizer (L.map q) :=
    le_trans (Subgroup.map_mono hEL) (Subgroup.le_normalizer_map q)
  -- (e) `G/K` has `p`-length one (third isomorphism theorem).
  have hpl1bar : OddOrder.BG.Ch1.hasPLengthOne p (G ⧸ K) := by
    have hKle : K ≤ Ch03.oPiPrimePiCore {p} G := by
      rw [hKdef]; exact Ch03.oPiCore_compl_le_oPiPrimePiCore {p} G
    -- `(oPiPrimePiCore {p} G).map q = oPiCore {p}(G/K)`
    -- (def: `oPiPrimePiCore {p} G = comap q O_p(G/K)`).
    have hmapO : (Ch03.oPiPrimePiCore {p} G).map q = Ch03.oPiCore ({p} : Set ℕ) (G ⧸ K) := by
      rw [hqdef]
      change ((Ch03.oPiCore ({p} : Set ℕ) (G ⧸ K)).comap (QuotientGroup.mk' K)).map
        (QuotientGroup.mk' K) = _
      exact Subgroup.map_comap_eq_self_of_surjective hqsurj _
    -- `oPiPrimePiCore {p}(G/K) = oPiCore {p}(G/K)` since `O_{p'}(G/K) = ⊥`.
    have hOpp_GK : Ch03.oPiPrimePiCore {p} (G ⧸ K) = Ch03.oPiCore ({p} : Set ℕ) (G ⧸ K) :=
      oPiPrimePiCore_eq_oPiCore_of_compl_bot hKq
    -- third iso: `(G/K) ⧸ ((oPiPrimePiCore {p} G).map q) ≃* G ⧸ oPiPrimePiCore {p} G`.
    have hcard_eq : Nat.card ((G ⧸ K) ⧸ Ch03.oPiPrimePiCore {p} (G ⧸ K)) =
        Nat.card (G ⧸ Ch03.oPiPrimePiCore {p} G) := by
      rw [hOpp_GK, ← hmapO]
      exact Nat.card_congr
        (QuotientGroup.quotientQuotientEquivQuotient K _ hKle).toEquiv
    rw [hasPLengthOne] at hpl1 ⊢
    rw [hcard_eq]; exact hpl1
  -- apply the reduced case to `G/K`.
  have hLbar_bot : L.map q = ⊥ :=
    thm67_reduced (G := G ⧸ K) hp_odd hKq hpl1bar hEbar hLbar_p' hELbar
  have hle : L ≤ q.ker := (Subgroup.map_eq_bot_iff L).mp hLbar_bot
  rwa [hqdef, QuotientGroup.ker_mk'] at hle

end

end OddOrder.BG.Ch1.S06
