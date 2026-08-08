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
# BG §6 — additional lemmas: the opening blocks (conjugation bridges + Lem 6.3)

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
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

BG Thm 6.2 (`Z(J(S))·O_{p'}(G) ⊴ G`, 任意 S) の reduced case。

⚠ **一般形は本定理に簡約できない** (2026-07-19 調査確定、issue 3017)。旧 docstring は
「`O_{p'}(G)` で商を取り本定理に簡約する (後続コミット)」と書いていたが、これは**誤り**で、
その道を辿ると行き止まりになる。障害は仮説 `C_G(Z(P)) = P` で、これは一般の奇数位数 solvable
`G` (`O_{p'}(G) = ⊥` でも) で**自動でない** — 反例: `p = 7`、`P = 7^{1+2}` (指数 7)、
`C₃ ≤ SL(2,7)` (`3 ∣ 7−1` ゆえ存在) として `G = P ⋊ C₃` (位数 1029) は奇数・solvable・
`O_{7'}(G) = 1` だが、`C₃` は行列式 1 で作用するので `Z(P)` を中心化し `C_G(Z(P)) = G ≠ P`。

一般形に要るのは Glauberman ZJ (p-stable + p-constrained が仮説) であって、本定理の
`C_G(Z(P)) = P` 版ではない。BG 自身 p.49 で証明を **G** Thm 6.5.1/8.2.11 (= Gorenstein の
ZJ) への引用で済ませており、math-comp も ZJ を形式化せず Puig の `L(S)` で代替している
(`BGappendixAB.v:16`)。本 repo も `L(S)` 一般形は済 = `AppB_Thm62.zCenter_lOdd_sup_oPiCore_normal`
(book の Remark が推奨する代替)。literal `J(S)` 一般形は Gorenstein Ch.8 §2 の移植待ち。
詳細と規模見積は `S06_Thm62JS.lean` の docstring と issue 3017 を参照。 -/
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
特殊形 (reduced case)。

**一般形は済** — `OddOrder.BG.AppA.thmA4b` (`O_{p'}(G) = ⊥` も `C_G(Z(P)) = P` も仮定せず、
`O_{p'}` reduction を内部で行う) が BG Thm 6.1 そのもの (mmd L4627「Theorem A.4(b) is just
Theorem 6.1」)。§6 側の入口は `S06_Thm61.le_oPiPrimePiCore_of_abelian_normal_in_sylow`
(`thmA4b` の `p ≠ 2` を任意素数へ外したもの)。本定理はその `J(P)`-instance にすぎない。 -/
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
theorem commutator_le_sup_commutator {K U : Subgroup G} [K.Normal]
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

open OddOrder.GroupTheory in
/-- **BG Lemma 6.3(a)** (mmd L1981), the book's packaging.  Let `G` be a finite solvable group,
`H` a **normal Hall** subgroup of `G` and `K` a complement of `H` in `G`, with `H ⊆ G'`.  Then

* `H = ⁅H, K⁆`, and
* `C_H(K) ⊆ H'`.

The book's "Hall" hypothesis is rendered as the coprimality `(|H|, |K|) = 1` (equivalent for a
normal subgroup with a complement).  Mirrors `lemma63b` (`S06_Lem63b.lean`), which packages the
two conclusions of part (b) the same way.

⚠ The first conclusion `commutator_eq_self_of_isComplement'_le_commutator` is **stronger than
this clause**: it needs neither finiteness nor coprimality.  Cite it directly when the Hall
hypothesis is unavailable. -/
theorem lemma63a [Finite G] [IsSolvable G]
    {H K : Subgroup G} [H.Normal] (hHK : H.IsComplement' K) (hH : H ≤ commutator G)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥K)) :
    ⁅H, K⁆ = H ∧ Subgroup.centralizer (K : Set G) ⊓ H ≤ derivedInG H :=
  ⟨commutator_eq_self_of_isComplement'_le_commutator hHK hH,
    centralizer_inf_le_derivedInG_of_isComplement' hHK hH hcop⟩

end /- 6.3 -/

/-! ## 6.5: 可解群の N/C 分解 (pp. 64-65, mmd L2048-2088)

**Lemma 6.5**: `K, U, H ≤ G` 可解, `K ⊴ G`, `G = KU`, `H ⊆ U`, `(|H|, |K|) = 1` のとき
(a) `H ∩ G' = H ∩ U'`, (b) `N_G(H) = C_K(H)·N_U(H)`, (c) `H^g ⊆ U ⇒ g = cu`
(`c ∈ C_K(H)`, `u ∈ U`)。§8 (`N_G(P)=LC_K(P)`), §10, §13, Thm 7.4(d) で多用。
原文どおり (b) は (c) から従い, (c) が本体 (Hall π-部分群の共役)。 -/


end OddOrder.BG.Ch1.S06
