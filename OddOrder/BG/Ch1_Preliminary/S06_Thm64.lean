/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S01_FrattiniBurnside

/-!
# BG §6: Theorem 6.4 — coprime engine and the centralizing-conjugator step

Bender–Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
Chapter I §6 (p. 50), mmd `references/bg/local-analysis.mmd` L2011–L2038.

> **Theorem 6.4.** Suppose `G` is a group, `π` is a set of primes, `H` is a `π'`-subgroup of
> `G`, and `G₀` is a normal Hall subgroup of `G`. Assume that `G₀/F(G₀)` and
> `(G/G₀)/F(G/G₀)` are nilpotent. Assume further that `H` normalizes two `π`-subgroups `J₁`
> and `J₂` of `G`. Then there exists an element `x ∈ ⟨J₁, J₂⟩` such that `⟨J₁ˣ, J₂⟩` is a
> `π`-group and `x` centralizes `H`.

**状態**: 本ファイルは Theorem 6.4 本体の**上流部品**を提供する (本体は未形式化)。
BG の証明 (`|G| + |H|` の帰納法) は二つの場合に分かれ, どちらも下の部品を骨格に使う。

* `exists_centralizing_conj_sup_isPiGroup` — **Prop 1.5(b)+(c) の subgroup 合成形**。
  BG が Theorem 6.4 の場合 1 の最終段で「By Proposition 1.5, there exists `w ∈ C_{L*}(H)`
  such that `⟨J₁^{yzw}, J₂⟩` is a `π`-group」と一行で済ませている推論そのもの。
  作用群 `A` と作用先 `N` の位数が互いに素なとき, `A`-不変な二つの `π`-部分群は
  `C_G(A)` の元による共役で同時に一つの `π`-群へ入る。Theorem 6.4 は本補題の
  「`|A|`, `|N|` が互いに素」という仮定を Hall/Fitting 仮説へ弱めた一般化にあたるので,
  これが場合 1 の実質的なエンジンになる。

* `mem_centralizer_of_mem_normalizer_of_commutator_le` — 場合 1 の
  「`yz` は `H` を中心化する」段 (下記の**誤植訂正**込み)。

* `isSolvable_of_isNilpotent_quotient_fitting_of_normal` — Theorem 6.4 の二つの Fitting 商
  仮説 (`G₀/F(G₀)` と `(G/G₀)/F(G/G₀)` が冪零) から `G` の可解性を導く段。Proposition 1.5
  (場合 1 のエンジン `exists_centralizing_conj_sup_isPiGroup` が使う) が可解性を要求するので
  必要になる。

正規 Hall 部分群の仮説を部分群 `L ⊔ H` と商 `G ⧸ N` へ移す部分は
`OddOrder.GroupTheory.NormalHallHeredity`, Fitting 商の仮説を移す部分は
`OddOrder.GroupTheory.FittingHeredity` にある (どちらも汎用補題なので `GroupTheory/` 側)。

## ⚠ 原文の誤植 (p. 50)

BG p. 50 の場合 1 は, `y ∈ L` と `z ∈ N` を取って `H^{yz} = H` としたのち

> `[H, yz] ⊆ H ∩ L = 1.`

と書く (mmd L2031, PDF p. 50 の印字でも同一) が, **`H ∩ L = 1` は仮定から従わない**。
`G = LH` かつ `L ⊴ G` という直前の設定は `G/L ≅ H/(H ∩ L)` を与えるだけで,
`H ∩ L` の自明性は主張していない。

正しくは `L` ではなく `N` で, `[H, yz] ⊆ H ∩ N = 1` である:

* `yz ∈ N_G(H)` より `[H, yz] ⊆ H`;
* `y` が `HN/N` を中心化する (6.3) ので各 `h ∈ H` に対し `h⁻¹ h^y ∈ N`, かつ `z ∈ N` と
  `N ⊴ G` より `h⁻¹ h^{yz} ∈ N`, すなわち `[H, yz] ⊆ N`;
* `N ≤ O_p(F(G))` は `p`-群で `p ∉ π(H)` ゆえ `H ∩ N = 1` — これは BG 自身が直前に
  述べる「`H` is a Hall `p'`-subgroup of `HN`」と同じ内容。

よって結論 (`yz` が `H` を中心化する) は正しく, 証明は `H ∩ L` を `H ∩ N` に読み替えれば
そのまま通る。この訂正版が `mem_centralizer_of_mem_normalizer_of_commutator_le`。
-/

namespace OddOrder.BG.Ch1.S06

open Pointwise
open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-! ## 共役と `subgroupOf` の相互作用 (局所 helper) -/

private theorem subtype_comp_conj_eq {U : Subgroup G} (n' : ↥U) :
    U.subtype.comp ((MulAut.conj n').toMonoidHom) =
      ((MulAut.conj (n'.val : G)).toMonoidHom).comp U.subtype := by
  ext ⟨x, hx⟩; rfl

private theorem map_subtype_conj_subgroupOf {U : Subgroup G} (n' : ↥U) (K : Subgroup G)
    (hKU : K ≤ U) :
    ((K.subgroupOf U).map (MulAut.conj n').toMonoidHom).map U.subtype =
      K.map (MulAut.conj (n'.val : G)).toMonoidHom := by
  rw [Subgroup.map_map, subtype_comp_conj_eq, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hKU]

/-- The pointwise `MulAut.conj` action on a subgroup is the image under the conjugation
homomorphism. -/
theorem conj_smul_eq_map (g : G) (K : Subgroup G) :
    MulAut.conj g • K = K.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]; rfl

/-! ## `π`-部分群性の移送 -/

/-- A subgroup of a `π`-subgroup is a `π`-subgroup (its order divides). -/
theorem isPiSubgroup_of_le [Finite G] {π : Set ℕ} {K P : Subgroup G} (hKP : K ≤ P)
    (hP : Subgroup.IsPiSubgroup π P) : Subgroup.IsPiSubgroup π K := by
  intro p hp
  obtain ⟨hprime, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  exact hP p (Nat.mem_primeFactors.mpr
    ⟨hprime, hdvd.trans (Subgroup.card_dvd_of_le hKP), Nat.card_pos.ne'⟩)

/-- An ambient `π`-subgroup `K ≤ N` becomes a `π`-group inside the subtype `↥N`. -/
theorem isPiGroup_subgroupOf {π : Set ℕ} {N K : Subgroup G} (hKN : K ≤ N)
    (hK : Subgroup.IsPiSubgroup π K) : Ch03.Subgroup.IsPiGroup π (K.subgroupOf N) := by
  intro p hp
  exact hK p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv] at hp)

/-- A `π`-group inside the subtype `↥N` pushes forward to an ambient `π`-subgroup. -/
theorem isPiSubgroup_map_subtype {π : Set ℕ} {N : Subgroup G} {P : Subgroup ↥N}
    (hP : Ch03.Subgroup.IsPiGroup π P) : Subgroup.IsPiSubgroup π (P.map N.subtype) := by
  intro p hp
  exact hP p (by rwa [Subgroup.card_map_of_injective N.subtype_injective] at hp)

/-! ## BG Proposition 1.5(b)+(c), subgroup 合成形 -/

/-- **BG Proposition 1.5(b)+(c), joint subgroup form** — Theorem 6.4 の場合 1 で使われる
「一手で二つの `π`-部分群を一つの `π`-群に入れる」推論。

`A` が `N` を正規化し `(|A|, |N|) = 1` で `N` が可解, `J₁, J₂ ≤ N` が `A`-不変な
`π`-部分群のとき, ある `w ∈ N ∩ C_G(A)` が存在して `⟨J₁^w, J₂⟩` は `π`-群になる。

証明は BG の一行 (p. 50, "By Proposition 1.5, there exists `w ∈ C_{L*}(H)` such that
`⟨J₁^{yzw}, J₂⟩` is a `π`-group") の展開: Prop 1.5(b)
(`aInvariant_piSubgroup_le_aInvariant_hall`) で `J₁, J₂` をそれぞれ `A`-不変 Hall
`π`-部分群 `P₁, P₂` に入れ, Prop 1.5(c) (`aInvariant_hall_conj`) で `P₁^w = P₂`
(`w` は `A` に固定される = `C_G(A)` の元) とすれば `J₁^w ⊔ J₂ ≤ P₂` で `P₂` は `π`-群。 -/
theorem exists_centralizing_conj_sup_isPiGroup [Finite G] {A N : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G))
    (hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥N))
    [IsSolvable ↥N] {π : Set ℕ} {J₁ J₂ : Subgroup G}
    (hJ₁N : J₁ ≤ N) (hJ₁pi : Subgroup.IsPiSubgroup π J₁)
    (hJ₁A : A ≤ Subgroup.normalizer (J₁ : Set G))
    (hJ₂N : J₂ ≤ N) (hJ₂pi : Subgroup.IsPiSubgroup π J₂)
    (hJ₂A : A ≤ Subgroup.normalizer (J₂ : Set G)) :
    ∃ w : G, w ∈ N ∧ w ∈ Subgroup.centralizer (A : Set G) ∧
      Subgroup.IsPiSubgroup π ((MulAut.conj w • J₁) ⊔ J₂) := by
  classical
  letI act : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (N : Set G))) ↥N
      (Subgroup.inclusion hAN)
  set φ : ↥A →* MulAut ↥N := MulDistribMulAction.toMulAut ↥A ↥N with hφ
  have hφ_coe : ∀ (a : ↥A) (x : ↥N), ((φ a) x : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  -- `A`-invariance transports to `subgroupOf N`.
  have htr : ∀ K : Subgroup G, A ≤ Subgroup.normalizer (K : Set G) →
      Ch03.IsAInvariant φ (K.subgroupOf N) := by
    intro K hK
    rw [Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hφ_coe a x]
    exact (Subgroup.mem_normalizer_iff.mp (hK a.2) (x : G)).mp hx
  -- Prop 1.5(b) twice: invariant Hall `π`-overgroups of `J₁`, `J₂` inside `↥N`.
  obtain ⟨P₁, hP₁hall, hP₁inv, hJ₁P₁⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (G := ↥N) (A := ↥A) (φ := φ) hcop (isPiGroup_subgroupOf hJ₁N hJ₁pi) (htr J₁ hJ₁A)
  obtain ⟨P₂, hP₂hall, hP₂inv, hJ₂P₂⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (G := ↥N) (A := ↥A) (φ := φ) hcop (isPiGroup_subgroupOf hJ₂N hJ₂pi) (htr J₂ hJ₂A)
  -- Prop 1.5(c): an `A`-fixed conjugator `c ∈ ↥N` carrying `P₁` onto `P₂`.
  obtain ⟨c, hc_fix, hc_conj⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_hall_conj (G := ↥N) (A := ↥A) (φ := φ)
      hcop hP₁hall hP₂hall hP₁inv hP₂inv
  refine ⟨(c : G), c.2, ?_, ?_⟩
  · -- `c` is fixed by every `a ∈ A`, i.e. `c ∈ C_G(A)`.
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hval : ((φ ⟨a, ha⟩) c : G) = (c : G) :=
      congrArg (fun z : ↥N => (z : G)) (hc_fix ⟨a, ha⟩)
    rw [hφ_coe ⟨a, ha⟩ c] at hval
    exact mul_inv_eq_iff_eq_mul.mp hval
  · -- `J₁^c ⊔ J₂ ≤ P₂.map N.subtype`, which is a `π`-subgroup.
    have hP₂amb : Subgroup.IsPiSubgroup π (P₂.map N.subtype) :=
      isPiSubgroup_map_subtype hP₂hall.1
    refine isPiSubgroup_of_le (sup_le ?_ ?_) hP₂amb
    · -- the conjugate of `J₁`
      have hstep : (J₁.subgroupOf N).map (MulAut.conj c).toMonoidHom ≤ P₂ := by
        have h1 : (J₁.subgroupOf N).map (MulAut.conj c).toMonoidHom
            ≤ P₁.map (MulAut.conj c).toMonoidHom := Subgroup.map_mono hJ₁P₁
        have h2 : P₁.map (MulAut.conj c).toMonoidHom = P₂ :=
          (conj_smul_eq_map c P₁).symm.trans hc_conj
        rwa [h2] at h1
      calc MulAut.conj (c : G) • J₁
          = J₁.map (MulAut.conj (c : G)).toMonoidHom := conj_smul_eq_map _ _
        _ = ((J₁.subgroupOf N).map (MulAut.conj c).toMonoidHom).map N.subtype :=
            (map_subtype_conj_subgroupOf c J₁ hJ₁N).symm
        _ ≤ P₂.map N.subtype := Subgroup.map_mono hstep
    · -- `J₂` itself
      calc J₂ = (J₂.subgroupOf N).map N.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hJ₂N).symm
        _ ≤ P₂.map N.subtype := Subgroup.map_mono hJ₂P₂

/-! ## 場合 1 の中心化段 (原文 `H ∩ L = 1` の誤植訂正版) -/

/-- **BG Theorem 6.4, 場合 1 の `yz ∈ C_G(H)` 段** (p. 50; 原文の `H ∩ L = 1` を
`H ∩ N = 1` に訂正したもの — ファイル冒頭の注記参照)。

`N ⊴ G` と `H ⊓ N = ⊥` を仮定し, `t ∈ N_G(H)` が各 `h ∈ H` について
`h⁻¹ · h^t ∈ N` を満たすなら, `t` は `H` を中心化する。

証明: `h ∈ H` に対し `h^t ∈ H` (`t` は `H` を正規化する) ゆえ `h⁻¹ h^t ∈ H`, 仮定より
`h⁻¹ h^t ∈ N`, よって `h⁻¹ h^t ∈ H ⊓ N = ⊥`, すなわち `h^t = h`。

BG での適用: `t = yz`, `N ≤ O_p(F(G))`, `H` は `p'`-群なので `H ⊓ N = ⊥` (BG が
「`H` is a Hall `p'`-subgroup of `HN`」と述べる箇所), そして `h⁻¹ h^{yz} ∈ N` は
(6.3) の「`y` は `HN/N` を中心化する」と `z ∈ N`, `N ⊴ G` から従う。 -/
theorem mem_centralizer_of_mem_normalizer_of_commutator_le {N H : Subgroup G}
    (hdisj : H ⊓ N = ⊥) {t : G} (htH : t ∈ Subgroup.normalizer (H : Set G))
    (hcomm : ∀ h ∈ H, h⁻¹ * (t⁻¹ * h * t) ∈ N) :
    t ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hconjH : t⁻¹ * h * t ∈ H := (Subgroup.mem_normalizer_iff''.mp htH h).mp hh
  have hmemH : h⁻¹ * (t⁻¹ * h * t) ∈ H := H.mul_mem (H.inv_mem hh) hconjH
  have hbot : h⁻¹ * (t⁻¹ * h * t) ∈ (⊥ : Subgroup G) := by
    rw [← hdisj]; exact ⟨hmemH, hcomm h hh⟩
  rw [Subgroup.mem_bot, inv_mul_eq_one] at hbot
  -- `h = t⁻¹ * h * t` gives `h * t = t * h`.
  have h3 : t * h = h * t :=
    calc t * h = t * (t⁻¹ * h * t) := by rw [← hbot]
      _ = h * t := by group
  exact h3.symm

/-! ## Fitting 商の冪零性からの可解性 (Proposition 1.5 を呼ぶための前提) -/

/-- **Fitting 長 `≤ 2` の有限群は可解**: `X/F(X)` が冪零なら `X` は可解。

`F(X)` は冪零 (`Isaacs.Ch01.fitting.isNilpotent`) ゆえ可解, 仮定より `X/F(X)` も冪零ゆえ
可解, そして可解群による可解群の拡大は可解 (`solvable_of_ker_le_range` を
`F(X) ↪ X ↠ X/F(X)` に適用; `ker (mk' F(X)) = F(X) = range F(X).subtype`)。 -/
theorem isSolvable_of_isNilpotent_quotient_fitting {X : Type*} [Group X] [Finite X]
    (h : Group.IsNilpotent (X ⧸ Ch01.fitting X)) : IsSolvable X := by
  haveI := h
  haveI : Group.IsNilpotent ↥(Ch01.fitting X) := Ch01.fitting.isNilpotent
  refine solvable_of_ker_le_range (Ch01.fitting X).subtype
    (QuotientGroup.mk' (Ch01.fitting X)) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

/-- **BG Theorem 6.4 の可解性の段**: `N ⊴ X` について `N/F(N)` と `(X/N)/F(X/N)` が
ともに冪零なら `X` は可解。

Theorem 6.4 の仮説はまさに `N = G₀` に対するこの形 (`G₀` は `G` の正規 Hall 部分群で
`G₀/F(G₀)` と `(G/G₀)/F(G/G₀)` が冪零) なので, 本補題が場合 1 のエンジンである
Proposition 1.5 (`exists_centralizing_conj_sup_isPiGroup` の `[IsSolvable ↥N]` 仮説) を
使えるようにする。

証明: `isSolvable_of_isNilpotent_quotient_fitting` を `↥N` と `X ⧸ N` に適用して
`IsSolvable ↥N`, `IsSolvable (X ⧸ N)` を得, 再び `solvable_of_ker_le_range` を
`N ↪ X ↠ X/N` に適用する。Hall 性はここでは不要。 -/
theorem isSolvable_of_isNilpotent_quotient_fitting_of_normal {X : Type*} [Group X] [Finite X]
    (N : Subgroup X) [N.Normal]
    (hN : Group.IsNilpotent (↥N ⧸ Ch01.fitting ↥N))
    (hQ : Group.IsNilpotent ((X ⧸ N) ⧸ Ch01.fitting (X ⧸ N))) :
    IsSolvable X := by
  haveI : IsSolvable ↥N := isSolvable_of_isNilpotent_quotient_fitting hN
  haveI : IsSolvable (X ⧸ N) := isSolvable_of_isNilpotent_quotient_fitting hQ
  refine solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

end OddOrder.BG.Ch1.S06

