/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S06_Thm64
import OddOrder.BG.Ch1_Preliminary.OperatorQuotientAction

/-!
# BG §6: Theorem 6.4 — 場合 2 (`π(F(G)) ⊆ π(H)`) と定理本体

Bender–Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
Chapter I §6 (p. 50), mmd `references/bg/local-analysis.mmd` L2036–L2046。

`OddOrder.BG.Ch1_Preliminary.S06_Thm64` が主張 (`Thm64Statement`)・帰納骨格
(`thm64_of_ih`)・reduction (`thm64_of_sup_ne_top`)・**場合 1**
(`thm64_case_fitting_primes_not_subset`) を提供する。本ファイルは残る**場合 2**を証明し,
三分岐 dispatch (`thm64_step`) を経て **Theorem 6.4 本体**
(`exists_centralizing_conj_sup_isPiGroup_of_normalHall`) を無条件形で得る。

## 場合 2 (`π(F(G)) ⊆ π(H)`) の段どり

原文 (mmd L2036–L2046):

> Now assume that `π(F(G)) ⊆ π(H)`. Then (6.4) `O_π(G) = 1` and `π(F(M)) ⊆ π(H)`.
> By (6.1), `M` is a nonidentity normal Hall subgroup of `G`. Therefore `M` contains a
> Hall `π(F(M))`-subgroup of `H` that is not trivial. Let `B = H ∩ M` and let `H*` be a
> complement of `B` in `H`. Then `B ≠ 1` and `|H*| < |H|`. By induction, there exists an
> element `y ∈ L` such that `⟨J₁ʸ, J₂⟩` is a `π`-group and `y` centralizes `H*`.
> Let `K₁ = [J₁, B]` and `F = F(M)`. … `K₁ ⊆ F` … `K₁ ⊆ O_π(F) ⊆ O_π(G) = 1`.
> Thus `B` centralizes `J₁`. By symmetry, `B` centralizes `J₂`. Hence `B` centralizes `L`
> and `y`. Finally, since `y` centralizes `H*` and `H = H*B`, we see that `y` centralizes `H`.

対応する Lean の部品:

* `exists_normalHall_isNilpotent_quotient_fitting` — **(6.1)**。`G₀ ≠ 1` なら `M := G₀`,
  さもなくば `M := ⊤`。どちらの場合も `M` は非自明な正規 Hall 部分群で `M/F(M)` は冪零。
  場合 1 はこの分岐を一度も使っていないので, 本ファイルが (6.1) の最初の消費者。
* `inf_ne_bot_of_prime_dvd_card` — 「`M` は自明でない `H` の Hall 部分群を含む」段:
  `M` が正規 Hall で素数 `q` が `|M|` と `|H|` の両方を割るなら `M ⊓ H ≠ 1`。
* `inf_le_centralizer_of_isPiSubgroup` — `[J, B] = 1` すなわち **`B` は `J` を中心化する**段。
  `⁅J, B⁆` は coprime 作用ゆえ自己再生 (`⁅⁅J,B⁆,B⁆ = ⁅J,B⁆`) し, 冪零商 `M/F(M)` の中では
  自己再生する部分群は下降中心列のすべての項に入って消える。よって `⁅J,B⁆ ≤ F(M) ≤ F(G)`
  で, これは `π`-群かつ (場合 2 の仮定より) `π'`-群なので自明。
* `eq_bot_of_commutator_eq_self` — その下降中心列の議論。
* `mem_centralizer_sup` — 「`B` は `L = ⟨J₁,J₂⟩` を中心化する」「`H = H*B` を中心化する」段。

**原文からの逸脱 1 点** (弱化ではない): 原文は `O_π(G) = 1` を経由するが, 実際に要るのは
「`F(G)` が `π'`-群」だけである (`π(F(G)) ⊆ π(H) ⊆ π'`)。`K₁ ≤ F(M) ≤ F(G)` は
`Ch01.fitting_map_subtype_le_fitting` (`M ⊴ G ⟹ F(M) ≤ F(G)`) で直接得られるので,
`O_π(F)` と `O_π(G)` の比較は不要。同じ理由で `π(F(M)) ⊆ π(H)` も独立には要らない
(`B ≠ 1` の段でのみ `F(M) ≤ F(G)` 経由で使う)。

また場合 2 は **`G = LH` を使わない** (帰納法は `G` を変えず `H` を真部分群 `H*` に
取り替えて降下する) ので, `thm64_case_fitting_primes_subset` は `hsup` を仮定しない。

## Theorem 6.4 本体

* `thm64_step` — 帰納段の三分岐 dispatch。新しい数学は無い:
  `J₁ ⊔ J₂ ⊔ H ≠ ⊤` なら `thm64_of_sup_ne_top`, さもなくば `π(F(G)) ⊆ π(H)` で
  場合 2 / 場合 1 に振り分ける。
* `exists_centralizing_conj_sup_isPiGroup_of_normalHall` — **BG Theorem 6.4**, 無条件形。

⚠ 場合 1 で使う原文の `[H, yz] ⊆ H ∩ L = 1` は **誤植**で, 正しくは `H ∩ N = 1` である
(`S06_Thm64` の冒頭注記参照; PDF p. 50 の印字で確認済)。結論は不変。

## 重複の記録

`commutator_commutator_right_eq_of_le_normalizer` は
`OddOrder.BG.Ch3.S13.commutator_commutator_right_eq_of_le_normalizer` と同じ主張・同じ証明。
Ch.3 は Ch.1 の下流なので import できず, ここで再導出せざるを得ない。共通化するなら
`OddOrder/GroupTheory/` の leaf へ移すのが筋 (本ファイルの守備範囲外)。
-/

namespace OddOrder.BG.Ch1.S06

open Pointwise
open OddOrder.Isaacs

universe u

variable {G : Type*} [Group G]

/-! ## 冪零群における自己再生部分群の消滅 -/

/-- **冪零群で `⁅W, D⁆ = W` なら `W = ⊥`**。

下降中心列 `γ₀ = ⊤`, `γₙ₊₁ = ⁅γₙ, ⊤⁆` に沿って `W ≤ γₙ` を `n` について帰納する:
`W ≤ γₙ` なら `W = ⁅W, D⁆ ≤ ⁅γₙ, ⊤⁆ = γₙ₊₁`。冪零性より `γₙ = ⊥` となる `n` があるので
`W = ⊥`。

BG Theorem 6.4 の場合 2 で `M/F(M)` が冪零であることを使う段。そこでの `W` は
`⁅J₁, B⁆` の像で, coprime 作用の自己再生性 `⁅⁅J₁,B⁆,B⁆ = ⁅J₁,B⁆` (BG Prop 1.6(b)) が
仮定 `⁅W, D⁆ = W` を供給する。 -/
theorem eq_bot_of_commutator_eq_self {Q : Type*} [Group Q] [hQ : Group.IsNilpotent Q]
    {W D : Subgroup Q} (h : ⁅W, D⁆ = W) : W = ⊥ := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hQ
  have key : ∀ m : ℕ, W ≤ (⊤ : Subgroup Q).lowerCentralSeries m := by
    intro m
    induction m with
    | zero => exact le_top
    | succ k ih =>
        calc W = ⁅W, D⁆ := h.symm
          _ ≤ ⁅(⊤ : Subgroup Q).lowerCentralSeries k, (⊤ : Subgroup Q)⁆ :=
              Subgroup.commutator_mono ih le_top
          _ = (⊤ : Subgroup Q).lowerCentralSeries (k + 1) :=
              (Subgroup.lowerCentralSeries_succ _ k).symm
  exact le_bot_iff.mp (hn ▸ key n)

/-- **BG Proposition 1.6(b), `D` が正規でない版**: `Q` が `D` を正規化し `|D|`, `|Q|` が
互いに素で周囲が可解なら `⁅⁅D, Q⁆, Q⁆ = ⁅D, Q⁆`。

`D` は `D ⊔ Q` の中では正規なので, そこで
`OperatorQuotientAction.commutator_commutator_right_eq` を使い `D ⊔ Q ↪ G` で押し戻す。

⚠ `OddOrder.BG.Ch3.S13.commutator_commutator_right_eq_of_le_normalizer` と同内容。
Ch.3 は本ファイルの下流ゆえ import できず再導出している (共通化先は `GroupTheory/`)。 -/
theorem commutator_commutator_right_eq_of_le_normalizer [Finite G] [IsSolvable G]
    {D Q : Subgroup G} (hQD : Q ≤ Subgroup.normalizer (D : Set G))
    (hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q)) :
    ⁅⁅D, Q⁆, Q⁆ = ⁅D, Q⁆ := by
  have hD_le : D ≤ D ⊔ Q := le_sup_left
  have hQ_le : Q ≤ D ⊔ Q := le_sup_right
  have hDQnorm : (D ⊔ Q : Subgroup G) ≤ Subgroup.normalizer (D : Set G) :=
    sup_le Subgroup.le_normalizer hQD
  haveI : (D.subgroupOf (D ⊔ Q)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDQnorm
  have hcop' : Nat.Coprime (Nat.card ↥(D.subgroupOf (D ⊔ Q)))
      (Nat.card ↥(Q.subgroupOf (D ⊔ Q))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv]
    exact hcop
  have h2 := OddOrder.BG.Ch1.OperatorQuotientAction.commutator_commutator_right_eq
    (D.subgroupOf (D ⊔ Q)) (Q.subgroupOf (D ⊔ Q)) hcop'
  have hDmap : (D.subgroupOf (D ⊔ Q)).map (D ⊔ Q).subtype = D := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hD_le]
  have hQmap : (Q.subgroupOf (D ⊔ Q)).map (D ⊔ Q).subtype = Q := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQ_le]
  have h3 := congrArg (Subgroup.map (D ⊔ Q).subtype) h2
  simp only [Subgroup.map_commutator] at h3
  rw [hDmap, hQmap] at h3
  exact h3

/-! ## 中心化の join への持ち上げ -/

/-- 二つの部分群を中心化する元は, その join も中心化する。

`Subgroup.centralizer` は集合を引数に取るので `⊔` との相互作用は自動では出ない。
`y` を中心化する元の集合 `C_G({y})` が部分群であることを使い, `S₁, S₂ ≤ C_G({y})` から
`S₁ ⊔ S₂ ≤ C_G({y})` を得る。

BG Theorem 6.4 の場合 2 で二度使う: 「`B` は `J₁` と `J₂` を中心化するので
`L = ⟨J₁, J₂⟩` を中心化する」と「`y` は `H*` と `B` を中心化するので `H = H*B` を
中心化する」。 -/
theorem mem_centralizer_sup {S₁ S₂ : Subgroup G} {y : G}
    (h₁ : y ∈ Subgroup.centralizer (S₁ : Set G))
    (h₂ : y ∈ Subgroup.centralizer (S₂ : Set G)) :
    y ∈ Subgroup.centralizer ((S₁ ⊔ S₂ : Subgroup G) : Set G) := by
  have hle : (S₁ ⊔ S₂ : Subgroup G) ≤ Subgroup.centralizer ({y} : Set G) := by
    refine sup_le (fun s hs => ?_) (fun s hs => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      rintro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (Subgroup.mem_centralizer_iff.mp h₁ s hs).symm
    · rw [Subgroup.mem_centralizer_iff]
      rintro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (Subgroup.mem_centralizer_iff.mp h₂ s hs).symm
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (Subgroup.mem_centralizer_iff.mp (hle hh) y rfl).symm

/-! ## BG (6.1): 非自明な正規 Hall 部分群 `M` で `M/F(M)` 冪零 -/

/-- **BG Theorem 6.4 (6.1)** (p. 50):

> Let `M = G₀` if `G₀ ≠ 1` and `M = G` otherwise. … `M` is a nonidentity normal Hall
> subgroup of `G` and `M/F(M)` is nilpotent.

`G₀ ≠ 1` の場合は `M := G₀` がそのまま仮説を満たす。`G₀ = 1` の場合は `M := ⊤` で,
Hall 性は `[G : G] = 1` から自明, 冪零性は仮説 `(G/G₀)/F(G/G₀)` 冪零を同型
`G ⧸ ⊥ ≃* G ≃* ↥⊤` で運ぶ。非自明性は `G ≠ 1` から。

場合 1 (`thm64_case_fitting_primes_not_subset`) はこの分岐を一度も使わないので,
場合 2 が (6.1) の最初の消費者である。 -/
theorem exists_normalHall_isNilpotent_quotient_fitting {X : Type*} [Group X] [Finite X]
    [Nontrivial X] (G₀ : Subgroup X) [G₀.Normal]
    (hG₀hall : Nat.Coprime (Nat.card ↥G₀) G₀.index)
    (hG₀nil : Group.IsNilpotent (↥G₀ ⧸ Ch01.fitting ↥G₀))
    (hQnil : Group.IsNilpotent ((X ⧸ G₀) ⧸ Ch01.fitting (X ⧸ G₀))) :
    ∃ M : Subgroup X, M.Normal ∧ M ≠ ⊥ ∧ Nat.Coprime (Nat.card ↥M) M.index ∧
      Group.IsNilpotent (↥M ⧸ Ch01.fitting ↥M) := by
  by_cases hbot : G₀ = ⊥
  · subst hbot
    refine ⟨⊤, inferInstance, ?_, ?_, ?_⟩
    · intro htop
      obtain ⟨x, hx⟩ := exists_ne (1 : X)
      exact hx (Subgroup.mem_bot.mp (htop ▸ Subgroup.mem_top x))
    · rw [Subgroup.index_top]
      exact Nat.coprime_one_right _
    · have e : (X ⧸ (⊥ : Subgroup X)) ≃* ↥(⊤ : Subgroup X) :=
        QuotientGroup.quotientBot.trans Subgroup.topEquiv.symm
      exact OddOrder.GroupTheory.isNilpotent_quotient_fitting_of_surjective
        e.toMonoidHom e.surjective hQnil
  · exact ⟨G₀, inferInstance, hbot, hG₀hall, hG₀nil⟩

/-! ## `B = H ⊓ M` の非自明性 -/

/-- **正規 Hall 部分群との交わりは素数を拾う**: `M` が `G` の正規 Hall 部分群で,
素数 `q` が `|M|` と `|H|` の両方を割るなら `M ⊓ H ≠ ⊥`。

BG Theorem 6.4 の場合 2 で「`M` contains a Hall `π(F(M))`-subgroup of `H` that is not
trivial」と述べる段。実質は `|H| = |M ⊓ H| · [H : M ⊓ H]` と `[H : M ⊓ H] ∣ [G : M]`
(`Subgroup.relIndex_dvd_index_of_normal`) から, `q ∣ |M|` と `(|M|, [G:M]) = 1` で
`q ∤ [H : M ⊓ H]` となり `q ∣ |M ⊓ H|`。 -/
theorem inf_ne_bot_of_prime_dvd_card [Finite G] {M H : Subgroup G} [M.Normal]
    (hMhall : Nat.Coprime (Nat.card ↥M) M.index) {q : ℕ} (hq : q.Prime)
    (hqM : q ∣ Nat.card ↥M) (hqH : q ∣ Nat.card ↥H) : M ⊓ H ≠ ⊥ := by
  have hqidx : ¬ q ∣ M.index := by
    intro hdvd
    have h1 : q ∣ 1 := hMhall ▸ Nat.dvd_gcd hqM hdvd
    exact hq.one_lt.ne' (Nat.dvd_one.mp h1)
  have hidx : (M.subgroupOf H).index ∣ M.index := Subgroup.relIndex_dvd_index_of_normal M H
  have hcard : Nat.card ↥(M.subgroupOf H) * (M.subgroupOf H).index = Nat.card ↥H :=
    Subgroup.card_mul_index _
  have hqB : q ∣ Nat.card ↥(M.subgroupOf H) := by
    rcases (Nat.Prime.dvd_mul hq).mp (hcard ▸ hqH) with h | h
    · exact h
    · exact absurd (h.trans hidx) hqidx
  have hiso : Nat.card ↥(M.subgroupOf H) = Nat.card ↥(M ⊓ H) :=
    calc Nat.card ↥(M.subgroupOf H)
        = Nat.card ↥((M ⊓ H).subgroupOf H) := by rw [Subgroup.inf_subgroupOf_right]
      _ = Nat.card ↥(M ⊓ H) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  intro hbot
  rw [hiso, hbot, Subgroup.card_bot] at hqB
  exact hq.one_lt.ne' (Nat.dvd_one.mp hqB)

/-! ## 場合 2 の核: `B = M ⊓ H` は `J` を中心化する -/

/-- **BG Theorem 6.4, 場合 2 の `[J, B] = 1` 段** (p. 50, mmd L2040–L2045):

> Let `K₁ = [J₁, B]` and `F = F(M)`. Since `K₁ ⊆ J₁`, `K₁` is a `π`-group. By (6.1),
> `M/F` is nilpotent. Since `B` is a `π'`-group, … `K₁ ⊆ F`. Since `F` is nilpotent,
> (6.4) yields `K₁ ⊆ O_π(F) ⊆ O_π(G) = 1`. Thus `B` centralizes `J₁`.

仮定は `M ⊴ G` で `M/F(M)` 冪零, `F(G)` が `π'`-部分群 (場合 2 の仮定
`π(F(G)) ⊆ π(H)` と `H` が `π'` から従う), `H` が `π'`-部分群で `J` を正規化,
`J` が `π'`-部分群。結論は `M ⊓ H ≤ C_G(J)`。

証明:

1. `W := ⁅J, B⁆` は `J` に含まれ (`B ≤ H ≤ N_G(J)`), かつ `M` に含まれる (`B ≤ M ⊴ G`)。
2. `|J|` と `|B|` は互いに素なので `⁅W, B⁆ = W` (BG Prop 1.6(b),
   `commutator_commutator_right_eq_of_le_normalizer`)。
3. その関係は `↥M` の中でも, さらに冪零商 `↥M ⧸ F(M)` の中でも成り立つので,
   `eq_bot_of_commutator_eq_self` で像は自明, すなわち `W ≤ F(M)`。
4. `F(M) ≤ F(G)` (`Ch01.fitting_map_subtype_le_fitting`, `M ⊴ G`) より `W ≤ F(G)` は
   `π'`-部分群。同時に `W ≤ J` は `π`-部分群なので `W = ⊥`。

⚠ 原文は 4 を `O_π(F) ⊆ O_π(G) = 1` と書くが, 使っているのは「`F(G)` が `π'`-群」
だけなので, ここでは `O_π` を経由せず直接示す (弱化ではなく短絡)。 -/
theorem inf_le_centralizer_of_isPiSubgroup {X : Type*} [Group X] [Finite X] [IsSolvable X]
    {π : Set ℕ} {M H J : Subgroup X} [M.Normal]
    (hMnil : Group.IsNilpotent (↥M ⧸ Ch01.fitting ↥M))
    (hFpi : Subgroup.IsPiSubgroup πᶜ (Ch01.fitting X))
    (hH : Subgroup.IsPiSubgroup πᶜ H) (hJ : Subgroup.IsPiSubgroup π J)
    (hJnorm : H ≤ Subgroup.normalizer (J : Set X)) :
    (M ⊓ H : Subgroup X) ≤ Subgroup.centralizer (J : Set X) := by
  haveI := hMnil
  have hBM : (M ⊓ H : Subgroup X) ≤ M := inf_le_left
  have hBH : (M ⊓ H : Subgroup X) ≤ H := inf_le_right
  have hBpi : Subgroup.IsPiSubgroup πᶜ (M ⊓ H : Subgroup X) := isPiSubgroup_of_le hBH hH
  have hBnorm : (M ⊓ H : Subgroup X) ≤ Subgroup.normalizer (J : Set X) := hBH.trans hJnorm
  -- 1. `W = ⁅J, B⁆ ≤ J ⊓ M`
  have hWJ : ⁅J, (M ⊓ H : Subgroup X)⁆ ≤ J :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hBnorm
  have hWM : ⁅J, (M ⊓ H : Subgroup X)⁆ ≤ M :=
    le_trans (Subgroup.commutator_mono le_rfl hBM) (Subgroup.commutator_le_right J M)
  -- 2. coprime 作用の自己再生性
  have hcop : Nat.Coprime (Nat.card ↥J) (Nat.card ↥(M ⊓ H : Subgroup X)) :=
    (coprime_card_of_isPiSubgroup_compl hBpi hJ).symm
  have hself : ⁅⁅J, (M ⊓ H : Subgroup X)⁆, (M ⊓ H : Subgroup X)⁆ = ⁅J, (M ⊓ H : Subgroup X)⁆ :=
    commutator_commutator_right_eq_of_le_normalizer hBnorm hcop
  -- 3. `↥M` へ落とし, 冪零商 `↥M ⧸ F(M)` で消す
  have hsub : ⁅⁅J, (M ⊓ H : Subgroup X)⁆.subgroupOf M, (M ⊓ H : Subgroup X).subgroupOf M⁆
      = ⁅J, (M ⊓ H : Subgroup X)⁆.subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    simp only [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype]
    rw [inf_eq_left.mpr hWM, inf_eq_left.mpr hBM]
    exact hself
  have hmapbot : (⁅J, (M ⊓ H : Subgroup X)⁆.subgroupOf M).map
      (QuotientGroup.mk' (Ch01.fitting ↥M)) = ⊥ := by
    refine eq_bot_of_commutator_eq_self
      (D := ((M ⊓ H : Subgroup X).subgroupOf M).map (QuotientGroup.mk' (Ch01.fitting ↥M))) ?_
    rw [← Subgroup.map_commutator, hsub]
  have hWfitM : ⁅J, (M ⊓ H : Subgroup X)⁆.subgroupOf M ≤ Ch01.fitting ↥M := by
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmapbot
  have hWfit : ⁅J, (M ⊓ H : Subgroup X)⁆ ≤ (Ch01.fitting ↥M).map M.subtype :=
    calc ⁅J, (M ⊓ H : Subgroup X)⁆
        = ⁅J, (M ⊓ H : Subgroup X)⁆ ⊓ M := (inf_eq_left.mpr hWM).symm
      _ = (⁅J, (M ⊓ H : Subgroup X)⁆.subgroupOf M).map M.subtype :=
          (Subgroup.subgroupOf_map_subtype _ M).symm
      _ ≤ (Ch01.fitting ↥M).map M.subtype := Subgroup.map_mono hWfitM
  -- 4. `π`-群 かつ `π'`-群 ゆえ自明
  have hWfitX : ⁅J, (M ⊓ H : Subgroup X)⁆ ≤ Ch01.fitting X :=
    hWfit.trans Ch01.fitting_map_subtype_le_fitting
  have hWbot : ⁅J, (M ⊓ H : Subgroup X)⁆ = ⊥ :=
    eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl (isPiSubgroup_of_le hWJ hJ)
      (isPiSubgroup_of_le hWfitX hFpi)
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.mp ?_
  rw [Subgroup.commutator_comm]
  exact hWbot

/-! ## BG Theorem 6.4 の場合 2 (`π(F(G)) ⊆ π(H)`) -/

/-- **BG Theorem 6.4, 場合 2** (p. 50, mmd L2036–L2046): `π(F(G)) ⊆ π(H)` のとき,
帰納法の仮定から Theorem 6.4 の結論が出る。

原文の段どりに沿った証明:

1. `G = 1` なら `x = 1` で終わり (原文の「We can assume that `G ≠ 1`」)。
2. 二つの Fitting 商仮説から `G` は可解 (`isSolvable_of_isNilpotent_quotient_fitting_of_normal`)。
3. **(6.1)** で非自明な正規 Hall 部分群 `M` (`M/F(M)` 冪零) を取る。
4. `F(M) ≠ 1` の素因子 `q` は `F(M) ≤ F(G)` と場合 2 の仮定より `π(H)` に属し,
   `M` が正規 Hall ゆえ `q ∣ |M ⊓ H|`。よって `B := M ⊓ H ≠ 1`
   (`inf_ne_bot_of_prime_dvd_card`)。
5. `B` は `H` の正規 Hall 部分群 (`NormalHallHeredity`) なので Schur–Zassenhaus で補群
   `H*` を持ち, `B ≠ 1` から `|H*| < |H|`。
6. 測度 `|G| + |H*| < |G| + |H|` で帰納法の仮定を使い, `y ∈ L` で `⟨J₁ʸ, J₂⟩` が `π`-群,
   `y ∈ C_G(H*)` を得る。
7. `B` は `J₁` と `J₂` を中心化する (`inf_le_centralizer_of_isPiSubgroup`) ので
   `L = ⟨J₁, J₂⟩` を中心化し, `y ∈ L` から `y ∈ C_G(B)`。
8. `H = B ⊔ H*` なので `y ∈ C_G(H)` (`mem_centralizer_sup`)。

⚠ 場合 1 と違い `G = LH` (`J₁ ⊔ J₂ ⊔ H = ⊤`) は**使わない**。帰納法は `G` を変えず
`H` だけを縮めるので, reduction を経由する必要がない。 -/
theorem thm64_case_fitting_primes_subset {X : Type u} [Group X] [Finite X] (π : Set ℕ)
    (H G₀ J₁ J₂ : Subgroup X) [G₀.Normal] (hIH : Thm64IH X H)
    (hsub : (Nat.card ↥(Ch01.fitting X)).primeFactors ⊆ (Nat.card ↥H).primeFactors) :
    Thm64Statement π H G₀ J₁ J₂ := by
  intro hH hG₀hall hG₀nil hQnil hJ₁pi hJ₂pi hJ₁norm hJ₂norm
  classical
  -- ## 1. `G = 1` の場合
  rcases subsingleton_or_nontrivial X with hXsub | hXnt
  · have hbotall : ∀ K : Subgroup X, K = ⊥ := by
      intro K
      ext x
      have hx1 : x = 1 := Subsingleton.elim x 1
      subst hx1
      simp
    refine ⟨1, Subgroup.one_mem _, ?_, Subgroup.one_mem _⟩
    rw [hbotall ((MulAut.conj (1 : X) • J₁) ⊔ J₂)]
    exact Subgroup.IsPiSubgroup.bot
  -- ## 2. `G` は可解
  haveI hXsolv : IsSolvable X :=
    isSolvable_of_isNilpotent_quotient_fitting_of_normal G₀ hG₀nil hQnil
  -- 場合 2 の仮定: `F(G)` は `π'`-部分群
  have hFpi : Subgroup.IsPiSubgroup πᶜ (Ch01.fitting X) := fun q hq => hH q (hsub hq)
  -- ## 3. (6.1)
  obtain ⟨M, hMnormal, hMne, hMhall, hMnil⟩ :=
    exists_normalHall_isNilpotent_quotient_fitting G₀ hG₀hall hG₀nil hQnil
  haveI : M.Normal := hMnormal
  haveI hMnt : Nontrivial ↥M := (M.bot_or_nontrivial).resolve_left hMne
  -- ## 4. `B = M ⊓ H ≠ ⊥`
  have hFMne : Ch01.fitting ↥M ≠ ⊥ := Ch01.fitting_ne_bot_of_solvable_nontrivial ↥M
  obtain ⟨q, hqprime, hqdvd⟩ :=
    Nat.exists_prime_and_dvd (n := Nat.card ↥(Ch01.fitting ↥M))
      (fun hc => hFMne (Subgroup.eq_bot_of_card_eq _ hc))
  have hqM : q ∣ Nat.card ↥M := hqdvd.trans (Subgroup.card_subgroup_dvd_card _)
  have hqFX : q ∣ Nat.card ↥(Ch01.fitting X) := by
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le
      (Ch01.fitting_map_subtype_le_fitting (M := M)))
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hqdvd
  have hqH : q ∣ Nat.card ↥H := by
    have hmem : q ∈ (Nat.card ↥(Ch01.fitting X)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqprime, hqFX, Nat.card_pos.ne'⟩
    exact (Nat.mem_primeFactors.mp (hsub hmem)).2.1
  have hBne : (M ⊓ H : Subgroup X) ≠ ⊥ :=
    inf_ne_bot_of_prime_dvd_card hMhall hqprime hqM hqH
  -- ## 5. Schur–Zassenhaus: `H*`
  haveI hBhnormal : (M.subgroupOf H).Normal :=
    (OddOrder.GroupTheory.normal_coprime_card_index_subgroupOf hMhall H).1
  have hBhhall : Nat.Coprime (Nat.card ↥(M.subgroupOf H)) (M.subgroupOf H).index :=
    (OddOrder.GroupTheory.normal_coprime_card_index_subgroupOf hMhall H).2
  obtain ⟨Kc, hKc⟩ := Subgroup.exists_right_complement'_of_coprime hBhhall
  have hHstarle : Kc.map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hBmap : (M.subgroupOf H).map H.subtype = M ⊓ H := Subgroup.subgroupOf_map_subtype M H
  have hsupH : (M ⊓ H : Subgroup X) ⊔ Kc.map H.subtype = H := by
    have h : ((M.subgroupOf H) ⊔ Kc).map H.subtype = (⊤ : Subgroup ↥H).map H.subtype :=
      congrArg (Subgroup.map H.subtype) hKc.sup_eq_top
    rw [Subgroup.map_sup, hBmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    exact h
  have hBhne : M.subgroupOf H ≠ ⊥ := by
    intro h
    exact hBne (by rw [← hBmap, h, Subgroup.map_bot])
  have hBhcard : Nat.card ↥(M.subgroupOf H) ≠ 1 := fun h =>
    hBhne (Subgroup.eq_bot_of_card_eq _ h)
  have hHstarlt : Nat.card ↥(Kc.map H.subtype) < Nat.card ↥H := by
    have hcardHstar : Nat.card ↥(Kc.map H.subtype) = Nat.card ↥Kc :=
      Subgroup.card_map_of_injective H.subtype_injective
    have hcardmul : Nat.card ↥(M.subgroupOf H) * Nat.card ↥Kc = Nat.card ↥H := hKc.card_mul
    have hBpos : 0 < Nat.card ↥(M.subgroupOf H) := Nat.card_pos
    have hKpos : 0 < Nat.card ↥Kc := Nat.card_pos
    have h2 : 2 ≤ Nat.card ↥(M.subgroupOf H) := by omega
    have hmul : 2 * Nat.card ↥Kc ≤ Nat.card ↥(M.subgroupOf H) * Nat.card ↥Kc :=
      Nat.mul_le_mul h2 (le_refl _)
    rw [hcardmul] at hmul
    omega
  -- ## 6. 帰納法の仮定を `(G, H*)` で使う
  obtain ⟨y, hyL, hypi, hyc⟩ :=
    hIH X (Kc.map H.subtype) (by omega) π G₀ J₁ J₂
      (isPiSubgroup_of_le hHstarle hH) hG₀hall hG₀nil hQnil hJ₁pi hJ₂pi
      (hHstarle.trans hJ₁norm) (hHstarle.trans hJ₂norm)
  -- ## 7. `B` は `L` を中心化し, したがって `y` を中心化する
  have hBJ₁ : (M ⊓ H : Subgroup X) ≤ Subgroup.centralizer (J₁ : Set X) :=
    inf_le_centralizer_of_isPiSubgroup hMnil hFpi hH hJ₁pi hJ₁norm
  have hBJ₂ : (M ⊓ H : Subgroup X) ≤ Subgroup.centralizer (J₂ : Set X) :=
    inf_le_centralizer_of_isPiSubgroup hMnil hFpi hH hJ₂pi hJ₂norm
  have hBL : (M ⊓ H : Subgroup X) ≤ Subgroup.centralizer ((J₁ ⊔ J₂ : Subgroup X) : Set X) :=
    fun b hb => mem_centralizer_sup (hBJ₁ hb) (hBJ₂ hb)
  have hyB : y ∈ Subgroup.centralizer ((M ⊓ H : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp (hBL hb) y hyL).symm
  -- ## 8. `H = B ⊔ H*` を中心化する
  refine ⟨y, hyL, hypi, ?_⟩
  have hyH := mem_centralizer_sup hyB hyc
  rwa [hsupH] at hyH

/-! ## Theorem 6.4 の帰納段と本体 -/

/-- **BG Theorem 6.4 の帰納段** (p. 50): 帰納法の仮定のもとで主張が成り立つ。

新しい数学は無く, 既に証明済みの三つの補題への **dispatch** だけである:

* `J₁ ⊔ J₂ ⊔ H ≠ ⊤` (= `G ≠ LH`) なら reduction `thm64_of_sup_ne_top`;
* `G = LH` かつ `π(F(G)) ⊆ π(H)` なら場合 2 `thm64_case_fitting_primes_subset`;
* `G = LH` かつ `π(F(G)) ⊄ π(H)` なら場合 1 `thm64_case_fitting_primes_not_subset`。

(場合 2 は `G = LH` を必要としないので, 実際にはこの三分岐のうち `hsup` を使うのは
場合 1 のみ。) -/
theorem thm64_step (X : Type u) [Group X] [Finite X] (H : Subgroup X) (hIH : Thm64IH X H)
    (π : Set ℕ) (G₀ : Subgroup X) [G₀.Normal] (J₁ J₂ : Subgroup X) :
    Thm64Statement π H G₀ J₁ J₂ := by
  classical
  by_cases hsup : J₁ ⊔ J₂ ⊔ H = ⊤
  · by_cases hsubset :
      (Nat.card ↥(Ch01.fitting X)).primeFactors ⊆ (Nat.card ↥H).primeFactors
    · exact thm64_case_fitting_primes_subset π H G₀ J₁ J₂ hIH hsubset
    · exact thm64_case_fitting_primes_not_subset π H G₀ J₁ J₂ hIH hsup hsubset
  · exact thm64_of_sup_ne_top π H G₀ J₁ J₂ hIH hsup

/-- **BG Theorem 6.4** (p. 50, mmd L2011):

> Suppose `G` is a group, `π` is a set of primes, `H` is a `π'`-subgroup of `G`, and `G₀`
> is a normal Hall subgroup of `G`. Assume that `G₀/F(G₀)` and `(G/G₀)/F(G/G₀)` are
> nilpotent. Assume further that `H` normalizes two `π`-subgroups `J₁` and `J₂` of `G`.
> Then there exists an element `x ∈ ⟨J₁, J₂⟩` such that `⟨J₁ˣ, J₂⟩` is a `π`-group and
> `x` centralizes `H`.

証明は `|G| + |H|` に関する強帰納法 (`thm64_of_ih` + `thm64_step`)。帰納段は
reduction「`G = LH` としてよい」(`thm64_of_sup_ne_top`) と, `π(F(G))` が `π(H)` に
含まれるか否かの二つの場合 (`thm64_case_fitting_primes_not_subset` /
`thm64_case_fitting_primes_subset`) からなる。

綴りについて:

* 「`G₀` が Hall 部分群」は `π` に依らない `Nat.Coprime |G₀| [G:G₀]` で書く
  (`OddOrder.GroupTheory.NormalHallHeredity` と同じ convention)。
* 共役は左作用 `MulAut.conj x • J₁ = x J₁ x⁻¹`。BG の `J₁ˣ = x⁻¹ J₁ x` とは
  `x ↦ x⁻¹` の違いだけで, `⟨J₁, J₂⟩` も `C_G(H)` も逆元で閉じているので主張は同値。

⚠ **原文の誤植**: 場合 1 の末尾で BG p. 50 は `[H, yz] ⊆ H ∩ L = 1` と書くが,
`H ∩ L = 1` は仮定から従わない (`G = LH` と `L ⊴ G` は `G/L ≅ H/(H ∩ L)` を与えるだけで,
`L = ⟨J₁,J₂⟩` が `π`-群であることは本定理の**結論**であって未知)。正しくは `L` ではなく
`N` で `[H, yz] ⊆ H ∩ N = 1` — これは BG 自身が直前に述べる「`H` is a Hall
`p'`-subgroup of `HN`」と同じ内容である。結論は不変で, 本形式化はこの訂正版
(`mem_centralizer_of_mem_normalizer_of_commutator_le`) を使っている。詳細は
`OddOrder.BG.Ch1_Preliminary.S06_Thm64` の冒頭注記を参照。 -/
theorem exists_centralizing_conj_sup_isPiGroup_of_normalHall {X : Type u} [Group X] [Finite X]
    (π : Set ℕ) (H G₀ J₁ J₂ : Subgroup X) [G₀.Normal]
    (hH : Subgroup.IsPiSubgroup πᶜ H)
    (hG₀hall : Nat.Coprime (Nat.card ↥G₀) G₀.index)
    (hG₀nil : Group.IsNilpotent (↥G₀ ⧸ Ch01.fitting ↥G₀))
    (hQnil : Group.IsNilpotent ((X ⧸ G₀) ⧸ Ch01.fitting (X ⧸ G₀)))
    (hJ₁pi : Subgroup.IsPiSubgroup π J₁) (hJ₂pi : Subgroup.IsPiSubgroup π J₂)
    (hJ₁norm : H ≤ Subgroup.normalizer (J₁ : Set X))
    (hJ₂norm : H ≤ Subgroup.normalizer (J₂ : Set X)) :
    ∃ x ∈ J₁ ⊔ J₂, Subgroup.IsPiSubgroup π ((MulAut.conj x • J₁) ⊔ J₂) ∧
      x ∈ Subgroup.centralizer (H : Set X) := by
  have h := thm64_of_ih thm64_step X π H G₀ J₁ J₂
  exact h hH hG₀hall hG₀nil hQnil hJ₁pi hJ₂pi hJ₁norm hJ₂norm

end OddOrder.BG.Ch1.S06
