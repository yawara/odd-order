/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.Problems9D
import OddOrder.Isaacs.Ch02_Subnormality.Basic

/-!
# Isaacs, Finite Group Theory — Problem 9D.4: Kegel 予想の極小反例 (p. 294)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 9D.4 (書籍 p. 294):

> Lemma 9.31 の逆 (**Kegel 予想**; Kleidman が単純群の分類を用いて証明) の極小反例
> `(G, S)` (`|S| + |G|` が最小) では, `G` と `S` はどちらも非可換単純である.

本 leaf は極小反例の述語 `IsKegelMinimalCounterexample` と, その骨格
(skeleton step 1–4) を扱う. 3 つの降下補題 (`KegelHypothesis.subgroupOf` /
`KegelHypothesis.map_mk` / `KegelHypothesis.infNormal`) は `Problems9D.lean` にある.

## 極小性の持ち方

降下先 (`↥K` と `G ⧸ N`) は `G` と同じ universe に住むので, **同 universe 内の全群**に
ついての極小性で足りる (`IsKegelMinimalCounterexample` の第 3 成分).

## Main results

* `IsKegelMinimalCounterexample.ne_bot` / `.ne_top` — skeleton 1.
* `IsKegelMinimalCounterexample.sup_eq_top` — skeleton 2: 非自明な正規部分群 `N` は
  `S` と合わせて `G` 全体を生成する (`SN = G`).
-/

set_option autoImplicit false

namespace OddOrder.Isaacs.Ch09

universe u

variable {G : Type u} [Group G] [Finite G]

section /- 9D.4: 極小反例 (p. 294) -/

/-! ## 位数の減少 -/

/-- 真部分群の位数は真に小さい. -/
theorem card_lt_card_of_ne_top {H : Subgroup G} (h : H ≠ ⊤) : Nat.card ↥H < Nat.card G := by
  have hmul := Subgroup.card_mul_index H
  have hidx : 1 < H.index := Subgroup.one_lt_index_of_ne_top h
  have hpos : 0 < Nat.card ↥H := Nat.card_pos
  nlinarith [hmul, hidx, hpos]

/-- 非自明な正規部分群による商の位数は真に小さい. -/
theorem card_quotient_lt_card {N : Subgroup G} [N.Normal] (h : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  have hmul := Subgroup.card_mul_index N
  haveI : Nontrivial ↥N := N.nontrivial_iff_ne_bot.mpr h
  have hcard : 1 < Nat.card ↥N := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hpos : 0 < N.index := Nat.card_pos
  have : N.index = Nat.card (G ⧸ N) := rfl
  nlinarith [hmul, hcard, hpos]

/-! ## 極小反例 -/

/-- **Kegel 予想の極小反例** (Isaacs Problem 9D.4, p. 294).

`S ≤ G` は Kegel の仮説 (`KegelHypothesis`) をみたすが `G` に subnormal でなく,
`|T| + |H| < |S| + |G|` なるどの対 `(H, T)` では Kegel の仮説から subnormality が従う.

降下先 (`↥K` と `G ⧸ N`) は `G` と同じ universe に住むので, 同 universe 内の全群に
ついての極小性で足りる. -/
def IsKegelMinimalCounterexample (S : Subgroup G) : Prop :=
  KegelHypothesis S ∧ ¬ S.IsSubnormal ∧
    ∀ {H : Type u} [Group H] [Finite H] (T : Subgroup H),
      Nat.card ↥T + Nat.card H < Nat.card ↥S + Nat.card G → KegelHypothesis T → T.IsSubnormal

/-! ## subnormal 鎖の最後から 2 番目 -/

omit [Finite G] in
/-- **`T ◁◁ N`, `T ≠ N` なら `N`-不変な真部分群 `M` に `T` が収まる.**

subnormal 鎖 `T ◁ ⋯ ◁ N` の最後から 2 番目を取るだけ
(`Subgroup.IsSubnormal.exists_normal_and_le_and_lt_top_of_ne` を `↥N` で使う). -/
theorem exists_lt_of_isSubnormal_subgroupOf {N T : Subgroup G} (hTN : T ≤ N)
    (hsub : (T.subgroupOf N).IsSubnormal) (hne : T ≠ N) :
    ∃ M : Subgroup G, T ≤ M ∧ M < N ∧ ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M := by
  have hmapTop : (⊤ : Subgroup ↥N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hnetop : T.subgroupOf N ≠ ⊤ := by
    intro hc
    refine hne ?_
    have := congrArg (fun X : Subgroup ↥N => X.map N.subtype) hc
    rwa [Subgroup.map_subgroupOf_eq_of_le hTN, hmapTop] at this
  obtain ⟨K, hKnorm, hTK, hKlt⟩ := hsub.exists_normal_and_le_and_lt_top_of_ne hnetop
  refine ⟨K.map N.subtype, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hTN]
    exact Subgroup.map_mono hTK
  · refine lt_of_le_of_ne (Subgroup.map_subtype_le K) ?_
    intro hc
    exact hKlt.ne (Subgroup.map_injective N.subtype_injective (hc.trans hmapTop.symm))
  · rintro n hn m ⟨k, hk, rfl⟩
    exact ⟨⟨n, hn⟩ * k * ⟨n, hn⟩⁻¹, hKnorm.conj_mem k hk ⟨n, hn⟩, rfl⟩

namespace IsKegelMinimalCounterexample

variable {S : Subgroup G} (hmc : IsKegelMinimalCounterexample S)

include hmc

omit [Finite G] in
theorem kegel : KegelHypothesis S := hmc.1

omit [Finite G] in
theorem not_isSubnormal : ¬ S.IsSubnormal := hmc.2.1

omit [Finite G] in
/-- **skeleton 1**: `S ≠ ⊥` (`⊥` は subnormal). -/
theorem ne_bot : S ≠ ⊥ := fun h => hmc.2.1 (h ▸ Subgroup.IsSubnormal.bot)

omit [Finite G] in
/-- **skeleton 1**: `S ≠ ⊤` (`⊤` は subnormal). -/
theorem ne_top : S ≠ ⊤ := fun h => hmc.2.1 (h ▸ Subgroup.IsSubnormal.top)

/-- **skeleton 2**: 非自明な正規部分群 `N` について `SN = G`.

`S ⊔ N < G` と仮定すると, (F1) と極小性から `S ◁◁ SN`, (F2) と極小性から
`SN/N ◁◁ G/N` すなわち (対応定理 = `IsSubnormal.comap` + `Subgroup.comap_map_eq`)
`SN ◁◁ G`. 推移性 (`IsSubnormal.trans`) で `S ◁◁ G` となり反例であることに矛盾. -/
theorem sup_eq_top {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) : S ⊔ N = ⊤ := by
  by_contra hne
  -- (F1) `S ◁◁ SN`
  have hcardS : Nat.card ↥(S.subgroupOf (S ⊔ N)) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : S ≤ S ⊔ N)).toEquiv
  have hcardSN : Nat.card ↥(S ⊔ N) < Nat.card G := card_lt_card_of_ne_top hne
  have h1 : (S.subgroupOf (S ⊔ N)).IsSubnormal :=
    hmc.2.2 _ (by omega) (hmc.1.subgroupOf le_sup_left)
  -- (F2) `SN/N ◁◁ G/N`, ゆえに `SN ◁◁ G`
  have hcardQ : Nat.card (G ⧸ N) < Nat.card G := card_quotient_lt_card hN
  have hcardMap : Nat.card ↥(S.map (QuotientGroup.mk' N)) ≤ Nat.card ↥S :=
    Nat.card_le_card_of_surjective _ ((QuotientGroup.mk' N).subgroupMap_surjective S)
  have h2 : (S.map (QuotientGroup.mk' N)).IsSubnormal :=
    hmc.2.2 _ (by omega) (hmc.1.map_mk N)
  have h3 : (S ⊔ N).IsSubnormal := by
    have hc := h2.comap (QuotientGroup.mk' N)
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hc
  exact hmc.2.1 (Subgroup.IsSubnormal.trans le_sup_left h1 h3)

/-- **skeleton 3**: `N ◁ G` が `N ≠ ⊤` なら `S ∩ N` は `N` に subnormal.

(F3) `KegelHypothesis.infNormal` と極小性 (`|S ⊓ N| + |N| < |S| + |G|`). -/
theorem inf_isSubnormal {N : Subgroup G} [N.Normal] (hN : N ≠ ⊤) :
    ((S ⊓ N).subgroupOf N).IsSubnormal := by
  have hcard1 : Nat.card ↥((S ⊓ N).subgroupOf N) = Nat.card ↥(S ⊓ N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : S ⊓ N ≤ N)).toEquiv
  have hcard2 : Nat.card ↥(S ⊓ N) ≤ Nat.card ↥S :=
    Nat.card_le_card_of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective _)
  have hcard3 : Nat.card ↥N < Nat.card G := card_lt_card_of_ne_top hN
  exact hmc.2.2 _ (by omega) (hmc.1.infNormal N)

/-- **skeleton 4**: `N` が極小正規で `N ≠ ⊤` なら `S ∩ N = 1`.

`(S∩N)^G` は `N` に含まれる `G`-正規部分群なので `N` の極小性から `⊥` か `N`.
`= N` は不可能: `S ∩ N = N` なら `N ≤ S` で `G = SN = S` が `S ≠ ⊤` に反し, そうでなければ
skeleton 3 の subnormal 鎖から `S ∩ N ≤ M < N` (`M` は `N`-不変) がとれて,
`G = NS` (skeleton 2) と `(S∩N)^s = S∩N` (`s ∈ S`) から `G`-共役はすべて `M` に入るので
`(S∩N)^G ≤ M < N`. -/
theorem inf_eq_bot {N : Subgroup G} (hN : Ch02.IsMinimalNormal N) (hNtop : N ≠ ⊤) : S ⊓ N = ⊥ := by
  haveI : N.Normal := hN.1
  have hRle : Subgroup.normalClosure ((S ⊓ N : Subgroup G) : Set G) ≤ N :=
    Subgroup.normalClosure_le_normal (fun x hx => hx.2)
  rcases hN.2.2 _ Subgroup.normalClosure_normal hRle with hbot | htop
  · exact le_bot_iff.mp (hbot ▸ Subgroup.le_normalClosure)
  exfalso
  -- `S ∩ N = N` なら `N ≤ S` で `G = SN = S`
  have hne : S ⊓ N ≠ N := by
    intro hc
    have hNS : N ≤ S := hc ▸ inf_le_left
    refine hmc.ne_top ?_
    have hsup := hmc.sup_eq_top (N := N) hN.2.1
    rwa [sup_eq_left.mpr hNS] at hsup
  obtain ⟨M, hTM, hMlt, hMnorm⟩ :=
    exists_lt_of_isSubnormal_subgroupOf inf_le_right (hmc.inf_isSubnormal hNtop) hne
  -- `G = NS` を使って `G`-共役を `M` に押し込む
  have hGtop : N ⊔ S = ⊤ := sup_comm S N ▸ hmc.sup_eq_top (N := N) hN.2.1
  have hRM : Subgroup.normalClosure ((S ⊓ N : Subgroup G) : Set G) ≤ M := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    rintro y hy
    rw [Group.mem_conjugatesOfSet_iff] at hy
    obtain ⟨x, hx, hconj⟩ := hy
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    have hg : g ∈ (↑(N ⊔ S) : Set G) := by rw [hGtop]; trivial
    rw [Subgroup.normal_mul N S] at hg
    obtain ⟨n, hn, t, ht, rfl⟩ := hg
    -- `(n t) x (n t)⁻¹ = n (t x t⁻¹) n⁻¹`, `t x t⁻¹ ∈ S ⊓ N ≤ M`
    have hxSN : x ∈ S ⊓ N := hx
    have hconjS : t * x * t⁻¹ ∈ S ⊓ N :=
      ⟨S.mul_mem (S.mul_mem ht hxSN.1) (S.inv_mem ht), ‹N.Normal›.conj_mem x hxSN.2 t⟩
    have := hMnorm n hn _ (hTM hconjS)
    have hrw : n * t * x * (n * t)⁻¹ = n * (t * x * t⁻¹) * n⁻¹ := by group
    rw [hrw]
    exact this
  rw [htop] at hRM
  exact absurd hRM hMlt.not_ge

end IsKegelMinimalCounterexample

/-! ## `G = S ⋉ N` の retraction と `N`-共役で不変な Sylow 交わり -/

section Retraction

variable {N S : Subgroup G} [N.Normal]

/-- `S ⊓ N = ⊥` かつ `S ⊔ N = ⊤` のとき, 合成 `↥S ↪ G ↠ G ⧸ N` は同型. -/
noncomputable def splitEquivQuotient (hinf : S ⊓ N = ⊥) (hsup : S ⊔ N = ⊤) : ↥S ≃* G ⧸ N := by
  refine MulEquiv.ofBijective ((QuotientGroup.mk' N).comp S.subtype) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : G) ∈ N := by simpa [QuotientGroup.eq_one_iff] using hx
    have hmem : (x : G) ∈ S ⊓ N := ⟨x.2, hxN⟩
    rw [hinf] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  · intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hg : g ∈ (↑(S ⊔ N) : Set G) := by rw [hsup]; trivial
    rw [Subgroup.mul_normal] at hg
    obtain ⟨t, ht, n, hn, rfl⟩ := hg
    refine ⟨⟨t, ht⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq.mpr (by simpa using hn)

/-- **`G = S ⋉ N` の retraction** `G →* ↥S` (`N` を潰して `G ⧸ N ≅ ↥S` を戻す). -/
noncomputable def splitRetraction (hinf : S ⊓ N = ⊥) (hsup : S ⊔ N = ⊤) : G →* ↥S :=
  (splitEquivQuotient hinf hsup).symm.toMonoidHom.comp (QuotientGroup.mk' N)

omit [Finite G] in
@[simp]
theorem splitRetraction_coe (hinf : S ⊓ N = ⊥) (hsup : S ⊔ N = ⊤) (x : ↥S) :
    splitRetraction hinf hsup (x : G) = x :=
  (splitEquivQuotient hinf hsup).symm_apply_apply x

omit [Finite G] in
theorem splitRetraction_eq_one (hinf : S ⊓ N = ⊥) (hsup : S ⊔ N = ⊤) {n : G} (hn : n ∈ N) :
    splitRetraction hinf hsup n = 1 := by
  simp [splitRetraction, hn]

omit [Finite G] in
/-- Sylow の共役への所属は共役を戻した所属. -/
theorem mem_smul_sylow_iff {p : ℕ} [Fact p.Prime] {P : Sylow p G} {g x : G} :
    x ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  simp [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]

omit [Finite G] in
/-- Kegel の仮説のもとで, Sylow `P` と `S` の交わりは retraction による `P` の像に一致する.

`P ∩ S ≤ π(P)` は `π` が `S` 上恒等だから; 逆は `P ∩ S` が `↥S` の Sylow (Kegel) で
`π(P)` が `p`-群だから極大性. -/
theorem sylowInf_subgroupOf_eq_map (hK : KegelHypothesis S) (hinf : S ⊓ N = ⊥)
    (hsup : S ⊔ N = ⊤) {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    ((P : Subgroup G) ⊓ S).subgroupOf S = (P : Subgroup G).map (splitRetraction hinf hsup) := by
  have hpg : IsPGroup p ↥(((P : Subgroup G) ⊓ S).subgroupOf S) :=
    (P.isPGroup'.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective _)).comap_subtype
  have hidx : ¬ p ∣ (((P : Subgroup G) ⊓ S).subgroupOf S).index := by
    have := hK p ‹Fact p.Prime› P
    rwa [Subgroup.relIndex] at this
  have hle : ((P : Subgroup G) ⊓ S).subgroupOf S
      ≤ (P : Subgroup G).map (splitRetraction hinf hsup) := by
    intro x hx
    exact ⟨(x : G), hx.1, splitRetraction_coe hinf hsup x⟩
  have hmax := (hpg.toSylow hidx).3 (P.isPGroup'.map (splitRetraction hinf hsup)) hle
  rw [IsPGroup.toSylow_coe] at hmax
  exact hmax.symm

omit [Finite G] in
/-- **`P ∩ S` は `N`-共役で変わらない**: `π` が `N` を潰すので `π(P^n) = π(P)`. -/
theorem inf_smul_eq_inf (hK : KegelHypothesis S) (hinf : S ⊓ N = ⊥) (hsup : S ⊔ N = ⊤)
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {n : G} (hn : n ∈ N) :
    ((n • P : Sylow p G) : Subgroup G) ⊓ S = (P : Subgroup G) ⊓ S := by
  have hmap : ((n • P : Sylow p G) : Subgroup G).map (splitRetraction hinf hsup)
      = (P : Subgroup G).map (splitRetraction hinf hsup) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, mem_smul_sylow_iff] at hx
      refine ⟨n⁻¹ * x * n, hx, ?_⟩
      rw [map_mul, map_mul, map_inv, splitRetraction_eq_one hinf hsup hn]
      group
    · rintro ⟨x, hx, rfl⟩
      refine ⟨n * x * n⁻¹, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_smul_sylow_iff]
        have hgr : n⁻¹ * (n * x * n⁻¹) * n = x := by group
        rw [hgr]
        exact hx
      · rw [map_mul, map_mul, map_inv, splitRetraction_eq_one hinf hsup hn]
        group
  have h1 := sylowInf_subgroupOf_eq_map hK hinf hsup (n • P)
  have h2 := sylowInf_subgroupOf_eq_map hK hinf hsup P
  have heq : (((n • P : Sylow p G) : Subgroup G) ⊓ S).subgroupOf S
      = ((P : Subgroup G) ⊓ S).subgroupOf S := by rw [h1, h2, hmap]
  have := congrArg (fun X : Subgroup ↥S => X.map S.subtype) heq
  rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right,
    Subgroup.map_subgroupOf_eq_of_le inf_le_right] at this

omit [Finite G] in
/-- **`P ∩ S ≤ P^n` (`n ∈ N`)** — `(I)` step 3. -/
theorem inf_le_smul (hK : KegelHypothesis S) (hinf : S ⊓ N = ⊥) (hsup : S ⊔ N = ⊤)
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {n : G} (hn : n ∈ N) :
    (P : Subgroup G) ⊓ S ≤ ((n • P : Sylow p G) : Subgroup G) :=
  (inf_smul_eq_inf hK hinf hsup P hn) ▸ inf_le_left

omit [Finite G] in
/-- **`(I)` step 4**: `R := ⟨(P ∩ S)^N⟩` は `P` に含まれる (したがって `p`-群) で,
`N` に正規化される. -/
theorem exists_pgroup_normalizedBy (hK : KegelHypothesis S) (hinf : S ⊓ N = ⊥)
    (hsup : S ⊔ N = ⊤) {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    ∃ R : Subgroup G, (P : Subgroup G) ⊓ S ≤ R ∧ R ≤ (P : Subgroup G) ∧
      ∀ n ∈ N, ∀ r ∈ R, n * r * n⁻¹ ∈ R := by
  classical
  set X : Set G := {x : G | ∃ n ∈ N, ∃ y ∈ (P : Subgroup G) ⊓ S, x = n * y * n⁻¹} with hX
  refine ⟨Subgroup.closure X, ?_, ?_, ?_⟩
  · intro y hy
    exact Subgroup.subset_closure ⟨1, N.one_mem, y, hy, by group⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨n, hn, y, hy, rfl⟩
    have h1 : y ∈ ((n⁻¹ • P : Sylow p G) : Subgroup G) :=
      inf_le_smul hK hinf hsup P (N.inv_mem hn) hy
    rw [mem_smul_sylow_iff] at h1
    have h2 : n * y * n⁻¹ ∈ (P : Subgroup G) := by
      have hgr : (n⁻¹)⁻¹ * y * n⁻¹ = n * y * n⁻¹ := by group
      rwa [hgr] at h1
    exact h2
  · intro n hn
    have hsub : Subgroup.closure X ≤ (Subgroup.closure X).comap (MulAut.conj n).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro x ⟨m, hm, y, hy, rfl⟩
      refine Subgroup.subset_closure ⟨n * m, N.mul_mem hn hm, y, hy, ?_⟩
      change n * (m * y * m⁻¹) * n⁻¹ = n * m * y * (n * m)⁻¹
      group
    exact fun r hr => hsub hr

end Retraction

end -- 9D.4

end OddOrder.Isaacs.Ch09
