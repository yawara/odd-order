/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.GlaubermanReplacement
import OddOrder.Isaacs.Ch09_MoreSubnormality.SylowSubnormal

/-!
# Glauberman の `Z(J)`-定理 (Gorenstein Thm 2.10 / 2.11)

Gorenstein, *Finite Groups* (1968), Ch.8 §2 の締め括り
(pdftotext L15282-15355; mmd は p.298 が MISSING):

* **Theorem 2.10** (Glauberman): `B` を `p`-stable な群 `G` の非自明正規 `p`-部分群,
  `p` odd, `P ∈ Syl_p(G)` とすると `B ∩ Z(J(P)) ⊴ G`.
* **Theorem 2.11** (Glauberman `Z(J)`-定理): `G` が `p`-constrained かつ `p`-stable,
  `O_p(G) ≠ 1`, `p` odd なら `G = O_{p'}(G) · N_G(Z(J(P)))`; 特に `O_{p'}(G) = 1`
  なら `Z(J(P)) ⊴ G`.

`J` は Gorenstein 版 abelian Thompson subgroup `thompsonJAbelian`
(`ThompsonSubgroupAbelian.lean`), `Z(J(P))` は `C_G(J(P)) ⊓ J(P)` で符号化する
(`S06_Thm62JS` の `zCenter` 規約).

## p-stability の受け方

Gorenstein Ch.8 §1 の**群論的** p-stability (「`K ⊴ G` 正規 `p`-部分群, `A` `p`-部分群,
`[K,A,A] = 1` ⟹ `A C_G(K)/C_G(K) ≤ O_p(G/C_G(K))`」) を `IsPStableOp` として定義し,
Thm 2.10 の仮定に取る. ⚠ repo 既存の `OddOrder.BG.AppA.IsPStable` は**表現論的**定義
(faithful rep 上の quadratic minimal polynomial) で別物 — ただし BG Thm 6.2 の適用先
(odd solvable) では `AppA.stabilityLiftAux` (Gorenstein 6.5.3) が本条件をそのまま与える
ので, discharge は BG 側 (issue 3017/3024) で行う. Issue 9403.
-/

namespace Subgroup

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch01 in
/-- **Gorenstein Ch.8 §1 の群論的 p-stability** (Thm 2.10/2.11 の仮定形):
`K ⊴ G` が正規 `p`-部分群, `A` が `p`-部分群で `⁅⁅K,A⁆,A⁆ = ⊥` なら,
`A` の `G/C_G(K)` での像は `O_p(G/C_G(K))` に含まれる.

odd solvable な `G` では `OddOrder.BG.AppA.stabilityLiftAux` (Gorenstein 6.5.3)
がこの条件を与える. -/
def IsPStableOp (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ (K A : Subgroup G) (_ : K.Normal) (_ : IsPGroup p ↥K) (_ : IsPGroup p ↥A)
    (_ : ⁅⁅K, A⁆, A⁆ = ⊥),
    haveI : K.Normal := ‹_›
    A.map (QuotientGroup.mk' (centralizer (K : Set G)))
      ≤ opCore p (G ⧸ centralizer (K : Set G))

/-- 商での可換性による交換子の `T`-membership 特徴付け:
`⁅g, b⁆ ∈ T ⟺ mk g と mk b が可換` (`T ⊴ G`). -/
theorem commutatorElement_mem_iff_commute_mk {T : Subgroup G} [T.Normal] {g b : G} :
    ⁅g, b⁆ ∈ T ↔ Commute (QuotientGroup.mk' T g) (QuotientGroup.mk' T b) := by
  rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).symm

/-- **Gorenstein (2.20) の帳簿**: `B, T ⊴ G` で `⁅W, B⁆ ≤ T` なら
`⁅normalClosure W, B⁆ ≤ T` (共役は `B, T` の正規性で吸収される).
特に `B = normalClosure (Z ⊓ B)` (Thm 2.10 の最小反例) に適用して `B' ≤ Z ⊓ B'`. -/
theorem commutator_normalClosure_le {B W T : Subgroup G}
    [B.Normal] [T.Normal] (hWB : ⁅W, B⁆ ≤ T) :
    ⁅normalClosure (W : Set G), B⁆ ≤ T := by
  haveI : ((B.map (QuotientGroup.mk' T)) : Subgroup (G ⧸ T)).Normal :=
    Subgroup.Normal.map ‹B.Normal› _ (QuotientGroup.mk'_surjective T)
  have hkey : normalClosure (W : Set G)
      ≤ (centralizer ((B.map (QuotientGroup.mk' T)) : Set (G ⧸ T))).comap
          (QuotientGroup.mk' T) := by
    refine normalClosure_le_normal ?_
    intro w hw
    rw [SetLike.mem_coe, mem_comap, mem_centralizer_iff]
    rintro - ⟨b, hb, rfl⟩
    exact (commutatorElement_mem_iff_commute_mk.mp
      (hWB (commutator_mem_commutator hw hb))).symm.eq
  rw [commutator_le]
  intro g hg b hb
  refine commutatorElement_mem_iff_commute_mk.mpr ?_
  have hmem := hkey hg
  rw [mem_comap, mem_centralizer_iff] at hmem
  exact (hmem (QuotientGroup.mk' T b) (mem_map_of_mem _ hb)).symm

/-- **Gorenstein Theorem 2.10** (Glauberman): `G` 有限, `p` 奇素数,
`G` が群論的に `p`-stable (`IsPStableOp`), `B ⊴ G` が `p`-部分群,
`P ∈ Syl_p(G)` とすると, `B ⊓ Z(J_a(P)) ⊴ G`
(`Z(J_a(P))` は `C_G(J_a(P)) ⊓ J_a(P)` で符号化).

証明 (pdftotext L15282-15340, 最小反例帰納) は issue 9403 の分解 (a)-(e).
現状は honest statement + sorry (組立は次段; sorried-cite で下流 Thm 2.11 と
BG Thm 6.2 hZJ の組立を先行させる). -/
theorem inf_zCenter_thompsonJAbelian_normal [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hstable : IsPStableOp p G)
    (P : Sylow p G) {B : Subgroup G} [B.Normal] (hB : IsPGroup p ↥B) :
    (B ⊓ (centralizer ((thompsonJAbelian (P : Subgroup G)) : Set G)
      ⊓ thompsonJAbelian (P : Subgroup G))).Normal := by
  sorry

/-- conj で固定される部分群への normalizer membership. -/
theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hmem : (MulAut.conj g) x ∈ H.map (MulAut.conj g).toMonoidHom :=
      mem_map_of_mem _ hx
    rw [h] at hmem
    simpa [MulAut.conj_apply] using hmem
  · intro hx
    have hmem : g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := h.symm ▸ hx
    obtain ⟨y, hy, hye⟩ := mem_map.mp hmem
    have hyx : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hye
      exact mul_left_cancel (mul_right_cancel hye)
    exact hyx ▸ hy

/-- 正規化元による centralizer 元の共役は centralizer に留まる. -/
theorem conj_mem_centralizer_of_mem_normalizer {X : Subgroup G} {g c : G}
    (hg : g ∈ normalizer (X : Set G)) (hc : c ∈ centralizer (X : Set G)) :
    g * c * g⁻¹ ∈ centralizer (X : Set G) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro s hs
  have hs' : g⁻¹ * s * g ∈ X := by
    have h1 := mem_normalizer_iff.mp hg (g⁻¹ * s * g)
    rw [show g * (g⁻¹ * s * g) * g⁻¹ = s by group] at h1
    exact h1.mpr hs
  have h2 := hc _ hs'
  calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h2]
    _ = (g * c * g⁻¹) * s := by group

/-- 正規化元は centralizer も正規化する. -/
theorem mem_normalizer_centralizer {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer ((centralizer (X : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro c
  constructor
  · exact fun hc => conj_mem_centralizer_of_mem_normalizer hg hc
  · intro hc
    have hginv : g⁻¹ ∈ normalizer (X : Set G) := (normalizer (X : Set G)).inv_mem hg
    have h1 := conj_mem_centralizer_of_mem_normalizer hginv hc
    rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at h1

/-- `P₀ ≤ N(Z(J_a(P₀)))`: `J_a` は `P₀`-conj 不変 (characteristic) なので
その中心の符号化 `C(J_a) ⊓ J_a` も `P₀` に正規化される. -/
theorem le_normalizer_zCenter_thompsonJAbelian (P₀ : Subgroup G) :
    P₀ ≤ normalizer ((centralizer (thompsonJAbelian P₀ : Set G)
      ⊓ thompsonJAbelian P₀ : Subgroup G) : Set G) := by
  intro g hg
  have hgJ : g ∈ normalizer ((thompsonJAbelian P₀ : Subgroup G) : Set G) :=
    mem_normalizer_of_map_conj_eq
      (thompsonJAbelian_map_conj_eq_of_mem_normalizer (le_normalizer hg))
  exact mem_normalizer_inf (mem_normalizer_centralizer hgJ) hgJ

/-- **Thm 2.10 step (a)**: 最小反例の構造分析. `B ⊴ G`, `B ≤ P₀`,
`B = normalClosure (Z ⊓ B)` (`Z := C(J_a(P₀)) ⊓ J_a(P₀)`), `Z ⊓ ⁅B,B⁆ ⊴ G`
(帰納法が `⁅B,B⁆` に供給) のとき, `⁅B,B⁆ ≤ Z` (= Thm 2.7 の `B' ≤ Z(J_a)` 仮定)
かつ `⁅B,B⁆ ≤ C(B)` (= class ≤ 2). -/
theorem commutator_le_zCenter_and_centralizer_of_normalClosure_eq
    {P₀ B : Subgroup G} [B.Normal] (hBP : B ≤ P₀)
    (hBcl : B = normalClosure (((centralizer (thompsonJAbelian P₀ : Set G)
      ⊓ thompsonJAbelian P₀) ⊓ B : Subgroup G) : Set G))
    [hZB' : ((centralizer (thompsonJAbelian P₀ : Set G) ⊓ thompsonJAbelian P₀)
      ⊓ ⁅B, B⁆).Normal] :
    ⁅B, B⁆ ≤ centralizer (thompsonJAbelian P₀ : Set G) ⊓ thompsonJAbelian P₀
      ∧ ⁅B, B⁆ ≤ centralizer (B : Set G) := by
  -- (i) `⁅Z ⊓ B, B⁆ ≤ Z ⊓ B'`
  have hi : ⁅(centralizer (thompsonJAbelian P₀ : Set G) ⊓ thompsonJAbelian P₀) ⊓ B, B⁆
      ≤ (centralizer (thompsonJAbelian P₀ : Set G) ⊓ thompsonJAbelian P₀) ⊓ ⁅B, B⁆ := by
    refine le_inf ?_ (commutator_mono inf_le_right le_rfl)
    refine le_trans (commutator_mono inf_le_left le_rfl) ?_
    exact le_normalizer_iff_commutator_le_left.mp
      (hBP.trans (le_normalizer_zCenter_thompsonJAbelian P₀))
  -- (ii) `B' ≤ Z ⊓ B'` ((2.20) 帳簿)
  have hii : ⁅B, B⁆
      ≤ (centralizer (thompsonJAbelian P₀ : Set G) ⊓ thompsonJAbelian P₀) ⊓ ⁅B, B⁆ := by
    have h1 := commutator_normalClosure_le hi
    rwa [← hBcl] at h1
  have hB'Z : ⁅B, B⁆
      ≤ centralizer (thompsonJAbelian P₀ : Set G) ⊓ thompsonJAbelian P₀ :=
    hii.trans inf_le_left
  refine ⟨hB'Z, ?_⟩
  -- (iii) `B ≤ C(B')` (もう一度 (2.20), `T := ⊥`)
  rw [le_centralizer_iff]
  have hWB' : ⁅(centralizer (thompsonJAbelian P₀ : Set G) ⊓ thompsonJAbelian P₀) ⊓ B,
      ⁅B, B⁆⁆ ≤ (⊥ : Subgroup G) := by
    refine le_of_eq (commutator_eq_bot_iff_le_centralizer.mpr ?_)
    calc (centralizer (thompsonJAbelian P₀ : Set G) ⊓ thompsonJAbelian P₀) ⊓ B
        ≤ centralizer (thompsonJAbelian P₀ : Set G) := inf_le_left.trans inf_le_left
      _ ≤ centralizer ((⁅B, B⁆ : Subgroup G) : Set G) :=
          centralizer_le (SetLike.coe_subset_coe.mpr (hB'Z.trans inf_le_right))
  have h3 := commutator_normalClosure_le (T := (⊥ : Subgroup G)) hWB'
  rw [← hBcl] at h3
  exact commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp h3)

/-! ### Thm 2.10 step (b): `W` を正規化する最大の正規部分群 `L` -/

/-- **Gorenstein Thm 2.10 の `L`**: `W` を正規化する正規部分群全体の join.
join も `W` を正規化し (normalizer は部分群)、正規で、この性質を持つ正規部分群の
最大元になる. -/
def sSupNormalNormalizing (W : Subgroup G) : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ N ≤ normalizer (W : Set G)}

theorem sSupNormalNormalizing_le_normalizer (W : Subgroup G) :
    sSupNormalNormalizing W ≤ normalizer (W : Set G) :=
  sSup_le fun _ hN => hN.2

theorem le_sSupNormalNormalizing {W N : Subgroup G} (hN : N.Normal)
    (h : N ≤ normalizer (W : Set G)) : N ≤ sSupNormalNormalizing W :=
  le_sSup ⟨hN, h⟩

/-- `L = sSupNormalNormalizing W` は正規 (各生成部分群の conj-不変性から、
`comap (conj g)` への `sSup_le` で帰納なしに閉じる). -/
theorem sSupNormalNormalizing_normal (W : Subgroup G) :
    (sSupNormalNormalizing W).Normal := by
  constructor
  intro n hn g
  have key : sSupNormalNormalizing W
      ≤ (sSupNormalNormalizing W).comap (MulAut.conj g).toMonoidHom := by
    refine sSup_le fun N hN => ?_
    intro m hm
    rw [mem_comap]
    have hmem : (MulAut.conj g).toMonoidHom m ∈ N := by
      simpa [MulAut.conj_apply] using hN.1.conj_mem m hm g
    exact le_sSup hN hmem
  have h1 := key hn
  rw [mem_comap] at h1
  simpa [MulAut.conj_apply] using h1

/-- **Gorenstein Thm 1.3.8** (Sylow-of-normal): `L ⊴ G`, `P ∈ Syl_p(G)` について
`(P ⊓ L).subgroupOf L` を carrier とする `↥L` の Sylow `p` が存在する. -/
theorem exists_sylow_inf_of_normal [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (L : Subgroup G) [L.Normal] :
    ∃ Q : Sylow p ↥L, (Q : Subgroup ↥L) = ((P : Subgroup G) ⊓ L).subgroupOf L := by
  have hsub : IsPGroup p ↥(((P : Subgroup G) ⊓ L).subgroupOf L) :=
    (P.isPGroup'.to_inf_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : (P : Subgroup G) ⊓ L ≤ L)).symm
  have hidx : ¬ p ∣ (((P : Subgroup G) ⊓ L).subgroupOf L).index :=
    OddOrder.Isaacs.Ch09.not_dvd_relIndex_inf_of_isSubnormal
      (Subgroup.Normal.isSubnormal ‹L.Normal›) P
  exact ⟨hsub.toSylow hidx, hsub.toSylow_coe hidx⟩

/-- **Frattini + characteristic 昇格** (Gorenstein Thm 1.3.7 の用法):
`L ⊴ G`, `Q ∈ Syl_p(↥L)` について `L ⊔ N_G(J_a(Q-ambient)) = ⊤`
(`J_a` は conj 共変ゆえ `N_G(Q) ≤ N_G(J_a(Q))`). -/
theorem frattini_normalizer_thompsonJAbelian [Finite G] {p : ℕ} [Fact p.Prime]
    {L : Subgroup G} [L.Normal] (Q : Sylow p ↥L) :
    L ⊔ normalizer
      ((thompsonJAbelian ((Q : Subgroup ↥L).map L.subtype) : Subgroup G) : Set G)
      = ⊤ := by
  have hfr := Sylow.normalizer_sup_eq_top (p := p) (N := L) Q
  have hchar : normalizer (((Q : Subgroup ↥L).map L.subtype : Subgroup G) : Set G)
      ≤ normalizer
        ((thompsonJAbelian ((Q : Subgroup ↥L).map L.subtype) : Subgroup G) : Set G) :=
    fun _ hg => mem_normalizer_of_map_conj_eq
      (thompsonJAbelian_map_conj_eq_of_mem_normalizer hg)
  refine top_le_iff.mp ?_
  rw [← hfr]
  exact sup_le (hchar.trans le_sup_right) le_sup_left

open OddOrder.Isaacs.Ch01 in
/-- **Thm 2.10 step (c) 前半**: `P ≤ N(W)` なら `O_p(G ⧸ L) = ⊥`
(`L := sSupNormalNormalizing W`). Gorenstein の `K = L(P ∩ K)` 論法を index 算術
(`[K:M]` が `p` と互いに素かつ `p`-冪 ⟹ `= 1`) で実装. -/
theorem opCore_quotient_sSupNormalNormalizing_eq_bot [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {W : Subgroup G}
    (hPW : (P : Subgroup G) ≤ normalizer (W : Set G)) :
    haveI := sSupNormalNormalizing_normal W
    opCore p (G ⧸ sSupNormalNormalizing W) = ⊥ := by
  haveI := sSupNormalNormalizing_normal W
  set L := sSupNormalNormalizing W with hLdef
  set K := (opCore p (G ⧸ L)).comap (QuotientGroup.mk' L) with hKdef
  haveI hKnorm : K.Normal := Subgroup.normal_comap _
  have hLK : L ≤ K := by
    intro l hl
    rw [hKdef, mem_comap]
    have h1 : QuotientGroup.mk' L l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [h1]
    exact (opCore p (G ⧸ L)).one_mem
  have hmapK : K.map (QuotientGroup.mk' L) = opCore p (G ⧸ L) := by
    rw [hKdef]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective L) _
  have hKLpow : ∃ n, L.relIndex K = p ^ n := by
    rw [show L = (QuotientGroup.mk' L).ker from (QuotientGroup.ker_mk' L).symm,
      Subgroup.relIndex_ker, hmapK]
    exact (opCore_isPGroup p (G ⧸ L)).exists_card_eq
  have hSyl : ¬ p ∣ ((P : Subgroup G) ⊓ K).relIndex K :=
    OddOrder.Isaacs.Ch09.not_dvd_relIndex_inf_of_isSubnormal
      (Subgroup.Normal.isSubnormal hKnorm) P
  have hMK : L ⊔ ((P : Subgroup G) ⊓ K) = K := by
    have hMle : L ⊔ ((P : Subgroup G) ⊓ K) ≤ K := sup_le hLK inf_le_right
    have h1 : (L ⊔ ((P : Subgroup G) ⊓ K)).relIndex K
        ∣ ((P : Subgroup G) ⊓ K).relIndex K :=
      Subgroup.relIndex_dvd_of_le_left K le_sup_right
    have h2 : (L ⊔ ((P : Subgroup G) ⊓ K)).relIndex K ∣ L.relIndex K :=
      Subgroup.relIndex_dvd_of_le_left K le_sup_left
    obtain ⟨n, hn⟩ := hKLpow
    rw [hn] at h2
    have hne : ¬ p ∣ (L ⊔ ((P : Subgroup G) ⊓ K)).relIndex K :=
      fun hd => hSyl (dvd_trans hd h1)
    have hone : (L ⊔ ((P : Subgroup G) ⊓ K)).relIndex K = 1 := by
      rcases (Nat.dvd_prime_pow Fact.out).mp h2 with ⟨m, hm, hem⟩
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [hem, h0, pow_zero]
      · exact absurd (hem ▸ dvd_pow_self p hpos.ne') hne
    exact le_antisymm hMle (Subgroup.relIndex_eq_one.mp hone)
  have hKNW : K ≤ normalizer (W : Set G) := by
    rw [← hMK]
    exact sup_le (sSupNormalNormalizing_le_normalizer W) (inf_le_left.trans hPW)
  have hKL : K ≤ L := le_sSupNormalNormalizing hKnorm hKNW
  rw [← hmapK]
  refine le_bot_iff.mp ?_
  intro x hx
  obtain ⟨k, hk, rfl⟩ := mem_map.mp hx
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff _).mpr (hKL hk)

open OddOrder.Isaacs.Ch01 in
/-- **`O_p` の全射転送**: `f : G →* H` 全射なら `(O_p(G)).map f ≤ O_p(H)`
(像は正規 `p`-部分群ゆえ Isaacs Problem 1B.2 の最大性で吸収される). -/
theorem map_opCore_le_opCore_of_surjective {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] {f : G →* H} (hf : Function.Surjective f) :
    (opCore p G).map f ≤ opCore p H := by
  haveI : ((opCore p G).map f).Normal := Subgroup.Normal.map (opCore.normal p G) f hf
  exact normal_pgroup_le_opCore ((opCore_isPGroup p G).map f)

open OddOrder.Isaacs.Ch01 in
/-- **Thm 2.10 step (c) 後半** (Gorenstein p. 278-279): `G` が `p`-stable,
`B ⊴ G` `p`-部分群, `W ≤ B`, `P ≤ N(W)`, `A ∈ A(P)` で `⁅⁅B,A⁆,A⁆ = ⊥` なら
`A ≤ L := sSupNormalNormalizing W`.

論法: `C := C_G(B)` は `W ≤ B` を中心化するので `C ≤ N(W)`, `C ⊴ G`
(mathlib `normal_centralizer`) ⟹ `L` の最大性で `C ≤ L`. p-stability で
`AC/C ≤ O_p(G/C)`; 全射 `G/C → G/L` で `AL/L ≤ O_p(G/L) = ⊥` (step (c) 前半)
⟹ `A ≤ L`. -/
theorem le_sSupNormalNormalizing_of_isPStableOp [Finite G] {p : ℕ} [Fact p.Prime]
    (hstable : IsPStableOp p G) (P : Sylow p G)
    {B W A : Subgroup G} [B.Normal] (hB : IsPGroup p ↥B)
    (hWB : W ≤ B) (hPW : (P : Subgroup G) ≤ normalizer (W : Set G))
    (hA : A ∈ maxAbelianIn (P : Subgroup G))
    (hBAA : ⁅⁅B, A⁆, A⁆ = ⊥) :
    A ≤ sSupNormalNormalizing W := by
  haveI := sSupNormalNormalizing_normal W
  -- `C := C_G(B) ≤ L` (正規 + `W` を中心化 ⟹ 正規化).
  have hCL : centralizer (B : Set G) ≤ sSupNormalNormalizing W :=
    le_sSupNormalNormalizing inferInstance
      ((centralizer_le (SetLike.coe_subset_coe.mpr hWB)).trans
        (centralizer_le_normalizer _))
  -- p-stability の適用: `A` の `G/C` での像は `O_p(G/C)`.
  have hApgroup : IsPGroup p ↥A :=
    P.isPGroup'.of_injective (Subgroup.inclusion hA.1) (Subgroup.inclusion_injective _)
  have hstab := hstable B A ‹B.Normal› hB hApgroup hBAA
  -- 全射 `φ : G/C → G/L` で転送.
  set φ : G ⧸ centralizer (B : Set G) →* G ⧸ sSupNormalNormalizing W :=
    QuotientGroup.map _ _ (MonoidHom.id G) (fun x hx => hCL hx) with hφdef
  have hcomp : φ.comp (QuotientGroup.mk' (centralizer (B : Set G)))
      = QuotientGroup.mk' (sSupNormalNormalizing W) := by
    ext x
    simp [hφdef]
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (sSupNormalNormalizing W) y
    exact ⟨QuotientGroup.mk' _ x, by rw [← MonoidHom.comp_apply, hcomp]⟩
  have hmapL : A.map (QuotientGroup.mk' (sSupNormalNormalizing W))
      ≤ opCore p (G ⧸ sSupNormalNormalizing W) := by
    calc A.map (QuotientGroup.mk' (sSupNormalNormalizing W))
        = (A.map (QuotientGroup.mk' (centralizer (B : Set G)))).map φ := by
          rw [Subgroup.map_map, hcomp]
      _ ≤ (opCore p (G ⧸ centralizer (B : Set G))).map φ := Subgroup.map_mono hstab
      _ ≤ opCore p (G ⧸ sSupNormalNormalizing W) :=
          map_opCore_le_opCore_of_surjective hφsurj
  have hbot : A.map (QuotientGroup.mk' (sSupNormalNormalizing W)) = ⊥ :=
    le_bot_iff.mp (hmapL.trans_eq
      (opCore_quotient_sSupNormalNormalizing_eq_bot P hPW))
  intro a ha
  have h1 : QuotientGroup.mk' (sSupNormalNormalizing W) a ∈
      A.map (QuotientGroup.mk' (sSupNormalNormalizing W)) := mem_map_of_mem _ ha
  rw [hbot, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff a).mp h1

/-! ### Thm 2.10 step (d): `B = normalClosure (Z ⊓ B) ≤ Z(J_a(P ⊓ L))` -/

/-- **Frattini 分解による normal closure の吸収**: `L ⊔ N(X) = ⊤`, `L ⊴ G`,
`L ≤ N(W)`, `W ≤ X` なら `normalClosure W ≤ X`
(`g = n·l` 分解で `W^g = (W^l)^n = W^n ≤ X^n = X`). -/
theorem normalClosure_le_of_sup_normalizer_eq_top {L W X : Subgroup G} [L.Normal]
    (hsup : L ⊔ normalizer (X : Set G) = ⊤)
    (hLW : L ≤ normalizer (W : Set G)) (hWX : W ≤ X) :
    normalClosure (W : Set G) ≤ X := by
  refine (closure_le X).mpr ?_
  intro a ha
  rw [Group.mem_conjugatesOfSet_iff] at ha
  obtain ⟨b, hb, hconj⟩ := ha
  obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
  have hctop : c ∈ ((normalizer (X : Set G) : Subgroup G) : Set G) * (L : Set G) := by
    rw [← Subgroup.mul_normal]
    show c ∈ ((normalizer (X : Set G) ⊔ L : Subgroup G) : Set G)
    rw [sup_comm, hsup]
    exact Subgroup.mem_top c
  rw [Set.mem_mul] at hctop
  obtain ⟨n, hn, l, hl, rfl⟩ := hctop
  have hbW : l * b * l⁻¹ ∈ W := (mem_normalizer_iff.mp (hLW hl) b).mp hb
  have hbX : n * (l * b * l⁻¹) * n⁻¹ ∈ X :=
    (mem_normalizer_iff.mp hn _).mp (hWX hbW)
  have heq : n * l * b * (n * l)⁻¹ = n * (l * b * l⁻¹) * n⁻¹ := by group
  rw [SetLike.mem_coe, heq]
  exact hbX

/-- **Thm 2.10 step (d)** (Gorenstein p. 279): `W ≤ Z(J_a(P))`, `A ∈ A(P)`,
`A ≤ L := sSupNormalNormalizing W` なら `normalClosure W ≤ X := Z(J_a(P ⊓ L))`
(Thm 2.10 では `W = Z ⊓ B`, `B = normalClosure W` に適用して **`B` abelian** を得る).

`A ≤ P ⊓ L` が `A(P⊓L)` の witness になり `J_a(P⊓L) ≤ J_a(P)` (Lem 2.2(a));
`W ≤ Z(J_a(P)) ≤ A ≤ J_a(P⊓L)` (Lem 2.1 系 2) と `W ≤ C(J_a(P)) ≤ C(J_a(P⊓L))` で
`W ≤ X`; Frattini `G = L·N(J_a(P⊓L))` (Thm 1.3.7/1.3.8) + `N(J_a) ≤ N(X)` +
`L ≤ N(W)` で normal closure が `X` に吸収される. -/
theorem normalClosure_le_zCenter_thompsonJAbelian_inf [Finite G] {p : ℕ}
    [Fact p.Prime] (P : Sylow p G) {W A : Subgroup G}
    (hWZ : W ≤ centralizer ((thompsonJAbelian (P : Subgroup G)) : Set G)
      ⊓ thompsonJAbelian (P : Subgroup G))
    (hA : A ∈ maxAbelianIn (P : Subgroup G))
    (hAL : A ≤ sSupNormalNormalizing W) :
    normalClosure (W : Set G)
      ≤ centralizer
          ((thompsonJAbelian ((P : Subgroup G) ⊓ sSupNormalNormalizing W)) : Set G)
        ⊓ thompsonJAbelian ((P : Subgroup G) ⊓ sSupNormalNormalizing W) := by
  haveI := sSupNormalNormalizing_normal W
  have hAPL : A ≤ (P : Subgroup G) ⊓ sSupNormalNormalizing W := le_inf hA.1 hAL
  have hAin : A ∈ maxAbelianIn ((P : Subgroup G) ⊓ sSupNormalNormalizing W) :=
    ⟨hAPL, hA.2.1, fun B' hB' hB'comm => hA.2.2 B' (hB'.trans inf_le_left) hB'comm⟩
  have hJle : thompsonJAbelian ((P : Subgroup G) ⊓ sSupNormalNormalizing W)
      ≤ thompsonJAbelian (P : Subgroup G) :=
    thompsonJAbelian_le_of_le inf_le_left hA hAPL
  have hWX : W ≤ centralizer
      ((thompsonJAbelian ((P : Subgroup G) ⊓ sSupNormalNormalizing W)) : Set G)
      ⊓ thompsonJAbelian ((P : Subgroup G) ⊓ sSupNormalNormalizing W) :=
    le_inf
      ((hWZ.trans inf_le_left).trans
        (centralizer_le (SetLike.coe_subset_coe.mpr hJle)))
      ((hWZ.trans (zCenter_thompsonJAbelian_le_of_mem_maxAbelianIn hA)).trans
        (le_thompsonJAbelian_of_mem_maxAbelianIn hAin))
  obtain ⟨Q, hQ⟩ := exists_sylow_inf_of_normal P (sSupNormalNormalizing W)
  have hfr := frattini_normalizer_thompsonJAbelian Q
  have hmap : ((Q : Subgroup ↥(sSupNormalNormalizing W)).map
      (sSupNormalNormalizing W).subtype)
      = (P : Subgroup G) ⊓ sSupNormalNormalizing W := by
    rw [hQ, subgroupOf_map_subtype]
    exact inf_eq_left.mpr inf_le_right
  rw [hmap] at hfr
  have hsup : sSupNormalNormalizing W
      ⊔ normalizer ((centralizer
          ((thompsonJAbelian ((P : Subgroup G) ⊓ sSupNormalNormalizing W)) : Set G)
        ⊓ thompsonJAbelian ((P : Subgroup G) ⊓ sSupNormalNormalizing W)
          : Subgroup G) : Set G) = ⊤ := by
    rw [eq_top_iff, ← hfr]
    refine sup_le_sup_left (fun g hg => ?_) _
    exact mem_normalizer_inf (mem_normalizer_centralizer hg) hg
  exact normalClosure_le_of_sup_normalizer_eq_top hsup
    (sSupNormalNormalizing_le_normalizer W) hWX

end Subgroup




