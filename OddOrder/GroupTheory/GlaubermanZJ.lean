/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.GlaubermanReplacement

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

end Subgroup
