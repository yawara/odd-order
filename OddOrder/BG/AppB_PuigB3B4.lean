/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppB_Puig
import OddOrder.BG.AppA_PStability

/-!
# BG Appendix B: Lemma B.3 + Theorem B.4 (Puig, = Thm 6.2 代替)

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Appendix B (pp. 142-144), mmd L4644-4757.

`OddOrder/BG/AppB_Puig.lean` (定義 + Lemma B.1 + B.2) と `AppA_PStability.lean` (Thm A.5) の上に
**Lemma B.3** (Sylow ↔ p-core の `L`-tower 階層) と **Theorem B.4** (Puig, `Z(L(S))·O_{p'}(G) ⊴ G`,
= BG Thm 6.2 = Glauberman `Z(J)` の自己完結代替) を構築する. issue 2001.

B.4(a) (`G = O_{p'}(G)·N_G(Z(L(S)))`) は異群 iso 共変性を要するため別 issue (2002)。
本ファイルは **B.3 + B.4(b)** (`O_{p'}(G)=1 ⇒ Z(L(S)) ⊴ G`)。

## Main results

* `OddOrder.BG.AppB.b3_chain` — **BG Lemma B.3** (L4646): `p` odd solvable, `O_{p'}(G)=1`,
  `S ∈ Syl_p(G)`, `T = O_p(G)` ⇒ `L_*(S) ⊆ L_*(T) ⊆ L(T) ⊆ L(S)`.
-/

namespace OddOrder.BG.AppB

open OddOrder.Isaacs.Ch01 OddOrder.Isaacs.Ch03 OddOrder.BG.AppA

variable {G : Type*} [Group G]

/-- **BG Lemma B.3 帰納核** (mmd L4650-4668): `∀ n`,
`L_{2n}(S) ⊆ L_{2n}(T) ⊆ L_{2n+1}(T) ⊆ L_{2n+1}(S)` (`T = O_p(G)`).
偶段は Thm A.5(2) (`P = L_{2n+1}(T)`, `X = L_{2n+2}(S)`) で `L_{2n+2}(S) ⊆ T` を得て従う. -/
private theorem b3_interleave [Finite G] {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hsolv : IsSolvable G) (hodd : Odd (Nat.card G))
    (hOp' : oPiCore {q | q ≠ p} G = ⊥) (S : Sylow p G) :
    ∀ n, lNIn (S : Subgroup G) (2 * n) ≤ lNIn (opCore p G) (2 * n) ∧
      lNIn (opCore p G) (2 * n) ≤ lNIn (opCore p G) (2 * n + 1) ∧
      lNIn (opCore p G) (2 * n + 1) ≤ lNIn (S : Subgroup G) (2 * n + 1) := by
  have hT_le_S : opCore p G ≤ (S : Subgroup G) := opCore_le S
  have hT_pg : IsPGroup p ↥(opCore p G) := opCore_isPGroup p G
  intro n
  induction n with
  | zero =>
      have h1 : lNIn (S : Subgroup G) (2 * 0) = ⊥ := lNIn_zero _
      have h2 : lNIn (opCore p G) (2 * 0) = ⊥ := lNIn_zero _
      have h3 : lNIn (opCore p G) (2 * 0 + 1) = opCore p G := lNIn_one _
      have h4 : lNIn (S : Subgroup G) (2 * 0 + 1) = (S : Subgroup G) := lNIn_one _
      rw [h1, h2, h3, h4]
      exact ⟨le_refl _, bot_le, hT_le_S⟩
  | succ n ih =>
      obtain ⟨_, _, hTS⟩ := ih
      -- Step 1 (A.5): L_{2n+2}(S) ⊆ T
      haveI hP_char : (lNIn (opCore p G) (2 * n + 1)).Characteristic :=
        lNIn_characteristic_of_characteristic (opCore.characteristic p G) (2 * n + 1)
      haveI hP_normal : (lNIn (opCore p G) (2 * n + 1)).Normal := inferInstance
      have hP_pg : IsPGroup p ↥(lNIn (opCore p G) (2 * n + 1)) := hT_pg.to_le (lNIn_le_self _ _)
      have hX : lNIn (S : Subgroup G) (2 * n + 2) ≤ ⨆ A ∈ {A : Subgroup G | IsMulCommutative ↥A ∧
          IsPGroup p ↥A ∧ lNIn (opCore p G) (2 * n + 1) ≤ Subgroup.normalizer (A : Set G)}, A := by
        rw [show lNIn (S : Subgroup G) (2 * n + 2)
            = lRelIn (S : Subgroup G) (lNIn (S : Subgroup G) (2 * n + 1)) from lNIn_succ _ _]
        exact lRelIn_le_iSup_pgroup_normalized S.isPGroup' hTS
      have hST2 : lNIn (S : Subgroup G) (2 * n + 2) ≤ opCore p G :=
        thmA5_part2 hp_odd hsolv hodd hP_pg hX hOp' (centralizer_lNIn_inf_le hT_pg (by omega))
      -- (a) L_{2n+2}(S) ⊆ L_{2n+2}(T)
      have e1 : lNIn (S : Subgroup G) (2 * n + 2)
          = lRelIn (S : Subgroup G) (lNIn (S : Subgroup G) (2 * n + 1)) := lNIn_succ _ _
      have e2 : lNIn (opCore p G) (2 * n + 2)
          = lRelIn (opCore p G) (lNIn (opCore p G) (2 * n + 1)) := lNIn_succ _ _
      have ha : lNIn (S : Subgroup G) (2 * n + 2) ≤ lNIn (opCore p G) (2 * n + 2) := by
        rw [e1, e2]; exact lRelIn_le_lRelIn hTS hST2
      -- (b) L_{2n+2}(T) ⊆ L_{2n+3}(T)
      have hb : lNIn (opCore p G) (2 * n + 2) ≤ lNIn (opCore p G) (2 * n + 3) := by
        have h := lNIn_even_le_odd (opCore p G) (n + 1) (n + 1)
        rwa [show 2 * (n + 1) = 2 * n + 2 from by ring] at h
      -- (c) L_{2n+3}(T) ⊆ L_{2n+3}(S)
      have hc : lNIn (opCore p G) (2 * n + 3) ≤ lNIn (S : Subgroup G) (2 * n + 3) := by
        rw [show lNIn (opCore p G) (2 * n + 3)
              = lRelIn (opCore p G) (lNIn (opCore p G) (2 * n + 2)) from lNIn_succ _ _,
          show lNIn (S : Subgroup G) (2 * n + 3)
              = lRelIn (S : Subgroup G) (lNIn (S : Subgroup G) (2 * n + 2)) from lNIn_succ _ _]
        exact (lRelIn_anti_right ha).trans (lRelIn_mono_left hT_le_S _)
      refine ⟨?_, ?_, ?_⟩
      · rw [show 2 * (n + 1) = 2 * n + 2 from by ring]; exact ha
      · rw [show 2 * (n + 1) = 2 * n + 2 from by ring]; exact hb
      · rw [show 2 * (n + 1) + 1 = 2 * n + 3 from by ring]; exact hc

/-- **BG Lemma B.3** (mmd L4646): `p` odd, `G` solvable of odd order, `O_{p'}(G)=1`,
`S ∈ Syl_p(G)`, `T = O_p(G)` ⇒ `L_*(S) ⊆ L_*(T) ⊆ L(T) ⊆ L(S)`. -/
theorem b3_chain [Finite G] {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hsolv : IsSolvable G) (hodd : Odd (Nat.card G))
    (hOp' : oPiCore {q | q ≠ p} G = ⊥) (S : Sylow p G) :
    lStarIn (S : Subgroup G) ≤ lStarIn (opCore p G) ∧
      lStarIn (opCore p G) ≤ lOddIn (opCore p G) ∧
      lOddIn (opCore p G) ≤ lOddIn (S : Subgroup G) := by
  obtain ⟨k1, hk1⟩ := exists_lStarIn_eq (S : Subgroup G)
  obtain ⟨k2, hk2⟩ := exists_lStarIn_eq (opCore p G)
  obtain ⟨k3, hk3⟩ := exists_lOddIn_eq (opCore p G)
  obtain ⟨k4, hk4⟩ := exists_lOddIn_eq (S : Subgroup G)
  set K := max (max k1 k2) (max k3 k4) with hK
  obtain ⟨hSS, _, hTS⟩ := b3_interleave hp_odd hsolv hodd hOp' S K
  refine ⟨?_, lStarIn_le_lOddIn (opCore p G), ?_⟩
  · rw [hk1 K (le_trans (le_max_left _ _) (le_max_left _ _)),
      hk2 K (le_trans (le_max_right _ _) (le_max_left _ _))]
    exact hSS
  · rw [hk3 K (le_trans (le_max_left _ _) (le_max_right _ _)),
      hk4 K (le_trans (le_max_right _ _) (le_max_right _ _))]
    exact hTS

/-! ### Theorem B.4(b): `O_{p'}(G)=1 ⇒ Z(L(S)) ⊴ G` (= Thm 6.2 代替, mmd L4686-4762) -/

/-- `Z(L(H))` を `G` の部分群として実現: `L(H)` の中心を subtype で `G` に落とす. -/
def zCenterLOdd (H : Subgroup G) : Subgroup G :=
  (Subgroup.center (lOddIn H : Subgroup G)).map (lOddIn H).subtype

/-- `Z(L(H)) ⊆ L(H)`. -/
theorem zCenterLOdd_le_lOddIn (H : Subgroup G) : zCenterLOdd H ≤ (lOddIn H : Subgroup G) :=
  Subgroup.map_subtype_le _

/-- **keystone bridge**: `Z(L(H)) = C_G(L(H)) ⊓ L(H)` (中心を `G`-中心化群の交わりで表す). -/
theorem zCenterLOdd_eq_centralizer_inf (H : Subgroup G) :
    zCenterLOdd H = Subgroup.centralizer (lOddIn H : Set G) ⊓ (lOddIn H : Subgroup G) := by
  refine le_antisymm (le_inf ?_ (zCenterLOdd_le_lOddIn H)) ?_
  · rintro g hg
    obtain ⟨z, hz_center, rfl⟩ := Subgroup.mem_map.mp hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hw := Subgroup.mem_center_iff.mp hz_center ⟨h, hh⟩
    have hco := congrArg (Subtype.val) hw
    push_cast at hco
    exact hco
  · intro g hg
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hg
    obtain ⟨hg_cent, hg_mem⟩ := hg
    refine ⟨⟨g, hg_mem⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    push_cast
    exact hg_cent (w : G) w.2

/-- **BG Theorem B.4(b) Step 2** (mmd L4707-4719): `Z(L(S)) ⊆ Z(L(T))` (`T = O_p(G)`).
`Z(L(S))` は `S` 内で `L(S) ⊇ L_*(S)` を中心化 ⇒ 相対 B.1(f) で `L_*(S)` に入り,
B.3 で `L_*(S) ⊆ L_*(T) ⊆ L(T)`; かつ `L(T) ⊆ L(S)` ゆえ `L(T)` も中心化. -/
theorem zCenterLOdd_sylow_le_zCenterLOdd_opCore [Finite G] {p : ℕ} [Fact p.Prime]
    (hp_odd : p ≠ 2) (hsolv : IsSolvable G) (hodd : Odd (Nat.card G))
    (hOp' : oPiCore {q | q ≠ p} G = ⊥) (S : Sylow p G) :
    zCenterLOdd (S : Subgroup G) ≤ zCenterLOdd (opCore p G) := by
  obtain ⟨hSS, hST, hTS⟩ := b3_chain hp_odd hsolv hodd hOp' S
  have hZ_cent_LS : zCenterLOdd (S : Subgroup G)
      ≤ Subgroup.centralizer (lOddIn (S : Subgroup G) : Set G) := by
    rw [zCenterLOdd_eq_centralizer_inf]; exact inf_le_left
  have hZ_le_S : zCenterLOdd (S : Subgroup G) ≤ (S : Subgroup G) :=
    (zCenterLOdd_le_lOddIn (S : Subgroup G)).trans (lOddIn_le_self (S : Subgroup G))
  have hZ_cent_LstarS : zCenterLOdd (S : Subgroup G)
      ≤ Subgroup.centralizer (lStarIn (S : Subgroup G) : Set G) :=
    hZ_cent_LS.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (lStarIn_le_lOddIn _)))
  have hZ_le_LstarS : zCenterLOdd (S : Subgroup G) ≤ lStarIn (S : Subgroup G) :=
    (le_inf hZ_cent_LstarS hZ_le_S).trans (centralizer_lStarIn_inf_le S.isPGroup')
  have hZ_le_LT : zCenterLOdd (S : Subgroup G) ≤ lOddIn (opCore p G) :=
    (hZ_le_LstarS.trans hSS).trans hST
  have hZ_cent_LT : zCenterLOdd (S : Subgroup G)
      ≤ Subgroup.centralizer (lOddIn (opCore p G) : Set G) :=
    hZ_cent_LS.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTS))
  rw [zCenterLOdd_eq_centralizer_inf (opCore p G)]
  exact le_inf hZ_cent_LT hZ_le_LT

/-- `L(H)` は `H` を固定する `G`-自己同型 `φ` で不変 (`lNIn_map_equiv` を `⨅` に分配). -/
theorem lOddIn_map_equiv (φ : G ≃* G) {H : Subgroup G} (hH : H.map φ.toMonoidHom = H) :
    (lOddIn H).map φ.toMonoidHom = lOddIn H := by
  change (⨅ n, lNIn H (2 * n + 1)).map φ.toMonoidHom = ⨅ n, lNIn H (2 * n + 1)
  rw [Subgroup.map_iInf φ.toMonoidHom φ.injective]
  exact iInf_congr fun n => lNIn_map_equiv φ hH (2 * n + 1)

/-- `K.map (conj g) = K ↔ g ∈ N_G(K)` (共役写像が `K` を固定 ⇔ `g` が `K` を正規化). -/
theorem map_conj_eq_iff_mem_normalizer {K : Subgroup G} {g : G} :
    K.map (MulAut.conj g).toMonoidHom = K ↔ g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  constructor
  · intro hmap h
    constructor
    · intro hh
      have hm : (MulAut.conj g).toMonoidHom h ∈ K.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hh
      rw [hmap] at hm
      simpa [MulAut.conj_apply] using hm
    · intro hh
      have hm : g * h * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := by rw [hmap]; exact hh
      obtain ⟨y, hy, hxy⟩ := hm
      simp only [MulAut.conj_apply, MonoidHom.coe_coe] at hxy
      have hyh : y = h := mul_left_cancel (mul_right_cancel hxy)
      rwa [← hyh]
  · intro hnorm
    ext x
    simp only [Subgroup.mem_map, MulAut.conj_apply, MonoidHom.coe_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hnorm y).mp hy
    · intro hx
      have he : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      refine ⟨g⁻¹ * x * g, ?_, he⟩
      rw [← SetLike.mem_coe, hnorm (g⁻¹ * x * g), he]
      exact hx

/-- **`L`-operator の normalizer 同変性**: `N_G(H) ≤ N_G(L(H))` (任意の `H`).
`g ∈ N_G(H)` ⇒ 共役 `conj g` が `H` を固定 ⇒ `L(H)` も固定 ⇒ `g ∈ N_G(L(H))`.
これが B.4(b) Step3 の `N_G(C∩S) ≤ N_G(L(C∩S))` を subgroupOf transport 無しで与える. -/
theorem normalizer_le_normalizer_lOddIn (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (lOddIn H : Set G) := by
  intro g hg
  exact map_conj_eq_iff_mem_normalizer.mp
    (lOddIn_map_equiv (MulAut.conj g) (map_conj_eq_iff_mem_normalizer.mpr hg))

end OddOrder.BG.AppB
