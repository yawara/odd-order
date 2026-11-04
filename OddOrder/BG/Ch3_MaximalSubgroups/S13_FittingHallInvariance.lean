/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import OddOrder.BG.Ch2_Uniqueness.S08_FittingInGBasic

/-!
# BG §13: Fitting 部分群の同型不変性 (Lemma 13.8 の Hall 共役 dispatch 用)

**Scope**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter III §13 (mmd L3630, pp. 101–102) — Lemma 13.8 の証明で使う補題群。

`p`-core と Fitting 部分群が群同型で保たれること、およびその帰結として可解群の共役な Hall
部分群の `F`-素因子が一致すること (`fittingInG_primeFactors_eq_of_isHall_subgroupOf`)。
`S13_Lemma138` が 1,500 行を超えたため切り出した (issue 0190)。
-/

@[expose] public section

namespace OddOrder.BG.Ch3.S13

open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-! ## helper: Fitting の同型不変性 (Lemma 13.8 dispatch — Hall 共役の F-primes 一致) -/

/-- **`p`-core の像 ≤ `p`-core** (群同型 `e`): `(O_p(A)).map e ≤ O_p(B)`。像は正規 `p`-部分群
ゆえ `normal_pgroup_le_opCore`。 -/
theorem opCore_map_le_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} [Fact p.Prime] (e : A ≃* B) :
    (Ch01.opCore p A).map e.toMonoidHom ≤ Ch01.opCore p B := by
  have : ((Ch01.opCore p A).map e.toMonoidHom).Normal :=
    (Ch01.opCore.normal p A).map e.toMonoidHom e.surjective
  exact Ch01.normal_pgroup_le_opCore
    ((Ch01.opCore_isPGroup p A).of_equiv
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective))

/-- **`p`-core は群同型で保たれる**: `e : A ≃* B` なら `(O_p(A)).map e = O_p(B)`。 -/
theorem opCore_map_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} [Fact p.Prime] (e : A ≃* B) :
    (Ch01.opCore p A).map e.toMonoidHom = Ch01.opCore p B := by
  refine le_antisymm (opCore_map_le_of_mulEquiv e) ?_
  have h2 := opCore_map_le_of_mulEquiv (p := p) e.symm
  have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by ext x; simp
  calc Ch01.opCore p B
      = (Ch01.opCore p B).map (MonoidHom.id B) := (Subgroup.map_id _).symm
    _ = ((Ch01.opCore p B).map e.symm.toMonoidHom).map e.toMonoidHom := by
        rw [← hid, Subgroup.map_map]
    _ ≤ (Ch01.opCore p A).map e.toMonoidHom := Subgroup.map_mono h2

/-- **Fitting 部分群の位数は群同型で不変**: `e : A ≃* B` なら `|F(A)| = |F(B)|`。
`F = ⨆ O_p` を `opCore_map_of_mulEquiv` + `map_iSup` で写し、`card_map_of_injective`。 -/
theorem fitting_card_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) : Nat.card ↥(Ch01.fitting A) = Nat.card ↥(Ch01.fitting B) := by
  have hmap : (Ch01.fitting A).map e.toMonoidHom = Ch01.fitting B := by
    unfold Ch01.fitting
    rw [Subgroup.map_iSup]
    refine iSup_congr (fun p => ?_)
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    exact opCore_map_of_mulEquiv e
  rw [← hmap, Subgroup.card_map_of_injective e.injective]

/-- **共役 Hall 部分群の `F`-素因子は一致** (Lemma 13.8 dispatch の核): `C` 可解で `H, K` が
`C` の Hall `θ`-部分群 (相対) なら `π(F(H)) = π(F(K))`。`hall_C` で `H, K` は `C` 内共役、
`fitting_card_eq_of_mulEquiv` で `|F(H)| = |F(K)|`。

13.8 main: `s ∈ π(F(H))` (`H ⊇ C_{M_β}(P)`) を `π(F(H*))` (`H* ⊇ C_{M*_β}(P)`) へ移送し
WLOG `s ∈ β(M)` / `β(M*)` の向き切替を可能にする。 -/
theorem fittingInG_primeFactors_eq_of_isHall_subgroupOf [Finite G] {C H K : Subgroup G}
    [Group.IsSolvable ↥C] {θ : Set ℕ} (hHC : H ≤ C) (hKC : K ≤ C)
    (hH : Ch03.IsHallSubgroup θ (H.subgroupOf C)) (hK : Ch03.IsHallSubgroup θ (K.subgroupOf C)) :
    (Nat.card ↥(Ch2.S08.fittingInG H)).primeFactors
      = (Nat.card ↥(Ch2.S08.fittingInG K)).primeFactors := by
  obtain ⟨c, hc⟩ := Ch03.hall_C hH hK
  have ehk : ↥(H.subgroupOf C) ≃* ↥(K.subgroupOf C) := by
    rw [← hc]
    exact Subgroup.equivMapOfInjective _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
  have e : ↥H ≃* ↥K :=
    (Subgroup.subgroupOfEquivOfLe hHC).symm.trans (ehk.trans (Subgroup.subgroupOfEquivOfLe hKC))
  have h1 : Nat.card ↥(Ch2.S08.fittingInG H) = Nat.card ↥(Ch01.fitting ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have h2 : Nat.card ↥(Ch2.S08.fittingInG K) = Nat.card ↥(Ch01.fitting ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  rw [h1, h2, fitting_card_eq_of_mulEquiv e]

end OddOrder.BG.Ch3.S13
