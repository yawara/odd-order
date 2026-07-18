/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import OddOrder.GroupTheory.OmegaSubgroup
import OddOrder.GroupTheory.ThompsonSubgroup
import OddOrder.Isaacs.Ch02_Subnormality.Main
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.Isaacs.Ch05_Transfer.Main
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main

/-!
# Isaacs FGT Ch.7 (Thompson subgroup) — S7A part 1: J(P) def, Thm 7.1 stmt, Lem 7.3 GL(2,p) lemma
(pp. 201-208)
-/

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## §7A: `J(P)` definition + GL(2,p) lemma + normal-P theorem (pp. 201-208) -/


/-!
### `J(P)` 定義

Thompson subgroup `J(P) = ⟨E(P)⟩` の定義は
[`OddOrder.GroupTheory.ThompsonSubgroup`](../../GroupTheory/ThompsonSubgroup.lean)
に集約: `Subgroup.thompsonJ P p` および `Subgroup.maxElemAbelianIn P p`
(Isaacs L3727 の `E(P)`).

Isaacs L3727 の **Aschbacher/Isaacs 版** (max **order**) を採用. Thompson 原版 (max
**rank**) は abelian non-elementary な P で異なりうるが本書では本版を一次採用.
-/

/-- **Isaacs Thm 7.2** (J(P) は中間部分群でも変わらない).

`J(P) ≤ Q ≤ P` のとき `J(Q) = J(P)`. 系として **`J(P)` は `Q` 内 characteristic**
(`J(Q)` の Q 内 characteristic 性と組み合わせて従う).

証明は [`OddOrder.GroupTheory.Subgroup.thompsonJ_eq_of_le_of_le`](
../../GroupTheory/ThompsonSubgroup.lean) に集約. -/
theorem thompsonJ_eq_of_le [Finite G] {P Q : Subgroup G} {p : ℕ}
    (hJQ : Subgroup.thompsonJ P p ≤ Q) (hQP : Q ≤ P) :
    Subgroup.thompsonJ Q p = Subgroup.thompsonJ P p :=
  Subgroup.thompsonJ_eq_of_le_of_le hJQ hQP

/-! ### Thm 7.1 — Thompson normal p-complement (statement 保留)

**Isaacs Thm 7.1** (Thompson, mmd L3721):

> `p ≠ 2`, `P ∈ Syl_p(G)`, `C_G(Z(P))` と `N_G(J(P))` が normal p-complement を持つ
> ⇒ G が normal p-complement を持つ.

**先行 def 依存**: `Group.HasNormalPComplement G p` (Ch.5 で実装予定, 設計判断
[`notes/isaacs/ch07_thompson.md`](../../../notes/isaacs/ch07_thompson.md) §設計判断 (2)).

**proof 戦略** (§7C, Steps 1-7): counterexample-minimum + Thm 7.6 normal-J +
Thm 5.26 Frobenius normal p-complement + Lem 7.7 (N/C `p'`-quotient).

**下流**: Ch.6 Thm 6.23 (`axiom`/`sorry`) を本定理で書き換え, 6.24 (Frobenius
kernel nilpotent) を完備化. BG/Peterfalvi 直接被引用は無し (Ch.6 経由のみ).

着手は Ch.5 §5E (5.26) + 本ファイル §7B (7.6) + §7C (7.7) 完成後. -/

/-! ### Lem 7.3 — GL(2,p) 補題

**Isaacs Lem 7.3** (mmd L3739): `p ≠ 2` prime, `P ≤ GL(2,p)` p-subgroup,
`P ≤ N(L)`, `(|L|, p) = 1`, `L` の Sylow 2-subgroup abelian ⇒ `P ≤ C_G(L)`.

**Lean 上の statement と証明 skeleton は Lem 7.4 の後** に配置
(`gl2_pSubgroup_centralizes_of_normalizes`). 証明は `|L|`-induction + P-invariant
Sylow (Ch.3 Thm 3.23(a)) + Lem 7.4 (本ファイル) + Lem 4.29 (Ch.4 §4D) を組み合わせる.

**仮説形の選択**: 「L の Sylow 2-subgroup abelian」は「L 内の任意の 2-subgroup が
abelian」と同値で, 後者の方が帰納法 (`Subgroup` の transitivity による継承) で扱い
やすい. Lean では後者 (`hL2abelian`) を採用. 呼び出し側 (Thm 7.5 等) では一行で
変換可能.

**Aut(E) ≅ GL(n, ZMod p)** bridge は Thm 7.5 で初めて必要となる (ノート設計判断 (3)). -/

-- `Neg (SpecialLinearGroup (Fin 2) F)` のための `Fact (Even 2)`.
private instance instFactEvenFinTwo : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩

/-- **Isaacs Lem 7.4** (mmd L3765): `F` field, characteristic ≠ 2 ⇒ `SL(2, F)`
の唯一 involution は `-1` (= `-I`).

Isaacs 原本の "`q` odd" は本質的に `char F ≠ 2` (= `(2 : F) ≠ 0`) の特殊化.
`F = ZMod q` (`q` 奇素数冪) では `(2 : ZMod q) ≠ 0`.

**proof 戦略**: `M := ↑ₘt`, `M² = I`, `det M = 1`. 4 entries `a = M 0 0`,
`b = M 0 1`, `c = M 1 0`, `d = M 1 1` で:

* `M² = I` の (0,1) entry: `b(a+d) = 0`.
* `M² = I` の (1,0) entry: `c(a+d) = 0`.
* `M² = I` の (0,0) entry: `a² + bc = 1`.
* `M² = I` の (1,1) entry: `bc + d² = 1`.
* `det M = 1`: `ad - bc = 1`.

`a + d = 0` の場合: `det + (0,0)entry` から `a² - 1 = -1 - a² + (a² + bc) - bc - 0 = -1`,
即ち `2 = 0`, char ≠ 2 と矛盾. 従って `a + d ≠ 0`, よって `b = c = 0`.
`a² = 1` かつ `a · d = 1`, `a = d` で `a = ±1`. `t ≠ 1` から `a = -1`, `d = -1`. -/
theorem sl2_unique_involution
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {t : Matrix.SpecialLinearGroup (Fin 2) F}
    (ht_sq : t ^ 2 = 1) (ht_ne : t ≠ 1) :
    t = -1 := by
  -- 行列レベルで議論する: M := t.val
  set M : Matrix (Fin 2) (Fin 2) F := t.val with hM_def
  -- 1) M * M = I (from t ^ 2 = 1)
  have hM_sq : M * M = 1 := by
    have h := congrArg Subtype.val ht_sq
    simpa [sq, hM_def, Matrix.SpecialLinearGroup.coe_mul,
           Matrix.SpecialLinearGroup.coe_one] using h
  -- 2) det M = 1
  have hM_det : M.det = 1 := t.property
  -- 3) 4 entries
  set a := M 0 0
  set b := M 0 1
  set c := M 1 0
  set d := M 1 1
  -- det equation
  have hdet : a * d - b * c = 1 := by
    have h := Matrix.det_fin_two M
    rw [hM_det] at h
    linear_combination -h
  -- M² entries (from M * M = 1)
  have h00 : a * a + b * c = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hM_sq
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
  have h01 : a * b + b * d = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hM_sq
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
  have h10 : c * a + d * c = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hM_sq
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
  have h11 : c * b + d * d = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) hM_sq
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
  -- b * (a + d) = 0, c * (a + d) = 0
  have hb_ad : b * (a + d) = 0 := by linear_combination h01
  have hc_ad : c * (a + d) = 0 := by linear_combination h10
  -- a + d ≠ 0 (would imply 2 = 0)
  have had_ne : a + d ≠ 0 := by
    intro had
    apply h2
    linear_combination -hdet - h00 + a * had
  -- a + d ≠ 0 ⇒ b = c = 0
  have hb_zero : b = 0 :=
    (mul_eq_zero.mp hb_ad).resolve_right had_ne
  have hc_zero : c = 0 :=
    (mul_eq_zero.mp hc_ad).resolve_right had_ne
  -- After b = c = 0: a * d = 1, a² = 1
  have had_eq_one : a * d = 1 := by linear_combination hdet + b * hc_zero
  have ha_sq : a * a = 1 := by linear_combination h00 - b * hc_zero
  -- a ≠ 0 (since a² = 1)
  have ha_ne : a ≠ 0 := by
    intro hae
    apply one_ne_zero (α := F)
    linear_combination -ha_sq + a * hae
  -- d = a
  have hd_eq_a : d = a := by
    have h : a * (d - a) = 0 := by linear_combination had_eq_one - ha_sq
    have hda : d - a = 0 := (mul_eq_zero.mp h).resolve_left ha_ne
    linear_combination hda
  -- (a - 1) * (a + 1) = a² - 1 = 0
  have h_factor : (a - 1) * (a + 1) = 0 := by linear_combination ha_sq
  rcases mul_eq_zero.mp h_factor with h_pos | h_neg
  · -- a = 1 case: t = I, contradicts t ≠ 1
    exfalso
    apply ht_ne
    have ha_one : a = 1 := by linear_combination h_pos
    have hd_one : d = 1 := by rw [hd_eq_a]; exact ha_one
    have hM_eq : M = !![(1 : F), 0; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact ha_one
      · exact hb_zero
      · exact hc_zero
      · exact hd_one
    have hone_val : ((1 : Matrix.SpecialLinearGroup (Fin 2) F).val
        : Matrix (Fin 2) (Fin 2) F) = !![(1 : F), 0; 0, 1] := by
      rw [Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    exact Subtype.ext (hM_eq.trans hone_val.symm)
  · -- a = -1 case: t = -I
    have ha_neg : a = -1 := by linear_combination h_neg
    have hd_neg : d = -1 := by rw [hd_eq_a]; exact ha_neg
    have hM_eq : M = !![(-1 : F), 0; 0, -1] := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact ha_neg
      · exact hb_zero
      · exact hc_zero
      · exact hd_neg
    have hneg_val : ((-1 : Matrix.SpecialLinearGroup (Fin 2) F).val
        : Matrix (Fin 2) (Fin 2) F) = !![(-1 : F), 0; 0, -1] := by
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.neg_apply]
    exact Subtype.ext (hM_eq.trans hneg_val.symm)

private theorem card_sl2_mul_units_eq_card_gl2_zmod_prime
    {p : ℕ} [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) * (p - 1) =
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by
  let detGL : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) →* (ZMod p)ˣ :=
    Matrix.GeneralLinearGroup.det
  let toGLSL : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod p) :=
    Matrix.SpecialLinearGroup.toGL
  have htoGL_range_eq_ker : toGLSL.range = detGL.ker := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      simp [detGL, toGLSL]
    · intro hg
      rw [MonoidHom.mem_ker] at hg
      have hgdet : ((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
        have := congrArg Units.val hg
        simpa [detGL, Matrix.GeneralLinearGroup.val_det_apply] using this
      refine ⟨⟨((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)), hgdet⟩, ?_⟩
      exact Units.ext rfl
  have htop_map_eq_range :
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))).map toGLSL =
        toGLSL.range := by
    ext g
    simp [toGLSL]
  have hcard_SL_range :
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) =
        Nat.card toGLSL.range := by
    calc
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
          = Nat.card (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) := by
            rw [Subgroup.card_top]
      _ = Nat.card ((⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))).map
            toGLSL) := by
            exact Nat.card_congr
              (Subgroup.equivMapOfInjective
                (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) toGLSL
                Matrix.SpecialLinearGroup.toGL_injective).toEquiv
      _ = Nat.card toGLSL.range := by
            rw [htop_map_eq_range]
  have hcard_SL_ker :
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) =
        Nat.card detGL.ker := by
    rw [hcard_SL_range, htoGL_range_eq_ker]
  have hdet_range_top : detGL.range = ⊤ := by
    ext u
    constructor
    · intro _
      trivial
    · intro _
      let A : Matrix (Fin 2) (Fin 2) (ZMod p) := !![(u : ZMod p), 0; 0, 1]
      have hdetA_ne : A.det ≠ 0 := by
        simp [A, Matrix.det_fin_two, u.ne_zero]
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdetA_ne, ?_⟩
      ext
      simp [detGL, A, Matrix.det_fin_two]
  have hcard_range : Nat.card detGL.range = p - 1 := by
    rw [hdet_range_top, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units,
      ZMod.card]
  have hker_mul_range :
      Nat.card detGL.ker * Nat.card detGL.range =
        Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by
    rw [← Subgroup.index_ker detGL]
    exact Subgroup.card_mul_index detGL.ker
  calc
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) * (p - 1)
        = Nat.card detGL.ker * Nat.card detGL.range := by
          rw [hcard_SL_ker, hcard_range]
    _ = Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := hker_mul_range

private theorem card_gl2_zmod_prime {p : ℕ} [Fact p.Prime] :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) =
      p * (p - 1) * (p - 1) * (p + 1) := by
  rw [Matrix.card_GL_field (n := 2)]
  rw [ZMod.card]
  simp only [Fin.prod_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
    Nat.mod_succ, pow_one]
  have h_sq_sub_one : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    simpa using Nat.sq_sub_sq p 1
  have h_sq_sub_self : p ^ 2 - p = p * (p - 1) := by
    calc
      p ^ 2 - p = p * p - p * 1 := by rw [pow_two, mul_one]
      _ = p * (p - 1) := (Nat.mul_sub_left_distrib p p 1).symm
  rw [h_sq_sub_one, h_sq_sub_self]
  ring

/-- A `p`-subgroup of `GL(2,p)` has order at most `p`.

This is the formal version of the cardinality step in Isaacs Thm 7.5 after embedding the
faithful action on an elementary-abelian group of order `p²` into `GL(2,p)`. -/
theorem gl2_pSubgroup_card_le_prime {p : ℕ} [Fact p.Prime]
    (P : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) (hP : IsPGroup p P) :
    Nat.card P ≤ p := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rcases n with _ | n
  · rw [hn, pow_zero]
    exact (Fact.out : p.Prime).pos
  rcases n with _ | n
  · rw [hn, pow_one]
  · exfalso
    have hp2_dvd_card : p ^ 2 ∣ Nat.card P := by
      rw [hn]
      exact Nat.pow_dvd_pow p (by omega : 2 ≤ n + 2)
    have hp2_dvd_gl :
        p ^ 2 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :=
      hp2_dvd_card.trans P.card_subgroup_dvd_card
    rw [card_gl2_zmod_prime (p := p)] at hp2_dvd_gl
    have hp_not_dvd_pred : ¬ p ∣ p - 1 := by
      intro h
      have hp_pos : 0 < p := (Fact.out : p.Prime).pos
      have hpred_pos : 0 < p - 1 := by
        have hp_two : 2 ≤ p := (Fact.out : p.Prime).two_le
        omega
      have hle : p ≤ p - 1 := Nat.le_of_dvd hpred_pos h
      omega
    have hp_not_dvd_succ : ¬ p ∣ p + 1 := by
      intro h
      have hp_dvd_one : p ∣ 1 := by
        have hsub : p ∣ (p + 1) - p := Nat.dvd_sub h (dvd_refl p)
        have hsub_eq : (p + 1) - p = 1 := by omega
        rwa [hsub_eq] at hsub
      exact (Fact.out : p.Prime).not_dvd_one hp_dvd_one
    have hp_not_dvd_rest : ¬ p ∣ (p - 1) * (p - 1) * (p + 1) := by
      intro h
      rcases (Fact.out : p.Prime).dvd_mul.mp h with hleft | hsucc
      · rcases (Fact.out : p.Prime).dvd_mul.mp hleft with hpred | hpred
        · exact hp_not_dvd_pred hpred
        · exact hp_not_dvd_pred hpred
      · exact hp_not_dvd_succ hsucc
    have hp_dvd_rest : p ∣ (p - 1) * (p - 1) * (p + 1) := by
      have hp_pos : 0 < p := (Fact.out : p.Prime).pos
      have hmul : p * p ∣ p * ((p - 1) * (p - 1) * (p + 1)) := by
        simpa [pow_two, mul_assoc] using hp2_dvd_gl
      exact Nat.dvd_of_mul_dvd_mul_left hp_pos hmul
    exact hp_not_dvd_rest hp_dvd_rest

/-- If a Sylow `p`-subgroup has order at most `p` and is not normal, then `O_p(G)=1`.

This is the `O_p(G)=1` reduction in Isaacs Thm 7.5 after the faithful action has embedded
the group into `GL(2,p)` and `gl2_pSubgroup_card_le_prime` has bounded `|P|`. -/
theorem opCore_eq_bot_of_sylow_card_le_prime_of_not_normal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP_card : Nat.card (P : Subgroup G) ≤ p)
    (hP_not_normal : ¬ (P : Subgroup G).Normal) :
    OddOrder.Isaacs.Ch01.opCore p G = ⊥ := by
  by_contra hOp_ne_bot
  have hOp_le_P : OddOrder.Isaacs.Ch01.opCore p G ≤ (P : Subgroup G) :=
    OddOrder.Isaacs.Ch01.opCore_le P
  have hOp_p : IsPGroup p (OddOrder.Isaacs.Ch01.opCore p G) :=
    OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hOp_p
  have hOp_gt_one : 1 < Nat.card (OddOrder.Isaacs.Ch01.opCore p G) :=
    (Subgroup.one_lt_card_iff_ne_bot (OddOrder.Isaacs.Ch01.opCore p G)).mpr hOp_ne_bot
  have hp_le_Op : p ≤ Nat.card (OddOrder.Isaacs.Ch01.opCore p G) := by
    cases n with
    | zero =>
        have hcard_one : Nat.card (OddOrder.Isaacs.Ch01.opCore p G) = 1 := by
          simpa using hn
        omega
    | succ n =>
        rw [hn, pow_succ]
        have hpow_pos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
        simpa [mul_comm] using Nat.le_mul_of_pos_right p hpow_pos
  have hOp_card_le_P : Nat.card (OddOrder.Isaacs.Ch01.opCore p G) ≤
      Nat.card (P : Subgroup G) :=
    Subgroup.card_le_of_le hOp_le_P
  have hP_card_eq : Nat.card (P : Subgroup G) = p :=
    le_antisymm hP_card (hp_le_Op.trans hOp_card_le_P)
  have hOp_card_eq : Nat.card (OddOrder.Isaacs.Ch01.opCore p G) = p :=
    le_antisymm (hOp_card_le_P.trans hP_card) hp_le_Op
  have hOp_eq_P : OddOrder.Isaacs.Ch01.opCore p G = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hOp_le_P (by rw [hP_card_eq, hOp_card_eq])
  apply hP_not_normal
  rw [← hOp_eq_P]
  infer_instance

/-- Hall-Higman final-step form for Isaacs Thm 7.5.

If the usual `p`-core is trivial, then Hall-Higman can be applied with
`π = {p}'`, so the `p'`-core is self-centralizing. -/
theorem centralizer_oPiCore_compl_le_of_opCore_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp : OddOrder.Isaacs.Ch01.opCore p G = ⊥) :
    Subgroup.centralizer
        (OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G : Set G) ≤
      OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G := by
  classical
  set π' : Set ℕ := {q | q ∉ ({p} : Set ℕ)} with hπ'_def
  haveI hPiSepCompl : OddOrder.Isaacs.Ch03.IsPiSeparable π' G :=
    OddOrder.Isaacs.Ch03.isPiSeparable_compl ({p} : Set ℕ) G inferInstance
  have hCoreCompl : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ π'} G = ⊥ := by
    rw [show ({q | q ∉ π'} : Set ℕ) = ({p} : Set ℕ) by
      ext q
      simp [π']]
    rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p]
    exact hOp
  simpa [π', hπ'_def] using
    (OddOrder.Isaacs.Ch03.hall_higman_1_2_3 (G := G) π' hCoreCompl)

/-- A Sylow `p`-subgroup contained in `O_{p'}(G)` is trivial.

This is the final coprime contradiction in Isaacs Thm 7.5 after Hall-Higman puts
`C_G(O_{p'}(G))` inside `O_{p'}(G)`. -/
theorem sylow_eq_bot_of_le_oPiCore_compl
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP_le :
      (P : Subgroup G) ≤
        OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G) :
    (P : Subgroup G) = ⊥ := by
  have hP_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) (P : Subgroup G) :=
    OddOrder.Isaacs.Ch04.isPiGroup_singleton_of_isPGroup P.isPGroup'
  have hL_pi :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)}
        (OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G) :=
    OddOrder.Isaacs.Ch03.oPiCore.isPiGroup {q | q ∉ ({p} : Set ℕ)}
  have hP_pi' :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} (P : Subgroup G) :=
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le hP_le hL_pi
  have hcop : Nat.Coprime (Nat.card (P : Subgroup G)) (Nat.card (P : Subgroup G)) :=
    OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne' hP_pi hP_pi'
  have hInf : (P : Subgroup G) ⊓ (P : Subgroup G) = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  simpa using hInf

private theorem card_sl2_zmod_prime {p : ℕ} [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) =
      p * (p - 1) * (p + 1) := by
  have hp_pred_pos : 0 < p - 1 := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  apply Nat.mul_right_cancel hp_pred_pos
  calc
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) * (p - 1)
        = Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :=
          card_sl2_mul_units_eq_card_gl2_zmod_prime (p := p)
    _ = p * (p - 1) * (p - 1) * (p + 1) := card_gl2_zmod_prime (p := p)
    _ = (p * (p - 1) * (p + 1)) * (p - 1) := by ring

private theorem prime_dvd_pred_or_succ_of_dvd_prime_mul_pred_succ
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq_ne_p : q ≠ p)
    (h : q ∣ p * (p - 1) * (p + 1)) :
    q ∣ p - 1 ∨ q ∣ p + 1 := by
  have h' : q ∣ p * ((p - 1) * (p + 1)) := by
    simpa [mul_assoc] using h
  rcases (hq.dvd_mul.mp h') with hq_dvd_p | hq_dvd_rest
  · rcases (Nat.dvd_prime hp).mp hq_dvd_p with hq_eq_one | hq_eq_p
    · exact (hq.ne_one hq_eq_one).elim
    · exact (hq_ne_p hq_eq_p).elim
  · exact hq.dvd_mul.mp hq_dvd_rest

private theorem prime_not_dvd_pred_and_succ_of_ne_two
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq_ne_two : q ≠ 2) :
    ¬ (q ∣ p - 1 ∧ q ∣ p + 1) := by
  rintro ⟨hq_dvd_pred, hq_dvd_succ⟩
  have hq_dvd_two : q ∣ 2 := by
    have hsub : q ∣ (p + 1) - (p - 1) := Nat.dvd_sub hq_dvd_succ hq_dvd_pred
    have hsub_eq : (p + 1) - (p - 1) = 2 := by
      have hp2 : 2 ≤ p := hp.two_le
      omega
    rwa [hsub_eq] at hsub
  rcases (Nat.dvd_prime Nat.prime_two).mp hq_dvd_two with hq_eq_one | hq_eq_two
  · exact hq.ne_one hq_eq_one
  · exact hq_ne_two hq_eq_two

private theorem prime_power_dvd_pred_or_succ_of_dvd_prime_mul_pred_succ
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hq_ne_p : q ≠ p) (hq_ne_two : q ≠ 2)
    (hn_qpow : ∃ k, n = q ^ k) (hq_dvd_n : q ∣ n)
    (hn_dvd : n ∣ p * (p - 1) * (p + 1)) :
    n ∣ p - 1 ∨ n ∣ p + 1 := by
  rcases hn_qpow with ⟨k, rfl⟩
  by_cases hk0 : k = 0
  · left
    simp [hk0]
  have hq_not_dvd_p : ¬ q ∣ p := by
    intro hq_dvd_p
    rcases (Nat.dvd_prime hp).mp hq_dvd_p with hq_eq_one | hq_eq_p
    · exact hq.ne_one hq_eq_one
    · exact hq_ne_p hq_eq_p
  have hq_dvd_formula : q ∣ p * (p - 1) * (p + 1) :=
    hq_dvd_n.trans hn_dvd
  have hq_dvd_pred_or_succ : q ∣ p - 1 ∨ q ∣ p + 1 :=
    prime_dvd_pred_or_succ_of_dvd_prime_mul_pred_succ hp hq hq_ne_p hq_dvd_formula
  have hq_not_both : ¬ (q ∣ p - 1 ∧ q ∣ p + 1) :=
    prime_not_dvd_pred_and_succ_of_ne_two hp hq hq_ne_two
  rcases hq_dvd_pred_or_succ with hq_dvd_pred | hq_dvd_succ
  · left
    have hq_not_dvd_succ : ¬ q ∣ p + 1 :=
      fun hq_dvd_succ => hq_not_both ⟨hq_dvd_pred, hq_dvd_succ⟩
    have hq_not_dvd_p_succ : ¬ q ∣ p * (p + 1) := by
      intro hq_dvd_p_succ
      rcases (hq.dvd_mul.mp hq_dvd_p_succ) with hq_dvd_p | hq_dvd_succ
      · exact hq_not_dvd_p hq_dvd_p
      · exact hq_not_dvd_succ hq_dvd_succ
    have hcop : Nat.Coprime (q ^ k) (p * (p + 1)) :=
      (Nat.Prime.coprime_pow_of_not_dvd hq hq_not_dvd_p_succ).symm
    have hn_dvd_rearr : q ^ k ∣ (p - 1) * (p * (p + 1)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hn_dvd
    exact (hcop.dvd_mul_right).mp hn_dvd_rearr
  · right
    have hq_not_dvd_pred : ¬ q ∣ p - 1 :=
      fun hq_dvd_pred => hq_not_both ⟨hq_dvd_pred, hq_dvd_succ⟩
    have hq_not_dvd_p_pred : ¬ q ∣ p * (p - 1) := by
      intro hq_dvd_p_pred
      rcases (hq.dvd_mul.mp hq_dvd_p_pred) with hq_dvd_p | hq_dvd_pred
      · exact hq_not_dvd_p hq_dvd_p
      · exact hq_not_dvd_pred hq_dvd_pred
    have hcop : Nat.Coprime (q ^ k) (p * (p - 1)) :=
      (Nat.Prime.coprime_pow_of_not_dvd hq hq_not_dvd_p_pred).symm
    have hn_dvd_rearr : q ^ k ∣ (p + 1) * (p * (p - 1)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hn_dvd
    exact (hcop.dvd_mul_right).mp hn_dvd_rearr

private theorem pgroup_action_card_ge_prime_succ_of_moved
    {p : ℕ} [Fact p.Prime]
    {A X : Type*} [Group A] [Group X] [MulDistribMulAction A X] [Finite X]
    (hA : IsPGroup p A) {a : A} {x : X} (hmove : a • x ≠ x) :
    p + 1 ≤ Nat.card X := by
  have hx_ne_one : x ≠ 1 := by
    intro hx
    apply hmove
    simp [hx]
  have horbit_ne_one : ∀ y : MulAction.orbit A x, (y : X) ≠ 1 := by
    intro y hy
    rcases y.2 with ⟨b, hb⟩
    apply hx_ne_one
    calc
      x = b⁻¹ • (b • x) := by simp
      _ = b⁻¹ • (y : X) := congrArg (fun z : X => b⁻¹ • z) hb
      _ = b⁻¹ • (1 : X) := by rw [hy]
      _ = 1 := by simp
  haveI : Nontrivial (MulAction.orbit A x) := by
    refine ⟨⟨⟨x, MulAction.mem_orbit_self x⟩, ⟨a • x, MulAction.mem_orbit x a⟩, ?_⟩⟩
    intro h
    exact hmove (Subtype.ext_iff.mp h).symm
  have horbit_card_gt_one : 1 < Nat.card (MulAction.orbit A x) :=
    Finite.one_lt_card
  obtain ⟨k, hk⟩ := hA.card_orbit x
  have hk_pos : 0 < k := by
    by_contra hk_not_pos
    have hk_zero : k = 0 := Nat.eq_zero_of_not_pos hk_not_pos
    have : Nat.card (MulAction.orbit A x) = 1 := by
      rw [hk, hk_zero, pow_zero]
    omega
  have hp_le_orbit : p ≤ Nat.card (MulAction.orbit A x) := by
    rw [hk]
    cases k with
    | zero => omega
    | succ k =>
        rw [pow_succ]
        simpa [mul_comm] using
          Nat.le_mul_of_pos_right p (Nat.pow_pos (Fact.out : p.Prime).pos)
  let f : Option (MulAction.orbit A x) → X
    | none => 1
    | some y => y
  have hf : Function.Injective f := by
    intro u v huv
    cases u with
    | none =>
        cases v with
        | none => rfl
        | some y =>
            exfalso
            exact horbit_ne_one y huv.symm
    | some y =>
        cases v with
        | none =>
            exfalso
            exact horbit_ne_one y huv
        | some z =>
            exact congrArg some (Subtype.ext huv)
  have hoption_le : Nat.card (Option (MulAction.orbit A x)) ≤ Nat.card X :=
    Nat.card_le_card_of_injective f hf
  rw [Finite.card_option] at hoption_le
  exact (Nat.add_le_add_right hp_le_orbit 1).trans hoption_le

private theorem cyclic_two_group_mulAut_isPGroup
    {G : Type*} [Group G] [Finite G] [IsCyclic G] (hG : IsPGroup 2 G) :
    IsPGroup 2 (MulAut G) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hG
  rcases k with _ | k
  · apply IsPGroup.of_card (p := 2) (n := 0)
    rw [IsCyclic.card_mulAut, hk, pow_zero, Nat.totient_one]
  · apply IsPGroup.of_card (p := 2) (n := k)
    rw [IsCyclic.card_mulAut, hk, Nat.totient_prime_pow_succ Nat.prime_two]
    norm_num

private theorem zmod_two_power_half_order_two {k : ℕ} (hk : 0 < k) :
    orderOf (Multiplicative.ofAdd ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k))) = 2 := by
  rw [orderOf_ofAdd_eq_addOrderOf]
  rw [ZMod.addOrderOf_coe (2 ^ (k - 1)) (pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0))]
  rw [Nat.gcd_eq_right (pow_dvd_pow 2 (Nat.sub_le k 1))]
  have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [hpow]
  exact Nat.mul_div_right _ (pow_pos (by norm_num : 0 < 2) _)

private theorem zmod_eq_two_power_half_order_two {n k : ℕ} (hn : n = 2 ^ k) (hk : 0 < k) :
    orderOf (Multiplicative.ofAdd ((2 ^ (k - 1) : ℕ) : ZMod n)) = 2 := by
  subst n
  exact zmod_two_power_half_order_two (k := k) hk

private theorem isCyclic_pi_of_subsingleton
    {ι : Type*} [Subsingleton ι]
    {M : ι → Type*} [∀ i, Group (M i)] [∀ i, IsCyclic (M i)] :
    IsCyclic (∀ i, M i) := by
  by_cases hι : Nonempty ι
  · classical
    rcases hι with ⟨i⟩
    haveI : Unique ι := uniqueOfSubsingleton i
    let e : (∀ i, M i) ≃* M default :=
      { toEquiv := Equiv.piUnique M
        map_mul' := fun _ _ => rfl }
    exact e.isCyclic.mpr inferInstance
  · haveI : IsEmpty ι := ⟨fun i => hι ⟨i⟩⟩
    exact isCyclic_of_subsingleton

private theorem isCyclic_of_comm_two_group_unique_order_two
    {G : Type*} [CommGroup G] [Finite G] (hG : IsPGroup 2 G)
    (huniq : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y) :
    IsCyclic G := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι, _, n, hn_gt, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  let T := (i : ι) → Multiplicative (ZMod (n i))
  have hn_pow : ∀ i : ι, ∃ k, n i = 2 ^ k := by
    intro i
    let gen : T := Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (n i)))
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hG) (e.symm gen)
    refine ⟨k, ?_⟩
    have horder : orderOf (e.symm gen) = n i := by
      rw [← e.orderOf_eq (e.symm gen)]
      simp [gen, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
    exact horder.symm.trans hk
  have hι_sub : Subsingleton ι := by
    by_contra hnot
    haveI : Nontrivial ι := not_subsingleton_iff_nontrivial.mp hnot
    obtain ⟨i, j, hij⟩ := exists_pair_ne ι
    obtain ⟨ki, hki⟩ := hn_pow i
    obtain ⟨kj, hkj⟩ := hn_pow j
    have hki_pos : 0 < ki := by
      cases ki with
      | zero =>
          have : 1 < (1 : ℕ) := by simpa [hki] using hn_gt i
          omega
      | succ ki => exact Nat.succ_pos _
    have hkj_pos : 0 < kj := by
      cases kj with
      | zero =>
          have : 1 < (1 : ℕ) := by simpa [hkj] using hn_gt j
          omega
      | succ kj => exact Nat.succ_pos _
    let ai : Multiplicative (ZMod (n i)) :=
      Multiplicative.ofAdd ((2 ^ (ki - 1) : ℕ) : ZMod (n i))
    let aj : Multiplicative (ZMod (n j)) :=
      Multiplicative.ofAdd ((2 ^ (kj - 1) : ℕ) : ZMod (n j))
    have hai_order : orderOf ai = 2 := by
      simpa [ai] using zmod_eq_two_power_half_order_two (n := n i) (k := ki) hki hki_pos
    have haj_order : orderOf aj = 2 := by
      simpa [aj] using zmod_eq_two_power_half_order_two (n := n j) (k := kj) hkj hkj_pos
    let xi : T := Pi.mulSingle i ai
    let xj : T := Pi.mulSingle j aj
    have hxi_order : orderOf xi = 2 := by
      simpa [xi, hai_order] using
        (orderOf_piMulSingle
          (M := fun t : ι => Multiplicative (ZMod (n t))) (i := i) (g := ai))
    have hxj_order : orderOf xj = 2 := by
      simpa [xj, haj_order] using
        (orderOf_piMulSingle
          (M := fun t : ι => Multiplicative (ZMod (n t))) (i := j) (g := aj))
    have hxi_ne_xj : xi ≠ xj := by
      intro h
      have hi_coord := congrFun h i
      have hai_ne_one : ai ≠ 1 := by
        intro hai
        have : orderOf ai = 1 := by simp [hai]
        omega
      apply hai_ne_one
      simpa [xi, xj, hij] using hi_coord
    have hpre_eq : e.symm xi = e.symm xj :=
      huniq (e.symm xi) (e.symm xj)
        (by
          rw [← e.orderOf_eq (e.symm xi)]
          simpa using hxi_order)
        (by
          rw [← e.orderOf_eq (e.symm xj)]
          simpa using hxj_order)
    exact hxi_ne_xj (by simpa using congrArg e hpre_eq)
  have htarget : IsCyclic T := by
    haveI : Subsingleton ι := hι_sub
    exact isCyclic_pi_of_subsingleton
  exact e.isCyclic.mpr htarget

/-! ### Isaacs Lem 7.3 — GL(2,p) 補題 (formal statement + proof)

**Isaacs Lem 7.3** (mmd L3739): `p ≠ 2` prime, `P ≤ GL(2, ZMod p)` p-subgroup,
`L ≤ GL(2, ZMod p)`, `P ≤ N(L)`, `(|L|, p) = 1`, `L` の Sylow 2-subgroup abelian
⇒ `P ≤ C_G(L)`.

**証明戦略** (Isaacs p.204):
1. `|L|`-strong induction. IH: 任意の (より小さい) P-invariant subgroup `M ⊊ L` で
   `P ≤ C(M)` が成立.
2. q | `|L : C_L(P)|` を取り, P-invariant Sylow q-subgroup `Q ≤ L` を
   `exists_aInvariant_sylow` (Ch.3 Thm 3.23(a)) で取得. IH より `Q = L`, 即ち L は q-群.
3. `[L,P] < L` なら IH + Lem 4.29 (coprime ⇒ `[L,P,P] = [L,P]`) で `[L,P] = 1`, 終了.
   よって `[L,P] = L` を仮定可. このとき `L ⊆ G' ⊆ SL(2,p)` (det homom が abelian quotient).
4. `q = 2`: L abelian (仮定) + Lem 7.4 (L 内 unique involution = -I) ⇒ L cyclic 2-群.
   Aut(cyclic 2-群) は 2-群で p-群 P の作用は trivial.
5. `q` odd: `|L|` は q-冪 で `|SL(2,p)| = p(p-1)(p+1)` を割る. `q ≠ p` で `q | (p-1)(p+1)`.
   `q` odd かつ `gcd(p-1, p+1) ∣ 2` より `q | (p-1)` または `q | (p+1)` の片方のみ.
   よって `|L| ≤ p+1`. P が L に非自明作用なら orbit が p 以上を持ち `|L| ≥ p+1`,
   即ち `|L| = p+1` で `|L|` even. 矛盾 (q odd).

Lean proof は [`lem73_aux`](#) に集約し、公開 theorem
`gl2_pSubgroup_centralizes_of_normalizes` は strong-induction bound を `Nat.card L` に
特殊化する薄い wrapper. -/

/-- **Isaacs Lemma 7.3 (`|L|`-induction aux)**: `Nat.card L ≤ n` をパラメータに取り,
強い帰納法のための補助 form. p, P は外側で固定し L のみ帰納法で動かす. -/
private theorem lem73_aux
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))}
    (hPp : IsPGroup p P) :
    ∀ (n : ℕ) {L : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))}
      (_hPnorm : P ≤ Subgroup.normalizer (L : Set _))
      (_hLcop : ¬ p ∣ Nat.card L)
      (_hL2abelian : ∀ S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
        S ≤ L → IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x),
      Nat.card L ≤ n →
      P ≤ Subgroup.centralizer (L : Set _) := by
  intro n
  induction n with
  | zero =>
    -- n = 0 ⇒ Nat.card L = 0. 一方 L : Subgroup G で G = GL(2,ZMod p) は finite, よって
    -- L も finite で `Nat.card L ≥ 1`. 矛盾.
    intro L _ _ _ hL_le
    exfalso
    have hL_pos : 0 < Nat.card L := Nat.card_pos
    omega
  | succ n ih =>
    intro L hPnorm hLcop hL2abelian hL_le
    -- ## Step 1a: 共役作用 φ : ↥P →* MulAut ↥L
    -- `P ≤ N(L)` ⇒ `↥P` を inclusion で `↥(N(L))` に埋め, normalizerMonoidHom で MulAut ↥L へ.
    let φ : ↥P →* MulAut ↥L :=
      L.normalizerMonoidHom.comp (Subgroup.inclusion hPnorm)
    -- ## Step 1b: (|P|, |L|) coprime
    -- P が p-群 ⇒ |P| = p^k. 仮定 `¬ p ∣ |L|` から `Nat.Coprime p (Nat.card L)`.
    have hp_prime : p.Prime := Fact.out
    have hp_coprime_L : Nat.Coprime p (Nat.card ↥L) :=
      (Nat.Prime.coprime_iff_not_dvd hp_prime).mpr hLcop
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    have hCop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥L) := by
      rw [hk]; exact hp_coprime_L.pow_left k
    -- ## Step 1c: P が solvable (p-群 ⇒ nilpotent ⇒ solvable)
    haveI hP_nilpotent : Group.IsNilpotent ↥P := IsPGroup.isNilpotent hPp
    haveI hP_solvable : IsSolvable ↥P := inferInstance
    -- ## Step 1d: 自明分岐 — `L ≤ C_G(P)` なら結論直結 (centralizer の対称性)
    -- Isaacs proof は「q | |L:C_L(P)| を取る」ところから始まり, 暗黙に `C_L(P) ⊊ L` を仮定.
    -- C_L(P) = L (即ち L ≤ C_G(P)) なら index = 1 で q が取れないため, 別途処理する.
    by_cases hL_in_C : L ≤ Subgroup.centralizer (P : Set _)
    · -- L ≤ C(P) ⇔ P ≤ C(L) (centralizer の対称性, `Subgroup.le_centralizer_iff`).
      exact Subgroup.le_centralizer_iff.mp hL_in_C
    · -- L ⊄ C(P): C_L(P) = L ⊓ C_G(P) は L の真部分群. q | |L:C_L(P)| が取れる.
      -- ## Step 1e: C_L_P := L ⊓ centralizer(P) の真部分群性
      set C_L_P : Subgroup _ := L ⊓ Subgroup.centralizer (P : Set _) with hC_L_P_def
      have hC_le_L : C_L_P ≤ L := inf_le_left
      have hC_ne_L : C_L_P ≠ L := by
        intro h_eq
        apply hL_in_C
        rw [← h_eq]; exact inf_le_right
      have h_card_lt : Nat.card ↥C_L_P < Nat.card ↥L := by
        rcases lt_or_eq_of_le (Subgroup.card_le_of_le hC_le_L) with h | h
        · exact h
        · exact absurd (Subgroup.eq_of_le_of_card_ge hC_le_L h.ge) hC_ne_L
      -- ## Step 1f: index `|L : C_L(P)| > 1` から素因子 q を取得
      -- `Nat.card C_L_P ∣ Nat.card L` (Lagrange) + `|C_L_P| < |L|` ⇒ `|L| / |C_L_P| > 1`.
      have hC_dvd : Nat.card ↥C_L_P ∣ Nat.card ↥L := Subgroup.card_dvd_of_le hC_le_L
      have hC_pos : 0 < Nat.card ↥C_L_P := Nat.card_pos
      have h_idx_gt : 1 < Nat.card ↥L / Nat.card ↥C_L_P := by
        by_contra h_not
        have h_le_one : Nat.card ↥L / Nat.card ↥C_L_P ≤ 1 := not_lt.mp h_not
        have h_prod : Nat.card ↥L / Nat.card ↥C_L_P * Nat.card ↥C_L_P = Nat.card ↥L :=
          Nat.div_mul_cancel hC_dvd
        have h_le : Nat.card ↥L ≤ Nat.card ↥C_L_P :=
          calc Nat.card ↥L
              = Nat.card ↥L / Nat.card ↥C_L_P * Nat.card ↥C_L_P := h_prod.symm
            _ ≤ 1 * Nat.card ↥C_L_P := Nat.mul_le_mul_right _ h_le_one
            _ = Nat.card ↥C_L_P := one_mul _
        omega
      obtain ⟨q, hq_prime, hq_dvd_idx⟩ :=
        Nat.exists_prime_and_dvd (Nat.ne_of_gt h_idx_gt)
      haveI : Fact q.Prime := ⟨hq_prime⟩
      -- ## Step 1g: P-invariant Sylow q-subgroup Q of ↥L を `exists_aInvariant_sylow` で取得
      obtain ⟨Q, hQ_inv⟩ :=
        OddOrder.Isaacs.Ch04.exists_aInvariant_sylow (A := ↥P) (G := ↥L) (φ := φ) hCop
          (Or.inl hP_solvable) q
      -- ## Step 1h: Q (Sylow q of ↥L) を G_ambient = GL(2, ZMod p) の subgroup に lift.
      -- `Q' := Q.toSubgroup.map L.subtype` で「L 内で見ていた Q」を G の subgroup として復元.
      let Q' : Subgroup _ := Q.toSubgroup.map L.subtype
      -- Q' ≤ L: image of subgroup of ↥L through subtype is contained in L.
      have hQ'_le_L : Q' ≤ L := by
        rintro _ ⟨h, _, rfl⟩
        exact h.2
      -- Q' は q-群 (Q が Sylow q of ↥L で `IsPGroup` を持つ).
      have hQ'_pgroup : IsPGroup q Q' := by
        have hQ_pgroup : IsPGroup q Q.toSubgroup := Q.2
        exact hQ_pgroup.map L.subtype
      -- |Q'| = |Q.toSubgroup| (L.subtype は injective).
      have hQ'_card : Nat.card ↥Q' = Nat.card ↥Q.toSubgroup :=
        Nat.card_congr (Equiv.Set.image _ _ L.subtype_injective).symm
      -- `φ` の定義レベルでの計算: `((φ a) h).val = a.val * h.val * a.val⁻¹` (in G).
      -- これは `normalizerMonoidHom` の `MulDistribMulAction` action の `smul` から `rfl` で従う.
      have hphi_val : ∀ (a : ↥P) (h : ↥L),
          (((φ a) h : ↥L) : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
            = (a : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
              * (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
              * (a : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))⁻¹ :=
        fun _ _ => rfl
      -- ## Step 1i: P normalizes Q' (translation of IsAInvariant via normalizerMonoidHom).
      have hPnorm_Q' : P ≤ Subgroup.normalizer (Q' : Set _) := by
        intro a ha
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · -- y ∈ Q' ⇒ a y a⁻¹ ∈ Q'.  Destructure y = L.subtype h with rfl.
          rintro ⟨h, hhQ, rfl⟩
          -- Goal: a * L.subtype h * a⁻¹ ∈ Q'.
          have hsmul_mem : (φ ⟨a, ha⟩) h ∈ Q.toSubgroup := hQ_inv.smul_mem ⟨a, ha⟩ hhQ
          refine ⟨(φ ⟨a, ha⟩) h, hsmul_mem, ?_⟩
          -- L.subtype ((φ a) h) = a * L.subtype h * a⁻¹ by hphi_val.
          exact hphi_val ⟨a, ha⟩ h
        · -- a y a⁻¹ ∈ Q' ⇒ y ∈ Q'.
          rintro ⟨h, hhQ, hh_eq⟩
          -- hh_eq : L.subtype h = a * y * a⁻¹.  Apply (φ a)⁻¹ to h.
          have hsmul_mem : (φ ⟨a, ha⟩)⁻¹ h ∈ Q.toSubgroup := hQ_inv.inv_smul_mem ⟨a, ha⟩ hhQ
          refine ⟨(φ ⟨a, ha⟩)⁻¹ h, hsmul_mem, ?_⟩
          -- Apply hphi_val to (φ a)⁻¹ h.
          have h_aux := hphi_val ⟨a, ha⟩ ((φ ⟨a, ha⟩)⁻¹ h)
          -- Simplify (φ a) ((φ a)⁻¹ h) = h on LHS, then convert L.subtype h ↔ ↑h via coe_subtype.
          rw [show (φ ⟨a, ha⟩) ((φ ⟨a, ha⟩)⁻¹ h) = h from MulAut.apply_inv_self _ _ _]
            at h_aux
          simp only [Subgroup.coe_subtype] at hh_eq
          -- h_aux : ↑h = a * ↑((φ a)⁻¹ h) * a⁻¹.   hh_eq : ↑h = a * y * a⁻¹.
          rw [hh_eq] at h_aux
          -- h_aux : a * y * a⁻¹ = a * ↑((φ a)⁻¹ h) * a⁻¹.  Cancel.
          have := mul_right_cancel h_aux
          exact (mul_left_cancel this).symm
      -- ## Step 1j: Q' = L vs Q' ⊊ L の場合分け. Q' ⊊ L だと IH + 矛盾, つまり L が q-群.
      have hQ'_eq_L : Q' = L := by
        by_contra hne
        have hQ'_lt_L : Q' < L := lt_of_le_of_ne hQ'_le_L hne
        have hQ'_card_lt_L : Nat.card ↥Q' < Nat.card ↥L := by
          rcases lt_or_eq_of_le (Subgroup.card_le_of_le hQ'_le_L) with h | h
          · exact h
          · exact absurd (Subgroup.eq_of_le_of_card_ge hQ'_le_L h.ge) hne
        have hQ'_card_le_n : Nat.card ↥Q' ≤ n := by omega
        -- IH 仮説の準備.
        have hLcop_Q' : ¬ p ∣ Nat.card ↥Q' :=
          fun hp_dvd => hLcop (hp_dvd.trans (Subgroup.card_dvd_of_le hQ'_le_L))
        have hL2abelian_Q' :
            ∀ S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
              S ≤ Q' → IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x :=
          fun S hS hS2 => hL2abelian S (hS.trans hQ'_le_L) hS2
        -- IH 適用: P ≤ C(Q').
        have hP_cent_Q' : P ≤ Subgroup.centralizer (Q' : Set _) :=
          ih hPnorm_Q' hLcop_Q' hL2abelian_Q' hQ'_card_le_n
        -- ⇒ Q' ≤ C(P).  C_L_P = L ⊓ C(P) なので Q' ≤ C_L_P.
        have hQ'_le_C : Q' ≤ Subgroup.centralizer (P : Set _) :=
          Subgroup.le_centralizer_iff.mpr hP_cent_Q'
        have hQ'_le_C_L_P : Q' ≤ C_L_P := le_inf hQ'_le_L hQ'_le_C
        -- |Q'| ∣ |C_L_P|.
        have hQ'_dvd_C : Nat.card ↥Q' ∣ Nat.card ↥C_L_P :=
          Subgroup.card_dvd_of_le hQ'_le_C_L_P
        -- |C_L_P| ∣ |L| は hC_dvd.  div_dvd_div_left で |L|/|C_L_P| ∣ |L|/|Q'|.
        have h_div_dvd_div : Nat.card ↥L / Nat.card ↥C_L_P ∣
            Nat.card ↥L / Nat.card ↥Q' :=
          Nat.div_dvd_div_left hC_dvd hQ'_dvd_C
        -- Sylow.not_dvd_index: q ∤ Q.toSubgroup.index = |↥L|/|Q.toSubgroup| = |↥L|/|Q'|.
        have hQ_not_dvd_idx : ¬ q ∣ Q.toSubgroup.index := Q.not_dvd_index
        have hQ_idx_eq : Q.toSubgroup.index = Nat.card ↥L / Nat.card ↥Q' := by
          have h1 : Nat.card ↥Q.toSubgroup * Q.toSubgroup.index = Nat.card ↥L :=
            Subgroup.card_mul_index Q.toSubgroup
          rw [← hQ'_card] at h1
          have hpos : 0 < Nat.card ↥Q' := Nat.card_pos
          have h2 : Nat.card ↥L = Q.toSubgroup.index * Nat.card ↥Q' := by
            rw [← h1, mul_comm]
          exact (Nat.div_eq_of_eq_mul_left hpos h2).symm
        rw [hQ_idx_eq] at hQ_not_dvd_idx
        -- hq_dvd_idx : q ∣ |L|/|C_L_P|.  h_div_dvd_div で q ∣ |L|/|Q'|.  矛盾.
        exact hQ_not_dvd_idx (hq_dvd_idx.trans h_div_dvd_div)
      -- Step j 後: Q' = L で `↥L` が q-群.
      have hL_qgroup : IsPGroup q ↥L := hQ'_eq_L ▸ hQ'_pgroup
      obtain ⟨kL, hL_card_qpow⟩ := IsPGroup.iff_card.mp hL_qgroup
      have hq_dvd_L : q ∣ Nat.card ↥L :=
        hq_dvd_idx.trans (Nat.div_dvd_of_dvd hC_dvd)
      have hq_ne_p : q ≠ p := by
        intro hqp
        exact hLcop (hqp ▸ hq_dvd_L)
      -- ## Step 1k: [L, P] の場合分け.
      -- [L, P] < L なら IH + Lem 4.29 で P ≤ C(L) (本ファイル内では未完成).
      -- [L, P] = L は Step l へ.
      set LP_comm : Subgroup _ := ⁅L, P⁆ with hLP_comm_def
      -- [L, P] ≤ L: P normalizes L なので ⁅L, P⁆ ⊆ L * L = L.
      have hLP_le_L : LP_comm ≤ L := by
        rw [hLP_comm_def, Subgroup.commutator_le]
        intro x hxL p hpP
        -- ⁅x, p⁆ = x * p * x⁻¹ * p⁻¹.
        -- p ∈ N(L) ⇒ p * x⁻¹ * p⁻¹ ∈ L (when x⁻¹ ∈ L).
        have hp_inN : p ∈ Subgroup.normalizer (L : Set _) := hPnorm hpP
        have hxinv_L : x⁻¹ ∈ L := L.inv_mem hxL
        have h_conj : p * x⁻¹ * p⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp hp_inN x⁻¹).mp hxinv_L
        -- ⁅x, p⁆ = x * p * x⁻¹ * p⁻¹ = x * (p * x⁻¹ * p⁻¹)
        have h_assoc : x * p * x⁻¹ * p⁻¹ = x * (p * x⁻¹ * p⁻¹) := by group
        change x * p * x⁻¹ * p⁻¹ ∈ L
        rw [h_assoc]
        exact L.mul_mem hxL h_conj
      -- [L, P] は P-不変 (P normalizes L and P, commutator subgroup of normal pair is invariant).
      have hPnorm_LP : P ≤ Subgroup.normalizer (LP_comm : Set _) := by
        simpa [hLP_comm_def] using
          (OddOrder.Isaacs.Ch04.subgroup_le_normalizer_commutator_self_right L P)
      by_cases hLP_eq_L : LP_comm = L
      · -- Case [L, P] = L: 続く Step l, m, n へ.
        -- Since the determinant map has abelian target, it kills commutators. Thus
        -- `[L,P]=L` forces every element of L to have determinant 1.
        let detGL : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) →* (ZMod p)ˣ :=
          Matrix.GeneralLinearGroup.det
        have hLP_le_detKer : LP_comm ≤ detGL.ker := by
          rw [hLP_comm_def, Subgroup.commutator_le]
          intro x hxL y hyP
          change detGL ⁅x, y⁆ = 1
          rw [map_commutatorElement]
          simp [commutatorElement_def, mul_assoc]
        have hL_le_detKer : L ≤ detGL.ker := by
          intro x hx
          exact hLP_le_detKer (by rwa [hLP_eq_L])
        have hL_le_SL_range :
            L ≤ (Matrix.SpecialLinearGroup.toGL :
              Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →*
                Matrix.GeneralLinearGroup (Fin 2) (ZMod p)).range := by
          intro x hx
          have hxdetGL : detGL x = 1 := hL_le_detKer hx
          have hxdet : ((x : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
              Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
            have := congrArg Units.val hxdetGL
            simpa [detGL, Matrix.GeneralLinearGroup.val_det_apply] using this
          refine ⟨⟨((x : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
            Matrix (Fin 2) (Fin 2) (ZMod p)), hxdet⟩, ?_⟩
          exact Units.ext rfl
        let toGLSL : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →*
            Matrix.GeneralLinearGroup (Fin 2) (ZMod p) :=
          Matrix.SpecialLinearGroup.toGL
        let L_SL : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
          L.comap toGLSL
        have hL_SL_map_eq : L_SL.map toGLSL = L := by
          apply le_antisymm
          · exact Subgroup.map_comap_le _ _
          · intro x hx
            rcases hL_le_SL_range hx with ⟨s, hs_eq⟩
            refine ⟨s, ?_, hs_eq⟩
            change toGLSL s ∈ L
            rw [hs_eq]
            exact hx
        have hL_card_eq_LSL : Nat.card ↥L =
            Nat.card ↥L_SL := by
          have hmap_card : Nat.card ↥L_SL = Nat.card ↥(L_SL.map toGLSL) :=
            Nat.card_congr
              (Subgroup.equivMapOfInjective L_SL toGLSL
                Matrix.SpecialLinearGroup.toGL_injective).toEquiv
          rw [hL_SL_map_eq] at hmap_card
          exact hmap_card.symm
        have hL_card_dvd_SL : Nat.card ↥L ∣
            Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
          rw [hL_card_eq_LSL]
          simpa using
            (Subgroup.card_dvd_of_le
              (show L_SL ≤
                (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) from le_top))
        have hq_dvd_SL : q ∣
            Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
          hq_dvd_L.trans hL_card_dvd_SL
        have hq_dvd_SL_formula : q ∣ p * (p - 1) * (p + 1) := by
          rwa [card_sl2_zmod_prime (p := p)] at hq_dvd_SL
        have hq_dvd_pred_or_succ : q ∣ p - 1 ∨ q ∣ p + 1 :=
          prime_dvd_pred_or_succ_of_dvd_prime_mul_pred_succ
            (Fact.out : p.Prime) hq_prime hq_ne_p hq_dvd_SL_formula
        have hq_not_dvd_both_of_odd : q ≠ 2 → ¬ (q ∣ p - 1 ∧ q ∣ p + 1) :=
          fun hq_ne_two =>
            prime_not_dvd_pred_and_succ_of_ne_two (Fact.out : p.Prime) hq_prime hq_ne_two
        have hL_card_dvd_SL_formula : Nat.card ↥L ∣ p * (p - 1) * (p + 1) := by
          rwa [card_sl2_zmod_prime (p := p)] at hL_card_dvd_SL
        have hL_card_dvd_pred_or_succ_of_odd :
            q ≠ 2 → Nat.card ↥L ∣ p - 1 ∨ Nat.card ↥L ∣ p + 1 :=
          fun hq_ne_two =>
            prime_power_dvd_pred_or_succ_of_dvd_prime_mul_pred_succ
              (Fact.out : p.Prime) hq_prime hq_ne_p hq_ne_two ⟨kL, hL_card_qpow⟩ hq_dvd_L
              hL_card_dvd_SL_formula
        have hL_card_le_p_succ_of_odd : q ≠ 2 → Nat.card ↥L ≤ p + 1 := by
          intro hq_ne_two
          have hp_pred_pos : 0 < p - 1 := by
            have hp_two_le : 2 ≤ p := (Fact.out : p.Prime).two_le
            omega
          have hp_succ_pos : 0 < p + 1 := by omega
          rcases hL_card_dvd_pred_or_succ_of_odd hq_ne_two with hL_dvd_pred | hL_dvd_succ
          · have hle_pred : Nat.card ↥L ≤ p - 1 :=
              Nat.le_of_dvd hp_pred_pos hL_dvd_pred
            omega
          · exact Nat.le_of_dvd hp_succ_pos hL_dvd_succ
        have hSL_card_dvd_GL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ∣
            Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :=
          ⟨p - 1, (card_sl2_mul_units_eq_card_gl2_zmod_prime (p := p)).symm⟩
        have hq_dvd_GL : q ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :=
          hq_dvd_SL.trans hSL_card_dvd_GL
        letI : MulDistribMulAction ↥P ↥L := MulDistribMulAction.compHom ↥L φ
        have hP_moves_L : ∃ (a : ↥P) (x : ↥L), a • x ≠ x := by
          by_contra h_no_move
          apply hL_in_C
          intro x hxL
          rw [Subgroup.mem_centralizer_iff]
          intro y hyP
          have hfix : (⟨y, hyP⟩ : ↥P) • (⟨x, hxL⟩ : ↥L) = ⟨x, hxL⟩ := by
            by_contra hne
            exact h_no_move ⟨⟨y, hyP⟩, ⟨x, hxL⟩, hne⟩
          have hconj : y * x * y⁻¹ = x := by
            have hval := congrArg (fun z : ↥L =>
              (z : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) hfix
            change
              (((φ ⟨y, hyP⟩) ⟨x, hxL⟩ : ↥L) :
                Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) = x at hval
            rw [hphi_val] at hval
            exact hval
          calc
            y * x = (y * x * y⁻¹) * y := by group
            _ = x * y := by rw [hconj]
        by_cases hq_eq_two : q = 2
        · have hL_2group : IsPGroup 2 ↥L := by
            simpa [hq_eq_two] using hL_qgroup
          have hL_comm : ∀ x y : ↥L, x * y = y * x :=
            hL2abelian L le_rfl hL_2group
          letI : CommGroup ↥L := { (inferInstance : Group ↥L) with mul_comm := hL_comm }
          have hzmod_two_ne_zero : (2 : ZMod p) ≠ 0 := by
            intro hzero
            have hp_dvd_two : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
            rcases (Nat.dvd_prime Nat.prime_two).mp hp_dvd_two with hp_eq_one | hp_eq_two
            · exact (Fact.out : p.Prime).ne_one hp_eq_one
            · exact hp2 hp_eq_two
          have hL_unique_order_two :
              ∀ x y : ↥L, orderOf x = 2 → orderOf y = 2 → x = y := by
            intro x y hx_order hy_order
            rcases hL_le_SL_range x.2 with ⟨sx, hsx⟩
            rcases hL_le_SL_range y.2 with ⟨sy, hsy⟩
            have hx_ne_one : x ≠ 1 := by
              intro hx_one
              have : orderOf x = 1 := by simp [hx_one]
              omega
            have hy_ne_one : y ≠ 1 := by
              intro hy_one
              have : orderOf y = 1 := by simp [hy_one]
              omega
            have hxGL_sq :
                ((x : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) ^ 2) = 1 := by
              have h := congrArg (fun z : ↥L =>
                (z : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) (pow_orderOf_eq_one x)
              simpa [hx_order] using h
            have hyGL_sq :
                ((y : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) ^ 2) = 1 := by
              have h := congrArg (fun z : ↥L =>
                (z : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) (pow_orderOf_eq_one y)
              simpa [hy_order] using h
            have hsx_sq : sx ^ 2 = 1 := by
              apply Matrix.SpecialLinearGroup.toGL_injective
              change toGLSL (sx ^ 2) = toGLSL 1
              rw [map_pow, map_one, hsx]
              exact hxGL_sq
            have hsy_sq : sy ^ 2 = 1 := by
              apply Matrix.SpecialLinearGroup.toGL_injective
              change toGLSL (sy ^ 2) = toGLSL 1
              rw [map_pow, map_one, hsy]
              exact hyGL_sq
            have hsx_ne_one : sx ≠ 1 := by
              intro hsx_one
              apply hx_ne_one
              have hx_val : (x : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) = 1 := by
                calc
                  (x : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) = toGLSL sx := hsx.symm
                  _ = toGLSL 1 := by rw [hsx_one]
                  _ = 1 := map_one toGLSL
              exact Subtype.ext hx_val
            have hsy_ne_one : sy ≠ 1 := by
              intro hsy_one
              apply hy_ne_one
              have hy_val : (y : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) = 1 := by
                calc
                  (y : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) = toGLSL sy := hsy.symm
                  _ = toGLSL 1 := by rw [hsy_one]
                  _ = 1 := map_one toGLSL
              exact Subtype.ext hy_val
            have hsx_eq_neg : sx = -1 :=
              sl2_unique_involution hzmod_two_ne_zero hsx_sq hsx_ne_one
            have hsy_eq_neg : sy = -1 :=
              sl2_unique_involution hzmod_two_ne_zero hsy_sq hsy_ne_one
            apply Subtype.ext
            change (x : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) =
              (y : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
            rw [← hsx, ← hsy, hsx_eq_neg, hsy_eq_neg]
          haveI hL_cyclic : IsCyclic ↥L :=
            isCyclic_of_comm_two_group_unique_order_two hL_2group hL_unique_order_two
          have hAut_2 : IsPGroup 2 (MulAut ↥L) :=
            cyclic_two_group_mulAut_isPGroup hL_2group
          have htop_P_p : IsPGroup p (⊤ : Subgroup ↥P) :=
            hPp.to_subgroup ⊤
          have hRange_p : IsPGroup p φ.range := by
            rw [φ.range_eq_map]
            exact htop_P_p.map φ
          have hRange_2 : IsPGroup 2 φ.range :=
            hAut_2.to_subgroup φ.range
          have hRange_coprime :
              Nat.Coprime (Nat.card ↥φ.range) (Nat.card ↥φ.range) :=
            IsPGroup.coprime_card_of_ne p 2 hp2 φ.range φ.range hRange_p hRange_2
          have hRange_card_one : Nat.card ↥φ.range = 1 :=
            Nat.eq_one_of_dvd_coprimes hRange_coprime dvd_rfl dvd_rfl
          have hRange_bot : φ.range = ⊥ :=
            Subgroup.card_eq_one.mp hRange_card_one
          have hphi_triv : φ = 1 :=
            MonoidHom.range_eq_bot_iff.mp hRange_bot
          intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro l hl
          have hfix : (φ ⟨a, ha⟩) ⟨l, hl⟩ = ⟨l, hl⟩ := by
            rw [hphi_triv]
            simp
          have hconj : a * l * a⁻¹ = l := by
            have := congrArg (fun z : ↥L =>
              (z : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) hfix
            simpa [hphi_val ⟨a, ha⟩ ⟨l, hl⟩] using this
          have hcomm : a * l = l * a := by
            calc
              a * l = (a * l * a⁻¹) * a := by group
              _ = l * a := by rw [hconj]
          exact hcomm.symm
        · exfalso
          obtain ⟨a_move, x_move, hmove⟩ := hP_moves_L
          have hL_card_ge_p_succ : p + 1 ≤ Nat.card ↥L :=
            pgroup_action_card_ge_prime_succ_of_moved hPp hmove
          have hL_card_eq_p_succ : Nat.card ↥L = p + 1 :=
            le_antisymm (hL_card_le_p_succ_of_odd hq_eq_two) hL_card_ge_p_succ
          have htwo_dvd_p_succ : 2 ∣ p + 1 := by
            rcases (Fact.out : p.Prime).odd_of_ne_two hp2 with ⟨m, hm⟩
            rw [hm]
            exact ⟨m + 1, by omega⟩
          have htwo_not_dvd_q : ¬ 2 ∣ q := by
            intro htwo_dvd_q
            have htwo_eq_q : 2 = q :=
              (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq_prime).mp htwo_dvd_q
            exact hq_eq_two htwo_eq_q.symm
          have htwo_not_dvd_L : ¬ 2 ∣ Nat.card ↥L := by
            rw [hL_card_qpow]
            intro htwo_dvd_qpow
            exact htwo_not_dvd_q (Nat.prime_two.dvd_of_dvd_pow htwo_dvd_qpow)
          exact htwo_not_dvd_L (by
            rw [hL_card_eq_p_succ]
            exact htwo_dvd_p_succ)
      · -- Case [L, P] < L: IH 適用 → P ≤ C([L, P]) → Lem 4.29 で [L, P] = ⊥ → P ≤ C(L).
        have hLP_lt_L : LP_comm < L := lt_of_le_of_ne hLP_le_L hLP_eq_L
        have hLP_card_lt_L : Nat.card ↥LP_comm < Nat.card ↥L := by
          rcases lt_or_eq_of_le (Subgroup.card_le_of_le hLP_le_L) with h | h
          · exact h
          · exact absurd (Subgroup.eq_of_le_of_card_ge hLP_le_L h.ge) hLP_eq_L
        have hLP_card_le_n : Nat.card ↥LP_comm ≤ n := by omega
        -- IH 仮説の準備.
        have hLcop_LP : ¬ p ∣ Nat.card ↥LP_comm :=
          fun hp_dvd => hLcop (hp_dvd.trans (Subgroup.card_dvd_of_le hLP_le_L))
        have hL2abelian_LP :
            ∀ S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
              S ≤ LP_comm → IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x :=
          fun S hS hS2 => hL2abelian S (hS.trans hLP_le_L) hS2
        -- IH 適用: P ≤ C([L, P]).
        have hP_cent_LP : P ≤ Subgroup.centralizer (LP_comm : Set _) :=
          ih hPnorm_LP hLcop_LP hL2abelian_LP hLP_card_le_n
        -- Ch.4 §4D action-commutator corollary: if P acts trivially on `[L,P]`,
        -- then the coprime action of P on L is trivial.
        have hAC_le_LP :
            OddOrder.Isaacs.Ch04.actionCommutator φ ≤ LP_comm.comap L.subtype := by
          rw [OddOrder.Isaacs.Ch04.actionCommutator_le_iff]
          intro a g
          change (((φ a) g * g⁻¹ : ↥L) :
              Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) ∈ LP_comm
          rw [hLP_comm_def]
          have hcomm : ⁅(a : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
              (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))⁆ ∈
              (⁅P, L⁆ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) :=
            Subgroup.commutator_mem_commutator a.2 g.2
          have hcomm' : ⁅(a : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
              (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))⁆ ∈
              (⁅L, P⁆ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) := by
            rwa [Subgroup.commutator_comm] at hcomm
          simpa [hphi_val a g, commutatorElement_def, mul_assoc] using hcomm'
        have htriv_on_AC : ∀ a : ↥P, ∀ h ∈ OddOrder.Isaacs.Ch04.actionCommutator φ,
            (φ a) h = h := by
          intro a h hh
          apply L.subtype_injective
          change (((φ a) h : ↥L) : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) =
            (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
          have hhLP : (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) ∈ LP_comm :=
            hAC_le_LP hh
          have hcomm :
              (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) *
                  (a : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) =
                (a : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) *
                  (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :=
            Subgroup.mem_centralizer_iff.mp (hP_cent_LP a.2) h hhLP
          rw [hphi_val a h]
          rw [← hcomm]
          group
        have hAC_bot : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
          OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime
            hCop (Or.inl hP_solvable) htriv_on_AC
        have hacts : ∀ a : ↥P, ∀ g : ↥L, (φ a) g = g := by
          rwa [OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially] at hAC_bot
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hfix := hacts ⟨a, ha⟩ ⟨l, hl⟩
        have hconj : a * l * a⁻¹ = l := by
          have := congrArg (fun x : ↥L =>
            (x : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) hfix
          simpa [hphi_val ⟨a, ha⟩ ⟨l, hl⟩] using this
        have hcomm : a * l = l * a := by
          calc
            a * l = (a * l * a⁻¹) * a := by group
            _ = l * a := by rw [hconj]
        exact hcomm.symm

/-- **Isaacs Lemma 7.3** ⭐ (GL(2,p) 補題). `p ≠ 2` prime, `P ≤ GL(2, ZMod p)`
p-subgroup が `L ≤ GL(2, ZMod p)` を normalize し, `(|L|, p) = 1` かつ `L` 内の
任意の 2-部分群が abelian ⇒ P は L を centralize.

**Sylow 2-subgroup abelian の hereditary form**: 仮説 `hL2abelian` は「L 内の任意の
2-部分群が abelian」と述べる. Isaacs 原本の「L の Sylow 2 が abelian」と同値だが
(任意の 2-部分群は Sylow 2 に含まれ, abelian 群の部分群は abelian), 帰納法
(IH 適用時の継承) で便利な形.

**proof** (詳細はファイル上部 §7A docstring 参照): `|L|`-strong induction を
[`lem73_aux`](#) で展開. P-invariant Sylow 取得, proper commutator branch, `q = 2`
cyclicity branch, odd `q` orbit-count branch をすべて同補助定理内で処理する. -/
theorem gl2_pSubgroup_centralizes_of_normalizes
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P L : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))}
    (hPp : IsPGroup p P) (hPnorm : P ≤ Subgroup.normalizer (L : Set _))
    (hLcop : ¬ p ∣ Nat.card L)
    (hL2abelian : ∀ S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
      S ≤ L → IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) :
    P ≤ Subgroup.centralizer (L : Set _) :=
  lem73_aux hp2 hPp (Nat.card L) hPnorm hLcop hL2abelian le_rfl


end OddOrder.Isaacs.Ch07
