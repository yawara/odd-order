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
# OddOrder.Isaacs.Ch07 — The Thompson Subgroup

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 7 (pp. 201-222) の Lean 化.

**FT クリティカル経路の頂点**. **章本体は 8 結果**だが BG/Peterfalvi 経由で
Feit-Thompson 局所解析の中核を担う:

- **Thm 7.1 Thompson normal p-complement** — Ch.6 Thm 6.23 を完備化.
- **Thm 7.2** — `J(P)` は Q 内 characteristic (本ファイルで `thompsonJ_eq_of_le_of_le`
  経由で完成済).
- **Lem 7.3 GL(2,p) 補題** — Thm 7.5 の道具.
- **Lem 7.4 SL(2,q) 唯一 involution = -I** — Thm 7.3 の道具.
- **Thm 7.5 normal-P theorem** — Thm 7.6 の中核 step.
- **Thm 7.6 normal-J theorem** ≡ BG Thm 6.2 (odd-order 仮定). **FT クリティカル度
  HIGHEST**. BG §6, §8, §9, App.A で 7 ヶ所超で直接引用.
- **Lem 7.7** — `N/C` 系の `p'`-quotient (Lem 2.17 拡張).
- **Thm 7.8 Burnside `p^a q^b`** — character-free 証明 (Goldschmidt-Bender-Matsuyama).

## Notes / Roadmap

詳細な mini-roadmap は [`notes/isaacs/ch07_thompson.md`](../../../notes/isaacs/ch07_thompson.md)
参照. 主要な设计判断 (HasNormalPComplement def, `Aut(E) ≅ GL(n,p)` 橋渡し,
`p`-stability 概念) も同ノートに集約.

## Shared modules

* [`OddOrder.GroupTheory.ElementaryAbelian`](../../GroupTheory/ElementaryAbelian.lean) —
  `IsElementaryAbelian p G` / `Subgroup.IsElementaryAbelian H p` def (Ch.3, Ch.6, Ch.7 共用).
* [`OddOrder.GroupTheory.ThompsonSubgroup`](../../GroupTheory/ThompsonSubgroup.lean) —
  `Subgroup.thompsonJ P p` def + Thm 7.2 (BG App.A, App.B 共用視野).

## Implementation order (本ファイル内)

1. ✅ Thm 7.2 (`thompsonJ` shared module 経由)
2. ✅ Lem 7.4 SL(2,q) — 独立小テーマ (先行章不要)
3. ✅ Lem 7.7 — Lem 2.17 拡張 (Ch.2 完成済から短い延長)
4. ✅ Lem 7.3 GL(2,p) 補題 — `|L|`-induction + Lem 7.4 + Ch.4 coprime action
5. Thm 7.5 normal-P → Thm 7.6 normal-J
6. (Ch.5 §5E 5.26 完成後) Thm 7.1
7. (上記完成後) Thm 7.8 Burnside

未着手 statement の def 系前提 (`HasNormalPComplement`, `GeneralLinearGroup` 引数法,
`Aut(E) ≅ GL(n,p)`) は実装時に決める.
-/

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## §7A: `J(P)` definition + GL(2,p) lemma + normal-P theorem (pp. 201-208) -/

section /- 7A: J(P), GL(2,p), normal-P theorem -/

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
    Subgroup.inf_eq_bot_of_coprime hcop
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

/-! ### Thm 7.5 — normal-P theorem (statement 保留)

**Isaacs Thm 7.5** (mmd L3783):

> (i) G p-solvable, (ii) `p ≠ 2`, (iii) Sylow-2 abelian, (iv) G が p-group V に
> 忠実作用, (v) `|V:C_V(P)| ≤ p` ⇒ `P ⊴ G`.

**先行 def 依存**: `Aut(E) ≅ GL(n,p)` (Lem 7.3 と共用).

**proof 戦略** (8 Step): Sylow conjugacy + GL(2,p) embedding + Hall-Higman 3.21
+ Lem 7.3 + Ch.6 6.11 (p-group ≤1 subgroup p ⇒ cyclic/quaternion).

Ch.6 6.11 は `isCyclic_or_two_quaternion_of_subgroups_card_prime_unique` として利用可能.
残る作業は, 下の action / fixed subgroup bridge 群を使って Thm 7.5 の本体 statement と
book proof の contradiction assembly を Lean に載せること. -/

/-! #### Thm 7.5 action infrastructure

Theorem 7.5 repeatedly uses the faithful action of `G` on the `p`-group `V` as an
embedding `G ↪ Aut(V)`, and writes `C_V(P)` for the fixed subgroup of `P` acting on
`V`.  The following helpers keep those two translations explicit. -/

/-- Reinterpret automorphisms of an abelian group of exponent dividing `p` as `ZMod p`-linear
automorphisms of its additive type.

The `ZMod p`-module structure is supplied explicitly because in Thm 7.5 it is built from the
elementary-abelian hypothesis on a quotient. -/
noncomputable def mulAutZModGeneralLinearEquiv
    (V : Type*) [Group V] [IsMulCommutative V] (p : ℕ)
    [Module (ZMod p) (Additive V)] :
    MulAut V ≃* LinearMap.GeneralLinearGroup (ZMod p) (Additive V) where
  toFun φ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive V)).symm
      ((MulEquiv.toAdditive φ).toLinearEquiv
        (fun c x => ZMod.map_smul (MulEquiv.toAdditive φ).toAddMonoidHom c x))
  invFun φ :=
    (MulEquiv.toAdditive (G := V) (H := V)).symm φ.toLinearEquiv.toAddEquiv
  left_inv φ := by
    ext x
    rfl
  right_inv φ := by
    ext x
    rfl
  map_mul' φ ψ := by
    ext x
    rfl

/-- A chosen `ZMod p`-basis of size `2` identifies `Aut(V)` with `GL(2,p)`.

This is the explicit bridge needed to feed the action on an elementary-abelian quotient into
Isaacs Lemma 7.3 (`gl2_pSubgroup_centralizes_of_normalizes`). -/
noncomputable def mulAutGLTwoEquivOfBasis
    (V : Type*) [Group V] [IsMulCommutative V] (p : ℕ)
    [Module (ZMod p) (Additive V)]
    (b : Module.Basis (Fin 2) (ZMod p) (Additive V)) :
    MulAut V ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod p) :=
  (mulAutZModGeneralLinearEquiv V p).trans (Matrix.GeneralLinearGroup.toLin' b).symm

/-- The `ZMod p` scalar-torsion condition supplied by an elementary-abelian multiplicative group.
-/
private lemma additive_nsmul_eq_zero_of_isElementaryAbelian
    {V : Type*} [Group V] {p : ℕ}
    (hV : OddOrder.GroupTheory.IsElementaryAbelian p V) :
    ∀ x : Additive V, (p : ℕ) • x = 0 := by
  intro x
  apply Additive.toMul.injective
  show (p • x).toMul = (0 : Additive V).toMul
  rw [toMul_nsmul, toMul_zero]
  exact hV.pow_eq_one x.toMul

/-- An elementary-abelian group of order `p^2` has automorphism group identified with `GL(2,p)`.

The basis is chosen noncomputably from the finite `ZMod p`-vector-space structure on the
additive type. -/
noncomputable def mulAutGLTwoEquivOfIsElementaryAbelianCard
    (V : Type*) [Group V] [Finite V] {p : ℕ} [Fact p.Prime]
    (hV : OddOrder.GroupTheory.IsElementaryAbelian p V) (hcard : Nat.card V = p ^ 2) :
    MulAut V ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod p) := by
  classical
  haveI : IsMulCommutative V := ⟨⟨hV.comm⟩⟩
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (Additive V) := Fintype.ofEquiv V Additive.ofMul
  haveI : Module (ZMod p) (Additive V) :=
    AddCommGroup.zmodModule (additive_nsmul_eq_zero_of_isElementaryAbelian hV)
  have hfinrank : Module.finrank (ZMod p) (Additive V) = 2 := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    calc
      p ^ Module.finrank (ZMod p) (Additive V)
          = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) (Additive V) := by
              rw [ZMod.card]
      _ = Fintype.card (Additive V) := (Module.card_eq_pow_finrank
              (K := ZMod p) (V := Additive V)).symm
      _ = Nat.card (Additive V) := by rw [Nat.card_eq_fintype_card]
      _ = Nat.card V := (Nat.card_congr Additive.ofMul).symm
      _ = p ^ 2 := hcard
  let b0 := Module.Free.chooseBasis (ZMod p) (Additive V)
  have hidx_card : Fintype.card (Module.Free.ChooseBasisIndex (ZMod p) (Additive V)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact hfinrank
  let eidx : Module.Free.ChooseBasisIndex (ZMod p) (Additive V) ≃ Fin 2 :=
    Fintype.equivOfCardEq (by rw [hidx_card, Fintype.card_fin])
  exact mulAutGLTwoEquivOfBasis V p (b0.reindex eidx)

/-- Transport Isaacs Lemma 7.3 back from `GL(2,p)` to automorphism subgroups.

The hypotheses are stated for the images of `P` and `L` under a chosen identification
`Aut(V) ≃ GL(2,p)`.  The conclusion is the original centralizer statement in `Aut(V)`. -/
theorem mulAut_centralizes_of_gl2_image_hypotheses
    {V : Type*} [Group V] {p : ℕ} [Fact p.Prime]
    (e : MulAut V ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) (hp2 : p ≠ 2)
    {P L : Subgroup (MulAut V)}
    (hPp : IsPGroup p (P.map e.toMonoidHom))
    (hPnorm : P.map e.toMonoidHom ≤
      Subgroup.normalizer ((L.map e.toMonoidHom) : Set _))
    (hLcop : ¬ p ∣ Nat.card (L.map e.toMonoidHom))
    (hL2abelian :
      ∀ S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
        S ≤ L.map e.toMonoidHom → IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) :
    P ≤ Subgroup.centralizer (L : Set _) := by
  have hGL : P.map e.toMonoidHom ≤ Subgroup.centralizer ((L.map e.toMonoidHom) : Set _) :=
    gl2_pSubgroup_centralizes_of_normalizes hp2 hPp hPnorm hLcop hL2abelian
  intro x hxP
  rw [Subgroup.mem_centralizer_iff]
  intro y hyL
  have hxGL : e x ∈ P.map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom hxP
  have hyGL : e y ∈ L.map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom hyL
  have hcommGL : e y * e x = e x * e y :=
    (Subgroup.mem_centralizer_iff.mp (hGL hxGL)) (e y) hyGL
  apply e.injective
  simpa [map_mul] using hcommGL

/-- Pull a centralizer conclusion back through an injective homomorphism.

This is the faithful-action transfer used in Isaacs Thm 7.5: once the images of `P` and
`L` centralize inside `Aut(V)`, the original subgroups centralize in the acting group. -/
theorem le_centralizer_of_map_le_centralizer_of_injective
    {A B : Type*} [Group A] [Group B] {φ : A →* B} (hφ : Function.Injective φ)
    {P L : Subgroup A}
    (hmap : P.map φ ≤ Subgroup.centralizer ((L.map φ) : Set B)) :
    P ≤ Subgroup.centralizer (L : Set A) := by
  intro x hxP
  rw [Subgroup.mem_centralizer_iff]
  intro y hyL
  have hxmap : φ x ∈ P.map φ := Subgroup.mem_map_of_mem φ hxP
  have hymap : φ y ∈ L.map φ := Subgroup.mem_map_of_mem φ hyL
  have hcomm : φ y * φ x = φ x * φ y :=
    (Subgroup.mem_centralizer_iff.mp (hmap hxmap)) (φ y) hymap
  apply hφ
  simpa [map_mul] using hcomm

/-- Isaacs Thm 7.5 GL(2,p) centralizer step for a faithful action.

This combines the `Aut(V) ≃ GL(2,p)` bridge with the injective-action transfer, so the
conclusion is directly in the acting group rather than in `MulAut V`. -/
theorem subgroup_centralizes_of_mulAut_gl2_image_hypotheses
    {A V : Type*} [Group A] [Group V] {p : ℕ} [Fact p.Prime]
    {φ : A →* MulAut V} (hφ : Function.Injective φ)
    (e : MulAut V ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) (hp2 : p ≠ 2)
    {P L : Subgroup A}
    (hPp : IsPGroup p ((P.map φ).map e.toMonoidHom))
    (hPnorm : (P.map φ).map e.toMonoidHom ≤
      Subgroup.normalizer (((L.map φ).map e.toMonoidHom) : Set _))
    (hLcop : ¬ p ∣ Nat.card ((L.map φ).map e.toMonoidHom))
    (hL2abelian :
      ∀ S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
        S ≤ (L.map φ).map e.toMonoidHom → IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) :
    P ≤ Subgroup.centralizer (L : Set A) :=
  le_centralizer_of_map_le_centralizer_of_injective hφ
    (mulAut_centralizes_of_gl2_image_hypotheses e hp2 hPp hPnorm hLcop hL2abelian)

/-- The image of any subgroup normalizes the image of a normal subgroup.

This is the normalizer adapter used in the reduced `GL(2,p)` branch of Isaacs Thm 7.5:
`P` normalizes `O_{p'}(G)`, so its faithful image normalizes the image of `O_{p'}(G)`. -/
theorem map_le_normalizer_map_of_normal
    {A B : Type*} [Group A] [Group B] {φ : A →* B} {P L : Subgroup A} [L.Normal] :
    P.map φ ≤ Subgroup.normalizer ((L.map φ) : Set B) := by
  rintro _ ⟨p, _hpP, rfl⟩
  have hLnorm : L.Normal := inferInstance
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨l, hlL, rfl⟩
    refine ⟨p * l * p⁻¹, hLnorm.conj_mem l hlL p, ?_⟩
    simp [map_mul]
  · rintro ⟨l, hlL, hyl⟩
    have hconj : p⁻¹ * l * p ∈ L := by
      simpa using hLnorm.conj_mem l hlL p⁻¹
    refine ⟨p⁻¹ * l * p, hconj, ?_⟩
    calc
      φ (p⁻¹ * l * p) = (φ p)⁻¹ * φ l * φ p := by simp [map_mul]
      _ = y := by rw [hyl]; group

/-- A `p'`-subgroup remains `p'` after an injective homomorphic image. -/
theorem not_dvd_card_map_of_isPiGroup_compl_of_injective
    {A B : Type*} [Group A] [Group B] [Finite A] {p : ℕ} [Fact p.Prime]
    {φ : A →* B} (hφ : Function.Injective φ) {L : Subgroup A}
    (hLpi :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} L) :
    ¬ p ∣ Nat.card (L.map φ) := by
  intro hp_dvd
  have hcard : Nat.card (L.map φ) = Nat.card L :=
    Nat.card_congr (Subgroup.equivMapOfInjective L φ hφ).symm.toEquiv
  have hp_L_pf : p ∈ (Nat.card L).primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨Fact.out, by rwa [hcard] at hp_dvd, Nat.card_pos.ne'⟩
  exact hLpi p hp_L_pf (by simp)

/-- Transfer the hereditary "all 2-subgroups are abelian" hypothesis through an injective
image.

This is the hypothesis adapter for Lemma 7.3 in the reduced Thm 7.5 branch: a 2-subgroup
inside the image of `L` is pulled back to a 2-subgroup of the original group, where the
global Sylow-2-abelian hypothesis is available. -/
theorem two_subgroup_abelian_of_le_map_of_injective
    {A B : Type*} [Group A] [Group B] {φ : A →* B} (hφ : Function.Injective φ)
    (h2abelian : ∀ S : Subgroup A, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    {L : Subgroup A} {T : Subgroup B}
    (hT_le : T ≤ L.map φ) (hT2 : IsPGroup 2 T) :
    ∀ x y : ↥T, x * y = y * x := by
  let H : Subgroup A := T.comap φ
  let ψ : H →* T := {
    toFun a := ⟨φ a, a.property⟩
    map_one' := by ext; simp
    map_mul' a b := by ext; simp }
  have hψ_inj : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    apply hφ
    exact congrArg Subtype.val hab
  have hH2 : IsPGroup 2 H := hT2.of_injective ψ hψ_inj
  have hHcomm := h2abelian H hH2
  intro x y
  obtain ⟨a, haL, hax⟩ := hT_le x.property
  obtain ⟨b, hbL, hby⟩ := hT_le y.property
  have haT : φ a ∈ T := by rw [hax]; exact x.property
  have hbT : φ b ∈ T := by rw [hby]; exact y.property
  have hab : a * b = b * a :=
    congrArg Subtype.val (hHcomm ⟨a, haT⟩ ⟨b, hbT⟩)
  apply Subtype.ext
  change (x : B) * (y : B) = (y : B) * (x : B)
  rw [← hax, ← hby, ← map_mul, hab, map_mul]

/-- Reduced elementary-abelian branch of Isaacs Thm 7.5.

After the minimal-counterexample quotient reduction has replaced `V` by a faithful
elementary-abelian group of order `p²`, the `GL(2,p)` embedding, Lemma 7.3, and
Hall-Higman force the chosen Sylow `p`-subgroup to be normal. -/
theorem sylow_normal_of_elementaryAbelian_card_prime_sq_of_faithful
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hp2 : p ≠ 2)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    {φ : G →* MulAut V} (hφ : Function.Injective φ)
    (hVelem : OddOrder.GroupTheory.IsElementaryAbelian p V)
    (hVcard : Nat.card V = p ^ 2) (P : Sylow p G) :
    (P : Subgroup G).Normal := by
  by_contra hP_not_normal
  let e := mulAutGLTwoEquivOfIsElementaryAbelianCard V (p := p) hVelem hVcard
  have hφGL : Function.Injective (e.toMonoidHom.comp φ) := by
    intro a b hab
    exact hφ (e.injective hab)
  have hPp : IsPGroup p (((P : Subgroup G).map φ).map e.toMonoidHom) :=
    (P.isPGroup'.map φ).map e.toMonoidHom
  have hP_image_card_le :
      Nat.card (((P : Subgroup G).map φ).map e.toMonoidHom) ≤ p :=
    gl2_pSubgroup_card_le_prime _ hPp
  have hP_map_phi_card :
      Nat.card ((P : Subgroup G).map φ) = Nat.card (P : Subgroup G) :=
    Nat.card_congr
      (Subgroup.equivMapOfInjective (P : Subgroup G) φ hφ).symm.toEquiv
  have hP_map_GL_card :
      Nat.card (((P : Subgroup G).map φ).map e.toMonoidHom) =
        Nat.card ((P : Subgroup G).map φ) :=
    Nat.card_congr
      (Subgroup.equivMapOfInjective ((P : Subgroup G).map φ) e.toMonoidHom
        e.injective).symm.toEquiv
  have hP_card_le : Nat.card (P : Subgroup G) ≤ p := by
    rwa [hP_map_GL_card, hP_map_phi_card] at hP_image_card_le
  have hOp : OddOrder.Isaacs.Ch01.opCore p G = ⊥ :=
    opCore_eq_bot_of_sylow_card_le_prime_of_not_normal P hP_card_le hP_not_normal
  set L : Subgroup G := OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G with hL_def
  haveI hLnormal : L.Normal := by
    dsimp [L]
    infer_instance
  have hPnorm :
      ((P : Subgroup G).map φ).map e.toMonoidHom ≤
        Subgroup.normalizer (((L.map φ).map e.toMonoidHom) : Set _) := by
    have hcomp :
        (P : Subgroup G).map (e.toMonoidHom.comp φ) ≤
          Subgroup.normalizer ((L.map (e.toMonoidHom.comp φ)) : Set _) :=
      map_le_normalizer_map_of_normal
        (φ := e.toMonoidHom.comp φ) (P := (P : Subgroup G)) (L := L)
    simpa [Subgroup.map_map] using hcomp
  have hLpi :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} L := by
    simpa [L, hL_def] using
      (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup
        (G := G) {q | q ∉ ({p} : Set ℕ)})
  have hLcop :
      ¬ p ∣ Nat.card ((L.map φ).map e.toMonoidHom) := by
    have hcomp :
        ¬ p ∣ Nat.card (L.map (e.toMonoidHom.comp φ)) :=
      not_dvd_card_map_of_isPiGroup_compl_of_injective
        (p := p) (φ := e.toMonoidHom.comp φ) hφGL hLpi
    simpa [Subgroup.map_map] using hcomp
  have hL2abelian :
      ∀ S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
        S ≤ (L.map φ).map e.toMonoidHom → IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x := by
    intro S hS_le hS2
    have hS_le_comp : S ≤ L.map (e.toMonoidHom.comp φ) := by
      simpa [Subgroup.map_map] using hS_le
    exact two_subgroup_abelian_of_le_map_of_injective hφGL h2abelian hS_le_comp hS2
  have hPcentral : (P : Subgroup G) ≤ Subgroup.centralizer (L : Set G) :=
    subgroup_centralizes_of_mulAut_gl2_image_hypotheses
      (φ := φ) hφ e hp2 hPp hPnorm hLcop hL2abelian
  have hcentral_le_L : Subgroup.centralizer (L : Set G) ≤ L := by
    simpa [L, hL_def] using
      (centralizer_oPiCore_compl_le_of_opCore_eq_bot (G := G) (p := p) hOp)
  have hP_le_L : (P : Subgroup G) ≤ L := hPcentral.trans hcentral_le_L
  have hP_bot : (P : Subgroup G) = ⊥ :=
    sylow_eq_bot_of_le_oPiCore_compl P (by simpa [L, hL_def] using hP_le_L)
  apply hP_not_normal
  rw [hP_bot]
  infer_instance

/-- Cyclic branch of Isaacs Thm 7.5: a group acting faithfully by automorphisms on a cyclic
group is commutative, hence every acting subgroup is normal.

The proof uses mathlib's explicit `Aut(V) ≃ (ZMod |V|)ˣ` identification for cyclic groups.
This is the formal version of the book step "if `V` is cyclic, then `Aut(V)` is abelian, so
`G` is abelian and `P` is normal." -/
theorem subgroup_normal_of_injective_mulAut_of_isCyclic
    {A V : Type*} [Group A] [Group V] [IsCyclic V]
    {φ : A →* MulAut V} (hφ : Function.Injective φ) (P : Subgroup A) :
    P.Normal := by
  let e := IsCyclic.mulAutMulEquiv V
  letI : CommGroup (MulAut V) := e.toMonoidHom.commGroupOfInjective e.injective
  letI : CommGroup A := φ.commGroupOfInjective hφ
  infer_instance

/-- A faithful action by automorphisms embeds the acting group into `MulAut V`. -/
theorem toMulAut_injective_of_faithful {A V : Type*} [Group A] [Group V]
    [MulDistribMulAction A V] [FaithfulSMul A V] :
    Function.Injective (MulDistribMulAction.toMulAut A V) := by
  intro a b hab
  apply MulAction.toPerm_injective (α := A) (β := V)
  ext v
  have h := congrArg (fun ψ : MulAut V => ψ v) hab
  simpa using h

/-- Kernel form of `toMulAut_injective_of_faithful`. -/
theorem toMulAut_ker_eq_bot_of_faithful {A V : Type*} [Group A] [Group V]
    [MulDistribMulAction A V] [FaithfulSMul A V] :
    (MulDistribMulAction.toMulAut A V).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).mpr toMulAut_injective_of_faithful

/-- A subgroup of a finite `p`-group with index at most `p` is normal. -/
theorem normal_of_isPGroup_index_le_prime
    {V : Type*} [Group V] [Finite V] {p : ℕ} [Fact p.Prime]
    (hV : IsPGroup p V) {H : Subgroup V} (hH : H.index ≤ p) :
    H.Normal := by
  haveI : H.FiniteIndex := inferInstance
  obtain ⟨n, hn⟩ := hV.index H
  rcases n with _ | n
  · exact Subgroup.normal_of_index_eq_one (by simpa using hn)
  rcases n with _ | n
  · have hindex : H.index = p := by simpa using hn
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hV
    have hm_ne_zero : m ≠ 0 := by
      intro hm_zero
      have hcard_one : Nat.card V = 1 := by
        rw [hm, hm_zero, pow_zero]
      have hdiv : p ∣ 1 := by
        rw [← hcard_one, ← hindex]
        exact H.index_dvd_card
      exact (Fact.out : Nat.Prime p).not_dvd_one hdiv
    have hmin : (Nat.card V).minFac = p := by
      rw [hm, (Fact.out : Nat.Prime p).pow_minFac hm_ne_zero]
    exact Subgroup.normal_of_index_eq_minFac_card (by rw [hindex, hmin])
  · have hpow_le : p ^ 2 ≤ p := by
      have hpow : p ^ 2 ≤ p ^ (n + 2) := by
        exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) (by omega)
      have hindex_le : p ^ (n + 2) ≤ p := by
        simpa [hn, pow_succ] using hH
      exact hpow.trans hindex_le
    have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    nlinarith [hpow_le, hp_two]

/-- A faithful action by automorphisms realizes the acting group as a subgroup of `Aut(V)`. -/
noncomputable def subgroupOfMulAutAction (A V : Type*) [Group A] [Group V]
    [MulDistribMulAction A V] [FaithfulSMul A V] :
    A ≃* (MulDistribMulAction.toMulAut A V).range :=
  MulEquiv.ofLeftInverse' _
    (Classical.choose_spec (toMulAut_injective_of_faithful (A := A) (V := V)).hasLeftInverse)

/-- Action-centralizer notation for `C_V(P)`: the elements of `V` fixed by every element of `P`
under `φ : A →* MulAut V`. -/
def actionCentralizer {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P : Subgroup A) : Subgroup V :=
  Subgroup.fixedPointsOfMulAut (φ.comp P.subtype)

@[simp]
theorem mem_actionCentralizer {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {P : Subgroup A} {v : V} :
    v ∈ actionCentralizer φ P ↔ ∀ p : P, (φ p) v = v :=
  Iff.rfl

@[simp]
theorem mem_actionCentralizer_top {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {v : V} :
    v ∈ actionCentralizer φ (⊤ : Subgroup A) ↔ ∀ a : A, (φ a) v = v := by
  constructor
  · intro hv a
    exact hv ⟨a, trivial⟩
  · intro hv a
    exact hv a

/-- If `P ≤ Q`, then `C_V(Q) ≤ C_V(P)`. -/
theorem actionCentralizer_antitone {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {P Q : Subgroup A} (hPQ : P ≤ Q) :
    actionCentralizer φ Q ≤ actionCentralizer φ P := by
  intro v hv p
  exact hv ⟨p, hPQ p.property⟩

/-- If `Q = P^g`, then `C_V(Q) = C_V(P)^g` for the action `φ`.

This is the Lean form of the first conjugacy step in Isaacs Thm 7.5. -/
theorem actionCentralizer_map_conj {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P : Subgroup A) (g : A) :
    actionCentralizer φ (P.map (MulAut.conj g).toMonoidHom) =
      (φ g : MulAut V) • actionCentralizer φ P := by
  ext v
  constructor
  · intro hv
    refine ⟨(φ g)⁻¹ v, ?_, MulAut.apply_inv_self V (φ g) v⟩
    intro p
    have hfix := hv ⟨(MulAut.conj g) p,
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom p.property⟩
    change (φ ((MulAut.conj g) (p : A))) v = v at hfix
    have hfix'' : (φ (g * (p : A) * g⁻¹)) v = v := by
      simpa [MulAut.conj_apply] using hfix
    have h := congrArg (fun x : V => (φ g)⁻¹ x) hfix''
    simpa [map_mul] using h
  · rintro ⟨u, hu, rfl⟩ q
    rcases q.property with ⟨p, hp, hq⟩
    have hpfix := hu ⟨p, hp⟩
    have h := congrArg (fun x : V => (φ g) x) hpfix
    have hq' : q.val = g * p * g⁻¹ := by
      simpa [MulAut.conj_apply] using hq.symm
    change (φ q.val) ((φ g) u) = (φ g) u
    rw [hq']
    simpa [map_mul] using h

/-- Conjugate subgroups have action-centralizers of the same index. -/
theorem actionCentralizer_map_conj_index {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P : Subgroup A) (g : A) :
    (actionCentralizer φ (P.map (MulAut.conj g).toMonoidHom)).index =
      (actionCentralizer φ P).index := by
  rw [actionCentralizer_map_conj]
  have h := Subgroup.relIndex_pointwise_smul (h := (φ g : MulAut V))
    (J := actionCentralizer φ P) (K := (⊤ : Subgroup V))
  have htop : (φ g : MulAut V) • (⊤ : Subgroup V) = ⊤ := by
    rw [Subgroup.pointwise_smul_def]
    exact Subgroup.map_top_of_surjective _ (fun v => ⟨(φ g)⁻¹ v, by simp⟩)
  simpa [htop] using h

/-- The fixed subgroup of a generated subgroup is the intersection of the fixed subgroups.

This is the formal version of the Theorem 7.5 step: if both `P` and `Q` act trivially on `U`,
then so does `⟨P, Q⟩`. -/
theorem actionCentralizer_sup {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P Q : Subgroup A) :
    actionCentralizer φ (P ⊔ Q) = actionCentralizer φ P ⊓ actionCentralizer φ Q := by
  ext v
  constructor
  · intro hv
    exact ⟨actionCentralizer_antitone (show P ≤ P ⊔ Q from le_sup_left) hv,
      actionCentralizer_antitone (show Q ≤ P ⊔ Q from le_sup_right) hv⟩
  · rintro ⟨hP, hQ⟩ x
    have hx : (x : A) ∈ Subgroup.closure ((P : Set A) ∪ (Q : Set A)) := by
      simpa [Subgroup.sup_eq_closure] using x.property
    refine Subgroup.closure_induction
      (p := fun a _ => (φ a) v = v) ?mem ?one ?mul ?inv hx
    · intro a ha
      rcases ha with ha | ha
      · exact hP ⟨a, ha⟩
      · exact hQ ⟨a, ha⟩
    · simp
    · intro a b _ _ ha hb
      simp [map_mul, hb, ha]
    · intro a _ ha
      calc
        (φ a⁻¹) v = (φ a)⁻¹ v := by rw [map_inv]
        _ = (φ a)⁻¹ ((φ a) v) := by rw [ha]
        _ = v := MulAut.inv_apply_self V (φ a) v

/-- The index of the fixed subgroup for `P ⊔ Q` is bounded by the product of the two
individual fixed-subgroup indices. -/
theorem actionCentralizer_sup_index_le {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P Q : Subgroup A) :
    (actionCentralizer φ (P ⊔ Q)).index ≤
      (actionCentralizer φ P).index * (actionCentralizer φ Q).index := by
  rw [actionCentralizer_sup]
  exact Subgroup.index_inf_le

/-- A packaged version of `actionCentralizer_sup_index_le` with external bounds. -/
theorem actionCentralizer_sup_index_le_of_le {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P Q : Subgroup A) {m n : ℕ}
    (hP : (actionCentralizer φ P).index ≤ m)
    (hQ : (actionCentralizer φ Q).index ≤ n) :
    (actionCentralizer φ (P ⊔ Q)).index ≤ m * n :=
  (actionCentralizer_sup_index_le φ P Q).trans (Nat.mul_le_mul hP hQ)

/-- The Theorem 7.5 index estimate: if both fixed subgroups have index at most `p`, then
the fixed subgroup of `P ⊔ Q` has index at most `p^2`. -/
theorem actionCentralizer_sup_index_le_sq {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P Q : Subgroup A) {p : ℕ}
    (hP : (actionCentralizer φ P).index ≤ p)
    (hQ : (actionCentralizer φ Q).index ≤ p) :
    (actionCentralizer φ (P ⊔ Q)).index ≤ p ^ 2 := by
  calc
    (actionCentralizer φ (P ⊔ Q)).index ≤ p * p :=
      actionCentralizer_sup_index_le_of_le φ P Q hP hQ
    _ = p ^ 2 := by ring

/-- The same Theorem 7.5 index estimate, in the `U = C_V(P) ∩ C_V(Q)` form used in
the book proof. -/
theorem actionCentralizer_inf_index_le_sq {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P Q : Subgroup A) {p : ℕ}
    (hP : (actionCentralizer φ P).index ≤ p)
    (hQ : (actionCentralizer φ Q).index ≤ p) :
    (actionCentralizer φ P ⊓ actionCentralizer φ Q).index ≤ p ^ 2 := by
  rw [← actionCentralizer_sup]
  exact actionCentralizer_sup_index_le_sq φ P Q hP hQ

/-- If `V` is a finite `p`-group and both `C_V(P)` and `C_V(Q)` have index at most `p`,
then `C_V(P) ∩ C_V(Q)` is normal in `V`.

This supplies the `U ⊴ V` bridge before the quotient `V/U` in Isaacs Thm 7.5. -/
theorem actionCentralizer_inf_normal_of_index_le_prime
    {A V : Type*} [Group A] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime] (hV : IsPGroup p V)
    {φ : A →* MulAut V} {P Q : Subgroup A}
    (hP : (actionCentralizer φ P).index ≤ p)
    (hQ : (actionCentralizer φ Q).index ≤ p) :
    (actionCentralizer φ P ⊓ actionCentralizer φ Q).Normal := by
  have hPN : (actionCentralizer φ P).Normal :=
    normal_of_isPGroup_index_le_prime hV hP
  have hQN : (actionCentralizer φ Q).Normal :=
    normal_of_isPGroup_index_le_prime hV hQ
  letI : (actionCentralizer φ P).Normal := hPN
  letI : (actionCentralizer φ Q).Normal := hQN
  infer_instance

/-- Quotient-cardinality form of the Theorem 7.5 index estimate:
if both `C_V(P)` and `C_V(Q)` have index at most `p`, then
`|V / (C_V(P) ∩ C_V(Q))| ≤ p²`. -/
theorem quotient_card_le_prime_sq_of_actionCentralizer_inf
    {A V : Type*} [Group A] [Group V] (φ : A →* MulAut V) (P Q : Subgroup A)
    {p : ℕ} [(actionCentralizer φ P ⊓ actionCentralizer φ Q).Normal]
    (hP : (actionCentralizer φ P).index ≤ p)
    (hQ : (actionCentralizer φ Q).index ≤ p) :
    Nat.card (V ⧸ (actionCentralizer φ P ⊓ actionCentralizer φ Q)) ≤ p ^ 2 := by
  simpa [Subgroup.index_eq_card] using actionCentralizer_inf_index_le_sq φ P Q hP hQ

/-- The Theorem 7.5 quotient reduction: in the `U = C_V(P) ∩ C_V(Q)` quotient, if the
quotient is noncyclic then it is elementary abelian of order `p²`.

This packages the index estimate with the small-order noncyclic `p`-group bridge from
`OddOrder.GroupTheory.ElementaryAbelian`. -/
theorem quotient_isElementaryAbelian_card_prime_sq_of_actionCentralizer_inf_not_isCyclic
    {A V : Type*} [Group A] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime] (φ : A →* MulAut V) (P Q : Subgroup A)
    [(actionCentralizer φ P ⊓ actionCentralizer φ Q).Normal]
    (hV : IsPGroup p V)
    (hP : (actionCentralizer φ P).index ≤ p)
    (hQ : (actionCentralizer φ Q).index ≤ p)
    (hNotCyclic : ¬ IsCyclic (V ⧸ (actionCentralizer φ P ⊓ actionCentralizer φ Q))) :
    OddOrder.GroupTheory.IsElementaryAbelian p
        (V ⧸ (actionCentralizer φ P ⊓ actionCentralizer φ Q)) ∧
      Nat.card (V ⧸ (actionCentralizer φ P ⊓ actionCentralizer φ Q)) = p ^ 2 :=
  IsPGroup.isElementaryAbelian_card_prime_sq_of_card_le_prime_sq_of_not_isCyclic
    (hV.to_quotient (actionCentralizer φ P ⊓ actionCentralizer φ Q))
    (quotient_card_le_prime_sq_of_actionCentralizer_inf φ P Q hP hQ)
    hNotCyclic

/-- Any subgroup fixed pointwise by the whole acting group is invariant under the action. -/
theorem isAInvariant_of_le_actionCentralizer_top {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {U : Subgroup V}
    (hU : U ≤ actionCentralizer φ (⊤ : Subgroup A)) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ U := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a u hu
  rw [(mem_actionCentralizer_top.mp (hU hu)) a]
  exact hu

/-- If `G = ⟨P, Q⟩`, then `U = C_V(P) ∩ C_V(Q)` is invariant under the whole action.

This is the invariant-subgroup bridge needed before passing to `V/U` in Isaacs Thm 7.5. -/
theorem actionCentralizer_inf_isAInvariant_of_sup_eq_top
    {A V : Type*} [Group A] [Group V] {φ : A →* MulAut V}
    {P Q : Subgroup A} (hPQ : P ⊔ Q = ⊤) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ
      (actionCentralizer φ P ⊓ actionCentralizer φ Q) := by
  apply isAInvariant_of_le_actionCentralizer_top
  rw [← actionCentralizer_sup, hPQ]

/-- If `U ≤ C`, then the image of `C` in `V/U` has the same index as `C`.

This is the quotient-index bridge behind the Theorem 7.5 passage from `V` to `V/U`. -/
theorem quotient_image_index_eq_of_le {V : Type*} [Group V]
    {U C : Subgroup V} [U.Normal] (hUC : U ≤ C) :
    (C.map (QuotientGroup.mk' U)).index = C.index :=
  Subgroup.index_map_eq C (QuotientGroup.mk'_surjective U) (by
    rw [QuotientGroup.ker_mk']
    exact hUC)

/-- Action-centralizer version of `quotient_image_index_eq_of_le`: if `U ≤ C_V(P)`,
then `C_V(P)/U` has the same index in `V/U` as `C_V(P)` has in `V`. -/
theorem actionCentralizer_quotient_image_index_eq_of_le
    {A V : Type*} [Group A] [Group V] (φ : A →* MulAut V)
    (P : Subgroup A) {U : Subgroup V} [U.Normal]
    (hU : U ≤ actionCentralizer φ P) :
    ((actionCentralizer φ P).map (QuotientGroup.mk' U)).index =
      (actionCentralizer φ P).index :=
  quotient_image_index_eq_of_le hU

/-- The induced action on `V/U` for an invariant normal subgroup `U`. -/
noncomputable def quotientActionHom {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) : A →* MulAut (V ⧸ U) :=
  OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hU

@[simp]
theorem quotientActionHom_apply_mk' {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) (a : A) (v : V) :
    (quotientActionHom φ hU a) (QuotientGroup.mk' U v) =
      QuotientGroup.mk' U ((φ a) v) :=
  OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk'
    hU a v

/-- The image of `C_V(P)` in `V/U` is fixed by `P` for the induced quotient action. -/
theorem actionCentralizer_quotient_image_le_quotientActionHom_actionCentralizer
    {A V : Type*} [Group A] [Group V] {φ : A →* MulAut V}
    {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) (P : Subgroup A) :
    (actionCentralizer φ P).map (QuotientGroup.mk' U) ≤
      actionCentralizer (quotientActionHom φ hU) P := by
  rintro _ ⟨v, hv, rfl⟩ p
  change (quotientActionHom φ hU (p : A)) (QuotientGroup.mk' U v) =
    QuotientGroup.mk' U v
  rw [quotientActionHom_apply_mk']
  exact congrArg (QuotientGroup.mk' U) (hv p)

/-- Kernel of the induced action on `V/U`. In Isaacs Thm 7.5 this is the subgroup `K`
acting trivially on `V/U`. -/
noncomputable def quotientActionKernel {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) : Subgroup A :=
  (quotientActionHom φ hU).ker

/-- The kernel of the induced quotient action is normal in the acting group. -/
instance quotientActionKernel_normal {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) :
    (quotientActionKernel φ hU).Normal := by
  change (quotientActionHom φ hU).ker.Normal
  infer_instance

/-- The faithful action of `A/K` on `V/U`, where `K` is the kernel of the induced action.

This is the formal version of the Thm 7.5 step "the quotient group `G/K` acts faithfully on
`V/U`". -/
noncomputable def quotientActionFaithfulHom {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) :
    A ⧸ quotientActionKernel φ hU →* MulAut (V ⧸ U) :=
  QuotientGroup.kerLift (quotientActionHom φ hU)

@[simp]
theorem quotientActionFaithfulHom_mk' {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) (a : A) :
    quotientActionFaithfulHom φ hU
        (QuotientGroup.mk' (quotientActionKernel φ hU) a) =
      quotientActionHom φ hU a :=
  rfl

/-- In the faithful quotient action of `A/K` on `V/U`, the image of `C_V(P)` is fixed by
the image of `P`. -/
theorem actionCentralizer_quotient_image_le_quotientActionFaithful_actionCentralizer
    {A V : Type*} [Group A] [Group V] {φ : A →* MulAut V}
    {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) (P : Subgroup A) :
    (actionCentralizer φ P).map (QuotientGroup.mk' U) ≤
      actionCentralizer (quotientActionFaithfulHom φ hU)
        (P.map (QuotientGroup.mk' (quotientActionKernel φ hU))) := by
  rintro _ ⟨v, hv, rfl⟩ pbar
  rcases pbar.property with ⟨p, hpP, hp_eq⟩
  have hfix :
      (quotientActionHom φ hU p) (QuotientGroup.mk' U v) =
        QuotientGroup.mk' U v := by
    rw [quotientActionHom_apply_mk']
    exact congrArg (QuotientGroup.mk' U) (hv ⟨p, hpP⟩)
  have hpbar : (pbar : A ⧸ quotientActionKernel φ hU) =
      QuotientGroup.mk' (quotientActionKernel φ hU) p := hp_eq.symm
  change (quotientActionFaithfulHom φ hU (pbar : A ⧸ quotientActionKernel φ hU))
      (QuotientGroup.mk' U v) = QuotientGroup.mk' U v
  rw [hpbar, quotientActionFaithfulHom_mk']
  exact hfix

/-- The fixed-subgroup index hypothesis descends to the faithful quotient action on `V/U`. -/
theorem actionCentralizer_quotientActionFaithful_index_le
    {A V : Type*} [Group A] [Group V] [Finite V] {φ : A →* MulAut V}
    {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) (P : Subgroup A) {p : ℕ}
    (hU_le : U ≤ actionCentralizer φ P)
    (hP : (actionCentralizer φ P).index ≤ p) :
    (actionCentralizer (quotientActionFaithfulHom φ hU)
        (P.map (QuotientGroup.mk' (quotientActionKernel φ hU)))).index ≤ p := by
  have hle := actionCentralizer_quotient_image_le_quotientActionFaithful_actionCentralizer
    hU P
  calc
    (actionCentralizer (quotientActionFaithfulHom φ hU)
        (P.map (QuotientGroup.mk' (quotientActionKernel φ hU)))).index
        ≤ ((actionCentralizer φ P).map (QuotientGroup.mk' U)).index :=
          Subgroup.index_antitone hle
    _ = (actionCentralizer φ P).index :=
          actionCentralizer_quotient_image_index_eq_of_le φ P hU_le
    _ ≤ p := hP

/-- The action of `A/K` on `V/U` is faithful by construction. -/
theorem quotientActionFaithfulHom_injective {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) :
    Function.Injective (quotientActionFaithfulHom φ hU) := by
  dsimp [quotientActionFaithfulHom, quotientActionKernel]
  exact QuotientGroup.kerLift_injective (quotientActionHom φ hU)

/-- If `K` lies in the kernel of the quotient action on `V/U`, then `[V,K] ≤ U`.

This is the formal quotient-kernel bridge used in Isaacs Thm 7.5 after passing from
`V` to `V/U`. -/
theorem actionCommutator_le_of_le_quotientActionKernel
    {A V : Type*} [Group A] [Group V] {φ : A →* MulAut V}
    {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    {K : Subgroup A} (hK : K ≤ quotientActionKernel φ hU) :
    OddOrder.Isaacs.Ch04.actionCommutator (φ.comp K.subtype) ≤ U := by
  rw [OddOrder.Isaacs.Ch04.actionCommutator_le_iff_left]
  intro k v
  have hk : quotientActionHom φ hU (k : A) = 1 := by
    change (k : A) ∈ (quotientActionHom φ hU).ker
    exact hK k.property
  have hq :
      quotientActionHom φ hU (k : A) (QuotientGroup.mk' U v) =
        (1 : MulAut (V ⧸ U)) (QuotientGroup.mk' U v) := by
    rw [hk]
  rw [quotientActionHom_apply_mk'] at hq
  simp only [MulAut.one_apply] at hq
  change (((φ (k : A)) v : V) : V ⧸ U) = (v : V ⧸ U) at hq
  rw [QuotientGroup.eq] at hq
  simpa [mul_inv_rev] using U.inv_mem hq

/-- Kernel-specialized form of `actionCommutator_le_of_le_quotientActionKernel`. -/
theorem actionCommutator_quotientActionKernel_le
    {A V : Type*} [Group A] [Group V] {φ : A →* MulAut V}
    {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) :
    OddOrder.Isaacs.Ch04.actionCommutator
      (φ.comp (quotientActionKernel φ hU).subtype) ≤ U :=
  actionCommutator_le_of_le_quotientActionKernel hU le_rfl

/-- If `U` is fixed pointwise by the whole acting group and `K` acts trivially on `V/U`,
then `K` acts trivially on `[V,K]`.

This is the Ch07-side formalization of the Thm 7.5 step `[V,K,K] = 1`. -/
theorem actionCommutator_le_fixedPoints_of_le_quotientActionKernel
    {A V : Type*} [Group A] [Group V] {φ : A →* MulAut V}
    {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    (hU_top : U ≤ actionCentralizer φ (⊤ : Subgroup A))
    {K : Subgroup A} (hK : K ≤ quotientActionKernel φ hU) :
    OddOrder.Isaacs.Ch04.actionCommutator (φ.comp K.subtype) ≤
      Subgroup.fixedPointsOfMulAut (φ.comp K.subtype) := by
  intro v hv k
  have hvU : v ∈ U := actionCommutator_le_of_le_quotientActionKernel hU hK hv
  exact (mem_actionCentralizer_top.mp (hU_top hvU)) (k : A)

/-- Kernel-specialized form: the kernel `K` of the quotient action satisfies `[V,K,K]=1`
when `U` is fixed pointwise by the original action. -/
theorem actionCommutator_quotientActionKernel_le_fixedPoints
    {A V : Type*} [Group A] [Group V] {φ : A →* MulAut V}
    {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    (hU_top : U ≤ actionCentralizer φ (⊤ : Subgroup A)) :
    OddOrder.Isaacs.Ch04.actionCommutator
        (φ.comp (quotientActionKernel φ hU).subtype) ≤
      Subgroup.fixedPointsOfMulAut (φ.comp (quotientActionKernel φ hU).subtype) :=
  actionCommutator_le_fixedPoints_of_le_quotientActionKernel hU hU_top le_rfl

/-- Semidirect-product bridge: the condition `[V,A,A]=1`, expressed as
`[V,A] ≤ C_V(A)`, gives the length-two iterated commutator vanishing used by the Ch.4
faithful-action prime-divisor theorem. -/
theorem iterCommutator_inl_inr_two_eq_bot_of_actionCommutator_le_fixedPoints
    {A V : Type*} [Group A] [Group V] (φ : A →* MulAut V)
    (h_triv : OddOrder.Isaacs.Ch04.actionCommutator φ ≤
      Subgroup.fixedPointsOfMulAut φ) :
    OddOrder.Isaacs.Ch04.iterCommutator
        (SemidirectProduct.inl : V →* V ⋊[φ] A).range
        (SemidirectProduct.inr : A →* V ⋊[φ] A).range 2 = ⊥ := by
  rw [OddOrder.Isaacs.Ch04.iterCommutator_succ,
    OddOrder.Isaacs.Ch04.iterCommutator_succ,
    OddOrder.Isaacs.Ch04.iterCommutator_zero]
  rw [← OddOrder.Isaacs.Ch04.actionCommutator_map_inl φ]
  rw [eq_bot_iff, Subgroup.commutator_le]
  rintro _ ⟨v, hv, rfl⟩ _ ⟨a, rfl⟩
  rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
  have h_fix : (φ a) v = v := h_triv hv a
  rw [show (φ a) v⁻¹ = ((φ a) v)⁻¹ from map_inv (φ a) v,
    h_fix, mul_inv_cancel]
  exact map_one _

/-- If a faithful finite group action on a finite `p`-group has quotient-action kernel `K`
with `[V,K,K]=1`, then `K` is a `p`-group.

This packages the Ch.4 faithful iterated-commutator theorem for the kernel arising in
Isaacs Thm 7.5. -/
theorem quotientActionKernel_isPGroup_of_faithful_of_isPGroup
    {A V : Type*} [Group A] [Group V] [Finite A] [Finite V]
    {p : ℕ} [Fact p.Prime] {φ : A →* MulAut V}
    {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    (hφ : Function.Injective φ) (hV : IsPGroup p V)
    (hU_top : U ≤ actionCentralizer φ (⊤ : Subgroup A)) :
    IsPGroup p (quotientActionKernel φ hU) := by
  set K : Subgroup A := quotientActionKernel φ hU with hK_def
  let ψ : K →* MulAut V := φ.comp K.subtype
  have hψ : Function.Injective ψ := by
    intro x y hxy
    apply Subtype.ext
    exact hφ hxy
  have h_triv : OddOrder.Isaacs.Ch04.actionCommutator ψ ≤
      Subgroup.fixedPointsOfMulAut ψ := by
    simpa [ψ, K, hK_def] using
      actionCommutator_quotientActionKernel_le_fixedPoints hU hU_top
  have h_iter :
      OddOrder.Isaacs.Ch04.iterCommutator
          (SemidirectProduct.inl : V →* V ⋊[ψ] K).range
          (SemidirectProduct.inr : K →* V ⋊[ψ] K).range 2 = ⊥ :=
    iterCommutator_inl_inr_two_eq_bot_of_actionCommutator_le_fixedPoints ψ h_triv
  have hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)
      (⊤ : Subgroup K) := by
    intro q hq
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hq_dvd_K : q ∣ Nat.card K := by
      simpa [Subgroup.card_top] using Nat.dvd_of_mem_primeFactors hq
    have hq_dvd_V : q ∣ Nat.card V :=
      OddOrder.Isaacs.Ch04.prime_dvd_card_of_faithful_iterCommutator_eq_bot
        ψ hψ (m := 2) (by norm_num) h_iter hq_prime hq_dvd_K
    have hV_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)
        (⊤ : Subgroup V) :=
      OddOrder.Isaacs.Ch04.isPiGroup_singleton_of_isPGroup
        (G := V) (H := (⊤ : Subgroup V)) (hV.to_subgroup _)
    have hqV : q ∈ (Nat.card (⊤ : Subgroup V)).primeFactors := by
      rw [Subgroup.card_top]
      exact Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd_V, Nat.card_pos.ne'⟩
    exact hV_pi q hqV
  have hK_top_p : IsPGroup p (⊤ : Subgroup K) :=
    OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton
      (G := K) (H := (⊤ : Subgroup K)) hK_pi
  simpa [K, hK_def] using hK_top_p.of_equiv Subgroup.topEquiv

/-- The `U = C_V(P) ∩ C_V(Q)` specialization of
`quotientActionKernel_isPGroup_of_faithful_of_isPGroup`.

Normality of this fixed-point intersection is kept as an explicit hypothesis; in the book proof
this is the preceding `U ⊴ V` step. -/
theorem actionCentralizer_inf_quotientActionKernel_isPGroup_of_sup_eq_top
    {A V : Type*} [Group A] [Group V] [Finite A] [Finite V]
    {p : ℕ} [Fact p.Prime] {φ : A →* MulAut V}
    {P Q : Subgroup A}
    [hU_normal : (actionCentralizer φ P ⊓ actionCentralizer φ Q).Normal]
    (hPQ : P ⊔ Q = ⊤) (hφ : Function.Injective φ) (hV : IsPGroup p V) :
    IsPGroup p (quotientActionKernel φ
      (actionCentralizer_inf_isAInvariant_of_sup_eq_top (φ := φ) hPQ)) := by
  apply quotientActionKernel_isPGroup_of_faithful_of_isPGroup
  · exact hφ
  · exact hV
  · rw [← actionCentralizer_sup, hPQ]

/-- Normality of the image of `P` in `G/K` pulls back to normality of `P`, provided
`K ≤ P`.

This is the quotient-correspondence bridge used in Isaacs Thm 7.5 after proving the image
of a Sylow subgroup is normal in the faithful quotient action. -/
theorem normal_of_quotient_image_normal_of_le
    {G : Type*} [Group G] {K P : Subgroup G} [K.Normal]
    (hKP : K ≤ P)
    (hPbar : (P.map (QuotientGroup.mk' K)).Normal) :
    P.Normal := by
  have hcomap :
      Subgroup.comap (QuotientGroup.mk' K) (P.map (QuotientGroup.mk' K)) = P := by
    rw [QuotientGroup.comap_map_mk']
    exact sup_eq_right.mpr hKP
  rw [← hcomap]
  exact hPbar.comap (QuotientGroup.mk' K)

/-- A normal `p`-subgroup is contained in every Sylow `p`-subgroup. -/
private theorem normal_isPGroup_le_sylow
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)]
    {K : Subgroup G} [K.Normal] (hK : IsPGroup p K) (P : Sylow p G) :
    K ≤ (P : Subgroup G) :=
  (OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hK).trans
    (OddOrder.Isaacs.Ch01.opCore_le P)

/-- If a normal `p`-subgroup `K` is quotiented out, normality of the image of a Sylow
`p`-subgroup pulls back to normality of the original Sylow subgroup. -/
theorem sylow_normal_of_quotient_image_normal_of_normal_isPGroup
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) {K : Subgroup G} [K.Normal] (hK : IsPGroup p K)
    (hPbar : (((P : Subgroup G).map (QuotientGroup.mk' K))).Normal) :
    P.Normal :=
  normal_of_quotient_image_normal_of_le (normal_isPGroup_le_sylow hK P) hPbar

/-- If two subgroups both contain the quotient kernel, equality of their images in the
quotient implies equality upstairs.

This is the subgroup-correspondence step used in Isaacs Thm 7.5 to keep the two Sylow
subgroups distinct after quotienting by the action kernel. -/
theorem quotient_images_ne_of_ne_of_le
    {G : Type*} [Group G] {K P Q : Subgroup G} [K.Normal]
    (hKP : K ≤ P) (hKQ : K ≤ Q) (hPQ : P ≠ Q) :
    P.map (QuotientGroup.mk' K) ≠ Q.map (QuotientGroup.mk' K) := by
  intro hmap
  apply hPQ
  have hPcomap :
      Subgroup.comap (QuotientGroup.mk' K) (P.map (QuotientGroup.mk' K)) = P := by
    rw [QuotientGroup.comap_map_mk']
    exact sup_eq_right.mpr hKP
  have hQcomap :
      Subgroup.comap (QuotientGroup.mk' K) (Q.map (QuotientGroup.mk' K)) = Q := by
    rw [QuotientGroup.comap_map_mk']
    exact sup_eq_right.mpr hKQ
  rw [← hPcomap, ← hQcomap, hmap]

/-- Quotienting by a normal `p`-subgroup preserves distinctness of Sylow images. -/
theorem quotient_sylow_images_ne_of_ne_of_normal_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P Q : Sylow p G} (hPQ : P ≠ Q)
    {K : Subgroup G} [K.Normal] (hK : IsPGroup p K) :
    P.mapSurjective (QuotientGroup.mk'_surjective K) ≠
      Q.mapSurjective (QuotientGroup.mk'_surjective K) := by
  intro hmap
  haveI : Finite (Sylow p G) := P.finite_of_finiteIndex
  have hsub_ne :
      (P : Subgroup G).map (QuotientGroup.mk' K) ≠
        (Q : Subgroup G).map (QuotientGroup.mk' K) :=
    quotient_images_ne_of_ne_of_le
      (normal_isPGroup_le_sylow hK P)
      (normal_isPGroup_le_sylow hK Q)
      (fun hsub => hPQ (Sylow.ext hsub))
  apply hsub_ne
  have hsub_eq := congrArg
    (fun R : Sylow p (G ⧸ K) => (R : Subgroup (G ⧸ K))) hmap
  simpa using hsub_eq

/-- If the quotient image of `P` were normal, then `P` would already be normal upstairs. -/
theorem quotient_sylow_image_not_normal_of_not_normal_of_normal_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {K : Subgroup G} [K.Normal] (hK : IsPGroup p K)
    (hP_not_normal : ¬ (P : Subgroup G).Normal) :
    ¬ (((P.mapSurjective (QuotientGroup.mk'_surjective K) :
          Sylow p (G ⧸ K)) : Subgroup (G ⧸ K)).Normal) := by
  intro hPbar
  haveI : Finite (Sylow p G) := P.finite_of_finiteIndex
  exact hP_not_normal
    (sylow_normal_of_quotient_image_normal_of_normal_isPGroup
      (G := G) (p := p) P (K := K) hK (by simpa using hPbar))

/-- The hypothesis that every `2`-subgroup is abelian descends to a quotient.

This is the Sylow-lift bridge needed in Isaacs Thm 7.5 for applying the reduced theorem to
`G/K`: a `2`-subgroup of `G/K` is the image of a Sylow `2`-subgroup of its preimage, and
that Sylow subgroup is abelian by the upstairs hypothesis. -/
theorem quotient_two_subgroup_abelian
    {G : Type*} [Group G] [Finite G] {K : Subgroup G} [K.Normal]
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (S : Subgroup (G ⧸ K)) (hS2 : IsPGroup 2 S) :
    ∀ x y : ↥S, x * y = y * x := by
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let T : Subgroup G := Subgroup.comap q S
  let f : T →* S :=
    { toFun := fun t => ⟨q t, t.property⟩
      map_one' := by
        ext
        simp [q]
      map_mul' := by
        intro a b
        ext
        simp [q] }
  have hf : Function.Surjective f := by
    intro s
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective K (s : G ⧸ K)
    refine ⟨⟨g, ?_⟩, ?_⟩
    · change q g ∈ S
      simp [q, hg, s.property]
    · ext
      simpa [f, q] using hg
  let R : Sylow 2 T := default
  let Rbar : Sylow 2 S := R.mapSurjective hf
  have hRbar_top : (Rbar : Subgroup S) = ⊤ := by
    have htop2 : IsPGroup 2 (⊤ : Subgroup S) := hS2.to_subgroup ⊤
    exact (Rbar.is_maximal' htop2 le_top).symm
  have hRcomm : ∀ a b : ↥R, a * b = b * a := by
    have hRG2 : IsPGroup 2 ((R : Subgroup T).map T.subtype) :=
      R.isPGroup'.map T.subtype
    have hRGcomm := h2abelian ((R : Subgroup T).map T.subtype) hRG2
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    let ag : ↥((R : Subgroup T).map T.subtype) :=
      ⟨((a : T) : G), ⟨(a : T), a.property, rfl⟩⟩
    let bg : ↥((R : Subgroup T).map T.subtype) :=
      ⟨((b : T) : G), ⟨(b : T), b.property, rfl⟩⟩
    have h := congrArg (fun z : ↥((R : Subgroup T).map T.subtype) => (z : G))
      (hRGcomm ag bg)
    simpa using h
  intro x y
  have hxRbar : x ∈ (Rbar : Subgroup S) := by
    rw [hRbar_top]
    trivial
  have hyRbar : y ∈ (Rbar : Subgroup S) := by
    rw [hRbar_top]
    trivial
  rw [Sylow.coe_mapSurjective] at hxRbar hyRbar
  rcases hxRbar with ⟨rx, hrx, hfx⟩
  rcases hyRbar with ⟨ry, hry, hfy⟩
  let rxR : R := ⟨rx, hrx⟩
  let ryR : R := ⟨ry, hry⟩
  have hxyT : rx * ry = ry * rx :=
    congrArg (fun z : ↥R => (z : T)) (hRcomm rxR ryR)
  calc
    x * y = f rx * f ry := by rw [← hfx, ← hfy]
    _ = f (rx * ry) := by rw [map_mul]
    _ = f (ry * rx) := by rw [hxyT]
    _ = f ry * f rx := by rw [map_mul]
    _ = y * x := by rw [hfy, hfx]

/-- Elementary-abelian quotient branch of Isaacs Thm 7.5 after passing to the faithful
action of `G/K` on `V/U`.

This is the quotient-condition bundle for the reduced theorem:
`p`-separability descends by Ch03, the `2`-subgroup abelian hypothesis descends by
`quotient_two_subgroup_abelian`, and faithfulness is by construction of
`quotientActionFaithfulHom`. -/
theorem quotient_sylow_normal_of_elementaryAbelian_card_prime_sq_of_actionKernel
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hp2 : p ≠ 2)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    {φ : G →* MulAut V} {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    (hVelem : OddOrder.GroupTheory.IsElementaryAbelian p (V ⧸ U))
    (hVcard : Nat.card (V ⧸ U) = p ^ 2) (P : Sylow p G) :
    (((P.mapSurjective (QuotientGroup.mk'_surjective (quotientActionKernel φ hU)) :
          Sylow p (G ⧸ quotientActionKernel φ hU)) : Subgroup
          (G ⧸ quotientActionKernel φ hU))).Normal := by
  haveI hSepQuot :
      OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ)
        (G ⧸ quotientActionKernel φ hU) :=
    OddOrder.Isaacs.Ch03.quotient_isPiSeparable
      ({p} : Set ℕ) G (quotientActionKernel φ hU)
  exact sylow_normal_of_elementaryAbelian_card_prime_sq_of_faithful
    (G := G ⧸ quotientActionKernel φ hU) (V := V ⧸ U) (p := p)
    hp2 (quotient_two_subgroup_abelian h2abelian)
    (φ := quotientActionFaithfulHom φ hU)
    (quotientActionFaithfulHom_injective hU) hVelem hVcard
    (P.mapSurjective (QuotientGroup.mk'_surjective (quotientActionKernel φ hU)))

/-- Contradiction form of the elementary-abelian quotient branch of Isaacs Thm 7.5.

If the action kernel `K` is a normal `p`-subgroup and the faithful quotient action on `V/U`
has elementary-abelian order `p²`, the reduced branch proves the image of `P` normal in
`G/K`; pulling normality back contradicts a counterexample assumption upstairs. -/
theorem false_of_quotient_elementaryAbelian_card_prime_sq_of_sylow_not_normal
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hp2 : p ≠ 2)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    {φ : G →* MulAut V} {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    (hK : IsPGroup p (quotientActionKernel φ hU))
    (hVelem : OddOrder.GroupTheory.IsElementaryAbelian p (V ⧸ U))
    (hVcard : Nat.card (V ⧸ U) = p ^ 2) (P : Sylow p G)
    (hP_not_normal : ¬ (P : Subgroup G).Normal) : False :=
  hP_not_normal
    (sylow_normal_of_quotient_image_normal_of_normal_isPGroup
      (G := G) (p := p) P (K := quotientActionKernel φ hU) hK
      (quotient_sylow_normal_of_elementaryAbelian_card_prime_sq_of_actionKernel
        hp2 h2abelian hU hVelem hVcard P))

/-- Cyclic quotient branch of Isaacs Thm 7.5 after passing to the faithful action of
`G/K` on `V/U`.

If `V/U` is cyclic, then `Aut(V/U)` is abelian. Since the quotient action is faithful,
`G/K` is abelian, so the image of any Sylow subgroup is normal. -/
theorem quotient_sylow_normal_of_isCyclic_of_actionKernel
    {G V : Type*} [Group G] [Finite G] [Group V]
    {p : ℕ} [Fact p.Prime]
    {φ : G →* MulAut V} {U : Subgroup V} [U.Normal] [IsCyclic (V ⧸ U)]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) (P : Sylow p G) :
    (((P.mapSurjective (QuotientGroup.mk'_surjective (quotientActionKernel φ hU)) :
          Sylow p (G ⧸ quotientActionKernel φ hU)) : Subgroup
          (G ⧸ quotientActionKernel φ hU))).Normal :=
  subgroup_normal_of_injective_mulAut_of_isCyclic
    (A := G ⧸ quotientActionKernel φ hU) (V := V ⧸ U)
    (φ := quotientActionFaithfulHom φ hU)
    (quotientActionFaithfulHom_injective hU)
    ((P.mapSurjective (QuotientGroup.mk'_surjective (quotientActionKernel φ hU)) :
      Sylow p (G ⧸ quotientActionKernel φ hU)) : Subgroup
        (G ⧸ quotientActionKernel φ hU))

/-- Contradiction form of the cyclic quotient branch of Isaacs Thm 7.5. -/
theorem false_of_quotient_isCyclic_of_sylow_not_normal
    {G V : Type*} [Group G] [Finite G] [Group V]
    {p : ℕ} [Fact p.Prime]
    {φ : G →* MulAut V} {U : Subgroup V} [U.Normal] [IsCyclic (V ⧸ U)]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    (hK : IsPGroup p (quotientActionKernel φ hU)) (P : Sylow p G)
    (hP_not_normal : ¬ (P : Subgroup G).Normal) : False :=
  hP_not_normal
    (sylow_normal_of_quotient_image_normal_of_normal_isPGroup
      (G := G) (p := p) P (K := quotientActionKernel φ hU) hK
      (quotient_sylow_normal_of_isCyclic_of_actionKernel hU P))

/-- Descend the action-centralizer index hypothesis from `G` to a subgroup `H`.

For every Sylow `R : Sylow p H`, the image `R.map H.subtype` is a `p`-subgroup of `G`,
hence contained in some Sylow `S : Sylow p G`.  Antitonicity of `actionCentralizer`
then gives `(actionCentralizer (φ.comp H.subtype) R).index ≤ (actionCentralizer φ S).index`,
which is bounded by `p` by the upstairs hypothesis. -/
private theorem actionCentralizer_comp_subtype_index_le_of_globalHypothesis
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime]
    {φ : G →* MulAut V}
    (h_centralizer_index :
      ∀ (P : Sylow p G), (actionCentralizer φ (P : Subgroup G)).index ≤ p)
    (H : Subgroup G) (R : Sylow p H) :
    (actionCentralizer (φ.comp H.subtype) (R : Subgroup H)).index ≤ p := by
  -- The image of `R` in `G` is a `p`-subgroup of `G`.
  have hRG_p : IsPGroup p ((R : Subgroup H).map H.subtype) :=
    R.isPGroup'.map H.subtype
  obtain ⟨S, hS_le⟩ := hRG_p.exists_le_sylow
  have h_eq :
      actionCentralizer (φ.comp H.subtype) (R : Subgroup H) =
        actionCentralizer φ ((R : Subgroup H).map H.subtype) := by
    ext v
    simp only [mem_actionCentralizer]
    constructor
    · intro hv g
      rcases g.property with ⟨r, hrR, hrg⟩
      have hfix := hv ⟨r, hrR⟩
      change (φ ((r : H) : G)) v = v at hfix
      rw [show (g : G) = ((r : H) : G) from hrg.symm]
      exact hfix
    · intro hv r
      have hr_mem : ((r : H) : G) ∈ (R : Subgroup H).map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype r.property
      exact hv ⟨((r : H) : G), hr_mem⟩
  rw [h_eq]
  -- Antitonicity in P direction: bigger P → smaller actionCentralizer.
  have h_anti :
      actionCentralizer φ (S : Subgroup G) ≤
        actionCentralizer φ ((R : Subgroup H).map H.subtype) :=
    actionCentralizer_antitone hS_le
  exact (Subgroup.index_antitone h_anti).trans (h_centralizer_index S)

/-- **Isaacs Thm 7.5** (normal-P theorem).

If `G` is `p`-solvable with `p ≠ 2`, every `2`-subgroup of `G` is abelian, `G` acts
faithfully on a finite `p`-group `V`, and `|V : C_V(P)| ≤ p` for every Sylow `p`-subgroup
`P`, then every Sylow `p`-subgroup of `G` is normal.

The proof is by strong induction on `|G|`.  If `G` has a unique Sylow `p`-subgroup, the
result is trivial.  Otherwise pick two distinct Sylows `P, Q`.  If `⟨P, Q⟩ ≠ G`, descend
to the subgroup `⟨P, Q⟩` and apply the induction hypothesis there.  When `⟨P, Q⟩ = G`,
the action-centralizer index estimate forces `|V/U| ≤ p²` for `U := C_V(P) ∩ C_V(Q)`, and
splitting on whether `V/U` is cyclic produces the contradiction via the elementary-abelian
or cyclic branch built up above. -/
theorem sylow_normal_of_elementary_normal_P_theorem
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hp2 : p ≠ 2)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    {φ : G →* MulAut V} (hφ : Function.Injective φ)
    (hV : IsPGroup p V)
    (h_centralizer_index :
      ∀ (P : Sylow p G), (actionCentralizer φ (P : Subgroup G)).index ≤ p)
    (P : Sylow p G) : (P : Subgroup G).Normal := by
  classical
  -- Strong induction on |G|, using an explicit motive.
  let motive : ℕ → Prop := fun n =>
    ∀ (G : Type _) [Group G] [Finite G] [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
      (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
      (φ : G →* MulAut V) (_hφ : Function.Injective φ)
      (_h_centralizer_index :
        ∀ (P : Sylow p G), (actionCentralizer φ (P : Subgroup G)).index ≤ p)
      (P : Sylow p G), Nat.card G = n → (P : Subgroup G).Normal
  suffices hmain : motive (Nat.card G) by
    exact hmain G h2abelian φ hφ h_centralizer_index P rfl
  refine Nat.strong_induction_on (Nat.card G) ?_
  intro n ih G _ _ _ h2abelian φ hφ h_centralizer_index P hcard
  by_contra hP_not_normal
  -- Sylows are not subsingleton, else `P` would be normal.
  have hNotSub : ¬ Subsingleton (Sylow p G) := by
    intro hSub
    exact hP_not_normal (Sylow.normal_of_subsingleton P)
  -- Pick Q ≠ P.
  haveI : Nontrivial (Sylow p G) := not_subsingleton_iff_nontrivial.mp hNotSub
  obtain ⟨Q, hQP⟩ := exists_ne P
  -- We have Q ≠ P; consider H := ⟨P, Q⟩ = P ⊔ Q.
  set H : Subgroup G := (P : Subgroup G) ⊔ (Q : Subgroup G) with hH_def
  by_cases hH_top : H = ⊤
  · -- §7A closing branch: H = ⊤.
    -- U := C_V(P) ∩ C_V(Q) is normal, A-invariant, with |V/U| ≤ p².
    have hPidx : (actionCentralizer φ (P : Subgroup G)).index ≤ p :=
      h_centralizer_index P
    have hQidx : (actionCentralizer φ (Q : Subgroup G)).index ≤ p :=
      h_centralizer_index Q
    haveI hU_normal :
        (actionCentralizer φ (P : Subgroup G) ⊓
            actionCentralizer φ (Q : Subgroup G)).Normal :=
      actionCentralizer_inf_normal_of_index_le_prime hV hPidx hQidx
    have hPQ_top : (P : Subgroup G) ⊔ (Q : Subgroup G) = ⊤ := by
      simpa [H, hH_def] using hH_top
    have hU_invariant :
        OddOrder.Isaacs.Ch03.IsAInvariant φ
          (actionCentralizer φ (P : Subgroup G) ⊓
            actionCentralizer φ (Q : Subgroup G)) :=
      actionCentralizer_inf_isAInvariant_of_sup_eq_top hPQ_top
    -- The action kernel K on V/U is a p-group.
    have hK_p :
        IsPGroup p (quotientActionKernel φ hU_invariant) := by
      have := actionCentralizer_inf_quotientActionKernel_isPGroup_of_sup_eq_top
        (φ := φ) (P := (P : Subgroup G)) (Q := (Q : Subgroup G))
        hPQ_top hφ hV
      simpa using this
    -- Split on cyclicity of V/U.
    by_cases hVU_cyclic :
        IsCyclic (V ⧸ (actionCentralizer φ (P : Subgroup G) ⊓
          actionCentralizer φ (Q : Subgroup G)))
    · -- Cyclic branch.
      haveI := hVU_cyclic
      exact
        false_of_quotient_isCyclic_of_sylow_not_normal
          (φ := φ) hU_invariant hK_p P hP_not_normal
    · -- Non-cyclic ⇒ elementary abelian of order p².
      obtain ⟨hVU_elem, hVU_card⟩ :=
        quotient_isElementaryAbelian_card_prime_sq_of_actionCentralizer_inf_not_isCyclic
          φ (P : Subgroup G) (Q : Subgroup G) hV hPidx hQidx hVU_cyclic
      exact
        false_of_quotient_elementaryAbelian_card_prime_sq_of_sylow_not_normal
          (φ := φ) hp2 h2abelian hU_invariant hK_p hVU_elem hVU_card P hP_not_normal
  · -- Generation reduction: descend to H = ⟨P, Q⟩ ≠ ⊤.
    have hHidx_gt : 1 < H.index :=
      Subgroup.one_lt_index_of_ne_top hH_top
    have hH_card_lt : Nat.card H < Nat.card G := by
      have hmul : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
      have hcard_pos : 0 < Nat.card H := Nat.card_pos
      calc
        Nat.card H = Nat.card H * 1 := (mul_one _).symm
        _ < Nat.card H * H.index := (Nat.mul_lt_mul_left hcard_pos).mpr hHidx_gt
        _ = Nat.card G := hmul
    -- P and Q sit inside H.
    have hP_le_H : (P : Subgroup G) ≤ H := by simpa [H, hH_def] using le_sup_left
    have hQ_le_H : (Q : Subgroup G) ≤ H := by simpa [H, hH_def] using le_sup_right
    -- View P as a Sylow of H.
    let P' : Sylow p H := P.subtype hP_le_H
    -- Descend hypothesis (i): IsPiSeparable on H.
    haveI : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H :=
      OddOrder.Isaacs.Ch03.Subgroup.isPiSeparable_of_isPiSeparable ({p} : Set ℕ) H
    -- Descend hypothesis (iii): 2-subgroup abelian.
    have h2abelian' :
        ∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x := by
      intro S hS2
      have hSG2 : IsPGroup 2 (S.map H.subtype) := hS2.map H.subtype
      have hSGcomm := h2abelian (S.map H.subtype) hSG2
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      let ag : ↥(S.map H.subtype) :=
        ⟨((a : H) : G), ⟨(a : H), a.property, rfl⟩⟩
      let bg : ↥(S.map H.subtype) :=
        ⟨((b : H) : G), ⟨(b : H), b.property, rfl⟩⟩
      have h := congrArg (fun z : ↥(S.map H.subtype) => (z : G)) (hSGcomm ag bg)
      simpa using h
    -- Descend hypothesis (iv): φ ∘ H.subtype is injective.
    have hφ' : Function.Injective (φ.comp H.subtype) := by
      intro a b hab
      apply Subtype.ext
      exact hφ hab
    -- Descend hypothesis (v).
    have h_centralizer_index' :
        ∀ (R : Sylow p H), (actionCentralizer (φ.comp H.subtype)
          (R : Subgroup H)).index ≤ p :=
      fun R =>
        actionCentralizer_comp_subtype_index_le_of_globalHypothesis
          (φ := φ) h_centralizer_index H R
    have hcard_lt : Nat.card H < n := by rw [← hcard]; exact hH_card_lt
    -- Apply IH to H.
    have hP'_normal : (P' : Subgroup H).Normal :=
      ih (Nat.card H) hcard_lt H h2abelian' (φ.comp H.subtype) hφ'
        h_centralizer_index' P' rfl
    -- The same IH applied to Q.
    let Q' : Sylow p H := Q.subtype hQ_le_H
    have hQ'_normal : (Q' : Subgroup H).Normal :=
      ih (Nat.card H) hcard_lt H h2abelian' (φ.comp H.subtype) hφ'
        h_centralizer_index' Q' rfl
    -- In `H`, both `P'` and `Q'` are normal Sylow p-subgroups, hence equal.
    have hPQ_eq : P' = Q' := by
      haveI := Sylow.unique_of_normal P' hP'_normal
      exact Subsingleton.elim P' Q'
    have hPQsubgroup_eq : (P : Subgroup G) = (Q : Subgroup G) := by
      have h := congrArg (fun R : Sylow p H => (R : Subgroup H)) hPQ_eq
      simp only [P', Q', Sylow.coe_subtype] at h
      have hPmap :
          ((P : Subgroup G).subgroupOf H).map H.subtype = (P : Subgroup G) := by
        rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, H.range_subtype]
        exact inf_eq_right.mpr hP_le_H
      have hQmap :
          ((Q : Subgroup G).subgroupOf H).map H.subtype = (Q : Subgroup G) := by
        rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, H.range_subtype]
        exact inf_eq_right.mpr hQ_le_H
      have := congrArg (fun K : Subgroup H => K.map H.subtype) h
      simpa [hPmap, hQmap] using this
    exact hQP (Sylow.ext hPQsubgroup_eq.symm)

end -- 7A

/-! ## §7B: normal-J theorem (pp. 209-214) -/

section /- 7B: normal-J theorem -/

/-! ### Thm 7.6 — normal-J theorem ⭐⭐ (conditional on 8-step argument)

**Isaacs Thm 7.6** (mmd L3832):

> (i) G p-solvable, (ii) `p ≠ 2`, (iii) Sylow-2 abelian, (iv) `O_{p'}(G) = 1`,
> (v) `P = C_G(Z(P))` ⇒ `J(P) ⊴ G`.

**= BG Theorem 6.2 の odd-order 等価版**. **FT クリティカル度 HIGHEST**: BG §6, §8,
§9, App.A で 7 ヶ所超で直接引用.

**proof 戦略** (8 Step, mmd L3832-3896): Thm 7.5 + Ch.6 **6.20** (abelian coprime
⟨C_N(a)⟩=N) + Ch.4 **4.35** (Ω₁ fixed) + Hall-Higman 3.21.

The full Goldschmidt-style 8-step proof requires Thm 7.5 (✅ landed) + Ch.6 6.20 +
Ch.4 4.35 (still pending).  Below we land the **conditional version** that takes
the minimum-counterexample contradiction as a forward-dependency hypothesis. -/

/-! ### Step 1 corollaries of Hall-Higman 3.21 (mmd L3837)

The first step of Isaacs Thm 7.6 proof observes that under hyp (iv)
`O_{p'}(G) = 1`, Hall-Higman 3.21 (with `π = {p}`) yields
`C_G(O_p(G)) ≤ O_p(G)`, and consequently `Z(P) ≤ O_p(G)` for any
Sylow `p`-subgroup `P`. -/

/-- The image of `Z(P)` in `G` centralizes `O_p(G)`.

Pure structural fact: since `O_p(G) ≤ P`, any element of `Z(P)` commutes with
every element of `O_p(G)`.  Hypothesis (iv) `O_{p'}(G) = 1` is **not** needed
here; it enters only at the next step (Hall-Higman 3.21). -/
private theorem center_sylow_le_centralizer_opCore
    {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) :
    (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
      Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) := by
  rintro _ ⟨⟨z, hzP⟩, hz_center, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh_P : h ∈ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P hh
  have hc : (⟨h, hh_P⟩ : (P : Subgroup G)) * ⟨z, hzP⟩
      = ⟨z, hzP⟩ * ⟨h, hh_P⟩ :=
    Subgroup.mem_center_iff.mp hz_center ⟨h, hh_P⟩
  exact congr_arg Subtype.val hc

/-- **Isaacs Thm 7.6 Step 1** (mmd L3837): Hall-Higman 3.21 with `π = {p}`.

If `G` is `{p}`-separable (equivalently `p`-solvable) and `O_{p'}(G) = ⊥`,
then `C_G(O_p(G)) ≤ O_p(G)`. -/
theorem centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) :
    Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) ≤
      OddOrder.Isaacs.Ch01.opCore p G := by
  have hπ' : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥ := by
    rw [show ({q | q ∉ ({p} : Set ℕ)} : Set ℕ) = {q | q ≠ p} by
      ext q; simp]
    exact hOp'
  have hHH :=
    OddOrder.Isaacs.Ch03.hall_higman_1_2_3 (G := G) ({p} : Set ℕ) hπ'
  rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p] at hHH
  exact hHH

/-- **Isaacs Thm 7.6 Step 1** (mmd L3837): `Z(P) ≤ O_p(G)` under `O_{p'}(G) = ⊥`.

Composition of `center_sylow_le_centralizer_opCore` (structural) and
`centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot` (Hall-Higman 3.21).
This is the core conclusion of Step 1 in the 8-step proof of Thm 7.6. -/
theorem center_sylow_le_opCore_of_oPiCorePrime_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G) :
    (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
      OddOrder.Isaacs.Ch01.opCore p G :=
  (center_sylow_le_centralizer_opCore P).trans
    (centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot hOp')

/-- **Isaacs Thm 7.6 Step 1(c)** (mmd L3839): in the quotient
`G̅ := G / O_p(G)`, the centralizer of `L̅ := O_{p'}(G̅)` is contained in `L̅`.

Stated with the quotient taken at `oPiCore ({p} : Set ℕ) G` (the canonical
form recognized by `oPiCore_quotient_self_eq_bot`).  Use sites that work with
`opCore p G` should transport across `oPiCore_singleton_eq_opCore` via
`QuotientGroup.quotientMulEquivOfEq` before calling. -/
theorem step1_c_centralizer_oPiPrime_quotient_le_self
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G] :
    Subgroup.centralizer
        (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
            (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :
          Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ≤
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
  -- (1) `{p}`-separability passes to the quotient (mathlib instance).
  haveI : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ)
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := inferInstance
  -- (2) Take complement: `IsPiSeparable π G → IsPiSeparable {p | p ∉ π} G`.
  haveI : OddOrder.Isaacs.Ch03.IsPiSeparable ({q | q ≠ p} : Set ℕ)
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
    have hcompl := OddOrder.Isaacs.Ch03.isPiSeparable_compl
      ({p} : Set ℕ) (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) inferInstance
    have hπeq : ({q : ℕ | q ∉ ({p} : Set ℕ)} : Set ℕ) = {q | q ≠ p} := by
      ext q; simp
    rw [hπeq] at hcompl
    exact hcompl
  -- (3) Hall-Higman complement: `O_{{p}}(G̅) = ⊥` (self-quotient kills radical).
  have hπ'bot :
      OddOrder.Isaacs.Ch03.oPiCore
          ({q : ℕ | q ∉ ({q | q ≠ p} : Set ℕ)} : Set ℕ)
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) = ⊥ := by
    have hπ'eq : ({q : ℕ | q ∉ ({q | q ≠ p} : Set ℕ)} : Set ℕ) = ({p} : Set ℕ) := by
      ext q; simp
    rw [hπ'eq]
    exact OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot ({p} : Set ℕ)
  -- (4) Apply Hall-Higman 3.21 to `G̅` with `π = {q | q ≠ p}`.
  exact OddOrder.Isaacs.Ch03.hall_higman_1_2_3 ({q | q ≠ p} : Set ℕ) hπ'bot

/-! ### §7B Step 4 setup: the subgroup `L = O_{p',p}(G)`.

Following Isaacs L3835 the book sets `L̅ = O_{p'}(G̅)` (where `G̅ = G/U`,
`U = O_p(G)`) and defines `L` to be the unique preimage of `L̅` in `G`
containing `U`.  We work with the comap-along-`mk'` form. -/

/-- `L = O_{p',p}(G)` defined as the preimage of `L̅ = O_{p'}(G̅)` along
the quotient map `G →* G/(O_p(G))`.  This is the second term of the lower
`p`-radical series of `G` (with `O_p` first, `O_{p'}` second). -/
noncomputable def opPpPrimeCore (G : Type*) [Group G] [Finite G] (p : ℕ)
    [Fact p.Prime] : Subgroup G :=
  (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)).comap
    (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))

/-- `L = O_{p',p}(G)` is `G`-normal (comap of normal subgroup is normal). -/
instance opPpPrimeCore_normal {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] : (opPpPrimeCore G p).Normal := by
  unfold opPpPrimeCore
  infer_instance

/-- `U = O_p(G) ≤ L = O_{p',p}(G)`: the kernel of the quotient map lies in the
preimage of any subgroup of the quotient. -/
theorem oPiCore_p_le_opPpPrimeCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G ≤ opPpPrimeCore G p := by
  unfold opPpPrimeCore
  intro x hx
  rw [Subgroup.mem_comap]
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
  exact (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
    (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)).one_mem

/-- `L.map (mk' U) = L̅`: the image of `L = O_{p',p}(G)` in `G̅ = G/U`
is exactly `L̅ = O_{p'}(G̅)`.  Follows from `map_comap_eq_self_of_surjective`. -/
theorem opPpPrimeCore_map_eq_LBar
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    (opPpPrimeCore G p).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) =
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
  unfold opPpPrimeCore
  exact Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective _) _

/-- **Isaacs Thm 7.6 Step 5 prep** (mmd L3873): for any `p`-subgroup `A ≤ G`,
the image `Ā = A.map (mk' U)` is disjoint from `L̅ = O_{p'}(G̅)` in `G̅ = G/U`.

`Ā` is a `p`-group (image of `p`-group `A`), and `L̅` is a `{q | q ≠ p}`-group
by `oPiCore.isPiGroup`.  Their cardinalities are coprime, hence the
intersection is trivial. -/
theorem AbarInf_LBar_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA_pg : IsPGroup p A) :
    A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ⊓
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) = ⊥ := by
  -- A̅ is a p-group, hence {p}-IsPiGroup.
  have hAbar_pg : IsPGroup p
      (A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))) :=
    hA_pg.map _
  have hAbar_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)
      (A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))) := by
    intro q hq
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hq_dvd : q ∣ Nat.card
        (A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))) :=
      Nat.dvd_of_mem_primeFactors hq
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAbar_pg
    rw [hk] at hq_dvd
    have hq_eq_p : q = p :=
      (Nat.prime_dvd_prime_iff_eq hq_prime Fact.out).mp
        (hq_prime.dvd_of_dvd_pow hq_dvd)
    simp [hq_eq_p]
  -- L̅ is a {q | q ≠ p}-group; rewrite as `{q | q ∉ {p}}` for the coprime lemma.
  have hLbar_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup
      ({q : ℕ | q ∉ ({p} : Set ℕ)} : Set ℕ)
      (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) := by
    have hLbar_pi := OddOrder.Isaacs.Ch03.oPiCore.isPiGroup
      (G := G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) ({q | q ≠ p} : Set ℕ)
    have hπeq : ({q : ℕ | q ∉ ({p} : Set ℕ)} : Set ℕ) = {q | q ≠ p} := by
      ext q; simp
    rw [hπeq]; exact hLbar_pi
  -- Apply `inf_eq_bot_of_coprime` + `coprime_of_isPiGroup_of_isPiGroup_compl`.
  apply Subgroup.inf_eq_bot_of_coprime
  exact OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    Nat.card_pos.ne' Nat.card_pos.ne' hAbar_pi hLbar_pi'

/-- **Step 5 conclusion synthesizer** (mmd L3874): a nontrivial, finite,
elementary abelian, cyclic `p`-group has order exactly `p`.  Generic. -/
theorem card_eq_prime_of_isElementaryAbelian_isCyclic_nontrivial
    {p : ℕ} [Fact p.Prime] {H : Type*} [Group H] [Finite H] [Nontrivial H]
    (hH_el : OddOrder.GroupTheory.IsElementaryAbelian p H) (hH_cyc : IsCyclic H) :
    Nat.card H = p := by
  -- Get generator; |H| = orderOf g for cyclic.
  obtain ⟨g, hg⟩ := hH_cyc.exists_generator
  have hzgen : Subgroup.zpowers g = ⊤ := by
    ext x
    exact ⟨fun _ => Subgroup.mem_top _, fun _ => hg x⟩
  have hcard : Nat.card H = orderOf g := by
    have hcard_zpow : Nat.card (Subgroup.zpowers g) = Nat.card H := by
      rw [hzgen]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [← hcard_zpow, Nat.card_zpowers]
  -- g^p = 1 ⇒ orderOf g ∣ p.
  have hpow : g ^ p = 1 := hH_el.pow_eq_one g
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hpow
  -- p prime + orderOf g ∣ p ⇒ orderOf g = 1 or p.
  rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | hp'
  · -- orderOf g = 1 ⇒ g = 1 ⇒ zpowers g = ⊥; but zpowers g = ⊤ (hzgen), contradict.
    exfalso
    have hg_eq : g = 1 := orderOf_eq_one_iff.mp h1
    have hbot : Subgroup.zpowers g = ⊥ := by
      rw [hg_eq, Subgroup.zpowers_one_eq_bot]
    have hcontra : (⊤ : Subgroup H) = ⊥ := hzgen.symm.trans hbot
    exact absurd hcontra top_ne_bot
  · rw [hcard, hp']

/-- `A ≤ P` propagates to images: `Ā ≤ P̄`.  Pure monotonicity of `Subgroup.map`. -/
theorem map_le_map_of_le
    {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    {P A : Subgroup G} (hA_le_P : A ≤ P) :
    A.map (QuotientGroup.mk' N) ≤ P.map (QuotientGroup.mk' N) :=
  Subgroup.map_mono hA_le_P

/-- **Step 2 entry / Step 7 closure**: `J(P) ≤ X` iff every elementary abelian
maximal `E ∈ E(P)` is contained in `X`.  Pure unfold of the iSup definition. -/
theorem thompsonJ_le_iff
    {G : Type*} [Group G] (P X : Subgroup G) (p : ℕ) :
    Subgroup.thompsonJ P p ≤ X ↔
      ∀ E ∈ Subgroup.maxElemAbelianIn P p, E ≤ X := by
  unfold Subgroup.thompsonJ
  exact iSup₂_le_iff

/-- Contrapositive of `thompsonJ_le_iff`: if `J(P) ⊄ X` then some maximal
elementary abelian member is not contained in `X`.  This is the Step 2
entry of the Thm 7.6 counterexample-minimum argument: assuming `G` is a
counterexample, `J(P) ⊄ U`, hence we can pick `A ∈ E(P)` with `A ⊄ U`. -/
theorem exists_maxElemAbelianIn_not_le_of_thompsonJ_not_le
    {G : Type*} [Group G] (P X : Subgroup G) (p : ℕ)
    (h : ¬ Subgroup.thompsonJ P p ≤ X) :
    ∃ E ∈ Subgroup.maxElemAbelianIn P p, ¬ E ≤ X := by
  by_contra h_all
  push_neg at h_all
  exact h ((thompsonJ_le_iff P X p).mpr h_all)

/-- The image of an elementary abelian subgroup under a group hom is
elementary abelian.  Generic for `Subgroup.IsElementaryAbelian`. -/
theorem isElementaryAbelian_map_of_isElementaryAbelian
    {G H : Type*} [Group G] [Group H] {p : ℕ} (f : G →* H)
    {A : Subgroup G} (hA : A.IsElementaryAbelian p) :
    (A.map f).IsElementaryAbelian p := by
  refine ⟨?_, ?_⟩
  · rintro ⟨_, a₁, ha₁, rfl⟩ ⟨_, a₂, ha₂, rfl⟩
    apply Subtype.ext
    show f a₁ * f a₂ = f a₂ * f a₁
    rw [← f.map_mul, ← f.map_mul]
    have hcomm : (⟨a₁, ha₁⟩ : A) * ⟨a₂, ha₂⟩ = ⟨a₂, ha₂⟩ * ⟨a₁, ha₁⟩ :=
      hA.1 ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩
    exact congr_arg f (congr_arg Subtype.val hcomm)
  · rintro ⟨_, a, ha, rfl⟩
    apply Subtype.ext
    show (f a) ^ p = 1
    rw [← f.map_pow, ← f.map_one]
    have hpow : (⟨a, ha⟩ : A) ^ p = 1 := hA.2 ⟨a, ha⟩
    exact congr_arg f (congr_arg Subtype.val hpow)

/-- **Isaacs Thm 7.6 Step 5 nontriviality** (mmd L3874): if `A ⊄ U`
(= `oPiCore {p} G`), then the image `Ā = A.map (mk' U)` is nontrivial.

Contrapositive: `Ā = ⊥ ⇒ A ≤ ker mk' = U`. -/
theorem Abar_ne_bot_of_not_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G}
    (hA_not_le : ¬ A ≤ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :
    A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ≠ ⊥ := by
  intro h_eq
  apply hA_not_le
  intro x hx
  have hmem :
      (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) x ∈
        A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) :=
    ⟨x, hx, rfl⟩
  rw [h_eq, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff x).mp hmem

/-- **Isaacs Thm 7.6 Step 5 faithfulness** (mmd L3874): for any `p`-subgroup
`A ≤ G`, the image `Ā = A.map (mk' U)` acts faithfully on `L̅ = O_{p'}(G̅)`,
i.e., `Ā ⊓ C_{G̅}(L̅) = ⊥`.

Combines Step 1(c) (`C_{G̅}(L̅) ⊆ L̅`) with `Ā ⊓ L̅ = ⊥`. -/
theorem AbarInf_centralizer_LBar_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    {A : Subgroup G} (hA_pg : IsPGroup p A) :
    A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ⊓
      Subgroup.centralizer
        (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
            (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :
          Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
  rw [eq_bot_iff]
  calc
    A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ⊓
        Subgroup.centralizer
          (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
              (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :
            Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))
        ≤ A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ⊓
            OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
              (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :=
      inf_le_inf_left _ step1_c_centralizer_oPiPrime_quotient_le_self
    _ = ⊥ := AbarInf_LBar_eq_bot hA_pg

/-! ### Step 2-3: structural bridges for `A ∈ E(P)`, `A ⊄ L` (mmd L3845-3858)

We pick `A ∈ maxElemAbelianIn P p` with `A ⊄ L = O_p(G)`.  These bridges express
the basic structural relations between `A`, `D := A ⊓ L`, and the global subgroups
of `G` needed in subsequent steps.

The book takes `A ∈ E(P)` failing to lie in `L` for the contradiction in Step 7.
We package the elementary observations: `A` is an elementary abelian `p`-subgroup
of `P`, hence contained in `P`; and `D = A ⊓ L` is a proper subgroup of `A` (with
nontrivial quotient `A/D`). -/

/-- **Isaacs Thm 7.6 Step 2** preparation (mmd L3845-3846):
`A ∈ maxElemAbelianIn P p` is an elementary abelian `p`-subgroup of `P`.

Pure unpacking of the `maxElemAbelianIn` definition (see
`OddOrder.GroupTheory.ThompsonSubgroup.maxElemAbelianIn`).  Placed here as a
shorthand for §7B Steps 3-7 which reuse the elementary-abelian / `≤ P` facts. -/
private theorem maxElemAbelianIn_isElementaryAbelian {G : Type*} [Group G]
    {P A : Subgroup G} {p : ℕ}
    (hA : A ∈ Subgroup.maxElemAbelianIn P p) :
    A.IsElementaryAbelian p :=
  hA.2.1

private theorem maxElemAbelianIn_le_parent {G : Type*} [Group G]
    {P A : Subgroup G} {p : ℕ}
    (hA : A ∈ Subgroup.maxElemAbelianIn P p) :
    A ≤ P :=
  hA.1

/-- **Isaacs Thm 7.6 Step 3** (mmd L3850-3856): the quotient `A / (A ⊓ L)` has order `p`.

Book argument: `A` is elementary abelian (`x^p = 1` for all `x ∈ A`), so `A/D`
embeds into `G/L`.  Under hypothesis (iv) `O_{p'}(G) = 1` we have `L = O_p(G)`,
hence `G/L` has trivial `p`-Sylow (Hall-Higman 3.21 / Isaacs Cor 3.21).

For the bridge layer we record the **abstract version**: if `D ≤ A`, `D ≠ A`, and
`A.IsElementaryAbelian p`, then `D` has index dividing `p` in `A`.  In an
elementary abelian `p`-group every proper subgroup has prime power index.  The
stronger conclusion "index exactly `p`" needs the **maximality of `A`** —
otherwise we could enlarge `D` to a strict sub of `A` of index `p`, contradicting
that `A ∈ E(P)`.

We package the elementary-abelian quotient observation: in `A/D` the exponent
divides `p` so `|A/D|` is a power of `p`. -/
private theorem relIndex_isPGroup_of_isElementaryAbelian
    {G : Type*} [Group G] {A D : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hA_el : A.IsElementaryAbelian p) :
    IsPGroup p (D.subgroupOf A) := by
  -- A is elementary abelian ⇒ A is a p-group ⇒ subgroup of A is a p-group.
  have hA_pG : IsPGroup p A := hA_el.isPGroup
  exact hA_pG.to_subgroup _

/-- **Isaacs Thm 7.6 Step 3** companion: the order of `A` is a power of `p`.

Since `A.IsElementaryAbelian p`, `A` is itself a `p`-group, so `Nat.card A = p^k`
for some `k`. -/
private theorem isPGroup_of_isElementaryAbelian
    {G : Type*} [Group G] {A : Subgroup G} {p : ℕ}
    (hA_el : A.IsElementaryAbelian p) :
    IsPGroup p A :=
  hA_el.isPGroup

/-! ### Step 4: action of `A` on `V := Z(L) = Z(O_p(G))` (mmd L3858-3864)

Set `V := Z(L)`.  Since `L = O_p(G)` is `G`-normal, the conjugation action of `G`
on `L` restricts to an action on `Z(L)`, and in particular `A ≤ P ≤ G` acts on `V`.
Furthermore `D = A ⊓ L ≤ L` commutes with all of `V = Z(L)` by definition of
center, so `D` is contained in the kernel of the action of `A` on `V`. -/

/-- **Isaacs Thm 7.6 Step 4** (mmd L3858): `Z(O_p(G))` is `G`-normal (and `G`-characteristic).

The `Subgroup.center` of a characteristic subgroup is itself characteristic in the
ambient group.  In particular `Subgroup.center` of `O_p(G)`, viewed as the image
of `Subgroup.center (opCore p G)` in `G`, is `G`-normal. -/
private theorem center_opCore_map_normal {G : Type*} [Group G] {p : ℕ} :
    ((Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G)).map
      (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G).subtype).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨⟨z, hz_L⟩, hz_center, rfl⟩ g
  -- g * z * g⁻¹ ∈ opCore p G  (since opCore is normal)
  have hLnorm : (OddOrder.Isaacs.Ch01.opCore p G).Normal := inferInstance
  have hgz : g * z * g⁻¹ ∈ OddOrder.Isaacs.Ch01.opCore p G :=
    hLnorm.conj_mem z hz_L g
  refine ⟨⟨g * z * g⁻¹, hgz⟩, ?_, rfl⟩
  -- Show ⟨g*z*g⁻¹, _⟩ ∈ Subgroup.center (opCore p G).
  change (⟨g * z * g⁻¹, hgz⟩ : OddOrder.Isaacs.Ch01.opCore p G) ∈
    Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G)
  rw [Subgroup.mem_center_iff]
  rintro ⟨h, hh_L⟩
  -- ⟨h, hh_L⟩ * ⟨g*z*g⁻¹, hgz⟩ = ⟨g*z*g⁻¹, hgz⟩ * ⟨h, hh_L⟩,
  -- i.e., h * (g*z*g⁻¹) = (g*z*g⁻¹) * h.
  have hgh : g⁻¹ * h * g ∈ OddOrder.Isaacs.Ch01.opCore p G := by
    have := hLnorm.conj_mem h hh_L g⁻¹
    simpa [mul_assoc] using this
  have hcomm : (⟨g⁻¹ * h * g, hgh⟩ : OddOrder.Isaacs.Ch01.opCore p G) * ⟨z, hz_L⟩
      = ⟨z, hz_L⟩ * ⟨g⁻¹ * h * g, hgh⟩ :=
    Subgroup.mem_center_iff.mp hz_center _
  have hcomm_G : (g⁻¹ * h * g) * z = z * (g⁻¹ * h * g) := congr_arg Subtype.val hcomm
  apply Subtype.ext
  calc h * (g * z * g⁻¹)
      = g * ((g⁻¹ * h * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * h * g)) * g⁻¹ := by rw [hcomm_G]
    _ = (g * z * g⁻¹) * h := by group

/-- **Isaacs Thm 7.6 Step 4** (mmd L3859-3860):
`D := A ⊓ L` centralizes `V := Z(L)`.

For any `d ∈ D`, `d ∈ L`.  For any `v` representing an element of `Z(L) ↪ G`,
the conjugation `d * v * d⁻¹` equals `v` because `v ∈ Z(L)`.  This packages the
"the `A`-action restricted to `D` is trivial" observation: `D ≤ centralizer V`. -/
private theorem A_inter_opCore_le_centralizer_center_opCore
    {G : Type*} [Group G] {p : ℕ} {A : Subgroup G} :
    A ⊓ OddOrder.Isaacs.Ch01.opCore p G ≤
      Subgroup.centralizer
        (((Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G)).map
          (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G).subtype) : Set G) := by
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨⟨v, hv_L⟩, hv_center, rfl⟩
  -- d ∈ L, ⟨v, _⟩ ∈ Z(L) ⇒ they commute in L ⇒ commute in G.
  have hd_L : d ∈ OddOrder.Isaacs.Ch01.opCore p G := hd.2
  -- mem_centralizer_iff: ∀ h ∈ s, h * g = g * h, so v * d = d * v.
  -- mem_center_iff gives ∀ g, g * z = z * g, so ⟨d, _⟩ * ⟨v, _⟩ = ⟨v, _⟩ * ⟨d, _⟩.
  have hcomm : (⟨d, hd_L⟩ : OddOrder.Isaacs.Ch01.opCore p G) * ⟨v, hv_L⟩
      = ⟨v, hv_L⟩ * ⟨d, hd_L⟩ :=
    Subgroup.mem_center_iff.mp hv_center _
  exact (congr_arg Subtype.val hcomm).symm

/-! ### Step 5-6: action triviality on `V := Z(O_p(G))` (mmd L3864-3884)

The book applies Ch.6 Thm 6.20 + Ch.4 Cor 4.35 to deduce that the action of
`A/D ≅ ℤ/p` on `V = Z(L)` is trivial.  At the bridge layer we record:

* `V` is a finite abelian `p`-group (Ch.4 Cor 4.35 hypothesis).
* `Z(L)` is the centralizer of `L` inside `L`, which contains the image of
  `Z(P)` (by Step 1's `center_sylow_le_opCore_of_oPiCorePrime_eq_bot` and the
  fact that `Z(P)` ≤ centralizer (Z(P)) ≤ centralizer L ⊓ L = Z(L)`...).

The combined deduction "A trivial on `Ω₁ Z(L)` ⇒ A trivial on `Z(L)`" requires
both Thm 6.20 (factoring through cyclic quotients) and Cor 4.35 (Ω₁ argument).
We supply pieces; the full Step 5-6 deduction is deferred to a later session. -/

/-- **Isaacs Thm 7.6 Step 5** (mmd L3864): `Z(O_p(G))` is a `p`-group.

Direct: `O_p(G)` is itself a `p`-group (`opCore_isPGroup`), and the center of a
`p`-group is a `p`-group (`IsPGroup.to_subgroup`). -/
private theorem center_opCore_isPGroup {G : Type*} [Group G] (p : ℕ) [Fact p.Prime] :
    IsPGroup p (Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G)) :=
  (OddOrder.Isaacs.Ch01.opCore_isPGroup p G).to_subgroup _

/-- **Isaacs Thm 7.6 Step 5** (mmd L3864): the image of `Z(O_p(G))` in `G` is also a
`p`-group.

Push-forward of `center_opCore_isPGroup` under the inclusion `opCore p G ↪ G`. -/
private theorem center_opCore_map_isPGroup
    {G : Type*} [Group G] (p : ℕ) [Fact p.Prime] :
    IsPGroup p
      ((Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G)).map
        (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G).subtype) :=
  (center_opCore_isPGroup p).map _

/-- **Isaacs Thm 7.6 Step 5** (mmd L3864): `Z(O_p(G))` is commutative as a group.

Since `Z(O_p(G)) ≤ Z(O_p(G))` (tautologically) and the center is commutative,
`Z(O_p(G))` carries a `CommGroup` structure.  We expose only the underlying
`∀ x y, x * y = y * x` (lemma form), which avoids declaring a `CommGroup`
instance that could collide. -/
private theorem center_opCore_comm
    {G : Type*} [Group G] (p : ℕ) :
    ∀ x y : Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G),
      x * y = y * x := by
  intro x y
  -- Both x, y belong to Subgroup.center; use mem_center_iff to commute.
  have hx : (x : OddOrder.Isaacs.Ch01.opCore p G) ∈
      Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) := x.2
  have hcomm := Subgroup.mem_center_iff.mp hx (y : OddOrder.Isaacs.Ch01.opCore p G)
  -- hcomm : (y : _) * (x : _) = (x : _) * (y : _).  Want x * y = y * x in Z(L).
  apply Subtype.ext
  exact hcomm.symm

/-! ### Step 7 preparation: `V := Ω₁(Z(O_p(G)))` as a subgroup of `G` (sub-session A)

For the Step 5-6 application of Cor 4.35 we need
`V := Ω₁(Z(O_p(G)))`, i.e., `{z ∈ Z(O_p(G)) | z^p = 1}`.  Since `Z(O_p(G))`
is abelian (it is a center), this set forms a subgroup of `G` directly,
without taking a closure.  We package it as `omega1ZCenterOpCore` together
with its key properties: normal in `G`, contained in `O_p(G)`, abelian as
a group, and a `p`-group.

These are the structural ingredients for **Isaacs Thm 7.6 Step 7 sub-session
(A)**.  The downstream application combines `V` with Cor 4.35
(`actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`) to derive
`[A, V] = ⊥` from the fixed-point hypothesis. -/

/-- Local notation shorthand inside §7B: the underlying subgroup of `Z(O_p(G))`
viewed inside `G` (i.e., the image of `Subgroup.center (opCore p G)` under
the inclusion `opCore p G ↪ G`). -/
private def zCenterOpCoreSubgroup (G : Type*) [Group G] (p : ℕ) : Subgroup G :=
  (Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G)).map
    (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G).subtype

private theorem zCenterOpCoreSubgroup_le_opCore
    {G : Type*} [Group G] {p : ℕ} :
    zCenterOpCoreSubgroup G p ≤ OddOrder.Isaacs.Ch01.opCore p G := by
  rintro _ ⟨⟨z, hz_L⟩, _, rfl⟩
  exact hz_L

private theorem zCenterOpCoreSubgroup_comm
    {G : Type*} [Group G] {p : ℕ} :
    ∀ x ∈ zCenterOpCoreSubgroup G p,
      ∀ y ∈ zCenterOpCoreSubgroup G p, x * y = y * x := by
  rintro _ ⟨⟨x, hx_L⟩, hx_center, rfl⟩ _ ⟨⟨y, hy_L⟩, hy_center, rfl⟩
  -- ⟨x, _⟩ ∈ Z(L) so commutes with ⟨y, _⟩ in L; project to G.
  -- mem_center_iff: x ∈ center ↔ ∀ g, g * x = x * g.
  have hcomm :
      (⟨y, hy_L⟩ : OddOrder.Isaacs.Ch01.opCore p G) * ⟨x, hx_L⟩ =
        ⟨x, hx_L⟩ * ⟨y, hy_L⟩ :=
    Subgroup.mem_center_iff.mp hx_center _
  exact (congr_arg Subtype.val hcomm).symm

/-- **V := Ω₁(Z(O_p(G)))** as a subgroup of `G`.

The set `{g ∈ Z(O_p(G)) | g^p = 1}`, viewed inside `G`.  Since `Z(O_p(G))`
is abelian, this is a subgroup of `G` directly (no closure required).

This is the `V` of **Isaacs Thm 7.6 Step 7 sub-session (A)**: the bottom
layer `Ω₁` of the center of the `p`-core, on which the action of
`A ∈ E(P)` will be analyzed via Cor 4.35. -/
def omega1ZCenterOpCore (G : Type*) [Group G] (p : ℕ) : Subgroup G :=
  OddOrder.GroupTheory.omega1OfAbelian G (zCenterOpCoreSubgroup G p) p
    zCenterOpCoreSubgroup_comm

/-- Membership characterization for `V := Ω₁(Z(O_p(G)))`. -/
theorem mem_omega1ZCenterOpCore {G : Type*} [Group G] {p : ℕ} {g : G} :
    g ∈ omega1ZCenterOpCore G p ↔
      g ∈ zCenterOpCoreSubgroup G p ∧ g ^ p = 1 := by
  unfold omega1ZCenterOpCore
  exact OddOrder.GroupTheory.mem_omega1OfAbelian

/-- `V ≤ Z(O_p(G))` (the bottom layer is contained in the center it sits in). -/
theorem omega1ZCenterOpCore_le_zCenterOpCore
    {G : Type*} [Group G] {p : ℕ} :
    omega1ZCenterOpCore G p ≤ zCenterOpCoreSubgroup G p :=
  OddOrder.GroupTheory.omega1OfAbelian_le

/-- `V ≤ O_p(G)`: immediate via the chain `V ≤ Z(O_p(G)) ≤ O_p(G)`. -/
theorem omega1ZCenterOpCore_le_opCore
    {G : Type*} [Group G] {p : ℕ} :
    omega1ZCenterOpCore G p ≤ OddOrder.Isaacs.Ch01.opCore p G :=
  omega1ZCenterOpCore_le_zCenterOpCore.trans zCenterOpCoreSubgroup_le_opCore

/-- **Isaacs Thm 7.6 Step 7 sub-session (A)**: `V := Ω₁(Z(O_p(G)))` is normal in `G`.

Proof: `Z(O_p(G))` (as `zCenterOpCoreSubgroup`) is normal in `G` (already in
`center_opCore_map_normal`).  Conjugation by `g ∈ G` preserves the power map
`x ↦ x^p`, so it sends `{z ∈ Z(O_p(G)) | z^p = 1}` to itself. -/
instance omega1ZCenterOpCore_normal {G : Type*} [Group G] {p : ℕ} :
    (omega1ZCenterOpCore G p).Normal := by
  refine ⟨?_⟩
  intro n hn g
  rw [mem_omega1ZCenterOpCore] at hn ⊢
  refine ⟨?_, ?_⟩
  · -- Z(O_p(G)) is normal (center_opCore_map_normal).
    have h_norm : (zCenterOpCoreSubgroup G p).Normal := center_opCore_map_normal
    exact h_norm.conj_mem _ hn.1 g
  · -- (g * n * g⁻¹) ^ p = g * n^p * g⁻¹ = g * 1 * g⁻¹ = 1.
    calc (g * n * g⁻¹) ^ p
        = g * n ^ p * g⁻¹ := by rw [conj_pow]
      _ = g * 1 * g⁻¹ := by rw [hn.2]
      _ = 1 := by group

/-- `V := Ω₁(Z(O_p(G)))` is a `p`-group.

Direct consequence of `V ≤ O_p(G)` and `O_p(G)` being a `p`-group. -/
theorem omega1ZCenterOpCore_isPGroup
    {G : Type*} [Group G] (p : ℕ) [Fact p.Prime] :
    IsPGroup p (omega1ZCenterOpCore G p) :=
  (OddOrder.Isaacs.Ch01.opCore_isPGroup p G).of_injective
    (Subgroup.inclusion omega1ZCenterOpCore_le_opCore)
    (Subgroup.inclusion_injective _)

/-- The elements of `V := Ω₁(Z(O_p(G)))` commute pairwise (V is abelian).

Inherited from the fact that they sit in `Z(O_p(G))`. -/
theorem omega1ZCenterOpCore_comm {G : Type*} [Group G] {p : ℕ} :
    ∀ x y : ↥(omega1ZCenterOpCore G p), x * y = y * x := by
  intro x y
  apply Subtype.ext
  have hx : (x : G) ∈ zCenterOpCoreSubgroup G p :=
    omega1ZCenterOpCore_le_zCenterOpCore x.2
  have hy : (y : G) ∈ zCenterOpCoreSubgroup G p :=
    omega1ZCenterOpCore_le_zCenterOpCore y.2
  exact zCenterOpCoreSubgroup_comm _ hx _ hy

/-- `V := Ω₁(Z(O_p(G)))` as a `CommGroup`.

The pairwise-commutativity from `omega1ZCenterOpCore_comm` upgrades the
ambient `Group ↥V` structure to `CommGroup`. -/
@[reducible] def omega1ZCenterOpCore_commGroup (G : Type*) [Group G] (p : ℕ) :
    CommGroup ↥(omega1ZCenterOpCore G p) :=
  { (inferInstance : Group ↥(omega1ZCenterOpCore G p)) with
    mul_comm := omega1ZCenterOpCore_comm }

/-- Every element of `V := Ω₁(Z(O_p(G)))` has order dividing `p`.

Pure unpacking of `mem_omega1ZCenterOpCore.2`. -/
theorem pow_p_eq_one_of_mem_omega1ZCenterOpCore
    {G : Type*} [Group G] {p : ℕ} {g : G}
    (hg : g ∈ omega1ZCenterOpCore G p) : g ^ p = 1 :=
  ((mem_omega1ZCenterOpCore).mp hg).2

/-! ### Step 7 sub-session (A): Cor 4.35 wrapper for `V := Ω₁(Z(O_p(G)))`

We specialize **Isaacs Cor 4.35**
(`OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`)
to `V := Ω₁(Z(O_p(G)))`: any `p'`-group `A` acting on `V` that fixes every
element of order `p` (= every element of `V`!) has `actionCommutator φ = ⊥`.

The wrapper packages the `CommGroup`, `IsPGroup p`, `Finite` instances on `V`
so callers only need to supply the action `φ : A →* MulAut ↥V` and the
hypotheses `¬ p ∣ |A|` and the fixed-point property. -/

/-- **Isaacs Thm 7.6 Step 7 sub-session (A)**: Cor 4.35 specialized to
`V := Ω₁(Z(O_p(G)))`.

Given a finite group `A` with `p ∤ |A|` acting on `V` via `φ : A →* MulAut ↥V`,
if every element of order `p` (equivalently every element of `V`, since
`V = Ω₁(...)`) is fixed by every `a ∈ A`, then `actionCommutator φ = ⊥`.

Reduces to Cor 4.35
(`OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`)
once the abelian + `p`-group instances on `V` are produced. -/
theorem cor_4_35_for_omega1ZCenterOpCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Type*} [Group A] [Finite A]
    (φ : A →* MulAut ↥(omega1ZCenterOpCore G p))
    (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ v : ↥(omega1ZCenterOpCore G p), v ^ p = 1 →
      ∀ a : A, (φ a) v = v) :
    OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
  let _ : CommGroup ↥(omega1ZCenterOpCore G p) :=
    omega1ZCenterOpCore_commGroup G p
  OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p
    (p := p) φ (omega1ZCenterOpCore_isPGroup p) hA_p' h_fix

/-- `Z(U) = Z(O_p(G))` is `G`-normal: it is the image of the center
of the (`G`-normal) `O_p(G)`, transported up via `center_opCore_map_normal`. -/
instance zCenterOpCoreSubgroup_normal
    {G : Type*} [Group G] {p : ℕ} :
    (zCenterOpCoreSubgroup G p).Normal := center_opCore_map_normal

/-- The conjugation action of an arbitrary subgroup `Q ≤ G` on `Z(U) = Z(O_p(G))`:
`Q →* MulAut Z(U)` via `MulAut.conjNormal ∘ Q.subtype`.

Used in Step 6: `Q` (a Sylow `q`-subgroup of `K = C_G(V)`, `q ≠ p`) acts on
`Z(U)` by conjugation; combined with `Q` fixing `V = Ω₁ Z(U)` (from `Q ⊆ K`),
Cor 4.35 yields `Q` acts trivially on `Z(U)`. -/
noncomputable def conjActionOnZCenterOpCoreSubgroup
    {G : Type*} [Group G] {p : ℕ} (Q : Subgroup G) :
    Q →* MulAut ↥(zCenterOpCoreSubgroup G p) :=
  MulAut.conjNormal.comp Q.subtype


/-- `Z(U) = Z(O_p(G))` is a `p`-group: it is a subgroup of `U = O_p(G)`,
which is a `p`-group. -/
theorem zCenterOpCoreSubgroup_isPGroup
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    IsPGroup p (zCenterOpCoreSubgroup G p) :=
  (OddOrder.Isaacs.Ch01.opCore_isPGroup p G).to_le zCenterOpCoreSubgroup_le_opCore

/-- Pairwise commutativity on the subtype ↥(Z(U)). -/
theorem zCenterOpCoreSubgroup_comm_subtype
    {G : Type*} [Group G] {p : ℕ} :
    ∀ x y : ↥(zCenterOpCoreSubgroup G p), x * y = y * x := by
  intro x y
  apply Subtype.ext
  exact zCenterOpCoreSubgroup_comm _ x.2 _ y.2

/-- `Z(U)` as a `CommGroup`. -/
@[reducible] def zCenterOpCoreSubgroup_commGroup
    (G : Type*) [Group G] (p : ℕ) :
    CommGroup ↥(zCenterOpCoreSubgroup G p) :=
  { (inferInstance : Group ↥(zCenterOpCoreSubgroup G p)) with
    mul_comm := zCenterOpCoreSubgroup_comm_subtype }

/-- Centralizer-conjugation lemma: `q ∈ centralizer s` ⇒ `q * z * q⁻¹ = z`
for every `z ∈ s`.  Generic. -/
theorem conj_eq_self_of_mem_centralizer
    {G : Type*} [Group G] {s : Set G}
    {q : G} (hq : q ∈ Subgroup.centralizer s) {z : G} (hz : z ∈ s) :
    q * z * q⁻¹ = z := by
  have hcomm : z * q = q * z := Subgroup.mem_centralizer_iff.mp hq z hz
  calc q * z * q⁻¹ = z * q * q⁻¹ := by rw [hcomm]
    _ = z := by group

/-- **Isaacs Cor 4.35 specialized for Z(U) = Z(O_p(G))**.

Given a `p'`-group `A` acting on `Z(U)` and fixing every element of order
`p` (= elements of `V = Ω₁ Z(U)`), `actionCommutator φ = ⊥`. -/
theorem cor_4_35_for_zCenterOpCoreSubgroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Type*} [Group A] [Finite A]
    (φ : A →* MulAut ↥(zCenterOpCoreSubgroup G p))
    (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ v : ↥(zCenterOpCoreSubgroup G p), v ^ p = 1 →
      ∀ a : A, (φ a) v = v) :
    OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
  let _ : CommGroup ↥(zCenterOpCoreSubgroup G p) :=
    zCenterOpCoreSubgroup_commGroup G p
  OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p
    (p := p) φ (zCenterOpCoreSubgroup_isPGroup p) hA_p' h_fix

/-- Generic: a subgroup-level `IsElementaryAbelian p H` upgrades the ambient
`Group ↥H` to a `CommGroup ↥H` using the commutativity component.  Local
construction used when applying CommGroup-requiring lemmas (e.g., index
calculations) on elementary abelian subgroups. -/
@[reducible] def isElementaryAbelian_commGroup
    {G : Type*} [Group G] {p : ℕ} {H : Subgroup G} (hH : H.IsElementaryAbelian p) :
    CommGroup ↥H :=
  { (inferInstance : Group ↥H) with mul_comm := hH.1 }

/-- `O_p(G) ⊓ O_{p'}(G) = ⊥`: the `p`-core and the `p'`-core of `G` are
disjoint, by coprime cardinalities.  Specialization of `oPiCore.coprime_inf`. -/
theorem opCore_inf_oPiCorePrime_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    OddOrder.Isaacs.Ch01.opCore p G ⊓
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥ := by
  have h1 : OddOrder.Isaacs.Ch01.opCore p G =
      OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  have hπeq : ({q : ℕ | q ∉ ({p} : Set ℕ)} : Set ℕ) = {q | q ≠ p} := by
    ext q; simp
  rw [h1, ← hπeq]
  exact OddOrder.Isaacs.Ch03.oPiCore.coprime_inf ({p} : Set ℕ)

/-- If `Q ⊆ K = C_G(V)`, conjugation by elements of `Q` fixes every element
of `V = Ω₁ Z(U)` pointwise in `G`. -/
theorem conj_fixes_omega1ZCenterOpCore_of_le_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup G}
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G))
    (q : ↥Q) {v : G} (hv : v ∈ omega1ZCenterOpCore G p) :
    (q : G) * v * (q : G)⁻¹ = v :=
  conj_eq_self_of_mem_centralizer (hQ_le_K q.2) hv

/-- `V ⊆ centralizer U` in `G`: since `V ⊆ Z(U)`, every element of `V`
commutes with every element of `U`.  Used in Step 7 to argue `V * D`
is abelian (`V ⊆ centralizer U ⊇ D`). -/
theorem omega1ZCenterOpCore_centralizes_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    omega1ZCenterOpCore G p ≤
      Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) := by
  intro x hx
  have hx_ZU : x ∈ zCenterOpCoreSubgroup G p :=
    omega1ZCenterOpCore_le_zCenterOpCore hx
  rcases hx_ZU with ⟨⟨z, hz_U⟩, hz_center, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hcomm : (⟨u, hu⟩ : ↥(OddOrder.Isaacs.Ch01.opCore p G)) * ⟨z, hz_U⟩ =
      ⟨z, hz_U⟩ * ⟨u, hu⟩ :=
    Subgroup.mem_center_iff.mp hz_center _
  exact congr_arg Subtype.val hcomm

/-- `U.map (mk' U) = ⊥`: the image of `U = O_p(G)` in `G̅ = G/U` is trivial. -/
theorem opCore_map_mk_oPiCore_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    (OddOrder.Isaacs.Ch01.opCore p G).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [show OddOrder.Isaacs.Ch01.opCore p G =
        OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G from
      (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm]

/-- Intersection with any subgroup preserves `IsElementaryAbelian`: if `A` is
elementary abelian then `A ⊓ B` is elementary abelian.  Used in Step 7 to
get `D = A ⊓ U`, `E = A ⊓ V` elementary abelian. -/
theorem inf_isElementaryAbelian_of_isElementaryAbelian
    {G : Type*} [Group G] {p : ℕ} {A : Subgroup G} (hA : A.IsElementaryAbelian p)
    (B : Subgroup G) :
    (A ⊓ B).IsElementaryAbelian p := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hxA, _hxB⟩ ⟨y, hyA, _hyB⟩
    apply Subtype.ext
    -- Goal in G: x * y = y * x
    have hcomm_A : (⟨x, hxA⟩ : ↥A) * ⟨y, hyA⟩ = ⟨y, hyA⟩ * ⟨x, hxA⟩ := hA.1 _ _
    exact (congr_arg (Subtype.val (p := fun x => x ∈ A)) hcomm_A : (x * y : G) = y * x)
  · rintro ⟨x, hxA, _hxB⟩
    apply Subtype.ext
    -- Goal in G: x^p = 1
    have hpow_A : (⟨x, hxA⟩ : ↥A) ^ p = 1 := hA.2 _
    exact (congr_arg (Subtype.val (p := fun x => x ∈ A)) hpow_A : (x ^ p : G) = 1)

/-- **V is elementary abelian**: every element has order dividing `p`,
and the group is commutative (it lies inside the center `Z(O_p(G))`).
Used in Step 7 (`VD` elementary abelian counting argument). -/
theorem omega1ZCenterOpCore_isElementaryAbelian
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    (omega1ZCenterOpCore G p).IsElementaryAbelian p := by
  refine ⟨omega1ZCenterOpCore_comm, ?_⟩
  intro x
  apply Subtype.ext
  show ((x : G) ^ p) = 1
  exact pow_p_eq_one_of_mem_omega1ZCenterOpCore x.2

/-- **Isaacs Thm 7.6 Step 6 prep** (mmd L3881): `Z(P) ⊆ Z(U)` (in the image
form): under hypothesis (iv), `Z(P)` lies inside `Z(O_p(G)) = Z(U)`.

`Z(P) ⊆ U` by Step 1(a) (`center_sylow_le_opCore_of_oPiCorePrime_eq_bot`),
and any `z ∈ Z(P)` commutes with every `u ∈ U ⊆ P`. -/
theorem center_sylow_le_zCenterOpCoreSubgroup_of_oPiCorePrime_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G) :
    (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
      zCenterOpCoreSubgroup G p := by
  rintro _ ⟨⟨z', hz'_P⟩, hz'_center, rfl⟩
  -- z' ∈ U by Step 1(a).
  have hz_in_U : (z' : G) ∈ OddOrder.Isaacs.Ch01.opCore p G :=
    center_sylow_le_opCore_of_oPiCorePrime_eq_bot hOp' P
      ⟨⟨z', hz'_P⟩, hz'_center, rfl⟩
  -- ⟨z', hz_in_U⟩ ∈ Z(U) because z' commutes with each u ∈ U ⊆ P.
  refine ⟨⟨(z' : G), hz_in_U⟩, ?_, rfl⟩
  show (⟨(z' : G), hz_in_U⟩ : ↥(OddOrder.Isaacs.Ch01.opCore p G)) ∈
      Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G)
  rw [Subgroup.mem_center_iff]
  intro u
  apply Subtype.ext
  show ((u : G) * (z' : G)) = ((z' : G) * (u : G))
  have hu_P : (u : G) ∈ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P u.2
  have hcomm : (⟨(u : G), hu_P⟩ : (P : Subgroup G)) * ⟨z', hz'_P⟩
      = ⟨z', hz'_P⟩ * ⟨(u : G), hu_P⟩ :=
    Subgroup.mem_center_iff.mp hz'_center _
  exact congr_arg Subtype.val hcomm

/-- `V ⊆ K = C_G(V)`: abelian subgroup is contained in its own centralizer. -/
theorem omega1ZCenterOpCore_le_centralizer_self
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    omega1ZCenterOpCore G p ≤
      Subgroup.centralizer (omega1ZCenterOpCore G p : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hcomm : (⟨y, hy⟩ : ↥(omega1ZCenterOpCore G p)) * ⟨x, hx⟩ =
      ⟨x, hx⟩ * ⟨y, hy⟩ := omega1ZCenterOpCore_comm _ _
  exact congr_arg Subtype.val hcomm

/-- **Isaacs Thm 7.6 Step 6 setup** (mmd L3879): `K := C_G(V)` (where
`V = Ω₁(Z(O_p(G)))`) is `G`-normal.  Trivial: centralizers of normal subgroups
are normal. -/
instance centralizer_omega1ZCenterOpCore_normal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)).Normal :=
  Subgroup.normal_centralizer

/-- **Isaacs Thm 7.6 Step 6 conclusion** (mmd L3882): if `K = C_G(V)` is a
`p`-group, then `K ≤ O_p(G)` via `normal_pgroup_le_opCore`. -/
theorem centralizer_omega1ZCenterOpCore_le_opCore_of_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hK_pg : IsPGroup p (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G))) :
    Subgroup.centralizer (omega1ZCenterOpCore G p : Set G) ≤
      OddOrder.Isaacs.Ch01.opCore p G :=
  OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hK_pg

/-! ### Step 6 main: `K := C_G(V)` is a `p`-group (mmd L3879-3884)

This is the heart of Step 6: for every prime `q ≠ p`, the action of any
Sylow `q`-subgroup `Q` of `K` on `Z(U) = Z(O_p(G))` (by conjugation) is
forced to be trivial via Cor 4.35 (`Q` fixes every element of order `p`
in `Z(U)`, namely all of `V`), so `Q ⊆ C_G(Z(U)) ⊆ C_G(Z(P)) = P`.  Then
`Q ⊆ P ∩ K`, but `Q` is a `q`-group and `P` is a `p`-group with `q ≠ p`,
forcing `Q = ⊥`.  Since all primes `q ≠ p` give trivial Sylow `q`-subgroups
of `K`, `K` is a `p`-group. -/

/-- The conjugation action of `Q ≤ K = C_G(V)` on `V = Ω₁ Z(U)` is trivial:
every element of `V` is fixed by every element of `Q`.  Pure unpacking of
`conj_fixes_omega1ZCenterOpCore_of_le_centralizer` into the action form needed
to apply Cor 4.35. -/
private theorem conj_fixes_zCenterOpCoreSubgroup_v_of_le_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup G}
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G))
    (z : ↥(zCenterOpCoreSubgroup G p)) (hz_p : z ^ p = 1) (q : ↥Q) :
    (conjActionOnZCenterOpCoreSubgroup Q q) z = z := by
  -- (z : G) ∈ V := Ω₁ Z(U) since z ∈ Z(U) and z^p = 1.
  have hz_V : (z : G) ∈ omega1ZCenterOpCore G p := by
    rw [mem_omega1ZCenterOpCore]
    refine ⟨z.2, ?_⟩
    -- z^p = 1 in subtype ↥(Z(U)) ⇒ (z : G)^p = 1.
    have hzp_coe := congr_arg (fun x : ↥(zCenterOpCoreSubgroup G p) => (x : G)) hz_p
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hzp_coe
    exact hzp_coe
  -- Q ⊆ C_G(V), so (q : G) * (z : G) * (q : G)⁻¹ = (z : G).
  have hconj : (q : G) * (z : G) * (q : G)⁻¹ = (z : G) :=
    conj_fixes_omega1ZCenterOpCore_of_le_centralizer hQ_le_K q hz_V
  apply Subtype.ext
  -- (conjActionOnZCenterOpCoreSubgroup Q q) z = MulAut.conjNormal (q : G) z
  unfold conjActionOnZCenterOpCoreSubgroup
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
  exact hconj

/-- A `q`-subgroup `Q` of `K = C_G(V)` (`q ≠ p` prime) is contained in
the centralizer of `Z(U)` in `G`.

Apply Cor 4.35 (`cor_4_35_for_zCenterOpCoreSubgroup`) with the conjugation action
of `Q` on `Z(U)`: `Q` is a `p'`-group, and `Q` fixes every order-`p` element of
`Z(U)` (these are the elements of `V = Ω₁ Z(U)`, and `Q ⊆ K = C_G(V)`).  This
yields `actionCommutator = ⊥`, i.e., `Q` acts trivially on `Z(U)`. -/
private theorem q_subgroup_in_K_le_centralizer_zCenter
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {q : ℕ} (hq_prime : q.Prime) (hqp : q ≠ p)
    {Q : Subgroup G} (hQ_q : IsPGroup q Q)
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) :
    Q ≤ Subgroup.centralizer (zCenterOpCoreSubgroup G p : Set G) := by
  haveI : Fact q.Prime := ⟨hq_prime⟩
  -- (1) Q is a p'-group: q ≠ p prime + |Q| = q^k ⇒ p ∤ |Q|.
  have hQp' : ¬ p ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ_q
    rw [hk]
    intro hpdvd
    have hp_prime : p.Prime := Fact.out
    have hq_dvd_p : p ∣ q := hp_prime.dvd_of_dvd_pow hpdvd
    -- p ∣ q with p, q prime ⇒ p = q
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp hq_dvd_p
    exact hqp this.symm
  -- (2) Apply Cor 4.35: the conjugation action of Q on Z(U) has actionCommutator = ⊥.
  have h_ac_bot :
      OddOrder.Isaacs.Ch04.actionCommutator (conjActionOnZCenterOpCoreSubgroup Q)
        = ⊥ :=
    cor_4_35_for_zCenterOpCoreSubgroup (conjActionOnZCenterOpCoreSubgroup Q) hQp'
      (fun z hz_p s => conj_fixes_zCenterOpCoreSubgroup_v_of_le_centralizer hQ_le_K z hz_p s)
  -- (3) Translate "actionCommutator = ⊥" into "Q acts trivially":
  --     for all (qq : Q), (z : Z(U)), MulAut.conjNormal qq z = z.
  have h_trivial :
      ∀ qq : Q, ∀ z : ↥(zCenterOpCoreSubgroup G p),
        (conjActionOnZCenterOpCoreSubgroup Q qq) z = z :=
    (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially _).mp h_ac_bot
  -- (4) Convert to: Q ⊆ C_G(Z(U)) inside G.
  intro qq hqq_Q
  rw [Subgroup.mem_centralizer_iff]
  rintro z hz
  -- z ∈ Z(U) as Subgroup G ⇒ z is in zCenterOpCoreSubgroup, lifted from a z' in subtype.
  -- Apply h_trivial at (⟨qq, hqq_Q⟩ : ↥Q) and (⟨z, hz⟩ : ↥(Z(U))).
  have hcommute := h_trivial ⟨qq, hqq_Q⟩ ⟨z, hz⟩
  -- hcommute: (conjActionOnZCenterOpCoreSubgroup Q ⟨qq, hqq_Q⟩) ⟨z, hz⟩ = ⟨z, hz⟩
  -- Unfold: MulAut.conjNormal (qq) ⟨z, hz⟩ = ⟨z, hz⟩, i.e., qq * z * qq⁻¹ = z.
  have hcommute_coe : ((conjActionOnZCenterOpCoreSubgroup Q ⟨qq, hqq_Q⟩) ⟨z, hz⟩ : G)
      = (⟨z, hz⟩ : ↥(zCenterOpCoreSubgroup G p)) := by
    rw [hcommute]
  unfold conjActionOnZCenterOpCoreSubgroup at hcommute_coe
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply] at hcommute_coe
  -- hcommute_coe : qq * z * qq⁻¹ = z. Rearrange to z * qq = qq * z.
  calc z * qq = (qq * z * qq⁻¹) * qq := by rw [hcommute_coe]
    _ = qq * z := by group

/-- A `q`-subgroup `Q` of `K = C_G(V)` (`q ≠ p` prime) is contained in
`P`, under hypothesis (v) `P = C_G(Z(P))` and `O_{p'}(G) = ⊥`.

Combines `q_subgroup_in_K_le_centralizer_zCenter` (yielding `Q ⊆ C_G(Z(U))`) with
the chain `Z(P) ⊆ Z(U)` (`center_sylow_le_zCenterOpCoreSubgroup_of_oPiCorePrime_eq_bot`)
+ contravariant `centralizer_le` + hypothesis (v) `C_G(Z(P)) = P`. -/
private theorem q_subgroup_in_K_le_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {q : ℕ} (hq_prime : q.Prime) (hqp : q ≠ p)
    {Q : Subgroup G} (hQ_q : IsPGroup q Q)
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) :
    Q ≤ (P : Subgroup G) := by
  -- Q ⊆ C_G(Z(U)).
  have hQ_cZU : Q ≤ Subgroup.centralizer (zCenterOpCoreSubgroup G p : Set G) :=
    q_subgroup_in_K_le_centralizer_zCenter hq_prime hqp hQ_q hQ_le_K
  -- Z(P) ⊆ Z(U), so C_G(Z(U)) ⊆ C_G(Z(P)) = P.
  have hZP_le_ZU :
      ((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype : Subgroup G) ≤
        zCenterOpCoreSubgroup G p :=
    center_sylow_le_zCenterOpCoreSubgroup_of_oPiCorePrime_eq_bot hOp' P
  have hC_ZU_le_C_ZP :
      Subgroup.centralizer (zCenterOpCoreSubgroup G p : Set G) ≤
        Subgroup.centralizer
          (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G) :=
    Subgroup.centralizer_le hZP_le_ZU
  rw [h_centralizer_center] at hC_ZU_le_C_ZP
  exact hQ_cZU.trans hC_ZU_le_C_ZP

/-- A `q`-subgroup `Q` of `K = C_G(V)` (`q ≠ p` prime) is trivial,
under the Thm 7.6 hypotheses (iv) `O_{p'}(G) = ⊥` and (v) `P = C_G(Z(P))`.

From `q_subgroup_in_K_le_sylow` we get `Q ⊆ P`.  Then `Q` is a `q`-group inside a
`p`-group `P` with `q ≠ p`, forcing `Q = ⊥` by coprimality of cardinalities. -/
private theorem q_subgroup_in_K_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {q : ℕ} (hq_prime : q.Prime) (hqp : q ≠ p)
    {Q : Subgroup G} (hQ_q : IsPGroup q Q)
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) :
    Q = ⊥ := by
  haveI : Fact q.Prime := ⟨hq_prime⟩
  have hQ_le_P : Q ≤ (P : Subgroup G) :=
    q_subgroup_in_K_le_sylow hOp' P h_centralizer_center hq_prime hqp hQ_q hQ_le_K
  -- Q is a q-group and Q ≤ P which is a p-group; coprime ⇒ |Q| = 1.
  have hP_p : IsPGroup p (P : Subgroup G) := P.isPGroup'
  have hQ_p : IsPGroup p Q := hP_p.to_le hQ_le_P
  obtain ⟨a, hQa⟩ := IsPGroup.iff_card.mp hQ_q
  obtain ⟨b, hQb⟩ := IsPGroup.iff_card.mp hQ_p
  have hp_prime : p.Prime := Fact.out
  have hQ_card : Nat.card Q = 1 := by
    have h_eq : q ^ a = p ^ b := hQa.symm.trans hQb
    by_contra h_ne
    have ha_pos : 1 ≤ a := by
      rcases a with _ | a'
      · -- a = 0 ⇒ |Q| = q^0 = 1, contradicting h_ne.
        exfalso
        apply h_ne
        rw [hQa, pow_zero]
      · exact Nat.le_add_left 1 a'
    have hq_dvd_qa : q ∣ q ^ a := dvd_pow_self q (Nat.one_le_iff_ne_zero.mp ha_pos)
    rw [h_eq] at hq_dvd_qa
    have hq_dvd_p : q ∣ p := hq_prime.dvd_of_dvd_pow hq_dvd_qa
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp hq_dvd_p
    exact hqp this
  exact Subgroup.eq_bot_of_card_eq Q hQ_card

/-- **Isaacs Thm 7.6 Step 6 main** (mmd L3879-3884): under hypotheses
(iv) `O_{p'}(G) = ⊥` and (v) `P = C_G(Z(P))`, `K := C_G(V)` is a `p`-group.

Proof: for every `g ∈ K`, the order `orderOf g` has only `p` as a prime divisor.
Indeed, if some prime `q ≠ p` divided `orderOf g = n`, then `g^(n/q) ∈ K` would
generate a `q`-subgroup of order `q`, which is forced to be trivial by
`q_subgroup_in_K_eq_bot`, contradicting `orderOf (g^(n/q)) = q > 1`.

Hence `orderOf g` is a power of `p` for every `g ∈ K`, so `K` is a `p`-group. -/
theorem centralizer_omega1ZCenterOpCore_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G)) :
    IsPGroup p (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) := by
  -- Use IsPGroup.iff_orderOf: K is a p-group iff every g ∈ K has order a power of p.
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg_K⟩
  set K : Subgroup G := Subgroup.centralizer (omega1ZCenterOpCore G p : Set G) with hK_def
  -- Step (1): orderOf ⟨g, hg_K⟩ in K = orderOf g in G.
  set n : ℕ := orderOf g with hn_def
  have h_ord_eq : orderOf (⟨g, hg_K⟩ : ↥K) = n := Subgroup.orderOf_mk g hg_K
  rw [h_ord_eq]
  -- Reduce to: n is a power of p. Argue by contradiction.
  by_contra hno_pk
  push Not at hno_pk
  have hn_pos : 0 < n := orderOf_pos g
  have hp_prime : p.Prime := Fact.out
  -- ∃ q prime, q ≠ p, q ∣ n.
  have h_exists_q : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ n := by
    by_contra h_all
    push Not at h_all
    suffices ∀ q ∈ n.primeFactorsList, q = p by
      have : ∃ k, n = p ^ k := by
        refine ⟨n.primeFactorsList.length, ?_⟩
        rw [← List.prod_replicate, ← List.eq_replicate_of_mem this,
          Nat.prod_primeFactorsList hn_pos.ne']
      obtain ⟨k, hk⟩ := this
      exact hno_pk _ hk
    intro q hq
    obtain ⟨hq_prime, hq_dvd⟩ := (Nat.mem_primeFactorsList hn_pos.ne').mp hq
    by_contra hqp
    exact h_all q hq_prime hqp hq_dvd
  obtain ⟨q, hq_prime, hqp, hq_dvd_n⟩ := h_exists_q
  -- Set h := g^(n/q). It has order q.
  set h_elem : G := g ^ (n / q) with h_elem_def
  have hh_K : h_elem ∈ K := K.pow_mem hg_K _
  have hgq_pow_q : h_elem ^ q = 1 := by
    rw [h_elem_def, ← pow_mul, Nat.div_mul_cancel hq_dvd_n, pow_orderOf_eq_one]
  -- h ≠ 1 because n/q < n and orderOf g = n.
  have hh_ne_one : h_elem ≠ 1 := by
    intro h_eq
    have h_div : n ∣ (n / q) := by
      rw [hn_def]; exact orderOf_dvd_of_pow_eq_one h_eq
    have hq_two : 2 ≤ q := hq_prime.two_le
    have hnq_lt : n / q < n := Nat.div_lt_self hn_pos hq_two
    have hnq_pos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn_pos hq_dvd_n) hq_prime.pos
    have : n ≤ n / q := Nat.le_of_dvd hnq_pos h_div
    omega
  -- orderOf h = q.
  have hh_ord : orderOf h_elem = q := by
    have h_ord_dvd : orderOf h_elem ∣ q := orderOf_dvd_of_pow_eq_one hgq_pow_q
    rcases (Nat.dvd_prime hq_prime).mp h_ord_dvd with h1 | hqeq
    · exact absurd (orderOf_eq_one_iff.mp h1) hh_ne_one
    · exact hqeq
  -- Q := Subgroup.zpowers h is a q-group of K.
  have hQ_q : IsPGroup q (Subgroup.zpowers h_elem) := by
    haveI : Fact q.Prime := ⟨hq_prime⟩
    rw [IsPGroup.iff_card]
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers, hh_ord, pow_one]
  have hQ_le_K : (Subgroup.zpowers h_elem) ≤ K := by
    rw [Subgroup.zpowers_le]; exact hh_K
  -- Apply q_subgroup_in_K_eq_bot: ⟨h⟩ = ⊥.
  have hQ_bot : Subgroup.zpowers h_elem = ⊥ :=
    q_subgroup_in_K_eq_bot hOp' P h_centralizer_center hq_prime hqp hQ_q hQ_le_K
  -- But h ∈ ⟨h⟩ = ⊥ ⇒ h = 1, contradicting hh_ne_one.
  have : h_elem ∈ Subgroup.zpowers h_elem := Subgroup.mem_zpowers _
  rw [hQ_bot, Subgroup.mem_bot] at this
  exact hh_ne_one this

/-- **Isaacs Thm 7.6 Step 6 faithfulness** (mmd L3884): `K̄ = ⊥` in `Ḡ` given
`K ≤ U`.  This is the final Step 6 conclusion: the Ḡ-action on V is faithful
because its kernel `K̄ = (K.map mk')` is trivial. -/
theorem centralizer_omega1ZCenterOpCore_map_eq_bot_of_le_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hK_le_U : Subgroup.centralizer (omega1ZCenterOpCore G p : Set G) ≤
        OddOrder.Isaacs.Ch01.opCore p G) :
    (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  -- Goal: K ≤ oPiCore {p} G
  intro x hx
  have hx_U : x ∈ OddOrder.Isaacs.Ch01.opCore p G := hK_le_U hx
  rwa [show OddOrder.Isaacs.Ch01.opCore p G =
        OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G from
      (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm] at hx_U

/-! ### Step 7 counting argument: `|V : V ∩ A| ≤ p` (mmd L3886-3892)

The book's Step 7 derives a counting bound on `V := Ω₁ Z(O_p(G))`:

> Write `D = U ∩ A` and `E = V ∩ A`.  Then `|V:E| = |V:V∩D| = |VD:D|`.  Now
> `D` is elementary abelian in `U`, and `V` is a central elementary abelian
> subgroup of `U`, so `VD` is elementary abelian.  By `A ∈ E(P)`, `|VD| ≤ |A|`,
> hence `|VD:D| ≤ |A:D| = |Ā| = p`.

We package this combinatorial step as `omega1ZCenterOpCore_relIndex_inter_A_le`,
isolating from the broader Goldschmidt argument the part that only needs
elementary-abelian structure, `V ≤ centralizer U`, and the maximality of
`A ∈ maxElemAbelianIn P p`.

The hypothesis `|A : A ⊓ U| ≤ p` is supplied externally (it is the Step 5
conclusion `|Ā| = p`). -/

/-- **Subgroup `V ⊔ D` is contained in its own centralizer** when `V`
centralizes `D`, `V` is commutative, and `D` is commutative.

This packages `V ⊔ D ≤ centralizer (V ⊔ D)`, i.e., `V ⊔ D` is abelian. -/
private theorem sup_le_centralizer_self_of_centralizing
    {G : Type*} [Group G] {V D : Subgroup G}
    (hV_comm : ∀ x y : ↥V, x * y = y * x)
    (hD_comm : ∀ x y : ↥D, x * y = y * x)
    (hVD : V ≤ Subgroup.centralizer (D : Set G)) :
    (V ⊔ D : Subgroup G) ≤ Subgroup.centralizer ((V ⊔ D : Subgroup G) : Set G) := by
  -- Strategy: show V ∪ D ⊆ centralizer (V ⊔ D), then by closure of centralizer.
  -- centralizer is a subgroup, so closure (V ∪ D) ⊆ centralizer (V ⊔ D).
  -- V ⊔ D = closure (V ∪ D), giving the conclusion.
  have h_VuD_in_cent : (V : Set G) ∪ (D : Set G) ⊆
      Subgroup.centralizer ((V ⊔ D : Subgroup G) : Set G) := by
    -- Show each element of V ∪ D commutes with every element of V ⊔ D.
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    -- x ∈ V ⊔ D ⟺ x ∈ closure (V ∪ D). Use closure_induction.
    have hx_clos : x ∈ Subgroup.closure ((V : Set G) ∪ (D : Set G)) := by
      rwa [← Subgroup.sup_eq_closure]
    clear hx
    -- w ∈ V ∪ D, x ∈ closure (V ∪ D). Goal: x * w = w * x.
    induction hx_clos using Subgroup.closure_induction with
    | mem y hy =>
      -- Both w and y are in V ∪ D, show they commute.
      rcases hw with hw_V | hw_D
      · rcases hy with hy_V | hy_D
        · have := hV_comm ⟨y, hy_V⟩ ⟨w, hw_V⟩
          exact congr_arg Subtype.val this
        · -- w ∈ V, y ∈ D: hVD says V centralizes D.
          have h_w_cent := hVD hw_V
          rw [Subgroup.mem_centralizer_iff] at h_w_cent
          exact h_w_cent y hy_D
      · rcases hy with hy_V | hy_D
        · -- w ∈ D, y ∈ V: hVD says V centralizes D.
          have h_y_cent := hVD hy_V
          rw [Subgroup.mem_centralizer_iff] at h_y_cent
          exact (h_y_cent w hw_D).symm
        · have := hD_comm ⟨y, hy_D⟩ ⟨w, hw_D⟩
          exact congr_arg Subtype.val this
    | one => rw [one_mul, mul_one]
    | mul a b _ _ ha hb =>
      calc (a * b) * w = a * (b * w) := by group
        _ = a * (w * b) := by rw [hb]
        _ = (a * w) * b := by group
        _ = (w * a) * b := by rw [ha]
        _ = w * (a * b) := by group
    | inv a _ ha =>
      have hcomm : a * w = w * a := ha
      calc a⁻¹ * w = a⁻¹ * (w * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * w) * a⁻¹ := by rw [hcomm]
        _ = w * a⁻¹ := by group
  -- Now centralizer is a subgroup, so closure (V ∪ D) ⊆ centralizer (V ⊔ D).
  -- The result follows because V ⊔ D = closure (V ∪ D).
  intro x hx
  -- Convert hx to closure form, apply h_VuD_in_cent + closure_le.
  have hx_clos : x ∈ Subgroup.closure ((V : Set G) ∪ (D : Set G)) := by
    rwa [← Subgroup.sup_eq_closure]
  exact (Subgroup.closure_le _).mpr h_VuD_in_cent hx_clos

/-- **VD is elementary abelian**: if `V` centralizes `D`, both `V` and `D` are
elementary abelian `p`-groups, and `V` is normal in `G`, then `V ⊔ D` is also
elementary abelian.

Proof: by `mul_normal`, every element of `V ⊔ D` is `v * d` for some `v ∈ V`,
`d ∈ D`.  Commutativity in `V ⊔ D` and exponent `p` both follow from `V` and
`D` commuting pointwise. -/
private theorem sup_isElementaryAbelian_of_centralizing
    {G : Type*} [Group G] {p : ℕ} {V D : Subgroup G} [V.Normal]
    (hV : V.IsElementaryAbelian p) (hD : D.IsElementaryAbelian p)
    (hVD : V ≤ Subgroup.centralizer (D : Set G)) :
    (V ⊔ D : Subgroup G).IsElementaryAbelian p := by
  have h_VD_comm : (V ⊔ D : Subgroup G) ≤
      Subgroup.centralizer ((V ⊔ D : Subgroup G) : Set G) :=
    sup_le_centralizer_self_of_centralizing hV.1 hD.1 hVD
  -- Element decomposition: every element of V ⊔ D is v*d for v ∈ V, d ∈ D.
  have h_decomp : ∀ x ∈ (V ⊔ D : Subgroup G), ∃ v ∈ V, ∃ d ∈ D, (v * d : G) = x := by
    intro x hx
    have h_mul : (↑(V ⊔ D) : Set G) = V * D := Subgroup.normal_mul V D
    have hx_set : x ∈ (↑(V ⊔ D) : Set G) := hx
    rw [h_mul] at hx_set
    obtain ⟨v, hv, d, hd, hvd⟩ := hx_set
    exact ⟨v, hv, d, hd, hvd⟩
  refine ⟨?_, ?_⟩
  · -- Commutativity in V ⊔ D.
    intro x y
    apply Subtype.ext
    have hxy_cent := h_VD_comm x.2
    rw [Subgroup.mem_centralizer_iff] at hxy_cent
    have : (y : G) * x = x * y := hxy_cent y y.2
    exact this.symm
  · -- Exponent p.  In V ⊔ D, every element w has w^p = 1.
    intro w
    apply Subtype.ext
    change (w.val : G) ^ p = 1
    -- w = v * d for some v ∈ V, d ∈ D.
    obtain ⟨v, hv_V, d, hd_D, hvd_eq⟩ := h_decomp w.val w.2
    rw [← hvd_eq]
    -- (v * d)^p = v^p * d^p (since v and d commute), and v^p = 1, d^p = 1.
    have hv_d_comm : v * d = d * v := by
      have hv_cent := hVD hv_V
      rw [Subgroup.mem_centralizer_iff] at hv_cent
      exact (hv_cent d hd_D).symm
    have hCom : Commute v d := hv_d_comm
    have : (v * d) ^ p = v ^ p * d ^ p := Commute.mul_pow hCom p
    rw [this]
    have hv_p : v ^ p = 1 := by
      have := hV.2 ⟨v, hv_V⟩
      exact congr_arg Subtype.val this
    have hd_p : d ^ p = 1 := by
      have := hD.2 ⟨d, hd_D⟩
      exact congr_arg Subtype.val this
    rw [hv_p, hd_p, mul_one]

/-- **Isaacs Thm 7.6 Step 7** (mmd L3886-3892): `|V : V ∩ A| ≤ p` for any
`A ∈ maxElemAbelianIn P p`, assuming `|A : A ∩ U| ≤ p` (Step 5).

`A.relIndex V` is `|V : V ⊓ A|` in book notation
(`(A.subgroupOf V).index = |V/(A ⊓ V)|`).  Similarly,
`(A ⊓ U).relIndex A = |A : A ⊓ U|` is the Step-5 bound.

The book's argument:
1. Set `D = U ∩ A` and `E = V ∩ A`.  Observe `V ⊆ U` (so `V ∩ A = V ∩ D`).
2. `D` is elementary abelian (sub of `A`).
3. `V` is elementary abelian and central in `U`, so `V ⊆ centralizer D`.
4. `VD := V ⊔ D` is elementary abelian (`sup_isElementaryAbelian_of_centralizing`).
5. `VD ≤ P` (since `V ≤ U ≤ P` and `D ≤ A ≤ P`).
6. By maximality `A ∈ E(P)`, `|VD| ≤ |A|`, so `|VD : D| ≤ |A : D|`.
7. By second isomorphism (V normal, V centralizes D), `|V : V ∩ D| = |VD : D|`.
8. Combine: `|V : V ∩ A| = |V : V ∩ D| = |VD : D| ≤ |A : D| ≤ p`. -/
theorem omega1ZCenterOpCore_relIndex_inter_A_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {A : Subgroup G}
    (hA : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (hA_D_relIndex : (OddOrder.Isaacs.Ch01.opCore p G).relIndex A ≤ p) :
    A.relIndex (omega1ZCenterOpCore G p) ≤ p := by
  classical
  set V : Subgroup G := omega1ZCenterOpCore G p with hV_def
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set D : Subgroup G := A ⊓ U with hD_def
  -- Basic facts.
  have hV_le_U : V ≤ U := omega1ZCenterOpCore_le_opCore
  have hA_P : A ≤ (P : Subgroup G) := hA.1
  have hU_P : U ≤ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P
  have hA_el : A.IsElementaryAbelian p := hA.2.1
  have hD_el : D.IsElementaryAbelian p :=
    inf_isElementaryAbelian_of_isElementaryAbelian hA_el U
  have hV_el : V.IsElementaryAbelian p := omega1ZCenterOpCore_isElementaryAbelian
  have hV_cent_U : V ≤ Subgroup.centralizer (U : Set G) :=
    omega1ZCenterOpCore_centralizes_opCore
  have hD_le_U : D ≤ U := inf_le_right
  have hD_le_A : D ≤ A := inf_le_left
  have hV_cent_D : V ≤ Subgroup.centralizer (D : Set G) :=
    hV_cent_U.trans (Subgroup.centralizer_le hD_le_U)
  -- V ⊔ D is elementary abelian.
  haveI : V.Normal := omega1ZCenterOpCore_normal
  have hVD_el : (V ⊔ D : Subgroup G).IsElementaryAbelian p :=
    sup_isElementaryAbelian_of_centralizing hV_el hD_el hV_cent_D
  -- V ⊔ D ≤ P.
  have hVD_le_P : (V ⊔ D : Subgroup G) ≤ (P : Subgroup G) := by
    rw [sup_le_iff]
    exact ⟨hV_le_U.trans hU_P, hD_le_A.trans hA_P⟩
  -- Maximality of A: |V ⊔ D| ≤ |A|.
  have hVD_card_le_A : Nat.card (V ⊔ D : Subgroup G) ≤ Nat.card A :=
    hA.2.2 (V ⊔ D) hVD_le_P hVD_el
  -- A.relIndex V = |V : V ∩ A| (book notation).  Rewrite via V ⊓ A = V ⊓ D.
  -- V ⊓ A = V ⊓ U ⊓ A = V ⊓ (U ⊓ A) = V ⊓ (A ⊓ U) = V ⊓ D since V ≤ U.
  have hVA_eq_VD : V ⊓ A = V ⊓ D := by
    have h_VU : V ⊓ U = V := inf_eq_left.mpr hV_le_U
    rw [hD_def, inf_comm A U, ← inf_assoc, h_VU]
  have hAV_eq : A.relIndex V = D.relIndex V := by
    -- A.relIndex V = (A ⊓ V).relIndex V via inf_relIndex_right.
    -- Same for D. Use V ⊓ A = V ⊓ D, i.e., A ⊓ V = D ⊓ V (by inf_comm).
    have h1 : A.relIndex V = (A ⊓ V).relIndex V := (Subgroup.inf_relIndex_right A V).symm
    have h2 : D.relIndex V = (D ⊓ V).relIndex V := (Subgroup.inf_relIndex_right D V).symm
    have h_inf_comm : A ⊓ V = D ⊓ V := by
      rw [inf_comm A V, inf_comm D V]; exact hVA_eq_VD
    rw [h1, h2, h_inf_comm]
  rw [hAV_eq]
  -- Second isomorphism: V / (D ⊓ V) ≅ (V ⊔ D) / D, requiring V ≤ normalizer D.
  -- V centralizes D, so V ≤ centralizer D ≤ normalizer D.
  have hV_norm_D : V ≤ Subgroup.normalizer D := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hv_cent : v ∈ Subgroup.centralizer (D : Set G) := hV_cent_D hv
    have hv_inv_cent : v⁻¹ ∈ Subgroup.centralizer (D : Set G) := Subgroup.inv_mem _ hv_cent
    constructor
    · intro hy
      have hyv : y * v = v * y := Subgroup.mem_centralizer_iff.mp hv_cent y hy
      have heq : v * y * v⁻¹ = y := by
        calc v * y * v⁻¹ = (y * v) * v⁻¹ := by rw [hyv]
          _ = y := by group
      rw [heq]
      exact hy
    · intro hyc
      have hcomm := Subgroup.mem_centralizer_iff.mp hv_inv_cent (v * y * v⁻¹) hyc
      have heq : y = v⁻¹ * (v * y * v⁻¹) * v := by group
      have hpush : v⁻¹ * (v * y * v⁻¹) * v = v * y * v⁻¹ := by
        calc v⁻¹ * (v * y * v⁻¹) * v
            = (v * y * v⁻¹) * v⁻¹ * v := by rw [← hcomm]
          _ = v * y * v⁻¹ := by group
      rw [heq, hpush]
      exact hyc
  set VD : Subgroup G := V ⊔ D with hVD_def
  have hD_le_VD : D ≤ VD := hVD_def ▸ le_sup_right
  -- Apply second iso: |V/(D ⊓ V).subgroupOf V| = |VD/D.subgroupOf VD|.
  letI hD_normal_in_V : (D.subgroupOf V).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hV_norm_D
  letI hD_normal_in_VD : (D.subgroupOf VD).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hV_norm_D
  have h_card_quot_V : Nat.card (V ⧸ D.subgroupOf V) =
      Nat.card (VD ⧸ D.subgroupOf VD) :=
    Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient V D hV_norm_D).toEquiv
  have h_card_eq : D.relIndex V = D.relIndex VD := by
    unfold Subgroup.relIndex Subgroup.index
    exact h_card_quot_V
  rw [h_card_eq]
  -- Lagrange: |VD| = D.relIndex VD * |D|, |A| = U.relIndex A * |D|.
  have hD_card_pos : 0 < Nat.card D := Nat.card_pos
  have h_lag_VD : Nat.card VD = D.relIndex VD * Nat.card D := by
    have h_index_mul_card : (D.subgroupOf VD).index *
        Nat.card (D.subgroupOf VD) = Nat.card VD :=
      Subgroup.index_mul_card _
    have hD_card_eq : Nat.card (D.subgroupOf VD) = Nat.card D := by
      have h_map_eq : ((D.subgroupOf VD : Subgroup VD).map VD.subtype : Subgroup G) = D :=
        Subgroup.map_subgroupOf_eq_of_le hD_le_VD
      have h_card : Nat.card (D.subgroupOf VD) =
          Nat.card ((D.subgroupOf VD : Subgroup VD).map VD.subtype) :=
        (Subgroup.card_map_of_injective VD.subtype_injective).symm
      rw [h_card, h_map_eq]
    rw [show D.relIndex VD = (D.subgroupOf VD).index from rfl,
        ← h_index_mul_card, hD_card_eq]
  have h_lag_A : Nat.card A = U.relIndex A * Nat.card D := by
    have h_index_mul_card : (U.subgroupOf A).index *
        Nat.card (U.subgroupOf A) = Nat.card A :=
      Subgroup.index_mul_card _
    have hU_subgrpOf_card : Nat.card (U.subgroupOf A) = Nat.card D := by
      -- (U.subgroupOf A).map A.subtype = U ⊓ A = A ⊓ U = D.
      have h_map_eq : ((U.subgroupOf A : Subgroup A).map A.subtype : Subgroup G) = U ⊓ A :=
        Subgroup.subgroupOf_map_subtype U A
      have h_card : Nat.card (U.subgroupOf A) =
          Nat.card ((U.subgroupOf A : Subgroup A).map A.subtype) :=
        (Subgroup.card_map_of_injective A.subtype_injective).symm
      rw [h_card, h_map_eq, inf_comm, ← hD_def]
    rw [show U.relIndex A = (U.subgroupOf A).index from rfl,
        ← h_index_mul_card, hU_subgrpOf_card]
  -- D.relIndex VD * |D| = |VD| ≤ |A| = U.relIndex A * |D|.
  have hVD_card_le_A' : Nat.card VD ≤ Nat.card A := hVD_card_le_A
  have hmul_le : D.relIndex VD * Nat.card D ≤ U.relIndex A * Nat.card D := by
    rw [← h_lag_VD, ← h_lag_A]
    exact hVD_card_le_A'
  exact (Nat.le_of_mul_le_mul_right hmul_le hD_card_pos).trans hA_D_relIndex

/-! ### Step 7-8: closing reductions (mmd L3884-3896)

Once Step 5-6 produce the triviality of the `A`-action on `V = Z(L)`, the book:

* (Step 7) Combines `[A, V] = 1` with hypothesis (v) `P = C_G(Z(P))` and the
  maximality of `A ∈ E(P)` to force `A ⊆ L`, contradicting `A ⊄ L`.
* (Step 8) From Step 2's conclusion `J(P) ≤ L`, applies Thm 7.2
  (`thompsonJ_eq_of_le_of_le`) to get `J(L) = J(P)`, then uses that `J(L)` is
  characteristic in `L` and `L` is characteristic in `G` to conclude
  `J(P) ⊴ G`.

The Step 7 contradiction itself is a delicate counting argument over `E(P)`
combined with the action analysis; we defer it.  Step 8 only needs the Thm 7.2
bridge, which we record here. -/

/-- **Isaacs Thm 7.6 Step 8** (mmd L3893): if `J(P) ≤ L` and `L ≤ P` then
`J(L) = J(P)`, the consequence of Thm 7.2 needed in the closing step. -/
private theorem thompsonJ_opCore_eq_thompsonJ_sylow_of_thompsonJ_le_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} (P : Sylow p G)
    (h_le : Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G) :
    Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p =
      Subgroup.thompsonJ (P : Subgroup G) p :=
  Subgroup.thompsonJ_eq_of_le_of_le h_le (OddOrder.Isaacs.Ch01.opCore_le P)

/-- **Conjugating `maxElemAbelianIn L p` by `g ∈ G`** when `L` is `G`-normal.

If `L ⊴ G` and `E ∈ maxElemAbelianIn L p`, then for any `g : G`, the conjugate
`g E g⁻¹` is again in `maxElemAbelianIn L p`.  Pure normality + the fact that
conjugation is an isomorphism (preserves cardinality and elementary-abelian
property). -/
private theorem maxElemAbelianIn_conj_mem
    {G : Type*} [Group G] {L E : Subgroup G} [hL : L.Normal] {p : ℕ}
    (hE : E ∈ Subgroup.maxElemAbelianIn L p) (g : G) :
    E.map (MulAut.conj g).toMonoidHom ∈ Subgroup.maxElemAbelianIn L p := by
  refine ⟨?_, ?_, ?_⟩
  · -- E.map (conj g) ≤ L
    rintro _ ⟨e, he_E, rfl⟩
    have he_L : e ∈ L := hE.1 he_E
    change g * e * g⁻¹ ∈ L
    exact hL.conj_mem _ he_L g
  · -- E.map (conj g) is elementary abelian
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨a, ha_E, rfl⟩⟩ ⟨_, ⟨b, hb_E, rfl⟩⟩
      apply Subtype.ext
      change (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹)
      have habcomm : a * b = b * a := by
        have h := hE.2.1.comm ⟨a, ha_E⟩ ⟨b, hb_E⟩
        exact congr_arg Subtype.val h
      calc (g * a * g⁻¹) * (g * b * g⁻¹)
          = g * (a * b) * g⁻¹ := by group
        _ = g * (b * a) * g⁻¹ := by rw [habcomm]
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := by group
    · rintro ⟨_, ⟨a, ha_E, rfl⟩⟩
      apply Subtype.ext
      change (g * a * g⁻¹) ^ p = 1
      have ha_p : a ^ p = 1 := by
        have h := hE.2.1.pow_eq_one ⟨a, ha_E⟩
        exact congr_arg Subtype.val h
      calc (g * a * g⁻¹) ^ p
          = g * a ^ p * g⁻¹ := by
            rw [conj_pow]
        _ = g * 1 * g⁻¹ := by rw [ha_p]
        _ = 1 := by group
  · -- E.map (conj g) is of maximum cardinality
    intro F hF_L hF_el
    have hF_conj_card : Nat.card (F.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) =
        Nat.card F :=
      Subgroup.card_map_of_injective (MulEquiv.injective _)
    have hE_conj_card : Nat.card (E.map (MulAut.conj g).toMonoidHom : Subgroup G) =
        Nat.card E :=
      Subgroup.card_map_of_injective (MulEquiv.injective _)
    rw [hE_conj_card]
    have hF_inv : F.map (MulAut.conj g⁻¹).toMonoidHom ≤ L := by
      rintro _ ⟨e, he_F, rfl⟩
      have he_L : e ∈ L := hF_L he_F
      change g⁻¹ * e * g⁻¹⁻¹ ∈ L
      exact hL.conj_mem _ he_L g⁻¹
    have hF_inv_el : (F.map (MulAut.conj g⁻¹).toMonoidHom).IsElementaryAbelian p := by
      refine ⟨?_, ?_⟩
      · rintro ⟨_, ⟨a, ha_F, rfl⟩⟩ ⟨_, ⟨b, hb_F, rfl⟩⟩
        apply Subtype.ext
        change (g⁻¹ * a * g⁻¹⁻¹) * (g⁻¹ * b * g⁻¹⁻¹) =
          (g⁻¹ * b * g⁻¹⁻¹) * (g⁻¹ * a * g⁻¹⁻¹)
        have habcomm : a * b = b * a := by
          have h := hF_el.comm ⟨a, ha_F⟩ ⟨b, hb_F⟩
          exact congr_arg Subtype.val h
        calc (g⁻¹ * a * g⁻¹⁻¹) * (g⁻¹ * b * g⁻¹⁻¹)
            = g⁻¹ * (a * b) * g⁻¹⁻¹ := by group
          _ = g⁻¹ * (b * a) * g⁻¹⁻¹ := by rw [habcomm]
          _ = (g⁻¹ * b * g⁻¹⁻¹) * (g⁻¹ * a * g⁻¹⁻¹) := by group
      · rintro ⟨_, ⟨a, ha_F, rfl⟩⟩
        apply Subtype.ext
        change (g⁻¹ * a * g⁻¹⁻¹) ^ p = 1
        have ha_p : a ^ p = 1 := by
          have h := hF_el.pow_eq_one ⟨a, ha_F⟩
          exact congr_arg Subtype.val h
        calc (g⁻¹ * a * g⁻¹⁻¹) ^ p
            = g⁻¹ * a ^ p * g⁻¹⁻¹ := by rw [conj_pow]
          _ = g⁻¹ * 1 * g⁻¹⁻¹ := by rw [ha_p]
          _ = 1 := by group
    have := hE.2.2 (F.map (MulAut.conj g⁻¹).toMonoidHom) hF_inv hF_inv_el
    rw [hF_conj_card] at this
    exact this

/-- **Isaacs Thm 7.6 Step 8** (mmd L3893-3896): under the running hypotheses, the
**conditional conclusion** of Step 2 (`J(P) ≤ L`) yields normality of `J(P)` in `G`.

Strategy: from `J(P) ≤ L = O_p(G)` and the Step 2 / Thm 7.2 bridge, `J(L) = J(P)`.
Then `g ∈ G`, `E ∈ E(L)` ⇒ `g E g⁻¹ ∈ E(L)` (`maxElemAbelianIn_conj_mem`), so the
iSup defining `J(L)` is `G`-stable. -/
private theorem normal_thompsonJ_of_le_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} (P : Sylow p G)
    (h_le : Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G) :
    (Subgroup.thompsonJ (P : Subgroup G) p).Normal := by
  -- Replace J(P) by J(L) using Thm 7.2.
  have hJLP : Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p =
      Subgroup.thompsonJ (P : Subgroup G) p :=
    thompsonJ_opCore_eq_thompsonJ_sylow_of_thompsonJ_le_opCore P h_le
  rw [← hJLP]
  -- It suffices to show: ∀ g ∈ G, (J(L)).map (conj g) ≤ J(L).
  refine ⟨?_⟩
  intro n hn g
  -- Reduce to: g * J(L) * g⁻¹ ≤ J(L).
  -- We show `(J(L)).map (MulAut.conj g).toMonoidHom ≤ J(L)`.
  have h_map_le :
      (Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p).map
        (MulAut.conj g).toMonoidHom ≤
      Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p := by
    rw [show Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p
          = ⨆ E ∈ Subgroup.maxElemAbelianIn
            (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p, E from rfl,
        Subgroup.map_iSup]
    refine iSup_le fun E => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hE_mem => ?_
    -- E.map (conj g) ∈ maxElemAbelianIn L p, so E.map (conj g) ≤ J(L).
    have h_conj_mem :=
      maxElemAbelianIn_conj_mem (L := OddOrder.Isaacs.Ch01.opCore p G) hE_mem g
    exact Subgroup.le_thompsonJ_of_mem_maxElemAbelianIn h_conj_mem
  have : g * n * g⁻¹ ∈ (Subgroup.thompsonJ
      (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p).map
        (MulAut.conj g).toMonoidHom := by
    refine ⟨n, hn, ?_⟩
    change g * n * g⁻¹ = g * n * g⁻¹
    rfl
  exact h_map_le this

/-! ### Step 7: contradiction giving `J(P) ≤ L` (mmd L3884-3892)

The book's Step 7 combines:

* The Step 5-6 conclusion: `A` acts trivially on `V := Z(O_p(G))`, i.e.,
  `[A, V] = 1` (`A` and `V` commute pointwise).
* The Step 1 conclusion: `Z(P) ≤ Z(L)` (Z(P) sits inside Z(L) since
  Z(P) commutes with all of L).
* The hypothesis (v): `P = C_G(Z(P))`.
* The maximality of `A ∈ E(P)`.

The combined counting argument forces `A ⊆ L`, contradicting the choice of
`A ⊄ L`.  This is the most delicate part of the Goldschmidt-style proof; we
**axiomatize the Step 7 conclusion** as the existence of a contradiction from
the working hypotheses, and use it together with Step 8's wrap-up.

Tracking issue: [`issues/0036-stuck-7-6-step-7.md`](../../../issues/0036-stuck-7-6-step-7.md). -/

/-! ### Step 4-5-8 closing axioms (mmd L3870-3896)

The Goldschmidt-style closing argument combines:

* **Step 4** (mmd L3870): `G = LA` and `P = UA` (using induction hypothesis on
  the proper subgroup `H = LA` to reach a contradiction unless `H = G`).
* **Step 5** (mmd L3874): `|Ā| = p`, using Lemma 6.20 (cyclic faithful coprime
  action) applied to `Ā ↷ L̅` (faithful by Step 1(c), coprime by p / p').  The
  Step 6.20 hypothesis "trivial on every proper invariant subgroup" comes from
  Step 3 applied to `MA` for any `Ā`-invariant `M̅ < L̅`.
* **Step 8** (mmd L3893-3896): combines |V : V∩A| ≤ p (Step 7, landed) with
  `P̄ = Ā` (from Step 4) and `Ā` abelian centralizing `V∩A` to derive
  `|V : C_V(P̄)| ≤ p`, then applies Thm 7.5 (`sylow_normal_of_elementary_normal_P_theorem`)
  to get `P̄ ⊴ Ḡ`, then pulls back to `P ⊴ G` and `A ⊆ P ⊆ U`, contradicting
  `A ⊄ U`.

We split the remaining work into three focused axioms (each tracking a single
textbook step), so future sessions can discharge them independently:

* `step4_5_LA_eq_top_and_Abar_card_eq_p`: Steps 4 + 5 combined (they share the
  same induction-hypothesis usage via Step 3).  Produces `P = UA ∧ Nat.card Ā = p`.
* `step8_normal_via_thm75`: Step 8's Thm 7.5 application (Ḡ ↷ V faithful with
  the |V : C_V(P̄)| ≤ p bound to `P̄ ⊴ Ḡ`).
* `step8_pullback`: pulling back `P̄ ⊴ Ḡ` to `P ⊴ G` and concluding `A ⊆ U`.

The glue between them is proved as actual theorem code.

Tracking issue: [`issues/0036-stuck-7-6-step-7.md`](../../../issues/0036-stuck-7-6-step-7.md). -/

/-- **Isaacs Thm 7.6 Step 1(b)** (mmd L3843): if `U = O_p(G) ≤ H ≤ G` then
`O_{p'}(H) = 1`.

Book argument: write `M = O_{p'}(H)`.  Both `M` and `U` (as `U.subgroupOf H`)
are normal `H`-subgroups with coprime orders (`M` a `p'`-group, `U` a `p`-group),
so they commute; hence `M` (mapped into `G`) lies in `C_G(U) ≤ U` (Hall-Higman
3.21, hypothesis (iv)).  But `M` is a `p'`-group inside the `p`-group `U`, so
`M = 1`. -/
private theorem oPiCorePrime_subgroup_eq_bot_of_opCore_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    {H : Subgroup G} (hUH : OddOrder.Isaacs.Ch01.opCore p G ≤ H) :
    OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (↥H) = ⊥ := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set M : Subgroup (↥H) := OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (↥H) with hM_def
  -- `M` is a `{q ≠ p}`-group.
  have hM_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} M :=
    OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := ↥H) {q | q ≠ p}
  -- `U` lives inside `H` as `U.subgroupOf H = U.comap H.subtype`, normal in `↥H`.
  have hU_le_H : U ≤ H := hUH
  set Usub : Subgroup (↥H) := U.subgroupOf H with hUsub_def
  haveI hUsub_normal : Usub.Normal :=
    (OddOrder.Isaacs.Ch01.opCore.normal p G).subgroupOf H
  -- `Usub` is a `p`-group (`comap` of the `p`-group `U` along an injective hom).
  have hU_pg : IsPGroup p ↥U := OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  have hUsub_pg : IsPGroup p ↥Usub := hU_pg.comap_subtype
  obtain ⟨k, hUsub_card⟩ : ∃ k, Nat.card ↥Usub = p ^ k := IsPGroup.iff_card.mp hUsub_pg
  -- `M ⊓ Usub = ⊥`: coprime cards (`p ∤ |M|` since `M` is `{q≠p}`).
  have hp_not_dvd_M : ¬ p ∣ Nat.card M := by
    intro hdvd
    have hp_pf : p ∈ (Nat.card M).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩
    exact (hM_pi p hp_pf) rfl
  have hcoprime : Nat.Coprime (Nat.card M) (Nat.card ↥Usub) := by
    rw [hUsub_card]
    have hp_cop : Nat.Coprime p (Nat.card M) :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd_M
    exact (hp_cop.symm).pow_right k
  have h_disj : Disjoint M Usub := disjoint_iff.mpr (Subgroup.inf_eq_bot_of_coprime hcoprime)
  -- `M` commutes with `Usub` (both normal, disjoint).
  have h_comm : ∀ m ∈ M, ∀ u ∈ Usub, (m : ↥H) * u = u * m := fun m hm u hu =>
    Subgroup.commute_of_normal_of_disjoint M Usub
      (OddOrder.Isaacs.Ch03.oPiCore.normal {q | q ≠ p} (↥H)) hUsub_normal h_disj
      m u hm hu
  -- Map `M` into `G`.
  set M' : Subgroup G := M.map H.subtype with hM'_def
  -- `M' ≤ C_G(U)`.
  have hM'_le_centralizer : M' ≤ Subgroup.centralizer (U : Set G) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu_H : u ∈ H := hU_le_H hu
    have hu_Usub : (⟨u, hu_H⟩ : ↥H) ∈ Usub := by
      rw [hUsub_def, Subgroup.mem_subgroupOf]; exact hu
    have hval := congrArg (Subtype.val : ↥H → G) (h_comm m hm ⟨u, hu_H⟩ hu_Usub)
    simpa using hval.symm
  -- `C_G(U) ≤ U` (Hall-Higman) ⇒ `M' ≤ U`.
  have hM'_le_U : M' ≤ U := hM'_le_centralizer.trans
    (centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot h_oPiPrime_trivial)
  -- `M'` is a `p`-group (inside `U`) and `Nat.card M' = Nat.card M` (injective map);
  -- but `p ∤ Nat.card M`, so `Nat.card M' = 1`, hence `M' = ⊥`, hence `M = ⊥`.
  have hM'_card : Nat.card ↥M' = Nat.card M := by
    rw [hM'_def]
    exact Nat.card_congr (Subgroup.equivMapOfInjective M H.subtype Subtype.coe_injective).symm.toEquiv
  have hM'_pg : IsPGroup p ↥M' :=
    hU_pg.of_injective (Subgroup.inclusion hM'_le_U) (Subgroup.inclusion_injective hM'_le_U)
  obtain ⟨j, hj⟩ : ∃ j, Nat.card ↥M' = p ^ j := IsPGroup.iff_card.mp hM'_pg
  have hj_zero : j = 0 := by
    by_contra hj_ne
    apply hp_not_dvd_M
    rw [← hM'_card, hj]
    exact dvd_pow_self p hj_ne
  have hM'_card_one : Nat.card ↥M' = 1 := by rw [hj, hj_zero, pow_zero]
  have hM'_bot : M' = ⊥ := Subgroup.card_eq_one.mp hM'_card_one
  -- `M.map H.subtype = ⊥` with injective `H.subtype` ⇒ `M = ⊥`.
  have hM_le_ker : M ≤ (H.subtype).ker := by
    rw [← Subgroup.map_eq_bot_iff]; exact hM'_bot
  rw [Subgroup.ker_subtype] at hM_le_ker
  exact le_bot_iff.mp hM_le_ker

/-- **Isaacs Thm 7.6 Step 3 hypothesis (v)** (mmd L3852): for an intermediate
subgroup `U ≤ H ≤ G`, the Sylow `S = H ∩ P` of `↥H` satisfies `C_H(Z(S)) = S`.

Book proof: `Z(P) ⊆ U ⊆ S ⊆ P` gives `Z(P) ⊆ Z(S)`, so
`C_H(Z(S)) ⊆ C_G(Z(P)) = P` (hypothesis (v) on `G`), a `p`-subgroup of `H`
containing the Sylow `S`; maximality forces equality. -/
private theorem centralizer_center_sylow_subgroup_eq_self_of_intermediate
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {H : Subgroup G}
    (hU_le_H : OddOrder.Isaacs.Ch01.opCore p G ≤ H)
    (S : Sylow p ↥H)
    (hS_eq : (S : Subgroup ↥H) = (H ⊓ (P : Subgroup G)).subgroupOf H) :
    Subgroup.centralizer
        (((Subgroup.center (S : Subgroup ↥H)).map (S : Subgroup ↥H).subtype) : Set ↥H)
      = (S : Subgroup ↥H) := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  -- `S` mapped to `G` is `H ⊓ P`.
  have hS_map : (S : Subgroup ↥H).map H.subtype = H ⊓ (P : Subgroup G) := by
    rw [hS_eq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  have hS_le_P : (S : Subgroup ↥H).map H.subtype ≤ (P : Subgroup G) := by
    rw [hS_map]; exact inf_le_right
  -- `U ≤ S` (as `U.subgroupOf H ≤ S`), so `Z(P)` image ⊆ image of S.
  have hU_le_HP : U ≤ H ⊓ (P : Subgroup G) := le_inf hU_le_H (OddOrder.Isaacs.Ch01.opCore_le P)
  -- `Z(P).map P.subtype ≤ U` (Step 1a).
  have hZP_le_U : (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤ U :=
    center_sylow_le_opCore_of_oPiCorePrime_eq_bot h_oPiPrime_trivial P
  -- Abbreviation: `ZS := Z(S).map S.subtype` (subgroup of `↥H`), `ZSG := ZS.map H.subtype`.
  set ZS : Subgroup ↥H := (Subgroup.center (S : Subgroup ↥H)).map (S : Subgroup ↥H).subtype
    with hZS_def
  refine le_antisymm ?_ ?_
  · -- `C_H(ZS) ≤ S`.  Map to `G`: contained in `C_G(Z(P)-image) = P`, p-subgroup ⊇ S.
    -- Step (a): `Z(P).map P.subtype ≤ ZS.map H.subtype` (central elts of P, lying in S,
    -- are central in S).
    have hZPG_le_ZSG :
        (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
          ZS.map H.subtype := by
      rintro _ ⟨z, hz_center, rfl⟩
      -- `(z : G) ∈ U ≤ H ⊓ P`, so `z` corresponds to an element of `S`.
      have hzG_U : ((z : (P : Subgroup G)) : G) ∈ U :=
        hZP_le_U ⟨z, hz_center, rfl⟩
      have hzG_H : ((z : (P : Subgroup G)) : G) ∈ H := hU_le_H hzG_U
      have hzG_P : ((z : (P : Subgroup G)) : G) ∈ (P : Subgroup G) := z.property
      -- `z` as element of `↥H`.
      set zH : ↥H := ⟨((z : (P : Subgroup G)) : G), hzG_H⟩ with hzH_def
      have hzH_S : zH ∈ (S : Subgroup ↥H) := by
        rw [hS_eq, Subgroup.mem_subgroupOf]
        exact ⟨hzG_H, hzG_P⟩
      -- `zH` is central in `S`: it commutes with every element of `S` (via `z ∈ Z(P)`, `S ≤ P`).
      have hzH_center : (⟨zH, hzH_S⟩ : (S : Subgroup ↥H)) ∈
          Subgroup.center (S : Subgroup ↥H) := by
        rw [Subgroup.mem_center_iff]
        intro s
        -- `s : ↥(S:Subgroup ↥H)`, its image in `G` lies in `P`.
        have hsG_P : (((s : (S : Subgroup ↥H)) : ↥H) : G) ∈ (P : Subgroup G) := by
          have hmem : (((s : (S : Subgroup ↥H)) : ↥H) : G) ∈
              (S : Subgroup ↥H).map H.subtype :=
            Subgroup.mem_map_of_mem H.subtype s.property
          exact hS_le_P hmem
        apply Subtype.ext; apply Subtype.ext
        -- `z` central in `P` commutes with `s`-image: `s_G * z_G = z_G * s_G`.
        have hcomm := Subgroup.mem_center_iff.mp hz_center
          (⟨(((s : (S : Subgroup ↥H)) : ↥H) : G), hsG_P⟩ : (P : Subgroup G))
        have hval := congrArg (fun x : (P : Subgroup G) => (x : G)) hcomm
        -- Goal (after two `Subtype.ext`): `s_G * z_G = z_G * s_G`.
        simpa [hzH_def] using hval
      -- So `zH.val (in G) ∈ ZS.map H.subtype`.
      exact ⟨zH, ⟨⟨zH, hzH_S⟩, hzH_center, rfl⟩, rfl⟩
    -- Step (b): `(C_H(ZS)).map H.subtype ≤ C_G(ZS.map H.subtype)`.
    have hcent_map :
        (Subgroup.centralizer (ZS : Set ↥H)).map H.subtype ≤
          Subgroup.centralizer ((ZS.map H.subtype) : Set G) := by
      rintro _ ⟨c, hc, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      have hcomm : c * w = w * c := (Subgroup.mem_centralizer_iff.mp hc w hw).symm
      exact congrArg (fun x : ↥H => (x : G)) hcomm.symm
    -- Combine: `(C_H(ZS)).map H.subtype ≤ C_G(Z(P)-image) = P`.
    have hcent_le_P : (Subgroup.centralizer (ZS : Set ↥H)).map H.subtype ≤ (P : Subgroup G) := by
      refine hcent_map.trans ?_
      have hmono : Subgroup.centralizer ((ZS.map H.subtype) : Set G) ≤
          Subgroup.centralizer
            (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G) :=
        Subgroup.centralizer_le hZPG_le_ZSG
      rw [h_centralizer_center] at hmono
      exact hmono
    -- `C_H(ZS) ≤ P.subgroupOf H` (a `p`-group), containing the Sylow `S` ⇒ equal.
    have hcent_le_Psub :
        Subgroup.centralizer (ZS : Set ↥H) ≤ (P : Subgroup G).subgroupOf H := by
      intro c hc
      rw [Subgroup.mem_subgroupOf]
      have : (c : G) ∈ (P : Subgroup G) := hcent_le_P ⟨c, hc, rfl⟩
      exact this
    have hPsub_pg : IsPGroup p ↥((P : Subgroup G).subgroupOf H) :=
      P.isPGroup'.comap_subtype
    have hcent_pg : IsPGroup p ↥(Subgroup.centralizer (ZS : Set ↥H)) :=
      hPsub_pg.of_injective (Subgroup.inclusion hcent_le_Psub)
        (Subgroup.inclusion_injective hcent_le_Psub)
    -- `S ≤ C_H(ZS)` (next bullet), so the Sylow `S` is inside the `p`-subgroup `C_H(ZS)`.
    have hS_le_cent : (S : Subgroup ↥H) ≤ Subgroup.centralizer (ZS : Set ↥H) := by
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      have hcomm : (⟨s, hs⟩ : (S : Subgroup ↥H)) * w = w * ⟨s, hs⟩ :=
        Subgroup.mem_center_iff.mp hw ⟨s, hs⟩
      exact congrArg (fun x : (S : Subgroup ↥H) => (x : ↥H)) hcomm.symm
    exact (S.is_maximal' hcent_pg hS_le_cent).le
  · -- `S ≤ C_H(ZS)`: every `s ∈ S` centralizes `Z(S) ⊆ S`.
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    have hcomm : (⟨s, hs⟩ : (S : Subgroup ↥H)) * w = w * ⟨s, hs⟩ :=
      Subgroup.mem_center_iff.mp hw ⟨s, hs⟩
    exact congrArg (fun x : (S : Subgroup ↥H) => (x : ↥H)) hcomm.symm

/-- **Isaacs Thm 7.6 Step 3** (mmd L3850-3856): the IH-consuming core of the
Goldschmidt argument.

Given `U·A ≤ H` with `H` a **proper** subgroup of `G` and `H ∩ P ∈ Syl_p(H)`,
the conclusion is `⁅L ⊓ H, A⁆ ≤ U`, i.e. `Ā` centralizes `(L ∩ H)bar` in
`Ḡ = G/U`.  Here `L = O_{p',p}(G)` (`opPpPrimeCore`), `U = O_p(G)`.

Book proof (mmd L3850-3856):
* `H` satisfies the five Thm 7.6 hypotheses: (i) `p`-separable (subgroup),
  (ii) `p ≠ 2`, (iii) Sylow-2 abelian (descent), (iv) `O_{p'}(H) = 1`
  (`oPiCorePrime_subgroup_eq_bot_of_opCore_le`, landed), and (v)
  `C_H(Z(S)) = S` for `S = H ∩ P`
  (`centralizer_center_sylow_subgroup_eq_self_of_intermediate`, landed).
* By the IH (`H < G`), `J(S) ⊴ H`.  Since `A ∈ E(P)` and `A ⊆ S ⊆ P`,
  `A ∈ E(S)`, so `A ⊆ J(S)`.
* `⁅L ⊓ H, A⁆ ⊆ ⁅L ⊓ H, J(S)⁆ ⊆ (L ⊓ H) ⊓ J(S)` (both normal in `H`)
  `⊆ L ⊓ J(S) ⊆ U` (`U` is the unique Sylow-`p` of `L`).

Hypothesis (v) is the landed
`centralizer_center_sylow_subgroup_eq_self_of_intermediate`. -/
private theorem step3_Abar_centralizes_inter_LBar.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    (ih : ∀ (H : Type u) [Group H] [Finite H]
      [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H],
      Nat.card H < Nat.card G →
      (∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥ →
      ∀ (Q : Sylow p H),
        Subgroup.centralizer
            (((Subgroup.center (Q : Subgroup H)).map
              (Q : Subgroup H).subtype) : Set H)
          = (Q : Subgroup H) →
        (Subgroup.thompsonJ (Q : Subgroup H) p).Normal)
    {A : Subgroup G}
    (hA_mem : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    {H : Subgroup G}
    (hH_ne_top : H ≠ ⊤)
    (hUA_le_H : OddOrder.Isaacs.Ch01.opCore p G ⊔ A ≤ H)
    (S : Sylow p ↥H)
    (hS_eq : (S : Subgroup ↥H) = (H ⊓ (P : Subgroup G)).subgroupOf H) :
    (⁅opPpPrimeCore G p ⊓ H, A⁆ : Subgroup G) ≤ OddOrder.Isaacs.Ch01.opCore p G := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set L : Subgroup G := opPpPrimeCore G p with hL_def
  have hU_le_H : U ≤ H := le_sup_left.trans hUA_le_H
  have hA_le_H : A ≤ H := le_sup_right.trans hUA_le_H
  have hA_le_P : A ≤ (P : Subgroup G) := hA_mem.1
  -- `S` mapped to `G` is `H ⊓ P`.
  have hS_map : (S : Subgroup ↥H).map H.subtype = H ⊓ (P : Subgroup G) := by
    rw [hS_eq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  -- (a) `Nat.card ↥H < Nat.card G` (since `H ≠ ⊤`).
  have hcard_lt : Nat.card ↥H < Nat.card G := by
    have hidx : 1 < H.index := Subgroup.one_lt_index_of_ne_top hH_ne_top
    have hmul : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
    calc Nat.card ↥H = Nat.card ↥H * 1 := (mul_one _).symm
      _ < Nat.card ↥H * H.index := (Nat.mul_lt_mul_left Nat.card_pos).mpr hidx
      _ = Nat.card G := hmul
  -- (b) Descend hypotheses to `↥H`.
  haveI : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) (↥H) :=
    OddOrder.Isaacs.Ch03.Subgroup.isPiSeparable_of_isPiSeparable ({p} : Set ℕ) H
  have h2abelian' : ∀ T : Subgroup ↥H, IsPGroup 2 T → ∀ x y : ↥T, x * y = y * x := by
    intro T hT2
    have hTG2 : IsPGroup 2 (T.map H.subtype) := hT2.map H.subtype
    have hTGcomm := h2abelian (T.map H.subtype) hTG2
    intro a b
    apply Subtype.ext; apply Subtype.ext
    have h := hTGcomm ⟨((a : ↥H) : G), ⟨(a : ↥H), a.property, rfl⟩⟩
      ⟨((b : ↥H) : G), ⟨(b : ↥H), b.property, rfl⟩⟩
    exact congrArg (fun z : ↥(T.map H.subtype) => (z : G)) h
  have h_oPi' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (↥H) = ⊥ :=
    oPiCorePrime_subgroup_eq_bot_of_opCore_le h_oPiPrime_trivial hU_le_H
  -- Hypothesis (v) for `S`.
  have hv : Subgroup.centralizer
        (((Subgroup.center (S : Subgroup ↥H)).map (S : Subgroup ↥H).subtype) : Set ↥H)
      = (S : Subgroup ↥H) :=
    centralizer_center_sylow_subgroup_eq_self_of_intermediate h_oPiPrime_trivial P
      h_centralizer_center hU_le_H S hS_eq
  -- (c) IH: `J(S) ⊴ ↥H`.
  have hJS_normal : (Subgroup.thompsonJ (S : Subgroup ↥H) p).Normal :=
    ih (↥H) hcard_lt h2abelian' h_oPi' S hv
  -- (d) `A.subgroupOf H ∈ maxElemAbelianIn S p`, hence `A.subgroupOf H ≤ J(S)`.
  have hAsub_le_S : A.subgroupOf H ≤ (S : Subgroup ↥H) := by
    rw [hS_eq]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨x.property, hA_le_P hx⟩
  -- `A.subgroupOf H ≃* A` (since `A ≤ H`), preserving cardinality and elem-ab.
  have hAsub_equiv := Subgroup.subgroupOfEquivOfLe hA_le_H
  have hAsub_card : Nat.card ↥(A.subgroupOf H) = Nat.card ↥A :=
    Nat.card_congr hAsub_equiv.toEquiv
  have hAsub_el : (A.subgroupOf H).IsElementaryAbelian p := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · exact hAsub_equiv.injective (by
        rw [map_mul, map_mul]; exact (hA_mem.2.1).comm (hAsub_equiv x) (hAsub_equiv y))
    · exact hAsub_equiv.injective (by
        rw [map_pow, map_one]; exact (hA_mem.2.1).pow_eq_one (hAsub_equiv x))
  have hAsub_mem : A.subgroupOf H ∈ Subgroup.maxElemAbelianIn (S : Subgroup ↥H) p := by
    refine ⟨hAsub_le_S, hAsub_el, ?_⟩
    intro F hF_S hF_el
    -- `F.map H.subtype ≤ H ⊓ P ≤ P` is elem-ab; `A ∈ E(P)` ⇒ `|F| ≤ |A|`.
    have hFmap_le_P : F.map H.subtype ≤ (P : Subgroup G) := by
      have : F.map H.subtype ≤ (S : Subgroup ↥H).map H.subtype := Subgroup.map_mono hF_S
      rw [hS_map] at this
      exact this.trans inf_le_right
    have hFmap_el : (F.map H.subtype).IsElementaryAbelian p :=
      isElementaryAbelian_map_of_isElementaryAbelian H.subtype hF_el
    have hFmap_card : Nat.card ↥(F.map H.subtype) = Nat.card ↥F :=
      Nat.card_congr (Subgroup.equivMapOfInjective F H.subtype Subtype.coe_injective).symm.toEquiv
    have hle := hA_mem.2.2 (F.map H.subtype) hFmap_le_P hFmap_el
    rw [hFmap_card] at hle
    rw [← hAsub_card] at hle
    exact hle
  have hAsub_le_JS : A.subgroupOf H ≤ Subgroup.thompsonJ (S : Subgroup ↥H) p :=
    Subgroup.le_thompsonJ_of_mem_maxElemAbelianIn hAsub_mem
  -- (e) Commutator chain in `↥H`: `⁅L.subgroupOf H, A.subgroupOf H⁆ ≤ U.subgroupOf H`.
  set mk : G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hmk_def
  have hU_eq_oPi : U = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  -- `L.subgroupOf H` is normal in `↥H` (L ⊴ G).
  haveI hLsub_normal : (L.subgroupOf H).Normal := by
    rw [hL_def]; exact (opPpPrimeCore_normal (G := G) (p := p)).subgroupOf H
  -- `J(S) ≤ S ≤ P`, so `J(S).map H.subtype` is a `p`-subgroup of `G` inside `P`.
  have hJS_le_S : Subgroup.thompsonJ (S : Subgroup ↥H) p ≤ (S : Subgroup ↥H) :=
    Subgroup.thompsonJ_le _ _
  have hJSmap_le_P : (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤ (P : Subgroup G) := by
    have : (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤
        (S : Subgroup ↥H).map H.subtype := Subgroup.map_mono hJS_le_S
    rw [hS_map] at this
    exact this.trans inf_le_right
  -- `⁅L.subgroupOf H, A.subgroupOf H⁆ ≤ ⁅L.subgroupOf H, J(S)⁆ ≤ (L.subgroupOf H) ⊓ J(S)`.
  haveI := hJS_normal
  have hchain : (⁅L.subgroupOf H, A.subgroupOf H⁆ : Subgroup ↥H) ≤
      (L.subgroupOf H) ⊓ Subgroup.thompsonJ (S : Subgroup ↥H) p := by
    refine le_trans (Subgroup.commutator_mono le_rfl hAsub_le_JS) ?_
    exact Subgroup.commutator_le_inf (L.subgroupOf H) (Subgroup.thompsonJ (S : Subgroup ↥H) p)
  -- Map the chain back to `G`: `⁅L ⊓ H, A⁆ ≤ ((L.subgroupOf H) ⊓ J(S)).map H.subtype`.
  have hcomm_map_eq : (⁅L.subgroupOf H, A.subgroupOf H⁆ : Subgroup ↥H).map H.subtype =
      ⁅(L ⊓ H), A⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA_le_H, inf_comm L H]
  -- The target `⁅L ⊓ H, A⁆ ≤ U`.
  have hgoal_map : ⁅(L ⊓ H), A⁆ ≤ ((L.subgroupOf H) ⊓
      Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype := by
    rw [← hcomm_map_eq]; exact Subgroup.map_mono hchain
  -- `((L.subgroupOf H) ⊓ J(S)).map H.subtype ≤ L ⊓ (J(S).map H.subtype)`.
  have hinf_map_le : ((L.subgroupOf H) ⊓ Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤
      L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype := by
    rintro _ ⟨x, ⟨hxL, hxJ⟩, rfl⟩
    refine ⟨?_, Subgroup.mem_map_of_mem _ hxJ⟩
    have : (x : G) ∈ L := hxL
    exact this
  -- `L ⊓ (p-subgroup) ≤ U`: any `p`-subgroup of `L` lies in `U` (since `L/U` is `p'`).
  have hLinf_le_U : L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤ U := by
    -- `K := L ⊓ J(S).map` is a `p`-group (≤ J(S).map ≤ P).
    have hK_le_P : L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤
        (P : Subgroup G) := inf_le_right.trans hJSmap_le_P
    have hK_pg : IsPGroup p ↥(L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype) :=
      P.isPGroup'.of_injective (Subgroup.inclusion hK_le_P) (Subgroup.inclusion_injective hK_le_P)
    -- `K ≤ L`, and `K.map mk` is a `p`-group inside `L̄ = O_{p'}(Ḡ)`, hence trivial ⇒ `K ≤ U`.
    intro x hx
    have hxL : x ∈ L := hx.1
    -- `mk x ∈ L̄` and `mk x` lies in the `p`-group image, but `L̄` is `p'`, so `mk x = 1`.
    have hKmap_pg : IsPGroup p ((L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype).map mk) :=
      hK_pg.map mk
    have hxbar_mem : mk x ∈ (L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype).map mk :=
      Subgroup.mem_map_of_mem mk hx
    have hxbar_Lbar : mk x ∈ OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
      have hLmap : L.map mk = OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
        rw [hL_def, hmk_def]; exact opPpPrimeCore_map_eq_LBar
      rw [← hLmap]; exact Subgroup.mem_map_of_mem mk hxL
    -- `mk x` has order a power of `p` (in the image) and divides `|L̄|` (a `p'`-number) ⇒ `mk x = 1`.
    have hxbar_one : mk x = 1 := by
      -- order of `mk x` divides a `p`-power (from the `p`-group `K.map mk`).
      obtain ⟨k, hk⟩ := hKmap_pg ⟨mk x, hxbar_mem⟩
      have hord_dvd_pk : orderOf (mk x) ∣ p ^ k := by
        rw [orderOf_dvd_iff_pow_eq_one]
        have hk' : (⟨mk x, hxbar_mem⟩ :
            ↥((L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype).map mk)) ^ p ^ k = 1 := hk
        have := congrArg (Subtype.val) hk'
        simpa using this
      -- order of `mk x` divides `|L̄|` (since `mk x ∈ L̄`).
      have hord_dvd_Lbar : orderOf (mk x) ∣ Nat.card (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) :=
        Subgroup.orderOf_dvd_natCard _ hxbar_Lbar
      -- `|L̄|` is a `p'`-number, so coprime to `p^k`; hence `orderOf (mk x) = 1`.
      have hp_not_dvd_Lbar : ¬ p ∣ Nat.card (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) := by
        intro hdvd
        exact (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := G ⧸ OddOrder.Isaacs.Ch03.oPiCore
          ({p} : Set ℕ) G) {q | q ≠ p} p
          (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) rfl
      have hcop : Nat.Coprime (p ^ k) (Nat.card (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))) :=
        Nat.Coprime.pow_left k ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd_Lbar)
      have hord_one : orderOf (mk x) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hord_dvd_pk hord_dvd_Lbar
      exact orderOf_eq_one_iff.mp hord_one
    -- `mk x = 1 ⇒ x ∈ ker mk = U`.
    have hx_U : x ∈ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
      (QuotientGroup.eq_one_iff x).mp hxbar_one
    rwa [← hU_eq_oPi] at hx_U
  exact (hgoal_map.trans hinf_map_le).trans hLinf_le_U

/-- For `N ⊴ G` and `A` with `N ⊓ A = ⊥`, the relative index `A.relIndex (N ⊔ A)`
equals `Nat.card N`.  (Diamond isomorphism: `|NA : A| = |N : N ⊓ A| = |N|`.) -/
private theorem relIndex_sup_of_inf_eq_bot
    {G : Type*} [Group G] [Finite G] {N A : Subgroup G} [N.Normal]
    (h_inf : N ⊓ A = ⊥) :
    A.relIndex (N ⊔ A) = Nat.card N := by
  classical
  -- `|NA| = |A| * (A.relIndex NA)` (card_mul_index inside `↥(N ⊔ A)`).
  have hA_le : A ≤ N ⊔ A := le_sup_right
  have hN_le : N ≤ N ⊔ A := le_sup_left
  have h1 : Nat.card (A.subgroupOf (N ⊔ A)) * (A.subgroupOf (N ⊔ A)).index =
      Nat.card ↥(N ⊔ A) := Subgroup.card_mul_index _
  have h1' : Nat.card A * A.relIndex (N ⊔ A) = Nat.card ↥(N ⊔ A) := by
    rw [← h1]
    congr 1
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le).toEquiv).symm
  -- `|NA| = |N| * (N.relIndex NA)` and `N.relIndex NA = N.relIndex A = |A|`.
  have h2 : Nat.card (N.subgroupOf (N ⊔ A)) * (N.subgroupOf (N ⊔ A)).index =
      Nat.card ↥(N ⊔ A) := Subgroup.card_mul_index _
  have hNrel : (N.subgroupOf (N ⊔ A)).index = Nat.card A := by
    show N.relIndex (N ⊔ A) = Nat.card A
    rw [Subgroup.relIndex_sup_left]
    -- `N.relIndex A = |A : N ⊓ A| = |A : ⊥| = |A|`.
    show (N.subgroupOf A).index = Nat.card A
    have : N.subgroupOf A = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot]
      rw [disjoint_iff]; exact h_inf
    rw [this, Subgroup.index_bot]
  have h2' : Nat.card N * Nat.card A = Nat.card ↥(N ⊔ A) := by
    rw [← h2, hNrel]
    congr 1
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_le).toEquiv).symm
  -- Cancel `Nat.card A` from `|A| * relIndex = |N| * |A|`.
  have hA_pos : 0 < Nat.card A := Nat.card_pos
  have hfin : Nat.card A * A.relIndex (N ⊔ A) = Nat.card A * Nat.card N := by
    rw [h1', ← h2', mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hA_pos hfin

/-- **Modular law, normalizer form** (mmd L3877): if `W ≤ L`, `A ⊓ L = ⊥`, and `A`
normalizes `W`, then `(W ⊔ A) ⊓ L = W`.  Used to show `W ⊔ Ā = ⊤ ⇒ W = L̄`.

The mathlib `IsModularLattice (Subgroup ·)` instance only covers `[CommGroup]`; here
the noncommutative case is handled by hand via the product representation `W·A` of
`W ⊔ A` (valid since `A ≤ N(W)`, so `W` is normal in `W ⊔ A`). -/
private theorem inf_sup_eq_of_le_normalizer_of_inf_eq_bot
    {G : Type*} [Group G] {W A L : Subgroup G}
    (hW_le : W ≤ L) (hA_inf : A ⊓ L = ⊥) (hAnorm : A ≤ Subgroup.normalizer (W : Set G)) :
    (W ⊔ A) ⊓ L = W := by
  apply le_antisymm
  · intro x ⟨hxWA, hxL⟩
    -- `W` is normal in `A ⊔ W`, so `x = w * a` with `w ∈ W`, `a ∈ A`.
    haveI : (W.subgroupOf (A ⊔ W)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAnorm
    have hx_AW : x ∈ A ⊔ W := by rw [sup_comm]; exact hxWA
    have hmem : (⟨x, hx_AW⟩ : ↥(A ⊔ W)) ∈ (W.subgroupOf (A ⊔ W)) ⊔ (A.subgroupOf (A ⊔ W)) := by
      rw [← Subgroup.subgroupOf_sup (le_sup_right) (le_sup_left), sup_comm W A,
        Subgroup.subgroupOf_self]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_left] at hmem
    obtain ⟨⟨w, hw_AW⟩, hw, ⟨a, ha_AW⟩, ha, heq⟩ := hmem
    have hw_W : w ∈ W := hw
    have ha_A : a ∈ A := ha
    have hxeq : x = w * a := congrArg (Subtype.val) heq |>.symm
    -- `a = w⁻¹ * x ∈ L` (since `w ∈ W ≤ L`, `x ∈ L`), so `a ∈ A ⊓ L = ⊥`, `a = 1`.
    have ha_L : a ∈ L := by
      have : w⁻¹ * x ∈ L := L.mul_mem (L.inv_mem (hW_le hw_W)) hxL
      rwa [hxeq, ← mul_assoc, inv_mul_cancel, one_mul] at this
    have ha_one : a = 1 := by
      have : a ∈ A ⊓ L := ⟨ha_A, ha_L⟩
      rw [hA_inf, Subgroup.mem_bot] at this; exact this
    rw [hxeq, ha_one, mul_one]; exact hw_W
  · exact le_inf le_sup_left hW_le

/-- **Isaacs Thm 7.6 Step 5, "trivial on proper invariant" clause** (mmd L3876-3878).

Given the running Thm 7.6 hypotheses, the IH, the chosen `A ∈ E(P)` with `A ⊄ U`,
and Step 4's output `P = UA`, every `Ā`-invariant proper subgroup `W < L̄` of
`L̄ = O_{p'}(Ḡ)` is centralized by `Ā` (`⁅W, Ā⁆ = ⊥`).

Book proof: set `M = preimage of W in G containing U` (`= W.comap mk`), so
`U ≤ M ≤ L`.  `A ≤ N_G(M)` (since `Ā` normalizes `W` and `U = ker mk ≤ M`),
hence `H = M ⊔ A` is proper (`H = ⊤` would force `W ⊔ Ā = ⊤`, and the modular
law `(W ⊔ Ā) ⊓ L̄ = W ⊔ (Ā ⊓ L̄) = W` would give `L̄ = W`, contradicting `W < L̄`)
with `P = UA ⊆ H` Sylow (`|H : P| = |W|`, a `p'`-number, via `relIndex`).  Step 3
applied to `H` gives `⁅L ⊓ H, A⁆ ≤ U`; since `M ≤ L ⊓ H`, `⁅M, A⁆ ≤ U = ker mk`,
so `⁅W, Ā⁆ = mk⁅M, A⁆ = ⊥`. -/
private theorem step5_Abar_centralizes_invariant_proper.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    (ih : ∀ (H : Type u) [Group H] [Finite H]
      [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H],
      Nat.card H < Nat.card G →
      (∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥ →
      ∀ (Q : Sylow p H),
        Subgroup.centralizer
            (((Subgroup.center (Q : Subgroup H)).map
              (Q : Subgroup H).subtype) : Set H)
          = (Q : Subgroup H) →
        (Subgroup.thompsonJ (Q : Subgroup H) p).Normal)
    {A : Subgroup G}
    (hA_mem : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (h_P_eq_UA : OddOrder.Isaacs.Ch01.opCore p G ⊔ A = (P : Subgroup G))
    {W : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)}
    (hW_le : W ≤ OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))
    (hW_ne : W ≠ OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))
    (hW_normalized : ∀ a : G, a ∈ A → ∀ w, w ∈ W →
      (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) a * w *
        ((QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) a)⁻¹ ∈ W) :
    (⁅W, A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))⁆ :
      Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set L : Subgroup G := opPpPrimeCore G p with hL_def
  set mk : G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hmk_def
  set Lbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :=
    OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hLbar_def
  set Abar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := A.map mk
    with hAbar_def
  have hU_eq_oPi : U = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  have hker_mk : mk.ker = U := by rw [hmk_def, QuotientGroup.ker_mk', hU_eq_oPi]
  have hA_le_P : A ≤ (P : Subgroup G) := hA_mem.1
  have hA_pg : IsPGroup p A := hA_mem.2.1.isPGroup
  have hU_le_P : U ≤ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P
  -- `L = comap mk L̄`, and `L.map mk = L̄`.
  have hL_comap : L = Lbar.comap mk := by rw [hL_def, hLbar_def, hmk_def, opPpPrimeCore]
  have hLmap : L.map mk = Lbar := by rw [hL_def, hLbar_def, hmk_def]; exact opPpPrimeCore_map_eq_LBar
  have hU_le_L : U ≤ L := by rw [hU_eq_oPi, hL_def]; exact oPiCore_p_le_opPpPrimeCore
  -- `M = preimage of W`, `U ≤ M ≤ L`.
  set M : Subgroup G := W.comap mk with hM_def
  have hU_le_M : U ≤ M := by
    rw [hM_def, ← hker_mk]; intro x hx; rw [Subgroup.mem_comap, hx]; exact W.one_mem
  have hM_le_L : M ≤ L := by rw [hM_def, hL_comap]; exact Subgroup.comap_mono hW_le
  have hMmap : M.map mk = W := by
    rw [hM_def]; exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) W
  -- `H = M ⊔ A`.  `U ⊔ A ≤ H`, `P ≤ H`, `mk H = W ⊔ Abar`.
  set H : Subgroup G := M ⊔ A with hH_def
  have hUA_le_H : U ⊔ A ≤ H := sup_le_sup_right hU_le_M A
  have hP_le_H : (P : Subgroup G) ≤ H := by rw [← h_P_eq_UA]; exact hUA_le_H
  have hHmap : H.map mk = W ⊔ Abar := by
    rw [hH_def, Subgroup.map_sup, hMmap, hAbar_def]
  -- `Abar` normalizes `W` (from `hW_normalized`).
  have hAbar_inf_Lbar : Abar ⊓ Lbar = ⊥ := by
    rw [hAbar_def, hLbar_def]; exact AbarInf_LBar_eq_bot hA_pg
  have hAbar_norm_W : Abar ≤ Subgroup.normalizer (W : Set _) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw; exact hW_normalized a ha w hw
    · intro hw
      have := hW_normalized a⁻¹ (A.inv_mem ha) _ hw
      simpa [map_inv, mul_assoc] using this
  -- `H ≠ ⊤`: else `W ⊔ Abar = ⊤`, modular law forces `W = L̄`.
  have hH_ne_top : H ≠ ⊤ := by
    intro hHtop
    apply hW_ne
    have hWAbar_top : W ⊔ Abar = ⊤ := by rw [← hHmap, hHtop, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)]
    -- `(W ⊔ Abar) ⊓ L̄ = W` (modular law), and LHS `= ⊤ ⊓ L̄ = L̄`.
    have hmod := inf_sup_eq_of_le_normalizer_of_inf_eq_bot hW_le hAbar_inf_Lbar hAbar_norm_W
    rw [hWAbar_top, top_inf_eq] at hmod
    exact hmod.symm
  -- `P = UA ⊆ H` is a Sylow `p`-subgroup of `G` contained in `H`, hence Sylow in `↥H`
  -- (`Sylow.subtype`).  Since `P ⊆ H`, `H ⊓ P = P`, giving the form Step 3 wants.
  let S : Sylow p ↥H := P.subtype hP_le_H
  have hS_coe : (S : Subgroup ↥H) = (P : Subgroup G).subgroupOf H := P.coe_subtype hP_le_H
  have hHP_eq_P : H ⊓ (P : Subgroup G) = (P : Subgroup G) := inf_eq_right.mpr hP_le_H
  have hS_eq_HP : (S : Subgroup ↥H) = (H ⊓ (P : Subgroup G)).subgroupOf H := by
    rw [hS_coe, hHP_eq_P]
  -- Step 3 applied to `H`: `⁅L ⊓ H, A⁆ ≤ U`.
  have hStep3 : (⁅L ⊓ H, A⁆ : Subgroup G) ≤ U :=
    step3_Abar_centralizes_inter_LBar P hp2 h_pSolvable h2abelian h_oPiPrime_trivial
      h_centralizer_center ih hA_mem hH_ne_top hUA_le_H S hS_eq_HP
  -- `M ≤ L ⊓ H`, so `⁅M, A⁆ ≤ ⁅L ⊓ H, A⁆ ≤ U = ker mk`.
  have hM_le_LinfH : M ≤ L ⊓ H := le_inf hM_le_L le_sup_left
  have hMA_le_U : (⁅M, A⁆ : Subgroup G) ≤ U :=
    (Subgroup.commutator_mono hM_le_LinfH le_rfl).trans hStep3
  -- `⁅W, Abar⁆ = mk⁅M, A⁆ ≤ mk U = ⊥`.
  have hcomm_map : (⁅M, A⁆ : Subgroup G).map mk = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hker_mk]; exact hMA_le_U
  rw [← hMmap, hAbar_def, ← Subgroup.map_commutator, hcomm_map]

/-- The conjugation `MulDistribMulAction` of `↥Q` on the normal subgroup `↥N`
of `K`, via `MulAut.conjNormal ∘ Q.subtype`.  Under this action,
`a • n = ⟨↑a * ↑n * (↑a)⁻¹⟩`.  Used in Step 5 with `Q = Ā`, `N = L̄`. -/
private noncomputable def subgroupConjActionOnNormal
    {K : Type*} [Group K] (Q N : Subgroup K) [N.Normal] :
    MulDistribMulAction ↥Q ↥N :=
  MulDistribMulAction.compHom ↥N ((MulAut.conjNormal (H := N)).comp Q.subtype)

/-- **Isaacs Thm 7.6 Step 5** (mmd L3874): `|Ā| = p`, equivalently
`(O_p(G)).relIndex A = p`.

Given Step 4's output `P = UA` plus the running hypotheses and the induction
hypothesis, `Ā = A.map mk'` acts faithfully and coprimely on `L̄ = O_{p'}(Ḡ)`
(faithful by Step 1(c) + `Ā ⊓ L̄ = ⊥`; coprime by `p` vs `p'`).  By Lemma 6.20
(`isCyclic_of_faithful_trivial_on_proper_invariant`), `Ā` is cyclic — the
"trivial on every `Ā`-invariant proper subgroup `M̄ < L̄`" hypothesis is exactly
`step5_Abar_centralizes_invariant_proper` (Step 3 applied to `H = MA`).  A
nontrivial cyclic elementary abelian `p`-group has order `p`; the conversion of
`Nat.card Ā = p` to `(O_p(G)).relIndex A = p` is `relIndex_sup_of_inf_eq_bot`. -/
private theorem step5_Abar_card_eq_p.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    (ih : ∀ (H : Type u) [Group H] [Finite H]
      [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H],
      Nat.card H < Nat.card G →
      (∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥ →
      ∀ (Q : Sylow p H),
        Subgroup.centralizer
            (((Subgroup.center (Q : Subgroup H)).map
              (Q : Subgroup H).subtype) : Set H)
          = (Q : Subgroup H) →
        (Subgroup.thompsonJ (Q : Subgroup H) p).Normal)
    {A : Subgroup G}
    (hA_mem : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (hA_not_le : ¬ A ≤ OddOrder.Isaacs.Ch01.opCore p G)
    (h_P_eq_UA : OddOrder.Isaacs.Ch01.opCore p G ⊔ A = (P : Subgroup G)) :
    (OddOrder.Isaacs.Ch01.opCore p G).relIndex A = p := by
  classical
  haveI : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G := h_pSolvable
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set mk : G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hmk_def
  set Lbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :=
    OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hLbar_def
  set Abar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := A.map mk
    with hAbar_def
  have hU_eq_oPi : U = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  have hA_pg : IsPGroup p A := hA_mem.2.1.isPGroup
  haveI hLbar_normal : Lbar.Normal := by
    rw [hLbar_def]; exact OddOrder.Isaacs.Ch03.oPiCore.normal _ _
  -- `Ā ⊓ L̄ = ⊥`, `Ā ≠ ⊥`.
  have hAbar_inf_Lbar : Abar ⊓ Lbar = ⊥ := by
    rw [hAbar_def, hLbar_def]; exact AbarInf_LBar_eq_bot hA_pg
  have hAbar_ne_bot : Abar ≠ ⊥ := by
    rw [hAbar_def, hmk_def]
    exact Abar_ne_bot_of_not_le (by rwa [hU_eq_oPi] at hA_not_le)
  -- The conjugation action `↥Ā ↷ ↥L̄`.  `a • n = ⟨↑a * ↑n * (↑a)⁻¹⟩`.
  letI : MulDistribMulAction ↥Abar ↥Lbar := subgroupConjActionOnNormal Abar Lbar
  have hsmul_coe : ∀ (a : ↥Abar) (n : ↥Lbar),
      ((a • n : ↥Lbar) : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) =
        (↑a : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) * ↑n * (↑a)⁻¹ := by
    intro a n; rfl
  -- `Ā` is elementary abelian (image of the elementary abelian `A`).
  have hAbar_el : OddOrder.GroupTheory.IsElementaryAbelian p ↥Abar := by
    rw [hAbar_def]
    exact isElementaryAbelian_map_of_isElementaryAbelian mk
      (A := A) ⟨hA_mem.2.1.1, hA_mem.2.1.2⟩
  -- `↥Ā` is abelian.
  haveI : IsMulCommutative ↥Abar := ⟨⟨hAbar_el.1⟩⟩
  -- The action is faithful: `a` fixes all of `L̄` ⇒ `↑a ∈ C_Ḡ(L̄)`, and `Ā ⊓ C_Ḡ(L̄) = ⊥`.
  have hAbar_inf_cent :
      Abar ⊓ Subgroup.centralizer
        (Lbar : Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
    rw [hAbar_def, hLbar_def]; exact AbarInf_centralizer_LBar_eq_bot hA_pg
  haveI : FaithfulSMul ↥Abar ↥Lbar := by
    refine ⟨fun {a b} h => ?_⟩
    -- `↑b⁻¹ * ↑a` centralizes `L̄`.
    set ga : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G := a.1 with hga
    set gb : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G := b.1 with hgb
    have hcent : gb⁻¹ * ga ∈ Subgroup.centralizer
        (Lbar : Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have heq := h ⟨m, hm⟩
      rw [Subtype.ext_iff, hsmul_coe, hsmul_coe, ← hga, ← hgb] at heq
      -- `heq : ga * m * ga⁻¹ = gb * m * gb⁻¹`  ⇒  `m * (gb⁻¹ * ga) = (gb⁻¹ * ga) * m`.
      calc m * (gb⁻¹ * ga)
          = gb⁻¹ * (gb * m * gb⁻¹) * ga := by group
        _ = gb⁻¹ * (ga * m * ga⁻¹) * ga := by rw [heq]
        _ = (gb⁻¹ * ga) * m := by group
    have hmem : gb⁻¹ * ga ∈ Abar ⊓ Subgroup.centralizer
        (Lbar : Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) :=
      ⟨Abar.mul_mem (Abar.inv_mem b.2) a.2, hcent⟩
    rw [hAbar_inf_cent, Subgroup.mem_bot] at hmem
    exact Subtype.ext (inv_mul_eq_one.mp hmem).symm
  -- Coprimality: `|Ā|` is a `p`-power, `|L̄|` is a `p'`-number.
  have hCop : Nat.Coprime (Nat.card ↥Abar) (Nat.card ↥Lbar) := by
    have hAbar_pg : IsPGroup p ↥Abar := by rw [hAbar_def]; exact hA_pg.map mk
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAbar_pg
    rw [hk]
    refine Nat.Coprime.pow_left k ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr ?_)
    intro hdvd
    have hLbar_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} Lbar := by
      rw [hLbar_def]; exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup
        (G := G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) {q | q ≠ p}
    exact (hLbar_pi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) rfl
  -- `hproper`: `Ā` acts trivially on every `Ā`-invariant proper `M̄ < L̄`.
  have hproper : ∀ M : Subgroup ↥Lbar, (∀ a : ↥Abar, ∀ n ∈ M, a • n ∈ M) → M ≠ ⊤ →
      ∀ a : ↥Abar, ∀ n ∈ M, a • n = n := by
    intro M hM_inv hM_ne_top a n hn
    -- Set `W = M.map L̄.subtype ≤ L̄`, proper, `Ā`-invariant; apply the focused lemma.
    set W : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := M.map Lbar.subtype
      with hW_def
    have hW_le : W ≤ Lbar := by rw [hW_def]; exact Subgroup.map_subtype_le M
    have hW_ne : W ≠ Lbar := by
      intro hWtop
      apply hM_ne_top
      apply Subgroup.map_injective Lbar.subtype_injective
      rw [← hW_def, hWtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hW_normalized : ∀ a : G, a ∈ A → ∀ w, w ∈ W → mk a * w * (mk a)⁻¹ ∈ W := by
      intro g hg w hw
      obtain ⟨⟨w, hwL⟩, hwM, rfl⟩ := hw
      have hg_Abar : mk g ∈ Abar := Subgroup.mem_map_of_mem mk hg
      have hmoved := hM_inv ⟨mk g, hg_Abar⟩ ⟨w, hwL⟩ hwM
      rw [hW_def]
      have hsmul := hsmul_coe ⟨mk g, hg_Abar⟩ ⟨w, hwL⟩
      exact ⟨_, hmoved, hsmul⟩
    have hcomm := step5_Abar_centralizes_invariant_proper P hp2 h_pSolvable h2abelian
      h_oPiPrime_trivial h_centralizer_center ih hA_mem h_P_eq_UA hW_le hW_ne hW_normalized
    -- `⁅W, Ā⁆ = ⊥` ⇒ `Ā` centralizes `W` ⇒ `a • n = n`.
    apply Subtype.ext
    rw [hsmul_coe a n]
    -- `ga` and `gn` commute since `⁅W, Ā⁆ = ⊥` and `gn ∈ W`, `ga ∈ Ā`.
    set ga : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G := a.1 with hga
    set gn : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G := n.1 with hgn
    have hn_W : gn ∈ W := ⟨n, hn, rfl⟩
    have hcomm_mem : ⁅gn, ga⁆ ∈ (⊥ :
        Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) := by
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator hn_W a.2
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at hcomm_mem
    -- `gn` and `ga` commute ⇒ `ga * gn * ga⁻¹ = gn`.
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm_mem.symm.eq
  -- Apply Lemma 6.20: `Ā` is cyclic.
  have hAbar_cyclic : IsCyclic ↥Abar :=
    OddOrder.Isaacs.Ch06.isCyclic_of_faithful_trivial_on_proper_invariant hCop hproper
  -- `Ā` is nontrivial, elementary abelian, cyclic `p`-group ⇒ `|Ā| = p`.
  haveI : Nontrivial ↥Abar := (Subgroup.nontrivial_iff_ne_bot _).mpr hAbar_ne_bot
  have hAbar_card : Nat.card ↥Abar = p :=
    card_eq_prime_of_isElementaryAbelian_isCyclic_nontrivial hAbar_el hAbar_cyclic
  -- Convert `Nat.card Ā = p` to `U.relIndex A = p` via `relIndex_map_map` + diamond.
  -- `U.relIndex A = |A : A ⊓ U| = |Ā| = p` (`Ā = A.map mk ≅ A / (A ⊓ U)`, `ker mk = U`).
  rw [← hAbar_card]
  -- `U.relIndex A = (U.subgroupOf A).index`; `U.subgroupOf A = ker (mk ∘ A.subtype)`.
  change (U.subgroupOf A).index = Nat.card ↥Abar
  have hker : U.subgroupOf A = (mk.comp A.subtype).ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      hmk_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hU_eq_oPi]
  rw [hker]
  -- `|A : ker φ| = |range φ| = |A.map mk| = |Ā|` for `φ = mk ∘ A.subtype`.
  have hrange : (mk.comp A.subtype).range = Abar := by
    rw [hAbar_def, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact Subgroup.index_ker (mk.comp A.subtype)

/-- **Isaacs Thm 7.6 Steps 4 + 5** (mmd L3870-3878).

Together Steps 4-5 produce `P = UA ∧ A.relIndex U = p` given:
* The full Thm 7.6 hypotheses (i)-(v) on the running `G`.
* An induction hypothesis: Thm 7.6 holds for all proper subgroups `H < G`.
* A chosen `A ∈ E(P)` with `A ⊄ U` (Step 2 extraction).

**Step 4** (`P = UA`) is proved here as actual theorem code, using the focused
Step 3 axiom (`step3_Abar_centralizes_inter_LBar`).  **Step 5** (`|Ā| = p`)
is delegated to the focused `step5_Abar_card_eq_p` axiom.

Step 3 is **internal to this axiom**: both Step 4 and Step 5 use Step 3 by
applying the IH to proper subgroups (`H = LA` for Step 4, `H = MA` for any
Ā-invariant proper `M̄ < L̄` for Step 5).

The "|A : A ⊓ U|" formulation (= `A.relIndex U`) is used because the landed
Step 7 lemma (`omega1ZCenterOpCore_relIndex_inter_A_le`) consumes it directly. -/
private theorem step4_5_normal_J_hypotheses.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    (ih : ∀ (H : Type u) [Group H] [Finite H]
      [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H],
      Nat.card H < Nat.card G →
      (∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥ →
      ∀ (Q : Sylow p H),
        Subgroup.centralizer
            (((Subgroup.center (Q : Subgroup H)).map
              (Q : Subgroup H).subtype) : Set H)
          = (Q : Subgroup H) →
        (Subgroup.thompsonJ (Q : Subgroup H) p).Normal)
    {A : Subgroup G}
    (hA_mem : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (hA_not_le : ¬ A ≤ OddOrder.Isaacs.Ch01.opCore p G) :
    OddOrder.Isaacs.Ch01.opCore p G ⊔ A = (P : Subgroup G) ∧
      (OddOrder.Isaacs.Ch01.opCore p G).relIndex A = p := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set L : Subgroup G := opPpPrimeCore G p with hL_def
  set mk : G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hmk_def
  -- `U = O_{{p}}(G)` (kernel of `mk`), and `U ≤ L`.
  have hU_eq_oPi : U = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  have hker_mk : mk.ker = U := by rw [hmk_def, QuotientGroup.ker_mk', hU_eq_oPi]
  have hU_le_L : U ≤ L := by
    rw [hU_eq_oPi, hL_def]; exact oPiCore_p_le_opPpPrimeCore
  -- Basic facts about `A` and `U`.
  have hA_le_P : A ≤ (P : Subgroup G) := hA_mem.1
  have hA_pg : IsPGroup p A := hA_mem.2.1.isPGroup
  have hU_le_P : U ≤ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P
  -- `UA = U ⊔ A`, `LA = L ⊔ A`.
  set UA : Subgroup G := U ⊔ A with hUA_def
  set LA : Subgroup G := L ⊔ A with hLA_def
  have hUA_le_P : UA ≤ (P : Subgroup G) := sup_le hU_le_P hA_le_P
  have hUA_le_LA : UA ≤ LA := sup_le_sup_right hU_le_L A
  have hUA_pg : IsPGroup p ↥UA :=
    P.isPGroup'.of_injective (Subgroup.inclusion hUA_le_P)
      (Subgroup.inclusion_injective hUA_le_P)
  -- `Ā = A.map mk`, `L̄ = L.map mk = O_{p'}(Ḡ)`.
  set Abar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := A.map mk
    with hAbar_def
  set Lbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := L.map mk
    with hLbar_def
  have hLbar_eq : Lbar = OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
    rw [hLbar_def, hL_def, hmk_def]; exact opPpPrimeCore_map_eq_LBar
  haveI : Lbar.Normal := by rw [hLbar_eq]; exact OddOrder.Isaacs.Ch03.oPiCore.normal _ _
  -- `Ā ⊓ L̄ = ⊥` (p-group vs p'-group) and `Ā ≠ ⊥`.
  have hAbar_inf_Lbar : Abar ⊓ Lbar = ⊥ := by
    rw [hAbar_def, hLbar_eq]; exact AbarInf_LBar_eq_bot hA_pg
  have hAbar_ne_bot : Abar ≠ ⊥ := by
    rw [hAbar_def, hmk_def]
    exact Abar_ne_bot_of_not_le (by rwa [hU_eq_oPi] at hA_not_le)
  -- Step 4: prove `LA = ⊤`, then `UA = P`.
  have hLA_top : LA = ⊤ := by
    by_contra hLA_ne_top
    -- Build the Sylow `p`-subgroup `UA.subgroupOf LA` of `↥LA`.
    have hUA_le_LA' : UA ≤ LA := hUA_le_LA
    have hL_le_LA : L ≤ LA := le_sup_left
    have hA_le_LA : A ≤ LA := le_sup_right
    -- `UA.subgroupOf LA` is a `p`-group.
    have hUAsub_pg : IsPGroup p ↥(UA.subgroupOf LA) := hUA_pg.comap_subtype
    -- Its index in `↥LA` is `UA.relIndex LA = Nat.card L̄`, a `p'`-number.
    have hidx_eq : (UA.subgroupOf LA).index = UA.relIndex LA := rfl
    -- `UA.relIndex LA = Nat.card Lbar` via `relIndex_map_map` + diamond.
    have hrelindex_map : (Abar).relIndex (Lbar ⊔ Abar) = UA.relIndex LA := by
      rw [hAbar_def, hLbar_def]
      rw [← Subgroup.map_sup]
      rw [Subgroup.relIndex_map_map mk A (L ⊔ A)]
      rw [hker_mk]
      -- `(A ⊔ U).relIndex ((L ⊔ A) ⊔ U) = UA.relIndex LA` since `U ≤ A⊔U`, `U ≤ LA`.
      congr 1
      · rw [hUA_def, sup_comm]
      · rw [hLA_def]; rw [sup_assoc, sup_comm A U, ← sup_assoc, sup_eq_left.mpr hU_le_L]
    have hAbar_relindex : (Abar).relIndex (Lbar ⊔ Abar) = Nat.card Lbar :=
      relIndex_sup_of_inf_eq_bot (by rw [inf_comm]; exact hAbar_inf_Lbar)
    have hUA_relindex_LA : UA.relIndex LA = Nat.card Lbar := by
      rw [← hrelindex_map, hAbar_relindex]
    -- `Nat.card Lbar` is a `p'`-number, so `p ∤ (UA.subgroupOf LA).index`.
    have hLbar_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} Lbar := by
      rw [hLbar_eq]; exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) {q | q ≠ p}
    have hp_not_dvd : ¬ p ∣ (UA.subgroupOf LA).index := by
      rw [hidx_eq, hUA_relindex_LA]
      intro hdvd
      exact (hLbar_pi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) rfl
    -- The Sylow subgroup `S`.
    let S : Sylow p ↥LA := hUAsub_pg.toSylow hp_not_dvd
    have hS_coe : (S : Subgroup ↥LA) = UA.subgroupOf LA := hUAsub_pg.toSylow_coe hp_not_dvd
    -- `S = (LA ⊓ P).subgroupOf LA`: both are `p`-subgroups, `S` Sylow, `S ≤ (LA⊓P)sub`.
    have hLAP_pg : IsPGroup p ↥((LA ⊓ (P : Subgroup G)).subgroupOf LA) := by
      have : IsPGroup p ↥(LA ⊓ (P : Subgroup G)) :=
        P.isPGroup'.of_injective (Subgroup.inclusion (inf_le_right))
          (Subgroup.inclusion_injective _)
      exact this.comap_subtype
    have hS_le_LAP : (S : Subgroup ↥LA) ≤ (LA ⊓ (P : Subgroup G)).subgroupOf LA := by
      rw [hS_coe]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨x.property, hUA_le_P hx⟩
    have hS_eq_LAP : ((LA ⊓ (P : Subgroup G)).subgroupOf LA) = (S : Subgroup ↥LA) :=
      S.is_maximal' hLAP_pg hS_le_LAP
    -- Apply Step 3 with `H = LA`: `⁅L ⊓ LA, A⁆ ≤ U`.
    have hUA_le_H : U ⊔ A ≤ LA := sup_le (hU_le_L.trans hL_le_LA) hA_le_LA
    have hStep3 : (⁅L ⊓ LA, A⁆ : Subgroup G) ≤ U :=
      step3_Abar_centralizes_inter_LBar P hp2 h_pSolvable h2abelian h_oPiPrime_trivial
        h_centralizer_center ih hA_mem hLA_ne_top hUA_le_H S hS_eq_LAP.symm
    -- `L ⊓ LA = L` (since `L ≤ LA`).
    have hL_inf_LA : L ⊓ LA = L := inf_eq_left.mpr hL_le_LA
    rw [hL_inf_LA] at hStep3
    -- `⁅L, A⁆ ≤ U = ker mk` ⇒ `⁅L̄, Ā⁆ = ⊥` ⇒ `Ā ≤ C_Ḡ(L̄)`.
    have hcomm_map : (⁅L, A⁆ : Subgroup G).map mk = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hker_mk]; exact hStep3
    have hAbar_le_cent : Abar ≤ Subgroup.centralizer (Lbar : Set _) := by
      rw [hAbar_def, hLbar_def, ← Subgroup.commutator_eq_bot_iff_le_centralizer,
        ← Subgroup.map_commutator]
      rw [Subgroup.commutator_comm]
      exact hcomm_map
    -- Step 1(c): `C_Ḡ(L̄) ≤ L̄`.
    have hcent_le_Lbar : Subgroup.centralizer (Lbar : Set _) ≤ Lbar := by
      rw [hLbar_eq]; exact step1_c_centralizer_oPiPrime_quotient_le_self
    -- So `Ā ≤ L̄`, hence `Ā = Ā ⊓ L̄ = ⊥`, contradiction.
    have hAbar_le_Lbar : Abar ≤ Lbar := hAbar_le_cent.trans hcent_le_Lbar
    have hAbar_bot : Abar = ⊥ := by
      rw [← inf_eq_left.mpr hAbar_le_Lbar]; exact hAbar_inf_Lbar
    exact hAbar_ne_bot hAbar_bot
  -- From `LA = ⊤`: `UA = LA ⊓ P = ⊤ ⊓ P = P`.  Use `UA = LA ⊓ P`.
  have hUA_eq_P : UA = (P : Subgroup G) := by
    -- We re-derive the Sylow identity at `H = LA = ⊤`: `UA.subgroupOf LA = (LA⊓P).subgroupOf LA`,
    -- then map back.  With `LA = ⊤`, `LA ⊓ P = P`.
    apply le_antisymm hUA_le_P
    -- `P ≤ UA`: since `LA = ⊤`, `P ≤ LA`, and `LA ⊓ P = P` is a `p`-subgroup of `↥LA`
    -- containing the Sylow `UA.subgroupOf LA`, forcing equality.
    have hP_le_LA : (P : Subgroup G) ≤ LA := by rw [hLA_top]; exact le_top
    have hUAsub_pg : IsPGroup p ↥(UA.subgroupOf LA) := hUA_pg.comap_subtype
    have hidx_eq : (UA.subgroupOf LA).index = UA.relIndex LA := rfl
    have hrelindex_map : (Abar).relIndex (Lbar ⊔ Abar) = UA.relIndex LA := by
      rw [hAbar_def, hLbar_def, ← Subgroup.map_sup, Subgroup.relIndex_map_map mk A (L ⊔ A),
        hker_mk]
      congr 1
      · rw [hUA_def, sup_comm]
      · rw [hLA_def, sup_assoc, sup_comm A U, ← sup_assoc, sup_eq_left.mpr hU_le_L]
    have hAbar_relindex : (Abar).relIndex (Lbar ⊔ Abar) = Nat.card Lbar :=
      relIndex_sup_of_inf_eq_bot (by rw [inf_comm]; exact hAbar_inf_Lbar)
    have hLbar_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} Lbar := by
      rw [hLbar_eq]; exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) {q | q ≠ p}
    have hp_not_dvd : ¬ p ∣ (UA.subgroupOf LA).index := by
      rw [hidx_eq, hrelindex_map.symm.trans hAbar_relindex]
      intro hdvd
      exact (hLbar_pi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) rfl
    let S : Sylow p ↥LA := hUAsub_pg.toSylow hp_not_dvd
    have hS_coe : (S : Subgroup ↥LA) = UA.subgroupOf LA := hUAsub_pg.toSylow_coe hp_not_dvd
    have hLAP_pg : IsPGroup p ↥((LA ⊓ (P : Subgroup G)).subgroupOf LA) := by
      have : IsPGroup p ↥(LA ⊓ (P : Subgroup G)) :=
        P.isPGroup'.of_injective (Subgroup.inclusion (inf_le_right))
          (Subgroup.inclusion_injective _)
      exact this.comap_subtype
    have hS_le_LAP : (S : Subgroup ↥LA) ≤ (LA ⊓ (P : Subgroup G)).subgroupOf LA := by
      rw [hS_coe]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨x.property, hUA_le_P hx⟩
    have hS_eq_LAP : ((LA ⊓ (P : Subgroup G)).subgroupOf LA) = (S : Subgroup ↥LA) :=
      S.is_maximal' hLAP_pg hS_le_LAP
    -- So `(LA⊓P).subgroupOf LA = UA.subgroupOf LA`, hence `LA ⊓ P = UA` (both ≤ LA).
    rw [hS_coe] at hS_eq_LAP
    have hLAP_eq_UA : LA ⊓ (P : Subgroup G) = UA := by
      have hmap := congrArg (fun K : Subgroup ↥LA => K.map LA.subtype) hS_eq_LAP
      simp only [Subgroup.subgroupOf, Subgroup.map_comap_eq, LA.range_subtype] at hmap
      rwa [inf_eq_right.mpr (inf_le_left), inf_eq_right.mpr hUA_le_LA] at hmap
    -- `P ≤ LA ⊓ P = UA`.
    intro x hxP
    rw [← hLAP_eq_UA]
    exact ⟨hP_le_LA hxP, hxP⟩
  refine ⟨hUA_eq_P, ?_⟩
  -- Step 5 (delegated): `U.relIndex A = p`.
  exact step5_Abar_card_eq_p P hp2 h_pSolvable h2abelian h_oPiPrime_trivial
    h_centralizer_center ih hA_mem hA_not_le hUA_eq_P

/-! ### Step 8 action setup: `Ḡ →* MulAut V` (mmd L3879)

The book's Step 8 builds the conjugation action `Ḡ ↷ V` and checks
faithfulness (Step 6).  Below we lift `MulAut.conjNormal : G →* MulAut V` to a
homomorphism `Ḡ →* MulAut V` via `QuotientGroup.lift`, using `U ≤ ker` (which
holds because `V ⊆ Z(U)`). -/

/-- `O_p(G) ≤ ker (MulAut.conjNormal : G →* MulAut V)`: every `u ∈ U`
centralizes `V = Ω₁ Z(U)` (since `V ⊆ Z(U)`). -/
private theorem opCore_le_ker_conjNormal_omega1ZCenterOpCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    OddOrder.Isaacs.Ch01.opCore p G ≤
      (MulAut.conjNormal (H := omega1ZCenterOpCore G p)).ker := by
  intro u hu_U
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro v
  -- Goal: (MulAut.conjNormal u) v = (1 : MulAut V) v = v
  apply Subtype.ext
  -- Goal: ↑((MulAut.conjNormal u) v) = ↑v
  rw [MulAut.conjNormal_apply]
  -- Goal: u * v * u⁻¹ = v
  have hv_cent : (v : G) ∈ Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) :=
    omega1ZCenterOpCore_centralizes_opCore v.property
  have hvu : (u : G) * (v : G) = (v : G) * (u : G) :=
    (Subgroup.mem_centralizer_iff.mp hv_cent) u hu_U
  -- Convert "(1 : MulAut V) v" on the RHS.
  change (u : G) * (v : G) * (u : G)⁻¹ = (v : G)
  calc (u : G) * (v : G) * (u : G)⁻¹
      = (v : G) * (u : G) * (u : G)⁻¹ := by rw [hvu]
    _ = (v : G) := by group

/-- **The factored action `Ḡ →* MulAut V`**: lifts `MulAut.conjNormal` via
`U ≤ ker`. -/
private noncomputable def conjActionOnOmega1ZCenter_quotient
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) →*
      MulAut ↥(omega1ZCenterOpCore G p) :=
  QuotientGroup.lift _ MulAut.conjNormal (by
    rw [show OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G =
        OddOrder.Isaacs.Ch01.opCore p G from
      OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p]
    exact opCore_le_ker_conjNormal_omega1ZCenterOpCore)

/-- The kernel of `MulAut.conjNormal : G →* MulAut V` (for a normal subgroup `V`)
is exactly `C_G(V)`: `g` acts trivially on `V` iff `g` centralizes `V`. -/
private theorem conjNormal_ker_eq_centralizer
    {G : Type*} [Group G] {V : Subgroup G} [V.Normal] :
    (MulAut.conjNormal (H := V)).ker = Subgroup.centralizer (V : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg v hv
    -- `conjNormal g = 1` ⇒ `g * v * g⁻¹ = v`, i.e. `g * v = v * g`.
    have hfix : (MulAut.conjNormal g (⟨v, hv⟩ : V) : G) = ((⟨v, hv⟩ : V) : G) := by
      rw [hg]; rfl
    rw [MulAut.conjNormal_apply] at hfix
    -- `g * v * g⁻¹ = v` ⇒ `g * v = v * g`.
    have : g * v * g⁻¹ * g = v * g := by rw [hfix]
    have hcomm : g * v = v * g := by simpa [mul_assoc] using this
    exact hcomm.symm
  · intro hg
    -- Every `v ∈ V` is fixed: `g * v * g⁻¹ = v`.
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    simp only [MulAut.one_apply]
    rw [MulAut.conjNormal_apply]
    have hcomm : (v : G) * g = g * (v : G) := hg (v : G) v.property
    -- `g * v * g⁻¹ = v * g * g⁻¹ = v`.
    rw [← hcomm]; group

/-- **Isaacs Thm 7.6 Step 8a** (local axiom — mmd L3893-3895): apply Thm 7.5.

Given Step 4-5-6-7 outputs:
* `P = UA` (Step 4)
* `|Ā| = p` (Step 5)
* The Ḡ-action on V is faithful (= Step 6, landed via
  `centralizer_omega1ZCenterOpCore_map_eq_bot_of_le_opCore`)
* `|V : V ∩ A| ≤ p` (Step 7, landed via `omega1ZCenterOpCore_relIndex_inter_A_le`)
plus the running Thm 7.6 hypotheses (i)-(v),

apply Thm 7.5 (`sylow_normal_of_elementary_normal_P_theorem`) to derive
`P̄ ⊴ Ḡ`. -/
private theorem step8a_PBar_normal_GBar
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (_h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (_h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (_h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {A : Subgroup G}
    (hA_mem : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (h_P_eq_UA : OddOrder.Isaacs.Ch01.opCore p G ⊔ A = (P : Subgroup G))
    (_h_Abar_card_eq_p :
       (OddOrder.Isaacs.Ch01.opCore p G).relIndex A = p)
    (h_V_inter_A_le_p : A.relIndex (omega1ZCenterOpCore G p) ≤ p)
    (h_K_map_eq_bot :
       (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)).map
         (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥) :
    ((P : Subgroup G).map
      (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))).Normal := by
  classical
  -- Abbreviations: `U = O_p(G) = O_{{p}}(G)`, `Ḡ = G/U`, `V = Ω₁(Z(U))`,
  -- `φ : Ḡ →* MulAut V` the lifted conjugation action.
  set U : Subgroup G := OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G with hU_def
  set mk : G →* G ⧸ U := QuotientGroup.mk' U with hmk_def
  set V : Subgroup G := omega1ZCenterOpCore G p with hV_def
  set φ : (G ⧸ U) →* MulAut ↥V := conjActionOnOmega1ZCenter_quotient G p with hφ_def
  -- `U = O_p(G)` definitionally.
  have hU_eq : U = OddOrder.Isaacs.Ch01.opCore p G :=
    OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p
  -- (Hypothesis 1) `Ḡ` is `p`-separable: instance from `quotient_isPiSeparable`.
  haveI : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) (G ⧸ U) := inferInstance
  -- (Hypothesis 3) Every `2`-subgroup of `Ḡ` is abelian, by `quotient_two_subgroup_abelian`.
  have h2abelian_bar :
      ∀ S : Subgroup (G ⧸ U), IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x :=
    fun S hS2 => quotient_two_subgroup_abelian h2abelian S hS2
  -- (Hypothesis 4) `φ` is faithful: `ker φ = C_G(V).map mk = ⊥`.
  have hφ_inj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    -- `ker φ = (conjNormal).ker.map mk = C_G(V).map mk`.
    have hker : φ.ker = (Subgroup.centralizer (V : Set G)).map mk := by
      rw [hφ_def, hmk_def]
      unfold conjActionOnOmega1ZCenter_quotient
      rw [QuotientGroup.ker_lift, conjNormal_ker_eq_centralizer]
    rw [hker]
    exact h_K_map_eq_bot
  -- (Hypothesis 5 ingredient) `V` is a `p`-group.
  have hV_pg : IsPGroup p ↥V := omega1ZCenterOpCore_isPGroup p
  -- The candidate normal Sylow `P̄ = P.map mk` as a `Sylow p Ḡ`.
  set PBar : Sylow p (G ⧸ U) := P.mapSurjective (QuotientGroup.mk'_surjective U) with hPBar_def
  have hPBar_coe : (PBar : Subgroup (G ⧸ U)) = (P : Subgroup G).map mk := by
    rw [hPBar_def, Sylow.coe_mapSurjective]
  -- `P̄ = Ā` since `Ū = ⊥` and `P = UA`.
  have hPBar_eq_Abar : (PBar : Subgroup (G ⧸ U)) = A.map mk := by
    rw [hPBar_coe, ← h_P_eq_UA, ← hU_eq, Subgroup.map_sup]
    -- `U.map mk = ⊥`.
    have hU_map : U.map mk = ⊥ := by
      rw [hmk_def, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hU_map, bot_sup_eq]
  -- `A` is abelian (it is elementary abelian).
  have hA_comm : ∀ a b : ↥A, a * b = b * a := (hA_mem.2.1).comm
  -- Key step: `(actionCentralizer φ P̄).index ≤ p`, because `E = V ∩ A` is fixed by `P̄ = Ā`.
  -- Membership: every `v : ↥V` whose underlying element lies in `A` is `P̄`-fixed.
  have hE_le_centralizer :
      (A.subgroupOf V) ≤ actionCentralizer φ (PBar : Subgroup (G ⧸ U)) := by
    intro v hv
    -- `hv : (v : G) ∈ A` (membership of the subgroupOf).
    rw [Subgroup.mem_subgroupOf] at hv
    rw [mem_actionCentralizer]
    intro q
    -- `q ∈ P̄ = Ā`, so `q = mk a` for some `a ∈ A`.
    have hq_mem : (q : G ⧸ U) ∈ A.map mk := hPBar_eq_Abar ▸ q.property
    obtain ⟨a, ha_A, ha_eq⟩ := hq_mem
    -- `φ q v = φ (mk a) v = conjNormal a v = a * v * a⁻¹ = v` (A abelian).
    apply Subtype.ext
    have hφq : φ (q : G ⧸ U) = MulAut.conjNormal a := by
      rw [hφ_def]
      unfold conjActionOnOmega1ZCenter_quotient
      rw [← ha_eq, hmk_def]
      exact QuotientGroup.lift_mk' _ _ a
    rw [hφq, MulAut.conjNormal_apply]
    -- `a * v * a⁻¹ = v` since `a, v ∈ A` and `A` is abelian.
    have hcomm : a * (v : G) = (v : G) * a :=
      congrArg Subtype.val (hA_comm ⟨a, ha_A⟩ ⟨(v : G), hv⟩)
    rw [hcomm]; group
  -- `(actionCentralizer φ P̄).index ≤ (A.subgroupOf V).index = A.relIndex V ≤ p`.
  have hPBar_index : (actionCentralizer φ (PBar : Subgroup (G ⧸ U))).index ≤ p := by
    have h1 : (actionCentralizer φ (PBar : Subgroup (G ⧸ U))).index ≤
        (A.subgroupOf V).index := Subgroup.index_antitone hE_le_centralizer
    calc (actionCentralizer φ (PBar : Subgroup (G ⧸ U))).index
        ≤ (A.subgroupOf V).index := h1
      _ = A.relIndex V := rfl
      _ ≤ p := h_V_inter_A_le_p
  -- Extend the bound to *every* Sylow of `Ḡ` via conjugacy.
  have h_centralizer_index :
      ∀ R : Sylow p (G ⧸ U), (actionCentralizer φ (R : Subgroup (G ⧸ U))).index ≤ p := by
    intro R
    -- `R` and `P̄` are conjugate: `R = ḡ • P̄`.
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G ⧸ U) PBar R
    have hR_eq : (R : Subgroup (G ⧸ U)) =
        (PBar : Subgroup (G ⧸ U)).map (MulAut.conj g).toMonoidHom := by
      rw [← hg]
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    rw [hR_eq, actionCentralizer_map_conj_index]
    exact hPBar_index
  -- Apply Theorem 7.5 to `φ : Ḡ →* MulAut V` and the Sylow `P̄`.
  have hPBar_normal : (PBar : Subgroup (G ⧸ U)).Normal :=
    sylow_normal_of_elementary_normal_P_theorem hp2 h2abelian_bar hφ_inj hV_pg
      h_centralizer_index PBar
  -- Transport normality to `(P : Subgroup G).map mk`.
  rwa [hPBar_coe] at hPBar_normal

/-- **Isaacs Thm 7.6 Step 8b** (mmd L3896): pull back `P̄ ⊴ Ḡ` to derive `False`.

Once `P̄ ⊴ Ḡ` is established (Step 8a), correspondence-theorem reasoning gives
`P ⊴ G` (since `U ≤ P`, the preimage of `P̄` is `P`).  Then `P.Normal` and
`IsPGroup p P` give `P ≤ opCore p G = U` via `normal_pgroup_le_opCore`.
Combined with `A ≤ P`, this contradicts `A ⊄ U`. -/
theorem step8b_pullback_normal_P
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {A : Subgroup G}
    (hA_le_P : A ≤ (P : Subgroup G))
    (hA_not_le : ¬ A ≤ OddOrder.Isaacs.Ch01.opCore p G)
    (hPBar_normal :
       ((P : Subgroup G).map
         (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))).Normal) :
    False := by
  -- (1) U ≤ P (general).
  have hU_le_P : OddOrder.Isaacs.Ch01.opCore p G ≤ (P : Subgroup G) :=
    OddOrder.Isaacs.Ch01.opCore_le P
  -- (2) U ≤ oPiCore_p (definitionally equal).
  have hU_eq : OddOrder.Isaacs.Ch01.opCore p G =
      OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  -- (3) (P.map mk').comap mk' = P (since U ≤ P, and U = kernel of mk').
  have hP_preimage :
      ((P : Subgroup G).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))).comap
          (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) =
        (P : Subgroup G) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    -- Goal: P ⊔ oPiCore {p} G = P. Use U ≤ P.
    rw [← hU_eq]
    exact sup_eq_left.mpr hU_le_P
  -- (4) P̄ ⊴ Ḡ ⇒ comap P̄ = P is normal in G.
  have hP_normal : (P : Subgroup G).Normal := by
    rw [← hP_preimage]
    exact hPBar_normal.comap (QuotientGroup.mk' _)
  -- (5) P is a normal p-group ⇒ P ≤ opCore p G = U.
  have hP_pg : IsPGroup p (P : Subgroup G) := P.isPGroup'
  haveI := hP_normal
  have hP_le_U : (P : Subgroup G) ≤ OddOrder.Isaacs.Ch01.opCore p G :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hP_pg
  -- (6) A ≤ P ≤ U contradicts hA_not_le.
  exact hA_not_le (hA_le_P.trans hP_le_U)

/-- **Isaacs Thm 7.6 Step 1-7 conclusion**: `J(P) ≤ O_p(G)`.

Proved by strong induction on `Nat.card G` (so Step 3 can use the IH on proper
subgroups) + Step 2 extraction (`thompsonJ_le_iff`) + the Step 4-5 axiom
(`step4_5_normal_J_hypotheses`) + the landed Step 6 (`...isPGroup` /
`...le_opCore_of_isPGroup` / `...map_eq_bot_of_le_opCore`) + the landed Step 7
(`omega1ZCenterOpCore_relIndex_inter_A_le`) + the Step 8 axiom
(`step8_normal_J_closure`). -/
theorem thompsonJ_le_opCore_of_normal_J_hypotheses
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G)) :
    Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G := by
  classical
  -- Strong induction on `Nat.card G`, with the motive parametrized over arbitrary
  -- groups whose order is less than `|G|` and which satisfy the descended hypotheses.
  let motive : ℕ → Prop := fun n =>
    ∀ (H : Type _) [Group H] [Finite H] [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H]
      (_h2abelian : ∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
      (_h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥)
      (Q : Sylow p H)
      (_h_centralizer_center :
         Subgroup.centralizer
           (((Subgroup.center (Q : Subgroup H)).map (Q : Subgroup H).subtype) : Set H)
           = (Q : Subgroup H)),
      Nat.card H = n → Subgroup.thompsonJ (Q : Subgroup H) p ≤ OddOrder.Isaacs.Ch01.opCore p H
  suffices hmain : motive (Nat.card G) by
    exact hmain G h2abelian h_oPiPrime_trivial P h_centralizer_center rfl
  refine Nat.strong_induction_on (Nat.card G) ?_
  intro n ih H _ _ _ h2abelian' h_oPiPrime_trivial' Q h_centralizer_center' hcard
  -- The induction hypothesis at the "normal_J" level (i.e., normality of J(Q')
  -- in H' for groups H' with order < n).
  have ih_normal :
      ∀ (H' : Type _) [Group H'] [Finite H']
        [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H'],
      Nat.card H' < Nat.card H →
      (∀ S : Subgroup H', IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H' = ⊥ →
      ∀ (Q' : Sylow p H'),
        Subgroup.centralizer
            (((Subgroup.center (Q' : Subgroup H')).map
              (Q' : Subgroup H').subtype) : Set H')
          = (Q' : Subgroup H') →
        (Subgroup.thompsonJ (Q' : Subgroup H') p).Normal := by
    intro H' _ _ _ hH'_lt h2abelian'' h_oPiPrime_trivial'' Q' h_centralizer_center''
    have hH'_lt_n : Nat.card H' < n := hH'_lt.trans_eq hcard
    have h_le_op' :=
      ih (Nat.card H') hH'_lt_n H' h2abelian'' h_oPiPrime_trivial'' Q' h_centralizer_center'' rfl
    exact normal_thompsonJ_of_le_opCore Q' h_le_op'
  -- Now prove `J(Q) ≤ U` on the running group `H` of order `n` using Step 2 extraction
  -- + the Steps 4-5 axiom + Step 6 (landed) + Step 7 (landed) + Step 8 closure axiom.
  haveI h_pSolvable_in_H : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H :=
    inferInstance
  rw [thompsonJ_le_iff]
  intro A hA_mem
  by_contra hA_not_le
  -- Package the induction hypothesis for use by the Step 4-5 axiom.
  have ih_for_axioms :
      ∀ (H' : Type _) [Group H'] [Finite H']
        [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H'],
      Nat.card H' < Nat.card H →
      (∀ S : Subgroup H', IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H' = ⊥ →
      ∀ (Q' : Sylow p H'),
        Subgroup.centralizer
            (((Subgroup.center (Q' : Subgroup H')).map
              (Q' : Subgroup H').subtype) : Set H')
          = (Q' : Subgroup H') →
        (Subgroup.thompsonJ (Q' : Subgroup H') p).Normal :=
    fun H' _ _ _ hH'_lt h2 h_oPi Q' h_cent =>
      ih_normal H' hH'_lt h2 h_oPi Q' h_cent
  -- (Step 4 + Step 5): `P = UA` and `A.relIndex U = p` (= `|Ā| = p`).
  obtain ⟨h_P_eq_UA, h_Abar_card_eq_p⟩ :=
    step4_5_normal_J_hypotheses (G := H) Q hp2 h_pSolvable_in_H h2abelian'
      h_oPiPrime_trivial' h_centralizer_center' ih_for_axioms hA_mem hA_not_le
  have hA_D_relIndex : (OddOrder.Isaacs.Ch01.opCore p H).relIndex A ≤ p :=
    le_of_eq h_Abar_card_eq_p
  -- (Step 7): `A.relIndex V ≤ p`, from the landed counting lemma.
  have hV_inter_A_le_p : A.relIndex (omega1ZCenterOpCore H p) ≤ p :=
    omega1ZCenterOpCore_relIndex_inter_A_le Q hA_mem hA_D_relIndex
  -- (Step 6): `K̄ = ⊥` from K = C_G(V) being a p-group (landed), hence K ≤ U.
  have h_K_pg : IsPGroup p (Subgroup.centralizer (omega1ZCenterOpCore H p : Set H)) :=
    centralizer_omega1ZCenterOpCore_isPGroup h_oPiPrime_trivial' Q h_centralizer_center'
  have h_K_le_U : Subgroup.centralizer (omega1ZCenterOpCore H p : Set H) ≤
      OddOrder.Isaacs.Ch01.opCore p H :=
    centralizer_omega1ZCenterOpCore_le_opCore_of_isPGroup h_K_pg
  have h_K_map_eq_bot :
      (Subgroup.centralizer (omega1ZCenterOpCore H p : Set H)).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) H)) = ⊥ :=
    centralizer_omega1ZCenterOpCore_map_eq_bot_of_le_opCore h_K_le_U
  -- (Step 8a): apply Thm 7.5 to get P̄ ⊴ Ḡ.
  have hPBar_normal :
      ((Q : Subgroup H).map (QuotientGroup.mk'
        (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) H))).Normal :=
    step8a_PBar_normal_GBar (G := H) Q hp2 h_pSolvable_in_H h2abelian'
      h_oPiPrime_trivial' h_centralizer_center' hA_mem h_P_eq_UA h_Abar_card_eq_p
      hV_inter_A_le_p h_K_map_eq_bot
  -- (Step 8b): pull back P̄ ⊴ Ḡ to derive `False` from `A ⊆ P ⊆ U`.
  exact step8b_pullback_normal_P Q hA_mem.1 hA_not_le hPBar_normal

/-- **Isaacs Thm 7.6** (normal-J theorem, unconditional).

The full theorem (Isaacs L3832) states:

> Suppose `G` is `p`-solvable with `p ≠ 2`, Sylow `2`-subgroups of `G` are abelian,
> `O_{p'}(G) = 1`, and `P = C_G(Z(P))` for some `P ∈ Syl_p(G)`.  Then `J(P) ⊴ G`.

The textbook proof (Isaacs p.209-214) is an **8-step Goldschmidt-style argument**:
Steps 1-7 establish `J(P) ≤ O_p(G)` using Thm 7.5 (normal-P), Ch.4 Cor 4.35
(`actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`), Ch.6 Thm 6.20
(`isCyclic_of_faithful_trivial_on_proper_invariant`), and Hall-Higman 3.21.
Step 8 propagates normality from `O_p(G)` to `G` via Thm 7.2
(`thompsonJ_eq_of_le_of_le`) + characteristic-of-characteristic transport.

Remaining local axioms: `step4_5_normal_J_hypotheses` (Step 4+5 = `P = UA` and
`|Ā| = p`, both using Step 3's IH internally) and `step8_normal_J_closure`
(Step 8 = Thm 7.5 application + pullback).  All earlier landed bridge lemmas
(Steps 1, 6, 7) are unconditional. -/
theorem normal_J
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G)) :
    (Subgroup.thompsonJ (P : Subgroup G) p).Normal := by
  have h_le : Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G :=
    thompsonJ_le_opCore_of_normal_J_hypotheses P hp2 h_pSolvable h2abelian
      h_oPiPrime_trivial h_centralizer_center
  exact normal_thompsonJ_of_le_opCore P h_le

end -- 7B

/-! ## §7C: Thompson normal p-complement proof + N/C `p'`-quotient (pp. 215-219) -/

section /- 7C: 7.1 proof + 7.7 -/

open scoped commutatorElement

/-- centralizer ⊆ normalizer (mathlib v4.29.1 に直接の lemma 無し). -/
private theorem centralizer_le_normalizer {G : Type*} [Group G] (H : Subgroup G) :
    Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer H := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hcomm : ∀ z ∈ H, z * x = x * z := Subgroup.mem_centralizer_iff.mp hx
  have hx_inv_mem : x⁻¹ ∈ Subgroup.centralizer (H : Set G) :=
    Subgroup.inv_mem _ hx
  have hcomm_inv : ∀ z ∈ H, z * x⁻¹ = x⁻¹ * z :=
    Subgroup.mem_centralizer_iff.mp hx_inv_mem
  refine ⟨fun hy => ?_, fun hxyx => ?_⟩
  · -- y ∈ H ⇒ xyx⁻¹ = y ∈ H
    have hxy : x * y = y * x := (hcomm y hy).symm
    have : x * y * x⁻¹ = y := by rw [hxy]; group
    rw [this]; exact hy
  · -- xyx⁻¹ ∈ H ⇒ y = xyx⁻¹ ∈ H
    have hcomm_z : (x * y * x⁻¹) * x⁻¹ = x⁻¹ * (x * y * x⁻¹) :=
      hcomm_inv (x * y * x⁻¹) hxyx
    -- 計算: (xyx⁻¹) * x⁻¹ = x⁻¹*(xyx⁻¹) ⇒ y = xyx⁻¹
    have h_eq : y * x⁻¹ = (x * y * x⁻¹) * x⁻¹ := by
      rw [hcomm_z]; group
    have hy_eq : y = x * y * x⁻¹ := mul_right_cancel h_eq
    rw [hy_eq]; exact hxyx

/-- **Isaacs Lem 7.7 (a)** (image of normalizer under p'-quotient).

`N ⊴ G` で `p ∤ |N|`, `P` が `G` の非自明 `p`-部分群とすると, `f := mk' N` について
`N_Ḡ(P̄) = (N_G(P)).map f`.

This is exactly Isaacs Lemma 2.17 in the quotient form needed in Ch.7. -/
theorem normalizer_map_of_coprime_kernel [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ}
    [Fact p.Prime] (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_neBot : P ≠ ⊥) (hP_pgroup : IsPGroup p P) :
    Subgroup.normalizer
        ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (Subgroup.normalizer P).map (QuotientGroup.mk' N) :=
  OddOrder.Isaacs.Ch02.normalizer_map_of_coprime_kernel
    hp_coprime hP_neBot hP_pgroup

/-- **Isaacs Lem 7.7 (b)** (image of centralizer under p'-quotient).

`N ⊴ G` で `p ∤ |N|`, `P` が `G` の非自明 `p`-部分群とすると, `f := mk' N` について
`C_Ḡ(P̄) = (C_G(P)).map f`.

書籍 p.215-216 の証明 (Lem 2.17 の "short extension"):
1. ⊇ は明らか (image of centralizer ⊆ centralizer of image).
2. ⊆: Lem 2.17 (a) で `N̄(P̄) = (N_G(P)).map f`. `Cbar ≤ Nbar` (centralizer ≤ normalizer).
   correspondence: `X := N_G(P) ⊓ Cbar.comap f` とおく ⇒ `X.map f = Cbar`.
   `⁅P, X⁆.map f = ⁅Pbar, Cbar⁆ = ⊥` ⇒ `⁅P, X⁆ ≤ ker f = N`. かつ `⁅P, X⁆ ≤ P`
   (X ≤ N_G(P) なので). 従って `⁅P, X⁆ ≤ P ⊓ N = ⊥` (coprime), 即ち `X ≤ C_G(P)`. -/
theorem centralizer_map_of_coprime_kernel [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ}
    [Fact p.Prime] (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_neBot : P ≠ ⊥) (hP_pgroup : IsPGroup p P) :
    Subgroup.centralizer ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (Subgroup.centralizer (P : Set G)).map (QuotientGroup.mk' N) := by
  classical
  set f : G →* G ⧸ N := QuotientGroup.mk' N with hf_def
  set Pbar : Subgroup (G ⧸ N) := P.map f with hPbar_def
  set Cbar : Subgroup (G ⧸ N) := Subgroup.centralizer (Pbar : Set (G ⧸ N)) with hCbar_def
  -- Coprime: P ⊓ N = ⊥
  obtain ⟨k, hP_card⟩ : ∃ k, Nat.card ↥P = p ^ k := IsPGroup.iff_card.mp hP_pgroup
  have hp_prime : p.Prime := Fact.out
  have h_coprime_PN : Nat.Coprime (Nat.card ↥P) (Nat.card ↥N) := by
    rw [hP_card]
    exact Nat.Coprime.pow_left _ (hp_prime.coprime_iff_not_dvd.mpr hp_coprime)
  have hP_inf_N : P ⊓ N = ⊥ := Subgroup.inf_eq_bot_of_coprime h_coprime_PN
  -- ker f = N
  have hf_ker : f.ker = N := QuotientGroup.ker_mk' N
  refine le_antisymm ?_ ?_
  · -- ⊆ direction (hard)
    -- Cbar ≤ Nbar
    have hCbar_le_Nbar : Cbar ≤ Subgroup.normalizer Pbar := centralizer_le_normalizer Pbar
    -- Nbar = (N_G(P)).map f by Lem 2.17 (a)
    have hN_eq : Subgroup.normalizer Pbar = (Subgroup.normalizer P).map f := by
      rw [hPbar_def, hf_def]
      exact OddOrder.Isaacs.Ch02.normalizer_map_of_coprime_kernel hp_coprime hP_neBot hP_pgroup
    -- X := N_G(P) ⊓ (Cbar.comap f).  X.map f = Cbar (correspondence).
    set X : Subgroup G := Subgroup.normalizer P ⊓ Cbar.comap f with hX_def
    have hX_map_eq : X.map f = Cbar := by
      apply le_antisymm
      · rintro _ ⟨y, ⟨_hy_N, hy_C⟩, rfl⟩
        exact (Subgroup.mem_comap.mp hy_C : f y ∈ Cbar)
      · intro c hc
        have hc_Nbar : c ∈ Subgroup.normalizer Pbar := hCbar_le_Nbar hc
        rw [hN_eq] at hc_Nbar
        obtain ⟨n, hn_NgP, hn_eq⟩ := hc_Nbar
        refine ⟨n, ⟨hn_NgP, ?_⟩, hn_eq⟩
        show f n ∈ Cbar
        rw [hn_eq]
        exact hc
    -- Claim: X ≤ centralizer P
    have hX_le_C : X ≤ Subgroup.centralizer (P : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      -- ⁅X, P⁆ = ⊥: ⊆ N (commutator maps to ⊥) and ⊆ P (X ≤ N_G(P)), so ⊆ P ⊓ N = ⊥.
      have h_map_bot : (⁅X, P⁆ : Subgroup G).map f = ⊥ := by
        rw [Subgroup.map_commutator, hX_map_eq]
        -- goal: ⁅Cbar, Pbar⁆ = ⊥
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl
      have h_comm_le_N : (⁅X, P⁆ : Subgroup G) ≤ N := by
        rw [← hf_ker]
        exact (Subgroup.map_eq_bot_iff _).mp h_map_bot
      have h_comm_le_P : (⁅X, P⁆ : Subgroup G) ≤ P := by
        rw [Subgroup.commutator_le]
        intro x hx_X p hp_P
        -- x ∈ X ≤ N_G(P), so x p x⁻¹ ∈ P. Then ⁅x, p⁆ = x p x⁻¹ p⁻¹ ∈ P.
        have hx_N : x ∈ Subgroup.normalizer P := hx_X.1
        have hxpx : x * p * x⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp hx_N p).mp hp_P
        change x * p * x⁻¹ * p⁻¹ ∈ P
        exact P.mul_mem hxpx (P.inv_mem hp_P)
      -- ⁅X, P⁆ ≤ P ⊓ N = ⊥
      have h_comm_le_bot : (⁅X, P⁆ : Subgroup G) ≤ ⊥ := by
        have h_inf : (⁅X, P⁆ : Subgroup G) ≤ P ⊓ N := le_inf h_comm_le_P h_comm_le_N
        rw [hP_inf_N] at h_inf
        exact h_inf
      exact le_bot_iff.mp h_comm_le_bot
    -- Cbar = X.map f ⊆ (centralizer P).map f
    rw [← hX_map_eq]
    exact Subgroup.map_mono hX_le_C
  · -- ⊇ direction (easy): (C_G(P)).map f ≤ Cbar
    rintro - ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro - ⟨p, hp, rfl⟩
    -- c centralizes p in G ⇒ f(c) centralizes f(p)
    have hcp : c * p = p * c := (Subgroup.mem_centralizer_iff.mp hc p hp).symm
    rw [← map_mul, ← map_mul]
    exact congrArg f hcp.symm

/-- **Isaacs Lem 7.7** (N/C theorem for p'-quotients).

If `N ⊴ G` is a normal `p'`-subgroup and `P` is a nontrivial `p`-subgroup, then the
normalizer and centralizer of `P` commute with passage to `G/N`. -/
theorem normalizer_and_centralizer_map_of_coprime_kernel [Finite G]
    {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_neBot : P ≠ ⊥) (hP_pgroup : IsPGroup p P) :
    (Subgroup.normalizer
        ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (Subgroup.normalizer P).map (QuotientGroup.mk' N)) ∧
    (Subgroup.centralizer
        ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (Subgroup.centralizer (P : Set G)).map (QuotientGroup.mk' N)) :=
  ⟨normalizer_map_of_coprime_kernel hp_coprime hP_neBot hP_pgroup,
    centralizer_map_of_coprime_kernel hp_coprime hP_neBot hP_pgroup⟩

/-- Transport `OddOrder.Isaacs.Ch05.HasNormalPComplement` across a `MulEquiv`.

If `e : G ≃* H` and `G` has a normal `p`-complement, so does `H`. The complement is the
image of `G`'s complement under `e`. -/
private theorem hasNormalPComplement_of_mulEquiv
    {G' H : Type*} [Group G'] [Group H]
    [Finite G'] [Finite H] {p : ℕ} [Fact p.Prime] (e : G' ≃* H)
    (hG : OddOrder.Isaacs.Ch05.HasNormalPComplement p G') :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p H := by
  classical
  obtain ⟨N, hN_normal, hN_compl⟩ := hG
  refine ⟨N.map e.toMonoidHom, ?_, ?_⟩
  · -- `N.map e` is normal in `H` because `e` is surjective.
    exact Subgroup.Normal.map hN_normal _ e.surjective
  · intro Q
    -- Pull `Q` back to a Sylow `p`-subgroup of `G'` via `e`.
    have h_range_top : (e.toMonoidHom).range = ⊤ :=
      MonoidHom.range_eq_top.mpr e.surjective
    have hQ_le_range : (Q : Subgroup H) ≤ (e.toMonoidHom).range := by
      rw [h_range_top]; exact le_top
    let Q' : Sylow p G' := Q.comapOfInjective e.toMonoidHom e.injective hQ_le_range
    have hQ'_compl : Subgroup.IsComplement' N (Q' : Subgroup G') := hN_compl Q'
    -- The image of Q' under e equals Q.
    have hQ'_eq : (Q' : Subgroup G') = (Q : Subgroup H).comap e.toMonoidHom := by
      simp [Q', Sylow.coe_comapOfInjective]
    have hQ_map : (Q' : Subgroup G').map e.toMonoidHom = (Q : Subgroup H) := by
      rw [hQ'_eq, Subgroup.map_comap_eq, h_range_top, top_inf_eq]
    -- |G'| = |H|, |N.map e| = |N|, |Q| = |Q'|.
    have hG_card : Nat.card G' = Nat.card H := Nat.card_congr e.toEquiv
    have hN_card : Nat.card (N.map e.toMonoidHom : Subgroup H) = Nat.card N := by
      exact
        (Nat.card_congr
          (Subgroup.equivMapOfInjective N e.toMonoidHom e.injective).toEquiv).symm
    have hQ_card : Nat.card (Q : Subgroup H) = Nat.card (Q' : Subgroup G') := by
      rw [← hQ_map]
      exact
        (Nat.card_congr
          (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv).symm
    -- Multiplicativity: |N.map e| * |Q| = |H|.
    have h_card_eq :
        Nat.card N * Nat.card (Q' : Subgroup G') = Nat.card G' :=
      hQ'_compl.card_mul_card
    have h_card_H :
        Nat.card (N.map e.toMonoidHom : Subgroup H) * Nat.card (Q : Subgroup H) =
          Nat.card H := by
      rw [hN_card, hQ_card, h_card_eq, hG_card]
    -- Coprimality: |N| coprime to p (from complement in G' with p-Sylow Q').
    have hp_ndvd_N : ¬ p ∣ Nat.card N := by
      rw [← hQ'_compl.index_eq_card]; exact Q'.not_dvd_index
    obtain ⟨k, hQ'_pow⟩ := IsPGroup.iff_card.mp Q'.isPGroup'
    have hp_prime : p.Prime := Fact.out
    have h_coprime' : Nat.Coprime (Nat.card N) (Nat.card (Q' : Subgroup G')) := by
      rw [hQ'_pow]
      exact ((hp_prime.coprime_iff_not_dvd.mpr hp_ndvd_N).symm).pow_right k
    have h_coprime :
        Nat.Coprime (Nat.card (N.map e.toMonoidHom : Subgroup H))
          (Nat.card (Q : Subgroup H)) := by
      rw [hN_card, hQ_card]; exact h_coprime'
    exact Subgroup.isComplement'_of_coprime h_card_H h_coprime

/-- **Isaacs Thm 7.1** (Thompson normal `p`-complement theorem, conditional on Thm 7.6).

The full theorem (Isaacs L3721, proved L3913 — §7C) states:

> Let `p ≠ 2`, `P ∈ Syl_p(G)`. If `C_G(Z(P))` and `N_G(J(P))` both have normal
> `p`-complements, then `G` has a normal `p`-complement.

The textbook proof (Isaacs p.215-217) proceeds by a 7-step minimum-counterexample
argument that establishes the five hypotheses of the **normal-J theorem (Thm 7.6)** for
`G`, then concludes `J(P) ⊴ G`, and finally observes `G = N_G(J(P))` has a normal
`p`-complement.

**This formalization takes `J(P) ⊴ G` as a forward-dependency hypothesis**
(`hJ_normal`), which is precisely the conclusion of normal-J 7.6 applied to the
minimal counterexample. The Steps 1-6 establishing the normal-J hypotheses (`O_{p'}(G)
= 1`, `P = C_G(Z(P))`, abelian Sylow-2, p-solvability, ...) require Thm 7.5 +
Hall-Higman + Lem 7.7 + Frobenius 5.26 and will be back-filled when §7B normal-J
lands (see `notes/isaacs/ch07_thompson.md`).

Given the J(P)-normality hypothesis, the conclusion is immediate: `J(P) ⊴ G` ⇒
`N_G(J(P)) = ⊤` ⇒ `↥(N_G(J(P))) ≃* G` ⇒ `HasNormalPComplement` transports from
`N_G(J(P))` to `G`. -/
theorem thompson_normal_p_complement
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hNJP : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer
          ((Subgroup.thompsonJ (P : Subgroup G) p : Subgroup G) : Set G)))
    (hJ_normal : (Subgroup.thompsonJ (P : Subgroup G) p).Normal) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  classical
  -- J(P) ⊴ G implies N_G(J(P)) = ⊤.
  have h_norm_top :
      Subgroup.normalizer
        ((Subgroup.thompsonJ (P : Subgroup G) p : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hJ_normal
  set NG : Subgroup G :=
    Subgroup.normalizer
      ((Subgroup.thompsonJ (P : Subgroup G) p : Subgroup G) : Set G) with hNG_def
  -- Compose ↥NG ≃* ↥⊤ ≃* G.
  let eqEquiv : NG ≃* (⊤ : Subgroup G) := MulEquiv.subgroupCongr h_norm_top
  let topToG : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  let e : ↥NG ≃* G := eqEquiv.trans topToG
  exact hasNormalPComplement_of_mulEquiv e hNJP

end -- 7C

/-! ## §7D: Burnside `p^a q^b` (pp. 219-222) -/

section /- 7D: Burnside p^a q^b -/

/-! ### Thm 7.8 — Burnside `p^a q^b` ⇒ solvable (conditional on 9-step argument)

**Isaacs Thm 7.8** (mmd L3955):

> `|G| = p^a q^b` ⇒ G solvable.

**character 不使用** (Goldschmidt + Bender + Matsuyama, 9 Step proof).

**先行 dep**: Thm 7.6 normal-J + Ch.2 Thm **2.13 Baer** ✅ + Ch.4 Thm **4.33** (p-local).

BG/Peterfalvi 直接被引用無いので最後着手. Phase 1 完成度のため必須 (BG L2633 で
"we can obtain Burnside's `p^a q^b` very easily now" として言及). -/

/-! ### §7D scaffolding — `IsPCentral`, `IsPType`, helper lemmas

We formalize the supporting machinery of Isaacs' §7D proof.  These definitions
are local to §7D (Burnside `p^a q^b`); the term "p-central element" appears
informally in the textbook on p.220 and does not have a mathlib analog. -/

/-- **Isaacs p.220** (definition of *p-central element*).

`x` is `p`-central if it is a nonidentity element of the center of some Sylow
`p`-subgroup of `G`.  Used in §7D Steps 4-9.

The condition is phrased via `(Subgroup.center P).map P.subtype` so that the
membership predicate lives in the ambient group `G`. -/
def IsPCentral (p : ℕ) {G : Type*} [Group G] (x : G) : Prop :=
  x ≠ 1 ∧ ∃ P : Sylow p G,
    x ∈ (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype

/-- **Isaacs p.219** (definition of *p-type maximal subgroup*).

A maximal subgroup `M` of `G` is `p`-type if `O_p(M) ≠ ⊥` (where `O_p(M)`
denotes the largest normal `p`-subgroup of `M` as a group in its own right).
In Isaacs §7D this notion partitions the maximal subgroups of a simple group
of order `p^a q^b` into two flavors. -/
def IsPType (p : ℕ) {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  IsCoatom M ∧ OddOrder.Isaacs.Ch01.opCore p ↥M ≠ ⊥

/-- Dual of `IsPType` with roles of `p` and `q` swapped (just a convenience
re-export of `IsPType q`). -/
abbrev IsQType (q : ℕ) {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  IsPType q M

/-- A group whose order is a `{p, q}`-number: `|G| = p^a * q^b`. -/
def IsPaQbOrder (p q : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ a b : ℕ, Nat.card G = p ^ a * q ^ b

/-- A `p`-central element is nonidentity. -/
theorem IsPCentral.ne_one {G : Type*} [Group G] {p : ℕ} {x : G}
    (hx : IsPCentral p x) : x ≠ 1 := hx.1

/-- A `p`-central element lies in the center of some Sylow `p`-subgroup. -/
theorem IsPCentral.mem_center {G : Type*} [Group G] {p : ℕ} {x : G}
    (hx : IsPCentral p x) :
    ∃ P : Sylow p G,
      x ∈ (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype :=
  hx.2

/-- A `p`-central element of `G` lies in the chosen Sylow `p`-subgroup `P`. -/
theorem IsPCentral.mem_sylow {G : Type*} [Group G] {p : ℕ} {x : G}
    (hx : IsPCentral p x) :
    ∃ P : Sylow p G, x ∈ (P : Subgroup G) := by
  obtain ⟨P, hP_mem⟩ := hx.2
  refine ⟨P, ?_⟩
  obtain ⟨⟨y, hy⟩, _, rfl⟩ := hP_mem
  exact hy

-- Note: `IsPCentral.conj` (conjugation preserves p-central) would be a
-- natural lemma but its proof requires careful threading of Sylow
-- conjugation (`Sylow.coe_subgroup_smul`) which is somewhat involved.
-- Deferred until needed in Step 4.

/-- **Step 1 reduction** — turn the `hMinCounterexample` data into the
statement "`H` is simple".

`hMinCounterexample` says that every proper normal subgroup of `H` is solvable
and every proper quotient is solvable.  Combined with the existence theorem for
solvable extensions (`solvable_of_ker_le_range`), this forces `H` to have no
nontrivial proper normal subgroup, i.e., `H` is simple. -/
theorem isSimpleGroup_of_minCounterexample
    {H : Type*} [Group H] [Nontrivial H]
    (hH_nsol : ¬ IsSolvable H)
    (hN_solvable : ∀ N : Subgroup H, N ≠ ⊤ → N.Normal → IsSolvable N)
    (hQ_solvable : ∀ (N : Subgroup H) [N.Normal], N ≠ ⊥ → IsSolvable (H ⧸ N)) :
    IsSimpleGroup H := by
  refine ⟨fun N hN_norm => ?_⟩
  by_contra h_not_bot_top
  push Not at h_not_bot_top
  obtain ⟨h_ne_bot, h_ne_top⟩ := h_not_bot_top
  -- N solvable as subgroup
  have hN_sol : IsSolvable N := hN_solvable N h_ne_top hN_norm
  -- H/N solvable as quotient
  have hQ_sol : IsSolvable (H ⧸ N) := hQ_solvable N h_ne_bot
  -- Build H solvable from extension: N → H → H/N
  have hH_sol : IsSolvable H := by
    -- Use f = N.subtype, g = mk' N.  ker g = N = range f.
    refine solvable_of_ker_le_range (N.subtype) (QuotientGroup.mk' N) ?_
    rw [QuotientGroup.ker_mk']
    exact N.range_subtype.ge
  exact hH_nsol hH_sol

/-- Helper: the order of a finite nontrivial subgroup is positive. -/
private theorem Nat.card_pos_of_finite {H : Type*} [Group H] [Finite H] :
    0 < Nat.card H := Nat.card_pos

/-- **Isaacs §7D Step "preliminary"**: a finite nonsolvable group is not a
`p`-group.

If `H` were a `p`-group it would be nilpotent (mathlib `IsPGroup.isNilpotent`)
hence solvable, contradicting non-solvability. -/
private theorem not_isPGroup_of_nonsolvable {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hH_nsol : ¬ IsSolvable H) :
    ¬ IsPGroup p H := by
  intro h_pgroup
  haveI : Group.IsNilpotent H := h_pgroup.isNilpotent
  exact hH_nsol inferInstance

/-- **§7D helper**: in a finite simple non-solvable group, the `r`-core is
trivial for every prime `r`.

In a simple group, the normal subgroup `O_r(G)` is either `⊥` or `⊤`.  If it
were `⊤` then `G` would be an `r`-group, hence nilpotent and solvable,
contradicting non-solvability. -/
theorem opCore_eq_bot_of_simple_nonsolvable
    {H : Type*} [Group H] [Finite H] {r : ℕ} [Fact r.Prime]
    (_hH_simple : IsSimpleGroup H) (hH_nsol : ¬ IsSolvable H) :
    OddOrder.Isaacs.Ch01.opCore r H = ⊥ := by
  haveI := OddOrder.Isaacs.Ch01.opCore.normal r H
  rcases Subgroup.Normal.eq_bot_or_eq_top
    (OddOrder.Isaacs.Ch01.opCore.normal r H) with h | h
  · exact h
  · exfalso
    -- opCore r H = ⊤ ⇒ H is an r-group ⇒ solvable, contradiction.
    have h_top_pgroup : IsPGroup r ↥(OddOrder.Isaacs.Ch01.opCore r H) :=
      OddOrder.Isaacs.Ch01.opCore_isPGroup r H
    -- Top equivalence: ⊤ subgroup of H is equivalent to H itself.
    have h_iso : OddOrder.Isaacs.Ch01.opCore r H ≃* H := by
      have hEq : OddOrder.Isaacs.Ch01.opCore r H = ⊤ := h
      exact (MulEquiv.subgroupCongr hEq).trans Subgroup.topEquiv
    have hH_pgroup : IsPGroup r H := h_top_pgroup.of_equiv h_iso
    exact not_isPGroup_of_nonsolvable hH_nsol hH_pgroup

/-- **§7D helper**: in a finite simple non-solvable group, the order is
divisible by at least 2 distinct primes.

This is immediate from `not_isPGroup_of_nonsolvable`: if only one prime
divided `|H|`, then `|H| = r^n` (by unique factorization), so `H` is an
`r`-group by `IsPGroup.of_card`, hence solvable. -/
theorem two_primes_dvd_of_simple_nonsolvable
    {H : Type*} [Group H] [Finite H]
    (_hH_simple : IsSimpleGroup H) (hH_nsol : ¬ IsSolvable H) :
    ∃ r₁ r₂ : ℕ, r₁.Prime ∧ r₂.Prime ∧ r₁ ≠ r₂ ∧
      r₁ ∣ Nat.card H ∧ r₂ ∣ Nat.card H := by
  classical
  by_contra h_not_two
  push Not at h_not_two
  haveI : Nontrivial H := (inferInstance : IsSimpleGroup H).toNontrivial
  have hH_card_gt : 1 < Nat.card H := Finite.one_lt_card
  -- Pick any prime divisor.
  obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hH_card_gt.ne'
  haveI : Fact r.Prime := ⟨hr_prime⟩
  -- Every prime divisor equals r.
  have hr_only : ∀ s ∈ Nat.primeFactorsList (Nat.card H), s = r := by
    intro s hs
    obtain ⟨hs_prime, hs_dvd⟩ := (Nat.mem_primeFactorsList Nat.card_pos.ne').mp hs
    by_contra hsr
    exact h_not_two r s hr_prime hs_prime (Ne.symm hsr) hr_dvd hs_dvd
  -- Then |H| = r^|primeFactorsList H| via IsPGroup.iff_card mpr argument.
  have h_eq : Nat.card H = r ^ (Nat.card H).primeFactorsList.length := by
    have hH_ne : Nat.card H ≠ 0 := Nat.card_pos.ne'
    rw [← List.prod_replicate, ← List.eq_replicate_of_mem hr_only,
        Nat.prod_primeFactorsList hH_ne]
  have hH_pgroup : IsPGroup r H := IsPGroup.of_card h_eq
  exact not_isPGroup_of_nonsolvable hH_nsol hH_pgroup

/-- **§7D helper** (specialization): a simple non-solvable group of order
dividing `p^a * q^b` (with `p ≠ q` prime) has its order divisible by both
`p` and `q`. -/
theorem p_and_q_dvd_card_of_simple_nonsolvable
    {H : Type*} [Group H] [Finite H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (_hpq : p ≠ q)
    (hH_simple : IsSimpleGroup H) (hH_nsol : ¬ IsSolvable H)
    {a b : ℕ} (hH_dvd : Nat.card H ∣ p ^ a * q ^ b) :
    p ∣ Nat.card H ∧ q ∣ Nat.card H := by
  obtain ⟨r₁, r₂, hr₁_prime, hr₂_prime, hr_ne, hr₁_dvd, hr₂_dvd⟩ :=
    two_primes_dvd_of_simple_nonsolvable hH_simple hH_nsol
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  -- Each rᵢ divides p^a * q^b, so by Nat.Prime.dvd_mul rᵢ ∈ {p, q}.
  have hr_in : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = p ∨ r = q := by
    intro r hr_prime hr_dvd_H
    have hr_dvd : r ∣ p ^ a * q ^ b := hr_dvd_H.trans hH_dvd
    rcases (Nat.Prime.dvd_mul hr_prime).mp hr_dvd with hp_branch | hq_branch
    · left
      exact (Nat.prime_dvd_prime_iff_eq hr_prime hp_prime).mp
        (hr_prime.dvd_of_dvd_pow hp_branch)
    · right
      exact (Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp
        (hr_prime.dvd_of_dvd_pow hq_branch)
  -- We have r₁ ≠ r₂, each ∈ {p, q}. Therefore {r₁, r₂} = {p, q}.
  rcases hr_in r₁ hr₁_prime hr₁_dvd with hr₁p | hr₁q
  · rcases hr_in r₂ hr₂_prime hr₂_dvd with hr₂p | hr₂q
    · exact absurd (hr₁p.trans hr₂p.symm) hr_ne
    · exact ⟨hr₁p ▸ hr₁_dvd, hr₂q ▸ hr₂_dvd⟩
  · rcases hr_in r₂ hr₂_prime hr₂_dvd with hr₂p | hr₂q
    · exact ⟨hr₂p ▸ hr₂_dvd, hr₁q ▸ hr₁_dvd⟩
    · exact absurd (hr₁q.trans hr₂q.symm) hr_ne

/-- **§7D Step 2 helper** — in a simple group, the normal closure of any
nontrivial subgroup is the whole group.

Used in Step 2 to argue: if `H' = ⟨V, Q⟩ < G` contains all `G`-conjugates of
`V` (which it does in Step 2's setup), then `H'` contains `V^G = G`, contradiction. -/
theorem normalClosure_eq_top_of_simple_of_ne_bot
    {G : Type*} [Group G] [hG : IsSimpleGroup G]
    {V : Subgroup G} (hV_ne_bot : V ≠ ⊥) :
    Subgroup.normalClosure (V : Set G) = ⊤ := by
  haveI := Subgroup.normalClosure_normal (s := (V : Set G))
  rcases Subgroup.Normal.eq_bot_or_eq_top
    (Subgroup.normalClosure_normal (s := (V : Set G))) with h | h
  · -- V ≤ normalClosure V = ⊥ ⇒ V = ⊥, contradiction.
    exfalso
    apply hV_ne_bot
    apply le_antisymm _ bot_le
    calc V ≤ Subgroup.normalClosure (V : Set G) := Subgroup.le_normalClosure
      _ = ⊥ := h
  · exact h

/-- **§7D Step 2 main consequence** — in a simple group, if a subgroup `K`
contains every conjugate `g * v * g⁻¹` of a nontrivial subgroup `V`, then
`K = ⊤`.

This is the cleanest form of Step 2's argument: `V` nontrivial and simple `G`
imply `V^G = ⊤`, so any `K` containing `V^G` (equivalently, all conjugates of
elements of `V`) must be `⊤`. -/
theorem eq_top_of_contains_all_conjugates_of_simple
    {G : Type*} [Group G] [IsSimpleGroup G]
    {V K : Subgroup G} (hV_ne_bot : V ≠ ⊥)
    (h_contains : ∀ g : G, ∀ v ∈ V, g * v * g⁻¹ ∈ K) :
    K = ⊤ := by
  have h_top : Subgroup.normalClosure (V : Set G) = ⊤ :=
    normalClosure_eq_top_of_simple_of_ne_bot hV_ne_bot
  -- K contains the normalClosure since K is closed under containing conjugates.
  have hK_normal_aux : ∀ x : G, x ∈ Subgroup.normalClosure (V : Set G) → x ∈ K := by
    intro x hx
    refine Subgroup.closure_induction (p := fun y _ => y ∈ K)
      (fun y hy_conj => ?_) ?_ ?_ ?_ hx
    · -- y is a conjugate of some v ∈ V
      rcases (Group.mem_conjugatesOfSet_iff (s := (V : Set G)) (x := y)).mp hy_conj with
        ⟨a, ha_inV, hConj⟩
      obtain ⟨g, hg⟩ := isConj_iff.mp hConj
      -- y = g * a * g⁻¹
      rw [← hg]
      exact h_contains g a ha_inV
    · exact K.one_mem
    · intro x y _ _ hx hy
      exact K.mul_mem hx hy
    · intro x _ hx
      exact K.inv_mem hx
  rw [eq_top_iff]
  intro x _
  apply hK_normal_aux
  rw [h_top]
  exact Subgroup.mem_top x

/-- A Sylow `p`-subgroup is nontrivial whenever `p ∣ |G|`. -/
theorem Sylow.ne_bot_of_dvd_card
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp_dvd : p ∣ Nat.card G) (P : Sylow p G) :
    (P : Subgroup G) ≠ ⊥ := by
  intro hP_bot
  have hp_prime : p.Prime := Fact.out
  have h_card : Nat.card (P : Subgroup G) = 1 := by rw [hP_bot]; exact Subgroup.card_bot
  have h_eq := P.card_eq_multiplicity
  rw [h_card] at h_eq
  have h_pos : 0 < (Nat.card G).factorization p :=
    hp_prime.factorization_pos_of_dvd Nat.card_pos.ne' hp_dvd
  have h1 : (1 : ℕ) = p ^ 0 := by simp
  rw [h1] at h_eq
  have h_mult_zero : (Nat.card G).factorization p = 0 :=
    (Nat.pow_right_injective hp_prime.two_le h_eq).symm
  omega

/-- **§7D IsPCentral existence** — in a finite group with `p ∣ |G|`, every
Sylow `p`-subgroup has a nontrivial element in its center (since a nontrivial
finite `p`-group has nontrivial center), and any such nontrivial center
element is `p`-central. -/
theorem exists_isPCentral {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp_dvd : p ∣ Nat.card G) :
    ∃ x : G, IsPCentral p x := by
  classical
  haveI : Nontrivial G := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    exact lt_of_lt_of_le (Fact.out (p := p.Prime)).one_lt
      (Nat.le_of_dvd Nat.card_pos hp_dvd)
  -- Pick a Sylow p-subgroup; it is nontrivial.
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  have hP_ne_bot : (P : Subgroup G) ≠ ⊥ := Sylow.ne_bot_of_dvd_card hp_dvd P
  -- P is a finite nontrivial p-group, so its center is nontrivial.
  haveI : Nontrivial ↥(P : Subgroup G) := P.toSubgroup.nontrivial_iff_ne_bot.mpr hP_ne_bot
  haveI : Finite ↥(P : Subgroup G) := inferInstance
  have hPpg : IsPGroup p ↥(P : Subgroup G) := P.isPGroup'
  have h_center_nt : Nontrivial (Subgroup.center ↥(P : Subgroup G)) :=
    hPpg.center_nontrivial
  -- Pick a nontrivial center element.
  obtain ⟨⟨⟨c, hc_mem⟩, hc_in_center⟩, hc_ne_one⟩ :=
    exists_ne (1 : Subgroup.center ↥(P : Subgroup G))
  -- c ∈ G, c ∈ (Subgroup.center P).map P.subtype, c ≠ 1.
  refine ⟨c, ?_, P, ?_⟩
  · -- c ≠ 1 since (⟨⟨c, hc_mem⟩, hc_in_center⟩) ≠ 1 inside center.
    intro hc1
    apply hc_ne_one
    apply Subtype.ext
    apply Subtype.ext
    exact hc1
  · -- c ∈ (Subgroup.center P).map P.subtype
    exact ⟨⟨c, hc_mem⟩, hc_in_center, rfl⟩

/-- **§7D Sylow extraction** — in a finite simple non-solvable group of order
dividing `p^a * q^b`, every Sylow `p`-subgroup is nontrivial. -/
theorem sylow_ne_bot_of_simple_nonsolvable_paqb
    {H : Type*} [Group H] [Finite H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hH_simple : IsSimpleGroup H) (hH_nsol : ¬ IsSolvable H)
    {a b : ℕ} (hH_dvd : Nat.card H ∣ p ^ a * q ^ b)
    (P : Sylow p H) : (P : Subgroup H) ≠ ⊥ :=
  Sylow.ne_bot_of_dvd_card
    (p_and_q_dvd_card_of_simple_nonsolvable hpq hH_simple hH_nsol hH_dvd).1 P

/-- **§7D auxiliary observation** (Isaacs L3965) — if `M` is a maximal subgroup
of a simple group `G` and `K ≤ M` is a nontrivial subgroup normalized by every
element of `M`, then `M = N_G(K)`.

Proof: `M ⊆ N_G(K)` by hypothesis.  `N_G(K) ≠ ⊤` since otherwise `K ⊴ G`
which (by simplicity) forces `K = ⊥` (contradicting nontriviality) or `K = ⊤`
(contradicting `K ≤ M < G`).  By maximality, `N_G(K) = M`. -/
theorem maximal_eq_normalizer_of_M_normalizes
    {G : Type*} [Group G] [IsSimpleGroup G]
    {M K : Subgroup G} (hM_max : IsCoatom M)
    (hK_ne_bot : K ≠ ⊥) (hKM_le : K ≤ M)
    (hM_normalizes : M ≤ Subgroup.normalizer K) :
    Subgroup.normalizer K = M := by
  rcases hM_max.le_iff.mp hM_normalizes with h | h
  · -- N_G(K) = ⊤ ⇒ K is normal in G ⇒ K ∈ {⊥, ⊤} by simplicity.
    exfalso
    have hK_norm_G : K.Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hg_in_N : g ∈ Subgroup.normalizer K := h ▸ Subgroup.mem_top g
      rw [Subgroup.mem_normalizer_iff] at hg_in_N
      exact (hg_in_N x).mp hx
    rcases hK_norm_G.eq_bot_or_eq_top with hK_bot | hK_top
    · exact hK_ne_bot hK_bot
    · -- K = ⊤ contradicts K ≤ M and M < ⊤ (since M is a coatom).
      have : K ≤ M := hKM_le
      rw [hK_top] at this
      exact hM_max.ne_top (le_antisymm le_top this)
  · -- h : N_G(K) = M is exactly the goal.
    exact h

/-- **§7D Step 5 (first half)** — every `p`-subgroup of a finite group is
centralized by some `p`-central element.

Isaacs L3995-3998: "Given a `p`-subgroup `V ⊆ G`, choose `P ∈ Syl_p(G)` with
`P ⊇ V`.  Then `Z(P) ⊆ C_G(V)`, and so `C_G(V)` contains a `p`-central
element."

This requires `p ∣ |G|` (so `P` is nontrivial) and `V` to be a finite
`p`-subgroup (so it's contained in some Sylow). -/
theorem exists_isPCentral_centralizing
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp_dvd : p ∣ Nat.card G)
    (V : Subgroup G) (hV_pgroup : IsPGroup p V) :
    ∃ x : G, IsPCentral p x ∧ ∀ v ∈ V, x * v = v * x := by
  classical
  -- Extend V to a Sylow p-subgroup P; it is nontrivial since p ∣ |G|.
  obtain ⟨P, hVP⟩ := IsPGroup.exists_le_sylow hV_pgroup
  have hP_ne_bot : (P : Subgroup G) ≠ ⊥ := Sylow.ne_bot_of_dvd_card hp_dvd P
  -- P nontrivial p-group ⇒ Z(P) nontrivial.
  haveI : Nontrivial ↥(P : Subgroup G) :=
    (P : Subgroup G).nontrivial_iff_ne_bot.mpr hP_ne_bot
  haveI : Finite ↥(P : Subgroup G) := inferInstance
  have hPpg : IsPGroup p ↥(P : Subgroup G) := P.isPGroup'
  have h_center_nt : Nontrivial (Subgroup.center ↥(P : Subgroup G)) :=
    hPpg.center_nontrivial
  obtain ⟨⟨⟨c, hc_mem⟩, hc_in_center⟩, hc_ne_one⟩ :=
    exists_ne (1 : Subgroup.center ↥(P : Subgroup G))
  -- c is p-central.
  have hc_pcentral : IsPCentral p c := by
    refine ⟨?_, P, ⟨c, hc_mem⟩, hc_in_center, rfl⟩
    intro hc1
    apply hc_ne_one
    apply Subtype.ext
    apply Subtype.ext
    exact hc1
  -- c commutes with everything in P, in particular with everything in V ⊆ P.
  have hc_center_iff : ∀ g : ↥(P : Subgroup G),
      g * ⟨c, hc_mem⟩ = ⟨c, hc_mem⟩ * g :=
    Subgroup.mem_center_iff.mp hc_in_center
  have hc_comm : ∀ v ∈ V, c * v = v * c := by
    intro v hv
    have hv_P : v ∈ (P : Subgroup G) := hVP hv
    have hcomm := hc_center_iff ⟨v, hv_P⟩
    have := (congrArg Subtype.val hcomm).symm
    simpa [Subgroup.coe_mul] using this
  exact ⟨c, hc_pcentral, hc_comm⟩

/-- **§7D Step 7 (q = 2 application of Matsuyama)** — if `H` is a finite simple
non-solvable group and `q = 2`, then for any involution `t ∈ H` with `t ≠ 1`,
there exists an element `x` of odd prime order with `t * x * t = x⁻¹`.

This combines `opCore_eq_bot_of_simple_nonsolvable` (giving `t ∉ O_2(H)`) with
Matsuyama's theorem (Isaacs Thm 2.13).  Step 7 will use this to derive a
contradiction with Step 6 ("`q`-central elements normalize no nontrivial
`p`-subgroup"). -/
theorem matsuyama_of_simple_nonsolvable_q_two
    {H : Type*} [Group H] [Finite H]
    (hH_simple : IsSimpleGroup H) (hH_nsol : ¬ IsSolvable H)
    {t : H} (ht_sq : t * t = 1) (ht_ne_one : t ≠ 1) :
    ∃ x : H, ∃ p : ℕ, p.Prime ∧ Odd p ∧ orderOf x = p ∧ t * x * t = x⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- t ∉ O_2(H) since O_2(H) = ⊥ in a simple non-solvable group.
  have hO2_bot : OddOrder.Isaacs.Ch01.opCore 2 H = ⊥ :=
    opCore_eq_bot_of_simple_nonsolvable hH_simple hH_nsol
  have ht_notin : t ∉ OddOrder.Isaacs.Ch01.opCore 2 H := by
    rw [hO2_bot, Subgroup.mem_bot]
    exact ht_ne_one
  exact OddOrder.Isaacs.Ch02.matsuyama ht_sq ht_notin

/-! ### §7D Steps 2-9 — per-step decomposition of the 9-step argument

The original monolithic axiom `noNonsolvableSimplePaQb` (the entire
Goldschmidt-Bender-Matsuyama argument) is here decomposed into the individual
textbook steps.  Steps that are provable from the landed infrastructure appear
as theorems; the heavier steps (4, 8, 9) remain as fine-grained local axioms,
each tracked in issue 0032.  The steps are wired together into
`noNonsolvableSimplePaQb` (now a *theorem*) at the end. -/

/-- **§7D arithmetic helper** — a positive natural dividing `p^a * q^b`
(`p ≠ q` prime) is itself of the form `p^a' * q^b'`.

Both sides have the same `Nat.factorization` (agreeing at `p`, at `q`, and being
`0` elsewhere since the only prime factors are `p` and `q`), so they are equal. -/
theorem card_eq_pow_mul_pow_of_dvd {n p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hn : n ≠ 0)
    {a b : ℕ} (hdvd : n ∣ p ^ a * q ^ b) :
    n = p ^ n.factorization p * q ^ n.factorization q := by
  -- Every prime factor of n is p or q.
  have hpf : ∀ r, r.Prime → r ∣ n → r = p ∨ r = q := by
    intro r hr_prime hr_dvd
    have hr_dvd_paqb : r ∣ p ^ a * q ^ b := hr_dvd.trans hdvd
    rcases (Nat.Prime.dvd_mul hr_prime).mp hr_dvd_paqb with h | h
    · left; exact (Nat.prime_dvd_prime_iff_eq hr_prime hp).mp (hr_prime.dvd_of_dvd_pow h)
    · right; exact (Nat.prime_dvd_prime_iff_eq hr_prime hq).mp (hr_prime.dvd_of_dvd_pow h)
  -- Compare factorizations.
  apply Nat.eq_of_factorization_eq hn
    (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero))
  intro r
  -- factorization of RHS at r: (n.fact p)*(p.fact r) + (n.fact q)*(q.fact r).
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
      Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow,
      Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
  -- Use the explicit single-point factorization of a prime.
  rw [Nat.Prime.factorization hp, Nat.Prime.factorization hq,
      Finsupp.single_apply, Finsupp.single_apply]
  by_cases hrp : r = p
  · subst hrp
    rw [if_pos rfl, if_neg (fun h => hpq h.symm), mul_one, mul_zero, add_zero]
  · by_cases hrq : r = q
    · subst hrq
      rw [if_neg (fun h => hpq h), if_pos rfl, mul_one, mul_zero, zero_add]
    · -- r ∉ {p,q}: n.factorization r = 0 and both single-points miss r.
      rw [if_neg (fun h => hrp h.symm), if_neg (fun h => hrq h.symm), mul_zero, mul_zero, add_zero]
      -- n.factorization r = 0: r is not a prime factor of n.
      by_cases hr_prime : r.Prime
      · exact Nat.factorization_eq_zero_of_not_dvd (fun hdvd_pr => by
          rcases hpf r hr_prime hdvd_pr with h | h; exacts [hrp h, hrq h])
      · exact Nat.factorization_eq_zero_of_non_prime _ hr_prime

/-- **§7D Step 2 — complementary Sylow product** (Isaacs L3973).

In a finite group of order `p^a * q^b` (`p ≠ q` prime), a Sylow `p`-subgroup
and a Sylow `q`-subgroup are complementary: `|P| * |Q| = |G|` and they are
disjoint, so `(P, Q)` is a complement pair.  This packages the textbook fact
"`|PQ| = |P||Q| = |G|` since `P ∩ Q = 1`, and thus `PQ = G`". -/
theorem sylow_isComplement_of_paqb
    {H : Type*} [Group H] [Finite H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (P : Sylow p H) (Q : Sylow q H) :
    Subgroup.IsComplement' (P : Subgroup H) (Q : Subgroup H) := by
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  have hp_ne_dvd_q : ¬ p ∣ q := by
    rw [Nat.prime_dvd_prime_iff_eq hp_prime hq_prime]; exact hpq
  have hq_ne_dvd_p : ¬ q ∣ p := by
    rw [Nat.prime_dvd_prime_iff_eq hq_prime hp_prime]; exact (Ne.symm hpq)
  -- factorization of p^a * q^b at p is a, at q is b.
  have hfact_p : (p ^ a * q ^ b).factorization p = a := by
    rw [Nat.factorization_mul (pow_ne_zero a hp_prime.ne_zero)
        (pow_ne_zero b hq_prime.ne_zero), Finsupp.add_apply,
        Nat.factorization_pow_self hp_prime,
        Nat.factorization_pow, Finsupp.smul_apply,
        Nat.factorization_eq_zero_of_not_dvd hp_ne_dvd_q, smul_eq_mul, mul_zero, add_zero]
  have hfact_q : (p ^ a * q ^ b).factorization q = b := by
    rw [Nat.factorization_mul (pow_ne_zero a hp_prime.ne_zero)
        (pow_ne_zero b hq_prime.ne_zero), Finsupp.add_apply,
        Nat.factorization_pow_self hq_prime,
        Nat.factorization_pow, Finsupp.smul_apply,
        Nat.factorization_eq_zero_of_not_dvd hq_ne_dvd_p, smul_eq_mul, mul_zero, zero_add]
  -- |P| = p ^ a, |Q| = q ^ b.
  have hP_card : Nat.card (P : Subgroup H) = p ^ a := by
    rw [P.card_eq_multiplicity, hH_card, hfact_p]
  have hQ_card : Nat.card (Q : Subgroup H) = q ^ b := by
    rw [Q.card_eq_multiplicity, hH_card, hfact_q]
  -- |P| * |Q| = |G| and coprime ⇒ complement.
  refine Subgroup.isComplement'_of_coprime ?_ ?_
  · rw [hP_card, hQ_card, hH_card]
  · rw [hP_card, hQ_card]
    exact Nat.Coprime.pow a b (hp_prime.coprime_iff_not_dvd.mpr hp_ne_dvd_q)

/-- **§7D Step 2 — join with Sylow `q` is everything** (Isaacs L3973-3978).

If `P ∈ Syl_p(H)` normalizes a nontrivial subgroup `V` of a finite simple
group `H` of order `p^a q^b`, then `⟨V, Q⟩ = H` for every `Q ∈ Syl_q(H)`.

Proof (textbook): `H = PQ`, so for `g = xy` (`x ∈ P`, `y ∈ Q`),
`V^g = V^{xy} = V^y ⊆ ⟨V,Q⟩` since `P` normalizes `V`.  Thus `⟨V,Q⟩` contains
all `H`-conjugates of `V`; by simplicity `V^H = H`, so `⟨V,Q⟩ = H`. -/
theorem step2_join_sylow_q_eq_top
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (P : Sylow p H) (Q : Sylow q H)
    {V : Subgroup H} (hV_ne_bot : V ≠ ⊥)
    (hP_norm : (P : Subgroup H) ≤ Subgroup.normalizer V) :
    V ⊔ (Q : Subgroup H) = ⊤ := by
  -- (Q, P) is a complement pair, so every g factors as y * x with y ∈ Q, x ∈ P.
  have hcompl : Subgroup.IsComplement' (Q : Subgroup H) (P : Subgroup H) :=
    (sylow_isComplement_of_paqb hpq hH_card P Q).symm
  -- ⟨V, Q⟩ = V ⊔ Q contains all conjugates of V.
  have h_contains : ∀ g : H, ∀ v ∈ V, g * v * g⁻¹ ∈ V ⊔ (Q : Subgroup H) := by
    intro g v hv
    -- Factor g = y * x, y ∈ Q, x ∈ P.
    obtain ⟨⟨⟨y, hy⟩, ⟨x, hx⟩⟩, hyx⟩ := hcompl.2 g
    simp only at hyx
    subst hyx
    -- g v g⁻¹ = (y x) v (y x)⁻¹ = y (x v x⁻¹) y⁻¹.
    have hgvg : (y * x) * v * (y * x)⁻¹ = y * (x * v * x⁻¹) * y⁻¹ := by group
    rw [hgvg]
    -- x ∈ P ≤ N(V) ⇒ x * v * x⁻¹ ∈ V.
    have hx_norm : x ∈ Subgroup.normalizer V := hP_norm hx
    have hxvx_mem_V : x * v * x⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hx_norm v).mp hv
    -- Now y * (x v x⁻¹) * y⁻¹ ∈ ⟨V, Q⟩ since x v x⁻¹ ∈ V ≤ join, y ∈ Q ≤ join.
    have hy_join : y ∈ V ⊔ (Q : Subgroup H) := Subgroup.mem_sup_right hy
    have hxvx_join : x * v * x⁻¹ ∈ V ⊔ (Q : Subgroup H) := Subgroup.mem_sup_left hxvx_mem_V
    exact (V ⊔ (Q : Subgroup H)).mul_mem
      ((V ⊔ (Q : Subgroup H)).mul_mem hy_join hxvx_join)
      ((V ⊔ (Q : Subgroup H)).inv_mem hy_join)
  exact eq_top_of_contains_all_conjugates_of_simple hV_ne_bot h_contains

/-- **§7D Step 2 — a full Sylow `p`-subgroup normalizes no nontrivial
`q`-subgroup** (Isaacs L3978-3980, the "in particular" clause).

If `P ∈ Syl_p(H)` (`H` finite simple of order `p^a q^b`) normalized a
nontrivial `q`-subgroup `V`, then by `step2_join_sylow_q_eq_top` we would have
`V ⊔ Q = ⊤` for a suitable `Q ∈ Syl_q` chosen to contain `V`; but then
`V ⊔ Q = Q ≠ ⊤`, a contradiction. -/
theorem step2_pSylow_not_normalizes_nontrivial_qSubgroup
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hp_dvd : p ∣ Nat.card H)
    (P : Sylow p H) {V : Subgroup H} (hV_ne_bot : V ≠ ⊥)
    (hV_qgroup : IsPGroup q V)
    (hP_norm : (P : Subgroup H) ≤ Subgroup.normalizer V) :
    False := by
  -- Pick a Sylow q-subgroup Q ⊇ V.
  obtain ⟨Q, hVQ⟩ := IsPGroup.exists_le_sylow hV_qgroup
  -- Step 2: V ⊔ Q = ⊤.
  have h_top : V ⊔ (Q : Subgroup H) = ⊤ :=
    step2_join_sylow_q_eq_top hpq hH_card P Q hV_ne_bot hP_norm
  -- But V ≤ Q, so V ⊔ Q = Q, forcing Q = ⊤.
  have h_join_eq_Q : V ⊔ (Q : Subgroup H) = (Q : Subgroup H) := sup_eq_right.mpr hVQ
  rw [h_join_eq_Q] at h_top
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  have hp_ne_dvd_q : ¬ p ∣ q := by
    rw [Nat.prime_dvd_prime_iff_eq hp_prime hq_prime]; exact hpq
  have hq_ne_dvd_p : ¬ q ∣ p := by
    rw [Nat.prime_dvd_prime_iff_eq hq_prime hp_prime]; exact (Ne.symm hpq)
  -- Q = ⊤ ⇒ |H| = |Q| = q^b.  But p ∣ |H| = q^b ⇒ p ∣ q, contradiction.
  have hQ_card : Nat.card (Q : Subgroup H) = q ^ b := by
    rw [Q.card_eq_multiplicity, hH_card]
    congr 1
    rw [Nat.factorization_mul (pow_ne_zero a hp_prime.ne_zero)
        (pow_ne_zero b hq_prime.ne_zero), Finsupp.add_apply,
        Nat.factorization_pow_self hq_prime,
        Nat.factorization_pow, Finsupp.smul_apply,
        Nat.factorization_eq_zero_of_not_dvd hq_ne_dvd_p, smul_eq_mul, mul_zero, zero_add]
  have hH_card_eq_qb : Nat.card H = q ^ b := by
    have : Nat.card (Q : Subgroup H) = Nat.card H := by
      rw [h_top]; exact Nat.card_congr (Subgroup.topEquiv).toEquiv
    rw [← this, hQ_card]
  rw [hH_card_eq_qb] at hp_dvd
  exact hp_ne_dvd_q (hp_prime.dvd_of_dvd_pow hp_dvd)

/-- **§7D helper** — a nontrivial finite solvable group has nontrivial Fitting
subgroup.

**Proven.** Take the *last nontrivial term* `L = derivedSeries M (n-1)` of the
derived series (where `n` is minimal with `derivedSeries M n = ⊥`).  Then
`⁅L, L⁆ = derivedSeries M n = ⊥`, so `L` is abelian, hence nilpotent; `L` is
characteristic (`derivedSeries_characteristic`) hence normal, and nontrivial by
minimality of `n`.  By `nilpotent_normal_le_fitting`, `L ≤ F(M)`, so
`F(M) ≠ ⊥`. -/
theorem fitting_ne_bot_of_solvable_nontrivial
    (M : Type*) [Group M] [Finite M] [Nontrivial M] [IsSolvable M] :
    OddOrder.Isaacs.Ch01.fitting M ≠ ⊥ := by
  classical
  -- ∃ n, derivedSeries M n = ⊥.
  obtain ⟨N, hN⟩ := (isSolvable_def M).mp inferInstance
  -- Minimal such n.
  have hex : ∃ n, derivedSeries M n = ⊥ := ⟨N, hN⟩
  set n := Nat.find hex with hn_def
  have hn_bot : derivedSeries M n = ⊥ := Nat.find_spec hex
  -- n ≠ 0: derivedSeries M 0 = ⊤ ≠ ⊥ since M nontrivial.
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      have : derivedSeries M 0 = ⊥ := h0 ▸ hn_bot
      rw [derivedSeries_zero] at this
      exact (bot_ne_top (α := Subgroup M)) this.symm
    · exact hpos
  -- L := derivedSeries M (n-1) is the last nontrivial term.
  set m := n - 1 with hm_def
  have hm_succ : m + 1 = n := by omega
  set L := derivedSeries M m with hL_def
  -- L ≠ ⊥ by minimality of n.
  have hL_ne_bot : L ≠ ⊥ := by
    rw [hL_def]
    exact Nat.find_min hex (by omega)
  -- ⁅L, L⁆ = derivedSeries M n = ⊥.
  have hLL_bot : ⁅L, L⁆ = ⊥ := by
    rw [hL_def, ← derivedSeries_succ, hm_succ, hn_bot]
  -- L is abelian (commutative): ⁅L,L⁆ = ⊥ ⇒ each pair commutes.
  haveI hL_comm : IsMulCommutative L := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hLL_bot
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha_cent : (a : M) ∈ Subgroup.centralizer (L : Set M) := hLL_bot a.property
    rw [Subgroup.mem_centralizer_iff] at ha_cent
    apply Subtype.ext
    exact (ha_cent b.val b.property).symm
  -- L is normal (characteristic).
  haveI hL_normal : L.Normal := by rw [hL_def]; exact derivedSeries_normal M m
  -- L is nilpotent (abelian ⇒ CommGroup via CommGroup.ofIsMulCommutative ⇒ nilpotent).
  haveI hL_nilp : Group.IsNilpotent ↥L := inferInstance
  -- L ≤ F(M), so F(M) ≠ ⊥.
  have hL_le_fitting : L ≤ OddOrder.Isaacs.Ch01.fitting M :=
    OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
  intro hF_bot
  rw [hF_bot, le_bot_iff] at hL_le_fitting
  exact hL_ne_bot hL_le_fitting

/-- **§7D Steps 2-3 partition setup** — every maximal subgroup `M` of a simple
group of order `p^a q^b` is `p`-type or `q`-type (Isaacs L3963-3967).

`M` is solvable (proper subgroup, all proper subgroups solvable) and nontrivial,
so its Fitting subgroup is nontrivial; since `|M| ∣ p^a q^b` has prime factors
only among `{p, q}`, and `F(M) = ⨆_{r ∈ primeFactors |M|} O_r(M)`, at least one
of `O_p(M)`, `O_q(M)` is nontrivial. -/
theorem maximal_isPType_or_isQType
    {H : Type*} [Group H] [Finite H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    {M : Subgroup H} (hM_max : IsCoatom M) (hM_ne_bot : M ≠ ⊥)
    (hM_solvable : IsSolvable M) :
    IsPType p M ∨ IsQType q M := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  -- M is nontrivial since M ≠ ⊥ (in the §7D application H is non-solvable, so
  -- |H| is not prime and a maximal subgroup is never trivial).
  haveI hM_nontriv : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
  -- F(M) ≠ ⊥.
  have hF_ne_bot : OddOrder.Isaacs.Ch01.fitting ↥M ≠ ⊥ :=
    fitting_ne_bot_of_solvable_nontrivial ↥M
  -- F(M) = ⨆_{r ∈ primeFactors |M|} O_r(M).
  rw [OddOrder.Isaacs.Ch01.fitting_eq_iSup_primeFactors] at hF_ne_bot
  -- primeFactors |M| ⊆ {p, q}.
  have hM_card_dvd : Nat.card ↥M ∣ p ^ a * q ^ b := by
    rw [← hH_card]; exact M.card_subgroup_dvd_card
  have hpf_sub : ∀ r ∈ (Nat.card ↥M).primeFactors, r = p ∨ r = q := by
    intro r hr
    obtain ⟨hr_prime, hr_dvd, _⟩ := Nat.mem_primeFactors.mp hr
    have hr_dvd_paqb : r ∣ p ^ a * q ^ b := hr_dvd.trans hM_card_dvd
    rcases (Nat.Prime.dvd_mul hr_prime).mp hr_dvd_paqb with h | h
    · left; exact (Nat.prime_dvd_prime_iff_eq hr_prime hp_prime).mp (hr_prime.dvd_of_dvd_pow h)
    · right; exact (Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp (hr_prime.dvd_of_dvd_pow h)
  -- Some O_r(M) ≠ ⊥ with r ∈ {p,q}.
  by_contra h_neither
  push Not at h_neither
  obtain ⟨h_notP, h_notQ⟩ := h_neither
  -- h_notP : ¬ IsPType p M, i.e., ¬(IsCoatom M ∧ opCore p ↥M ≠ ⊥).
  have hOp_bot : OddOrder.Isaacs.Ch01.opCore p ↥M = ⊥ := by
    by_contra hne; exact h_notP ⟨hM_max, hne⟩
  have hOq_bot : OddOrder.Isaacs.Ch01.opCore q ↥M = ⊥ := by
    by_contra hne; exact h_notQ ⟨hM_max, hne⟩
  -- Then every generator opCore r ↥M (r ∈ primeFactors) is ⊥, so the sup is ⊥.
  apply hF_ne_bot
  rw [eq_bot_iff]
  refine iSup_le (fun r => ?_)
  rcases hpf_sub r r.2 with hrp | hrq
  · rw [show (r : ℕ) = p from hrp, hOp_bot]
  · rw [show (r : ℕ) = q from hrq, hOq_bot]


/-! ### §7D Steps 3-9 — per-step axioms + Step 7 theorem + final wiring

The remaining heavier steps (3, 4, 6, 8, 9) are stated as fine-grained local
axioms with textbook-faithful signatures.  Step 7 (`p, q` both odd) is *proven*
from the Step 6 axiom and the landed Matsuyama application.  All steps are
threaded into `noNonsolvableSimplePaQb` (now a theorem) at the end.  Each axiom
is tracked in issue 0032. -/

/-- **§7D Step 3 axiom** (Isaacs L3982-3993) — *not both cores nontrivial*.

For a maximal subgroup `M` of a simple group of order `p^a q^b`, it is **not**
the case that both `O_p(M)` and `O_q(M)` are nontrivial.  Combined with the
partition `maximal_isPType_or_isQType`, this gives: every maximal is `p`-type
**XOR** `q`-type.

Textbook proof: assuming both nontrivial, set `Z = Z(O_p(M)) · Z(O_q(M))`
(abelian, normal in `M`); then `M = N_G(Z)` is the unique maximal containing `Z`
(Step 1).  A Sylow `p`-subgroup `S` of `M` normalizes the nontrivial `q`-group
`Z_q`, so by Step 2 `S` is not a full Sylow `p`; the `N_P(S) > S` argument
produces `g ∈ G - M` with `S^g = S`, forcing `Z^g ⊆ M^g` and (via Thm 6.20 /
faithful-action analysis) `Z ⊆ M^g`, so `M = M^g` and `g ∈ M`, contradiction. -/
axiom step3_not_both_opCore_ne_bot
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_max : IsCoatom M) :
    OddOrder.Isaacs.Ch01.opCore p ↥M = ⊥ ∨ OddOrder.Isaacs.Ch01.opCore q ↥M = ⊥

/-- **§7D Steps 2-3 dichotomy** (Isaacs L4022-4026) — *every maximal subgroup
has exactly one type*.

Combining the partition (`maximal_isPType_or_isQType`, proven) with Step 3
(`step3_not_both_opCore_ne_bot`, axiom: not both cores nontrivial): a maximal
subgroup `M ≠ ⊥` of a simple group of order `p^a q^b` is `p`-type **xor**
`q`-type — exactly one of `IsPType p M`, `IsQType q M` holds.  This `Xor'` form
is the precise statement used throughout Steps 5-9. -/
theorem maximal_isPType_xor_isQType
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_max : IsCoatom M) (hM_ne_bot : M ≠ ⊥) :
    Xor' (IsPType p M) (IsQType q M) := by
  -- At least one type (partition).
  have h_or : IsPType p M ∨ IsQType q M :=
    maximal_isPType_or_isQType hpq hH_card hM_max hM_ne_bot (hSubgroupsSolvable M hM_max.1)
  -- Not both (Step 3): O_p(M) = ⊥ ∨ O_q(M) = ⊥.
  have h_step3 : OddOrder.Isaacs.Ch01.opCore p ↥M = ⊥ ∨ OddOrder.Isaacs.Ch01.opCore q ↥M = ⊥ :=
    step3_not_both_opCore_ne_bot hpq hH_card hSubgroupsSolvable hM_max
  -- IsPType p M = (IsCoatom M ∧ O_p(M) ≠ ⊥); IsQType q M = (IsCoatom M ∧ O_q(M) ≠ ⊥).
  have h_not_both : ¬ (IsPType p M ∧ IsQType q M) := by
    rintro ⟨hP, hQ⟩
    rcases h_step3 with hp_bot | hq_bot
    · exact hP.2 hp_bot
    · exact hQ.2 hq_bot
  rcases h_or with hP | hQ
  · exact Or.inl ⟨hP, fun hQ => h_not_both ⟨hP, hQ⟩⟩
  · exact Or.inr ⟨hQ, fun hP => h_not_both ⟨hP, hQ⟩⟩

/-- **§7D Step 8 helper** — for a `p`-type maximal `M` of a simple group of order
`p^a q^b`, the `p'`-core of `M` is trivial: `O_{p'}(M) = ⊥`.

`O_{p'}(M) = oPiCore {r ≠ p} ↥M` is a normal `{r ≠ p}`-subgroup of `↥M`.  Since
`|M| ∣ p^a q^b`, its only prime factors lie in `{p, q}`; intersecting with
`{r ≠ p}` leaves only `q`, so `O_{p'}(M)` is a `q`-group, hence `≤ O_q(M)`.  By
the dichotomy, `M` `p`-type ⇒ `O_q(M) = ⊥`. -/
theorem oPiCore_pPrime_eq_bot_of_isPType
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_pType : IsPType p M) :
    OddOrder.Isaacs.Ch03.oPiCore {r | r ≠ p} ↥M = ⊥ := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  have hM_ne_bot : M ≠ ⊥ := by
    intro hMbot
    have : Subsingleton ↥M := by rw [hMbot]; infer_instance
    exact hM_pType.2 (Subgroup.eq_bot_of_subsingleton _)
  -- `O_q(M) = ⊥` by the dichotomy (`M` p-type ⇒ not q-type ⇒ O_q(M) = ⊥).
  have hOq_bot : OddOrder.Isaacs.Ch01.opCore q ↥M = ⊥ := by
    rcases maximal_isPType_xor_isQType hpq hH_card hSubgroupsSolvable hM_pType.1 hM_ne_bot with
      h | h
    · by_contra hne
      exact h.2 ⟨hM_pType.1, hne⟩
    · exact absurd hM_pType h.2
  set K := OddOrder.Isaacs.Ch03.oPiCore {r | r ≠ p} ↥M with hK_def
  have hM_card_dvd : Nat.card ↥M ∣ p ^ a * q ^ b := by
    rw [← hH_card]; exact M.card_subgroup_dvd_card
  have hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {r | r ≠ p} K :=
    OddOrder.Isaacs.Ch03.oPiCore.isPiGroup {r | r ≠ p}
  -- `K` is a `q`-group: any prime factor `r ∣ |K|` is `≠ p`, divides `|M| ∣ p^a q^b`,
  -- hence `r = q`.
  have hK_q_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({q} : Set ℕ) K := by
    intro r hr
    obtain ⟨hr_prime, hr_dvd_K, _⟩ := Nat.mem_primeFactors.mp hr
    have hr_ne_p : r ≠ p := hK_pi r hr
    have hr_dvd_M : r ∣ Nat.card ↥M := hr_dvd_K.trans K.card_subgroup_dvd_card
    have hr_dvd_paqb : r ∣ p ^ a * q ^ b := hr_dvd_M.trans hM_card_dvd
    rcases (Nat.Prime.dvd_mul hr_prime).mp hr_dvd_paqb with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr_prime hp_prime).mp
        (hr_prime.dvd_of_dvd_pow h)) hr_ne_p
    · simp only [Set.mem_singleton_iff]
      exact (Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp (hr_prime.dvd_of_dvd_pow h)
  have hK_qgroup : IsPGroup q K :=
    OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton hK_q_pi
  haveI : K.Normal := OddOrder.Isaacs.Ch03.oPiCore.normal {r | r ≠ p} ↥M
  have hK_le : K ≤ OddOrder.Isaacs.Ch01.opCore q ↥M :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hK_qgroup
  rw [hOq_bot, le_bot_iff] at hK_le
  exact hK_le

/-- **§7D Step 4 axiom** (Isaacs L4001-4019) — *a `q`-central element normalizing
a `p`-subgroup forbids `p`-central elements*.

If `y` is `q`-central, `V` is a `p`-subgroup of the simple group `H` (order
`p^a q^b`) normalized by `y`, then `V` contains no `p`-central element.

Textbook proof (the `W`-maximality argument): for a `p`-subgroup `U`, let `U⋆` be
the subgroup generated by the `p`-central elements of `U`; `N_G(U)` permutes the
`p`-central elements of `U`, hence normalizes `U⋆`.  Let `W` be a `p`-subgroup
maximal subject to being normalized by `y` and generated by `p`-central elements.
If `W > 1`, set `N = N_G(W)`, `S ∈ Syl_p(N)`; since `⟨y, S⟩ ≤ N < G`, Step 2
(roles reversed) gives `S` not a full Sylow, so `∃ g ∈ G - N` with `S^g = S`,
whence `W^g ≠ W` but `W^g ⊆ S`.  A `p`-central generator `x` of `W` with
`x^g ∉ W` produces `(W (W^b ∩ N))⋆ ⊋ W` still normalized by `y` and `p`-central
generated, contradicting maximality.  So `V⋆ = 1`, i.e. `V` has no `p`-central
element. -/
axiom step4_qCentral_normalizes_no_pCentral
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {y : H} (hy_qcentral : IsPCentral q y)
    {V : Subgroup H} (hV_pgroup : IsPGroup p V)
    (hy_norm : y ∈ Subgroup.normalizer V)
    {x : H} (hx_pcentral : IsPCentral p x) (hx_mem : x ∈ V) :
    False

/-- **§7D Step 5 (second half)** (Isaacs L4027-4030) — *a `p`-type maximal
subgroup contains no `q`-central element*.  **Now a theorem** (was an axiom),
proven from Step 4 (`step4_qCentral_normalizes_no_pCentral`, axiom) plus
Hall-Higman.

Stated symmetrically in `p, q` (apply with `p := q`, `q := p` and `hH_card` in
the swapped form to use the dual).

Proof: for `M` `p`-type, `V := O_p(M)` is a nontrivial `p`-subgroup with
`O_{p'}(M) = ⊥`.  `M = N_H(V)` (since `V` is characteristic in `M`, and by
maximality + simplicity).  Hall-Higman 1.2.3
(`centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot`) gives `C_M(V) ⊆ V`, so a
nontrivial central element of a Sylow `p`-subgroup `P_H ⊇ V` of `H` is a
`p`-central element lying in `V`.  A `q`-central `y ∈ M = N_H(V)` then
contradicts Step 4. -/
theorem step5b_pType_no_qCentral
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_pType : IsPType p M)
    {y : H} (hy_qcentral : IsPCentral q y) :
    y ∉ M := by
  classical
  intro hy_in_M
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  obtain ⟨hp_dvd, hq_dvd⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  -- V := O_p(↥M) ≠ ⊥ (p-type); Vmap := V.map subtype.
  set K₀ : Subgroup ↥M := OddOrder.Isaacs.Ch01.opCore p ↥M with hK₀_def
  haveI hK₀_normal : K₀.Normal := by rw [hK₀_def]; infer_instance
  set V : Subgroup H := K₀.map M.subtype with hV_def
  have hV_ne_bot : V ≠ ⊥ := by
    intro hbot
    have hK₀_bot : K₀ = ⊥ := by
      rw [hV_def] at hbot
      exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp hbot
    exact hM_pType.2 hK₀_bot
  have hV_le_M : V ≤ M := by rw [hV_def]; exact Subgroup.map_subtype_le _
  -- V is a p-group.
  have hV_pgroup : IsPGroup p V := by
    rw [hV_def]; exact (OddOrder.Isaacs.Ch01.opCore_isPGroup p ↥M).map M.subtype
  -- M = N_H(V).
  have hM_norm_V : (M : Subgroup H) ≤ Subgroup.normalizer V := by
    have h1 : (Subgroup.normalizer (K₀ : Set ↥M)).map M.subtype
        ≤ Subgroup.normalizer ((K₀.map M.subtype : Subgroup H) : Set H) :=
      Subgroup.le_normalizer_map M.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr hK₀_normal] at h1
    have h3 : (⊤ : Subgroup ↥M).map M.subtype = M := by
      rw [← MonoidHom.range_eq_map, M.range_subtype]
    rw [h3] at h1; rw [hV_def]; exact h1
  have hM_eq_NV : Subgroup.normalizer V = M :=
    maximal_eq_normalizer_of_M_normalizes hM_pType.1 hV_ne_bot hV_le_M hM_norm_V
  -- y ∈ M = N_H(V).
  have hy_norm : y ∈ Subgroup.normalizer V := hM_eq_NV ▸ hy_in_M
  -- A p-central element x ∈ V (via Z(P_H) + Hall-Higman in ↥M).
  -- (i) P_H ∈ Syl_p(H) with V ≤ P_H.
  obtain ⟨PH, hV_le_PH⟩ := IsPGroup.exists_le_sylow hV_pgroup
  have hPH_ne_bot : (PH : Subgroup H) ≠ ⊥ := Sylow.ne_bot_of_dvd_card hp_dvd PH
  -- (ii) nontrivial Z(P_H) element x, p-central.
  haveI : Nontrivial ↥(PH : Subgroup H) :=
    (PH : Subgroup H).nontrivial_iff_ne_bot.mpr hPH_ne_bot
  have hPHpg : IsPGroup p ↥(PH : Subgroup H) := PH.isPGroup'
  have hZPH_nt : Nontrivial (Subgroup.center ↥(PH : Subgroup H)) := hPHpg.center_nontrivial
  obtain ⟨⟨⟨x, hx_mem_PH⟩, hx_center⟩, hx_ne_one⟩ :=
    exists_ne (1 : Subgroup.center ↥(PH : Subgroup H))
  have hx_ne_one' : x ≠ 1 := by
    intro h1; apply hx_ne_one; apply Subtype.ext; apply Subtype.ext; exact h1
  have hx_pcentral : IsPCentral p x := ⟨hx_ne_one', PH, ⟨x, hx_mem_PH⟩, hx_center, rfl⟩
  -- (iii) x centralizes V (V ≤ P_H, x ∈ Z(P_H)).
  have hx_centralizes_V : x ∈ Subgroup.centralizer (V : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv_PH : v ∈ (PH : Subgroup H) := hV_le_PH hv
    have hcomm := (Subgroup.mem_center_iff.mp hx_center) ⟨v, hv_PH⟩
    have h2 := congrArg (Subgroup.subtype (PH : Subgroup H)) hcomm
    simpa using h2
  -- (iv) x ∈ N_H(V) = M.
  have hx_in_NV : x ∈ Subgroup.normalizer V := centralizer_le_normalizer V hx_centralizes_V
  have hx_in_M : x ∈ M := hM_eq_NV ▸ hx_in_NV
  -- (v) xM := ⟨x,_⟩ ∈ C_M(K₀) (Hall-Higman context). Then xM ∈ K₀ ⇒ x ∈ V.
  set xM : ↥M := ⟨x, hx_in_M⟩ with hxM_def
  have hxM_cent_K₀ : xM ∈ Subgroup.centralizer (K₀ : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    -- w ∈ K₀; ↑w ∈ V; x centralizes ↑w.
    have hw_V : (M.subtype w) ∈ V := by rw [hV_def]; exact ⟨w, hw, rfl⟩
    have hxc := (Subgroup.mem_centralizer_iff.mp hx_centralizes_V) (M.subtype w) hw_V
    -- hxc : M.subtype w * x = x * M.subtype w.  Lift to ↥M.
    apply M.subtype_injective
    simp only [Subgroup.coe_mul, Subgroup.coe_subtype, hxM_def]
    exact hxc
  -- Hall-Higman in ↥M: C_M(K₀) ⊆ K₀.
  haveI hM_pSep : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) ↥M := by
    have hM_ne_top : (M : Subgroup H) ≠ ⊤ := hM_pType.1.ne_top
    haveI hM_sol : IsSolvable ↥M := hSubgroupsSolvable M hM_ne_top
    infer_instance
  have hOpp' : OddOrder.Isaacs.Ch03.oPiCore {r | r ≠ p} ↥M = ⊥ :=
    oPiCore_pPrime_eq_bot_of_isPType hpq hH_card hSubgroupsSolvable hM_pType
  have hHH : Subgroup.centralizer (K₀ : Set ↥M) ≤ K₀ := by
    rw [hK₀_def]
    exact centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot hOpp'
  have hxM_in_K₀ : xM ∈ K₀ := hHH hxM_cent_K₀
  have hx_in_V : x ∈ V := by rw [hV_def]; exact ⟨xM, hxM_in_K₀, rfl⟩
  -- (vi) Step 4: y q-central ∈ N_H(V), V p-group, x p-central ∈ V ⇒ False.
  exact step4_qCentral_normalizes_no_pCentral hpq hH_card hH_nsol hSubgroupsSolvable
    hy_qcentral hV_pgroup hy_norm hx_pcentral hx_in_V

/-- **§7D Step 6** (Isaacs L4031-4037) — *a `q`-central element cannot normalize
a nontrivial `p`-subgroup*.

**Proven** from Step 5 (second half) + the landed
`exists_isPCentral_centralizing` and the dichotomy.

Proof (textbook): let `V` be a nontrivial `p`-subgroup and `M ⊇ N_G(V)` a
maximal subgroup.  `N_G(V)` contains a `p`-central element (`Z(P) ⊆ C_G(V) ⊆
N_G(V)`), so `M` does too; by Step 5 (second half, with `p, q` swapped) `M`
cannot be `q`-type, hence `M` is `p`-type.  Then by Step 5 (second half) `M`
contains no `q`-central element.  In particular a `q`-central `y ∈ N_G(V) ⊆ M`
is impossible. -/
theorem step6_qCentral_not_normalizes_nontrivial_pSubgroup
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {y : H} (hy_qcentral : IsPCentral q y)
    {V : Subgroup H} (hV_ne_bot : V ≠ ⊥) (hV_pgroup : IsPGroup p V)
    (hy_norm : y ∈ Subgroup.normalizer V) :
    False := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  -- p ∣ |H| and q ∣ |H| (so p-central elements exist).
  obtain ⟨hp_dvd, hq_dvd⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  -- A maximal subgroup M ⊇ N_G(V).
  have hNV_ne_top : Subgroup.normalizer (V : Set H) ≠ ⊤ := by
    -- If N_G(V) = ⊤ then V ⊴ H, so V ∈ {⊥, ⊤} by simplicity; V ≠ ⊥, and V = ⊤
    -- would make H a p-group (V ≤ H p-subgroup), contradicting q ∣ |H|.
    intro hNV_top
    have hV_normal : V.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]; exact hNV_top
    rcases hV_normal.eq_bot_or_eq_top with hbot | htop
    · exact hV_ne_bot hbot
    · -- V = ⊤ ⇒ H is a p-group ⇒ q ∤ |H|, contradiction.
      have hH_pgroup : IsPGroup p H := by
        have : IsPGroup p (⊤ : Subgroup H) := htop ▸ hV_pgroup
        exact (this.of_equiv Subgroup.topEquiv)
      obtain ⟨k, hk⟩ := hH_pgroup.exists_card_eq
      rw [hk] at hq_dvd
      have : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp
        (hq_prime.dvd_of_dvd_pow hq_dvd)
      exact hpq this.symm
  obtain ⟨M, hM_max, hNV_le⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom
      (Subgroup.normalizer (V : Set H))).resolve_left hNV_ne_top
  -- N_G(V) contains a p-central element (centralizing V).
  obtain ⟨x, hx_pcentral, hx_comm⟩ := exists_isPCentral_centralizing hp_dvd V hV_pgroup
  have hx_in_CV : x ∈ Subgroup.centralizer (V : Set H) := by
    rw [Subgroup.mem_centralizer_iff]; intro v hv; exact (hx_comm v hv).symm
  have hx_in_NV : x ∈ Subgroup.normalizer V := centralizer_le_normalizer V hx_in_CV
  have hx_in_M : x ∈ M := hNV_le hx_in_NV
  -- M is p-type: it is not q-type, since a q-type maximal contains no
  -- p-central element (Step 5b with p,q swapped), but x ∈ M is p-central.
  have hM_ne_bot : M ≠ ⊥ := by
    intro hbot; rw [hbot] at hx_in_M
    exact hx_pcentral.ne_one (Subgroup.mem_bot.mp hx_in_M)
  have hM_pType : IsPType p M := by
    rcases maximal_isPType_xor_isQType hpq hH_card hSubgroupsSolvable hM_max hM_ne_bot with
      h | h
    · exact h.1
    · -- M is q-type: then by Step 5b (swapped) no p-central element ∈ M,
      -- contradicting x ∈ M being p-central.
      exfalso
      exact step5b_pType_no_qCentral (Ne.symm hpq) (a := b) (b := a)
        (by rw [hH_card]; ring) hH_nsol hSubgroupsSolvable h.1 hx_pcentral hx_in_M
  -- y is q-central and ∈ N_G(V) ⊆ M; Step 5b (p-type, no q-central) ⇒ False.
  have hy_in_M : y ∈ M := hNV_le hy_norm
  exact step5b_pType_no_qCentral hpq hH_card hH_nsol hSubgroupsSolvable hM_pType hy_qcentral hy_in_M

/-- **§7D Step 7** (Isaacs L4039-4043) — *both primes are odd*.

If `q = 2`, choose an involution `t` in the center of a Sylow `2`-subgroup
(so `t` is `q`-central).  By Matsuyama (Thm 2.13) there is an element `x` of odd
prime order with `t x t = x⁻¹`, hence `t ∈ N_G(⟨x⟩)` where `⟨x⟩` is a nontrivial
`p`-subgroup.  This contradicts Step 6.  Symmetrically `p ≠ 2`.

This step is **proven** from the Step 6 axiom and the landed
`matsuyama_of_simple_nonsolvable_q_two`. -/
theorem step7_p_ne_two_and_q_ne_two
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K) :
    p ≠ 2 ∧ q ≠ 2 := by
  classical
  -- The two cases are symmetric (swap p,q).  We prove a uniform sub-claim:
  -- if r is one of the two primes with r = 2 and s is the other prime (odd,
  -- s ∣ |H|), then we reach a contradiction with Step 6.
  -- Sub-claim: for primes r, s with r ≠ s, |H| = r^m s^k decomposition, r = 2,
  -- and Step 6 available for s-central elements normalizing r... but Step 6 is
  -- stated for q-central elements normalizing p-subgroups.  We need r playing
  -- the q-role and s playing the p-role.  Instantiate Step 6 accordingly.
  have key : ∀ (r s : ℕ) [Fact r.Prime] [Fact s.Prime], r ≠ s →
      ∀ m k : ℕ, Nat.card H = s ^ m * r ^ k → r = 2 → False := by
    intro r s _ _ hrs m k hcard hr2
    subst hr2
    -- A 2-central involution t exists: pick Q ∈ Syl_2, Z(Q) nontrivial 2-group.
    have h2_dvd : (2 : ℕ) ∣ Nat.card H :=
      (p_and_q_dvd_card_of_simple_nonsolvable (Ne.symm hrs) inferInstance hH_nsol
        (dvd_of_eq hcard)).2
    -- Build the 2-central involution.
    obtain ⟨Q⟩ := Sylow.nonempty (p := 2) (G := H)
    have hQ_ne_bot : (Q : Subgroup H) ≠ ⊥ := Sylow.ne_bot_of_dvd_card h2_dvd Q
    haveI : Nontrivial ↥(Q : Subgroup H) :=
      (Q : Subgroup H).nontrivial_iff_ne_bot.mpr hQ_ne_bot
    have hQpg : IsPGroup 2 ↥(Q : Subgroup H) := Q.isPGroup'
    have hZ_nt : Nontrivial (Subgroup.center ↥(Q : Subgroup H)) := hQpg.center_nontrivial
    -- 2 ∣ |Z(Q)| (nontrivial 2-group center), so Z(Q) has an involution.
    have h2_dvd_Z : (2 : ℕ) ∣ Nat.card (Subgroup.center ↥(Q : Subgroup H)) := by
      have hZpg : IsPGroup 2 (Subgroup.center ↥(Q : Subgroup H)) :=
        hQpg.to_subgroup _
      obtain ⟨k, hk⟩ := hZpg.exists_card_eq
      rw [hk]
      have hk_pos : 0 < k := by
        by_contra hk0
        rw [Nat.eq_zero_of_not_pos hk0, pow_zero] at hk
        exact (Finite.one_lt_card (α := Subgroup.center ↥(Q : Subgroup H))).ne' hk
      exact dvd_pow_self 2 hk_pos.ne'
    obtain ⟨z, hz_ord⟩ := exists_prime_orderOf_dvd_card' 2 h2_dvd_Z
    -- z ∈ Z(Q) with order 2; lift to t ∈ H, an involution, 2-central.
    -- z : ↥(center ↥↑Q).  The Sylow element is (z : ↥↑Q), and t = ((z : ↥↑Q) : H).
    set zQ : ↥(Q : Subgroup H) := (z : ↥(Q : Subgroup H)) with hzQ_def
    set t : H := (zQ : H) with ht_def
    -- orderOf t = orderOf zQ = orderOf z = 2.
    have ht_ord : orderOf t = 2 := by
      rw [ht_def, Subgroup.orderOf_coe, hzQ_def, Subgroup.orderOf_coe, hz_ord]
    have ht_ne_one : t ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at ht_ord
      exact (by norm_num : (1 : ℕ) ≠ 2) ht_ord
    have ht_sq : t * t = 1 := by
      have ht2 : t ^ 2 = 1 := by
        rw [← ht_ord]; exact pow_orderOf_eq_one t
      rw [pow_two] at ht2; exact ht2
    -- Matsuyama: ∃ x of odd prime order with t x t = x⁻¹.
    obtain ⟨x, p₀, hp₀_prime, hp₀_odd, hx_ord, hxt⟩ :=
      matsuyama_of_simple_nonsolvable_q_two inferInstance hH_nsol ht_sq ht_ne_one
    -- t normalizes ⟨x⟩.
    have hx_ne_one : x ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at hx_ord
      exact hp₀_prime.ne_one hx_ord.symm
    -- ⟨x⟩ is a p₀-subgroup; p₀ is odd and divides |H| = s^a 2^b, so p₀ = s.
    have hp₀_dvd : p₀ ∣ Nat.card H := hx_ord ▸ orderOf_dvd_natCard x
    have hp₀_eq_s : p₀ = s := by
      rw [hcard] at hp₀_dvd
      rcases (Nat.Prime.dvd_mul hp₀_prime).mp hp₀_dvd with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hp₀_prime (Fact.out (p := s.Prime))).mp
          (hp₀_prime.dvd_of_dvd_pow h)
      · -- p₀ ∣ 2^b ⇒ p₀ = 2, contradicting p₀ odd.
        exfalso
        have : p₀ = 2 := (Nat.prime_dvd_prime_iff_eq hp₀_prime Nat.prime_two).mp
          (hp₀_prime.dvd_of_dvd_pow h)
        rw [this] at hp₀_odd
        exact (by decide : ¬ Odd 2) hp₀_odd
    -- t is 2-central, i.e. q-central with q := 2.  ⟨x⟩ is a nontrivial
    -- s-subgroup.  Apply Step 6 with (p := s, q := 2).
    haveI : Fact s.Prime := inferInstance
    -- t is 2-central: t = (zQ : H), zQ = (z : ↥↑Q) ∈ center ↥↑Q.
    have ht_2central : IsPCentral 2 t :=
      ⟨ht_ne_one, Q, zQ, z.2, rfl⟩
    -- ⟨x⟩ s-subgroup, nontrivial.
    have hX_pgroup : IsPGroup s (Subgroup.zpowers x) := by
      rw [← hp₀_eq_s]
      apply IsPGroup.of_card (n := 1)
      rw [pow_one, Nat.card_zpowers, hx_ord]
    have hX_ne_bot : Subgroup.zpowers x ≠ ⊥ :=
      fun h => hx_ne_one (Subgroup.zpowers_eq_bot.mp h)
    -- t normalizes ⟨x⟩: conjugation by t (= t⁻¹) sends x ↦ t x t⁻¹ = t x t = x⁻¹,
    -- so it maps ⟨x⟩ into ⟨x⁻¹⟩ = ⟨x⟩, and likewise the reverse.
    have ht_inv : t⁻¹ = t := by
      rw [inv_eq_iff_mul_eq_one]; exact ht_sq
    -- t x t⁻¹ = x⁻¹.
    have hconj : t * x * t⁻¹ = x⁻¹ := by rw [ht_inv]; exact hxt
    -- x⁻¹ ∈ ⟨x⟩, hence (x⁻¹)^k ∈ ⟨x⟩ for all k.
    have hxinv_mem : ∀ k : ℤ, (x⁻¹) ^ k ∈ Subgroup.zpowers x := fun k =>
      (Subgroup.zpowers x).zpow_mem ((Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x)) k
    have ht_norm : t ∈ Subgroup.normalizer (Subgroup.zpowers x) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨fun hw => ?_, fun hw => ?_⟩
      · -- w ∈ ⟨x⟩ ⇒ t w t⁻¹ ∈ ⟨x⟩.
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        have h2 : t * x ^ k * t⁻¹ = (x⁻¹) ^ k := by
          rw [← conj_zpow (a := t) (b := x) (i := k), hconj]
        rw [h2]; exact hxinv_mem k
      · -- t w t⁻¹ ∈ ⟨x⟩ ⇒ w ∈ ⟨x⟩, via w = t⁻¹ (t w t⁻¹) t = t (t w t⁻¹) t⁻¹.
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
        -- t w t⁻¹ = x^k ⇒ w = t⁻¹ x^k t.  With t⁻¹ = t: w = t x^k t⁻¹ = (x⁻¹)^k.
        have hw_eq : w = t * x ^ k * t⁻¹ := by
          have : t * w * t⁻¹ = x ^ k := hk.symm
          calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
            _ = t * (t * w * t⁻¹) * t⁻¹ := by rw [ht_inv]
            _ = t * x ^ k * t⁻¹ := by rw [this]
        have h3 : t * x ^ k * t⁻¹ = (x⁻¹) ^ k := by
          rw [← conj_zpow (a := t) (b := x) (i := k), hconj]
        rw [hw_eq, h3]; exact hxinv_mem k
    exact step6_qCentral_not_normalizes_nontrivial_pSubgroup (p := s) (q := 2)
      (Ne.symm hrs) hcard hH_nsol hSubgroupsSolvable ht_2central hX_ne_bot hX_pgroup ht_norm
  refine ⟨?_, ?_⟩
  · -- p = 2: instantiate key with r := p (= 2), s := q.  |H| = q^b * p^a.
    intro hp2
    exact key p q hpq b a (by rw [hH_card]; ring) hp2
  · -- q = 2: instantiate key with r := q (= 2), s := p.  |H| = p^a * q^b = hH_card.
    intro hq2
    exact key q p (Ne.symm hpq) a b hH_card hq2

/-! ### §7D Step 8 — normal `J` for `p`-type maximals (Isaacs L4045-4063)

Helper lemmas toward discharging Step 8 (the `normal_J` hypotheses for `M`). -/


/-- **§7D Step 8 helper** — `2 ∤ |M|` for a subgroup `M` of a simple `p^a q^b`
group with `p, q` both odd.  Hence Sylow-`2` subgroups of `M` are trivial. -/
theorem two_not_dvd_card_subgroup_of_odd_primes
    {H : Type*} [Group H] [Finite H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (_hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (M : Subgroup H) :
    ¬ (2 : ℕ) ∣ Nat.card ↥M := by
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  intro h2_dvd
  have h2_dvd_H : (2 : ℕ) ∣ Nat.card H := h2_dvd.trans M.card_subgroup_dvd_card
  rw [hH_card] at h2_dvd_H
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2_dvd_H with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp_prime).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  · exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq_prime).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm

/-- **§7D Step 8 helper** — Sylow-`2` subgroups of `M` are abelian (in fact
trivial) when `2 ∤ |M|`.  Phrased as the `normal_J` hypothesis. -/
theorem sylow2_abelian_of_two_not_dvd
    {M : Type*} [Group M] [Finite M]
    (h2 : ¬ (2 : ℕ) ∣ Nat.card M) :
    ∀ S : Subgroup M, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S hS x y
  -- `S` is a `2`-group; `|S| ∣ |M|`; since `2 ∤ |M|`, `|S| = 1`, so `S` is trivial.
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hS_dvd : Nat.card ↥S ∣ Nat.card M := S.card_subgroup_dvd_card
  have hn0 : n = 0 := by
    by_contra hne
    exact h2 ((hn ▸ dvd_pow_self 2 hne).trans hS_dvd)
  have hS_card_one : Nat.card ↥S = 1 := by rw [hn, hn0, pow_zero]
  haveI : Subsingleton ↥S := Nat.card_eq_one_iff_unique.mp hS_card_one |>.1
  exact Subsingleton.elim (x * y) (y * x)

/-- **§7D Step 8 — fifth normal-J hypothesis** (Isaacs L4055-4063): for a
`p`-type maximal `M` and `S ∈ Syl_p(M)`, the centralizer of `Z(S)` in `M`
is exactly `S`: `C_M(Z(S)) = S`.

Textbook proof: `S ⊆ C_M(Z(S))` always.  For the reverse it suffices that
`C_M(Z(S))` is a `p`-group (a `p`-subgroup of `M` containing the Sylow `S` must
equal `S`).  Otherwise an order-`q` element `y ∈ C_M(Z(S))` gives a nontrivial
`q`-subgroup `Y = ⟨y⟩` normalized by `Z(S)`; choosing `P ∈ Syl_p(H)` with
`S = M ∩ P` and `M = N_H(O_p(M))`, the nontrivial center `Z(P)` lies in
`M ∩ P = S` and centralizes `S`, hence `Z(S)` contains a `p`-central element `x`
of `H`.  Then `x` normalizes `Y`, contradicting Step 6 (with `p, q` swapped). -/
theorem step8_centralizer_center_eq_sylow
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_pType : IsPType p M)
    (S : Sylow p ↥M) :
    Subgroup.centralizer
      (((Subgroup.center (S : Subgroup ↥M)).map (S : Subgroup ↥M).subtype) : Set ↥M)
      = (S : Subgroup ↥M) := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  -- `p ∣ |H|`, `q ∣ |H|`.
  obtain ⟨hp_dvd, hq_dvd⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  -- Abbreviations.
  set ZS : Subgroup ↥M :=
    (Subgroup.center (S : Subgroup ↥M)).map (S : Subgroup ↥M).subtype with hZS_def
  set C : Subgroup ↥M := Subgroup.centralizer (ZS : Set ↥M) with hC_def
  -- (A) `S ≤ C_M(Z(S))`: every `s ∈ S` commutes with `Z(S)`.
  have hS_le_C : (S : Subgroup ↥M) ≤ C := by
    intro s hs
    rw [hC_def, Subgroup.mem_centralizer_iff]
    intro z hz
    -- `z ∈ Z(S).map subtype`: `z = ↑z₀` with `z₀ ∈ center S`.
    obtain ⟨z₀, hz₀_center, rfl⟩ := hz
    -- `z₀` central in `S` ⇒ commutes with `⟨s, hs⟩`.
    have := (Subgroup.mem_center_iff.mp hz₀_center) ⟨s, hs⟩
    -- push to `↥M`.
    have h2 := congrArg (Subgroup.subtype (S : Subgroup ↥M)) this
    simpa [mul_comm] using h2.symm
  -- (B) `C` is a `p`-group.  Suppose not, and derive a contradiction via Step 6.
  have hC_pgroup : IsPGroup p C := by
    by_contra hC_not_p
    -- `q ∣ |C|`: a prime `r ∣ |C|` with `r ≠ p` must be `q` (since `|C| ∣ |M| ∣ p^a q^b`).
    -- Some prime `r ∣ |C|` is `≠ p` (else `C` would be a `p`-group).
    have hq_dvd_C : q ∣ Nat.card ↥C := by
      by_contra hq_ndvd
      -- Every prime factor of `|C|` is `p`, so `C` is a `p`-group — contradiction.
      apply hC_not_p
      apply OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton (G := ↥M) (p := p)
      intro r hr
      obtain ⟨hr_prime, hr_dvd_C, _⟩ := Nat.mem_primeFactors.mp hr
      have hr_dvd_M : r ∣ Nat.card ↥M := hr_dvd_C.trans C.card_subgroup_dvd_card
      have hr_dvd_paqb : r ∣ p ^ a * q ^ b := by
        rw [← hH_card]; exact hr_dvd_M.trans M.card_subgroup_dvd_card
      simp only [Set.mem_singleton_iff]
      rcases (Nat.Prime.dvd_mul hr_prime).mp hr_dvd_paqb with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hr_prime hp_prime).mp (hr_prime.dvd_of_dvd_pow h)
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp
          (hr_prime.dvd_of_dvd_pow h) ▸ hr_dvd_C) hq_ndvd
    -- Cauchy: an order-`q` element `y₀ ∈ C`.
    haveI : Fact q.Prime := ⟨hq_prime⟩
    obtain ⟨y₀, hy₀_ord⟩ := exists_prime_orderOf_dvd_card' q hq_dvd_C
    -- `Y₀ = ⟨y₀.val⟩` is a nontrivial `q`-subgroup of `↥M`; map to `H`.
    set yM : ↥M := (y₀ : ↥M) with hyM_def
    have hyM_ord : orderOf yM = q := by rw [hyM_def, Subgroup.orderOf_coe, hy₀_ord]
    have hyM_ne_one : yM ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at hyM_ord; exact hq_prime.ne_one hyM_ord.symm
    set Y₀ : Subgroup ↥M := Subgroup.zpowers yM with hY₀_def
    have hY₀_q : IsPGroup q Y₀ := by
      apply IsPGroup.of_card (n := 1)
      rw [pow_one, hY₀_def, Nat.card_zpowers, hyM_ord]
    set YH : Subgroup H := Y₀.map M.subtype with hYH_def
    have hYH_q : IsPGroup q YH := hY₀_q.map M.subtype
    -- `YH ≠ ⊥` (since `yM ≠ 1` maps to `↑yM ≠ 1`).
    have hYH_ne_bot : YH ≠ ⊥ := by
      rw [hYH_def, hY₀_def]
      intro hbot
      apply hyM_ne_one
      have : (M.subtype yM) = 1 := by
        have hmem : M.subtype yM ∈ (Subgroup.zpowers yM).map M.subtype :=
          ⟨yM, Subgroup.mem_zpowers yM, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem; exact hmem
      simpa using this
    -- Build the ambient `p`-central element `x ∈ Z(S) ⊆ M ∩ P` normalizing `YH`.
    -- (i) `M = N_H(V)` for `V = O_p(M).map subtype`.
    set K₀ : Subgroup ↥M := OddOrder.Isaacs.Ch01.opCore p ↥M with hK₀_def
    haveI hK₀_normal : K₀.Normal := by rw [hK₀_def]; infer_instance
    set V : Subgroup H := K₀.map M.subtype with hV_def
    have hV_ne_bot : V ≠ ⊥ := by
      intro hbot
      -- `V = ⊥` and `subtype` injective ⇒ `K₀ = ⊥`, contradicting `IsPType`.
      have hK₀_bot : K₀ = ⊥ := by
        rw [hV_def] at hbot
        exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp hbot
      exact hM_pType.2 hK₀_bot
    have hV_le_M : V ≤ M := by rw [hV_def]; exact Subgroup.map_subtype_le _
    have hM_norm_V : (M : Subgroup H) ≤ Subgroup.normalizer V := by
      -- `K₀ ⊴ ↥M` ⇒ `normalizer K₀ = ⊤`; map by `subtype` lands in `normalizer V`.
      have h1 : (Subgroup.normalizer (K₀ : Set ↥M)).map M.subtype
          ≤ Subgroup.normalizer ((K₀.map M.subtype : Subgroup H) : Set H) :=
        Subgroup.le_normalizer_map M.subtype
      rw [Subgroup.normalizer_eq_top_iff.mpr hK₀_normal] at h1
      have h3 : (⊤ : Subgroup ↥M).map M.subtype = M := by
        rw [← MonoidHom.range_eq_map, M.range_subtype]
      rw [h3] at h1
      rw [hV_def]
      exact h1
    have hM_eq_NV : Subgroup.normalizer V = M :=
      maximal_eq_normalizer_of_M_normalizes hM_pType.1 hV_ne_bot hV_le_M hM_norm_V
    -- (ii) `S_H := S.map subtype` extends to `P_H ∈ Syl_p(H)`.
    set SH : Subgroup H := (S : Subgroup ↥M).map M.subtype with hSH_def
    have hSH_p : IsPGroup p SH := S.isPGroup'.map M.subtype
    obtain ⟨PH, hSH_le_PH⟩ := IsPGroup.exists_le_sylow hSH_p
    have hPH_ne_bot : (PH : Subgroup H) ≠ ⊥ := Sylow.ne_bot_of_dvd_card hp_dvd PH
    -- (iii) `V ≤ SH ≤ PH` (since `K₀ = O_p(↥M) ≤ S`).
    have hV_le_SH : V ≤ SH := by
      rw [hV_def, hSH_def]
      exact Subgroup.map_mono (hK₀_def ▸ OddOrder.Isaacs.Ch01.opCore_le S)
    have hV_le_PH : V ≤ (PH : Subgroup H) := hV_le_SH.trans hSH_le_PH
    -- (iv) Nontrivial `Z(PH)` element `x`, `p`-central.
    haveI : Nontrivial ↥(PH : Subgroup H) :=
      (PH : Subgroup H).nontrivial_iff_ne_bot.mpr hPH_ne_bot
    have hPHpg : IsPGroup p ↥(PH : Subgroup H) := PH.isPGroup'
    have hZPH_nt : Nontrivial (Subgroup.center ↥(PH : Subgroup H)) := hPHpg.center_nontrivial
    obtain ⟨⟨⟨x, hx_mem_PH⟩, hx_center⟩, hx_ne_one⟩ :=
      exists_ne (1 : Subgroup.center ↥(PH : Subgroup H))
    have hx_ne_one' : x ≠ 1 := by
      intro h1; apply hx_ne_one; apply Subtype.ext; apply Subtype.ext; exact h1
    have hx_pcentral : IsPCentral p x := ⟨hx_ne_one', PH, ⟨x, hx_mem_PH⟩, hx_center, rfl⟩
    -- (v) `x ∈ M` (since `x ∈ Z(PH) ⊆ C_H(V) ⊆ N_H(V) = M`).
    have hx_centralizes_V : x ∈ Subgroup.centralizer (V : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv_PH : v ∈ (PH : Subgroup H) := hV_le_PH hv
      have hcomm := (Subgroup.mem_center_iff.mp hx_center) ⟨v, hv_PH⟩
      have := congrArg (Subgroup.subtype (PH : Subgroup H)) hcomm
      simpa [Subgroup.coe_mul] using this
    have hx_in_NV : x ∈ Subgroup.normalizer V := centralizer_le_normalizer V hx_centralizes_V
    have hx_in_M : x ∈ M := hM_eq_NV ▸ hx_in_NV
    -- (vi) `S = PH.subgroupOf M` (a `p`-subgroup of `↥M` containing the Sylow `S`).
    set xM : ↥M := ⟨x, hx_in_M⟩ with hxM_def
    have hPH_subOf_p : IsPGroup p ((PH : Subgroup H).subgroupOf M) :=
      hPHpg.comap_subtype
    have hS_le_PH_subOf : (S : Subgroup ↥M) ≤ (PH : Subgroup H).subgroupOf M := by
      intro s hs
      -- `↑s ∈ SH ≤ PH`.
      have : M.subtype s ∈ SH := ⟨s, hs, rfl⟩
      exact hSH_le_PH this
    have hS_eq : (PH : Subgroup H).subgroupOf M = (S : Subgroup ↥M) :=
      S.is_maximal' hPH_subOf_p hS_le_PH_subOf
    -- `xM ∈ S` since `↑xM = x ∈ PH`, i.e. `xM ∈ PH.subgroupOf M = S`.
    have hxM_in_S : xM ∈ (S : Subgroup ↥M) := by
      rw [← hS_eq, Subgroup.mem_subgroupOf]; exact hx_mem_PH
    -- (vii) `xM ∈ Z(S)`: `xM` centralizes `S` because `x ∈ Z(PH)` centralizes `PH ⊇ SH`.
    have hxM_center_S : (⟨xM, hxM_in_S⟩ : ↥(S : Subgroup ↥M)) ∈
        Subgroup.center (S : Subgroup ↥M) := by
      rw [Subgroup.mem_center_iff]
      intro s
      apply Subtype.ext
      apply Subtype.ext
      -- Reduce to commutation in `H`: `x * ↑s = ↑s * x`.
      have hs_PH : M.subtype (s : ↥M) ∈ (PH : Subgroup H) := by
        have : M.subtype (s : ↥M) ∈ SH := ⟨(s : ↥M), s.2, rfl⟩
        exact hSH_le_PH this
      have hcomm := (Subgroup.mem_center_iff.mp hx_center) ⟨M.subtype (s : ↥M), hs_PH⟩
      have hcomm' := congrArg (Subgroup.subtype (PH : Subgroup H)) hcomm
      simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at hcomm'
      -- `hcomm' : x * ↑s = ↑s * x`; goal is `↑s * x = x * ↑s`.
      simpa [Subgroup.coe_mul, hxM_def] using hcomm'
    have hxM_in_ZS : xM ∈ ZS :=
      ⟨⟨xM, hxM_in_S⟩, hxM_center_S, rfl⟩
    -- (viii) `xM` centralizes `yM` (since `yM ∈ C = C_M(Z(S))` and `xM ∈ Z(S)`).
    have hyM_in_C : yM ∈ C := y₀.2
    have hxM_comm_yM : x * M.subtype yM = M.subtype yM * x := by
      rw [hC_def, Subgroup.mem_centralizer_iff] at hyM_in_C
      have hcomm := hyM_in_C xM hxM_in_ZS
      -- `hcomm : xM * yM = yM * xM` in `↥M`; push to `H`.
      have := congrArg (Subgroup.subtype M) hcomm
      simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at this
      -- `↑xM = x`.
      simpa [hxM_def] using this
    -- (ix) `x` centralizes `↑yM`, hence `x ∈ N_H(YH)`.
    have hx_norm_YH : x ∈ Subgroup.normalizer YH := by
      apply centralizer_le_normalizer YH
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [hYH_def] at hw
      obtain ⟨w₀, hw₀_mem, rfl⟩ := hw
      -- `w₀ ∈ ⟨yM⟩`, so `w₀ = yM ^ k`; `x` commutes with `↑yM` ⇒ with `↑w₀`.
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw₀_mem
      -- `M.subtype (yM ^ k) = (M.subtype yM) ^ k`; `x` commutes with `M.subtype yM`.
      rw [map_zpow]
      -- goal: `(M.subtype yM)^k * x = x * (M.subtype yM)^k`.
      have hcx : Commute x (M.subtype yM) := hxM_comm_yM
      exact (hcx.zpow_right k).symm
    -- (x) Step 6 swapped: `x` `p`-central normalizing nontrivial `q`-subgroup `YH` ⇒ False.
    exact step6_qCentral_not_normalizes_nontrivial_pSubgroup (p := q) (q := p) (a := b) (b := a)
      (Ne.symm hpq) (by rw [hH_card]; ring) hH_nsol hSubgroupsSolvable hx_pcentral
      hYH_ne_bot hYH_q hx_norm_YH
  -- (C) `C` is a `p`-subgroup of `↥M` containing the Sylow `S`, hence `C = S`.
  exact S.is_maximal' hC_pgroup hS_le_C

/-- **§7D Step 8 — full Sylow** (Isaacs L4060-4063): for a `p`-type maximal `M`
and `S ∈ Syl_p(M)`, the image `S.map subtype` is a *full* Sylow `p`-subgroup of
the ambient group `H`.

Textbook proof: by the first part of Step 8, `J(S) ⊴ M`, and since `M` is
maximal with `J(S) ≤ M` nontrivial and `M`-normalized, `N_H(J(S)) = M`.  If
`S_H := S.map subtype` were not a full Sylow of `H`, then `S_H < T` for a
`p`-subgroup `T` (take `T = N_{P_H}(S_H)` for `P_H ∈ Syl_p(H)` containing `S_H`,
which strictly contains `S_H` by the normalizer condition for the nilpotent
group `P_H`); as `J(S_H)` is characteristic in `S_H`, `T` normalizes `J(S_H)`,
so `T ⊆ N_H(J(S_H)) = M`, making `T` a `p`-subgroup of `M` containing the Sylow
`S = M ∩ P_H` — but `T > S_H`, contradiction.  Hence `S_H = P_H` is a full
Sylow. -/
theorem step8_sylow_full
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (_hpq : p ≠ q)
    {a b : ℕ} (_hH_card : Nat.card H = p ^ a * q ^ b)
    (_hH_nsol : ¬ IsSolvable H)
    (_hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_pType : IsPType p M)
    (S : Sylow p ↥M)
    (hJ_normal : (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal) :
    ((S : Subgroup ↥M).map M.subtype) ∈
      Set.range (fun P : Sylow p H => (P : Subgroup H)) := by
  classical
  have hp_prime : p.Prime := Fact.out
  -- `M ≠ ⊥`; `O_p(↥M) ≠ ⊥`.
  have hOp_ne_bot : OddOrder.Isaacs.Ch01.opCore p ↥M ≠ ⊥ := hM_pType.2
  -- `SH := S.map subtype`, a `p`-group; extend to `PH ∈ Syl_p(H)`.
  set SH : Subgroup H := (S : Subgroup ↥M).map M.subtype with hSH_def
  have hSH_p : IsPGroup p SH := S.isPGroup'.map M.subtype
  obtain ⟨PH, hSH_le_PH⟩ := IsPGroup.exists_le_sylow hSH_p
  -- `SH ≠ ⊥` (since `O_p(↥M) ≤ S`, `O_p(↥M).map subtype ≤ SH` nontrivial).
  have hSH_ne_bot : SH ≠ ⊥ := by
    rw [hSH_def]
    intro hbot
    apply hOp_ne_bot
    have hOp_le_S : OddOrder.Isaacs.Ch01.opCore p ↥M ≤ (S : Subgroup ↥M) :=
      OddOrder.Isaacs.Ch01.opCore_le S
    have : (OddOrder.Isaacs.Ch01.opCore p ↥M).map M.subtype = ⊥ :=
      le_bot_iff.mp ((Subgroup.map_mono hOp_le_S).trans (le_of_eq hbot))
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp this
  -- `J(SH) = (J S).map subtype`.
  have hJSH : Subgroup.thompsonJ SH p = (Subgroup.thompsonJ (S : Subgroup ↥M) p).map M.subtype :=
    Subgroup.thompsonJ_map_of_injective M.subtype_injective (S : Subgroup ↥M) p
  -- `J(SH) ≠ ⊥`, `J(SH) ≤ M`.
  have hJSH_ne_bot : Subgroup.thompsonJ SH p ≠ ⊥ := Subgroup.thompsonJ_ne_bot hSH_p hSH_ne_bot
  have hJSH_le_M : Subgroup.thompsonJ SH p ≤ M :=
    (Subgroup.thompsonJ_le SH p).trans (hSH_def ▸ Subgroup.map_subtype_le _)
  -- `M ≤ N_H(J(SH))` from `J(S) ⊴ M` (the image is M-conjugation-invariant).
  have hM_norm_JSH : (M : Subgroup H) ≤ Subgroup.normalizer (Subgroup.thompsonJ SH p) := by
    have h1 : (Subgroup.normalizer (Subgroup.thompsonJ (S : Subgroup ↥M) p)).map M.subtype
        ≤ Subgroup.normalizer ((Subgroup.thompsonJ (S : Subgroup ↥M) p).map M.subtype) :=
      Subgroup.le_normalizer_map M.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr hJ_normal] at h1
    have h3 : (⊤ : Subgroup ↥M).map M.subtype = M := by
      rw [← MonoidHom.range_eq_map, M.range_subtype]
    rw [h3] at h1
    rw [hJSH]; exact h1
  -- `N_H(J(SH)) = M` (maximality).
  have hNJSH_eq_M : Subgroup.normalizer (Subgroup.thompsonJ SH p) = M :=
    maximal_eq_normalizer_of_M_normalizes hM_pType.1 hJSH_ne_bot hJSH_le_M hM_norm_JSH
  -- `S = PH.subgroupOf M`, i.e. `SH = M ⊓ PH`.
  have hPH_subOf_p : IsPGroup p ((PH : Subgroup H).subgroupOf M) := PH.isPGroup'.comap_subtype
  have hS_le_PH_subOf : (S : Subgroup ↥M) ≤ (PH : Subgroup H).subgroupOf M := by
    intro s hs
    have : M.subtype s ∈ SH := ⟨s, hs, rfl⟩
    exact hSH_le_PH this
  have hS_eq : (PH : Subgroup H).subgroupOf M = (S : Subgroup ↥M) :=
    S.is_maximal' hPH_subOf_p hS_le_PH_subOf
  -- Goal: `SH = PH`.  Suffices, then `SH = ↑PH ∈ range`.
  suffices hSH_eq : SH = (PH : Subgroup H) by exact ⟨PH, hSH_eq.symm⟩
  -- Show `SH = PH` by `le_antisymm`; `≤` is `hSH_le_PH`.
  refine le_antisymm hSH_le_PH ?_
  by_contra hPH_not_le
  -- `SH < PH`; use the normalizer condition in the nilpotent `p`-group `↥PH`.
  have hSH_lt_PH : SH < (PH : Subgroup H) := lt_of_le_of_ne hSH_le_PH (by
    intro h; exact hPH_not_le (le_of_eq h.symm))
  -- Work inside `↥PH`: `SH.subgroupOf PH < ⊤`.
  haveI : Group.IsNilpotent ↥(PH : Subgroup H) := PH.isPGroup'.isNilpotent
  have hNC : NormalizerCondition ↥(PH : Subgroup H) :=
    normalizerCondition_of_isNilpotent (G := ↥(PH : Subgroup H))
  have hSH_subOf_lt_top : SH.subgroupOf (PH : Subgroup H) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact absurd (le_antisymm hSH_le_PH htop) (by
      intro h; exact hPH_not_le (le_of_eq h.symm))
  -- `SH.subgroupOf PH < N(SH.subgroupOf PH)`.
  have hlt := hNC (SH.subgroupOf (PH : Subgroup H)) hSH_subOf_lt_top
  -- Get `t : ↥PH` with `t ∈ N(SH.subgroupOf PH)`, `t ∉ SH.subgroupOf PH`.
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt hlt
  -- `↑t ∈ N_H(SH)` (transport normalizer), `↑t ∉ SH`.
  rw [← Subgroup.subgroupOf_normalizer_eq hSH_le_PH, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  set tH : H := (t : H) with htH_def
  -- `tH` normalizes `J(SH)` (since `tH ∈ N_H(SH)`), so `tH ∈ N_H(J(SH)) = M`.
  have htH_norm_JSH : tH ∈ Subgroup.normalizer (Subgroup.thompsonJ SH p) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hconj : (Subgroup.thompsonJ SH p).map (MulAut.conj tH).toMonoidHom
        = Subgroup.thompsonJ SH p :=
      Subgroup.thompsonJ_map_conj_eq_of_mem_normalizer ht_norm
    constructor
    · intro hw
      have : tH * w * tH⁻¹ ∈ (Subgroup.thompsonJ SH p).map (MulAut.conj tH).toMonoidHom :=
        ⟨w, hw, rfl⟩
      rwa [hconj] at this
    · intro hw
      have : tH * w * tH⁻¹ ∈ (Subgroup.thompsonJ SH p).map (MulAut.conj tH).toMonoidHom := by
        rw [hconj]; exact hw
      obtain ⟨z, hz, hz_eq⟩ := this
      have hzw : w = z := by
        have heq : tH * z * tH⁻¹ = tH * w * tH⁻¹ := hz_eq
        -- cancel `tH⁻¹` on the right, then `tH` on the left.
        exact (mul_left_cancel (mul_right_cancel heq)).symm
      rw [hzw]; exact hz
  have htH_in_M : tH ∈ M := hNJSH_eq_M ▸ htH_norm_JSH
  -- `tH ∈ M ∩ PH`, so `(⟨tH, _⟩ : ↥M) ∈ PH.subgroupOf M = S`, i.e. `tH ∈ SH`.
  have htH_in_PH : tH ∈ (PH : Subgroup H) := t.2
  have htM_in_S : (⟨tH, htH_in_M⟩ : ↥M) ∈ (S : Subgroup ↥M) := by
    rw [← hS_eq, Subgroup.mem_subgroupOf]; exact htH_in_PH
  have htH_in_SH : tH ∈ SH := ⟨⟨tH, htH_in_M⟩, htM_in_S, rfl⟩
  -- But `t ∉ SH.subgroupOf PH` means `↑t ∉ SH`, contradiction.
  exact ht_not htH_in_SH

/-- **§7D Step 8** (Isaacs L4045-4063) — *normal `J` and full Sylow for a
`p`-type maximal*.

Let `M` be a `p`-type maximal subgroup and `S ∈ Syl_p(M)`.  Then `J(S) ⊴ M` and
`S` is a full Sylow `p`-subgroup of `G`.

Textbook proof: verify the five hypotheses of the normal-J theorem (Thm 7.6) on
the solvable group `M` — `p`-solvable, `p ≠ 2`, Sylow-2 abelian (trivial since
Step 7), `O_{p'}(M) = O_q(M) = 1` (Step 3), and `C_M(Z(S)) = S` (the latter via
Step 6: `Z(S)` contains a `p`-central element, so a hypothetical order-`q`
subgroup `Y ⊆ C_M(Z(S))` would be normalized by `Z(S)`, contradicting Step 6).
Then `J(S) ⊴ M` by Thm 7.6, and `S` full Sylow since `T > S` would give
`T ⊆ N_G(J(S)) = M`. -/
theorem step8_normalJ_and_fullSylow
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_pType : IsPType p M)
    (S : Sylow p ↥M) :
    (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal ∧
      IsPGroup p ((S : Subgroup ↥M).map M.subtype) ∧
      ((S : Subgroup ↥M).map M.subtype) ∈
        Set.range (fun P : Sylow p H => (P : Subgroup H)) := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  -- `M ≠ ⊥`, `M ≠ ⊤`, `M` solvable.
  have hM_ne_bot : M ≠ ⊥ := by
    intro hMbot
    have : Subsingleton ↥M := by rw [hMbot]; infer_instance
    exact hM_pType.2 (Subgroup.eq_bot_of_subsingleton _)
  have hM_ne_top : M ≠ ⊤ := hM_pType.1.ne_top
  haveI hM_sol : IsSolvable ↥M := hSubgroupsSolvable M hM_ne_top
  -- Step 7: both primes odd.
  obtain ⟨hp2, hq2⟩ := step7_p_ne_two_and_q_ne_two hpq hH_card hH_nsol hSubgroupsSolvable
  -- The five normal-J hypotheses on the group `↥M`.
  -- (1) `↥M` is `p`-solvable (it is solvable).
  haveI hM_pSep : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) ↥M := inferInstance
  -- (2) `p ≠ 2`.
  -- (3) Sylow-`2` subgroups abelian (trivial since `2 ∤ |M|`).
  have h2_not_dvd : ¬ (2 : ℕ) ∣ Nat.card ↥M :=
    two_not_dvd_card_subgroup_of_odd_primes hpq hH_card hp2 hq2 M
  have h2abelian : ∀ T : Subgroup ↥M, IsPGroup 2 T → ∀ x y : ↥T, x * y = y * x :=
    sylow2_abelian_of_two_not_dvd h2_not_dvd
  -- (4) `O_{p'}(M) = ⊥`.
  have h_oPiPrime : OddOrder.Isaacs.Ch03.oPiCore {r | r ≠ p} ↥M = ⊥ :=
    oPiCore_pPrime_eq_bot_of_isPType hpq hH_card hSubgroupsSolvable hM_pType
  -- The `normal_J` 4th hypothesis is phrased with `{q | q ≠ p}`; align the set.
  have h_oPiPrime' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} ↥M = ⊥ := h_oPiPrime
  -- (5) `C_M(Z(S)) = S`.
  have h_centralizer : Subgroup.centralizer
      (((Subgroup.center (S : Subgroup ↥M)).map (S : Subgroup ↥M).subtype) : Set ↥M)
      = (S : Subgroup ↥M) :=
    step8_centralizer_center_eq_sylow hpq hH_card hH_nsol hSubgroupsSolvable hM_pType S
  -- Conclude `J(S) ⊴ M` by the normal-J theorem.
  have hJ_normal : (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal :=
    normal_J S hp2 hM_pSep h2abelian h_oPiPrime' h_centralizer
  refine ⟨hJ_normal, ?_, ?_⟩
  · -- (2) `S.map M.subtype` is a `p`-group (image of the `p`-group `S`).
    exact (S.isPGroup'.map M.subtype)
  · -- (3) `S.map M.subtype` is a full Sylow `p`-subgroup of `H` (Step 8 second half).
    exact step8_sylow_full hpq hH_card hH_nsol hSubgroupsSolvable hM_pType S hJ_normal

/-! ### §7D Step 9 — terminal contradiction (Isaacs L4065-4093)

Step 9 is now **proven** (no longer an axiom).  We first land six reusable
helper lemmas, then `step9_core` (the WLOG-`|G|_p > |G|_q` argument), then the
dispatcher `step9_contradiction` that case-splits on which Sylow is larger. -/

/-- In a group of order `p^a q^b` (`p ≠ q` prime), a Sylow `p`-subgroup has
order `p^a`. -/
theorem sylow_p_card_eq_of_paqb
    {H : Type*} [Group H] [Finite H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (P : Sylow p H) :
    Nat.card (P : Subgroup H) = p ^ a := by
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  have hp_ne_dvd_q : ¬ p ∣ q := by
    rw [Nat.prime_dvd_prime_iff_eq hp_prime hq_prime]; exact hpq
  have hfact_p : (p ^ a * q ^ b).factorization p = a := by
    rw [Nat.factorization_mul (pow_ne_zero a hp_prime.ne_zero)
        (pow_ne_zero b hq_prime.ne_zero), Finsupp.add_apply,
        Nat.factorization_pow_self hp_prime,
        Nat.factorization_pow, Finsupp.smul_apply,
        Nat.factorization_eq_zero_of_not_dvd hp_ne_dvd_q, smul_eq_mul, mul_zero, add_zero]
  rw [P.card_eq_multiplicity, hH_card, hfact_p]

theorem sylow_inter_ne_bot_of_card_sq_gt
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (P : Sylow p H) (hcard : Nat.card H < Nat.card (P : Subgroup H) ^ 2)
    (S T : Sylow p H) :
    (S : Subgroup H) ⊓ (T : Subgroup H) ≠ ⊥ := by
  intro hbot
  have hS_card : Nat.card (S : Subgroup H) = Nat.card (P : Subgroup H) :=
    Nat.card_congr (Sylow.equiv S P).toEquiv
  have hT_card : Nat.card (T : Subgroup H) = Nat.card (P : Subgroup H) :=
    Nat.card_congr (Sylow.equiv T P).toEquiv
  have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card
    (S : Subgroup H) (T : Subgroup H)
  rw [hbot] at hprod
  simp only [Subgroup.card_bot, mul_one] at hprod
  rw [hS_card, hT_card] at hprod
  have hST_le : Nat.card ((↑(S : Subgroup H) : Set H) * (↑(T : Subgroup H) : Set H))
      ≤ Nat.card H :=
    Nat.card_le_card_of_injective (Subtype.val) Subtype.val_injective
  rw [hprod] at hST_le
  rw [sq] at hcard
  omega

/-- §7D Step 9: normalizer-grows. If `D < ↑S` for a finite `p`-group Sylow `S`,
then `D` is strictly contained in `N_H(D) ⊓ ↑S`. -/
theorem lt_normalizer_inf_sylow_of_lt
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (S : Sylow p H) {D : Subgroup H} (hD_lt : D < (S : Subgroup H)) :
    D < Subgroup.normalizer D ⊓ (S : Subgroup H) := by
  classical
  haveI : Group.IsNilpotent ↥(S : Subgroup H) := S.isPGroup'.isNilpotent
  have hNC : NormalizerCondition ↥(S : Subgroup H) :=
    normalizerCondition_of_isNilpotent (G := ↥(S : Subgroup H))
  -- D.subgroupOf S < ⊤.
  have hD_le : D ≤ (S : Subgroup H) := le_of_lt hD_lt
  have hsub_lt_top : D.subgroupOf (S : Subgroup H) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact (ne_of_lt hD_lt) (le_antisymm hD_le htop)
  have hlt := hNC (D.subgroupOf (S : Subgroup H)) hsub_lt_top
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hD_le, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  -- ↑t ∈ N_H(D) ⊓ ↑S, ↑t ∉ D.
  refine lt_of_le_of_ne (le_inf ?_ hD_le) ?_
  · -- D ≤ N_H(D).
    exact Subgroup.le_normalizer
  · intro heq
    apply ht_not
    have : (t : H) ∈ Subgroup.normalizer D ⊓ (S : Subgroup H) := ⟨ht_norm, t.2⟩
    rw [← heq] at this
    exact this

theorem exists_thompsonJ_ne
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H) :
    ∃ S T : Sylow p H,
      Subgroup.thompsonJ (S : Subgroup H) p ≠ Subgroup.thompsonJ (T : Subgroup H) p := by
  classical
  by_contra h_all_eq
  push Not at h_all_eq
  obtain ⟨hp_dvd, _⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := H)
  have hP_ne_bot : (P : Subgroup H) ≠ ⊥ := Sylow.ne_bot_of_dvd_card hp_dvd P
  set J₀ : Subgroup H := Subgroup.thompsonJ (P : Subgroup H) p with hJ₀_def
  have hJ₀_ne_bot : J₀ ≠ ⊥ := Subgroup.thompsonJ_ne_bot P.isPGroup' hP_ne_bot
  have hJ₀_pgroup : IsPGroup p J₀ :=
    P.isPGroup'.of_injective (Subgroup.inclusion (Subgroup.thompsonJ_le (P : Subgroup H) p))
      (Subgroup.inclusion_injective _)
  -- J₀ normal: conj g maps J₀ to J of the conjugate Sylow = J₀.
  have hJ₀_normal : J₀.Normal := by
    apply Subgroup.Normal.of_conjugate_fixed
    intro g
    change J₀.map (MulAut.conj g).toMonoidHom = J₀
    -- J₀.map (conj g) = J((↑P).map (conj g)) = J(↑(g • P)) = J(↑(g•P)) = J₀.
    have h1 : J₀.map (MulAut.conj g).toMonoidHom
        = Subgroup.thompsonJ ((P : Subgroup H).map (MulAut.conj g).toMonoidHom) p :=
      (Subgroup.thompsonJ_map_of_injective (MulAut.conj g).injective (P : Subgroup H) p).symm
    have h2 : (P : Subgroup H).map (MulAut.conj g).toMonoidHom
        = ((g • P : Sylow p H) : Subgroup H) :=
      Sylow.coe_subgroup_smul.symm
    rw [h1, h2, h_all_eq (g • P) P]
  have hOp_bot : OddOrder.Isaacs.Ch01.opCore p H = ⊥ :=
    opCore_eq_bot_of_simple_nonsolvable inferInstance hH_nsol
  have hJ₀_le_Op : J₀ ≤ OddOrder.Isaacs.Ch01.opCore p H :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hJ₀_pgroup
  rw [hOp_bot, le_bot_iff] at hJ₀_le_Op
  exact hJ₀_ne_bot hJ₀_le_Op

theorem exists_sylowM_of_full_sylow_le
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] {M : Subgroup H}
    (U : Sylow p H) (hUM : (U : Subgroup H) ≤ M) :
    ∃ UM : Sylow p ↥M, (UM : Subgroup ↥M).map M.subtype = (U : Subgroup H) := by
  classical
  have hUsub_p : IsPGroup p ((U : Subgroup H).subgroupOf M) := U.isPGroup'.comap_subtype
  obtain ⟨UM, hUsub_le⟩ := hUsub_p.exists_le_sylow
  refine ⟨UM, ?_⟩
  have hUM_p : IsPGroup p ((UM : Subgroup ↥M).map M.subtype) := UM.isPGroup'.map M.subtype
  have hmap_eq : ((U : Subgroup H).subgroupOf M).map M.subtype = (U : Subgroup H) := by
    rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, M.range_subtype]
    exact inf_eq_right.mpr hUM
  have hU_le : (U : Subgroup H) ≤ (UM : Subgroup ↥M).map M.subtype := by
    rw [← hmap_eq]; exact Subgroup.map_mono hUsub_le
  exact U.is_maximal' hUM_p hU_le

/-- §7D Step 9 bridge: for a `p`-type maximal `M` whose Sylow Thompson subgroups
are `M`-normal (Step 8), any two full Sylow `p`-subgroups of `H` lying in `M`
have the same Thompson subgroup. -/
theorem thompsonJ_eq_of_full_sylow_le_pType
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] {M : Subgroup H}
    (hStep8 : ∀ {N : Subgroup H} (_ : IsPType p N) (S : Sylow p ↥N),
      (Subgroup.thompsonJ (S : Subgroup ↥N) p).Normal)
    (hM_pType : IsPType p M)
    (U V : Sylow p H) (hUM : (U : Subgroup H) ≤ M) (hVM : (V : Subgroup H) ≤ M) :
    Subgroup.thompsonJ (U : Subgroup H) p = Subgroup.thompsonJ (V : Subgroup H) p := by
  classical
  obtain ⟨UM, hUM_eq⟩ := exists_sylowM_of_full_sylow_le U hUM
  obtain ⟨VM, hVM_eq⟩ := exists_sylowM_of_full_sylow_le V hVM
  -- J(↑U) = (J(↑UM)).map subtype.
  have hJU : Subgroup.thompsonJ (U : Subgroup H) p
      = (Subgroup.thompsonJ (UM : Subgroup ↥M) p).map M.subtype := by
    rw [← hUM_eq, Subgroup.thompsonJ_map_of_injective M.subtype_injective]
  have hJV : Subgroup.thompsonJ (V : Subgroup H) p
      = (Subgroup.thompsonJ (VM : Subgroup ↥M) p).map M.subtype := by
    rw [← hVM_eq, Subgroup.thompsonJ_map_of_injective M.subtype_injective]
  rw [hJU, hJV]
  -- Suffices: J(↑UM) = J(↑VM) in ↥M.
  suffices hJeq : Subgroup.thompsonJ (UM : Subgroup ↥M) p
      = Subgroup.thompsonJ (VM : Subgroup ↥M) p by rw [hJeq]
  -- UM, VM are M-conjugate.
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥M) UM VM
  -- J(↑UM) ⊴ M (Step 8).
  have hJUM_normal : (Subgroup.thompsonJ (UM : Subgroup ↥M) p).Normal := hStep8 hM_pType UM
  -- J(↑VM) = J(↑(g • UM)) = J((↑UM).map (conj g)) = (J(↑UM)).map (conj g) = J(↑UM).
  have h1 : Subgroup.thompsonJ (VM : Subgroup ↥M) p
      = Subgroup.thompsonJ ((UM : Subgroup ↥M).map (MulAut.conj g).toMonoidHom) p := by
    rw [← hg]; rfl
  haveI := hJUM_normal
  rw [h1, Subgroup.thompsonJ_map_of_injective (MulAut.conj g).injective]
  -- goal: J(↑UM) = (J(↑UM)).map (conj g); use normality (map = smul = self).
  exact (Subgroup.Normal.conj_smul_eq_self g (Subgroup.thompsonJ (UM : Subgroup ↥M) p)).symm

theorem step9_core
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    (hgt : q ^ b < p ^ a)
    (hStep8 : ∀ {M : Subgroup H} (_ : IsPType p M) (S : Sylow p ↥M),
      (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal) :
    False := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  obtain ⟨hp_dvd, hq_dvd⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  -- For P : Sylow p H, |P| = p^a, and |P|² > |H|.
  obtain ⟨P₀⟩ := Sylow.nonempty (p := p) (G := H)
  have hP₀_card : Nat.card (P₀ : Subgroup H) = p ^ a := sylow_p_card_eq_of_paqb hpq hH_card P₀
  have hcard_sq : Nat.card H < Nat.card (P₀ : Subgroup H) ^ 2 := by
    rw [hP₀_card, hH_card, sq]
    have hpa_pos : 0 < p ^ a := pow_pos hp_prime.pos a
    calc p ^ a * q ^ b < p ^ a * p ^ a := by
          exact (Nat.mul_lt_mul_left hpa_pos).mpr hgt
      _ = p ^ a * p ^ a := rfl
  -- (1) all p-Sylow pairs meet nontrivially.
  have hinter : ∀ S T : Sylow p H, (S : Subgroup H) ⊓ (T : Subgroup H) ≠ ⊥ := fun S T =>
    sylow_inter_ne_bot_of_card_sq_gt P₀ hcard_sq S T
  -- (2) ∃ pair with distinct J.
  obtain ⟨S₀, T₀, hJ_ne⟩ := exists_thompsonJ_ne hpq hH_card hH_nsol
  -- (3) maximize |↑S ⊓ ↑T| over distinct-J pairs.
  let distinctJ : Finset (Sylow p H × Sylow p H) :=
    Finset.univ.filter (fun ST =>
      Subgroup.thompsonJ (ST.1 : Subgroup H) p ≠ Subgroup.thompsonJ (ST.2 : Subgroup H) p)
  have hne : distinctJ.Nonempty := ⟨(S₀, T₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ_ne⟩⟩
  obtain ⟨STm, hSTm_mem, hSTm_max⟩ :=
    distinctJ.exists_max_image
      (fun ST => Nat.card ((ST.1 : Subgroup H) ⊓ (ST.2 : Subgroup H) : Subgroup H)) hne
  obtain ⟨S, T⟩ := STm
  have hST_Jne : Subgroup.thompsonJ (S : Subgroup H) p ≠ Subgroup.thompsonJ (T : Subgroup H) p :=
    (Finset.mem_filter.mp hSTm_mem).2
  have hmaxJ : ∀ R₁ R₂ : Sylow p H,
      Subgroup.thompsonJ (R₁ : Subgroup H) p ≠ Subgroup.thompsonJ (R₂ : Subgroup H) p →
      Nat.card ((R₁ : Subgroup H) ⊓ (R₂ : Subgroup H) : Subgroup H) ≤
      Nat.card ((S : Subgroup H) ⊓ (T : Subgroup H) : Subgroup H) := by
    intro R₁ R₂ hR
    exact hSTm_max (R₁, R₂) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR⟩)
  set D : Subgroup H := (S : Subgroup H) ⊓ (T : Subgroup H) with hD_def
  have hD_ne_bot : D ≠ ⊥ := hinter S T
  -- S ≠ T, ↑S ≠ ↑T.
  have hST_ne : S ≠ T := by intro h; exact hST_Jne (by rw [h])
  have hcoeST_ne : (S : Subgroup H) ≠ (T : Subgroup H) := by
    intro h; exact hST_ne (Sylow.ext h)
  -- D < ↑S (else ↑S ≤ ↑T, equal card ⇒ equal, contra).
  have hD_lt_S : D < (S : Subgroup H) := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hDS
    -- D = ↑S ⇒ ↑S ≤ ↑T ⇒ (equal card) ↑S = ↑T.
    have hS_le_T : (S : Subgroup H) ≤ (T : Subgroup H) := by
      rw [hD_def] at hDS; rw [← hDS]; exact inf_le_right
    have hcard_eq : Nat.card (S : Subgroup H) = Nat.card (T : Subgroup H) :=
      Nat.card_congr (Sylow.equiv S T).toEquiv
    exact hcoeST_ne (Subgroup.eq_of_le_of_card_ge hS_le_T (le_of_eq hcard_eq.symm))
  -- (5) N_H(D) < ⊤, maximal M ⊇ N_H(D).
  have hD_ne_top : D ≠ ⊤ := by
    intro h
    rw [h] at hD_lt_S
    exact (lt_irrefl _ (lt_of_lt_of_le hD_lt_S le_top))
  have hND_ne_top : Subgroup.normalizer (D : Set H) ≠ ⊤ := by
    intro hNtop
    have hD_normal : D.Normal := by rw [← Subgroup.normalizer_eq_top_iff]; exact hNtop
    rcases hD_normal.eq_bot_or_eq_top with hb | ht
    · exact hD_ne_bot hb
    · exact hD_ne_top ht
  obtain ⟨M, hM_max, hND_le⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom
      (Subgroup.normalizer (D : Set H))).resolve_left hND_ne_top
  -- D is a p-subgroup.
  have hD_pgroup : IsPGroup p D :=
    S.isPGroup'.of_injective (Subgroup.inclusion (le_of_lt hD_lt_S))
      (Subgroup.inclusion_injective _)
  -- (6) D < N_H(D) ⊓ ↑S.
  have hD_lt_NS : D < Subgroup.normalizer (D : Set H) ⊓ (S : Subgroup H) := by
    have := lt_normalizer_inf_sylow_of_lt S hD_lt_S
    -- normalizer of D (as subgroup) coerces to normalizer (D : Set H)
    exact this
  -- (7) M is p-type.
  -- M ≠ ⊥.
  have hD_le_M : D ≤ M := le_trans Subgroup.le_normalizer hND_le
  have hM_ne_bot : M ≠ ⊥ := by
    intro hbot; rw [hbot, le_bot_iff] at hD_le_M; exact hD_ne_bot hD_le_M
  -- p-central x centralizing D ⇒ x ∈ M.
  obtain ⟨x, hx_pcentral, hx_comm⟩ := exists_isPCentral_centralizing hp_dvd D hD_pgroup
  have hx_in_CD : x ∈ Subgroup.centralizer (D : Set H) := by
    rw [Subgroup.mem_centralizer_iff]; intro v hv; exact (hx_comm v hv).symm
  have hx_in_ND : x ∈ Subgroup.normalizer (D : Set H) := centralizer_le_normalizer D hx_in_CD
  have hx_in_M : x ∈ M := hND_le hx_in_ND
  have hM_pType : IsPType p M := by
    rcases maximal_isPType_xor_isQType hpq hH_card hSubgroupsSolvable hM_max hM_ne_bot with h | h
    · exact h.1
    · exfalso
      exact step5b_pType_no_qCentral (Ne.symm hpq) (a := b) (b := a)
        (by rw [hH_card]; ring) hH_nsol hSubgroupsSolvable h.1 hx_pcentral hx_in_M
  -- (8) Full Sylows U ⊇ M ⊓ ↑S and V ⊇ M ⊓ ↑T of H, contained in M.
  -- Generic: from a p-subgroup K ≤ M, get full Sylow W of H with ↑W ≤ M, K ≤ ↑W.
  have hfull : ∀ K : Subgroup H, K ≤ M → IsPGroup p K →
      ∃ W : Sylow p H, (W : Subgroup H) ≤ M ∧ K ≤ (W : Subgroup H) := by
    intro K hKM hK_p
    -- K.subgroupOf M is a p-group of ↥M; extend to Sylow W_M.
    have hKsub_p : IsPGroup p (K.subgroupOf M) := hK_p.comap_subtype
    obtain ⟨WM, hKsub_le⟩ := hKsub_p.exists_le_sylow
    -- (↑WM).map subtype is a full Sylow of H.
    obtain ⟨_, _, hWM_range⟩ :=
      step8_normalJ_and_fullSylow hpq hH_card hH_nsol hSubgroupsSolvable hM_pType WM
    obtain ⟨W, hW_eq⟩ := hWM_range
    simp only at hW_eq
    -- hW_eq : ↑W = (↑WM).map subtype
    refine ⟨W, ?_, ?_⟩
    · -- ↑W = (↑WM).map subtype ≤ M.
      rw [hW_eq]; exact Subgroup.map_subtype_le _
    · -- K ≤ ↑W: K = (K.subgroupOf M).map subtype ≤ (↑WM).map subtype = ↑W.
      rw [hW_eq]
      have hKmap : (K.subgroupOf M).map M.subtype = K := by
        rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, M.range_subtype]
        exact inf_eq_right.mpr hKM
      rw [← hKmap]; exact Subgroup.map_mono hKsub_le
  -- M ⊓ ↑S and M ⊓ ↑T are p-subgroups ≤ M.
  have hMS_p : IsPGroup p (M ⊓ (S : Subgroup H) : Subgroup H) :=
    S.isPGroup'.of_injective (Subgroup.inclusion (inf_le_right))
      (Subgroup.inclusion_injective _)
  have hMT_p : IsPGroup p (M ⊓ (T : Subgroup H) : Subgroup H) :=
    T.isPGroup'.of_injective (Subgroup.inclusion (inf_le_right))
      (Subgroup.inclusion_injective _)
  obtain ⟨U, hU_le_M, hMS_le_U⟩ := hfull (M ⊓ (S : Subgroup H)) inf_le_left hMS_p
  obtain ⟨V, hV_le_M, hMT_le_V⟩ := hfull (M ⊓ (T : Subgroup H)) inf_le_left hMT_p
  -- (9) ↑U ⊓ ↑S ⊇ N_H(D) ⊓ ↑S ⊋ D, similarly ↑V ⊓ ↑T ⊋ D.
  -- D < N_H(D) ⊓ ↑S ≤ M ⊓ ↑S ≤ ↑U; and N_H(D) ⊓ ↑S ≤ ↑U ⊓ ↑S, so D < ↑U ⊓ ↑S.
  have hNS_le_MS : Subgroup.normalizer (D : Set H) ⊓ (S : Subgroup H) ≤ M ⊓ (S : Subgroup H) :=
    inf_le_inf_right _ hND_le
  have hD_lt_US : D < (U : Subgroup H) ⊓ (S : Subgroup H) := by
    refine lt_of_lt_of_le hD_lt_NS ?_
    -- N_H(D) ⊓ ↑S ≤ ↑U ⊓ ↑S : left ≤ M⊓↑S ≤ ↑U; right ≤ ↑S.
    exact le_inf (le_trans hNS_le_MS hMS_le_U) inf_le_right
  have hD_lt_VT : D < (V : Subgroup H) ⊓ (T : Subgroup H) := by
    -- By symmetry: D = ↑S ⊓ ↑T = ↑T ⊓ ↑S; N_H(D) ⊓ ↑T ⊋ D.
    have hD_lt_T : D < (T : Subgroup H) := by
      refine lt_of_le_of_ne inf_le_right ?_
      intro hDT
      have hT_le_S : (T : Subgroup H) ≤ (S : Subgroup H) := by
        rw [hD_def] at hDT; rw [← hDT]; exact inf_le_left
      have hcard_eq : Nat.card (T : Subgroup H) = Nat.card (S : Subgroup H) :=
        Nat.card_congr (Sylow.equiv T S).toEquiv
      exact hcoeST_ne (Subgroup.eq_of_le_of_card_ge hT_le_S (le_of_eq hcard_eq.symm)).symm
    have hD_lt_NT : D < Subgroup.normalizer (D : Set H) ⊓ (T : Subgroup H) :=
      lt_normalizer_inf_sylow_of_lt T hD_lt_T
    have hNT_le_MT : Subgroup.normalizer (D : Set H) ⊓ (T : Subgroup H) ≤ M ⊓ (T : Subgroup H) :=
      inf_le_inf_right _ hND_le
    refine lt_of_lt_of_le hD_lt_NT ?_
    exact le_inf (le_trans hNT_le_MT hMT_le_V) inf_le_right
  -- (10) J(↑S) = J(↑U) and J(↑T) = J(↑V) by maximality of |D|.
  have hJS_eq_JU :
      Subgroup.thompsonJ (S : Subgroup H) p = Subgroup.thompsonJ (U : Subgroup H) p := by
    by_contra hne
    -- (S, U) distinct-J pair with |↑S ⊓ ↑U| > |D|, contradicting hmaxJ.
    have hle := hmaxJ S U hne
    have hcard_gt : Nat.card (D : Subgroup H)
        < Nat.card ((S : Subgroup H) ⊓ (U : Subgroup H) : Subgroup H) := by
      have : ((U : Subgroup H) ⊓ (S : Subgroup H))
          = ((S : Subgroup H) ⊓ (U : Subgroup H)) := inf_comm _ _
      rw [← this]
      exact Set.Finite.card_lt_card (Set.toFinite _) (hD_lt_US : (D : Set H) ⊂ _)
    omega
  have hJT_eq_JV :
      Subgroup.thompsonJ (T : Subgroup H) p = Subgroup.thompsonJ (V : Subgroup H) p := by
    by_contra hne
    have hle := hmaxJ T V hne
    have hcard_gt : Nat.card (D : Subgroup H)
        < Nat.card ((T : Subgroup H) ⊓ (V : Subgroup H) : Subgroup H) := by
      have : ((V : Subgroup H) ⊓ (T : Subgroup H))
          = ((T : Subgroup H) ⊓ (V : Subgroup H)) := inf_comm _ _
      rw [← this]
      exact Set.Finite.card_lt_card (Set.toFinite _) (hD_lt_VT : (D : Set H) ⊂ _)
    omega
  -- (11) J(↑U) = J(↑V) (both full Sylows ≤ M, M p-type).
  have hJU_eq_JV : Subgroup.thompsonJ (U : Subgroup H) p = Subgroup.thompsonJ (V : Subgroup H) p :=
    thompsonJ_eq_of_full_sylow_le_pType hStep8 hM_pType U V hU_le_M hV_le_M
  -- (12) J(↑S) = J(↑U) = J(↑V) = J(↑T), contradiction.
  exact hST_Jne (hJS_eq_JU.trans (hJU_eq_JV.trans hJT_eq_JV.symm))

/-- **§7D Step 9** (Isaacs L4065-4093) — *the terminal contradiction*.

Now a **theorem** (was an axiom).  Dispatches on whether `|G|_p > |G|_q` or
`|G|_q > |G|_p` (the two are unequal since `p^a = q^b` is impossible for distinct
primes with `a, b ≥ 1`), running `step9_core` with the prime whose Sylow is
larger.  Step 8 (`step8_normalJ_and_fullSylow`) and the partition
(`maximal_isPType_or_isQType`) are derived internally for that prime. -/
theorem step9_contradiction
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    (_hp2 : p ≠ 2) (_hq2 : q ≠ 2) :
    False := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  obtain ⟨hp_dvd, hq_dvd⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  -- a, b ≥ 1.
  have ha_pos : 0 < a := by
    by_contra h; push Not at h
    interval_cases a
    rw [pow_zero, one_mul] at hH_card
    -- p ∣ |H| = q^b ⇒ p = q.
    rw [hH_card] at hp_dvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp (hp_prime.dvd_of_dvd_pow hp_dvd))
  have hb_pos : 0 < b := by
    by_contra h; push Not at h
    interval_cases b
    rw [pow_zero, mul_one] at hH_card
    rw [hH_card] at hq_dvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp
      (hq_prime.dvd_of_dvd_pow hq_dvd)).symm
  -- p^a ≠ q^b.
  have hpa_ne_qb : p ^ a ≠ q ^ b := by
    intro heq
    -- p ∣ p^a = q^b ⇒ p = q.
    have : p ∣ q ^ b := heq ▸ dvd_pow_self p ha_pos.ne'
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp (hp_prime.dvd_of_dvd_pow this))
  have hH_card_swap : Nat.card H = q ^ b * p ^ a := by rw [hH_card]; ring
  rcases lt_or_gt_of_ne hpa_ne_qb with hlt | hgt
  · -- p^a < q^b: run core with (q, p) swapped.
    -- need hStep8 for q-type and partition for q.
    have hStep8' : ∀ {M : Subgroup H} (_ : IsPType q M) (S : Sylow q ↥M),
        (Subgroup.thompsonJ (S : Subgroup ↥M) q).Normal := by
      intro M hM S
      exact (step8_normalJ_and_fullSylow (Ne.symm hpq) hH_card_swap hH_nsol
        hSubgroupsSolvable hM S).1
    exact step9_core (Ne.symm hpq) hH_card_swap hH_nsol hSubgroupsSolvable hlt hStep8'
  · -- p^a > q^b: run core directly.
    have hStep8' : ∀ {M : Subgroup H} (_ : IsPType p M) (S : Sylow p ↥M),
        (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal := by
      intro M hM S
      exact (step8_normalJ_and_fullSylow hpq hH_card hH_nsol hSubgroupsSolvable hM S).1
    exact step9_core hpq hH_card hH_nsol hSubgroupsSolvable hgt hStep8'

/-- **§7D — no finite simple non-solvable group of order `p^a q^b`** (Isaacs
§7D, Thm 7.8 contradiction).

Now a **theorem**, threading the per-step decomposition:
* Step 2 (`step2_*`, proven) — complementary Sylow product.
* Step 3 (`step3_not_both_opCore_ne_bot`, axiom) + partition
  (`maximal_isPType_or_isQType`, proven) — `p`-type XOR `q`-type dichotomy.
* Steps 4-6 (`step4_*`, `step6_*`, axioms) — `q`-central elements normalize no
  nontrivial `p`-subgroup.
* Step 7 (`step7_p_ne_two_and_q_ne_two`, proven from Step 6) — both primes odd.
* Step 8 (`step8_normalJ_and_fullSylow`, axiom) — `J(S) ⊴ M` for `p`-type `M`.
* Step 9 (`step9_contradiction`, axiom) — terminal contradiction. -/
theorem noNonsolvableSimplePaQb.{u}
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (H : Type u) [Group H] [Finite H]
    (hH_simple : IsSimpleGroup H)
    (hH_nsol : ¬ IsSolvable H)
    (hH_order : ∃ a b : ℕ, Nat.card H ∣ p ^ a * q ^ b)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K) :
    False := by
  classical
  haveI := hH_simple
  -- Upgrade |H| ∣ p^a q^b to an exact equality |H| = p^a' q^b'.
  obtain ⟨a, b, hH_dvd⟩ := hH_order
  obtain ⟨a', b', hH_card⟩ : ∃ a' b' : ℕ, Nat.card H = p ^ a' * q ^ b' :=
    ⟨_, _, card_eq_pow_mul_pow_of_dvd Fact.out Fact.out hpq Nat.card_pos.ne' hH_dvd⟩
  -- Step 7: p, q both odd.
  obtain ⟨hp2, hq2⟩ :=
    step7_p_ne_two_and_q_ne_two hpq hH_card hH_nsol hSubgroupsSolvable
  -- Partition: every maximal (≠ ⊥) is p-type or q-type.
  have hPartition : ∀ {M : Subgroup H}, IsCoatom M → M ≠ ⊥ →
      IsPType p M ∨ IsQType q M := by
    intro M hM_max hM_ne_bot
    exact maximal_isPType_or_isQType hpq hH_card hM_max hM_ne_bot
      (hSubgroupsSolvable M hM_max.1)
  -- Step 8 packaged.
  have hStep8 : ∀ {M : Subgroup H} (_ : IsPType p M) (S : Sylow p ↥M),
      (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal := by
    intro M hM_pType S
    exact (step8_normalJ_and_fullSylow hpq hH_card hH_nsol hSubgroupsSolvable hM_pType S).1
  -- Step 9: terminal contradiction.
  exact step9_contradiction hpq hH_card hH_nsol hSubgroupsSolvable hp2 hq2

/-- **Isaacs Thm 7.8** (Burnside `p^a q^b` solvability).

> If `|G| = p^a * q^b` for primes `p, q`, then `G` is solvable.

The textbook proof (Isaacs p.219-222) is the character-free
**Goldschmidt-Bender-Matsuyama 9-step argument**: assume `G` is a minimum
counterexample (non-solvable group of minimum order `p^a q^b`).  Steps 1-3
establish that `G` is simple and identify maximal subgroups of `p`-type or
`q`-type; Steps 4-7 develop `p`-central element machinery and apply
Matsuyama 2.13 to force `p, q` odd; Step 8 applies the **normal-J theorem
(Thm 7.6)** to get `J(S) ⊴ M` for `S ∈ Syl_p(M)`; Step 9 derives a
contradiction from `J(S) ⊴ M` together with Thompson factorization
properties of `M`.

**Implementation strategy**: the actual 9-step argument is encapsulated in
the local axiom `noNonsolvableSimplePaQb` (issue 0032).  We carry out the
strong-induction-on-`Nat.card` reduction, peel off the simplicity reduction
via `isSimpleGroup_of_minCounterexample`, then invoke the axiom. -/
theorem burnside_p_pow_q_pow.{u}
    {G : Type u} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q)
    (hG_order : ∃ a b : ℕ, Nat.card G = p ^ a * q ^ b) :
    IsSolvable G := by
  classical
  -- Strong induction on `Nat.card` via an explicit motive over arbitrary finite
  -- groups whose order divides `|G|`.
  let motive : ℕ → Prop := fun n =>
    ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H ∣ Nat.card G → Nat.card H = n → IsSolvable H
  suffices hmain : motive (Nat.card G) by
    exact hmain G dvd_rfl rfl
  refine Nat.strong_induction_on (Nat.card G) ?_
  intro n ih H _ _ hH_dvd hH_card
  -- Apply the minimum-counterexample contradiction.
  by_contra hH_nsol
  have hG_pos : 0 < Nat.card G := Nat.card_pos
  have hH_pos : 0 < Nat.card H := Nat.pos_of_dvd_of_pos hH_dvd hG_pos
  -- Subgroup orders divide the ambient order; use Lagrange + IH.
  -- Every proper subgroup (not necessarily normal) is solvable.
  have hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K := by
    intro K hK_top
    have hK_dvd_H : Nat.card K ∣ Nat.card H := K.card_subgroup_dvd_card
    have hK_dvd_G : Nat.card K ∣ Nat.card G := hK_dvd_H.trans hH_dvd
    have hK_le : Nat.card K ≤ Nat.card H := Nat.le_of_dvd hH_pos hK_dvd_H
    have hK_ne : Nat.card K ≠ Nat.card H := fun h_eq =>
      hK_top (Subgroup.eq_top_of_card_eq _ h_eq)
    have hK_lt : Nat.card K < n :=
      (lt_of_le_of_ne hK_le hK_ne).trans_eq hH_card
    exact ih (Nat.card K) hK_lt K hK_dvd_G rfl
  -- Restriction of the above to normal proper subgroups.
  have hN_solvable :
      ∀ N : Subgroup H, N ≠ ⊤ → N.Normal → IsSolvable N := fun N hN _ =>
    hSubgroupsSolvable N hN
  -- Quotient orders divide the ambient order; use index-bound + IH.
  have hQ_solvable :
      ∀ (N : Subgroup H) [N.Normal], N ≠ ⊥ → IsSolvable (H ⧸ N) := by
    intro N hN_norm hN_bot
    have hQ_dvd_H : Nat.card (H ⧸ N) ∣ Nat.card H := N.card_quotient_dvd_card
    have hQ_dvd_G : Nat.card (H ⧸ N) ∣ Nat.card G := hQ_dvd_H.trans hH_dvd
    -- |H| = |H/N| * |N| with |N| ≥ 2 ⇒ |H/N| < |H|.
    have hN_card_two : 1 < Nat.card N := N.one_lt_card_iff_ne_bot.mpr hN_bot
    have hH_eq : Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hQ_pos : 0 < Nat.card (H ⧸ N) :=
      Nat.pos_of_dvd_of_pos hQ_dvd_H hH_pos
    have hQ_lt_H : Nat.card (H ⧸ N) < Nat.card H := by
      calc Nat.card (H ⧸ N)
          = Nat.card (H ⧸ N) * 1 := (Nat.mul_one _).symm
        _ < Nat.card (H ⧸ N) * Nat.card N :=
            Nat.mul_lt_mul_of_pos_left hN_card_two hQ_pos
        _ = Nat.card H := hH_eq.symm
    have hQ_lt : Nat.card (H ⧸ N) < n := hQ_lt_H.trans_eq hH_card
    exact ih (Nat.card (H ⧸ N)) hQ_lt (H ⧸ N) hQ_dvd_G rfl
  -- H is nontrivial: |H| = n.  If n = 1 then H is trivial which is solvable
  -- (contradicting hH_nsol).
  haveI hH_nontriv : Nontrivial H := by
    by_contra h_not_nontriv
    rw [not_nontrivial_iff_subsingleton] at h_not_nontriv
    exact hH_nsol inferInstance
  -- Step 1 reduction: H is simple.
  have hH_simple : IsSimpleGroup H :=
    isSimpleGroup_of_minCounterexample hH_nsol hN_solvable hQ_solvable
  -- Order divides p^a q^b: extract a',b' such that Nat.card H ∣ p^a' q^b'.
  obtain ⟨a, b, hG_card⟩ := hG_order
  have hH_dvd_paqb : ∃ a' b' : ℕ, Nat.card H ∣ p ^ a' * q ^ b' :=
    ⟨a, b, hG_card ▸ hH_dvd⟩
  -- Invoke the §7D core axiom.
  exact noNonsolvableSimplePaQb hpq H hH_simple hH_nsol hH_dvd_paqb
    hSubgroupsSolvable

end -- 7D

end OddOrder.Isaacs.Ch07
