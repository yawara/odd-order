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

/-- **Isaacs Thm 7.6 Step 7** (axiomatized — mmd L3884-3892).

Under the running hypotheses (i)-(v), assume there exists `A ∈ E(P)` with
`A ⊄ O_p(G)`.  Then there is no such `A`: a contradiction.

This is the core combinatorial counting / action-extension argument of Thm 7.6;
the bridge lemmas above (Steps 2-6 + Step 8) reduce the unconditional `normal_J`
proof to this axiomatic step.

Will be discharged once the Goldschmidt-style counting argument over `E(P)`
combined with Ch.6 Thm 6.20 + Ch.4 Cor 4.35 is filled in.

TODO Step 7: discharge this axiom via the book's counting argument over `E(P)`. -/
axiom thompsonJ_le_opCore_of_normal_J_hypotheses
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
    Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G

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

**This unconditional version** uses the Step 7 axiom
(`thompsonJ_le_opCore_of_normal_J_hypotheses`) to bridge Steps 1-7, then applies
the Step 8 wrap-up (`normal_thompsonJ_of_le_opCore`).  Once Step 7 is discharged
the theorem becomes axiom-free. -/
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

/-- **Isaacs Thm 7.8** (Burnside `p^a q^b` solvability, conditional on 9-step argument).

The full theorem (Isaacs L3955) states:

> If `|G| = p^a * q^b` for primes `p, q`, then `G` is solvable.

The textbook proof (Isaacs p.219-222) is the character-free
**Goldschmidt-Bender-Matsuyama 9-step argument**: assume `G` is a minimum
counterexample (non-solvable group of minimum order `p^a q^b`).  Steps 1-7
establish that `G` is simple, picks a `p`-type maximal subgroup `M` containing a
Sylow `p`-subgroup `P`, and shows `¬(p = 2 ∨ q = 2)`.  Step 8 applies the
**normal-J theorem (Thm 7.6)** to get `J(S) ⊴ M` for `S ∈ Syl_p(M)`.  Step 9
derives a contradiction from `J(S) ⊴ M` together with Thompson factorization
properties of `M`.

**This formalization takes the contradiction at the minimum counterexample as a
forward-dependency hypothesis** (`hMinCounterexample`), universalized over any
finite group `H` whose order divides `|G| = p^a q^b`.  The 9-step
Goldschmidt-Bender-Matsuyama argument will discharge this hypothesis once
Thm 7.6 + `IsPType` / Thompson factorization machinery lands in §7D.

Given `hMinCounterexample`, the conclusion follows by **strong induction on
`Nat.card G`**: at any group `H` (of order dividing `|G|`), if `H` is not
solvable then by the induction hypothesis every proper normal subgroup `N ⊴ H`
is solvable (since `|N| < |H|`) and every quotient `H/N` with `N ≠ ⊥` is solvable
(since `|H/N| < |H|`).  Plugging into `hMinCounterexample` yields `False`. -/
theorem burnside_p_pow_q_pow.{u}
    {G : Type u} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (_hpq : p ≠ q)
    (_hG_order : ∃ a b : ℕ, Nat.card G = p ^ a * q ^ b)
    (hMinCounterexample :
       ∀ (H : Type u) [Group H] [Finite H],
         Nat.card H ∣ Nat.card G →
         (¬ IsSolvable H) →
         (∀ N : Subgroup H, N ≠ ⊤ → N.Normal → IsSolvable N) →
         (∀ (N : Subgroup H) [N.Normal], N ≠ ⊥ → IsSolvable (H ⧸ N)) →
         False) :
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
  have hN_solvable :
      ∀ N : Subgroup H, N ≠ ⊤ → N.Normal → IsSolvable N := by
    intro N hN_top _hN_norm
    have hN_dvd_H : Nat.card N ∣ Nat.card H := N.card_subgroup_dvd_card
    have hN_dvd_G : Nat.card N ∣ Nat.card G := hN_dvd_H.trans hH_dvd
    have hN_le : Nat.card N ≤ Nat.card H := Nat.le_of_dvd hH_pos hN_dvd_H
    -- |N| ≠ |H| since N ≠ ⊤ (in a finite group).
    have hN_ne : Nat.card N ≠ Nat.card H := fun h_eq =>
      hN_top (Subgroup.eq_top_of_card_eq _ h_eq)
    have hN_lt : Nat.card N < n :=
      (lt_of_le_of_ne hN_le hN_ne).trans_eq hH_card
    exact ih (Nat.card N) hN_lt N hN_dvd_G rfl
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
  exact hMinCounterexample H hH_dvd hH_nsol hN_solvable hQ_solvable

end -- 7D

end OddOrder.Isaacs.Ch07
