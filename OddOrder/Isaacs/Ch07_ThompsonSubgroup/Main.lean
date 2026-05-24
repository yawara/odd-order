/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import OddOrder.GroupTheory.ThompsonSubgroup
import OddOrder.Isaacs.Ch02_Subnormality
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03

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
4. 🚧 Lem 7.3 (statement + 証明 skeleton 配置, 本体は別 commit) → Thm 7.5 → Thm 7.6
5. (Ch.5 §5E 5.26 完成後) Thm 7.1
6. (上記完成後) Thm 7.8 Burnside

各 statement の def 系前提 (`HasNormalPComplement`, `GeneralLinearGroup` 引数法,
`Aut(E) ≅ GL(n,p)`) は実装時に決める.
-/

namespace OddOrder.Isaacs.Ch07

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

/-! ### Isaacs Lem 7.3 — GL(2,p) 補題 (formal statement + skeleton)

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

**現状**: statement + 証明戦略 docstring のみ. 各 step の実装 (P-invariant Sylow 取得,
Lem 4.29 適用, q=2 / q-odd 場合分け) は別 commit で fill in. -/

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
      -- TODO (次 commit):
      --   h. Q (Sylow q ↥L) を G_ambient (= GL(2,ZMod p)) の subgroup に持ち上げる.
      --   i. Q が C_L(P) に含まれないことを確認 (`q | |L : C_L(P)|` から).
      --   j. IH を Q ⊊ L に適用 ⇒ P ≤ C(Q), 矛盾で `Q = L`, L が q-群.
      --   k. `[L,P] < L` case: IH + Lem 4.29 で P ≤ C(L), 終了.
      --   l. `[L,P] = L` case: L ≤ SL(2,p) を導出.
      --   m. q = 2: Lem 7.4 + cyclic 2-群 ⇒ Aut 2-群 ⇒ done.
      --   n. q odd: |SL(2,p)| 因子化 + orbit counting で矛盾.
      sorry

/-- **Isaacs Lemma 7.3** ⭐ (GL(2,p) 補題). `p ≠ 2` prime, `P ≤ GL(2, ZMod p)`
p-subgroup が `L ≤ GL(2, ZMod p)` を normalize し, `(|L|, p) = 1` かつ `L` 内の
任意の 2-部分群が abelian ⇒ P は L を centralize.

**Sylow 2-subgroup abelian の hereditary form**: 仮説 `hL2abelian` は「L 内の任意の
2-部分群が abelian」と述べる. Isaacs 原本の「L の Sylow 2 が abelian」と同値だが
(任意の 2-部分群は Sylow 2 に含まれ, abelian 群の部分群は abelian), 帰納法
(IH 適用時の継承) で便利な形.

**proof skeleton** (詳細はファイル上部 §7A docstring 参照): `|L|`-strong induction を
[`lem73_aux`](#) で展開. 各 step (P-invariant Sylow, Lem 4.29 適用, q=2 / q-odd) は
別 commit で fill in. -/
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

着手は Lem 7.3 + Ch.6 6.11 完成後. -/

end -- 7A

/-! ## §7B: normal-J theorem (pp. 209-214) -/

section /- 7B: normal-J theorem -/

/-! ### Thm 7.6 — normal-J theorem ⭐⭐ (statement 保留)

**Isaacs Thm 7.6** (mmd L3832):

> (i) G p-solvable, (ii) `p ≠ 2`, (iii) Sylow-2 abelian, (iv) `O_{p'}(G) = 1`,
> (v) `P = C_G(Z(P))` ⇒ `J(P) ⊴ G`.

**= BG Theorem 6.2 の odd-order 等価版**. **FT クリティカル度 HIGHEST**: BG §6, §8,
§9, App.A で 7 ヶ所超で直接引用.

**proof 戦略** (8 Step, mmd L3832-3896): Thm 7.5 + Ch.6 **6.20** (abelian coprime
⟨C_N(a)⟩=N) + Ch.4 **4.35** (Ω₁ fixed) + Hall-Higman 3.21.

着手は Thm 7.5 + Ch.6 6.20 + Ch.4 4.35 完成後. -/

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

end -- 7C

/-! ## §7D: Burnside `p^a q^b` (pp. 219-222) -/

section /- 7D: Burnside p^a q^b -/

/-! ### Thm 7.8 — Burnside `p^a q^b` ⇒ solvable (statement 保留)

**Isaacs Thm 7.8** (mmd L3955):

> `|G| = p^a q^b` ⇒ G solvable.

**character 不使用** (Goldschmidt + Bender + Matsuyama, 9 Step proof).

**先行 dep**: Thm 7.6 normal-J + Ch.2 Thm **2.13 Baer** ✅ + Ch.4 Thm **4.33** (p-local).

BG/Peterfalvi 直接被引用無いので最後着手. Phase 1 完成度のため必須 (BG L2633 で
"we can obtain Burnside's `p^a q^b` very easily now" として言及). -/

end -- 7D

end OddOrder.Isaacs.Ch07
