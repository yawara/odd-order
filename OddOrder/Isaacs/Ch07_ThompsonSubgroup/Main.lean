/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import OddOrder.GroupTheory.ThompsonSubgroup
import OddOrder.Isaacs.Ch02_Subnormality

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
2. Lem 7.4 SL(2,q) — 独立小テーマ (先行章不要)
3. Lem 7.7 — Lem 2.17 拡張 (Ch.2 完成済から短い延長)
4. (Ch.3 §3D ✅ + Ch.4 §4D 完成後) Lem 7.3 → Thm 7.5 → Thm 7.6
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

/-! ### Lem 7.3 — GL(2,p) 補題 (statement 保留)

**Isaacs Lem 7.3** (mmd L3739):

> `G = GL(2,p)`, `p ≠ 2`, `P ⊆ G` p-subgroup, `P ⊆ N_G(L)`, `(|L|, p) = 1`,
> `L` の Sylow-2 abelian ⇒ `P ⊆ C_G(L)`.

**先行 def 依存**:
- `Mathlib.LinearAlgebra.GeneralLinearGroup` (= `GeneralLinearGroup 2 (ZMod p)`).
- `Aut(E) ≅ GL(n, ZMod p)` for E elementary abelian (新規, ノート設計判断 (3)).

**proof 戦略**: induction on `|L|` + Sylow + 7.4 (-I unique inv) + Hall-Higman 3.21
(Ch.3 §3D ✅ 完成済).

着手は Lem 7.4 + Hall-Higman 利用環境整備後. -/

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
  sorry

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

/-! ### Lem 7.7 — `N/C` 系の `p'`-quotient (statement 保留)

**Isaacs Lem 7.7** (mmd L3902):

> `N ⊴ G` が `p'`-subgroup, `P ⊆ G` が `p`-subgroup ⇒
> (a) `N_{G/N}(PN/N) = N_G(P)·N/N` = **Lem 2.17** (Ch.2 既完: `normalizer_map_of_coprime_kernel`)
> (b) **`C_{G/N}(PN/N) = C_G(P)·N/N`** (Ch.7 で新規)

**先行**: Ch.2 Lem 2.17 ✅ 完成済 (`OddOrder.Isaacs.Ch02.normalizer_map_of_coprime_kernel`).

**proof 戦略** (b): Lem 2.17 (a) の証明戦略を centralizer に並行翻訳 (correspondence
+ Sylow-style Frattini argument). 短い延長.

**先行章不要で着手可** (Ch.2 完成済). -/

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
