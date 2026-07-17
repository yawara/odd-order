/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Module.ZMod
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import OddOrder.BG.Ch1_Preliminary.S02_Representations
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.GroupTheory.ElementaryAbelian
import OddOrder.GroupTheory.FrattiniPGroup
import OddOrder.GroupTheory.IsExtraspecial
import OddOrder.GroupTheory.IsMetacyclic
import OddOrder.GroupTheory.PRank
import OddOrder.GroupTheory.SCN
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main

/-!
# S04_SmallRankBasic

Prefix-split from `OddOrder.BG.Ch1_Preliminary.S04_PGroupsSmallRank` (2000-line limit, issue 0103 第
2 パス).
-/

/-!
# BG §4: p-Groups of Small Rank

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §4 (pp. 33-43), mmd
`references/bg/local-analysis.mmd` L1359-1788, **20 結果** (Lemma/Prop/Thm/Cor
4.1-4.20).

## 構造 (BG §4)

- **§4A** class ≤ 2/3 の冪・交換子 (Lemma 4.1-4.3)
- **§4B** SCN・normal `E_{p²}` の存在 (Prop 4.4-4.6)
- **§4C** rank ↔ SCN₃, `Ω₁` 構造 (Lemma 4.7-4.10)
- **§4D** Huppert metacyclic 判定 + operator (Prop 4.11, Thm 4.12)
- **§4E** `Aut R` の位数制約 + extraspecial (Lemma 4.13-4.15)
- **§4F** Blackburn 分類 (Thm 4.16)
- **§4G** solvable operator の導来部分群 (Lemma 4.17)
- **§4H** solvable odd group の構造定理 (Thm 4.18, Cor 4.19, Thm 4.20)

## Current status

本ファイルは §4 の **§4G (Lemma 4.17) の証明で必要な再利用補題**から着手する。
Lemma 4.17 (`A` solvable `p'`-operator, `r(R) ≤ 2`, `|A|` odd ⇒ `A'` は `p`-群)
の BG 原証明 (mmd L1706-1732) は次の 4 部品を組む:

1. (4.16) `C_A(H)` が `p`-群 (`H` = Thompson critical の `Ω₁(C)`).
   利用可能: `thompson_critical_omega` (`S01_Solvable`) が
   `IsPGroup p (autCentralizer H)` を供給する。
2. (4.17) `|H| ≤ p³` (Prop 4.8 — `r(R) ≤ 2` + exponent `p`).
   **未実装** (rank 理論 `pRank`/`m` が `OddOrder.GroupTheory.PRank` で def のみ)。
3. (4.18) `C := C_A(H/Φ(H))` が `p`-群 (Burnside Thm 1.8 で `C/C_A(H)` が `p`-群).
   Burnside は `burnside_operator` (`S01_Solvable`) で利用可能。
4. `m(V) = 2` のとき `Aut V ≅ GL(2,p)` で `(A/C)'` が `p`-群 (BG Thm 2.6).
   **本ファイルで供給** (`isPGroup_commutator_of_faithful_two_dim_charP`).

現状のゲートは (2) の Prop 4.8 + `m(V) ≤ 2` を与える rank 機構 (設計書 Wave 0)。
本ファイルでは部品 (4) = Blackburn 4.16 / Lemma 4.17 の `m(V) = 2` 分岐エンジン
であり Cor 4.19 でも直接引かれる「2 次元 faithful 表現 ⇒ 導来部分群が `p`-群」
を切り出して実装する。Lemma 4.17 本体は rank 機構の整備後に本ファイルへ追加する。

## References

- BG mmd `references/bg/local-analysis.mmd` L1359-1788 (Lemma 4.17 L1706-1732,
  Thm 2.6 L774-793, Cor 4.19 L1750-1762).
- Section note: `notes/bg/s04_pgroups_small_rank.md`,
  `notes/bg/s04_implementation_plan_2026_05_30.md`.
- BG Thm 2.6 (2 次元 faithful 表現): `OddOrder.BG.Ch1.S02.odd_two_dim_abelian`,
  `OddOrder.BG.Ch1.S02.odd_two_dim_sylow_abelian`
  (`OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`).
- BG Thm 1.13 (Thompson critical): `OddOrder.BG.Ch1.thompson_critical_omega`.
- BG Thm 1.8 (Burnside operator): `OddOrder.BG.Ch1.burnside_operator`.
-/

namespace OddOrder.BG.Ch1.S04

open OddOrder.BG.Ch1.S02

/-! ## §4F/§4G: 2 次元 faithful 表現の導来部分群 (Blackburn 4.16 / Lemma 4.17 の
`GL(2,p)` 分岐エンジン)

BG Theorem 4.16 の証明 (mmd L1732) と Lemma 4.17 の `m(V) = 2` の場合は
「`Aut V ≅ GL(2,p)` かつ `A/C` が `V` に faithful に作用するから, Theorem 2.6
により `(A/C)'` は `p`-群」と進む。Corollary 4.19 (mmd L1758) でも
「`G/C` が `U/V` に faithful かつ irreducible に作用するから `(G/C)'` は `p`-群」
として同じ帰結を用いる。

ここでは BG Thm 2.6(b) (`odd_two_dim_sylow_abelian`) を直接の再利用形
「奇数位数 `G` が標数 `p` の体上 2 次元 faithful 表現を持てば `G'` は `p`-群」
に整える。BG が `(A/C)'` を `p`-群と断ずる箇所はすべてこの形で読み替えられる。
-/

/-- **BG Theorem 2.6(b) の導来部分群形** (Blackburn 4.16 / Lemma 4.17 の `m(V)=2`
分岐エンジン, Cor 4.19 のエンジン).

奇数位数の有限群 `G` が標数 `p`(`p ∣ |G|`)の体 `F` 上で `2` 次元の faithful な
表現 `ρ` を持つとき, 導来部分群 `G'` (`commutator G`) は `p`-群である。

BG 原文では Lemma 4.17 (mmd L1732) と Cor 4.19 (mmd L1758) で
「`Aut V ≅ GL(2,p)` (resp. faithful irreducible on `U/V`) ゆえ Theorem 2.6 により
`(A/C)'` (resp. `(G/C)'`) は `p`-群」と一言で済ませる部分にあたる。

証明: Thm 2.6(b) (`odd_two_dim_sylow_abelian`) より, `p`-Sylow `P` は abelian で
`G' ≤ P` を満たす。`P` は `p`-群 (`Sylow.isPGroup'`) なので, その部分群
`G'` も `p`-群 (`IsPGroup.to_le`)。`Finite (Sylow p G)` は有限群から従う。 -/
theorem isPGroup_commutator_of_faithful_two_dim_charP
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (hdim : Module.finrank F V = 2) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    {p : ℕ} [Fact p.Prime] (hp_dvd : p ∣ Nat.card G) (hchar : CharP F p) :
    IsPGroup p (commutator G) := by
  -- 標準的な `p`-Sylow を取り Thm 2.6(b) を適用する。
  let P : Sylow p G := default
  obtain ⟨_hPab, hcomm_le⟩ :=
    odd_two_dim_sylow_abelian hodd hdim ρ hfaithful hp_dvd hchar P
  -- `P` は `p`-群, ゆえに `G' ≤ P` も `p`-群。
  exact P.isPGroup'.to_le hcomm_le

/-! ## §4A: commutator / power identities with a central commutator (Lemma 4.2)

BG Lemma 4.2 (mmd L1374-1383, BG defers to **G** Lemma 2.2.2): if `⁅x, y⁆ ∈ Z(G)`
then for all `n ≥ 1`,

* (a) `⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n = ⁅x, y ^ n⁆`, and
* (b) `(x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ (n.choose 2)`.

These are the basic collection identities for a single central commutator. Part (b)
is a rearrangement of the repo's class-`≤ 2` identity
`OddOrder.GroupTheory.mul_pow_eq_commutator_pow_mul_of_class_le_two`, but BG only
assumes `⁅x, y⁆ ∈ Z(G)` for the *given* pair, so we prove the single-pair forms
directly. -/

section CommutatorPowerIdentities

open scoped commutatorElement

variable {K : Type*} [Group K]

/-- Conjugation collection with a central commutator: if `z := ⁅x, y⁆` is central,
then `x ^ n * y * x⁻¹ ^ n = ⁅x, y⁆ ^ n * y`.

This is the engine for Lemma 4.2(a). Proof by induction using the base relation
`x * y * x⁻¹ = ⁅x, y⁆ * y` (immediate from `commutatorElement_def`) and centrality
of `z`. -/
private theorem conj_pow_eq_commutator_pow_mul_of_central {x y : K}
    (hz : ⁅x, y⁆ ∈ Subgroup.center K) (n : ℕ) :
    x ^ n * y * (x⁻¹) ^ n = ⁅x, y⁆ ^ n * y := by
  -- Base relation `x * y * x⁻¹ = z * y`, then treat `z = ⁅x, y⁆` as an opaque atom.
  have hbase : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
  have hcomm_x : Commute x ⁅x, y⁆ := Subgroup.mem_center_iff.mp hz x
  set z := ⁅x, y⁆ with hz_def
  induction n with
  | zero => simp
  | succ k ih =>
    -- `x` commutes with `z ^ k`.
    have hxk : x * z ^ k = z ^ k * x := (hcomm_x.pow_right k).eq
    calc x ^ (k + 1) * y * (x⁻¹) ^ (k + 1)
        = x * (x ^ k * y * (x⁻¹) ^ k) * x⁻¹ := by
          rw [pow_succ', pow_succ]; simp only [mul_assoc]
      _ = x * (z ^ k * y) * x⁻¹ := by rw [ih]
      _ = (x * z ^ k) * (y * x⁻¹) := by rw [mul_assoc, mul_assoc, mul_assoc]
      _ = (z ^ k * x) * (y * x⁻¹) := by rw [hxk]
      _ = z ^ k * (x * y * x⁻¹) := by rw [mul_assoc, mul_assoc]
      _ = z ^ k * (z * y) := by rw [hbase]
      _ = z ^ (k + 1) * y := by rw [pow_succ]; rw [mul_assoc]

/-- **BG Lemma 4.2(a)**, left slot. If `⁅x, y⁆` is central then
`⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n` for all `n`.

Proof: `⁅x ^ n, y⁆ = x ^ n * y * x⁻¹ ^ n * y⁻¹ = ⁅x, y⁆ ^ n * y * y⁻¹ = ⁅x, y⁆ ^ n`
using `conj_pow_eq_commutator_pow_mul_of_central`. -/
theorem commutatorElement_pow_left_of_central {x y : K}
    (hz : ⁅x, y⁆ ∈ Subgroup.center K) (n : ℕ) :
    ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  rw [commutatorElement_def, ← inv_pow, mul_assoc (x ^ n) y,
    show x ^ n * (y * (x⁻¹) ^ n) = x ^ n * y * (x⁻¹) ^ n by group,
    conj_pow_eq_commutator_pow_mul_of_central hz n]
  group

/-- **BG Lemma 4.2(a)**, right slot. If `⁅x, y⁆` is central then
`⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n` for all `n`.

Proof: pass to inverse commutators. `⁅x, y⁆⁻¹ = ⁅y, x⁆` (`commutatorElement_inv`),
which is also central, so `⁅y ^ n, x⁆ = ⁅y, x⁆ ^ n` by the left-slot version; invert
both sides and use `⁅y, x⁆⁻¹ = ⁅x, y⁆`. -/
theorem commutatorElement_pow_right_of_central {x y : K}
    (hz : ⁅x, y⁆ ∈ Subgroup.center K) (n : ℕ) :
    ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  -- `⁅y, x⁆ = ⁅x, y⁆⁻¹` is central.
  have hz' : ⁅y, x⁆ ∈ Subgroup.center K := by
    rw [← commutatorElement_inv]; exact (Subgroup.center K).inv_mem hz
  have h := commutatorElement_pow_left_of_central hz' n
  -- `⁅x, y^n⁆ = ⁅y^n, x⁆⁻¹ = (⁅y, x⁆ ^ n)⁻¹ = (⁅x, y⁆⁻¹ ^ n)⁻¹ = ⁅x, y⁆ ^ n`.
  rw [← commutatorElement_inv, h, ← commutatorElement_inv, inv_pow, inv_inv]

/-- Power collection with a central commutator (mathlib's commutator convention
`⁅a, b⁆ = a * b * a⁻¹ * b⁻¹`): if `z := ⁅y, x⁆` is central then
`y ^ n * x = ⁅y, x⁆ ^ n * x * y ^ n`.

The companion to `conj_pow_eq_commutator_pow_mul_of_central`, used for Lemma 4.2(b).
Proof by induction from the base relation `y * x = ⁅y, x⁆ * x * y`. -/
private theorem pow_mul_eq_commutator_pow_mul_mul_of_central {x y : K}
    (hz' : ⁅y, x⁆ ∈ Subgroup.center K) (n : ℕ) :
    y ^ n * x = ⁅y, x⁆ ^ n * x * y ^ n := by
  -- Base relation `y * x = z * x * y`, then treat `z = ⁅y, x⁆` as an opaque central atom.
  have hbase : y * x = ⁅y, x⁆ * x * y := by rw [commutatorElement_def]; group
  have hcomm_z : Commute ⁅y, x⁆ y := (Subgroup.mem_center_iff.mp hz' y).symm
  set z := ⁅y, x⁆ with hz_def
  -- `y` commutes with `z ^ m`.
  have hyz : ∀ m : ℕ, y * z ^ m = z ^ m * y := fun m => (hcomm_z.symm.pow_right m).eq
  induction n with
  | zero => simp
  | succ k ih =>
    calc y ^ (k + 1) * x
        = y * (y ^ k * x) := by rw [pow_succ']; rw [mul_assoc]
      _ = y * (z ^ k * x * y ^ k) := by rw [ih]
      _ = (y * z ^ k) * (x * y ^ k) := by rw [mul_assoc, mul_assoc]
      _ = (z ^ k * y) * (x * y ^ k) := by rw [hyz k]
      _ = z ^ k * (y * x) * y ^ k := by rw [mul_assoc, mul_assoc, mul_assoc]
      _ = z ^ k * (z * x * y) * y ^ k := by rw [hbase]
      _ = z ^ (k + 1) * x * y ^ (k + 1) := by
          rw [pow_succ z, pow_succ' y]; simp only [mul_assoc]

/-- **BG Lemma 4.2(b)**. If `⁅x, y⁆` is central then
`(x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ (n.choose 2)` for all `n`.

This is BG's form (commutator on the right). Proof by induction, moving the central
commutator `⁅y, x⁆` to the right; the exponent accumulates as the triangular numbers
`n.choose 2`. -/
theorem mul_pow_eq_mul_commutator_pow_of_central {x y : K}
    (hz : ⁅x, y⁆ ∈ Subgroup.center K) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ (n.choose 2) := by
  -- `⁅y, x⁆ = ⁅x, y⁆⁻¹` is central. Make `z = ⁅y, x⁆` opaque.
  have hz' : ⁅y, x⁆ ∈ Subgroup.center K := by
    rw [← commutatorElement_inv]; exact (Subgroup.center K).inv_mem hz
  have hpow := fun (k : ℕ) => pow_mul_eq_commutator_pow_mul_mul_of_central hz' k
  have hcentral : ∀ g : K, ⁅y, x⁆ * g = g * ⁅y, x⁆ :=
    fun g => (Subgroup.mem_center_iff.mp hz' g).symm
  set z := ⁅y, x⁆ with hz_def
  induction n with
  | zero => simp
  | succ k ih =>
    have hchoose : (k + 1).choose 2 = k.choose 2 + k := by
      rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right, Nat.add_comm]
    -- `z ^ j` is central: it commutes with every element `w` (so with `x`, `y`, and `z`).
    have hzw : ∀ (j : ℕ) (w : K), z ^ j * w = w * z ^ j :=
      fun j w => (Commute.pow_left (show Commute z w from hcentral w) j).eq
    -- First collection: `(x * y) ^ (k+1) = x ^ k * (y ^ k * x) * y * z ^ (k.choose 2)`.
    have hstep : (x * y) ^ (k + 1) = x ^ k * (y ^ k * x) * y * z ^ (k.choose 2) := by
      rw [pow_succ, ih, mul_assoc (x ^ k * y ^ k), hzw (k.choose 2) (x * y)]
      simp only [mul_assoc]
    rw [hstep, hpow k]
    -- Goal: `x^k*(z^k*x*y^k)*y*z^c = x^(k+1)*y^(k+1)*z^((k+1).choose 2)`.
    rw [hchoose, pow_add]
    -- Normalise to right-associated form.
    simp only [mul_assoc]
    -- LHS = `x^k * (z^k * (x * (y^k * (y * z^c))))`; move `z^k` rightward past `x, y^k, y`.
    rw [hzw k (x * (y ^ k * (y * z ^ (k.choose 2))))]
    -- Now `z^k` is to the right of `z^c`: bring them together via centrality of `z^c`.
    rw [show x * (y ^ k * (y * z ^ (k.choose 2))) * z ^ k
          = x * (y ^ k * (y * (z ^ (k.choose 2) * z ^ k))) by simp only [mul_assoc]]
    -- Combine: `x^k * (x * (y^k * (y * (z^c * z^k))))`, matching RHS `x^(k+1)*y^(k+1)*z^(c+k)`.
    rw [← pow_add, pow_succ x, pow_succ y]
    simp only [mul_assoc, pow_zero, one_mul]

end CommutatorPowerIdentities

/-! ## §4A: `Ω₁` of a class-`≤ 2` `p`-group has exponent `1` or `p` (Proposition 4.3(a))

BG Proposition 4.3 (mmd L1387-1472): for `p` odd and a `p`-group `R` with either
(a) `cl(R) ≤ 2`, or (b) `p > 3` and `cl(R) ≤ 3`, the subgroup `Ω₁(R)` has exponent
`1` or `p`, and (when `R' ⊆ Ω₁(R)`) the `p`-th power map is a homomorphism.

**The `cl(R) ≤ 2` half of part (a) is already formalised in the repo** and we reuse
it directly (no wrapper, per project policy):

* `OddOrder.GroupTheory.Omega.pow_eq_one_of_class_le_two`
  (`OddOrder/GroupTheory/CriticalSubgroup.lean`, Gorenstein Lemma 5.3.9(i)):
  for `p` odd and `⁅R, R⁆ ≤ Z(R)`, every `g ∈ Ω₁(R) = Omega R p 1` has `g ^ p = 1`,
  i.e. `Ω₁(R)` has exponent `1` or `p`.
* `OddOrder.GroupTheory.Omega.exponent_eq_of_class_le_two` (same file): the exponent
  form `Monoid.exponent (Omega R p 1) = p` (under `Nontrivial (Omega R p 1)`).

These are exactly BG Proposition 4.3(a) in the `cl ≤ 2` case; the BG-facing uses
(e.g. Lemma 4.5(c), applying 4.3(a) to `Z₂(R)`) call them directly. The
`cl ≤ 3, p > 3` branch of 4.3 (regular-`p`-group collection, mmd L1410-1472, which
needs the `(uv)^n` triple-commutator expansion (4.4)) is developed below: its
**mathematical core**, the iterated commutator power law (4.4)-precursor under
`cl ≤ 3`, is supplied here sorry-free (`commutatorElement_pow_left_of_triple_central`).
The full `(u*v)^n` collection bookkeeping and the `|R|`-induction packaging the
exponent-`≤ p` conclusion as `Omega.pow_eq_one_of_class_le_three` remain to be
assembled on top of this core (they additionally need `γ₄(R) = 1` collection and a
maximal-subgroup induction; see the section below). -/

/-! ## §4A: iterated commutator power law under `cl ≤ 3` (Proposition 4.3(a), `(4.4)`)

BG Proposition 4.3(a), `p > 3` branch (mmd L1410-1472), runs the regular-`p`-group
collection formula `(4.4)`. Its load-bearing ingredient is the **iterated commutator
power law**: when `γ₃(G) = ⁅⁅G,G⁆,G⁆ ⊆ Z(G)` (class `≤ 3`), the left slot of a
commutator collects as
`⁅u ^ n, w⁆ = ⁅u, w⁆ ^ n * ⁅u, ⁅u, w⁆⁆ ^ (n.choose 2)`,
the class-`3` analogue of Lemma 4.2(a)'s `⁅u ^ n, w⁆ = ⁅u, w⁆ ^ n` (which holds when
`⁅u, w⁆` is itself central). The correction term `⁅u, ⁅u, w⁆⁆` is central here (it is
`⁅⁅u, w⁆, u⁆⁻¹`, a `γ₃`-element), so it accumulates with the triangular exponent
`n.choose 2`.

This is the genuine mathematical content of `(4.4)` (no hidden hypotheses: `hc3` is
exactly `cl ≤ 3`, constructible from any class-`≤ 3` group). It is the class-`3`
sibling of the repo's class-`≤ 2` collection
`OddOrder.GroupTheory.mul_pow_eq_commutator_pow_mul_of_class_le_two`, and is reused by
the full `(u*v)^n` collection and by Lemma 4.5(c) / Prop 4.8.

The hypothesis is taken in the pointwise form `∀ a b c, ⁅⁅a, b⁆, c⁆ ∈ Z(G)`; a
`commutator (commutator ⊤) ≤ center` packaging converts to it via
`Subgroup.commutator_mem_commutator` exactly as the class-`≤ 2` lemma does with
`commutator K ≤ center K`. -/

section Prop43ClassThreeCollection

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- Drop a central right factor inside a commutator's right slot: `⁅u, A * z⁆ = ⁅u, A⁆`
when `z` is central.

Used to discard the central correction term produced by the inductive expansion of
`⁅u ^ n, w⁆` before iterating the right slot. -/
private theorem commutatorElement_right_mul_central {u A z : G}
    (hz : z ∈ Subgroup.center G) : ⁅u, A * z⁆ = ⁅u, A⁆ := by
  simp only [commutatorElement_def]
  have hc : ∀ g : G, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  rw [mul_inv_rev]
  calc u * (A * z) * u⁻¹ * (z⁻¹ * A⁻¹)
      = u * A * (z * u⁻¹) * (z⁻¹ * A⁻¹) := by group
    _ = u * A * (u⁻¹ * z) * (z⁻¹ * A⁻¹) := by rw [hc u⁻¹]
    _ = u * A * u⁻¹ * A⁻¹ := by group

/-- Collect a central element to the right: `z ^ m * (a * z ^ j) * b = a * b * z ^ (j + m)`
when `z` is central.

The accumulation step for the `n.choose 2` exponent in the iterated commutator power
law: after the inductive step exposes `z ^ k` (with `k = (k.choose 2)`-th batch) and a
fresh `z ^ (k.choose 2)`, this merges them on the right past the non-central `a`, `b`. -/
private theorem mul_central_pow_collect (z a b : G) (hz : ∀ g : G, Commute z g)
    (m j : ℕ) : z ^ m * (a * z ^ j) * b = a * b * z ^ (j + m) := by
  have hzk : ∀ (i : ℕ) (g : G), Commute (z ^ i) g := fun i g => (hz g).pow_left i
  have hblock : Commute (z ^ j * z ^ m) b := (hzk j b).mul_left (hzk m b)
  have h1 : z ^ m * (a * z ^ j) = a * (z ^ j * z ^ m) := by
    rw [(hzk m (a * z ^ j)).eq, mul_assoc]
  rw [h1, mul_assoc a, hblock.eq, ← mul_assoc, pow_add]

/-- **BG Proposition 4.3(a), `(4.4)`-precursor: iterated commutator power law under
`cl ≤ 3`.** If `γ₃(G) = ⁅⁅G,G⁆,G⁆ ⊆ Z(G)` (here `hc3 : ∀ a b c, ⁅⁅a, b⁆, c⁆ ∈ Z(G)`),
then for all `u w : G` and `n : ℕ`,
`⁅u ^ n, w⁆ = ⁅u, w⁆ ^ n * ⁅u, ⁅u, w⁆⁆ ^ (n.choose 2)`.

This is BG's `[u^n, w] = [u, w]^n · [u, w, u]^{C(n,2)}` in mathlib's commutator
convention `⁅a, b⁆ = a b a⁻¹ b⁻¹`; the correction commutator is
`⁅u, ⁅u, w⁆⁆ = ⁅⁅u, w⁆, u⁆⁻¹`, a `γ₃`-element, hence central, so the positive exponent
`n.choose 2` is recorded directly.

Proof: induction on `n`. The product rule
`⁅u ^ (k+1), w⁆ = ⁅u, ⁅u ^ k, w⁆⁆ · ⁅u ^ k, w⁆ · ⁅u, w⁆` (`group` after `commutatorElement_def`)
exposes a `⁅u, ⁅u ^ k, w⁆⁆`; substitute the inductive hypothesis, drop the central
correction factor inside its right slot (`commutatorElement_right_mul_central`),
iterate the right slot via the central-commutator law
`commutatorElement_pow_right_of_central` (Lemma 4.2(a), REUSED), and merge the central
powers (`mul_central_pow_collect`); the exponent satisfies
`(k+1).choose 2 = k.choose 2 + k` (`Nat.choose_succ_succ'`).

This is the genuine class-`3` analogue of Lemma 4.2(a)
(`commutatorElement_pow_left_of_central`, which needs `⁅u, w⁆` central) and the
class-`3` sibling of the repo's class-`≤ 2` collection
`OddOrder.GroupTheory.mul_pow_eq_commutator_pow_mul_of_class_le_two`. -/
theorem commutatorElement_pow_left_of_triple_central
    (hc3 : ∀ a b c : G, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center G) (u w : G) (n : ℕ) :
    ⁅u ^ n, w⁆ = ⁅u, w⁆ ^ n * ⁅u, ⁅u, w⁆⁆ ^ (n.choose 2) := by
  set d := ⁅u, ⁅u, w⁆⁆ with hd_def
  -- `d = ⁅u, ⁅u, w⁆⁆ = ⁅⁅u, w⁆, u⁆⁻¹` is a `γ₃`-element, hence central.
  have hd_cen : d ∈ Subgroup.center G := by
    rw [hd_def, ← commutatorElement_inv]; exact (Subgroup.center G).inv_mem (hc3 u w u)
  have hd_comm : ∀ g : G, Commute d g := fun g => (Subgroup.mem_center_iff.mp hd_cen g).symm
  induction n with
  | zero => simp
  | succ k ih =>
    -- Product rule for the left slot, pure group identity.
    have hbase : ⁅u ^ (k + 1), w⁆ = ⁅u, ⁅u ^ k, w⁆⁆ * ⁅u ^ k, w⁆ * ⁅u, w⁆ := by
      rw [pow_succ' u k]; simp only [commutatorElement_def]; group
    have hchoose : (k + 1).choose 2 = k.choose 2 + k := by
      rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right, Nat.add_comm]
    rw [hbase, ih,
        commutatorElement_right_mul_central
          (u := u) (A := ⁅u, w⁆ ^ k) (z := d ^ (k.choose 2))
          ((Subgroup.center G).pow_mem hd_cen _),
        commutatorElement_pow_right_of_central hd_cen k,
        hchoose, pow_succ ⁅u, w⁆ k]
    exact mul_central_pow_collect d (⁅u, w⁆ ^ k) ⁅u, w⁆ hd_comm k (k.choose 2)

/-- Base case `n = 2` of the `(u*v)^n` collection (`(4.4)`), pure group identity locking
the formula shape: `(u * v) ^ 2 = u * ⁅v, u⁆ * u * v ^ 2`.

For `cl ≤ 3` the inner commutator `⁅v, u⁆` is **not** central, so `(u*v)^n` does not
have the class-`≤ 2` shape `(central) * u ^ n * v ^ n`; the collection must carry
`⁅v, u⁆` through, generating `γ₃` corrections. This identity records the obstruction
that the full `(4.4)` (still to be assembled on top of
`commutatorElement_pow_left_of_triple_central`) has to resolve. -/
theorem mul_pow_two_eq_mul_commutator (u v : G) :
    (u * v) ^ 2 = u * ⁅v, u⁆ * u * v ^ 2 := by
  simp only [commutatorElement_def, pow_two]; group

/-- Bridge identity feeding the `(u*v)^n` collection induction: `v ^ k * u` exposes a
single left-slot commutator power, `v ^ k * u = ⁅v ^ k, u⁆ * u * v ^ k`.

Combined with `commutatorElement_pow_left_of_triple_central` (roles `v, u`) this yields
`v ^ k * u = ⁅v, u⁆ ^ k * ⁅v, ⁅v, u⁆⁆ ^ (k.choose 2) * u * v ^ k`, the step that moves a
block of `v`'s past a `u` during collection. -/
theorem pow_mul_eq_commutator_mul (u v : G) (k : ℕ) :
    v ^ k * u = ⁅v ^ k, u⁆ * u * v ^ k := by
  rw [commutatorElement_def]; group

/-! ### The full `(u*v)^n` collection formula `(4.4)`

We now assemble BG's two-generator collection formula `(4.4)` (mmd L1430-1464). For
`cl ≤ 3` the inner commutator `c := ⁅v, u⁆` is **not** central; what is central are the
weight-`3` commutators `d₁ := ⁅⁅v, u⁆, u⁆` and `d₂ := ⁅⁅v, u⁆, v⁆`. Centrality of `d₁, d₂`
is exactly `γ₄(G) = 1` (`hc4 : ⁅⁅⁅a, b⁆, c⁆, d⁆ = 1`): e.g. `⁅d₁, g⁆ = ⁅⁅⁅v, u⁆, u⁆, g⁆ = 1`.

The exponents `FF n = (n+1).choose 3` and `GG n = 2 * (n+1).choose 3` are **inlined as
closed forms** (no `def`, to remove the "tweak until green" degree of freedom). These are
model-verified (free nilpotent class-`3` group on two generators via the Magnus embedding,
`n = 0..8`); BG's literal `f(n) = C(n,3)`, `g(n) = 2 C(n,3) + C(n,2)` are for the *opposite*
commutator convention `[a,b] = a⁻¹b⁻¹ab` and are wrong here, as is `GG = (n+1).choose 3`.
The genuine recurrences are `FF(k+1) = FF(k) + k + k.choose 2` and `GG = 2 * FF`. -/

-- Soundness anchors (anti-scaffold `TRAP 1`): the inlined `FF`/`GG` values must match the
-- model, ruling out the BG-literal and the `GG = C(n+1,3)` mistakes.
example : (2 + 1).choose 3 = 1 := by decide          -- FF(2) = 1
example : (3 + 1).choose 3 = 4 := by decide          -- FF(3) = 4  (BG-literal would be 1)
example : (3 + 1).choose 3 ≠ 1 := by decide
example : 2 * (2 + 1).choose 3 = 2 := by decide      -- GG(2) = 2
example : 2 * (3 + 1).choose 3 = 8 := by decide      -- GG(3) = 8  (GG = C(n+1,3) would be 4)

/-- The weight-`3` commutator `⁅⁅v, u⁆, w⁆` is central under `γ₄(G) = 1`: indeed
`⁅⁅⁅v, u⁆, w⁆, g⁆ = 1` for every `g` (`hc4`). -/
private theorem triple_commutator_mem_center
    (hc4 : ∀ a b c d : G, ⁅⁅⁅a, b⁆, c⁆, d⁆ = 1) (u v w : G) :
    ⁅⁅v, u⁆, w⁆ ∈ Subgroup.center G :=
  Subgroup.mem_center_iff.2 fun g =>
    ((commutatorElement_eq_one_iff_commute.1 (hc4 v u w g)).symm).eq

/-- Move a power of the (non-central) commutator `c := ⁅v, u⁆` past a single element `w`,
picking up a central correction: `c ^ m * w = w * c ^ m * ⁅⁅v, u⁆, w⁆ ^ m`.

Only the centrality of `⁅⁅v, u⁆, w⁆ = ⁅c, w⁆` (from `hc4`) is needed: write
`c ^ m * w = ⁅c ^ m, w⁆ * w * c ^ m` (`pow_mul_eq_commutator_mul`) and
`⁅c ^ m, w⁆ = ⁅c, w⁆ ^ m` (`commutatorElement_pow_left_of_central`, since `⁅c, w⁆` is
central), then move the central correction to the right. With `w = u` this gives the
`d₁`-motion and with `w = v` the `d₂`-motion of BG's collection. -/
private theorem commutator_pow_mul_collect
    (hc4 : ∀ a b c d : G, ⁅⁅⁅a, b⁆, c⁆, d⁆ = 1) (u v w : G) (m : ℕ) :
    ⁅v, u⁆ ^ m * w = w * ⁅v, u⁆ ^ m * ⁅⁅v, u⁆, w⁆ ^ m := by
  have hcen := triple_commutator_mem_center hc4 u v w
  -- `⁅⁅v, u⁆, w⁆` central ⇒ commutes with everything, in particular `w` and `c = ⁅v, u⁆`.
  have hcd : ∀ g : G, Commute (⁅⁅v, u⁆, w⁆ ^ m) g :=
    fun g => (show Commute ⁅⁅v, u⁆, w⁆ g from (Subgroup.mem_center_iff.mp hcen g).symm).pow_left m
  rw [pow_mul_eq_commutator_mul w ⁅v, u⁆ m, commutatorElement_pow_left_of_central hcen m]
  -- Goal: `⁅..⁆^m * w * c^m = w * c^m * ⁅..⁆^m`; move the central correction to the right.
  rw [(hcd w).eq, mul_assoc, (hcd (⁅v, u⁆ ^ m)).eq, ← mul_assoc]

/-- Iterated form: move `c ^ k = ⁅v, u⁆ ^ k` past a *power* `w ^ j`,
`c ^ k * w ^ j = w ^ j * c ^ k * ⁅⁅v, u⁆, w⁆ ^ (k * j)`.

The commutator `⁅c ^ k, w ^ j⁆` collects to `⁅c, w⁆ ^ (k * j) = ⁅⁅v, u⁆, w⁆ ^ (k * j)` by the
central-commutator power laws (`commutatorElement_pow_left_of_central` then
`commutatorElement_pow_right_of_central`, both valid since `⁅⁅v, u⁆, w⁆` is central under
`hc4`); unfolding `⁅c ^ k, w ^ j⁆ = c^k w^j (c^k)⁻¹ (w^j)⁻¹` and moving the (central)
correction across gives the claim. Used to move the `c ^ k` block past `v ^ (k+1)`. -/
private theorem commutator_pow_mul_pow_collect
    (hc4 : ∀ a b c d : G, ⁅⁅⁅a, b⁆, c⁆, d⁆ = 1) (u v w : G) (k j : ℕ) :
    ⁅v, u⁆ ^ k * w ^ j = w ^ j * ⁅v, u⁆ ^ k * ⁅⁅v, u⁆, w⁆ ^ (k * j) := by
  have hcen := triple_commutator_mem_center hc4 u v w
  have hcomm : ∀ g : G, Commute ⁅⁅v, u⁆, w⁆ g :=
    fun g => (Subgroup.mem_center_iff.mp hcen g).symm
  -- `⁅c, w^j⁆ = ⁅c, w⁆^j` is central, so the left slot collects too.
  have hcenj : ⁅⁅v, u⁆, w ^ j⁆ ∈ Subgroup.center G :=
    (commutatorElement_pow_right_of_central hcen j).symm ▸ (Subgroup.center G).pow_mem hcen j
  -- `⁅c^k, w^j⁆ = ⁅c, w^j⁆^k = (⁅c, w⁆^j)^k = ⁅⁅v,u⁆,w⁆^(k*j)`.
  have hcomm_collect : ⁅⁅v, u⁆ ^ k, w ^ j⁆ = ⁅⁅v, u⁆, w⁆ ^ (k * j) := by
    rw [commutatorElement_pow_left_of_central hcenj k,
      commutatorElement_pow_right_of_central hcen j, ← pow_mul, Nat.mul_comm]
  -- From `⁅c^k, w^j⁆ = c^k w^j (c^k)⁻¹ (w^j)⁻¹` solve for `c^k * w^j`.
  have hbase : ⁅v, u⁆ ^ k * w ^ j = ⁅⁅v, u⁆ ^ k, w ^ j⁆ * (w ^ j * ⁅v, u⁆ ^ k) := by
    rw [commutatorElement_def]; group
  -- Goal: `e^(k*j) * (w^j * c^k) = w^j * c^k * e^(k*j)`; `e^(k*j)` is central, move it right.
  rw [hbase, hcomm_collect, ((hcomm (w ^ j * ⁅v, u⁆ ^ k)).pow_left (k * j)).eq]

/-- The non-central collection step `(4.4)` for the skeleton `u ^ k * v ^ k * c ^ C(k,2)`:
multiplying by `u * v` advances `k ↦ k + 1` while emitting the central corrections
`d₁ ^ (k + C(k,2))` and `d₂ ^ (k * (k+1))`:
`u^k v^k c^C(k,2) (u*v) = u^(k+1) v^(k+1) c^C(k+1,2) ⁅⁅v,u⁆,u⁆^(k+C(k,2)) ⁅⁅v,u⁆,v⁆^(k(k+1))`.

This is the heart of the induction. Reading left to right (with `c := ⁅v, u⁆`,
`d₁ := ⁅⁅v, u⁆, u⁆`, `d₂ := ⁅⁅v, u⁆, v⁆`):

* `c^C(k,2) * u = u * c^C(k,2) * d₁^C(k,2)` (`commutator_pow_mul_collect`, `w = u`);
* `c^C(k,2) * v = v * c^C(k,2) * d₂^C(k,2)` (`commutator_pow_mul_collect`, `w = v`);
* `v^k * u = ⁅v^k, u⁆ * u * v^k` (`pow_mul_eq_commutator_mul`) with
  `⁅v^k, u⁆ = c^k * d₂⁻¹^C(k,2)` (`commutatorElement_pow_left_of_triple_central` and
  `⁅v, ⁅v, u⁆⁆ = d₂⁻¹`); the `d₂⁻¹^C(k,2)` cancels a `d₂^C(k,2)`;
* `c^k * u = u * c^k * d₁^k` and `c^k * v^(k+1) = v^(k+1) * c^k * d₂^(k*(k+1))`
  (`commutator_pow_mul_collect` / `commutator_pow_mul_pow_collect`).

The `c`-exponent lands on `k + C(k,2) = C(k+1,2)` and the central exponents on
`d₁^(k + C(k,2))`, `d₂^(k*(k+1))` (model-verified). -/
private theorem collect_skeleton_step
    (hc3 : ∀ a b c : G, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center G)
    (hc4 : ∀ a b c d : G, ⁅⁅⁅a, b⁆, c⁆, d⁆ = 1) (u v : G) (k : ℕ) :
    u ^ k * v ^ k * ⁅v, u⁆ ^ (k.choose 2) * (u * v)
      = u ^ (k + 1) * v ^ (k + 1) * ⁅v, u⁆ ^ ((k + 1).choose 2)
          * ⁅⁅v, u⁆, u⁆ ^ (k + k.choose 2) * ⁅⁅v, u⁆, v⁆ ^ (k * (k + 1)) := by
  -- Central correction atoms (`d₁, d₂` central by `hc4`). Abbreviations via `m` only.
  have hd1cen := triple_commutator_mem_center hc4 u v u
  have hd2cen := triple_commutator_mem_center hc4 u v v
  have hd1 : ∀ g : G, Commute ⁅⁅v, u⁆, u⁆ g := fun g => (Subgroup.mem_center_iff.mp hd1cen g).symm
  have hd2 : ∀ g : G, Commute ⁅⁅v, u⁆, v⁆ g := fun g => (Subgroup.mem_center_iff.mp hd2cen g).symm
  -- `⁅v^k, u⁆ = ⁅v,u⁆^k * d₂⁻¹^C(k,2)`.
  have hvk : ⁅v ^ k, u⁆ = ⁅v, u⁆ ^ k * (⁅⁅v, u⁆, v⁆⁻¹) ^ (k.choose 2) := by
    rw [commutatorElement_pow_left_of_triple_central hc3 v u k, commutatorElement_inv]
  set m := k.choose 2 with hm
  have hchoose : (k + 1).choose 2 = k + m := by
    rw [hm, Nat.choose_succ_succ' k 1, Nat.choose_one_right, Nat.add_comm]
  -- `d₂⁻¹^m * d₂^m = 1`.
  have hcancel : (⁅⁅v, u⁆, v⁆⁻¹) ^ m * ⁅⁅v, u⁆, v⁆ ^ m = 1 := by rw [inv_pow, inv_mul_cancel]
  -- Central moves (push `d₁, d₂` powers rightward across an arbitrary tail `g`).
  have e1 : ∀ (a : ℕ) (g : G), ⁅⁅v, u⁆, u⁆ ^ a * g = g * ⁅⁅v, u⁆, u⁆ ^ a :=
    fun a g => ((hd1 g).pow_left a).eq
  have e2 : ∀ (a : ℕ) (g : G), ⁅⁅v, u⁆, v⁆ ^ a * g = g * ⁅⁅v, u⁆, v⁆ ^ a :=
    fun a g => ((hd2 g).pow_left a).eq
  have e2inv : ∀ (a : ℕ) (g : G), (⁅⁅v, u⁆, v⁆⁻¹) ^ a * g = g * (⁅⁅v, u⁆, v⁆⁻¹) ^ a :=
    fun a g => (((hd2 g).inv_left).pow_left a).eq
  -- Step A: expose `⁅v,u⁆^m * u` and `⁅v,u⁆^m * v`, applying the two single-element motions.
  rw [show u ^ k * v ^ k * ⁅v, u⁆ ^ m * (u * v) = u ^ k * v ^ k * (⁅v, u⁆ ^ m * u) * v by
        simp only [mul_assoc],
      commutator_pow_mul_collect hc4 u v u m]
  simp only [mul_assoc]
  -- Move the fresh `d₁^m` right past `v`, re-expose `⁅v,u⁆^m * v`, then the `v`-motion.
  rw [e1 m v, ← mul_assoc (⁅v, u⁆ ^ m) v, commutator_pow_mul_collect hc4 u v v m]
  simp only [mul_assoc]
  -- Step C: expose `v^k * u`, expand it (`⁅v^k,u⁆ = ⁅v,u⁆^k * d₂⁻¹^m`).
  rw [← mul_assoc (v ^ k) u, pow_mul_eq_commutator_mul u v k, hvk]
  simp only [mul_assoc]
  -- Push the central `d₂⁻¹^m` to the far right (past the whole tail).
  rw [e2inv m (u * (v ^ k * (v * (⁅v, u⁆ ^ m * (⁅⁅v, u⁆, v⁆ ^ m * ⁅⁅v, u⁆, u⁆ ^ m)))))]
  simp only [mul_assoc]
  -- Now `… * (d₂^m * (d₁^m * d₂⁻¹^m))`; commute `d₁^m` past `d₂⁻¹^m`, then `d₂^m * d₂⁻¹^m = 1`.
  rw [e1 m (⁅⁅v, u⁆, v⁆⁻¹ ^ m), inv_pow, ← mul_assoc (⁅⁅v, u⁆, v⁆ ^ m), mul_inv_cancel]
  simp only [one_mul]
  -- Step D: `⁅v,u⁆^k * u = u * ⁅v,u⁆^k * d₁^k`; merge `v^k * v = v^(k+1)`.
  rw [← mul_assoc (⁅v, u⁆ ^ k) u, commutator_pow_mul_collect hc4 u v u k]
  simp only [mul_assoc]
  -- Move `d₁^k` right past `v^k, v, ⁅v,u⁆^m`, merge with `d₁^m` into `d₁^(k+m)`.
  rw [e1 k (v ^ k * (v * (⁅v, u⁆ ^ m * ⁅⁅v, u⁆, u⁆ ^ m)))]
  simp only [mul_assoc]
  rw [← pow_add, Nat.add_comm m k]
  -- Step E: merge `v^k * v = v^(k+1)`; then `⁅v,u⁆^k * v^(k+1)` motion; merge `u^k*u`, `⁅v,u⁆`.
  rw [← mul_assoc (v ^ k) v, ← pow_succ, ← mul_assoc (⁅v, u⁆ ^ k) (v ^ (k + 1)),
      commutator_pow_mul_pow_collect hc4 u v v k (k + 1)]
  simp only [mul_assoc]
  -- Push `d₂^(k(k+1))` to the right of `⁅v,u⁆^m * d₁^(k+m)`, merge `⁅v,u⁆^k * ⁅v,u⁆^m`, `u^k*u`.
  rw [e2 (k * (k + 1)) (⁅v, u⁆ ^ m * ⁅⁅v, u⁆, u⁆ ^ (k + m))]
  simp only [mul_assoc]
  rw [← mul_assoc (⁅v, u⁆ ^ k) (⁅v, u⁆ ^ m), ← pow_add, ← hchoose,
      ← mul_assoc (u ^ k) u, ← pow_succ]

/-- Pascal recurrence for the `d₁`-exponent `FF n = (n+1).choose 3`:
`(k + k.choose 2) + (k+1).choose 3 = (k+2).choose 3`. The skeleton step emits `d₁^(k+C(k,2))`,
which combined with the carried `d₁^FF(k)` gives `d₁^FF(k+1)`. -/
private theorem ff_succ (k : ℕ) :
    k + k.choose 2 + (k + 1).choose 3 = (k + 2).choose 3 := by
  have hc2 : (k + 1).choose 2 = k + k.choose 2 := by
    rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right, Nat.add_comm]
  rw [show k + 2 = (k + 1) + 1 from rfl, Nat.choose_succ_succ' (k + 1) 2, hc2, Nat.add_comm]

/-- Pascal recurrence for the `d₂`-exponent `GG n = 2 * (n+1).choose 3`:
`k*(k+1) + 2 * (k+1).choose 3 = 2 * (k+2).choose 3`. The skeleton step emits `d₂^(k*(k+1))`,
which combined with the carried `d₂^GG(k)` gives `d₂^GG(k+1)`; note `k*(k+1) = 2*(k+1).choose 2`
(`Nat.succ_mul_choose_eq`). -/
private theorem gg_succ (k : ℕ) :
    k * (k + 1) + 2 * (k + 1).choose 3 = 2 * (k + 2).choose 3 := by
  -- `k*(k+1) = 2 * (k+1).choose 2`.
  have htwo : k * (k + 1) = 2 * (k + 1).choose 2 := by
    have h := Nat.add_one_mul_choose_eq k 1
    rw [Nat.choose_one_right] at h
    -- `h : (k+1) * k = (k+1).choose 2 * 2`
    rw [Nat.mul_comm k (k + 1), h, Nat.mul_comm]
  rw [htwo, ← Nat.mul_add, show k + 2 = (k + 1) + 1 from rfl, Nat.choose_succ_succ' (k + 1) 2,
    Nat.add_comm ((k + 1).choose 2)]

/-- **BG Proposition 4.3(a), `(4.4)`: two-generator collection formula under `cl ≤ 3`.**
For `γ₃(G) ⊆ Z(G)` (`hc3`) and `γ₄(G) = 1` (`hc4`), and all `u, v : G`, `n : ℕ`,
`(u*v)^n = u^n v^n ⁅v,u⁆^(C(n,2)) ⁅⁅v,u⁆,u⁆^((n+1).choose 3) ⁅⁅v,u⁆,v⁆^(2*(n+1).choose 3)`.

This is BG's `(uv)^n = u^n v^n [v,u]^{C(n,2)} [v,u,u]^{f(n)} [v,u,v]^{g(n)}` (mmd L1430-1464), but
the BG-literal `f(n) = C(n,3)`, `g(n) = 2 C(n,3) + C(n,2)` are stated for the convention
`[a,b] = a⁻¹b⁻¹ab`; in mathlib's convention `⁅a,b⁆ = a b a⁻¹ b⁻¹` the correct closed forms are
`f(n) = (n+1).choose 3` and `g(n) = 2 * (n+1).choose 3` (model-verified by the Magnus embedding
of the free nilpotent class-`3` group on two generators, `n = 0..8`). The exponents are inlined
as closed forms (no `def`) so the statement is pinned to these values.

Proof: induction on `n`. The non-central skeleton step (advancing `k ↦ k+1` while emitting
`⁅⁅v,u⁆,u⁆^(k+C(k,2))` and `⁅⁅v,u⁆,v⁆^(k(k+1))`)
is `collect_skeleton_step`; the carried central factors `⁅⁅v,u⁆,u⁆^FF(k)`, `⁅⁅v,u⁆,v⁆^GG(k)`
commute to the right and combine via the Pascal recurrences `ff_succ`, `gg_succ`. -/
theorem mul_pow_eq_collect_of_triple_central
    (hc3 : ∀ a b c : G, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center G)
    (hc4 : ∀ a b c d : G, ⁅⁅⁅a, b⁆, c⁆, d⁆ = 1) (u v : G) (n : ℕ) :
    (u * v) ^ n
      = u ^ n * v ^ n * ⁅v, u⁆ ^ (n.choose 2)
          * ⁅⁅v, u⁆, u⁆ ^ ((n + 1).choose 3)
          * ⁅⁅v, u⁆, v⁆ ^ (2 * (n + 1).choose 3) := by
  -- `d₁, d₂` central (by `hc4`).
  have hd1 : ∀ g : G, Commute ⁅⁅v, u⁆, u⁆ g :=
    fun g => (Subgroup.mem_center_iff.mp (triple_commutator_mem_center hc4 u v u) g).symm
  have hd2 : ∀ g : G, Commute ⁅⁅v, u⁆, v⁆ g :=
    fun g => (Subgroup.mem_center_iff.mp (triple_commutator_mem_center hc4 u v v) g).symm
  induction n with
  | zero => simp [Nat.choose_eq_zero_of_lt (by norm_num : 1 < 3)]
  | succ k ih =>
    rw [pow_succ, ih]
    -- Push the carried central `d₁^FF(k)`, `d₂^GG(k)` to the right of `(u*v)`.
    rw [mul_assoc (u ^ k * v ^ k * ⁅v, u⁆ ^ (k.choose 2) * ⁅⁅v, u⁆, u⁆ ^ ((k + 1).choose 3)),
        ((hd2 (u * v)).pow_left (2 * (k + 1).choose 3)).eq,
        ← mul_assoc, mul_assoc (u ^ k * v ^ k * ⁅v, u⁆ ^ (k.choose 2)),
        ((hd1 (u * v)).pow_left ((k + 1).choose 3)).eq, ← mul_assoc,
        collect_skeleton_step hc3 hc4 u v k]
    -- Now `… d₁^(k+C(k,2)) * (d₂^(k(k+1)) * (d₁^FF(k) * d₂^GG(k)))`; commute `d₂^(k(k+1))` past
    -- `d₁^FF(k)`, then combine the two `d₁` and the two `d₂` powers (`ff_succ`, `gg_succ`).
    simp only [mul_assoc]
    rw [← mul_assoc (⁅⁅v, u⁆, v⁆ ^ (k * (k + 1))),
        ((hd2 (⁅⁅v, u⁆, u⁆ ^ ((k + 1).choose 3))).pow_left (k * (k + 1))).eq]
    simp only [mul_assoc]
    rw [← mul_assoc (⁅⁅v, u⁆, u⁆ ^ (k + k.choose 2)), ← pow_add, ff_succ k,
        ← pow_add, gg_succ k]

end Prop43ClassThreeCollection

/-! ## §4A: `Ω₁` exponent and `p`-power map under `cl ≤ 3` (Proposition 4.3(a)(b))

BG Proposition 4.3 (mmd L1398-1472), `p > 3`, `cl(R) ≤ 3` branch. Building on the
collection formula `(4.4)` (`mul_pow_eq_collect_of_triple_central`), we close
Proposition 4.3:

* **(a)** every `g ∈ Ω₁(R)` has `g ^ p = 1` (`omega1_pow_eq_one`); and
* **(b)** if `R' ⊆ Ω₁(R)` then `(x * y) ^ p = x ^ p * y ^ p` for all `x, y`
  (`pow_mul_eq_mul_pow_of_commutator_le_omega1`).

The hypotheses are packaged: `hcl` is `cl(R) ≤ 2` (`⁅R, R⁆ ≤ Z(R)`) or
`p > 3 ∧ γ₃(R) pointwise central`; the latter encodes `cl(R) ≤ 3` directly. -/

section Prop43ClassThree

open OddOrder.GroupTheory
open scoped commutatorElement

/-- From pointwise `γ₃ ⊆ Z` one gets `γ₄ = 1`: a `γ₃`-element `z = ⁅⁅a, b⁆, c⁆` is
central, so `⁅z, d⁆ = 1`. This supplies the `hc4` hypothesis of the collection
formula `(4.4)` from the packaged `cl ≤ 3` assumption (no `LCS` detour). -/
private theorem triple_commutator_eq_one_of_pointwise_central {G : Type*} [Group G]
    (hc3 : ∀ a b c : G, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center G) :
    ∀ a b c d : G, ⁅⁅⁅a, b⁆, c⁆, d⁆ = 1 := by
  intro a b c d
  exact commutatorElement_eq_one_iff_commute.2
    (Subgroup.mem_center_iff.mp (hc3 a b c) d).symm

/-- **`cl ≤ 3` descends to subgroups.** If `γ₃(R)` is pointwise central in `R` and
`S : Subgroup R`, then `γ₃(↥S)` is pointwise central in `↥S`.

Proof mirrors `commutator_le_center_of_le_of_class_le_two`: push the iterated
commutator through `S.subtype` (`map_commutatorElement`), use centrality in `R`,
and pull back along `Subtype.ext`. -/
private theorem class_le_three_descent {R : Type*} [Group R]
    (hc3 : ∀ a b c : R, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center R) (S : Subgroup R) :
    ∀ a b c : ↥S, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center ↥S := by
  intro a b c
  rw [Subgroup.mem_center_iff]
  intro d
  apply Subtype.ext
  -- Goal in `R`: `(⁅⁅a,b⁆,c⁆ : R) * (d:R) = (d:R) * (⁅⁅a,b⁆,c⁆ : R)`.
  have hcoe : ((⁅⁅a, b⁆, c⁆ : ↥S) : R) = ⁅⁅(a : R), (b : R)⁆, (c : R)⁆ := by
    push_cast [commutatorElement_def]; group
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe]
  exact Subgroup.mem_center_iff.mp (hc3 (a : R) (b : R) (c : R)) (d : R)

/-- For a normal subgroup `H`, the commutator `⁅a, b⁆` with `b ∈ H` lies in `H`
(`⁅a, b⁆ = (a b a⁻¹) b⁻¹`, conjugate of `b` times `b⁻¹`). -/
private theorem commutatorElement_mem_of_normal_right {G : Type*} [Group G]
    {H : Subgroup G} (hH : H.Normal) {b : G} (hb : b ∈ H) (a : G) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (hH.conj_mem b hb a) (H.inv_mem hb)

/-- For a normal subgroup `H`, the commutator `⁅a, b⁆` with `a ∈ H` lies in `H`
(`⁅a, b⁆ = a (b a⁻¹ b⁻¹)`). -/
private theorem commutatorElement_mem_of_normal_left {G : Type*} [Group G]
    {H : Subgroup G} (hH : H.Normal) {a : G} (ha : a ∈ H) (b : G) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  have : b * a⁻¹ * b⁻¹ ∈ H := hH.conj_mem a⁻¹ (H.inv_mem ha) b
  have h2 : a * (b * a⁻¹ * b⁻¹) ∈ H := H.mul_mem ha this
  simpa [mul_assoc] using h2

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- **BG Proposition 4.3(a)** (mmd L1398-1472, `p > 3` / `cl ≤ 3` branch combined with
the classical `cl ≤ 2` case). For an odd prime `p`, a finite `p`-group `R` with
`cl(R) ≤ 2` or (`p > 3` and `cl(R) ≤ 3`), every element `g ∈ Ω₁(R) = Omega R p 1`
satisfies `g ^ p = 1`; i.e. `Ω₁(R)` has exponent dividing `p`.

The `cl ≤ 2` case is `Omega.pow_eq_one_of_class_le_two`. The `cl ≤ 3` case is the
"regular `p`-group" argument: it suffices (since `Ω₁(R)` is generated by the
`g ^ p = 1`) that the set `{g | g ^ p = 1}` is closed under products, i.e.
`x ^ p = y ^ p = 1 ⇒ (x * y) ^ p = 1`. This product-closure is proved by induction on
`|R|`. If `⟨x⟩ = R` then `R` is abelian and `(x*y)^p = x^p y^p = 1`. Otherwise pick a
maximal (hence normal) `S ⊇ ⟨x⟩`; by induction `Ω₁(↥S)` has exponent `p`, so the
weight-`2,3` commutators `⁅y, x⁆, ⁅⁅y, x⁆, x⁆, ⁅⁅y, x⁆, y⁆` — all in the `R`-normal
subgroup `Ω₁(↥S)` (which contains `x`) — have `p`-th power `1`. The collection `(4.4)`
at `n = p` then gives `(x*y)^p = x^p y^p · (those commutators)^{C(p,2),FF(p),GG(p)}`,
and `p ∣ C(p,2), (p+1).choose 3` (for `p > 3`) kills every correction factor. -/
theorem omega1_pow_eq_one (hR : IsPGroup p R) (hp_odd : Odd p)
    (hcl : _root_.commutator R ≤ Subgroup.center R ∨
           (3 < p ∧ ∀ a b c : R, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center R))
    {g : R} (hg : g ∈ Omega R p 1) : g ^ p = 1 := by
  rcases hcl with hc2 | ⟨hp3, hc3⟩
  · -- `cl ≤ 2`.
    exact Omega.pow_eq_one_of_class_le_two hp_odd hc2 hg
  -- `cl ≤ 3`, `p > 3`.
  have hc4 := triple_commutator_eq_one_of_pointwise_central hc3
  -- Product-closure of `{g | g^p = 1}` by `|R|`-strong-induction.
  suffices hclosed : ∀ x y : R, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1 by
    -- `{g | g^p=1}` is a subgroup containing the generators, hence `Omega R p 1`.
    let omega1 : Subgroup R :=
      { carrier := {g : R | g ^ p = 1}
        mul_mem' := fun {x y} hx hy => hclosed x y hx hy
        one_mem' := one_pow p
        inv_mem' := fun {x} hx => by rw [Set.mem_setOf_eq, inv_pow, hx, inv_one] }
    have hle : Omega R p 1 ≤ omega1 := by
      rw [Omega, Subgroup.closure_le]
      intro x hx
      change x ^ p = 1
      exact pow_one p ▸ hx
    simpa [omega1] using hle hg
  clear hg g
  -- Strong induction on `Nat.card R`.
  let motive : ℕ → Prop := fun n =>
    ∀ {R' : Type _} [Group R'] [Finite R'], IsPGroup p R' →
      (∀ a b c : R', ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center R') → Nat.card R' = n →
        ∀ x y : R', x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1
  refine (Nat.strongRecOn (motive := motive) (Nat.card R) ?_) hR hc3 rfl
  clear hR hc3
  intro n ih R' _ _ hR' hc3' hcard x y hxp hyp
  have hc4' := triple_commutator_eq_one_of_pointwise_central hc3'
  by_cases hxtop : Subgroup.zpowers x = ⊤
  · -- `⟨x⟩ = ⊤`: `R'` is cyclic, hence abelian; `x, y` commute.
    have hxy : Commute x y := by
      have hy_mem : y ∈ Subgroup.zpowers x := hxtop ▸ Subgroup.mem_top y
      obtain ⟨k, hk⟩ := hy_mem
      rw [← hk]; exact (Commute.refl x).zpow_right k
    rw [hxy.mul_pow, hxp, hyp, mul_one]
  · -- `⟨x⟩ ≠ ⊤`: take a maximal (normal) subgroup `S ⊇ ⟨x⟩`.
    obtain ⟨S, hS_coatom, hxS_le⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (Subgroup.zpowers x)).resolve_left hxtop
    haveI hS_normal : S.Normal := hS_coatom.normal_of_isPGroup hR'
    have hxS : x ∈ S := hxS_le (Subgroup.mem_zpowers x)
    -- `|↥S| < |R'| = n`.
    have hScard : Nat.card ↥S < n := by
      rw [← hcard]
      have h_dvd : Nat.card ↥S ∣ Nat.card R' := ⟨S.index, by rw [mul_comm, S.index_mul_card]⟩
      have h_le : Nat.card ↥S ≤ Nat.card R' := Nat.le_of_dvd Nat.card_pos h_dvd
      have h_ne : Nat.card ↥S ≠ Nat.card R' := fun heq =>
        hS_coatom.1 (Subgroup.eq_top_of_card_eq _ heq)
      exact Nat.lt_of_le_of_ne h_le h_ne
    haveI hSpg : IsPGroup p ↥S := hR'.to_subgroup S
    have hc3S := class_le_three_descent hc3' S
    -- Inductive hypothesis: product-closure on `↥S`.
    have IHS : ∀ a b : ↥S, a ^ p = 1 → b ^ p = 1 → (a * b) ^ p = 1 :=
      ih (Nat.card ↥S) hScard hSpg hc3S rfl
    -- `Ω₁(↥S)` (as an `R'`-subgroup) is normal in `R'` and has exponent `p`.
    haveI : (Omega ↥S p 1).Characteristic := Omega.characteristic
    set H : Subgroup R' := (Omega ↥S p 1).map S.subtype with hH_def
    haveI hH_normal : H.Normal := by rw [hH_def]; infer_instance
    -- Every element of `H` has `p`-th power `1` (via `IHS` and `closure_le`).
    have hHpow : ∀ z ∈ H, z ^ p = 1 := by
      -- `{a : ↥S | a^p = 1}` is a subgroup of `↥S` (by `IHS`), containing the generators.
      let omega1S : Subgroup ↥S :=
        { carrier := {a : ↥S | a ^ p = 1}
          mul_mem' := fun {a b} ha hb => IHS a b ha hb
          one_mem' := one_pow p
          inv_mem' := fun {a} ha => by rw [Set.mem_setOf_eq, inv_pow, ha, inv_one] }
      have hΩle : Omega ↥S p 1 ≤ omega1S := by
        rw [Omega, Subgroup.closure_le]
        intro a ha
        change a ^ p = 1
        exact pow_one p ▸ ha
      intro z hz
      rw [hH_def, Subgroup.mem_map] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      have hap : a ^ p = 1 := by simpa [omega1S] using hΩle ha
      rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hap, Subgroup.coe_one]
    -- `x ∈ H`.
    have hxH : x ∈ H := by
      rw [hH_def, Subgroup.mem_map]
      refine ⟨⟨x, hxS⟩, ?_, by rw [Subgroup.coe_subtype]⟩
      exact Omega.mem_of_pow_eq_one (by rw [pow_one]; exact Subtype.ext (by simpa using hxp))
    -- The three collection commutators lie in `H`, hence have `p`-th power `1`.
    have hcomm_xy : ⁅y, x⁆ ∈ H := commutatorElement_mem_of_normal_right hH_normal hxH y
    have h45a : ⁅y, x⁆ ^ p = 1 := hHpow _ hcomm_xy
    have h45b : ⁅⁅y, x⁆, x⁆ ^ p = 1 :=
      hHpow _ (commutatorElement_mem_of_normal_right hH_normal hxH ⁅y, x⁆)
    have h45c : ⁅⁅y, x⁆, y⁆ ^ p = 1 :=
      hHpow _ (commutatorElement_mem_of_normal_left hH_normal hcomm_xy y)
    -- The three correction factors vanish: `p ∣ C(p,2), (p+1).choose 3` and the bases
    -- have `p`-th power `1`.
    have hpc2 : p ∣ p.choose 2 :=
      Nat.Prime.dvd_choose_self (Fact.out : p.Prime) (by norm_num) (by omega)
    have hpc3 : p ∣ (p + 1).choose 3 :=
      Nat.Prime.dvd_choose (Fact.out : p.Prime) (by omega) (by omega) (by omega)
    have e1 : ⁅y, x⁆ ^ (p.choose 2) = 1 := by
      obtain ⟨m2, hm2⟩ := hpc2; rw [hm2, pow_mul, h45a, one_pow]
    have e2 : ⁅⁅y, x⁆, x⁆ ^ ((p + 1).choose 3) = 1 := by
      obtain ⟨m3, hm3⟩ := hpc3; rw [hm3, pow_mul, h45b, one_pow]
    have e3 : ⁅⁅y, x⁆, y⁆ ^ (2 * (p + 1).choose 3) = 1 := by
      obtain ⟨m3, hm3⟩ := hpc3
      rw [show 2 * (p + 1).choose 3 = p * (2 * m3) by rw [hm3]; ring, pow_mul, h45c, one_pow]
    -- Collection `(4.4)` at `n = p`, roles `u = x, v = y`.
    rw [mul_pow_eq_collect_of_triple_central hc3' hc4' x y p, hxp, hyp, e1, e2, e3,
        mul_one, mul_one, mul_one, one_mul]

/-- **BG Proposition 4.3(b)** (mmd L1398-1472). For an odd prime `p`, a finite
`p`-group `R` with `cl(R) ≤ 2` or (`p > 3` and `cl(R) ≤ 3`), and `R' ⊆ Ω₁(R)`, the
`p`-th power map is "multiplicative": `(x * y) ^ p = x ^ p * y ^ p` for all `x, y`.

(The map `x ↦ x ^ p` is not a `MonoidHom` on a nonabelian group, so this is stated as
the bare equation rather than via `mk'`.)

The `cl ≤ 2` case follows from `mul_pow_eq_commutator_pow_mul_of_class_le_two`: the
single correction factor `⁅y, x⁆ ^ (p(p-1)/2)` vanishes since `⁅y, x⁆ ∈ R' ⊆ Ω₁(R)`
gives `⁅y, x⁆ ^ p = 1` and `p ∣ p(p-1)/2` for odd `p`. The `cl ≤ 3` case substitutes
`n = p` into the collection `(4.4)`; each correction commutator lies in `R' ⊆ Ω₁(R)`,
so (by part (a) = `omega1_pow_eq_one`) has `p`-th power `1`, and the exponents
`C(p,2), (p+1).choose 3` are divisible by `p`. -/
theorem pow_mul_eq_mul_pow_of_commutator_le_omega1 (hR : IsPGroup p R) (hp_odd : Odd p)
    (hcl : _root_.commutator R ≤ Subgroup.center R ∨
           (3 < p ∧ ∀ a b c : R, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center R))
    (hsub : _root_.commutator R ≤ Omega R p 1) (x y : R) :
    (x * y) ^ p = x ^ p * y ^ p := by
  -- `⁅y, x⁆ ∈ R' ⊆ Ω₁(R)`.
  have hyx_mem : ⁅y, x⁆ ∈ Omega R p 1 :=
    hsub (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x))
  have h1 : ⁅y, x⁆ ^ p = 1 := omega1_pow_eq_one hR hp_odd hcl hyx_mem
  rcases hcl with hc2 | ⟨hp3, hc3⟩
  · -- `cl ≤ 2`: single correction factor.
    rw [mul_pow_eq_commutator_pow_mul_of_class_le_two hc2 x y p]
    have hdvd : p ∣ p * (p - 1) / 2 := by
      obtain ⟨k, rfl⟩ := hp_odd
      rw [show 2 * k + 1 - 1 = 2 * k by omega,
        Nat.mul_div_assoc _ (Dvd.intro k rfl : 2 ∣ 2 * k), Nat.mul_div_cancel_left k two_pos]
      exact Dvd.intro k rfl
    obtain ⟨m, hm⟩ := hdvd
    rw [hm, pow_mul, h1, one_pow, one_mul]
  -- `cl ≤ 3`, `p > 3`.
  have hc4 := triple_commutator_eq_one_of_pointwise_central hc3
  -- The other two correction commutators are also in `R' ⊆ Ω₁(R)`.
  have h2 : ⁅⁅y, x⁆, x⁆ ^ p = 1 :=
    omega1_pow_eq_one hR hp_odd (Or.inr ⟨hp3, hc3⟩)
      (hsub (Subgroup.commutator_mem_commutator (Subgroup.mem_top ⁅y, x⁆) (Subgroup.mem_top x)))
  have h3 : ⁅⁅y, x⁆, y⁆ ^ p = 1 :=
    omega1_pow_eq_one hR hp_odd (Or.inr ⟨hp3, hc3⟩)
      (hsub (Subgroup.commutator_mem_commutator (Subgroup.mem_top ⁅y, x⁆) (Subgroup.mem_top y)))
  have hpc2 : p ∣ p.choose 2 :=
    Nat.Prime.dvd_choose_self (Fact.out : p.Prime) (by norm_num) (by omega)
  have hpc3 : p ∣ (p + 1).choose 3 :=
    Nat.Prime.dvd_choose (Fact.out : p.Prime) (by omega) (by omega) (by omega)
  have e1 : ⁅y, x⁆ ^ (p.choose 2) = 1 := by
    obtain ⟨m2, hm2⟩ := hpc2; rw [hm2, pow_mul, h1, one_pow]
  have e2 : ⁅⁅y, x⁆, x⁆ ^ ((p + 1).choose 3) = 1 := by
    obtain ⟨m3, hm3⟩ := hpc3; rw [hm3, pow_mul, h2, one_pow]
  have e3 : ⁅⁅y, x⁆, y⁆ ^ (2 * (p + 1).choose 3) = 1 := by
    obtain ⟨m3, hm3⟩ := hpc3
    rw [show 2 * (p + 1).choose 3 = p * (2 * m3) by rw [hm3]; ring, pow_mul, h3, one_pow]
  rw [mul_pow_eq_collect_of_triple_central hc3 hc4 x y p, e1, e2, e3, mul_one, mul_one, mul_one]

end Prop43ClassThree

/-! ## §4B: existence of elementary abelian `E_{p²}` subgroups (Lemma 4.5(a))

BG Lemma 4.5(a) (mmd L1474, BG defers to **G** Theorem 5.4.10): an odd noncyclic
`p`-group `R` possesses a **normal** elementary abelian subgroup of order `p²`.

We supply the pieces that the repo infrastructure proves cleanly and rigorously:

* `exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic`: an odd noncyclic
  `p`-group has *some* elementary abelian `E_{p²}` (not yet normal). This is the
  contrapositive of Isaacs Thm 6.11 (`isCyclic_of_subgroups_card_prime_unique_of_odd`)
  followed by the order-`p²` construction in `ElementaryAbelian.lean`.
* `exists_normal_isElementaryAbelian_card_prime_sq_of_omega1_center_not_isCyclic`:
  if moreover `Ω₁(Z(R))` is noncyclic, the `E_{p²}` can be taken central, hence
  **normal**. This is the (clean) abelian-center case of 4.5(a).

The remaining (nonabelian, cyclic-center) case of the *normal* refinement is exactly
Gorenstein 5.4.10's substance and is deferred. Parts (b), (c) of Lemma 4.5 are also
deferred (4.5(b) needs the cyclic-maximal-subgroup classification **G** 5.4.3/5.4.4;
4.5(c) needs 4.5(a) + Prop 4.3(a) applied to `Z₂(R)` together with the *normal*
refinement). -/

section ElementaryAbelianExistence

open OddOrder.GroupTheory

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- A noncyclic finite `p`-group (`p` odd) has two distinct subgroups of order `p`.

This is the contrapositive of Isaacs Thm 6.11
(`OddOrder.Isaacs.Ch06.isCyclic_of_subgroups_card_prime_unique_of_odd`): a finite
odd `p`-group with a *unique* subgroup of order `p` is cyclic. -/
theorem exists_distinct_subgroups_card_prime_of_not_isCyclic (hR : IsPGroup p R)
    (hp_odd : Odd p) (hnc : ¬ IsCyclic R) :
    ∃ K L : Subgroup R, Nat.card K = p ∧ Nat.card L = p ∧ K ≠ L := by
  -- If no two order-`p` subgroups were distinct, `R` would be cyclic (Thm 6.11).
  have huniq : (∀ K L : Subgroup R, Nat.card K = p → Nat.card L = p → K = L) →
      IsCyclic R :=
    fun h => OddOrder.Isaacs.Ch06.isCyclic_of_subgroups_card_prime_unique_of_odd hR hp_odd h
  by_contra h
  -- `push Not` is deprecated in this toolchain; unfold the negated existential by hand.
  simp only [not_exists, not_and, ne_eq, not_not] at h
  exact hnc (huniq fun K L hK hL => h K L hK hL)

/-- **BG Lemma 4.5(a)** (existence half, normality deferred). An odd noncyclic
`p`-group `R` contains an elementary abelian subgroup of order `p²`.

Proof: by `exists_distinct_subgroups_card_prime_of_not_isCyclic` there are two
distinct order-`p` subgroups; `ElementaryAbelian.lean`'s
`exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_ne` builds an
`E_{p²}` from them. -/
theorem exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic (hR : IsPGroup p R)
    (hp_odd : Odd p) (hnc : ¬ IsCyclic R) :
    ∃ E : Subgroup R, E.IsElementaryAbelian p ∧ Nat.card E = p ^ 2 := by
  obtain ⟨K, L, hK, hL, hKL⟩ :=
    exists_distinct_subgroups_card_prime_of_not_isCyclic hR hp_odd hnc
  obtain ⟨E, hE_elem, hE_card⟩ :=
    hR.exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_ne hK hL hKL
  exact ⟨E, hE_elem, hE_card⟩

/-- `Ω₁(Z(R))` as a subgroup of `R`: the central elements of order dividing `p`.
The center is abelian, so this is the genuine `Ω₁` (the set is closed under
multiplication). -/
private def omega1Center (R : Type*) [Group R] (p : ℕ) : Subgroup R :=
  omega1OfAbelian R (Subgroup.center R) p
    (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm)

omit [Finite R] [Fact p.Prime] in
private theorem omega1Center_le_center : omega1Center R p ≤ Subgroup.center R :=
  fun _ hg => hg.1

omit [Finite R] [Fact p.Prime] in
private theorem mem_omega1Center {g : R} :
    g ∈ omega1Center R p ↔ g ∈ Subgroup.center R ∧ g ^ p = 1 := Iff.rfl

/-- **BG Lemma 4.5(a)** (the *normal* conclusion, abelian-center case). If the
central subgroup `Ω₁(Z(R))` of a finite `p`-group `R` is noncyclic — equivalently
`p² ∣ |Ω₁(Z(R))|`, the situation when `Z(R)` itself is noncyclic — then `R` has a
**normal** elementary abelian subgroup of order `p²`.

Proof: `Ω₁(Z(R))` is central, hence its `p²`-order subgroup `B` (obtained from
`Sylow.exists_subgroup_card_pow_prime_of_le_card`, valid since `B ≤ Ω₁(Z(R))` is a
`p`-group of order `≥ p²`) is central in `R`, therefore normal; and `B`, being a
subgroup of the elementary abelian group `Ω₁(Z(R))`, is itself elementary abelian.

This is the case of Lemma 4.5(a) that the repo proves cleanly. The general (cyclic
center, e.g. extraspecial) case is Gorenstein 5.4.10 and is deferred. -/
theorem exists_normal_isElementaryAbelian_card_prime_sq_of_prime_sq_dvd_card_omega1Center
    (hsq : p ^ 2 ∣ Nat.card (omega1Center R p)) :
    ∃ E : Subgroup R, E.Normal ∧ E.IsElementaryAbelian p ∧ Nat.card E = p ^ 2 := by
  -- `Ω₁(Z(R))` is an elementary abelian `p`-group (central, exponent dividing `p`).
  have hΩ_elem : (omega1Center R p).IsElementaryAbelian p := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · -- commutativity: both lie in the center.
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp (omega1Center_le_center x.2) (y : R)).symm
    · -- `x ^ p = 1` by definition of `Ω₁`.
      apply Subtype.ext
      have : (x : R) ^ p = 1 := (mem_omega1Center.mp x.2).2
      simpa using this
  have hΩ_pgroup : IsPGroup p (omega1Center R p) := hΩ_elem.isPGroup
  -- A `p²`-order subgroup `B` of `↥(Ω₁(Z(R)))` (`p² ∣ |Ω| ⇒ p² ≤ |Ω|`).
  have hΩ_le : p ^ 2 ≤ Nat.card (omega1Center R p) := Nat.le_of_dvd Nat.card_pos hsq
  obtain ⟨B, hB_card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card (n := 2) Fact.out hΩ_pgroup hΩ_le
  -- Push `B` into `R`; the image lands in `Ω₁(Z(R)) ≤ Z(R)`.
  set E : Subgroup R := B.map (omega1Center R p).subtype with hE_def
  have hE_le_Ω : E ≤ omega1Center R p := by
    rw [hE_def]; exact Subgroup.map_subtype_le B
  have hE_le_center : E ≤ Subgroup.center R := le_trans hE_le_Ω omega1Center_le_center
  refine ⟨E, ?_, ?_, ?_⟩
  · -- `E` central ⇒ normal.
    refine ⟨fun n hn g => ?_⟩
    have hgn : g * n = n * g := Subgroup.mem_center_iff.mp (hE_le_center hn) g
    simpa [mul_assoc, hgn] using hn
  · -- `E` elementary abelian: image of the elementary abelian `B` under an injective map.
    have hB_elem : B.IsElementaryAbelian p := hΩ_elem.to_subgroup B
    exact hB_elem.map (omega1Center R p).subtype_injective
  · -- `|E| = |B| = p²`.
    rw [hE_def, Subgroup.card_map_of_injective (omega1Center R p).subtype_injective, hB_card]

end ElementaryAbelianExistence

/-! ## §4C: `SCN₃(R)` empty ⟺ `r(R) ≤ 2` (Lemma 4.7)

BG Lemma 4.7 (mmd L1500-1502): for an odd prime `p` and a `p`-group `R`, `SCN₃(R)` is
empty if and only if `r(R) ≤ 2`.

In the repo encoding (`OddOrder.GroupTheory.SCN`, `OddOrder.GroupTheory.PRank`):

* `SCN₃(R) = ∅` is `∀ A : Subgroup R, ¬ IsSCN₃ p A`, where
  `IsSCN₃ p A := IsSCN A ∧ 3 ≤ pRank A p` (the BG generator number `m(A)` of an abelian
  `p`-group `A` is its `p`-rank `pRank A p`, since `|Ω₁(A)| = p^{m(A)}`).
* `r(R) ≤ 2` is `pRank R p ≤ 2`: for a `p`-group `R` every abelian `q`-subgroup with
  `q ≠ p` is trivial, so BG's all-primes rank `r(R) = max_q r_q(R)` collapses to the
  single `p`-rank `r_p(R) = pRank R p`.

**This file proves the easy (`⇐`) direction** of BG's iff — *"Obviously, `SCN₃(R)` is
empty if `r(R) ≤ 2`"* — as `scn3_empty_of_pRank_le_two`. The substance is pure
monotonicity of `pRank` under subgroup inclusion (`pRank_mono_of_le`): an SCN subgroup
`A` of rank `≥ 3` would force `3 ≤ pRank A p ≤ pRank R p ≤ 2`, impossible.

The hard converse (`SCN₃(R) = ∅ ⇒ r(R) ≤ 2`, BG = **G** Theorem 5.4.15(i), Gorenstein
mmd L4214-4231) is **deferred, with no `sorry`**: it rests on Gorenstein Lemma 5.4.14
(for a maximal abelian normal `A` with `m(A) = d_n(P)`, `Ω₁(C_P(Ω₁(A))) = Ω₁(A)` — a
`p`-odd induction on a chief-like chain `B₁ ◁ ⋯ ◁ Bₙ` plus an exponent-`p` argument via
BG Lemma 4.2 / Prop 4.3) together with the `GL(2,p)` linear bound (Gorenstein 2.8.1) to
exclude an elementary abelian `E_{p³}`. That converse is what makes `SCN₃ = ∅` a genuine
*rank* statement; the easy direction here is the one BG itself calls "obvious" and is the
piece §5/§7 (Thompson transitivity)/§10 (`α(M) = {p : r_p(M) ≥ 3}`) actually consume to
*recognise* `SCN₃`. -/

section SCN3Empty

open OddOrder.GroupTheory

variable {R : Type*} [Group R] [Finite R] {p : ℕ}

/-- **BG Lemma 4.7**, the easy (`⇐`) direction — *"Obviously, `SCN₃(R)` is empty if
`r(R) ≤ 2`"* (mmd L1502).

If the `p`-rank of `R` is at most `2` then `R` has no `SCN₃` subgroup: any subgroup `A`
with `3 ≤ pRank A p` (in particular any `IsSCN₃ p A`) would violate monotonicity of the
`p`-rank, since `pRank A p ≤ pRank R p ≤ 2` for `A ≤ R` (`pRank_mono_of_le`).

This is the half of BG's iff that §5 / §7 (Thompson transitivity) / §10 use to *detect*
`SCN₃`. The hard converse `SCN₃(R) = ∅ ⇒ pRank R p ≤ 2` is **G** Theorem 5.4.15(i)
(Gorenstein), deferred (see the section docstring); note it needs neither the SCN nor the
self-centralizing structure of `A` — only `3 ≤ pRank A p` and `A ≤ R` — so we state the
hypothesis-minimal form. -/
theorem not_le_pRank_of_pRank_le_two (hr : pRank R p ≤ 2) (A : Subgroup R) :
    ¬ 3 ≤ pRank A p := by
  intro hA
  -- `3 ≤ pRank A p ≤ pRank R p ≤ 2`, contradiction.
  have : (3 : ℕ) ≤ 2 := hA.trans ((pRank_mono_of_le A).trans hr)
  omega

/-- **BG Lemma 4.7**, the easy (`⇐`) direction, SCN form: if `r(R) ≤ 2` (i.e.
`pRank R p ≤ 2`) then `SCN₃(R)` is empty, `∀ A, ¬ IsSCN₃ p A`.

Immediate from `not_le_pRank_of_pRank_le_two` applied to the rank component of `IsSCN₃`.
This is the v1 goal opening the §4 dependency of §5 / §7 (Thompson transitivity) / §10. -/
theorem scn3_empty_of_pRank_le_two (hr : pRank R p ≤ 2) (A : Subgroup R) :
    ¬ IsSCN₃ p A := fun h => not_le_pRank_of_pRank_le_two hr A h.le_pRank

/-- **`SCN₃(R) = ∅ ⇒ d_n(R) ≤ 2`** — the *translation* half of the hard direction of BG
Lemma 4.7 (= **G** Theorem 5.4.15(i)). In a finite `p`-group with no `SCN₃` subgroup, every
**normal abelian** subgroup has `p`-rank `≤ 2`.

Each abelian normal `B` lies in a maximal abelian normal `A`
(`exists_maximalAbelianNormal_ge`), which is `SCN` in a `p`-group
(`IsMaximalAbelianNormal.isSCN`); since `A` is `SCN` but not `SCN₃`, we get `pRank A p ≤ 2`,
and `pRank B p ≤ pRank A p` by monotonicity (`pRank_le_of_injective` on the inclusion
`B ↪ A`). This `d_n(R) ≤ 2` statement is the genuine hypothesis fed to `G` Theorem 4.15(i)
(`pRank ≤ 2` for the *whole* group); it is **not** itself a rank bound on `R` (it constrains
only normal abelian subgroups), so it does not pre-suppose the conclusion. -/
theorem normalAbelian_pRank_le_two_of_scn3_empty [Fact p.Prime] (hR : IsPGroup p R)
    (hSCN : ∀ A : Subgroup R, ¬ IsSCN₃ p A)
    {B : Subgroup R} (hBnorm : B.Normal) (hBcomm : IsMulCommutative B) :
    pRank B p ≤ 2 := by
  obtain ⟨A, hBA, hAmax⟩ := exists_maximalAbelianNormal_ge hBnorm hBcomm
  have hAscn : IsSCN A := hAmax.isSCN hR
  have hApr : pRank A p ≤ 2 := by
    by_contra h
    exact hSCN A ⟨hAscn, by omega⟩
  have hmono : pRank B p ≤ pRank A p :=
    pRank_le_of_injective (Subgroup.inclusion_injective hBA)
  omega

end SCN3Empty

/-! ## §4C: BG Lemma 4.5(b) — cyclic subgroup of index `p` ⇒ `Ω₁(R) ≅ E_{p²}`

BG Lemma 4.5(b) (mmd L1484, BG defers to **G** Theorems 5.4.3/5.4.4): for `p` odd, a
**noncyclic** `p`-group `R` possessing a **cyclic** subgroup of index `p` has `Ω₁(R)`
elementary abelian of order `p²`.

BG's deferral is to the `M_m(p)` classification (Gorenstein 5.4.4: an odd nonabelian
`p`-group with a cyclic maximal subgroup is the modular group `M_m(p)`). **We do not
reconstruct the `M_m(p)` isomorphism.** The genuine content is `|Ω₁(R)| ≤ p²`, obtained
through a uniform class-`≤ 2` route that is valid precisely because `p` is odd:

* **`commutator R ≤ Z(R)`** (`commutator_le_center_of_cyclic_index_prime`): the Gorenstein
  5.4.4 Frattini computation. With `H = ⟨x⟩` cyclic of index `p`, `H ⊴ R` and `x^p ∈ Z(R)`;
  the latter is the irreducible number-theoretic heart, and we discharge it by **reusing the
  Isaacs Thm 6.12 conjugation engine** (`OddOrder.Isaacs.Ch06`): for any `a ∈ R`,
  `a x a⁻¹ = x^i` with `i^p ≡ 1 [ZMOD p^e]` (`conj_exponent_pow_modEq_one_of_pow_mem_zpowers`,
  using `a^p ∈ H`), and Isaacs Lemma 6.16 (`pow_prime_modEq_one_cases`) forces — for `p`
  *odd*, all `p = 2` branches vanish — `i ≡ 1 [ZMOD p^(e-1)]`, whence `a x^p a⁻¹ = x^p`
  (`conj_exponent_not_modEq_one_of_pow_conj_ne`, contrapositive). With `x^p` central,
  `R⧸⟨x^p⟩` has order `p²` (`= |R:H|·|H:⟨x^p⟩|`), hence is abelian, so `R' ≤ ⟨x^p⟩ ≤ Z(R)`.
* `cl(R) ≤ 2` + `p` odd ⇒ `Ω₁(R)` has exponent `p` (`Omega.pow_eq_one_of_class_le_two`),
  hence is elementary abelian.
* rank bound **`|Ω₁(R)| ≤ p²`** (`card_omega1_le_prime_sq_of_cyclic_index_prime`): with
  `K := Ω₁(R) ⊓ H`, `|K| ≤ p` (`K ≤ H` cyclic and exp `p`) and `Ω₁/K ↪ R/H` of order `p`
  (`(Ω₁⊓H).relIndex Ω₁ ∣ H.index = p`), so `|Ω₁| = |K|·(Ω₁⊓H).relIndex Ω₁ ≤ p·p`.
* noncyclic + `|Ω₁| ≤ p²` ⇒ `E_{p²}` via the prime-square classification
  (`isElementaryAbelian_card_prime_sq_of_card_le_prime_sq_of_not_isCyclic`); `Ω₁` is
  noncyclic because the two distinct order-`p` subgroups of `R` both lie in `Ω₁`.

The `|Ω₁(R)| ≤ p²` bound is **proven from the cyclic-index-`p` hypothesis**, never assumed. -/

section CyclicIndexP

open OddOrder.GroupTheory

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- ⚠ GENUINE SUB-LEMMA (the heart of 4.5(b)): for `p` odd and `H = ⟨x⟩ ⊴ R` cyclic of
index `p` in a `p`-group `R`, the `p`-th power `x^p` is central.

This is the Gorenstein 5.4.4 Frattini step, and where odd `p` is essential. For any
`a ∈ R`, conjugation acts on the normal cyclic `H = ⟨x⟩` as `a x a⁻¹ = x^i`; since
`a^p ∈ H` (as `|R:H| = p`), Isaacs Lemma 6.5-style bookkeeping gives `i^p ≡ 1 [ZMOD p^e]`
(`orderOf x = p^e`), and Isaacs Lemma 6.16 (`pow_prime_modEq_one_cases`) — whose `p = 2`
alternatives are excluded by `p` odd — forces `i ≡ 1 [ZMOD p^(e-1)]`, which is exactly
`a x^p a⁻¹ = x^p` (`conj_exponent_not_modEq_one_of_pow_conj_ne`, contrapositive). -/
theorem pow_mem_center_of_cyclic_index_prime
    (hR : IsPGroup p R) (hp_odd : Odd p) {x : R} (hHidx : (Subgroup.zpowers x).index = p) :
    x ^ p ∈ Subgroup.center R := by
  set H : Subgroup R := Subgroup.zpowers x with hH_def
  -- `H ⊴ R` (index `p` = `minFac` in a `p`-group).
  haveI hH_normal : H.Normal := by
    have hp_prime : p.Prime := Fact.out
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR
    have hm_ne : m ≠ 0 := by
      rintro rfl
      have : Nat.card R = 1 := by simpa using hm
      have hdvd : p ∣ 1 := this ▸ hHidx ▸ H.index_dvd_card
      exact hp_prime.not_dvd_one hdvd
    have hmin : (Nat.card R).minFac = p := by rw [hm, hp_prime.pow_minFac hm_ne]
    exact Subgroup.normal_of_index_eq_minFac_card (by rw [hHidx, hmin])
  -- `orderOf x = p^e`.
  obtain ⟨e, he_order⟩ := (IsPGroup.iff_orderOf.mp hR) x
  rw [Subgroup.mem_center_iff]
  intro a
  -- It suffices to show `a * x^p * a⁻¹ = x^p` (i.e. `a` and `x^p` commute).
  suffices hfix : a * x ^ p * a⁻¹ = x ^ p by
    calc a * x ^ p = (a * x ^ p * a⁻¹) * a := by group
      _ = x ^ p * a := by rw [hfix]
  -- Degenerate case `e = 0` (`x = 1`): the goal is about `x^p = 1`, trivially fixed.
  rcases Nat.eq_zero_or_pos e with he0 | he_pos
  · have hx1 : x = 1 := orderOf_eq_one_iff.mp (by rw [he_order, he0, pow_zero])
    rw [hx1]; group
  -- Main case `e ≥ 1`. Conjugation by `a` sends `x` into `H = ⟨x⟩`: `a x a⁻¹ = x^i`.
  have hconj_mem : a * x * a⁻¹ ∈ Subgroup.zpowers x :=
    hH_normal.conj_mem x (Subgroup.mem_zpowers x) a
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hconj_mem
  have h_conj : a * x * a⁻¹ = x ^ i := hi.symm
  -- `a^p ∈ H = ⟨x⟩` (since `|R : H| = p`).
  have ha_pow_mem : a ^ p ∈ Subgroup.zpowers x := by
    have := H.pow_index_mem a
    rwa [hHidx] at this
  -- `i^p ≡ 1 [ZMOD p^e]`.
  have hpow_mod : i ^ p ≡ 1 [ZMOD ((p : ℤ) ^ e)] :=
    OddOrder.Isaacs.Ch06.conj_exponent_pow_modEq_one_of_pow_mem_zpowers
      he_order h_conj ha_pow_mem
  -- For `p` odd, Lemma 6.16 leaves only `i ≡ 1 [ZMOD p^(e-1)]`.
  have hp_ne_two : p ≠ 2 := by
    rintro rfl; exact (Nat.not_odd_iff_even.mpr (by norm_num)) hp_odd
  have hmod_one : i ≡ 1 [ZMOD ((p : ℤ) ^ (e - 1))] := by
    rcases OddOrder.Isaacs.Ch06.pow_prime_modEq_one_cases (Fact.out : p.Prime) he_pos hpow_mod
      with h | h2 | h2
    · exact h
    · exact absurd h2.1 hp_ne_two
    · exact absurd h2.1 hp_ne_two
  -- `i ≡ 1 [ZMOD p^(e-1)]` ⇒ `a x^p a⁻¹ = x^p` (contrapositive of the noncentrality lemma).
  by_contra hne
  exact OddOrder.Isaacs.Ch06.conj_exponent_not_modEq_one_of_pow_conj_ne
    he_pos he_order h_conj hne hmod_one

/-- ⚠ GENUINE SUB-LEMMA (the heart of 4.5(b)): for `p` odd and `R` a `p`-group with a
cyclic subgroup `H = ⟨x⟩` of index `p`, the nilpotence class is `≤ 2`,
`commutator R ≤ Z(R)`.

`H ⊴ R` and `x^p ∈ Z(R)` (`pow_mem_center_of_cyclic_index_prime`). Then `⟨x^p⟩ ⊴ R` is
central, and `R⧸⟨x^p⟩` has order `p²` (`= |R:H|·|H:⟨x^p⟩| = p·p`), hence is abelian, so
`commutator R ≤ ⟨x^p⟩ ≤ Z(R)`. The order computation uses `|H| = orderOf x = p^e`
(`e ≥ 1`) and `|⟨x^p⟩| = orderOf (x^p) = p^(e-1)`. -/
theorem commutator_le_center_of_cyclic_index_prime
    (hR : IsPGroup p R) (hp_odd : Odd p) {x : R} (hHidx : (Subgroup.zpowers x).index = p) :
    _root_.commutator R ≤ Subgroup.center R := by
  have hp_prime : p.Prime := Fact.out
  set H : Subgroup R := Subgroup.zpowers x with hH_def
  -- `x^p` is central.
  have hxp_center : x ^ p ∈ Subgroup.center R :=
    pow_mem_center_of_cyclic_index_prime hR hp_odd hHidx
  -- `N := ⟨x^p⟩` is central, hence normal.
  set N : Subgroup R := Subgroup.zpowers (x ^ p) with hN_def
  have hN_le_center : N ≤ Subgroup.center R := by
    rw [hN_def, Subgroup.zpowers_le]; exact hxp_center
  haveI hN_normal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgn : g * n = n * g := Subgroup.mem_center_iff.mp (hN_le_center hn) g
    simpa [mul_assoc, hgn] using hn
  -- `orderOf x = p^e`.
  obtain ⟨e, he_order⟩ := (IsPGroup.iff_orderOf.mp hR) x
  -- Degenerate case `e = 0` (`x = 1`): `H = ⊥`, `|R| = p`, so `R` is cyclic (hence
  -- commutative) and `commutator R = ⊥ ≤ Z(R)`.
  rcases Nat.eq_zero_or_pos e with he0 | he_pos
  · have hx1 : x = 1 := orderOf_eq_one_iff.mp (by rw [he_order, he0, pow_zero])
    have hHbot : H = ⊥ := by rw [hH_def, hx1, Subgroup.zpowers_one_eq_bot]
    have hcardR : Nat.card R = p := by
      have hidx : (⊥ : Subgroup R).index = Nat.card R := Subgroup.index_bot
      rw [← hHbot, hHidx] at hidx; exact hidx.symm
    haveI : IsCyclic R := isCyclic_of_prime_card hcardR
    exact (commutator_eq_bot R).le.trans bot_le
  -- Main case `e ≥ 1`. `|R| = p · orderOf x = p^(e+1)`.
  have hcardR : Nat.card R = p ^ (e + 1) := by
    have h1 : Nat.card H * H.index = Nat.card R := Subgroup.card_mul_index H
    have hcardH : Nat.card H = p ^ e := by rw [hH_def, Nat.card_zpowers, he_order]
    rw [hcardH, hHidx, ← pow_succ] at h1
    exact h1.symm
  -- `|N| = orderOf (x^p) = p^(e-1)`.
  have hcardN : Nat.card N = p ^ (e - 1) := by
    rw [hN_def, Nat.card_zpowers, orderOf_pow x, he_order]
    -- `gcd (p^e) p = p`, so `p^e / p = p^(e-1)`.
    have hgcd : Nat.gcd (p ^ e) p = p := by
      have hdvd : p ∣ p ^ e := dvd_pow_self p he_pos.ne'
      exact Nat.gcd_eq_right hdvd
    rw [hgcd]
    -- `p^e / p = p^e / p^1 = p^(e-1)`.
    have : p ^ e / p = p ^ e / p ^ 1 := by rw [pow_one]
    rw [this, Nat.pow_div he_pos hp_prime.pos]
  -- `R ⧸ N` has order `p²`, hence abelian.
  have hcard_quot : Nat.card (R ⧸ N) = p ^ 2 := by
    have hmul : Nat.card N * N.index = Nat.card R := Subgroup.card_mul_index N
    rw [hcardN, hcardR] at hmul
    have hNidx : N.index = p ^ 2 := by
      have he1 : (e - 1) + 2 = e + 1 := by omega
      have : p ^ (e - 1) * N.index = p ^ (e - 1) * p ^ 2 := by
        rw [hmul, ← pow_add, he1]
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp_prime.pos _) this
    rw [← Subgroup.index_eq_card]; exact hNidx
  have hquot_comm : ∀ a b : R ⧸ N, a * b = b * a :=
    isMulCommutative_iff.mp
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hcard_quot)
  -- `commutator R ≤ N ≤ Z(R)`.
  have hcomm_le_N : _root_.commutator R ≤ N :=
    hN_normal.quotient_commutative_iff_commutator_le.mp ⟨⟨hquot_comm⟩⟩
  exact hcomm_le_N.trans hN_le_center

/-- ⚠ GENUINE SUB-LEMMA (the rank bound of 4.5(b)): for `p` odd and `R` a `p`-group with a
cyclic subgroup `H = ⟨x⟩` of index `p`, `|Ω₁(R)| ≤ p²`.

Set `Ω := Ω₁(R)` and `K := Ω ⊓ H`. By `commutator_le_center_of_cyclic_index_prime`,
`cl(R) ≤ 2`, so every element of `Ω` has `p`-th power `1` (`Omega.pow_eq_one_of_class_le_two`).
Hence `K ≤ H` is a finite subgroup of the cyclic `H` with exponent dividing `p`, so
`|K| ∣ p`. The second isomorphism `Ω⧸K ↪ R⧸H` (order `p`) gives
`(Ω⊓H).relIndex Ω ∣ H.index = p`. Then
`|Ω| = |K| · (Ω⊓H).relIndex Ω ≤ p · p`. -/
theorem card_omega1_le_prime_sq_of_cyclic_index_prime
    (hR : IsPGroup p R) (hp_odd : Odd p) {x : R} (hHidx : (Subgroup.zpowers x).index = p) :
    Nat.card (Omega R p 1) ≤ p ^ 2 := by
  set H : Subgroup R := Subgroup.zpowers x with hH_def
  set Ω : Subgroup R := Omega R p 1 with hΩ_def
  have hp_prime : p.Prime := Fact.out
  -- `H ⊴ R`.
  haveI hH_normal : H.Normal := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR
    have hm_ne : m ≠ 0 := by
      rintro rfl
      have : Nat.card R = 1 := by simpa using hm
      have hdvd : p ∣ 1 := this ▸ hHidx ▸ H.index_dvd_card
      exact hp_prime.not_dvd_one hdvd
    have hmin : (Nat.card R).minFac = p := by rw [hm, hp_prime.pow_minFac hm_ne]
    exact Subgroup.normal_of_index_eq_minFac_card (by rw [hHidx, hmin])
  -- `cl(R) ≤ 2`.
  have hcl : _root_.commutator R ≤ Subgroup.center R :=
    commutator_le_center_of_cyclic_index_prime hR hp_odd hHidx
  -- Every element of `Ω` has `p`-th power `1`.
  have hΩ_exp : ∀ g ∈ Ω, g ^ p = 1 := fun g hg =>
    Omega.pow_eq_one_of_class_le_two hp_odd hcl hg
  -- (1) `|K| ∣ p` where `K := Ω ⊓ H`.
  set K : Subgroup R := Ω ⊓ H with hK_def
  have hK_card_dvd : Nat.card K ∣ p := by
    -- `K` is a subgroup of cyclic `H`, hence cyclic; its exponent divides `p`.
    haveI hHcyc : IsCyclic H := by rw [hH_def]; exact Subgroup.isCyclic_zpowers x
    haveI hK_cyc : IsCyclic K := by
      -- `K.subgroupOf H` is a subgroup of the cyclic `H`, hence cyclic; transport to `K`.
      have hKH : K ≤ H := inf_le_right
      haveI : IsCyclic (K.subgroupOf H) := Subgroup.isCyclic _
      exact isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hKH).surjective
    -- exponent of `K` divides `p`.
    have hexp_dvd : Monoid.exponent K ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro g
      apply Subtype.ext
      have hgΩ : (g : R) ∈ Ω := (inf_le_left : K ≤ Ω) g.2
      rw [SubmonoidClass.coe_pow]; simpa using hΩ_exp (g : R) hgΩ
    -- cyclic ⇒ `card = exponent`.
    have : Nat.card K = Monoid.exponent K := IsCyclic.exponent_eq_card.symm
    rw [this]; exact hexp_dvd
  have hK_le : Nat.card K ≤ p := Nat.le_of_dvd hp_prime.pos hK_card_dvd
  -- (2) `(Ω ⊓ H).relIndex Ω ∣ p`.
  have hrel_dvd : (Ω ⊓ H).relIndex Ω ∣ p := by
    have h1 : (Ω ⊓ H).relIndex Ω = H.relIndex Ω := by
      rw [inf_comm]; exact Subgroup.inf_relIndex_right H Ω
    rw [h1]
    have h2 : H.relIndex Ω ∣ H.index := Subgroup.relIndex_dvd_index_of_normal H Ω
    rw [hHidx] at h2; exact h2
  have hrel_le : (Ω ⊓ H).relIndex Ω ≤ p := Nat.le_of_dvd hp_prime.pos hrel_dvd
  -- `|Ω| = |K| · (Ω ⊓ H).relIndex Ω`.
  have hΩ_factor : Nat.card K * (Ω ⊓ H).relIndex Ω = Nat.card Ω := by
    have hbot1 : (⊥ : Subgroup R).relIndex K = Nat.card K := Subgroup.relIndex_bot_left K
    have hbot2 : (⊥ : Subgroup R).relIndex Ω = Nat.card Ω := Subgroup.relIndex_bot_left Ω
    have hmrr := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup R) K Ω
      (bot_le) (inf_le_left)
    rw [hbot1, hbot2] at hmrr
    -- `(⊥).relIndex K = Nat.card K` and `K.relIndex Ω = (Ω⊓H).relIndex Ω`.
    simpa [hK_def] using hmrr
  -- Combine: `|Ω| ≤ p · p = p²`.
  rw [← hΩ_factor]
  calc Nat.card K * (Ω ⊓ H).relIndex Ω ≤ p * p := Nat.mul_le_mul hK_le hrel_le
    _ = p ^ 2 := by rw [sq]

/-- **BG Lemma 4.5(b)**, generator form (**G** Thms 5.4.3/5.4.4). For `p` odd, a noncyclic
`p`-group `R` such that `⟨x⟩ = Subgroup.zpowers x` has index `p` has `Ω₁(R)` elementary
abelian of order `p²`.

The hard content `|Ω₁(R)| ≤ p²` is `card_omega1_le_prime_sq_of_cyclic_index_prime`
(proven from the cyclic-index-`p` hypothesis via `cl(R) ≤ 2`, NOT hoisted). The finisher
is the prime-square classification. `Ω₁(R)` is noncyclic because the two distinct order-`p`
subgroups of `R` (Isaacs Thm 6.11) both lie in `Ω₁(R)`. The BG-facing statement
(`isElementaryAbelian_omega1_of_isCyclic_index_prime`) takes an abstract cyclic subgroup
`H` of index `p` and is reduced to this by extracting a generator. -/
theorem isElementaryAbelian_omega1_of_cyclic_index_prime
    (hR : IsPGroup p R) (hp_odd : Odd p) (hnc : ¬ IsCyclic R)
    {x : R} (hHidx : (Subgroup.zpowers x).index = p) :
    (Omega R p 1).IsElementaryAbelian p ∧ Nat.card (Omega R p 1) = p ^ 2 := by
  have hp_prime : p.Prime := Fact.out
  set Ω : Subgroup R := Omega R p 1 with hΩ_def
  -- `Ω` is a `p`-group.
  have hΩ_pgroup : IsPGroup p Ω := hR.to_subgroup _
  -- `|Ω| ≤ p²` (the genuine crux).
  have hle : Nat.card Ω ≤ p ^ 2 :=
    card_omega1_le_prime_sq_of_cyclic_index_prime hR hp_odd hHidx
  -- `Ω` is noncyclic: pull `R`'s two distinct order-`p` subgroups into `Ω`.
  have hΩ_nc : ¬ IsCyclic Ω := by
    obtain ⟨Ksub, Lsub, hK, hL, hKL⟩ :=
      exists_distinct_subgroups_card_prime_of_not_isCyclic hR hp_odd hnc
    -- order-`p` subgroups consist of `p`-torsion, hence sit inside `Ω`.
    have mem_omega_of_card_p : ∀ (M : Subgroup R), Nat.card M = p → M ≤ Ω := by
      intro M hM g hg
      have hgp : g ^ p = 1 := by
        have hM1 : (⟨g, hg⟩ : M) ^ Nat.card M = 1 := pow_card_eq_one'
        have hcoe : g ^ Nat.card M = 1 := by
          have := congrArg (Subtype.val) hM1
          rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
        rwa [hM] at hcoe
      exact Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hgp)
    have hKΩ : Ksub ≤ Ω := mem_omega_of_card_p Ksub hK
    have hLΩ : Lsub ≤ Ω := mem_omega_of_card_p Lsub hL
    intro hcyc
    haveI : IsCyclic Ω := hcyc
    -- `Ω` has exponent dividing `p` (class ≤ 2 + odd), and cyclic ⇒ `|Ω| = exponent ∣ p`.
    have hcl : _root_.commutator R ≤ Subgroup.center R :=
      commutator_le_center_of_cyclic_index_prime hR hp_odd hHidx
    have hexp_dvd : Monoid.exponent Ω ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro g; apply Subtype.ext
      rw [SubmonoidClass.coe_pow]
      simpa using Omega.pow_eq_one_of_class_le_two hp_odd hcl g.2
    have hΩcard_dvd : Nat.card Ω ∣ p := by
      rw [IsCyclic.exponent_eq_card (α := Ω)] at hexp_dvd; exact hexp_dvd
    -- `|Ksub| = p ≤ |Ω| ∣ p` ⇒ `|Ω| = p`, then `Ksub = Ω` and `Lsub = Ω` by card.
    have hp_le_Ω : p ≤ Nat.card Ω := hK ▸ Subgroup.card_le_of_le hKΩ
    have hΩ_le_p : Nat.card Ω ≤ p := Nat.le_of_dvd hp_prime.pos hΩcard_dvd
    have hΩcard : Nat.card Ω = p := le_antisymm hΩ_le_p hp_le_Ω
    have hKeq : Ksub = Ω := Subgroup.eq_of_le_of_card_ge hKΩ (by rw [hΩcard, hK])
    have hLeq : Lsub = Ω := Subgroup.eq_of_le_of_card_ge hLΩ (by rw [hΩcard, hL])
    exact hKL (hKeq.trans hLeq.symm)
  -- Finisher: noncyclic + `≤ p²` ⇒ `E_{p²}`.
  obtain ⟨hElem, hCard⟩ :=
    hΩ_pgroup.isElementaryAbelian_card_prime_sq_of_card_le_prime_sq_of_not_isCyclic hle hΩ_nc
  exact ⟨hElem, hCard⟩

/-- **BG Lemma 4.5(b)** (**G** Thms 5.4.3/5.4.4). For `p` odd, a noncyclic `p`-group `R`
possessing a cyclic subgroup `H` of index `p` has `Ω₁(R)` elementary abelian of order `p²`.

This is the faithful BG statement: `H` is an abstract cyclic subgroup of index `p`. The
proof extracts a generator (`H = Subgroup.zpowers x`) and applies the generator-form
`isElementaryAbelian_omega1_of_cyclic_index_prime`. Callers (BG Prop 4.11 / Thm 4.12)
instantiate `R` at a noncyclic subgroup `S₁` having a cyclic subgroup `S` of relative
index `p`. -/
theorem isElementaryAbelian_omega1_of_isCyclic_index_prime
    (hR : IsPGroup p R) (hp_odd : Odd p) (hnc : ¬ IsCyclic R)
    {H : Subgroup R} (hHcyc : IsCyclic H) (hidx : H.index = p) :
    (Omega R p 1).IsElementaryAbelian p ∧ Nat.card (Omega R p 1) = p ^ 2 := by
  -- Extract an ambient generator `x` with `H = ⟨x⟩`.
  obtain ⟨x, hx⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp hHcyc
  have hHidx : (Subgroup.zpowers x).index = p := by rw [hx]; exact hidx
  exact isElementaryAbelian_omega1_of_cyclic_index_prime hR hp_odd hnc hHidx

end CyclicIndexP

/-! ## §4C: `Ω₁` of a noncyclic metacyclic `p`-group (Lemma 4.10)

BG Lemma 4.10 (mmd L1546-1552): for `p` odd and `R` a **metacyclic** `p`-group that is
**not cyclic**, `Ω₁(R)` is elementary abelian of order `p²`.

This is a corollary of BG Lemma 4.5(b)
(`isElementaryAbelian_omega1_of_isCyclic_index_prime`, already in §4C above), via a
reduction to the subgroup `T ≤ R` whose quotient `T/S = Ω₁(R/S)`.

Concretely: take `S ⊴ R` with `S`, `R/S` cyclic (from `IsMetacyclic`). Set
`T := comap (mk' S) (Ω₁(R/S))`, so `S ≤ T`. Two genuine facts are proved (not hoisted):

* `Ω₁(R) = (Ω₁ ↥T).map T.subtype` — every `g` with `g^p = 1` has `mk' g ∈ Ω₁(R/S)`, hence
  `g ∈ T`; conversely the `Ω₁`-generators of `↥T` map to `p`-torsion of `R`.
* `S.relindex T = p` — via `relIndex_ker (mk' S) T = |T.map (mk' S)| = |Ω₁(R/S)| = p`,
  where the last equality is `card_omega1_eq_prime_of_isCyclic` (the unique order-`p`
  subgroup of the nontrivial cyclic `p`-group `R/S`).

Then `S.subgroupOf T` is cyclic (`≅ S`, as `S ≤ T`) of index `S.relindex T = p` in the
noncyclic `↥T`, so Lemma 4.5(b) applied to `↥T` gives `Ω₁(↥T) ≅ E_{p²}`; transfer the
conclusion across the injective `T.subtype`. `↥T` is noncyclic because `Ω₁(↥T)` maps onto
the noncyclic `Ω₁(R)` (noncyclic since `R` has two distinct order-`p` subgroups, both
inside `Ω₁(R)`). -/

section MetacyclicOmega

open OddOrder.GroupTheory

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- A nontrivial finite cyclic `p`-group `Q` has `|Ω₁(Q)| = p`.

`Q` cyclic ⇒ commutative, so the generating set `{g | g^p = 1}` of `Ω₁(Q) = Omega Q p 1`
is already the kernel of the `p`-th power map (`powMonoidHom p`), hence
`Ω₁(Q) = (powMonoidHom p).ker`. Its cardinality is `(|Q|).gcd p`
(`IsCyclic.card_powMonoidHom_ker`); for a nontrivial `p`-group `|Q| = p^k` with `k ≥ 1`, so
`gcd(p^k, p) = p`. -/
theorem card_omega1_eq_prime_of_isCyclic
    {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] [Nontrivial Q] (hQ : IsPGroup p Q) :
    Nat.card (Omega Q p 1) = p := by
  have hp_prime : p.Prime := Fact.out
  -- `Q` is commutative; use it for the `powMonoidHom` kernel cardinality lemma.
  letI : CommGroup Q := IsCyclic.commGroup
  -- `Ω₁(Q) = (powMonoidHom p).ker`: the generating set `{g | g^(p^1)=1}` *is* the kernel.
  have hset : {g : Q | g ^ (p ^ 1) = 1} = ((powMonoidHom p : Q →* Q).ker : Set Q) := by
    ext g
    simp only [Set.mem_setOf_eq, pow_one, SetLike.mem_coe, MonoidHom.mem_ker, powMonoidHom_apply]
  have hΩ_ker : Omega Q p 1 = (powMonoidHom p : Q →* Q).ker := by
    rw [Omega, hset, Subgroup.closure_eq]
  -- `|Q| = p^k` with `k ≥ 1` (nontrivial `p`-group).
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact absurd (by rw [hk, hk0, pow_zero] : Nat.card Q = 1)
        (by simpa using (Finite.one_lt_card (α := Q)).ne')
    · exact hk0
  -- `gcd(p^k, p) = p`.
  have hgcd : (Nat.card Q).gcd p = p := by
    rw [hk]; exact Nat.gcd_eq_right (dvd_pow_self p hk_pos.ne')
  rw [hΩ_ker, IsCyclic.card_powMonoidHom_ker (G := Q) p, hgcd]

/-- In a finite cyclic group `C`, two subgroups of order `p` (`p` prime) are equal.

This is the uniqueness half behind "noncyclic ⇒ two distinct order-`p` subgroups". Proof: any
order-`p` subgroup `K` has every element `p`-torsion (Lagrange), so `K ≤ (powMonoidHom p).ker`;
and `|ker| = gcd(|C|, p) = p` since `p = |K|` divides `|C|`. Equal cardinalities force
`K = ker`, so both `K` and `L` equal that unique kernel. -/
private theorem subgroup_card_prime_unique_of_isCyclic
    {C : Type*} [Group C] [Finite C] [IsCyclic C] {K L : Subgroup C}
    (hK : Nat.card K = p) (hL : Nat.card L = p) : K = L := by
  have hp_prime : p.Prime := Fact.out
  letI : CommGroup C := IsCyclic.commGroup
  -- Each order-`p` subgroup equals the unique order-`p` kernel `(powMonoidHom p).ker`.
  have key : ∀ {M : Subgroup C}, Nat.card M = p → M = (powMonoidHom p : C →* C).ker := by
    intro M hM
    -- `M ≤ ker`: every element of `M` is `p`-torsion (Lagrange in `M`).
    have hM_le : M ≤ (powMonoidHom p : C →* C).ker := by
      intro g hg
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have hg1 : (⟨g, hg⟩ : M) ^ Nat.card M = 1 := pow_card_eq_one'
      have := congrArg (Subtype.val) hg1
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one, hM] at this
    -- `|ker| = gcd(|C|, p) = p` (as `p = |M| ∣ |C|`).
    have hp_dvd : p ∣ Nat.card C := hM ▸ M.card_subgroup_dvd_card
    have hker_card : Nat.card (powMonoidHom p : C →* C).ker = p := by
      rw [IsCyclic.card_powMonoidHom_ker (G := C) p, Nat.gcd_eq_right hp_dvd]
    exact Subgroup.eq_of_le_of_card_ge hM_le (by rw [hker_card, hM])
  exact (key hK).trans (key hL).symm

/-- **BG Lemma 4.10** (mmd L1546-1552). For `p` odd, a noncyclic metacyclic `p`-group `R`
has `Ω₁(R)` elementary abelian of order `p²`.

Reduction to BG Lemma 4.5(b) (`isElementaryAbelian_omega1_of_isCyclic_index_prime`): with
`S ⊴ R` cyclic and `R/S` cyclic, the subgroup `T = comap (mk' S) (Ω₁(R/S))` satisfies
`Ω₁(R) = (Ω₁ ↥T).map T.subtype` and contains `S` with `S.relIndex T = p`; apply 4.5(b) to the
noncyclic `↥T` (cyclic subgroup `S.subgroupOf T` of index `p`) and transfer. -/
theorem isElementaryAbelian_omega1_of_isMetacyclic
    (hR : IsPGroup p R) (hp_odd : Odd p) (hmeta : IsMetacyclic R) (hnc : ¬ IsCyclic R) :
    (Omega R p 1).IsElementaryAbelian p ∧ Nat.card (Omega R p 1) = p ^ 2 := by
  classical
  -- Unpack the metacyclic structure.
  obtain ⟨S, hS_norm, hS_cyc, hQ_cyc⟩ := hmeta
  haveI := hS_norm
  haveI : IsCyclic (R ⧸ S) := hQ_cyc
  -- `R/S` is nontrivial: else `S = ⊤` and `R ≅ ↥S` is cyclic, contradicting `hnc`.
  haveI hQ_nontriv : Nontrivial (R ⧸ S) := by
    rcases subsingleton_or_nontrivial (R ⧸ S) with hsub | hnt
    · exfalso
      -- `R⧸S` subsingleton ⇒ `S.index = 1` ⇒ `S = ⊤`; then `↥(⊤) ≅ R` is cyclic.
      have hidx1 : S.index = 1 := by
        rw [Subgroup.index, Nat.card_eq_one_iff_unique]
        exact ⟨hsub, ⟨1⟩⟩
      have hStop : S = ⊤ := Subgroup.index_eq_one.mp hidx1
      have : IsCyclic ↥(⊤ : Subgroup R) := hStop ▸ hS_cyc
      exact hnc (isCyclic_of_surjective (Subgroup.topEquiv (G := R)).toMonoidHom
        (Subgroup.topEquiv (G := R)).surjective)
    · exact hnt
  have hQ_pgroup : IsPGroup p (R ⧸ S) := hR.to_quotient S
  -- `T := comap (mk' S) (Ω₁(R/S))`; `S ≤ T`.
  set T : Subgroup R := Subgroup.comap (QuotientGroup.mk' S) (Omega (R ⧸ S) p 1) with hT_def
  have hS_le_T : S ≤ T := by
    rw [hT_def]; exact QuotientGroup.le_comap_mk' S _
  have hT_pgroup : IsPGroup p T := hR.to_subgroup T
  -- (a) `Ω₁(R) = (Ω₁ ↥T).map T.subtype`.
  have hΩ_eq : Omega R p 1 = (Omega (↥T) p 1).map T.subtype := by
    apply le_antisymm
    · -- ⊆ : push each generator `g` (with `g^p = 1`) of `Ω₁(R)` into `T`, then into `Ω₁ ↥T`.
      rw [Omega, Subgroup.closure_le]
      intro g (hg : g ^ (p ^ 1) = 1)
      rw [pow_one] at hg
      have hgT : g ∈ T := by
        rw [hT_def, Subgroup.mem_comap]
        refine Omega.mem_of_pow_eq_one ?_
        rw [pow_one, ← map_pow, hg, map_one]
      change g ∈ Subgroup.map T.subtype (Omega (↥T) p 1)
      rw [Subgroup.mem_map]
      refine ⟨⟨g, hgT⟩, ?_, rfl⟩
      refine Omega.mem_of_pow_eq_one ?_
      rw [pow_one]
      ext
      rw [SubmonoidClass.coe_pow, Subgroup.coe_mk, OneMemClass.coe_one, hg]
    · -- ⊇ : the image of an `Ω₁ ↥T` generator lies in `Ω₁(R)`.
      rw [Subgroup.map_le_iff_le_comap, Omega, Subgroup.closure_le]
      rintro ⟨g, hgT⟩ (hg : (⟨g, hgT⟩ : ↥T) ^ (p ^ 1) = 1)
      change (⟨g, hgT⟩ : ↥T) ∈ Subgroup.comap T.subtype (Omega R p 1)
      rw [Subgroup.mem_comap]
      refine Omega.mem_of_pow_eq_one ?_
      rw [pow_one]
      have hval := congrArg (Subgroup.subtype T) hg
      rw [map_pow, pow_one, map_one] at hval
      simpa using hval
  -- `Ω₁(R) ≤ T` (image under `T.subtype` lands in `T`).
  have hΩ_le_T : Omega R p 1 ≤ T := by
    rw [hΩ_eq]; exact Subgroup.map_subtype_le _
  -- (b) `S.relIndex T = p`.
  have hSrel : S.relIndex T = p := by
    have hker : S = (QuotientGroup.mk' S).ker := (QuotientGroup.ker_mk' S).symm
    rw [hker, Subgroup.relIndex_ker, hT_def,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S)]
    exact card_omega1_eq_prime_of_isCyclic hQ_pgroup
  -- `↥T` noncyclic: pull `R`'s two distinct order-`p` subgroups into `↥T`.
  have hT_nc : ¬ IsCyclic ↥T := by
    intro hTcyc
    obtain ⟨Ksub, Lsub, hK, hL, hKL⟩ :=
      exists_distinct_subgroups_card_prime_of_not_isCyclic hR hp_odd hnc
    -- order-`p` subgroups of `R` sit inside `Ω₁(R) ≤ T`.
    have mem_omega_of_card_p : ∀ (M : Subgroup R), Nat.card M = p → M ≤ T := by
      intro M hM g hg
      have hgp : g ^ p = 1 := by
        have hM1 : (⟨g, hg⟩ : M) ^ Nat.card M = 1 := pow_card_eq_one'
        have hcoe : g ^ Nat.card M = 1 := by
          have := congrArg (Subtype.val) hM1
          rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
        rwa [hM] at hcoe
      exact hΩ_le_T (Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hgp))
    have hKT : Ksub ≤ T := mem_omega_of_card_p Ksub hK
    have hLT : Lsub ≤ T := mem_omega_of_card_p Lsub hL
    -- their `subgroupOf T` versions have order `p`; uniqueness in cyclic `↥T` forces equality.
    have hcardK : Nat.card (Ksub.subgroupOf T) = p := by
      rw [← Subgroup.card_map_of_injective (K := Ksub.subgroupOf T) (f := T.subtype)
            T.subtype_injective,
        Subgroup.subgroupOf_map_subtype, inf_of_le_left hKT, hK]
    have hcardL : Nat.card (Lsub.subgroupOf T) = p := by
      rw [← Subgroup.card_map_of_injective (K := Lsub.subgroupOf T) (f := T.subtype)
            T.subtype_injective,
        Subgroup.subgroupOf_map_subtype, inf_of_le_left hLT, hL]
    have hsub_eq : Ksub.subgroupOf T = Lsub.subgroupOf T :=
      subgroup_card_prime_unique_of_isCyclic hcardK hcardL
    -- map back along `T.subtype` to recover `Ksub = Lsub`, contradiction.
    apply hKL
    have := congrArg (Subgroup.map T.subtype) hsub_eq
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hKT, inf_of_le_left hLT] at this
  -- `S.subgroupOf T` is cyclic (`≅ ↥S`) of index `p`.
  have hSsub_cyc : IsCyclic ↥(S.subgroupOf T) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS_le_T).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hS_le_T).symm.surjective
  have hSsub_idx : (S.subgroupOf T).index = p := hSrel
  -- Apply Lemma 4.5(b) to `↥T`.
  obtain ⟨hΩT_elem, hΩT_card⟩ :=
    isElementaryAbelian_omega1_of_isCyclic_index_prime hT_pgroup hp_odd hT_nc
      hSsub_cyc hSsub_idx
  -- Transfer `E_{p²}` across `T.subtype`.
  refine ⟨?_, ?_⟩
  · rw [hΩ_eq]; exact hΩT_elem.map T.subtype_injective
  · rw [hΩ_eq, Subgroup.card_map_of_injective T.subtype_injective]; exact hΩT_card

end MetacyclicOmega

/-! ## §4D: converse of Lemma 4.5 — `|Ω₁(R)| ≤ p ⇒ R` cyclic (Thm 4.12 a-3 engine)

In the proof of BG Theorem 4.12(a) (mmd L1608, "Hence `|Ω₁(X)| ≤ |Ω₁(S)| = p`. By Lem 4.5,
`X` cyclic") and again at the `R/S` step (L1612), BG runs Lemma 4.5 *in the converse
direction*: a `p`-group whose `Ω₁` is small (`|Ω₁| ≤ p`) is cyclic. The repo's Lemma 4.5(b)
(`isElementaryAbelian_omega1_of_isCyclic_index_prime`) is the forward statement
(noncyclic ⇒ `Ω₁ ≅ E_{p²}`, so `|Ω₁| = p²`); this lemma is its contrapositive packaging.

The genuine content is just Isaacs Thm 6.11: an odd `p`-group with a *unique* subgroup of
order `p` is cyclic. Every order-`p` subgroup `M` consists of `p`-torsion (`g^p = 1` via
`pow_card_eq_one'`), hence sits inside `Ω₁(R) = Omega R p 1` (`Omega.mem_of_pow_eq_one`); if
`|Ω₁(R)| ≤ p` then any such `M` (which has `|M| = p ≥ |Ω₁|`) equals `Ω₁(R)` by
`Subgroup.eq_of_le_of_card_ge`, so the order-`p` subgroup is unique. This is reused by Thm
4.12 a-3 and by Prop 4.11. -/

section ConverseLemma45

open OddOrder.GroupTheory

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- **Converse of BG Lemma 4.5**: a finite `p`-group (`p` odd) with `|Ω₁(R)| ≤ p` is cyclic.

Every order-`p` subgroup lies in `Ω₁(R)`; if `|Ω₁(R)| ≤ p` it is the unique such subgroup,
so `R` is cyclic by Isaacs Thm 6.11
(`OddOrder.Isaacs.Ch06.isCyclic_of_subgroups_card_prime_unique_of_odd`).

Used in BG Thm 4.12(a) (mmd L1608, L1612) — the `|Ω₁(X)| ≤ p ⇒ X` cyclic and
`|Ω₁(R/S)| ≤ p ⇒ R/S` cyclic steps — and reusable for Prop 4.11. -/
theorem isCyclic_of_card_omega1_le_prime (hR : IsPGroup p R) (hp_odd : Odd p)
    (hΩ : Nat.card (Omega R p 1) ≤ p) : IsCyclic R := by
  apply OddOrder.Isaacs.Ch06.isCyclic_of_subgroups_card_prime_unique_of_odd hR hp_odd
  intro K L hK hL
  -- Every order-`p` subgroup consists of `p`-torsion, hence lies in `Ω₁(R)`.
  have memle : ∀ M : Subgroup R, Nat.card M = p → M ≤ Omega R p 1 := by
    intro M hM g hg
    have hgp : g ^ p = 1 := by
      have h1 : (⟨g, hg⟩ : M) ^ Nat.card M = 1 := pow_card_eq_one'
      have := congrArg Subtype.val h1
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one, hM] at this
    exact Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hgp)
  -- `|M| = p ≥ |Ω₁|` forces `M = Ω₁(R)`, so the order-`p` subgroup is unique.
  rw [Subgroup.eq_of_le_of_card_ge (memle K hK) (by rw [hK]; exact hΩ),
      Subgroup.eq_of_le_of_card_ge (memle L hL) (by rw [hL]; exact hΩ)]

end ConverseLemma45

end OddOrder.BG.Ch1.S04
