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
      show x ^ p = 1
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
        show a ^ p = 1
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
    IsPGroup.commutative_of_card_eq_prime_sq (p := p) hcard_quot
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

/-! ## 4E: Lemma 4.15 (extraspecial commutator constraint) (BG mmd L1632)

**BG Lemma 4.15**: if `S` is an extraspecial subgroup of a `p`-group `R` and
`[S, R] ⊆ S'`, then `R = S · C_R(S)`.

BG defers the proof to Gorenstein, _Finite Groups_, Lemma 5.4.6, p. 195 (= Gorenstein
Lemma 4.6, mmd `references/gorenstein/finite-groups.mmd` L4101-4109). The Gorenstein
argument: every `g ∈ R` induces, by conjugation, an automorphism of `S` that is trivial
on `S/Z(S)` (because `[S, R] ⊆ Z(S) = S'`); such automorphisms are exactly the inner ones,
so `g` agrees with conjugation by some `s ∈ S` and `g s⁻¹ ∈ C_R(S)`.

The Lean rendering replaces the "trivial-on-`S/Z` automorphism is inner" structure theorem by
a direct counting. For `g ∈ R` the map `δ_g : s ↦ (g s g⁻¹) s⁻¹` lands in `Z := Z(S)` (it is
`⁅g, s⁆ ∈ [S, R] ⊆ Z`), is a group homomorphism `S →* Z` (`Z` central), and therefore kills
`[S, S] = Z`, so it descends to `S/Z →* Z`. Viewing `S/Z` as an `𝔽_p`-vector space (it is
elementary abelian, being `S/Φ(S)`) and `Z` additively, `δ_g` becomes `𝔽_p`-linear, hence is
determined by its values on a basis of `S/Z`. This embeds `R/C_R(S)` into `ι → Z` (`ι` the
basis index), giving `|R/C_R(S)| ≤ |Z|^{|ι|} = p^{m} = |S/Z|`. Conversely `S/Z` embeds into
`R/C_R(S)` (via `S.subtype`, with kernel `S ∩ C_R(S) = Z`), giving the reverse inequality.
The two bounds force the embedding `S/Z ↪ R/C_R(S)` to be onto, i.e. `S · C_R(S) = R`.

The statement is `p`-general: only `cl(S) ≤ 2` (`[S,S] = Z(S)`) and `|Z(S)| = p` are used, not
the parity of `p`. (The neighbouring Lemmas 4.5, 4.7 and Prop 4.6 assume `p` odd; Lemma 4.15
deliberately does not.) -/

section ExtraspecialCommutator

open OddOrder.GroupTheory
open scoped commutatorElement
open scoped IsMulCommutative

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] {S : Subgroup R}

/-- `S` is normal in `R` from `⁅S, ⊤⁆ ≤ S`: the conjugation action lands in `S`. -/
private theorem extraspecial_normal_of_commutator_le
    (hSinR : ⁅S, (⊤ : Subgroup R)⁆ ≤ S) : S.Normal := by
  have hnorm : (⊤ : Subgroup R) ≤ Subgroup.normalizer S :=
    OddOrder.Isaacs.Ch04.le_normalizer_of_commutator_le hSinR
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hnorm)

/-- From `[S, R] ⊆ S' = Z(S)` the ambient inclusion `[S, R] ⊆ S` (image of a subgroup of `S`). -/
private theorem commutator_le_self_of_hSR
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) :
    ⁅S, (⊤ : Subgroup R)⁆ ≤ S :=
  le_trans hSR (Subgroup.map_subtype_le _)

/-- For `g ∈ R` and `s ∈ S`, the commutator `⁅g, ↑s⁆ = (g s g⁻¹) s⁻¹` lies in `S`
and, as an element of `↥S`, in the centre `Z(S)`. This is the heart of `[S, R] ⊆ Z(S)`. -/
private theorem commutatorElement_mem_center
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) (s : ↥S) :
    ⁅g, (s : R)⁆ ∈ (Subgroup.center (↥S)).map S.subtype := by
  have hmem : ⁅(s : R), g⁆ ∈ ⁅S, (⊤ : Subgroup R)⁆ :=
    Subgroup.commutator_mem_commutator s.2 (Subgroup.mem_top g)
  have hinv : ⁅g, (s : R)⁆ ∈ ⁅S, (⊤ : Subgroup R)⁆ := by
    rw [← commutatorElement_inv]
    exact (⁅S, (⊤ : Subgroup R)⁆).inv_mem hmem
  exact hSR hinv

/-- The element `(g · s · g⁻¹) · s⁻¹ ∈ ↥S` lies in `Z(S)`. (`= ⁅g, s⁆ ∈ [S, R] ⊆ Z(S)`,
reflected back into `↥S` via injectivity of `S.subtype`.) Requires `S` normal so that
conjugation by `g` is an automorphism of `↥S`. -/
private theorem deltaElement_mem [S.Normal]
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) (s : ↥S) :
    MulAut.conjNormal g s * s⁻¹ ∈ Subgroup.center (↥S) := by
  obtain ⟨z, hz_mem, hz_eq⟩ := commutatorElement_mem_center hSR g s
  have hcoe : ((MulAut.conjNormal g s * s⁻¹ : ↥S) : R) = ⁅g, (s : R)⁆ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, commutatorElement_def]
  have heq : MulAut.conjNormal g s * s⁻¹ = z := by
    apply S.subtype_injective
    rw [Subgroup.coe_subtype, hcoe, ← hz_eq, Subgroup.coe_subtype]
  rw [heq]; exact hz_mem

/-- **`δ_g : ↥S →* Z(S)`** (`g ∈ R`): the homomorphism `s ↦ (g s g⁻¹) s⁻¹`.

It is multiplicative because its values lie in the centre `Z(S)`: for `s, t`,
`δ_g(st) = δ_g(s) · δ_g(t)` after sliding the central factor `δ_g(t)` past `s⁻¹`.
This is the "displacement" homomorphism of the conjugation automorphism. -/
private noncomputable def deltaHom [S.Normal]
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) :
    ↥S →* Subgroup.center (↥S) :=
  MonoidHom.mk' (fun s => ⟨MulAut.conjNormal g s * s⁻¹, deltaElement_mem hSR g s⟩) (by
    intro s t
    apply Subtype.ext
    show MulAut.conjNormal g (s * t) * (s * t)⁻¹ =
      (MulAut.conjNormal g s * s⁻¹) * (MulAut.conjNormal g t * t⁻¹)
    have hcentral : MulAut.conjNormal g t * t⁻¹ ∈ Subgroup.center (↥S) :=
      deltaElement_mem hSR g t
    -- `(cg t) t⁻¹` is central, hence commutes with `s⁻¹`.
    have hcomm : Commute s⁻¹ (MulAut.conjNormal g t * t⁻¹) :=
      (Subgroup.mem_center_iff.mp hcentral s⁻¹)
    rw [map_mul, mul_inv_rev]
    calc
      MulAut.conjNormal g s * MulAut.conjNormal g t * (t⁻¹ * s⁻¹)
          = MulAut.conjNormal g s * ((MulAut.conjNormal g t * t⁻¹) * s⁻¹) := by
            simp only [mul_assoc]
      _ = MulAut.conjNormal g s * (s⁻¹ * (MulAut.conjNormal g t * t⁻¹)) := by
            rw [hcomm.symm.eq]
      _ = (MulAut.conjNormal g s * s⁻¹) * (MulAut.conjNormal g t * t⁻¹) := by
            simp only [mul_assoc])

@[simp]
private theorem deltaHom_apply [S.Normal]
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) (s : ↥S) :
    (deltaHom hSR g s : ↥S) = MulAut.conjNormal g s * s⁻¹ := rfl

/-- `δ_g = 1` (the trivial homomorphism) iff `g` centralizes `S`: `δ_g(s) = 1` says
`g s g⁻¹ = s` for every `s ∈ S`. -/
private theorem deltaHom_eq_one_iff_mem_centralizer [S.Normal]
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) :
    deltaHom hSR g = 1 ↔ g ∈ Subgroup.centralizer (S : Set R) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hδ s hs
    have h1 : deltaHom hSR g ⟨s, hs⟩ = 1 := by rw [hδ]; rfl
    have h2 : MulAut.conjNormal g (⟨s, hs⟩ : ↥S) * (⟨s, hs⟩ : ↥S)⁻¹ = 1 := by
      have hv := congrArg (Subtype.val) h1
      rw [deltaHom_apply] at hv
      exact hv
    have h3 : MulAut.conjNormal g (⟨s, hs⟩ : ↥S) = (⟨s, hs⟩ : ↥S) :=
      mul_inv_eq_one.mp h2
    have h4 : (g * s * g⁻¹ : R) = s := by
      have hh := congrArg (fun x : ↥S => (x : R)) h3
      simp only [MulAut.conjNormal_apply] at hh
      exact hh
    -- `g * s * g⁻¹ = s`, i.e. `s * g = g * s`.
    have : g * s * g⁻¹ * g = s * g := by rw [h4]
    simpa [mul_assoc] using this.symm
  · intro hcent
    refine MonoidHom.ext fun s => ?_
    have hcomm : (s : R) * g = g * (s : R) := hcent (s : R) s.2
    have hfix : MulAut.conjNormal g s = s := by
      apply S.subtype_injective
      rw [Subgroup.coe_subtype, MulAut.conjNormal_apply, ← hcomm]; group
    apply Subtype.ext
    show (deltaHom hSR g s : ↥S) = (1 : ↥S)
    rw [deltaHom_apply hSR g s, hfix, mul_inv_cancel]

/-- `δ_g` kills `Z(S)`: as a homomorphism into the abelian group `Z(S)` it kills `[S, S]`,
and `[S, S] = Z(S)` for extraspecial `S`. -/
private theorem center_le_ker_deltaHom [S.Normal] (hS : IsExtraspecial p (↥S))
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) :
    Subgroup.center (↥S) ≤ (deltaHom hSR g).ker := by
  have hcomm_le : commutator (↥S) ≤ (deltaHom hSR g).ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    -- `⁅δa, δb⁆ = 1` since `Z(S)` is commutative.
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (mul_comm (deltaHom hSR g a) (deltaHom hSR g b))
  exact hS.commutator_eq_center.symm.le.trans hcomm_le

/-- The descent of `δ_g` to `S/Z(S) →* Z(S)`. -/
private noncomputable def deltaQuot [S.Normal] (hS : IsExtraspecial p (↥S))
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) :
    (↥S ⧸ Subgroup.center (↥S)) →* Subgroup.center (↥S) :=
  QuotientGroup.lift (Subgroup.center (↥S)) (deltaHom hSR g) (center_le_ker_deltaHom hS hSR g)

@[simp]
private theorem deltaQuot_mk [S.Normal] (hS : IsExtraspecial p (↥S))
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) (s : ↥S) :
    deltaQuot hS hSR g (QuotientGroup.mk s) = deltaHom hSR g s :=
  QuotientGroup.lift_mk' _ _ s

/-- `S/Z(S)` is elementary abelian: it is `S/Φ(S)` (since `Φ(S) = Z(S)` for extraspecial `S`),
and `S/Φ(S)` is elementary abelian for any finite `p`-group (Burnside). -/
private theorem quotientCenter_isElementaryAbelian (hS : IsExtraspecial p (↥S)) :
    IsElementaryAbelian p (↥S ⧸ Subgroup.center (↥S)) := by
  have hfrat : frattini (↥S) = Subgroup.center (↥S) := hS.frattini_eq_center
  have hEA := IsPGroup.quotient_frattini_isElementaryAbelian (p := p) (R := ↥S) hS.isPGroup
  haveI : (frattini (↥S)).Normal := inferInstance
  exact IsElementaryAbelian.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hfrat) hEA

/-- `Z(S)` is elementary abelian: it is cyclic of prime order `p`. -/
private theorem centerS_isElementaryAbelian (hS : IsExtraspecial p (↥S)) :
    IsElementaryAbelian p (Subgroup.center (↥S)) := by
  refine ⟨fun x y => mul_comm x y, fun x => ?_⟩
  -- `|Z(S)| = p`, so every element has order dividing `p`.
  have hx : x ^ (Nat.card (Subgroup.center (↥S))) = 1 := pow_card_eq_one'
  rwa [hS.center_card] at hx

/-- The kernel of `R →* MulAut ↥S` (conjugation) is `C_R(S)`. -/
private theorem conjNormal_ker_eq_centralizer_local [S.Normal] :
    (MulAut.conjNormal (H := S) : R →* MulAut (↥S)).ker
      = Subgroup.centralizer (S : Set R) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg s hs
    have hfix0 : MulAut.conjNormal (H := S) g ⟨s, hs⟩ = (⟨s, hs⟩ : ↥S) := by
      rw [hg]; rfl
    have hfix : (g * s * g⁻¹ : R) = s := by
      have hh := congrArg (fun x : ↥S => (x : R)) hfix0
      simp only [MulAut.conjNormal_apply] at hh
      exact hh
    -- `g * s * g⁻¹ = s`, i.e. `s * g = g * s`.
    have : g * s * g⁻¹ * g = s * g := by rw [hfix]
    simpa [mul_assoc] using this.symm
  · intro hcent
    ext s
    have hcomm : (s : R) * g = g * (s : R) := hcent (s : R) s.2
    have hfix : MulAut.conjNormal (H := S) g s = s := by
      apply S.subtype_injective
      rw [Subgroup.coe_subtype, MulAut.conjNormal_apply, ← hcomm]; group
    rw [hfix]; rfl

/-- The `ZMod p`-scalar-torsion condition `p • x = 0` for an elementary-abelian
multiplicative group viewed additively. -/
private theorem additive_nsmul_eq_zero {V : Type*} [Group V]
    (hV : IsElementaryAbelian p V) : ∀ x : Additive V, (p : ℕ) • x = 0 := by
  intro x
  apply Additive.toMul.injective
  show (p • x).toMul = (0 : Additive V).toMul
  rw [toMul_nsmul, toMul_zero]
  exact hV.pow_eq_one x.toMul

/-- **Upper bound** (Gorenstein 4.6 counting): `|R / C_R(S)| ≤ |S / Z(S)|`.

Every `g ∈ R` gives a linear map `Λ_g : S/Z(S) → Z(S)` (the additive form of `δ_g`),
and these are constant on `C_R(S)`-cosets and distinguish them (two `g` with the same `Λ_g`
induce the same conjugation, hence differ by an element of `C_R(S) = ker(conjugation)`). Reading
off `Λ_g` on a fixed `𝔽_p`-basis `b` of `S/Z(S)` embeds `R/C_R(S)` into `(basis) → Z(S)`, whose
cardinality is `|Z(S)|^{dim} = p^{dim} = |S/Z(S)|`. -/
private theorem card_quotient_centralizer_le [S.Normal] (hS : IsExtraspecial p (↥S))
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) :
    Nat.card (R ⧸ Subgroup.centralizer (S : Set R)) ≤
      Nat.card (↥S ⧸ Subgroup.center (↥S)) := by
  classical
  -- Module structures on the two additive groups.
  set Q := ↥S ⧸ Subgroup.center (↥S) with hQ
  set Z := Subgroup.center (↥S) with hZ
  have hQ_EA : IsElementaryAbelian p Q := quotientCenter_isElementaryAbelian hS
  have hZ_EA : IsElementaryAbelian p Z := centerS_isElementaryAbelian hS
  haveI : IsMulCommutative Q := ⟨⟨hQ_EA.comm⟩⟩
  haveI : IsMulCommutative Z := ⟨⟨hZ_EA.comm⟩⟩
  haveI : Module (ZMod p) (Additive Q) := AddCommGroup.zmodModule (additive_nsmul_eq_zero hQ_EA)
  haveI : Module (ZMod p) (Additive Z) := AddCommGroup.zmodModule (additive_nsmul_eq_zero hZ_EA)
  -- A chosen `𝔽_p`-basis of `Additive Q`.
  let ι := Module.Free.ChooseBasisIndex (ZMod p) (Additive Q)
  let b : Module.Basis ι (ZMod p) (Additive Q) := Module.Free.chooseBasis (ZMod p) (Additive Q)
  -- The linear map attached to `g`.
  let Λ : R → (Additive Q →ₗ[ZMod p] Additive Z) :=
    fun g => (deltaQuot hS hSR g).toAdditive.toZModLinearMap p
  -- `Λ g = Λ g'` ⇔ `deltaQuot g = deltaQuot g'`.
  have hΛ_eq_iff : ∀ g g' : R, Λ g = Λ g' ↔ deltaQuot hS hSR g = deltaQuot hS hSR g' := by
    intro g g'
    constructor
    · intro h
      have h1 : (deltaQuot hS hSR g).toAdditive = (deltaQuot hS hSR g').toAdditive :=
        AddMonoidHom.toZModLinearMap_injective p h
      exact MonoidHom.toAdditive.injective h1
    · intro h; simp only [Λ, h]
  -- `deltaHom g = deltaHom g'` ⇒ `conjNormal g = conjNormal g'`.
  have hconj_of_delta : ∀ g g' : R, deltaHom hSR g = deltaHom hSR g' →
      MulAut.conjNormal (H := S) g = MulAut.conjNormal (H := S) g' := by
    intro g g' hδ
    refine MulEquiv.ext fun s => ?_
    have hs : (deltaHom hSR g s : ↥S) = (deltaHom hSR g' s : ↥S) :=
      congrArg (fun t : Subgroup.center (↥S) => (t : ↥S)) (congrArg (fun f => f s) hδ)
    simp only [deltaHom_apply] at hs
    exact mul_right_cancel hs
  -- `deltaQuot g = deltaQuot g'` ⇒ `deltaHom g = deltaHom g'`.
  have hdelta_of_quot : ∀ g g' : R, deltaQuot hS hSR g = deltaQuot hS hSR g' →
      deltaHom hSR g = deltaHom hSR g' := by
    intro g g' h
    refine MonoidHom.ext fun s => ?_
    have hms := congrArg (fun f => f (QuotientGroup.mk s)) h
    simpa only [deltaQuot_mk] using hms
  -- `conjNormal g = conjNormal g'` ⇒ `deltaQuot g = deltaQuot g'`.
  have hquot_of_conj : ∀ g g' : R, MulAut.conjNormal (H := S) g = MulAut.conjNormal (H := S) g' →
      deltaQuot hS hSR g = deltaQuot hS hSR g' := by
    intro g g' hconj
    have hδ : deltaHom hSR g = deltaHom hSR g' := by
      refine MonoidHom.ext fun s => ?_
      apply Subtype.ext
      simp only [deltaHom_apply]
      rw [show MulAut.conjNormal (H := S) g s = MulAut.conjNormal (H := S) g' s from
        congrArg (fun e => e s) hconj]
    -- both `deltaQuot` are lifts of `deltaHom g = deltaHom g'`.
    refine MonoidHom.ext fun q => ?_
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    rw [deltaQuot_mk, deltaQuot_mk, hδ]
  -- `conjNormal g = conjNormal g'` ⇔ `g⁻¹ g' ∈ C_R(S)`.
  have hconj_iff_mem : ∀ g g' : R,
      MulAut.conjNormal (H := S) g = MulAut.conjNormal (H := S) g' ↔
        g⁻¹ * g' ∈ Subgroup.centralizer (S : Set R) := by
    intro g g'
    rw [← conjNormal_ker_eq_centralizer_local (S := S), MonoidHom.mem_ker, map_mul, map_inv]
    constructor
    · intro h; rw [h, inv_mul_cancel]
    · intro h
      have hkey := congrArg (fun e => MulAut.conjNormal (H := S) g * e) h
      simp only [mul_one, mul_inv_cancel_left] at hkey
      exact hkey.symm
  -- The embedding `R/C_R(S) ↪ (ι → Z)`.
  let F : R ⧸ Subgroup.centralizer (S : Set R) → (ι → Z) :=
    Quotient.lift (fun g => fun i => deltaQuot hS hSR g (Additive.toMul (b i)))
      (by
        intro g g' hrel
        -- `g⁻¹ g' ∈ C_R(S)`, so `conjNormal g = conjNormal g'`, so `deltaQuot` agree.
        have hmem : g⁻¹ * g' ∈ Subgroup.centralizer (S : Set R) :=
          (QuotientGroup.leftRel_apply).mp hrel
        have hconj := (hconj_iff_mem g g').mpr hmem
        have hquot := hquot_of_conj g g' hconj
        funext i
        exact congrArg (fun f => f (Additive.toMul (b i))) hquot)
  have hF_inj : Function.Injective F := by
    intro x y hxy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
    -- From `F` agreeing: `Λ g (b i) = Λ g' (b i)` on basis, hence `Λ g = Λ g'`.
    have hbasis : ∀ i, Λ g (b i) = Λ g' (b i) := by
      intro i
      have hfi := congrFun hxy i
      simp only [F, Quotient.lift_mk] at hfi
      -- `Λ g (b i) = ofMul (deltaQuot g (toMul (b i)))`.
      show (Additive.ofMul (deltaQuot hS hSR g (Additive.toMul (b i)))) =
        (Additive.ofMul (deltaQuot hS hSR g' (Additive.toMul (b i))))
      rw [hfi]
    have hΛ : Λ g = Λ g' := Module.Basis.ext b hbasis
    have hconj := hconj_of_delta g g' (hdelta_of_quot g g' ((hΛ_eq_iff g g').mp hΛ))
    -- `conjNormal g = conjNormal g'` ⇒ `g⁻¹ g' ∈ C_R(S)` ⇒ same coset.
    exact QuotientGroup.eq.mpr ((hconj_iff_mem g g').mp hconj)
  -- Cardinality bookkeeping: `|ι → Z| = |Z|^|ι| = p^{finrank} = |Q|`.
  have hcardZ : Nat.card Z = p := hS.center_card
  haveI : Finite (Additive Q) := inferInstanceAs (Finite Q)
  have hι_card : Nat.card ι = Module.finrank (ZMod p) (Additive Q) := by
    rw [Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card]
  have hQ_pow : Nat.card Q = p ^ Module.finrank (ZMod p) (Additive Q) := by
    have hcard : Nat.card (Additive Q) = Nat.card Q := Nat.card_congr Additive.toMul
    have := FiniteField.pow_finrank_eq_natCard p (Additive Q)
    rw [hcard] at this
    exact this.symm
  calc
    Nat.card (R ⧸ Subgroup.centralizer (S : Set R)) ≤ Nat.card (ι → Z) :=
      Nat.card_le_card_of_injective F hF_inj
    _ = Nat.card Z ^ Nat.card ι := Nat.card_fun
    _ = p ^ Module.finrank (ZMod p) (Additive Q) := by rw [hcardZ, hι_card]
    _ = Nat.card Q := hQ_pow.symm

/-- An element `s ∈ S` centralizes `S` (in `R`) iff, as an element of `↥S`, it lies in `Z(S)`. -/
private theorem mem_centralizer_iff_mem_center (s : ↥S) :
    (s : R) ∈ Subgroup.centralizer (S : Set R) ↔ s ∈ Subgroup.center (↥S) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff]
  constructor
  · intro h t
    apply S.subtype_injective
    push_cast
    exact h (t : R) t.2
  · intro h r hr
    have hv := congrArg (fun x : ↥S => (x : R)) (h ⟨r, hr⟩)
    push_cast at hv
    exact hv

/-- **Reverse bound**: `|S / Z(S)| ≤ |R / C_R(S)|`, via the injection of *coset spaces*
`S/Z(S) ↪ R/C_R(S)` induced by `S.subtype`. (`C_R(S)` need not be normal, so this is an
injection of `Quotient`s, not a group homomorphism.) -/
private theorem card_quotient_center_le_card_quotient_centralizer :
    Nat.card (↥S ⧸ Subgroup.center (↥S)) ≤
      Nat.card (R ⧸ Subgroup.centralizer (S : Set R)) := by
  -- The coset-space map `S/Z(S) → R/C_R(S)`, `[s] ↦ [↑s]`.
  let ψ : (↥S ⧸ Subgroup.center (↥S)) → R ⧸ Subgroup.centralizer (S : Set R) :=
    Quotient.lift (fun s : ↥S => (QuotientGroup.mk (s : R)))
      (by
        intro a b hab
        -- `a⁻¹ b ∈ Z(S)` ⇒ `(↑a)⁻¹ (↑b) ∈ C_R(S)`.
        apply QuotientGroup.eq.mpr
        have hmem : a⁻¹ * b ∈ Subgroup.center (↥S) := (QuotientGroup.leftRel_apply).mp hab
        have hc : ((a⁻¹ * b : ↥S) : R) ∈ Subgroup.centralizer (S : Set R) :=
          (mem_centralizer_iff_mem_center (a⁻¹ * b)).mpr hmem
        simpa using hc)
  have hψ_inj : Function.Injective ψ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have hrel : (QuotientGroup.mk (a : R)) = (QuotientGroup.mk (b : R)) := hxy
    have hmem : (a : R)⁻¹ * (b : R) ∈ Subgroup.centralizer (S : Set R) :=
      (QuotientGroup.leftRel_apply).mp (Quotient.exact hrel)
    apply QuotientGroup.eq.mpr
    have hmemS : (a⁻¹ * b : ↥S) ∈ Subgroup.center (↥S) := by
      rw [← mem_centralizer_iff_mem_center]
      simpa using hmem
    simpa using hmemS
  exact Nat.card_le_card_of_injective ψ hψ_inj

/-- **BG Lemma 4.15** (Gorenstein, _Finite Groups_, Lemma 5.4.6, p. 195): if `S` is an
extraspecial subgroup of a `p`-group `R` and `[S, R] ⊆ S'`, then `R = S · C_R(S)`.

The hypothesis `[S, R] ⊆ S'` is recorded as `⁅S, ⊤⁆ ≤ (Z(S)).map S.subtype`, using
`S' = Z(S)` for extraspecial `S` (so the right side is the ambient image of the centre).

The statement is `p`-general: `cl(S) ≤ 2` (i.e. `[S, S] = Z(S)`) and `|Z(S)| = p` are the only
structural inputs; the parity of `p` is not used. (Lemma 4.15 deliberately omits the `p`-odd
standing hypothesis carried by the neighbouring Lemmas 4.5, 4.7 and Prop 4.6.)

Used in BG Thm 4.16 (Blackburn) Case B-1, where `S = Ω₁(R)` is extraspecial with `[S, R] ⊆ S'`,
to split `R` as the central product `S · C_R(S)`. -/
theorem mul_centralizer_eq_top_of_isExtraspecial
    (hS : IsExtraspecial p (↥S))
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) :
    S ⊔ Subgroup.centralizer (S : Set R) = ⊤ := by
  classical
  -- `S` is normal in `R`.
  haveI : S.Normal := extraspecial_normal_of_commutator_le (commutator_le_self_of_hSR hSR)
  -- The two bounds force `|S/Z(S)| = |R/C_R(S)|`.
  have hle1 := card_quotient_centralizer_le hS hSR
  have hle2 := card_quotient_center_le_card_quotient_centralizer (S := S)
  have hcard_eq : Nat.card (↥S ⧸ Subgroup.center (↥S)) =
      Nat.card (R ⧸ Subgroup.centralizer (S : Set R)) := le_antisymm hle2 hle1
  -- The reverse injection `ψ : S/Z(S) ↪ R/C_R(S)` is then surjective.
  let ψ : (↥S ⧸ Subgroup.center (↥S)) → R ⧸ Subgroup.centralizer (S : Set R) :=
    Quotient.lift (fun s : ↥S => (QuotientGroup.mk (s : R)))
      (by
        intro a b hab
        apply QuotientGroup.eq.mpr
        have hmem : a⁻¹ * b ∈ Subgroup.center (↥S) := (QuotientGroup.leftRel_apply).mp hab
        have hc : ((a⁻¹ * b : ↥S) : R) ∈ Subgroup.centralizer (S : Set R) :=
          (mem_centralizer_iff_mem_center (a⁻¹ * b)).mpr hmem
        simpa using hc)
  have hψ_inj : Function.Injective ψ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have hmem : (a : R)⁻¹ * (b : R) ∈ Subgroup.centralizer (S : Set R) :=
      (QuotientGroup.leftRel_apply).mp (Quotient.exact (hxy : ψ _ = ψ _))
    apply QuotientGroup.eq.mpr
    have hmemS : (a⁻¹ * b : ↥S) ∈ Subgroup.center (↥S) := by
      rw [← mem_centralizer_iff_mem_center]; simpa using hmem
    simpa using hmemS
  have hψ_surj : Function.Surjective ψ := by
    haveI : Finite (↥S ⧸ Subgroup.center (↥S)) := Nat.finite_of_card_ne_zero (by
      rw [hcard_eq]; exact Nat.card_pos.ne')
    haveI := Fintype.ofFinite (↥S ⧸ Subgroup.center (↥S))
    haveI := Fintype.ofFinite (R ⧸ Subgroup.centralizer (S : Set R))
    have hcardF : Fintype.card (↥S ⧸ Subgroup.center (↥S)) =
        Fintype.card (R ⧸ Subgroup.centralizer (S : Set R)) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard_eq]
    exact (Finite.injective_iff_surjective_of_equiv
      (Fintype.equivOfCardEq hcardF)).mp hψ_inj
  -- Every `r ∈ R` lies in `S · C_R(S)`.
  rw [eq_top_iff]
  intro r _
  obtain ⟨q, hq⟩ := hψ_surj (QuotientGroup.mk r)
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
  -- `mk (↑s) = mk r`, so `(↑s)⁻¹ r ∈ C_R(S)`.
  have hrel : (QuotientGroup.mk (s : R) : R ⧸ Subgroup.centralizer (S : Set R)) =
      QuotientGroup.mk r := hq
  have hc : (s : R)⁻¹ * r ∈ Subgroup.centralizer (S : Set R) :=
    (QuotientGroup.leftRel_apply).mp (Quotient.exact hrel)
  -- `r = ↑s · ((↑s)⁻¹ r)` with `↑s ∈ S`, `(↑s)⁻¹ r ∈ C_R(S)`.
  have hr_eq : r = (s : R) * ((s : R)⁻¹ * r) := by group
  rw [hr_eq]
  exact Subgroup.mul_mem_sup s.2 hc

end ExtraspecialCommutator

/-! ## 4D: Proposition 4.8(a) (pp. 35-36)

BG mmd L1511-1518. We formalize **part (a)** only: a `p`-group `R` of rank `r(R) ≤ 2`
and exponent `p` satisfies `|R| ≤ p³`. Part (b) (about `Ω₁(R)` for `p > 3`) depends on
Proposition 4.3 and is handled separately.
-/

section Prop48ExponentPrime

open OddOrder.GroupTheory

/-- **BG Proposition 4.8(a)** (BG mmd L1511-1518): if `p` is a prime, `R` is a `p`-group of
rank `r(R) ≤ 2` (here `pRank R p ≤ 2`) with exponent `p` (here `∀ x, x ^ p = 1`), then
`|R| ≤ p³`.

Following BG's proof: take a self-centralizing normal abelian subgroup `A ∈ SCN(R)` (obtained
from `Ch06.exists_maximal_normal_isMulCommutative` + `centralizer_eq_…`). Since `exp R = p`,
`A` is elementary abelian, so `|A| = p^{m(A)}` with `m(A) ≤ pRank R p ≤ 2`, giving `|A| ≤ p²`.
Conjugation embeds `R/A = R/C_R(A) ↪ Aut(A)`, so `|R/A| ∣ |Aut A|`; as `R/A` is a `p`-group
and `|Aut A|_p ≤ |GL(2,p)|_p = p` (for `|A| ≤ p²`), we get `|R/A| ≤ p`. Hence
`|R| = |R/A|·|A| ≤ p·p² = p³`. -/
theorem card_le_prime_cube_of_pRank_le_two_of_exponent_prime
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R) (hrank : pRank R p ≤ 2) (hexp : ∀ x : R, x ^ p = 1) :
    Nat.card R ≤ p ^ 3 := by
  classical
  have hp : p.Prime := Fact.out
  -- ── Step (i): take `A ∈ SCN(R)`, get self-centralizing `C_R(A) = A` (BG "Take A ∈ SCN(R)").
  obtain ⟨A, hA_normal, hA_comm, hA_max⟩ :=
    OddOrder.Isaacs.Ch06.exists_maximal_normal_isMulCommutative (P := R)
  haveI : A.Normal := hA_normal
  have hCent : Subgroup.centralizer (A : Set R) = A :=
    OddOrder.Isaacs.Ch06.centralizer_eq_of_maximal_normal_isMulCommutative hR hA_comm hA_max
  -- ── Step (ii): `exp p` ⇒ `A` elementary abelian; `|A| = p^kA`, `kA ≤ 2`, so `|A| ≤ p²`.
  have hA_ea : (A : Subgroup R).IsElementaryAbelian p := by
    refine ⟨isMulCommutative_iff.mp hA_comm, fun a => ?_⟩
    apply Subtype.ext
    push_cast
    exact hexp (a : R)
  letI : IsMulCommutative (↥A) := IsMulCommutative.of_comm hA_ea.comm
  letI := hA_ea.zmodModule
  have hlog_le : Nat.log p (Nat.card (↥A)) ≤ 2 := le_trans (le_pRank A hA_ea) hrank
  have hA_pow : Nat.card (↥A) = p ^ (Nat.log p (Nat.card (↥A))) := by
    rw [hA_ea.log_card_eq_finrank]
    exact hA_ea.card_eq_pow_finrank
  set kA := Nat.log p (Nat.card (↥A)) with hkA
  have hA_card : Nat.card (↥A) = p ^ kA := hA_pow
  have hA_le : Nat.card (↥A) ≤ p ^ 2 := by
    rw [hA_card]; exact Nat.pow_le_pow_right hp.pos hlog_le
  -- ── Step (iii): conjugation hom `R →* MulAut ↥A` with kernel `C_R(A) = A` ⇒ `R/A ↪ MulAut A`.
  let φ : R →* MulAut (↥A) := MulAut.conjNormal (H := A)
  -- `ker φ = C_R(A)` (the standard conjugation-kernel identity; cf. the local template
  -- `conjNormal_ker_eq_centralizer_local`), then `= A` by `hCent`.
  have hker_cent : φ.ker = Subgroup.centralizer (A : Set R) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg s hs
      have hfix0 : MulAut.conjNormal (H := A) g ⟨s, hs⟩ = (⟨s, hs⟩ : ↥A) := by
        rw [hg]; rfl
      have hfix : (g * s * g⁻¹ : R) = s := by
        have hh := congrArg (fun x : ↥A => (x : R)) hfix0
        simp only [MulAut.conjNormal_apply] at hh
        exact hh
      have : g * s * g⁻¹ * g = s * g := by rw [hfix]
      simpa [mul_assoc] using this.symm
    · intro hcent
      ext s
      have hcomm : (s : R) * g = g * (s : R) := hcent (s : R) s.2
      have hfix : MulAut.conjNormal (H := A) g s = s := by
        apply A.subtype_injective
        rw [Subgroup.coe_subtype, MulAut.conjNormal_apply, ← hcomm]; group
      rw [hfix]; rfl
  have hker : φ.ker = A := hker_cent.trans hCent
  let ψ : R ⧸ A →* MulAut (↥A) := QuotientGroup.lift A φ (by rw [hker])
  have hψ_inj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    dsimp only [ψ]
    rw [QuotientGroup.ker_lift, hker]
    simp
  have hdvd : Nat.card (R ⧸ A) ∣ Nat.card (MulAut (↥A)) :=
    Subgroup.card_dvd_of_injective ψ hψ_inj
  -- `R/A` is a `p`-group.
  obtain ⟨kQ, hkQ⟩ := IsPGroup.iff_card.mp (hR.to_quotient A)
  -- ── Step (iv): `|R/A| ≤ p` by case analysis on `kA ∈ {0, 1, 2}` (BG's `|Aut A|_p ≤ p`).
  have hquot_le : Nat.card (R ⧸ A) ≤ p := by
    -- It suffices to show `kQ ≤ 1`; then `|R/A| = p^kQ ≤ p`.
    suffices hkQ_le : kQ ≤ 1 by
      rw [hkQ]
      calc p ^ kQ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hkQ_le
        _ = p := pow_one p
    -- Reduce to `¬ (p² ∣ |MulAut A|)`: if `kQ ≥ 2` then `p² ∣ p^kQ = |R/A| ∣ |MulAut A|`.
    by_contra hkQ_gt
    rw [not_le] at hkQ_gt
    have hp2_dvd : p ^ 2 ∣ Nat.card (MulAut (↥A)) := by
      refine dvd_trans ?_ hdvd
      rw [hkQ]
      exact pow_dvd_pow p hkQ_gt
    -- `|MulAut A| = ∏_{i<kA}(p^kA - pⁱ)` (the `|GL(kA, p)|` formula), with `kA ≤ 2`.
    have hfr := hA_ea.log_card_eq_finrank
    rw [← hkA] at hfr
    have hcard_aut_gen :
        Nat.card (MulAut (↥A)) = ∏ i : Fin kA, (p ^ kA - p ^ (i : ℕ)) := by
      rw [hA_ea.card_mulAut, ← hfr]
    -- Now derive a contradiction by computing `|MulAut A|` in each rank case.
    have hp2_not_dvd : ¬ p ^ 2 ∣ Nat.card (MulAut (↥A)) := by
      rw [hcard_aut_gen]
      clear hp2_dvd hcard_aut_gen hdvd
      interval_cases kA
      · -- `kA = 0`: empty product `= 1`, `p² ∤ 1`.
        simp only [Finset.univ_eq_empty, Finset.prod_empty]
        intro hdvd1
        have := Nat.le_of_dvd one_pos hdvd1
        have hlt : 1 < p ^ 2 := by have := hp.two_le; nlinarith
        omega
      · -- `kA = 1`: product `= p^1 - p^0 = p - 1`, and `p ∤ p - 1` ⇒ `p² ∤ p - 1`.
        simp only [Fin.prod_univ_one, Fin.isValue, Fin.val_zero, pow_zero, pow_one]
        intro hdvd_pred
        have hp_dvd : p ∣ p - 1 :=
          (dvd_pow_self p (by norm_num : (2:ℕ) ≠ 0)).trans hdvd_pred
        have hpred_pos : 0 < p - 1 := by have := hp.two_le; omega
        have := Nat.le_of_dvd hpred_pos hp_dvd
        omega
      · -- `kA = 2`: product `= (p²-1)(p²-p) = p(p-1)(p-1)(p+1)`, whose `p`-part is `p¹`.
        have hcard_aut :
            (∏ i : Fin 2, (p ^ 2 - p ^ (i : ℕ))) = p * (p - 1) * (p - 1) * (p + 1) := by
          simp only [Fin.prod_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
          have h_sq_sub_one : p ^ 2 - 1 = (p + 1) * (p - 1) := by
            simpa using Nat.sq_sub_sq p 1
          have h_sq_sub_self : p ^ 2 - p = p * (p - 1) := by
            calc p ^ 2 - p = p * p - p * 1 := by rw [pow_two, mul_one]
              _ = p * (p - 1) := (Nat.mul_sub_left_distrib p p 1).symm
          rw [h_sq_sub_one, h_sq_sub_self]; ring
        rw [hcard_aut]
        -- `p² ∤ p(p-1)(p-1)(p+1)` because `p ∤ (p-1)(p-1)(p+1)`.
        intro hp2_dvd_aut
        have hp_not_dvd_pred : ¬ p ∣ p - 1 := by
          intro h
          have hpred_pos : 0 < p - 1 := by have := hp.two_le; omega
          have := Nat.le_of_dvd hpred_pos h
          omega
        have hp_not_dvd_succ : ¬ p ∣ p + 1 := by
          intro h
          have hsub : p ∣ (p + 1) - p := Nat.dvd_sub h (dvd_refl p)
          have hsub_eq : (p + 1) - p = 1 := by omega
          rw [hsub_eq] at hsub
          exact hp.not_dvd_one hsub
        have hp_not_dvd_rest : ¬ p ∣ (p - 1) * (p - 1) * (p + 1) := by
          intro h
          rcases hp.dvd_mul.mp h with hleft | hsucc
          · rcases hp.dvd_mul.mp hleft with h1 | h2
            · exact hp_not_dvd_pred h1
            · exact hp_not_dvd_pred h2
          · exact hp_not_dvd_succ hsucc
        have hp_dvd_rest : p ∣ (p - 1) * (p - 1) * (p + 1) := by
          have hmul : p * p ∣ p * ((p - 1) * (p - 1) * (p + 1)) := by
            simpa [pow_two, mul_assoc] using hp2_dvd_aut
          exact Nat.dvd_of_mul_dvd_mul_left hp.pos hmul
        exact hp_not_dvd_rest hp_dvd_rest
    exact hp2_not_dvd hp2_dvd
  -- ── Step (v): `|R| = |R/A|·|A| ≤ p·p² = p³`.
  have hmul : A.index * Nat.card (↥A) = Nat.card R := Subgroup.index_mul_card A
  have hindex : A.index = Nat.card (R ⧸ A) := (Subgroup.index_eq_card A).symm
  calc Nat.card R = A.index * Nat.card (↥A) := hmul.symm
    _ ≤ p * p ^ 2 := by rw [hindex]; exact Nat.mul_le_mul hquot_le hA_le
    _ = p ^ 3 := by ring

end Prop48ExponentPrime

/-! ## 4E: Proposition 4.8(b) (pp. 35-36)

BG mmd L1511-1520. We formalize **part (b)**: for `p > 3`, a `p`-group `R` of rank
`r(R) ≤ 2` has `Ω₁(R)` of exponent one or `p`. Following BG's minimal-counterexample
proof, the key reduction is "it suffices to show `cl(R) ≤ 3`", obtained by bounding
`|R| ≤ p⁴` (via part (a) on `Ω₁(S)` for a maximal `S`) and the standard fact that a
`p`-group of order `≤ p⁴` has nilpotency class `≤ 3`.
-/

section Prop48ExponentP

open OddOrder.GroupTheory
open scoped commutatorElement

/-- **`p`-group order bounds nilpotency class.** For a finite `p`-group `G` with
`|G| ≤ p^(j+1)` and `1 ≤ j`, the nilpotency class satisfies `cl(G) ≤ j`.

This is the standard fact "a group of order `pⁿ` has class `< n`" specialised to the
`j ≥ 1` regime where it holds without the abelian-endpoint exception (`Cₚ` has class
`1 = 0 + 1` but order `p = p^(0+1)`, so the naive `n = 1`, `j = 0` instance is false;
hence the `1 ≤ j` hypothesis).

Proof by strong induction on `|G|`, both `G` and `j` generalised:
* `Subsingleton G`: class `= 0 ≤ j`.
* `Nontrivial G`, `j = 1`: `|G| ≤ p²`, so `G` is abelian (order `1`, `p`, or `p²`;
  the `p²` case is `IsPGroup.commutative_of_card_eq_prime_sq`), giving `Z(G) = ⊤` and
  `cl(G) ≤ 1`.
* `Nontrivial G`, `j ≥ 2`: `|Z(G)| = pᵏ` with `k ≥ 1` (`card_center_eq_prime_pow`), so
  `|G/Z| ≤ p^((j-1)+1)`; the inductive hypothesis (on `j - 1 ≥ 1`) gives
  `cl(G/Z) ≤ j - 1`, and `cl(G) = cl(G/Z) + 1 ≤ j`. -/
theorem nilpotencyClass_le_of_card_le_pow {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G) {j : ℕ} (hj : 1 ≤ j)
    (hcard : Nat.card G ≤ p ^ (j + 1)) : Group.nilpotencyClass G ≤ j := by
  have hp : p.Prime := Fact.out
  -- Strong induction on `|G|`, with `j` and the group (as `R'`) quantified inside the motive.
  let motive : ℕ → Prop := fun N =>
    ∀ (j : ℕ), 1 ≤ j → ∀ {R' : Type _} [Group R'] [Finite R'], IsPGroup p R' →
      Nat.card R' = N → Nat.card R' ≤ p ^ (j + 1) → Group.nilpotencyClass R' ≤ j
  refine (Nat.strongRecOn (motive := motive) (Nat.card G) ?_) j hj hG rfl hcard
  intro N ih j hj R' _ _ hR' hcardN hcardR'
  haveI : Group.IsNilpotent R' := hR'.isNilpotent
  rcases subsingleton_or_nontrivial R' with hsub | hnt
  · -- `Subsingleton R'`: class `= 0 ≤ j`.
    exact le_trans (le_of_eq (Group.nilpotencyClass_zero_iff_subsingleton.mpr hsub)) (Nat.zero_le j)
  · -- `Nontrivial R'`.
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR'
    -- `m ≥ 1` since `R'` is nontrivial.
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with hm0 | hpos
      · exfalso; rw [hm0, pow_zero] at hm
        exact (not_subsingleton_iff_nontrivial.mpr hnt)
          (Finite.card_le_one_iff_subsingleton.mp (le_of_eq hm))
      · exact hpos
    rcases Nat.lt_or_ge j 2 with hj1 | hj2
    · -- `j = 1`: `|R'| ≤ p²` ⇒ `R'` abelian ⇒ `cl(R') ≤ 1`.
      have hj_eq : j = 1 := by omega
      subst hj_eq
      -- `R'` is commutative: `m ∈ {1, 2}` and `commutative_of_card_eq_prime_sq` / cyclic.
      have hcomm : ∀ a b : R', a * b = b * a := by
        have hm_le : m ≤ 2 := by
          have hpm : p ^ m ≤ p ^ 2 := by rw [← hm]; exact hcardR'
          exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hpm
        interval_cases m
        · -- `|R'| = p`: cyclic, hence commutative.
          haveI : IsCyclic R' := isCyclic_of_prime_card (p := p) (by rw [hm, pow_one])
          obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := R')
          intro a b
          obtain ⟨i, rfl⟩ := hg a
          obtain ⟨l, rfl⟩ := hg b
          exact zpow_mul_comm g i l
        · -- `|R'| = p²`: commutative.
          exact IsPGroup.commutative_of_card_eq_prime_sq hm
      -- `Z(R') = ⊤`, so `upperCentralSeries R' 1 = ⊤`, giving `cl(R') ≤ 1`.
      rw [← Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le, Subgroup.upperCentralSeries_one, eq_top_iff]
      intro z _
      rw [Subgroup.mem_center_iff]
      intro g
      exact hcomm g z
    · -- `j ≥ 2`: recurse on `R'/Z`.
      -- `|Z(R')| = pᵏ`, `k ≥ 1`.
      obtain ⟨k, hk_pos, hk⟩ := IsPGroup.card_center_eq_prime_pow hm hm_pos
      -- `|Z| · |R'/Z| = |R'|`.
      have hZmul : Nat.card (Subgroup.center R') * Nat.card (R' ⧸ Subgroup.center R') =
          Nat.card R' := by
        rw [← Subgroup.index_eq_card]; exact (Subgroup.center R').card_mul_index
      -- `|R'/Z| ≤ p^((j-1)+1) = p^j`.
      have hquot_le : Nat.card (R' ⧸ Subgroup.center R') ≤ p ^ ((j - 1) + 1) := by
        have hj_sub : (j - 1) + 1 = j := by omega
        rw [hj_sub]
        -- `p * |R'/Z| ≤ pᵏ * |R'/Z| = |R'| ≤ p^(j+1) = p * pʲ`.
        have hpk : p ≤ Nat.card (Subgroup.center R') := by
          rw [hk]; calc p = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk_pos
        have hstep : p * Nat.card (R' ⧸ Subgroup.center R') ≤ p * p ^ j := by
          calc p * Nat.card (R' ⧸ Subgroup.center R')
              ≤ Nat.card (Subgroup.center R') * Nat.card (R' ⧸ Subgroup.center R') :=
                Nat.mul_le_mul_right _ hpk
            _ = Nat.card R' := hZmul
            _ ≤ p ^ (j + 1) := hcardR'
            _ = p * p ^ j := by rw [pow_succ]; ring
        exact Nat.le_of_mul_le_mul_left hstep hp.pos
      -- `|R'/Z| < |R'| = N` since `|Z| ≥ p > 1`.
      have hquot_lt : Nat.card (R' ⧸ Subgroup.center R') < N := by
        rw [← hcardN, ← hZmul]
        have hZ_gt : 1 < Nat.card (Subgroup.center R') := by
          rw [hk]; exact one_lt_pow₀ hp.one_lt hk_pos.ne'
        have hQ_pos : 0 < Nat.card (R' ⧸ Subgroup.center R') := Nat.card_pos
        exact (Nat.lt_mul_iff_one_lt_left hQ_pos).mpr hZ_gt
      -- Inductive hypothesis on `R'/Z` with parameter `j - 1`.
      have hQpg : IsPGroup p (R' ⧸ Subgroup.center R') := hR'.to_quotient _
      have hQclass : Group.nilpotencyClass (R' ⧸ Subgroup.center R') ≤ j - 1 :=
        ih (Nat.card (R' ⧸ Subgroup.center R')) hquot_lt (j - 1) (by omega) hQpg rfl hquot_le
      -- `cl(R') = cl(R'/Z) + 1 ≤ (j-1) + 1 = j`.
      rw [Group.nilpotencyClass_eq_quotient_center_plus_one]
      omega

/-- From `cl(G) ≤ 3` one gets that every weight-`3` commutator `⁅⁅a, b⁆, c⁆` is central.
Bridge from the `nilpotencyClass` form (output of `nilpotencyClass_le_of_card_le_pow`) to
the packaged-commutator hypothesis required by `omega1_pow_eq_one`.

`cl(G) ≤ 3 ⇒ γ₄ = lowerCentralSeries G 3 = ⊥`. The element `⁅⁅a, b⁆, c⁆` lies in
`γ₃ = lowerCentralSeries G 2`, so for every `d`, `⁅⁅⁅a, b⁆, c⁆, d⁆ ∈ γ₄ = ⊥`, i.e.
`⁅⁅a, b⁆, c⁆` commutes with every `d`, i.e. it is central. -/
theorem pointwise_central_of_nilpotencyClass_le_three {G : Type*} [Group G]
    [Group.IsNilpotent G] (h : Group.nilpotencyClass G ≤ 3) :
    ∀ a b c : G, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center G := by
  -- `γ₄ = (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥`.
  have hbot : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr h
  intro a b c
  -- `⁅a, b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 = commutator G = ⁅⊤, ⊤⁆`.
  have h1 : ⁅a, b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
    rw [Subgroup.top_lowerCentralSeries_one]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  -- `⁅⁅a, b⁆, c⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 = ⁅lcs 1, ⊤⁆`.
  have h2 : ⁅⁅a, b⁆, c⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mem_commutator h1 (Subgroup.mem_top c)
  -- For every `d`, `⁅⁅⁅a, b⁆, c⁆, d⁆ ∈ lcs 3 = ⊥`, so the commutator is `1`.
  rw [Subgroup.mem_center_iff]
  intro d
  have h3 : ⁅⁅⁅a, b⁆, c⁆, d⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mem_commutator h2 (Subgroup.mem_top d)
  rw [hbot, Subgroup.mem_bot] at h3
  exact (commutatorElement_eq_one_iff_commute.mp h3).symm

/-- **BG Proposition 4.8(b)** (BG mmd L1511-1520): for a prime `p > 3` and a finite
`p`-group `R` of rank `r(R) ≤ 2` (here `pRank R p ≤ 2`), `Ω₁(R) = Omega R p 1` has
exponent one or `p`; i.e. every `g ∈ Ω₁(R)` satisfies `g ^ p = 1`.

Following BG's minimal-counterexample argument, recast (as in `omega1_pow_eq_one`) as a
strong induction on `|R|` proving the product-closure `x ^ p = y ^ p = 1 ⇒ (x*y)^p = 1`.
For each `R'`:
* If `⟨x, y⟩ ≠ R'`: apply the inductive hypothesis to the proper subgroup `⟨x, y⟩`.
* If `⟨x⟩ = R'`: `R'` is abelian, so `(x*y)^p = x^p y^p = 1`.
* Otherwise take a maximal (normal) `S ⊇ ⟨x⟩`. By induction `Ω₁(S)` has exponent `p`, so
  by part (a) `|Ω₁(S)| ≤ p³`; with `R' = ⟨Ω₁(S), y⟩` and `|⟨y⟩| ≤ p`, `|R'| ≤ p⁴`. Then
  `cl(R') ≤ 3` (`nilpotencyClass_le_of_card_le_pow`), so the weight-`3` commutators are
  central (`pointwise_central_of_nilpotencyClass_le_three`), and `omega1_pow_eq_one` (the
  `cl ≤ 3` branch of Prop 4.3) gives `(x*y)^p = 1`. -/
theorem omega1_pow_eq_one_of_pRank_le_two_of_three_lt
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R) (hp3 : 3 < p)
    (hrank : OddOrder.GroupTheory.pRank R p ≤ 2)
    {g : R} (hg : g ∈ Omega R p 1) : g ^ p = 1 := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  -- Reduce to product-closure of `{g | g^p = 1}`.
  suffices hclosed : ∀ x y : R, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1 by
    let omega1 : Subgroup R :=
      { carrier := {g : R | g ^ p = 1}
        mul_mem' := fun {x y} hx hy => hclosed x y hx hy
        one_mem' := one_pow p
        inv_mem' := fun {x} hx => by rw [Set.mem_setOf_eq, inv_pow, hx, inv_one] }
    have hle : Omega R p 1 ≤ omega1 := by
      rw [Omega, Subgroup.closure_le]
      intro x hx
      show x ^ p = 1
      exact pow_one p ▸ hx
    simpa [omega1] using hle hg
  clear hg g
  -- Strong induction on `Nat.card R`, with `R` and `pRank ≤ 2` in the motive.
  let motive : ℕ → Prop := fun n =>
    ∀ {R' : Type _} [Group R'] [Finite R'], IsPGroup p R' →
      OddOrder.GroupTheory.pRank R' p ≤ 2 → Nat.card R' = n →
        ∀ x y : R', x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1
  refine (Nat.strongRecOn (motive := motive) (Nat.card R) ?_) hR hrank rfl
  clear hR hrank
  intro n ih R' _ _ hR' hrank' hcard x y hxp hyp
  -- WLOG `⟨x, y⟩ = ⊤`: otherwise the inductive hypothesis on `K := ⟨x, y⟩` closes the goal.
  by_cases hxytop : Subgroup.closure ({x, y} : Set R') = ⊤
  · -- Main argument under `⟨x, y⟩ = ⊤`.
    by_cases hxtop : Subgroup.zpowers x = ⊤
    · -- `⟨x⟩ = ⊤`: `R'` is cyclic, hence abelian; `x, y` commute.
      have hxy : Commute x y := by
        have hy_mem : y ∈ Subgroup.zpowers x := hxtop ▸ Subgroup.mem_top y
        obtain ⟨ky, hk⟩ := hy_mem
        rw [← hk]; exact (Commute.refl x).zpow_right ky
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
      have hrankS : OddOrder.GroupTheory.pRank ↥S p ≤ 2 :=
        (OddOrder.GroupTheory.pRank_mono_of_le S).trans hrank'
      -- Inductive hypothesis: product-closure on `↥S`.
      have IHS : ∀ a b : ↥S, a ^ p = 1 → b ^ p = 1 → (a * b) ^ p = 1 :=
        ih (Nat.card ↥S) hScard hSpg hrankS rfl
      -- `{a : ↥S | a^p = 1}` is a subgroup of `↥S`; every element of `Ω₁(↥S)` has `p`-th power `1`.
      have hΩSpow : ∀ a ∈ Omega ↥S p 1, a ^ p = 1 := by
        let omega1S : Subgroup ↥S :=
          { carrier := {a : ↥S | a ^ p = 1}
            mul_mem' := fun {a b} ha hb => IHS a b ha hb
            one_mem' := one_pow p
            inv_mem' := fun {a} ha => by rw [Set.mem_setOf_eq, inv_pow, ha, inv_one] }
        have hΩle : Omega ↥S p 1 ≤ omega1S := by
          rw [Omega, Subgroup.closure_le]
          intro a ha
          show a ^ p = 1
          exact pow_one p ▸ ha
        intro a ha
        simpa [omega1S] using hΩle ha
      -- `Ω₁(↥S)` (as an `R'`-subgroup) is normal in `R'` and has exponent `p`.
      haveI : (Omega ↥S p 1).Characteristic := Omega.characteristic
      set H : Subgroup R' := (Omega ↥S p 1).map S.subtype with hH_def
      haveI hH_normal : H.Normal := by rw [hH_def]; infer_instance
      have hHpow : ∀ z ∈ H, z ^ p = 1 := by
        intro z hz
        rw [hH_def, Subgroup.mem_map] at hz
        obtain ⟨a, ha, rfl⟩ := hz
        have hap : a ^ p = 1 := hΩSpow a ha
        rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hap, Subgroup.coe_one]
      -- `x ∈ H`.
      have hxH : x ∈ H := by
        rw [hH_def, Subgroup.mem_map]
        refine ⟨⟨x, hxS⟩, ?_, by rw [Subgroup.coe_subtype]⟩
        exact Omega.mem_of_pow_eq_one (by rw [pow_one]; exact Subtype.ext (by simpa using hxp))
      -- **Step 5**: `|Ω₁(↥S)| ≤ p³` by part (a).
      haveI hSomega_pg : IsPGroup p ↥(Omega ↥S p 1) := hSpg.to_subgroup _
      have hSomega_rank : OddOrder.GroupTheory.pRank ↥(Omega ↥S p 1) p ≤ 2 :=
        (OddOrder.GroupTheory.pRank_mono_of_le (Omega ↥S p 1)).trans hrankS
      have hSomega_exp : ∀ w : ↥(Omega ↥S p 1), w ^ p = 1 := by
        intro w
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hΩSpow (w : ↥S) w.2
      have hcube : Nat.card ↥(Omega ↥S p 1) ≤ p ^ 3 :=
        card_le_prime_cube_of_pRank_le_two_of_exponent_prime hSomega_pg hSomega_rank hSomega_exp
      -- **Step 6**: `|R'| ≤ p⁴`. `R' = H ⊔ ⟨y⟩`, `|H| = |Ω₁(↥S)| ≤ p³`, `|⟨y⟩| ≤ p`.
      have hHcard : Nat.card ↥H ≤ p ^ 3 := by
        rw [hH_def, Subgroup.card_map_of_injective S.subtype_injective]
        exact hcube
      have hYcard : Nat.card ↥(Subgroup.zpowers y) ≤ p := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hyp)
      have hHY_top : H ⊔ Subgroup.zpowers y = ⊤ := by
        rw [eq_top_iff, ← hxytop, Subgroup.closure_le]
        intro w hw
        rcases hw with hw | hw
        · rw [hw]; exact Subgroup.mem_sup_left hxH
        · rw [Set.mem_singleton_iff] at hw; rw [hw]
          exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
      have hR'card : Nat.card R' ≤ p ^ 4 := by
        -- `↥(H ⊔ ⟨y⟩) = ↑H * ↑⟨y⟩`, so the multiplication map is surjective.
        have hsurj : Function.Surjective
            (fun q : ↥H × ↥(Subgroup.zpowers y) => ((q.1 : R') * (q.2 : R') : R')) := by
          intro z
          have hzmem : z ∈ H ⊔ Subgroup.zpowers y := hHY_top ▸ Subgroup.mem_top z
          rw [← SetLike.mem_coe, Subgroup.normal_mul] at hzmem
          obtain ⟨a, ha, b, hb, rfl⟩ := hzmem
          exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
        have hcard_le : Nat.card R' ≤ Nat.card (↥H × ↥(Subgroup.zpowers y)) := by
          have hRtop : Nat.card R' = Nat.card ↥(H ⊔ Subgroup.zpowers y) := by
            rw [hHY_top]; exact (Nat.card_congr (Subgroup.topEquiv).symm.toEquiv)
          rw [hRtop, hHY_top]
          have : Nat.card (↥(⊤ : Subgroup R')) = Nat.card R' :=
            Nat.card_congr (Subgroup.topEquiv).toEquiv
          rw [this]
          exact Nat.card_le_card_of_surjective _ hsurj
        calc Nat.card R' ≤ Nat.card (↥H × ↥(Subgroup.zpowers y)) := hcard_le
          _ = Nat.card ↥H * Nat.card ↥(Subgroup.zpowers y) := Nat.card_prod _ _
          _ ≤ p ^ 3 * p := Nat.mul_le_mul hHcard hYcard
          _ = p ^ 4 := by ring
      -- **Step 7**: `cl(R') ≤ 3`.
      haveI : Group.IsNilpotent R' := hR'.isNilpotent
      have hclass : Group.nilpotencyClass R' ≤ 3 :=
        nilpotencyClass_le_of_card_le_pow hR' (j := 3) (by norm_num) (by simpa using hR'card)
      -- **Step 8**: weight-`3` commutators central; apply `omega1_pow_eq_one`.
      have hc3' : ∀ a b c : R', ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center R' :=
        pointwise_central_of_nilpotencyClass_le_three hclass
      have hxy_mem : x * y ∈ Omega R' p 1 :=
        mul_mem
          (Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hxp))
          (Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hyp))
      exact omega1_pow_eq_one hR' hodd (Or.inr ⟨hp3, hc3'⟩) hxy_mem
  · -- `⟨x, y⟩ ≠ ⊤`: apply the inductive hypothesis to `K := ⟨x, y⟩`.
    set K : Subgroup R' := Subgroup.closure ({x, y} : Set R') with hK_def
    have hxK : x ∈ K := Subgroup.subset_closure (by left; rfl)
    have hyK : y ∈ K := Subgroup.subset_closure (by right; rfl)
    have hKcard : Nat.card ↥K < n := by
      rw [← hcard]
      have h_dvd : Nat.card ↥K ∣ Nat.card R' := ⟨K.index, by rw [mul_comm, K.index_mul_card]⟩
      have h_le : Nat.card ↥K ≤ Nat.card R' := Nat.le_of_dvd Nat.card_pos h_dvd
      have h_ne : Nat.card ↥K ≠ Nat.card R' := fun heq =>
        hxytop (Subgroup.eq_top_of_card_eq _ heq)
      exact Nat.lt_of_le_of_ne h_le h_ne
    haveI hKpg : IsPGroup p ↥K := hR'.to_subgroup K
    have hrankK : OddOrder.GroupTheory.pRank ↥K p ≤ 2 :=
      (OddOrder.GroupTheory.pRank_mono_of_le K).trans hrank'
    have IHK : ∀ a b : ↥K, a ^ p = 1 → b ^ p = 1 → (a * b) ^ p = 1 :=
      ih (Nat.card ↥K) hKcard hKpg hrankK rfl
    have hxKp : (⟨x, hxK⟩ : ↥K) ^ p = 1 := by
      apply Subtype.ext; rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hxp
    have hyKp : (⟨y, hyK⟩ : ↥K) ^ p = 1 := by
      apply Subtype.ext; rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hyp
    have hxyKp := IHK ⟨x, hxK⟩ ⟨y, hyK⟩ hxKp hyKp
    have hcoe : ((⟨x, hxK⟩ * ⟨y, hyK⟩ : ↥K) : R') ^ p = 1 := by
      rw [← Subgroup.coe_pow, hxyKp, Subgroup.coe_one]
    simpa using hcoe

/-- A maximal (coatom) normal subgroup `M` of a finite `p`-group `Q` has index `p`:
`Q/M` is a nontrivial `p`-group whose only subgroups are `⊥` and `⊤` (correspondence with
the coatom `M`), so a Cauchy order-`p` subgroup must be all of `Q/M`. -/
private theorem index_eq_prime_of_coatom {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQpg : IsPGroup p Q) (M : Subgroup Q) [M.Normal] (hM_coatom : IsCoatom M) :
    M.index = p := by
  have hp : p.Prime := Fact.out
  haveI hQMpg : IsPGroup p (Q ⧸ M) := hQpg.to_quotient M
  haveI hQMnt : Nontrivial (Q ⧸ M) := QuotientGroup.nontrivial_iff.mpr hM_coatom.1
  have hpdvd : p ∣ Nat.card (Q ⧸ M) := by
    rcases hQMpg.card_eq_or_dvd with h1 | hd
    · exact absurd (Finite.card_le_one_iff_subsingleton.mp h1.le)
        (not_subsingleton_iff_nontrivial.mpr hQMnt)
    · exact hd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Q ⧸ M) p hpdvd
  set H : Subgroup (Q ⧸ M) := Subgroup.zpowers g with hH_def
  have hHcard : Nat.card H = p := by rw [hH_def, Nat.card_zpowers, hg]
  have hHne : H ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hHcard; exact hp.one_lt.ne' hHcard.symm
  set Hc : Subgroup Q := H.comap (QuotientGroup.mk' M) with hHc_def
  have hM_le : M ≤ Hc := by
    rw [hHc_def]; intro m hm
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff m).mpr hm]
    exact one_mem H
  have hHc_eq : H = Hc.map (QuotientGroup.mk' M) := by
    rw [hHc_def, Subgroup.map_comap_eq, QuotientGroup.range_mk', top_inf_eq]
  have hHc_ne_M : Hc ≠ M := by
    intro heq; apply hHne; rw [hHc_eq, heq, QuotientGroup.map_mk'_self]
  have hHc_top : Hc = ⊤ := by
    rcases (hM_coatom.le_iff.mp hM_le) with h | h
    · exact h
    · exact absurd h.symm hHc_ne_M.symm
  have hH_top : H = ⊤ := by
    rw [hHc_eq, hHc_top, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective M)]
  rw [Subgroup.index_eq_card]
  have hcard : Nat.card (Q ⧸ M) = Nat.card H := by
    rw [hH_top]; exact (Nat.card_congr (Subgroup.topEquiv).toEquiv).symm
  rw [hcard, hHcard]

/-- **BG Lemma 4.9** (mmd L1522-1544). For `p > 3`, a `p`-group `R` with `|Ω₁(R)| ≤ p²`
satisfies `|Ω₁(R/T)| ≤ p²` for *every* normal subgroup `T ⊴ R`.

The proof is the double minimal-counterexample argument of BG: take `R` minimal among
counterexamples (strong induction on `|R|`) and, within `R`, take `T₀ ⊴ R` minimal subject
to `|Ω₁(R/T₀)| > p²`.

* `|T₀| = p`: otherwise pick a central `Z ≤ T₀ ∩ Z(R)` of order `p`; minimality of `T₀`
  gives `|Ω₁(R/Z)| ≤ p²`, induction (`|R/Z| < |R|`) applied to `R/Z` with `T₀/Z` plus the
  third isomorphism `(R/Z)/(T₀/Z) ≅ R/T₀` give `|Ω₁(R/T₀)| ≤ p²`, contradiction.
* `(4.6)`: `|R| = p⁴` and `R/T₀` has exponent `p`. The key sub-fact is that *every proper
  subgroup* `K < R/T₀` has `|Ω₁(K)| ≤ p²` (lift `K` to `K̃ < R`, apply induction to `K̃`).
  Hence `Ω₁(R/T₀)` is not contained in any maximal subgroup, so `Ω₁(R/T₀) = ⊤`; with
  Prop 4.8(b) (rank `≤ 2`) resp. the elementary-abelian extraction (rank `> 2`) this forces
  `R/T₀` of exponent `p` and order `p³`, whence `|R| = p⁴` (`|T₀| = p`).
* Final contradiction: `|Ω₁(R)| = p²` (Lemma 4.5 lower bound + hypothesis), so
  `|R/Ω₁(R)| = p²`. Since `cl(R) ≤ 3` (from `|R| ≤ p⁴`), `φ(x) = xᵖ` is a homomorphism
  (Prop 4.3(b)) with `ker φ = Ω₁(R)` and image in `T₀`, giving
  `p² = |R/Ω₁(R)| = |R/ker φ| = |im φ| ≤ |T₀| = p`, a contradiction. -/
theorem card_omega1_quotient_le_prime_sq {R : Type*} [Group R] [Finite R] {p : ℕ}
    [Fact p.Prime] (hR : IsPGroup p R) (hp3 : 3 < p)
    (hΩ : Nat.card (Omega R p 1) ≤ p ^ 2) (T : Subgroup R) [T.Normal] :
    Nat.card (Omega (R ⧸ T) p 1) ≤ p ^ 2 := by
  classical
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  -- Strong induction on `|R|`, with `R` and the hypotheses packaged in the motive.
  let motive : ℕ → Prop := fun n =>
    ∀ {R' : Type _} [Group R'] [Finite R'], IsPGroup p R' → Nat.card (Omega R' p 1) ≤ p ^ 2 →
      Nat.card R' = n → ∀ (T' : Subgroup R') [T'.Normal],
        Nat.card (Omega (R' ⧸ T') p 1) ≤ p ^ 2
  refine (Nat.strongRecOn (motive := motive) (Nat.card R) ?_) hR hΩ rfl T
  clear hR hΩ
  intro n ih R' _ _ hR' hΩ' hcard T' hT'N
  -- `ih : ∀ m < n, motive m`.
  -- Goal: `∀ T' [Normal], |Ω₁(R'/T')| ≤ p²`. By contradiction, pick a minimal bad `T₀`.
  by_contra hcon
  -- minimal `T₀` among normal subgroups with `|Ω₁(R'/T₀)| > p²`.
  have hex : ∃ (S : Subgroup R') (_ : S.Normal), p ^ 2 < Nat.card (Omega (R' ⧸ S) p 1) := by
    refine ⟨T', hT'N, ?_⟩; exact lt_of_not_ge hcon
  let Qpred : {S : Subgroup R' // S.Normal} → Prop := fun S =>
    haveI := S.2; p ^ 2 < Nat.card (Omega (R' ⧸ S.1) p 1)
  have hQne : {S : {S : Subgroup R' // S.Normal} | Qpred S}.Nonempty := by
    obtain ⟨S, hN, h⟩ := hex; exact ⟨⟨S, hN⟩, h⟩
  obtain ⟨T₀sub, hT₀mem, hT₀minraw⟩ :=
    Set.exists_min_image {S | Qpred S} (fun S => Nat.card S.1) (Set.toFinite _) hQne
  set T₀ : Subgroup R' := T₀sub.1 with hT₀def
  haveI hT₀N : T₀.Normal := T₀sub.2
  have hT₀bad : p ^ 2 < Nat.card (Omega (R' ⧸ T₀) p 1) := hT₀mem
  have hT₀min : ∀ (S : Subgroup R') [S.Normal],
      p ^ 2 < Nat.card (Omega (R' ⧸ S) p 1) → Nat.card T₀ ≤ Nat.card S := by
    intro S hSN hSbad; exact hT₀minraw ⟨S, hSN⟩ hSbad
  have hQpg : IsPGroup p (R' ⧸ T₀) := hR'.to_quotient T₀
  -- `R'/T₀` is nontrivial since `|Ω₁(R'/T₀)| > p² > 1`.
  haveI hQnt : Nontrivial (R' ⧸ T₀) := by
    rcases subsingleton_or_nontrivial (R' ⧸ T₀) with hs | hn
    · exfalso
      haveI := hs
      have h1 : Nat.card (Omega (R' ⧸ T₀) p 1) ≤ Nat.card (R' ⧸ T₀) :=
        Subgroup.card_le_card_group _
      have h2 : Nat.card (R' ⧸ T₀) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
      rw [h2] at h1
      have : 1 < p ^ 2 := by nlinarith [hp.two_le]
      omega
    · exact hn
  -- ============================================================
  -- Fact F: every proper subgroup `K < R'/T₀` has `|Ω₁(K)| ≤ p²`.
  -- ============================================================
  have factF : ∀ (K : Subgroup (R' ⧸ T₀)), K ≠ ⊤ →
      Nat.card (Omega ↥K p 1) ≤ p ^ 2 := by
    intro K hKtop
    -- Lift `K` to `M ≤ R'` via `comap (mk' T₀)`; then `K = M.map (mk' T₀)`, `M ≠ ⊤`.
    set M : Subgroup R' := K.comap (QuotientGroup.mk' T₀) with hM_def
    have hMmap : M.map (QuotientGroup.mk' T₀) = K := by
      rw [hM_def, Subgroup.map_comap_eq, QuotientGroup.range_mk', top_inf_eq]
    have hMtop : M ≠ ⊤ := by
      intro hMtop'
      exact hKtop (by rw [← hMmap, hMtop',
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective T₀)])
    haveI hMpg : IsPGroup p ↥M := hR'.to_subgroup M
    have hMcard_lt : Nat.card ↥M < n := by
      rw [← hcard]
      have hdvd : Nat.card ↥M ∣ Nat.card R' := ⟨M.index, by rw [mul_comm, M.index_mul_card]⟩
      have hle : Nat.card ↥M ≤ Nat.card R' := Nat.le_of_dvd Nat.card_pos hdvd
      have hne : Nat.card ↥M ≠ Nat.card R' := fun heq => hMtop (Subgroup.eq_top_of_card_eq _ heq)
      exact Nat.lt_of_le_of_ne hle hne
    -- `|Ω₁(↥M)| ≤ |Ω₁(R')| ≤ p²` (`Ω₁(↥M)` maps into `Ω₁(R')`).
    have hΩM : Nat.card (Omega ↥M p 1) ≤ p ^ 2 := by
      have hmap_le : (Omega ↥M p 1).map M.subtype ≤ Omega R' p 1 := by
        rw [Subgroup.map_le_iff_le_comap, Omega, Subgroup.closure_le]
        rintro ⟨g, hgM⟩ (hg : (⟨g, hgM⟩ : ↥M) ^ (p ^ 1) = 1)
        change (⟨g, hgM⟩ : ↥M) ∈ Subgroup.comap M.subtype (Omega R' p 1)
        rw [Subgroup.mem_comap]
        have hgp : g ^ (p ^ 1) = 1 := by
          have := congrArg (Subgroup.subtype M) hg; rwa [map_pow, map_one] at this
        exact Omega.mem_of_pow_eq_one hgp
      calc Nat.card (Omega ↥M p 1)
          = Nat.card ((Omega ↥M p 1).map M.subtype) :=
            (Subgroup.card_map_of_injective M.subtype_injective).symm
        _ ≤ Nat.card (Omega R' p 1) := Subgroup.card_le_of_le hmap_le
        _ ≤ p ^ 2 := hΩ'
    -- Induction on `↥M`: `4.9` holds for `↥M`.
    have h49M : ∀ (U : Subgroup ↥M) [U.Normal], Nat.card (Omega (↥M ⧸ U) p 1) ≤ p ^ 2 :=
      fun U _ => ih (Nat.card ↥M) hMcard_lt hMpg hΩM rfl U
    -- Transport: `↥K ≃ ↥M ⧸ (T₀.subgroupOf M)` via the first isomorphism theorem.
    let φ : M →* (R' ⧸ T₀) := (QuotientGroup.mk' T₀).comp M.subtype
    have hrange : φ.range = K := by
      rw [← hMmap]; ext x; simp [φ, MonoidHom.mem_range, Subgroup.mem_map]
    let e : (↥M ⧸ φ.ker) ≃* ↥φ.range := QuotientGroup.quotientKerEquivRange φ
    have hmap : (Omega (↥M ⧸ φ.ker) p 1).map e.toMonoidHom = Omega (↥φ.range) p 1 := by
      rw [Omega, Omega, MonoidHom.map_closure]
      congr 1
      ext b
      simp only [Set.mem_image, Set.mem_setOf_eq, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨a, ha, rfl⟩; rw [← map_pow, ha, map_one]
      · intro hb
        refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
        have hbb : e (e.symm b ^ p ^ 1) = b ^ p ^ 1 := by rw [map_pow, e.apply_symm_apply]
        rw [hb] at hbb
        have h1 : e.symm b ^ p ^ 1 = e.symm 1 := by rw [← hbb, e.symm_apply_apply]
        rw [h1, map_one]
    have hcardeq : Nat.card (Omega (↥φ.range) p 1) = Nat.card (Omega (↥M ⧸ φ.ker) p 1) := by
      rw [← hmap]; exact Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
    rw [show Nat.card (Omega ↥K p 1) = Nat.card (Omega (↥φ.range) p 1) by rw [hrange], hcardeq]
    exact h49M φ.ker
  -- ============================================================
  -- Step 1: `|T₀| = p`.
  -- ============================================================
  have hT₀card : Nat.card T₀ = p := by
    haveI hT₀pg : IsPGroup p T₀ := hR'.to_subgroup T₀
    -- `T₀` is nontrivial: if `T₀ = ⊥`, then `R'/⊥ ≃* R'` and `|Ω₁(R'/T₀)| = |Ω₁(R')| ≤ p²`,
    -- contradicting `|Ω₁(R'/T₀)| > p²`.
    have hT₀nt : Nontrivial T₀ := by
      rcases subsingleton_or_nontrivial T₀ with hs | hn
      · exfalso
        have hbot : T₀ = ⊥ := by
          rw [Subgroup.eq_bot_iff_card]
          exact Nat.card_eq_one_iff_unique.mpr ⟨hs, ⟨1⟩⟩
        -- `R'/T₀ ≃* R'/⊥ ≃* R'` (avoids rewriting `T₀` inside a quotient type).
        let e : (R' ⧸ T₀) ≃* R' :=
          (QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot (G := R'))
        have hmap : (Omega (R' ⧸ T₀) p 1).map e.toMonoidHom = Omega R' p 1 := by
          rw [Omega, Omega, MonoidHom.map_closure]; congr 1; ext b
          simp only [Set.mem_image, Set.mem_setOf_eq, MulEquiv.coe_toMonoidHom]
          constructor
          · rintro ⟨a, ha, rfl⟩; rw [← map_pow, ha, map_one]
          · intro hb; refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
            have hbb : e (e.symm b ^ p ^ 1) = b ^ p ^ 1 := by rw [map_pow, e.apply_symm_apply]
            rw [hb] at hbb
            have h1 : e.symm b ^ p ^ 1 = e.symm 1 := by rw [← hbb, e.symm_apply_apply]
            rw [h1, map_one]
        have hceq : Nat.card (Omega (R' ⧸ T₀) p 1) = Nat.card (Omega R' p 1) := by
          rw [← hmap]
          exact (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm
        rw [hceq] at hT₀bad; omega
      · exact hn
    by_contra hne
    -- Take a central `Z ≤ T₀` of order `p`.
    have hinf_nt : Nontrivial ((T₀ ⊓ Subgroup.center R' : Subgroup R')) :=
      OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial hR' hT₀nt
    have hpg_inf : IsPGroup p (T₀ ⊓ Subgroup.center R' : Subgroup R') := hR'.to_subgroup _
    have hpdvd : p ∣ Nat.card (T₀ ⊓ Subgroup.center R' : Subgroup R') := by
      rcases hpg_inf.card_eq_or_dvd with h1 | hd
      · exact absurd (Finite.card_le_one_iff_subsingleton.mp h1.le)
          (not_subsingleton_iff_nontrivial.mpr hinf_nt)
      · exact hd
    obtain ⟨g, hg⟩ :=
      exists_prime_orderOf_dvd_card' (G := (T₀ ⊓ Subgroup.center R' : Subgroup R')) p hpdvd
    set z : R' := (g : R') with hz_def
    set Z : Subgroup R' := Subgroup.zpowers z with hZ_def
    have hZ_le_center : Z ≤ Subgroup.center R' := by
      rw [hZ_def, Subgroup.zpowers_le]; exact g.2.2
    haveI hZ_normal : Z.Normal := by
      constructor; intro nn hnn g'
      have := Subgroup.mem_center_iff.mp (hZ_le_center hnn) g'
      rw [this, mul_assoc, mul_inv_cancel, mul_one]; exact hnn
    have hZT : Z ≤ T₀ := by rw [hZ_def, Subgroup.zpowers_le]; exact g.2.1
    have hZcard : Nat.card Z = p := by
      rw [hZ_def, Nat.card_zpowers, hz_def, Subgroup.orderOf_coe, hg]
    -- `|T₀| > p` (since `|T₀| ≥ |Z| = p` and `|T₀| ≠ p`).
    have hT₀_gt : p < Nat.card T₀ := by
      have hge : p ≤ Nat.card T₀ := hZcard ▸ Subgroup.card_le_of_le hZT
      omega
    -- Minimality of `T₀`: `|Z| = p < |T₀|` ⇒ `|Ω₁(R'/Z)| ≤ p²`.
    have hΩRZ : Nat.card (Omega (R' ⧸ Z) p 1) ≤ p ^ 2 := by
      by_contra hbad
      have hbad' : p ^ 2 < Nat.card (Omega (R' ⧸ Z) p 1) := lt_of_not_ge hbad
      have := hT₀min Z hbad'; rw [hZcard] at this; omega
    -- `|R'/Z| < |R'| = n`.
    have hRZ_lt : Nat.card (R' ⧸ Z) < n := by
      rw [← hcard, ← Z.index_eq_card]
      have hmul := Z.card_mul_index
      have hZpos : 1 < Nat.card Z := by rw [hZcard]; exact hp.one_lt
      calc Z.index = Nat.card R' / Nat.card Z := by
              rw [← hmul, Nat.mul_div_cancel_left _ Nat.card_pos]
        _ < Nat.card R' := Nat.div_lt_self Nat.card_pos hZpos
    haveI hRZpg : IsPGroup p (R' ⧸ Z) := hR'.to_quotient Z
    haveI hT₀map_normal : (T₀.map (QuotientGroup.mk' Z)).Normal :=
      Subgroup.Normal.map (inferInstance : T₀.Normal) (QuotientGroup.mk' Z)
        (QuotientGroup.mk'_surjective Z)
    -- Induction on `R'/Z` with `T₀/Z = T₀.map (mk' Z)`.
    have h49RZ := ih (Nat.card (R' ⧸ Z)) hRZ_lt hRZpg hΩRZ rfl (T₀.map (QuotientGroup.mk' Z))
    -- Third isomorphism `(R'/Z)/(T₀/Z) ≃* R'/T₀`, transport `Ω₁`.
    let e := QuotientGroup.quotientQuotientEquivQuotient Z T₀ hZT
    have hmap : (Omega ((R' ⧸ Z) ⧸ (T₀.map (QuotientGroup.mk' Z))) p 1).map e.toMonoidHom
        = Omega (R' ⧸ T₀) p 1 := by
      rw [Omega, Omega, MonoidHom.map_closure]; congr 1; ext b
      simp only [Set.mem_image, Set.mem_setOf_eq, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨a, ha, rfl⟩; rw [← map_pow, ha, map_one]
      · intro hb; refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
        have hbb : e (e.symm b ^ p ^ 1) = b ^ p ^ 1 := by rw [map_pow, e.apply_symm_apply]
        rw [hb] at hbb
        have h1 : e.symm b ^ p ^ 1 = e.symm 1 := by rw [← hbb, e.symm_apply_apply]
        rw [h1, map_one]
    have hcard_eq : Nat.card (Omega (R' ⧸ T₀) p 1)
        = Nat.card (Omega ((R' ⧸ Z) ⧸ (T₀.map (QuotientGroup.mk' Z))) p 1) := by
      rw [← hmap]; exact Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
    rw [hcard_eq] at hT₀bad
    exact absurd h49RZ (not_le.mpr hT₀bad)
  -- ============================================================
  -- Step 2 (4.6): `R'/T₀` has exponent `p`, `|R'/T₀| = p³`, `|R'| = p⁴`.
  -- ============================================================
  -- Helper: a subgroup `K ≤ M ≤ R'/T₀` of exponent `p` injects into `Ω₁(M)`.
  have hexp_card_le : ∀ (K M : Subgroup (R' ⧸ T₀)), K ≤ M → (∀ k ∈ K, k ^ p = 1) →
      Nat.card K ≤ Nat.card (Omega ↥M p 1) := by
    intro K M hKM hKexp
    have hsub_le : K.subgroupOf M ≤ Omega ↥M p 1 := by
      intro k hk
      rw [Subgroup.mem_subgroupOf] at hk
      refine Omega.mem_of_pow_eq_one ?_
      rw [pow_one]; apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hKexp _ hk
    calc Nat.card K = Nat.card (K.subgroupOf M) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv).symm
      _ ≤ Nat.card (Omega ↥M p 1) := Subgroup.card_le_of_le hsub_le
  -- `R'/T₀` has exponent `p` and order `p³`. Case split on `pRank (R'/T₀) p`.
  have hQ : (∀ x : R' ⧸ T₀, x ^ p = 1) ∧ Nat.card (R' ⧸ T₀) = p ^ 3 := by
    rcases Nat.lt_or_ge (OddOrder.GroupTheory.pRank (R' ⧸ T₀) p) 3 with hr | hr
    · -- Case `r(R'/T₀) ≤ 2`.
      have hr2 : OddOrder.GroupTheory.pRank (R' ⧸ T₀) p ≤ 2 := by omega
      -- Prop 4.8(b): every element of `Ω₁(R'/T₀)` has `p`-th power `1`.
      have hΩexp : ∀ g ∈ Omega (R' ⧸ T₀) p 1, g ^ p = 1 := fun g hg =>
        omega1_pow_eq_one_of_pRank_le_two_of_three_lt hQpg hp3 hr2 hg
      -- `Ω₁(R'/T₀) = ⊤`: else it sits in a maximal subgroup `M̄`, but then
      -- `|Ω₁(R'/T₀)| ≤ |Ω₁(M̄)| ≤ p²` (Fact F), contradicting `|Ω₁(R'/T₀)| > p²`.
      have hΩtop : Omega (R' ⧸ T₀) p 1 = ⊤ := by
        by_contra hne
        obtain ⟨M, hM_coatom, hΩM_le⟩ :=
          (IsCoatomic.eq_top_or_exists_le_coatom (Omega (R' ⧸ T₀) p 1)).resolve_left hne
        have hMtop : M ≠ ⊤ := hM_coatom.1
        have hcard_le := hexp_card_le (Omega (R' ⧸ T₀) p 1) M hΩM_le hΩexp
        have := hcard_le.trans (factF M hMtop)
        omega
      have hexp : ∀ x : R' ⧸ T₀, x ^ p = 1 := fun x =>
        hΩexp x (hΩtop ▸ Subgroup.mem_top x)
      refine ⟨hexp, ?_⟩
      -- `|R'/T₀| ≤ p³` (Prop 4.8(a)) and `> p²` (since `Ω₁ = ⊤`), so `= p³`.
      have hub : Nat.card (R' ⧸ T₀) ≤ p ^ 3 :=
        card_le_prime_cube_of_pRank_le_two_of_exponent_prime hQpg hr2 hexp
      have hgt : p ^ 2 < Nat.card (R' ⧸ T₀) := by
        have : Nat.card (Omega (R' ⧸ T₀) p 1) = Nat.card (R' ⧸ T₀) := by
          rw [hΩtop]; exact Nat.card_congr (Subgroup.topEquiv).toEquiv
        rw [← this]; exact hT₀bad
      -- `p² < |Q| ≤ p³`, `|Q|` a power of `p` ⇒ `|Q| = p³`.
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQpg
      rw [hm] at hub hgt ⊢
      have h2 : 2 < m := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hgt
      have h3 : m ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hub
      have : m = 3 := by omega
      rw [this]
    · -- Case `r(R'/T₀) ≥ 3`: there is an elementary abelian `A` with `p³ ≤ |A|`.
      have hnotle : ¬ OddOrder.GroupTheory.pRank (R' ⧸ T₀) p ≤ 2 := by omega
      rw [OddOrder.GroupTheory.pRank_le_iff] at hnotle
      simp only [not_forall, not_le, exists_prop] at hnotle
      obtain ⟨A, hA_elem, hA_log⟩ := hnotle
      have hA_card_ge : p ^ 3 ≤ Nat.card A := by
        calc p ^ 3 ≤ p ^ (Nat.log p (Nat.card A)) :=
              Nat.pow_le_pow_right hp.pos (by omega)
          _ ≤ Nat.card A := Nat.pow_log_le_self p Nat.card_pos.ne'
      have hA_exp : ∀ a ∈ A, a ^ p = 1 := by
        intro a ha
        have := hA_elem.pow_eq_one ⟨a, ha⟩
        simpa using congrArg (Subtype.val) this
      -- `A = ⊤`: else `A ≤ coatom M̄`, but then `p³ ≤ |A| ≤ |Ω₁(M̄)| ≤ p²`, contradiction.
      have hAtop : A = ⊤ := by
        by_contra hne
        obtain ⟨M, hM_coatom, hAM_le⟩ :=
          (IsCoatomic.eq_top_or_exists_le_coatom A).resolve_left hne
        have hcard_le := hexp_card_le A M hAM_le hA_exp
        have hcontra := hA_card_ge.trans (hcard_le.trans (factF M hM_coatom.1))
        have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
        omega
      -- `R'/T₀` is elementary abelian (`= A`), hence exponent `p`.
      have hQ_elem : (⊤ : Subgroup (R' ⧸ T₀)).IsElementaryAbelian p := hAtop ▸ hA_elem
      have hexp : ∀ x : R' ⧸ T₀, x ^ p = 1 := by
        intro x
        have := hQ_elem.pow_eq_one ⟨x, Subgroup.mem_top x⟩
        simpa using congrArg (Subtype.val) this
      refine ⟨hexp, ?_⟩
      -- `|R'/T₀| ≥ p³` (from `A`) and `≤ p³` (each maximal subgroup has order `≤ p²`).
      have hge : p ^ 3 ≤ Nat.card (R' ⧸ T₀) := by
        calc p ^ 3 ≤ Nat.card A := hA_card_ge
          _ ≤ Nat.card (R' ⧸ T₀) := Subgroup.card_le_card_group A
      have hle : Nat.card (R' ⧸ T₀) ≤ p ^ 3 := by
        -- maximal `M̄`: `|M̄| ≤ p²` (Fact F, `M̄` exp `p`), index `p`, so `|Q| ≤ p³`.
        obtain ⟨M, hM_coatom, _⟩ :=
          (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup (R' ⧸ T₀))).resolve_left
            (fun hbot => (bot_lt_top (α := Subgroup (R' ⧸ T₀))).ne hbot)
        have hMtop : M ≠ ⊤ := hM_coatom.1
        haveI : M.Normal := hM_coatom.normal_of_isPGroup hQpg
        have hMexp_card : Nat.card M ≤ p ^ 2 :=
          (hexp_card_le M M (le_refl M) (fun k _ => hexp k)).trans (factF M hMtop)
        have hindex : M.index = p := index_eq_prime_of_coatom hQpg M hM_coatom
        calc Nat.card (R' ⧸ T₀) = M.index * Nat.card M := (M.index_mul_card).symm
          _ = p * Nat.card M := by rw [hindex]
          _ ≤ p * p ^ 2 := Nat.mul_le_mul_left p hMexp_card
          _ = p ^ 3 := by ring
      exact le_antisymm hle hge
  have hQexp : ∀ x : R' ⧸ T₀, x ^ p = 1 := hQ.1
  have hQcard : Nat.card (R' ⧸ T₀) = p ^ 3 := hQ.2
  have hR'card : Nat.card R' = p ^ 4 := by
    have hmul := T₀.card_mul_index
    rw [hT₀card, Subgroup.index_eq_card, hQcard] at hmul
    rw [← hmul]; ring
  -- ============================================================
  -- Step 3: `|Ω₁(R')| = p²`, `|R'/Ω₁(R')| = p²`.
  -- ============================================================
  have hΩeq : Nat.card (Omega R' p 1) = p ^ 2 := by
    -- `R'/T₀` is noncyclic (`|Ω₁(R'/T₀)| > p² > p`), hence `R'` is noncyclic.
    have hQnc : ¬ IsCyclic (R' ⧸ T₀) := by
      intro hcyc
      haveI := hcyc
      have := card_omega1_eq_prime_of_isCyclic hQpg
      rw [this] at hT₀bad
      nlinarith [hp.two_le]
    have hRnc : ¬ IsCyclic R' := by
      intro hcyc
      haveI := hcyc
      haveI : IsCyclic (R' ⧸ T₀) :=
        isCyclic_of_surjective (QuotientGroup.mk' T₀) (QuotientGroup.mk'_surjective T₀)
      exact hQnc inferInstance
    -- Lemma 4.5(a): `R'` has an elementary abelian subgroup `E` of order `p²`; `E ≤ Ω₁(R')`.
    obtain ⟨E, hE_elem, hE_card⟩ :=
      exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic hR' hodd hRnc
    have hE_le : E ≤ Omega R' p 1 := by
      intro a ha
      refine Omega.mem_of_pow_eq_one ?_
      rw [pow_one]
      have := hE_elem.pow_eq_one ⟨a, ha⟩
      simpa using congrArg (Subtype.val) this
    have hlb : p ^ 2 ≤ Nat.card (Omega R' p 1) := by
      rw [← hE_card]; exact Subgroup.card_le_of_le hE_le
    exact le_antisymm hΩ' hlb
  have hRΩcard : Nat.card (R' ⧸ Omega R' p 1) = p ^ 2 := by
    have hmul := (Omega R' p 1).card_mul_index
    rw [Subgroup.index_eq_card, hΩeq, hR'card] at hmul
    have : p ^ 2 * Nat.card (R' ⧸ Omega R' p 1) = p ^ 2 * p ^ 2 := by rw [hmul]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  -- ============================================================
  -- Step 4: `φ(x) = xᵖ` is a homomorphism `R' →* R'`, image `≤ T₀`.
  -- ============================================================
  -- cl(R') ≤ 3
  haveI : Group.IsNilpotent R' := hR'.isNilpotent
  have hclass : Group.nilpotencyClass R' ≤ 3 :=
    nilpotencyClass_le_of_card_le_pow hR' (j := 3) (by norm_num) (by simpa using hR'card.le)
  have hc3 : ∀ a b c : R', ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center R' :=
    pointwise_central_of_nilpotencyClass_le_three hclass
  -- `commutator R' ≤ Ω₁(R')` from `R'/Ω₁(R')` abelian (order p²).
  have hcomm_le : _root_.commutator R' ≤ Omega R' p 1 := by
    haveI : IsMulCommutative (R' ⧸ Omega R' p 1) :=
      IsMulCommutative.of_comm (IsPGroup.commutative_of_card_eq_prime_sq hRΩcard)
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp ‹_›
  have hpow_hom : ∀ x y : R', (x * y) ^ p = x ^ p * y ^ p := fun x y =>
    pow_mul_eq_mul_pow_of_commutator_le_omega1 hR' hodd (Or.inr ⟨hp3, hc3⟩) hcomm_le x y
  let φ : R' →* R' := MonoidHom.mk' (fun x => x ^ p) (fun x y => hpow_hom x y)
  -- image ≤ T₀
  have hφ_range : φ.range ≤ T₀ := by
    rintro _ ⟨x, rfl⟩
    change (x ^ p) ∈ T₀
    have hq : (QuotientGroup.mk' T₀ x) ^ p = 1 := hQexp _
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
    exact hq
  -- ============================================================
  -- Step 5: `ker φ = Ω₁(R')` and the final contradiction.
  -- ============================================================
  have hker : φ.ker = Omega R' p 1 := by
    let om : Subgroup R' :=
      { carrier := {g : R' | g ^ p = 1}
        mul_mem' := fun {x y} hx hy => by
          rw [Set.mem_setOf_eq] at hx hy ⊢; rw [hpow_hom, hx, hy, mul_one]
        one_mem' := one_pow p
        inv_mem' := fun {x} hx => by
          rw [Set.mem_setOf_eq, inv_pow, (by exact hx : x ^ p = 1), inv_one] }
    have hker_eq : φ.ker = om := by
      ext x; simp only [MonoidHom.mem_ker, MonoidHom.mk'_apply, φ]; rfl
    rw [hker_eq]
    apply le_antisymm
    · intro x hx
      exact Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hx)
    · rw [Omega, Subgroup.closure_le]
      intro x hx
      simpa [om] using (pow_one p ▸ hx : x ^ p = 1)
  -- `|R'/ker φ| = |im φ| ≤ |T₀| = p`, but `= |R'/Ω₁(R')| = p²`.
  have hquot_card : Nat.card (R' ⧸ φ.ker) = p ^ 2 := by
    rw [hker]; exact hRΩcard
  have hrange_card : Nat.card φ.range = p ^ 2 := by
    have e := QuotientGroup.quotientKerEquivRange φ
    rw [← hquot_card]; exact (Nat.card_congr e.toEquiv).symm
  have hle_T₀ : Nat.card φ.range ≤ Nat.card T₀ := Subgroup.card_le_of_le hφ_range
  rw [hrange_card, hT₀card] at hle_T₀
  -- `p² ≤ p` with `p > 3`: contradiction.
  have : p ^ 2 ≤ p := hle_T₀
  nlinarith [hp.two_le, sq_nonneg p]

end Prop48ExponentP

section Lemma417

/-! ## §4G: Lemma 4.17 — rank-`≤ 2` `p`-群の odd 自己同型群の導来部分群 (mmd L1706-1732)

`A ≤ Aut R` odd, `r(R) ≤ 2` ⇒ `A'` は `p`-群。BG は `A` solvable も仮定するが,
本証明が使う §2 エンジン (`odd_two_dim_abelian` /
`isPGroup_commutator_of_faithful_two_dim_charP`) は odd のみで成立するため不要。

証明: Thm 1.13 の critical `H` (`exp p`, `C_{Aut R}(H)` は `p`-群) を取り
`V = H/Φ(H)`, `C = C_A(V)` とおく。
(i) `C` は `p`-群: `c ∈ C` の `p'`-part は `Φ(H)` mod 自明に作用するので Thm 1.8
(Burnside) で `C_A(H)` に落ち, それが `p`-群 (Thm 1.13) ゆえ自明。
(ii) `|H| ≤ p³` (Prop 4.8) で `|V| ∈ {p, p², p³}`。`|V| = p³` なら `Φ(H) = 1`,
`H` elem-ab rank 3 で `r(R) ≤ 2` に矛盾。
(iii) `|V| = p`: `Aut V` abelian ⇒ `A' ≤ C`。
(iv) `|V| = p²`: `A/C ↪ Aut V ≅ GL(2,p)` faithful。`p ∣ |A/C|` なら Thm 2.6(b) 形
(`isPGroup_commutator_of_faithful_two_dim_charP`) で `(A/C)'` は `p`-群, さもなくば
Thm 2.6(a) (`odd_two_dim_abelian`) で `A/C` abelian。いずれも kernel `C` (p-群) と
合成して `A'` は `p`-群。 -/

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)
open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)
open scoped commutatorElement IsMulCommutative

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- **GL(2,p) branch engine for Lemma 4.17**: a finite odd-order group `B` mapping
injectively into `GL (Fin 2) (ZMod p)` either has `p`-group commutator (`p ∣ |B|`,
Thm 2.6(b) via `isPGroup_commutator_of_faithful_two_dim_charP`) or is abelian
(`p ∤ |B|`, Thm 2.6(a) via `odd_two_dim_abelian`). The representation lives on the
concrete module `Fin 2 → ZMod p` (via `Matrix.GeneralLinearGroup.toLin`), keeping all
instances global — a `letI`-bound module on `Additive Q` would wedge instance synthesis
(cf. the warning at `IsElementaryAbelian.addAutEquivGL`). -/
private theorem isPGroup_commutator_or_comm_of_homGLTwo
    {p : ℕ} [Fact p.Prime] {B : Type*} [Group B] [Finite B] (hB_odd : Odd (Nat.card B))
    (ι : B →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
    (hι : Function.Injective ι) :
    IsPGroup p (_root_.commutator B) ∨ ∀ x y : B, x * y = y * x := by
  classical
  have hdim : Module.finrank (ZMod p) (Fin 2 → ZMod p) = 2 := by
    rw [Module.finrank_pi]
    simp
  let ρ : Representation (ZMod p) B (Fin 2 → ZMod p) :=
    (Units.coeHom (Module.End (ZMod p) (Fin 2 → ZMod p))).comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ι)
  have hρ_inj : Function.Injective ρ := by
    simp only [ρ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact Function.Injective.comp (fun _ _ h => Units.ext h)
      (Function.Injective.comp Matrix.GeneralLinearGroup.toLin.injective hι)
  by_cases hp_dvd : p ∣ Nat.card B
  · exact Or.inl (isPGroup_commutator_of_faithful_two_dim_charP hB_odd hdim ρ hρ_inj
      hp_dvd (ZMod.charP p))
  · refine Or.inr ?_
    have hchar' : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → ¬ CharP (ZMod p) q := by
      intro q hq hq_dvd hcharq
      exact hp_dvd ((CharP.eq (ZMod p) hcharq (ZMod.charP p)) ▸ hq_dvd)
    have hcomm := OddOrder.BG.Ch1.S02.odd_two_dim_abelian hB_odd hdim ρ hρ_inj hchar'
    exact fun x y => hcomm.comm x y

/-- **BG Lemma 4.17** (mmd L1706): `p` 奇素数, `R` 有限 `p`-群 with `r(R) ≤ 2`, `A` を
`R` の自己同型群の odd 位数部分群 (`φ : A →* MulAut R` faithful) とすると, `A'`
(`commutator A`) は `p`-群。

BG は `A` solvable も仮定するが, 本証明の §2 エンジンは odd のみで成立するため不要
(docstring 冒頭の section コメント参照)。下流: Thm 4.18 / BG §5 Thm 5.5(a) (rank ≤ 2 分岐) /
Cor 4.19。 -/
theorem isPGroup_commutator_of_mulAut_odd_of_pRank_le_two
    (hp_odd : Odd p) (hR : IsPGroup p R) (hrank : pRank R p ≤ 2)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hφ : Function.Injective φ) (hA_odd : Odd (Nat.card A)) :
    IsPGroup p (_root_.commutator A) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hp_odd
    norm_num at hp_odd
  -- R trivial: A embeds in the trivial `MulAut R`, so `A` and `A'` are trivial.
  rcases subsingleton_or_nontrivial R with hsub | hnontriv
  · haveI : Subsingleton (MulAut R) := ⟨fun f g => by ext r; exact Subsingleton.elim _ _⟩
    haveI : Subsingleton A := ⟨fun a b => hφ (Subsingleton.elim _ _)⟩
    intro g
    exact ⟨0, by
      rw [pow_zero, pow_one]
      exact Subtype.ext (Subsingleton.elim _ _)⟩
  -- Theorem 1.13: critical characteristic `H` with `exp H = p`, `C_{Aut R}(H)` a `p`-group.
  obtain ⟨H, hHchar, hHcommtop, hHcommcenter, hHexp, hHaut⟩ :=
    OddOrder.BG.Ch1.S01.thompson_critical_omega (p := p) hp2 hR
  haveI : H.Characteristic := hHchar
  have hH_inv : IsAInvariant φ H := IsAInvariant.of_characteristic φ
  set ψH : A →* MulAut ↥H := OddOrder.BG.Ch1.S01.restrictAction hH_inv with hψH_def
  have hH_pg : IsPGroup p ↥H := hR.to_subgroup H
  -- `C_A(H) = ker ψH` is a `p`-group (pulled back from `C_{Aut R}(H)` along the faithful `φ`).
  have hkerH_le : ψH.ker ≤ (autCentralizer H).comap φ := by
    intro a ha
    rw [Subgroup.mem_comap, mem_autCentralizer]
    intro h hh
    have := congrArg (fun e : MulAut ↥H => ((e ⟨h, hh⟩ : ↥H) : R)) ha
    simpa [hψH_def, OddOrder.BG.Ch1.S01.restrictAction_apply] using this
  have hkerH_pg : IsPGroup p ψH.ker :=
    (hHaut.comap_of_injective φ hφ).to_le hkerH_le
  -- `V = H/Φ(H)` with the induced `A`-action; `C = C_A(V)`.
  haveI : (_root_.frattini ↥H).Normal := inferInstance
  have hΦ_inv : IsAInvariant ψH (_root_.frattini ↥H) := IsAInvariant.of_characteristic ψH
  set ψV : A →* MulAut (↥H ⧸ _root_.frattini ↥H) :=
    quotientMulAutHom hΦ_inv with hψV_def
  set C : Subgroup A := ψV.ker with hC_def
  -- (i) `C` is a `p`-group.
  have hC_pg : IsPGroup p ↥C := by
    intro c
    set a : A := (c : A) with ha_def
    have ha_mem : a ∈ C := c.2
    have hn_pos : 0 < orderOf a := orderOf_pos a
    obtain ⟨k, m, hpm, hmn⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd hn_pos.ne' p hp.ne_one
    have hm_cop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
    -- the `p'`-part `a' = a ^ p ^ k` has order dividing `m`
    have ha'_pow_m : (a ^ p ^ k) ^ m = 1 := by
      rw [← pow_mul, ← hmn, pow_orderOf_eq_one]
    have ha'_order_dvd : orderOf (a ^ p ^ k) ∣ m := orderOf_dvd_of_pow_eq_one ha'_pow_m
    -- all powers of `a'` lie in `C`, hence act trivially mod `Φ(H)`
    have ha'_mem_C : a ^ p ^ k ∈ C := C.pow_mem ha_mem _
    have htriv : ∀ z : ℤ, ∀ r : ↥H,
        ∃ x ∈ _root_.frattini ↥H, ((ψH (a ^ p ^ k)) ^ z) r = r * x := by
      intro z r
      have hz_mem : (a ^ p ^ k) ^ z ∈ C := C.zpow_mem ha'_mem_C z
      have hz_ker : ψV ((a ^ p ^ k) ^ z) = 1 := hz_mem
      have hcoset : (((ψH ((a ^ p ^ k) ^ z)) r : ↥H) : ↥H ⧸ _root_.frattini ↥H) =
          (r : ↥H ⧸ _root_.frattini ↥H) := by
        rw [hψV_def] at hz_ker
        have h2 := congrArg (fun e : MulAut (↥H ⧸ _root_.frattini ↥H) =>
          e (r : ↥H ⧸ _root_.frattini ↥H)) hz_ker
        simp only [MulAut.one_apply] at h2
        exact h2
      refine ⟨r⁻¹ * (ψH ((a ^ p ^ k) ^ z)) r, QuotientGroup.eq.mp hcoset.symm, ?_⟩
      rw [← map_zpow]
      group
    -- Burnside: the `p'`-part acts trivially on `H`, so it lies in the `p`-group `ker ψH`.
    have hψ_cop : Nat.Coprime (orderOf (ψH (a ^ p ^ k))) p :=
      Nat.Coprime.coprime_dvd_left ((orderOf_map_dvd ψH _).trans ha'_order_dvd) hm_cop.symm
    have hf_one : ψH (a ^ p ^ k) = 1 :=
      OddOrder.BG.Ch1.S01.mulAut_eq_one_of_coprime_orderOf_of_frattini hH_pg _ hψ_cop htriv
    have ha'_kerH : a ^ p ^ k ∈ ψH.ker := hf_one
    -- inside the `p`-group `ker ψH`, a `p'`-order element is trivial
    obtain ⟨j, hj⟩ := hkerH_pg ⟨a ^ p ^ k, ha'_kerH⟩
    have hj' : (a ^ p ^ k) ^ p ^ j = 1 := by
      have := congrArg (Subtype.val) hj
      simpa using this
    have hdvd_pj : orderOf (a ^ p ^ k) ∣ p ^ j := orderOf_dvd_of_pow_eq_one hj'
    have ha'_one : a ^ p ^ k = 1 := by
      rw [← orderOf_eq_one_iff]
      have hcop' : Nat.Coprime (orderOf (a ^ p ^ k)) (p ^ j) :=
        Nat.Coprime.pow_right j (Nat.Coprime.coprime_dvd_left ha'_order_dvd hm_cop.symm)
      exact Nat.eq_one_of_dvd_coprimes hcop' dvd_rfl hdvd_pj
    exact ⟨k, Subtype.ext (by simpa using ha'_one)⟩
  -- `|H| ≤ p³` (Prop 4.8) and `H ≠ 1`.
  have hHexp' : ∀ x : ↥H, x ^ p = 1 := fun x => by
    rw [← hHexp]; exact Monoid.pow_exponent_eq_one x
  have hHrank : pRank ↥H p ≤ 2 :=
    le_trans (pRank_le_of_injective (f := H.subtype) H.subtype_injective) hrank
  have hHcard : Nat.card ↥H ≤ p ^ 3 :=
    card_le_prime_cube_of_pRank_le_two_of_exponent_prime hH_pg hHrank hHexp'
  haveI hH_nontriv : Nontrivial ↥H := by
    rcases subsingleton_or_nontrivial ↥H with h | h
    · exfalso
      have h1 : Monoid.exponent ↥H = 1 := Monoid.exp_eq_one_of_subsingleton
      rw [hHexp] at h1
      exact hp.one_lt.ne' h1
    · exact h
  -- `V` is elementary abelian of order `p ^ d`, `1 ≤ d ≤ 3`.
  have hV_pg : IsPGroup p (↥H ⧸ _root_.frattini ↥H) := hH_pg.to_quotient _
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hV_pg
  have hV_elem : OddOrder.GroupTheory.IsElementaryAbelian p (↥H ⧸ _root_.frattini ↥H) :=
    hH_pg.quotient_frattini_isElementaryAbelian
  have hV_dvd : Nat.card (↥H ⧸ _root_.frattini ↥H) ∣ Nat.card ↥H := by
    have := Subgroup.index_dvd_card (_root_.frattini ↥H)
    simpa [Subgroup.index] using this
  have hΦ_ne_top : _root_.frattini ↥H ≠ ⊤ := by
    obtain ⟨M, hM, _⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup ↥H)).resolve_left bot_lt_top.ne
    exact fun htop => hM.1 (le_antisymm le_top (htop ▸ frattini_le_coatom hM))
  have hV_ne_one : Nat.card (↥H ⧸ _root_.frattini ↥H) ≠ 1 := by
    intro h1
    exact hΦ_ne_top (Subgroup.index_eq_one.mp (by simpa [Subgroup.index] using h1))
  have hd_pos : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h
    · exact absurd (by simpa [h0] using hd) hV_ne_one
    · exact h
  have hd_le : d ≤ 3 := by
    have hle : p ^ d ≤ p ^ 3 :=
      le_trans (Nat.le_of_dvd Nat.card_pos (hd ▸ hV_dvd)) hHcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  -- Case split on `d = m(V)`.
  interval_cases d
  -- (iii) `|V| = p`: `Aut V` is abelian, so `A' ≤ C`.
  · haveI hVcyc : IsCyclic (↥H ⧸ _root_.frattini ↥H) :=
      isCyclic_of_prime_card (by simpa using hd)
    let e := IsCyclic.mulAutMulEquiv (↥H ⧸ _root_.frattini ↥H)
    letI : CommGroup (MulAut (↥H ⧸ _root_.frattini ↥H)) :=
      e.toMonoidHom.commGroupOfInjective e.injective
    have hA'_le : _root_.commutator A ≤ C := by
      rw [_root_.commutator, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      have : ψV ⁅g₁, g₂⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)
      exact this
    exact hC_pg.to_le hA'_le
  -- (iv) `|V| = p²`: `A/C` acts faithfully on the 2-dimensional `F_p`-space `V`.
  · have hquot_dvd : Nat.card (A ⧸ C) ∣ Nat.card A := by
      have := Subgroup.index_dvd_card C
      simpa [Subgroup.index] using this
    have hquot_odd : Odd (Nat.card (A ⧸ C)) := by
      rcases Nat.even_or_odd (Nat.card (A ⧸ C)) with he | ho
      · exfalso
        have h2 : (2 : ℕ) ∣ Nat.card A := dvd_trans he.two_dvd hquot_dvd
        rw [Nat.odd_iff] at hA_odd
        omega
      · exact ho
    -- `MulAut V ≃* GL (Fin 2) (ZMod p)` via the elementary abelian bridge
    have hfinrank := hV_elem.log_card_eq_finrank
    rw [hd, Nat.log_pow hp.one_lt] at hfinrank
    have ν := hV_elem.mulAutEquivGeneralLinearGroup
    rw [← hfinrank] at ν
    rcases isPGroup_commutator_or_comm_of_homGLTwo hquot_odd
        (ν.toMonoidHom.comp (QuotientGroup.kerLift ψV))
        (fun x y hxy => QuotientGroup.kerLift_injective ψV (ν.injective hxy))
        with hQ | hcomm
    · -- Thm 2.6(b): `(A/C)'` is a `p`-group; extend by the `p`-group `C`.
      have hker_pg : IsPGroup p ((QuotientGroup.mk' C).ker) := by
        rw [QuotientGroup.ker_mk']
        exact hC_pg
      have hcomap : IsPGroup p
          ((_root_.commutator (A ⧸ C)).comap (QuotientGroup.mk' C)) :=
        hQ.comap_of_ker_isPGroup (QuotientGroup.mk' C) hker_pg
      refine hcomap.to_le ?_
      have hmap : (_root_.commutator A).map (QuotientGroup.mk' C) =
          _root_.commutator (A ⧸ C) := by
        rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)]
      rw [← hmap]
      exact Subgroup.le_comap_map _ _
    · -- Thm 2.6(a): `A/C` is abelian, so `A' ≤ C`.
      have hA'_le : _root_.commutator A ≤ C := by
        rw [_root_.commutator, Subgroup.commutator_le]
        intro g₁ _ g₂ _
        have hmk : (QuotientGroup.mk' C) ⁅g₁, g₂⁆ = 1 := by
          rw [map_commutatorElement]
          exact commutatorElement_eq_one_iff_commute.mpr (hcomm _ _)
        exact (QuotientGroup.eq_one_iff _).mp hmk
      exact hC_pg.to_le hA'_le
  -- (ii) `|V| = p³` is impossible: `Φ(H) = 1` makes `H` elementary abelian of rank 3.
  · exfalso
    have hmul : Nat.card (_root_.frattini ↥H) * Nat.card (↥H ⧸ _root_.frattini ↥H) =
        Nat.card ↥H := by
      have := Subgroup.card_mul_index (_root_.frattini ↥H)
      simpa [Subgroup.index] using this
    have hΦ1 : Nat.card (_root_.frattini ↥H) = 1 := by
      have hle : Nat.card (_root_.frattini ↥H) * p ^ 3 ≤ 1 * p ^ 3 := by
        rw [one_mul]
        calc Nat.card (_root_.frattini ↥H) * p ^ 3
            = Nat.card (_root_.frattini ↥H) * Nat.card (↥H ⧸ _root_.frattini ↥H) := by
              rw [hd]
          _ = Nat.card ↥H := hmul
          _ ≤ p ^ 3 := hHcard
      have hle' := Nat.le_of_mul_le_mul_right hle (pow_pos hp.pos 3)
      have hpos := Nat.card_pos (α := ↥(_root_.frattini ↥H))
      omega
    have hΦbot : _root_.frattini ↥H = ⊥ := Subgroup.eq_bot_of_card_eq _ hΦ1
    have hH_elem : OddOrder.GroupTheory.IsElementaryAbelian p ↥H :=
      hH_pg.isElementaryAbelian_of_frattini_eq_bot hΦbot
    have hHcard3 : Nat.card ↥H = p ^ 3 := by
      rw [← hmul, hΦ1, one_mul, hd]
    have h3rank : 3 ≤ pRank R p := pow_le_card_of_le_pRank H hH_elem hHcard3
    omega

end Lemma417

end OddOrder.BG.Ch1.S04
