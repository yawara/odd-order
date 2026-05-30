/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S02_Representations
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.GroupTheory.ElementaryAbelian
import OddOrder.GroupTheory.IsMetacyclic
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
needs the `(uv)^n` triple-commutator expansion (4.4)) is deferred. -/

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
  push_neg at h
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

end ElementaryAbelianExistence

end OddOrder.BG.Ch1.S04
