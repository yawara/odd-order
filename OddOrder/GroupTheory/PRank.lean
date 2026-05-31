/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.ElementaryAbelian
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Free

-- rc2: the `IsMulCommutative → CommMonoid/CommGroup` instances are now `scoped`.
open scoped IsMulCommutative

/-!
# p-Rank of a Group

`OddOrder.GroupTheory` shared module: BG / Isaacs FGT の `r_p(G)` (`p`-rank) の概念.

mathlib v4.30.0-rc2 の `Group.rank G` は **minimum generators 数** (`Mathlib/GroupTheory/Rank.lean`)
で BG の `r_p(G)` (= max log_p of elementary abelian p-subgroup) とは別概念. 命名衝突を
避けるため `pRank G p` を採用.

**BG §4 全節 (Blackburn rank theory)**, **BG §5 (Narrow p-Groups)** で必要.

## Main definitions

* `OddOrder.GroupTheory.pRank G p`: `G` の `p`-rank, i.e. 最大の `n` で `G` が
  位数 `p^n` の elementary abelian p-subgroup を含む.
* `OddOrder.GroupTheory.rank G`: `G` の rank `r(G) = ⨆_p pRank G p` (全素数の sup, BG `r(G)`).

## Main results (本 module で提供)

* `pRank_bddAbove`: `[Finite G]` 下で `pRank` を定義する族の値域が有界 (BddAbove).
* `pRank_le_iff`: 評価補題 `pRank G p ≤ n ↔ ∀ elem-ab A, log_p |A| ≤ n` (`[Finite G]`).
* `IsElementaryAbelian.card_eq_pow_finrank` / `IsElementaryAbelian.log_card_eq_finrank`:
  **2 形の橋** — elem-ab `A` で `|A| = p ^ m(A)` かつ `log_p |A| = m(A)`,
  ここで `m(A) = Module.finrank (ZMod p) (Additive A)` (BG の `m(A)`).
* `pRank_mono_of_le` / `pRank_le_of_injective`: subgroup / 単射像での monotonicity.
* `rank` の `pRank` 単調連動と全素数 sup の性質.

## Design notes

* `noncomputable def` (iSup based). 一般 `G` で型は通るが, `[Finite G]` 下でのみ
  意味のある値 (無限群では unbounded → mathlib `iSup` convention で 0 になりうる).
* mathlib `Group.rank` (min generators) と区別するため必ず `pRank` 命名を使用.
* BG 教科書の `m(A)` (abelian `A` の最小生成元数) は **elem-ab `A` では F_p ベクトル空間次元
  `Module.finrank (ZMod p) (Additive A)` と一致**. この橋を `IsElementaryAbelian` 側に置く.
* `Additive A` の `Module (ZMod p)` 構造は `IsMulCommutative` (= elem-ab の commutativity) から
  `CommGroup A` → `AddCommGroup (Additive A)`, そこに `AddCommGroup.zmodModule` を被せて得る.
* `FiniteField.pow_finrank_eq_natCard` で `p ^ finrank = |Additive A| = |A|`.
* 将来 mathlib upstream 視野で `OddOrder/Mathlib/PRank.lean` 候補.

## References

* BG §4 (p-Groups of Small Rank), `m(A)`, `r_q(G)`, `r(G)` の定義 (printed p.33).
* BG §4 Lem 4.7 (rank ↔ SCN_3).
* BG §5 (Narrow p-Groups), 全節.
* Gorenstein, _Finite Groups_ (1968), Definition 5.4.10 (depth).

## Audit context

Phase 2a 第 1 波 audit 2026-05-23 で新規 shared module 候補として確定.
詳細は `notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`.
性質補強 2026-05-30 (BG §4 最初の山, `notes/bg/s04_implementation_plan_2026_05_30.md` §4.1).
-/

namespace OddOrder.GroupTheory

section Bridge

/-! ## 1A: 2 形の橋 (elem-ab `log_p |A|` ↔ abelian `m(A)`) (BG §4, p.33)

BG は `m(A) =` abelian `A` の最小生成元数 と置き, p-群 `A` で `|Ω₁(A)| = p^{m(A)}` と述べる.
elementary abelian `A` では `Ω₁(A) = A` なので `|A| = p^{m(A)}`. ここで `m(A)` は `A` を
`F_p`-ベクトル空間 (`Additive A` 上の `ZMod p`-module) と見たときの次元
`Module.finrank (ZMod p) (Additive A)` に他ならない. この橋を与える. -/

variable {p : ℕ} {G : Type*} [Group G]

/-- An elementary abelian `p`-group, viewed additively, is a `ZMod p`-module:
its commutativity gives `AddCommGroup (Additive G)`, and `x ^ p = 1` becomes `p • x = 0`. -/
@[reducible] noncomputable def IsElementaryAbelian.zmodModule [NeZero p]
    (h : IsElementaryAbelian p G) :
    letI : IsMulCommutative G := IsMulCommutative.of_comm h.comm
    Module (ZMod p) (Additive G) :=
  letI : IsMulCommutative G := IsMulCommutative.of_comm h.comm
  letI : CommGroup G := inferInstance
  AddCommGroup.zmodModule (G := Additive G) (n := p) (by
    intro x
    -- `p • x = 0` in `Additive G` ⟺ `x.toMul ^ p = 1` in `G`.
    have hx : (Additive.toMul x) ^ p = 1 := h.pow_eq_one _
    have h2 : Additive.ofMul ((Additive.toMul x) ^ p) = Additive.ofMul (1 : G) := by
      rw [hx]
    rw [ofMul_pow, ofMul_one, ofMul_toMul] at h2
    exact h2)

/-- **BG `m(A)` for elementary abelian `A`** (`p` prime): the order of an elementary
abelian `p`-group equals `p ^ m(A)`, where `m(A) = finrank (ZMod p) (Additive A)`.

Since `Ω₁(A) = A` for elementary abelian `A`, this is BG's identity `|Ω₁(A)| = p^{m(A)}`. -/
theorem IsElementaryAbelian.card_eq_pow_finrank [Fact p.Prime] [Finite G]
    (h : IsElementaryAbelian p G) :
    letI : IsMulCommutative G := IsMulCommutative.of_comm h.comm
    letI := h.zmodModule
    Nat.card G = p ^ Module.finrank (ZMod p) (Additive G) := by
  letI : IsMulCommutative G := IsMulCommutative.of_comm h.comm
  letI := h.zmodModule
  have hcard : Nat.card (Additive G) = Nat.card G := Nat.card_congr Additive.toMul
  have := FiniteField.pow_finrank_eq_natCard p (Additive G)
  rw [hcard] at this
  exact this.symm

/-- **`log_p |A| = m(A)`** for elementary abelian `A` (`p` prime): the `p`-logarithm of the
order recovers the `F_p`-dimension `m(A) = finrank (ZMod p) (Additive A)`.

This is the half of the BG two-form bridge feeding `pRank`: the summand `Nat.log p |A|` in the
`pRank` `iSup` equals BG's `m(A)`. -/
theorem IsElementaryAbelian.log_card_eq_finrank [Fact p.Prime] [Finite G]
    (h : IsElementaryAbelian p G) :
    letI : IsMulCommutative G := IsMulCommutative.of_comm h.comm
    letI := h.zmodModule
    Nat.log p (Nat.card G) = Module.finrank (ZMod p) (Additive G) := by
  letI : IsMulCommutative G := IsMulCommutative.of_comm h.comm
  letI := h.zmodModule
  rw [h.card_eq_pow_finrank, Nat.log_pow (Fact.out : p.Prime).one_lt]

end Bridge

section AutGL

/-! ## 1B: `Aut(E) ≅ GL(n, F_p)` for elementary abelian `E` (BG §4, standard bridge)

BG Lem 4.13 (mmd L1624) と Thm 4.16 (mmd L1658, `|GL(2,p)| = p(p²-1)(p-1)`) は,
elementary abelian `p`-群 `E` の自己同型群が `F_p`-ベクトル空間 `Additive E` の一般線型群と
同型である事実 `Aut(E) ≅ GL(n, p)` (`n = m(E) = finrank (ZMod p) (Additive E)`) を暗黙に使う.
この橋自体は教科書外の標準事実 (BG 本文に proof なし) なので, 標準的に形式化する.

橋の核心: 群準同型 `E → E` は `Additive E` 上の加法準同型, したがって `ZMod p`-スカラー作用を
自動的に保存する (`ZMod.map_smul`) ので `ZMod p`-線型. これにより `Aut(E)` (mult.) は
`AddAut (Additive E)` (add.) を経て `(Additive E ≃ₗ[ZMod p] Additive E)`, 基底を取って
`GL(Fin n, ZMod p)` へ移る. -/

/-- The automorphism group of a `ZMod p`-module `M` (as an additive group) is multiplicatively
equivalent to the group of `ZMod p`-linear automorphisms of `M`.

Every additive automorphism of `M` is automatically `ZMod p`-linear, because an additive map
preserves the `ZMod p`-scalar action (`ZMod.map_smul`): the action `c • x` is determined by the
group structure (`c • x = (c.val) • x` as an iterated sum), which any `AddMonoidHom` respects. -/
noncomputable def AddAut.toZModLinearEquiv {p : ℕ} {M : Type*}
    [AddCommGroup M] [Module (ZMod p) M] :
    AddAut M ≃* (M ≃ₗ[ZMod p] M) where
  toFun e := { e with map_smul' := ZMod.map_smul e.toAddMonoidHom }
  invFun e := { e.toAddEquiv with }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- **`Aut(M) ≅ GL(n, F_p)` for a finite `ZMod p`-module** (`p` prime,
`n = finrank (ZMod p) M`): the additive automorphism group of a finite `F_p`-vector space `M` is
multiplicatively equivalent to the general linear group `GL(Fin n, ZMod p)`.

This is the abstract `[Module (ZMod p) M]` form. Keeping the module abstract (rather than the
`letI`-bound `zmodModule` structure on `Additive E`) is essential: with a `letI`-bound local
module instance, the `Module.Finite` / `Module.Free` / basis instance synthesis gets stuck on the
shared module argument. The `Additive E`-specific form is obtained in
`IsElementaryAbelian.mulAutEquivGeneralLinearGroup` by composing with `AddAutAdditive`. -/
noncomputable def IsElementaryAbelian.addAutEquivGL {p : ℕ} [Fact p.Prime] {M : Type*}
    [AddCommGroup M] [Module (ZMod p) M] [Finite M] :
    AddAut M ≃* GL (Fin (Module.finrank (ZMod p) M)) (ZMod p) := by
  haveI : Module.Finite (ZMod p) M := Module.Finite.of_finite
  let b : Module.Basis (Fin (Module.finrank (ZMod p) M)) (ZMod p) M :=
    Module.finBasisOfFinrankEq (ZMod p) M rfl
  exact (AddAut.toZModLinearEquiv).trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) M).symm.trans
      (Matrix.GeneralLinearGroup.toLin' b).symm)

/-- **`Aut(E) ≅ GL(m(E), F_p)`** for an elementary abelian `p`-group `E` (`p` prime), where
`m(E) = finrank (ZMod p) (Additive E)` is BG's `m(E)`.

This is the standard bridge underlying BG Lem 4.13 and Thm 4.16: viewing `E` additively as an
`F_p`-vector space, `MulAut E` is multiplicatively equivalent to the general linear group of
dimension `m(E)` over `F_p`. The multiplicativity is honest (no anti-homomorphism flip): the
`AddAutAdditive` leg is a genuine `≃*` in the direction `AddAut (Additive E) → MulAut E`. -/
noncomputable def IsElementaryAbelian.mulAutEquivGeneralLinearGroup
    {p : ℕ} {E : Type*} [Group E] [Finite E] [Fact p.Prime]
    (hE : IsElementaryAbelian p E) :
    letI : IsMulCommutative E := IsMulCommutative.of_comm hE.comm
    letI := hE.zmodModule
    MulAut E ≃* GL (Fin (Module.finrank (ZMod p) (Additive E))) (ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : IsMulCommutative E := IsMulCommutative.of_comm hE.comm
  letI := hE.zmodModule
  haveI : Finite (Additive E) := inferInstanceAs (Finite E)
  exact (AddAutAdditive (G := E)).symm.trans IsElementaryAbelian.addAutEquivGL

/-- **`|Aut(E)| = ∏ (pⁿ - pⁱ)`** for an elementary abelian `p`-group `E` (`p` prime), where
`n = m(E) = finrank (ZMod p) (Additive E)`.

This is the standard order formula underlying BG Thm 4.16: `|Aut(E)| = |GL(n, p)|`. For `n = 2`
(BG's case `|E| = p²`) the product is `(p² - 1)(p² - p) = p(p² - 1)(p - 1)`, matching BG's
`|GL(2, p)| = p(p² - 1)(p - 1)` (via `Fin.prod_univ_two`). -/
theorem IsElementaryAbelian.card_mulAut
    {p : ℕ} {E : Type*} [Group E] [Finite E] [Fact p.Prime]
    (hE : IsElementaryAbelian p E) :
    letI : IsMulCommutative E := IsMulCommutative.of_comm hE.comm
    letI := hE.zmodModule
    Nat.card (MulAut E) =
      ∏ i : Fin (Module.finrank (ZMod p) (Additive E)),
        (p ^ Module.finrank (ZMod p) (Additive E) - p ^ (i : ℕ)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : IsMulCommutative E := IsMulCommutative.of_comm hE.comm
  letI := hE.zmodModule
  rw [Nat.card_congr (hE.mulAutEquivGeneralLinearGroup).toEquiv,
      Matrix.card_GL_field, ZMod.card]

/-- A `p`-subgroup `K` of a finite group whose order is **not** divisible by `p²` has
`|K| ≤ p`. This is the abstract heart of the rank-`≤ 2` squeeze: a `p`-subgroup of
`GL(n, p)` with `n ≤ 2` has order `≤ p`, because `p² ∤ |GL(n, p)|` for `n ≤ 2`. -/
theorem card_le_prime_of_isPGroup_of_not_sq_dvd {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {K : Subgroup G} (hK : IsPGroup p K) (hnsq : ¬ p ^ 2 ∣ Nat.card G) :
    Nat.card K ≤ p := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK
  rw [hk]
  by_contra hlt
  push_neg at hlt
  have hk2 : 2 ≤ k := by
    by_contra h
    push_neg at h
    have hle : p ^ k ≤ p := by
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le (by omega)
        _ = p := pow_one p
    omega
  exact hnsq ((pow_dvd_pow p hk2).trans (hk ▸ K.card_subgroup_dvd_card))

/-- `p² ∤ ∏_{i<n}(pⁿ - pⁱ)` for `n ≤ 2` (`p` prime). This is the order of `GL(n, p)`; its
`p`-adic valuation is `n(n-1)/2 ≤ 1` when `n ≤ 2`. -/
private theorem not_sq_dvd_prod_pow_sub {p n : ℕ} (hp : p.Prime) (hn : n ≤ 2) :
    ¬ p ^ 2 ∣ ∏ i : Fin n, (p ^ n - p ^ (i : ℕ)) := by
  have h2p : 2 ≤ p := hp.two_le
  interval_cases n
  · -- n = 0: empty product = 1
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    intro h
    have hle := Nat.le_of_dvd one_pos h
    have h4 : (2 : ℕ) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h2p 2
    norm_num at h4
    omega
  · -- n = 1: product = p - 1
    simp only [Fin.prod_univ_one, Fin.val_zero, pow_zero, pow_one]
    intro h
    have hle := Nat.le_of_dvd (by omega) h
    have hps : p ≤ p ^ 2 := Nat.le_self_pow two_ne_zero p
    omega
  · -- n = 2: product = (p² - 1)(p² - p)
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have hpp : p ^ 2 - p = p * (p - 1) := by rw [Nat.mul_sub_one, pow_two]
    have hfac : (p ^ 2 - 1) * (p ^ 2 - p) = p * ((p ^ 2 - 1) * (p - 1)) := by
      rw [hpp]; ring
    intro hdvd
    rw [hfac, pow_two] at hdvd
    have hM : p ∣ (p * p - 1) * (p - 1) := (Nat.mul_dvd_mul_iff_left hp.pos).mp hdvd
    rcases hp.dvd_mul.mp hM with h1 | h2
    · -- p ∣ p*p - 1 : impossible since p ∣ p*p
      have hpsq : p ∣ p * p := dvd_mul_right p p
      have hd1 : p ∣ p * p - (p * p - 1) := Nat.dvd_sub hpsq h1
      have hX1 : 1 ≤ p * p := by nlinarith
      have : p * p - (p * p - 1) = 1 := by omega
      rw [this] at hd1
      exact hp.one_lt.ne' (Nat.dvd_one.mp hd1)
    · -- p ∣ p - 1 : impossible since 0 < p - 1 < p
      have := Nat.le_of_dvd (by omega) h2
      omega

/-- **`|p`-subgroup of `Aut(E)| ≤ p`** for an elementary abelian `E` of order `≤ p²`
(`p` prime): since `p² ∤ |Aut(E)|` when `m(E) ≤ 2`, any `p`-subgroup of `MulAut E` has
order `≤ p`. This is the rank-`≤ 2` GL squeeze, packaged for the conjugation action in
Gorenstein Theorem 4.15(i). -/
theorem card_pSubgroup_mulAut_le_prime_of_card_le_prime_sq
    {E : Type*} [Group E] [Finite E] {p : ℕ} [Fact p.Prime]
    (hE : IsElementaryAbelian p E) (hcard : Nat.card E ≤ p ^ 2)
    {K : Subgroup (MulAut E)} (hK : IsPGroup p K) :
    Nat.card K ≤ p := by
  have hp := (Fact.out : p.Prime)
  refine card_le_prime_of_isPGroup_of_not_sq_dvd hK ?_
  rw [hE.card_mulAut]
  refine not_sq_dvd_prod_pow_sub hp ?_
  have hcardE := hE.card_eq_pow_finrank
  rw [hcardE] at hcard
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard

/-- **GL number-theory kernel for BG Lemma 4.13 / Gorenstein Theorem 4.15(ii).** Let `E` be an
elementary abelian `p`-group of order `≤ p²` and `σ : MulAut E` an automorphism of prime order
`q ≠ p`. Then `q ∣ p² - 1`.

Here `Aut(E) = GL(m, p)` with `m = m(E) ≤ 2`, and `|GL(m, p)| = ∏_{i<m}(pᵐ - pⁱ)`. For `m ≤ 2`
the `p`-free part of this order divides `(p² - 1)(p - 1)`, so a prime `q ≠ p` dividing it divides
`p² - 1` (using `p - 1 ∣ p² - 1`). This is the rank-`≤ 2` half of BG's `q ∣ p² - 1` and is used
once `q` is realized as acting on the elementary abelian quotient `D / Φ(D)` of the minimal
special subgroup `D` of precursor 2. -/
theorem prime_dvd_prime_sq_sub_one_of_orderOf_mulAut {p q : ℕ} [Fact p.Prime] (hq : q.Prime)
    (hqp : q ≠ p) {E : Type*} [Group E] [Finite E] (hE : IsElementaryAbelian p E)
    (hcard : Nat.card E ≤ p ^ 2) {σ : MulAut E} (hσ : orderOf σ = q) :
    q ∣ p ^ 2 - 1 := by
  have hp := (Fact.out : p.Prime)
  letI : IsMulCommutative E := IsMulCommutative.of_comm hE.comm
  letI := hE.zmodModule
  -- `q = |σ| ∣ |MulAut E| = ∏_{i<n}(pⁿ - pⁱ)`, `n = m(E) ≤ 2`.
  set n := Module.finrank (ZMod p) (Additive E) with hn
  have hcardE : Nat.card E = p ^ n := hE.card_eq_pow_finrank
  have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcardE ▸ hcard)
  have hqdvd : q ∣ ∏ i : Fin n, (p ^ n - p ^ (i : ℕ)) := by
    rw [← hE.card_mulAut, ← hσ]; exact orderOf_dvd_natCard σ
  -- `p - 1 ∣ p² - 1`.
  have hp1dvd : p - 1 ∣ p ^ 2 - 1 := by
    rcases p with _ | b
    · simp
    · rw [Nat.succ_sub_one, show (b + 1) ^ 2 = b * (b + 2) + 1 from by ring, Nat.add_sub_cancel]
      exact dvd_mul_right b (b + 2)
  -- Split on `m(E) ∈ {0, 1, 2}`.
  interval_cases n
  · simp only [Finset.univ_eq_empty, Finset.prod_empty, Nat.dvd_one] at hqdvd
    exact absurd hqdvd hq.ne_one
  · simp only [Fin.prod_univ_one, Fin.val_zero, pow_zero, pow_one] at hqdvd
    exact hqdvd.trans hp1dvd
  · simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      show p ^ 2 - p = p * (p - 1) from by rw [Nat.mul_sub_one, pow_two]] at hqdvd
    rcases hq.dvd_mul.mp hqdvd with h1 | h2
    · exact h1
    · rcases hq.dvd_mul.mp h2 with hpp | hp1
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp hpp) hqp
      · exact hp1.trans hp1dvd

/-- **`q < p` companion** for BG Lemma 4.13 (`p` odd). If `p, q` are primes, `p` is odd,
`q ≠ p`, and `q ∣ p² - 1`, then `q < p`.

`p² - 1 = (p-1)(p+1)`; a prime `q ≠ p` dividing it divides `p-1` (giving `q ≤ p-1 < p`) or
`p+1`. For odd `p` the factor `p+1` is even and `> 2`, so it is not prime, hence `q ≠ p+1` and
`q ≤ p+1` forces `q ≤ p-1 < p`. (Pairs with `prime_dvd_prime_sq_sub_one_of_orderOf_mulAut`.) -/
theorem lt_of_prime_dvd_prime_sq_sub_one {p q : ℕ} (hp : p.Prime) (hpo : Odd p) (hq : q.Prime)
    (hqp : q ≠ p) (hdvd : q ∣ p ^ 2 - 1) : q < p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hfac : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    rcases p with _ | b
    · simp
    · rw [Nat.succ_sub_one, show (b + 1) ^ 2 = b * (b + 2) + 1 from by ring, Nat.add_sub_cancel]
  rw [hfac] at hdvd
  rcases hq.dvd_mul.mp hdvd with h1 | h2
  · exact lt_of_le_of_lt (Nat.le_of_dvd (by omega) h1) (by omega)
  · have hle : q ≤ p + 1 := Nat.le_of_dvd (by omega) h2
    have hqne1 : q ≠ p + 1 := by
      intro hq1
      have hev : Even (p + 1) := hpo.add_one
      rw [← hq1] at hev
      have : q = 2 := (Nat.Prime.even_iff hq).mp hev
      omega
    omega

end AutGL

variable (G : Type*) [Group G]

/-- **p-Rank of a group**: the maximum `n` such that `G` contains an elementary abelian
`p`-subgroup of order `p^n`.

For `G = ⊥` or no elementary abelian `p`-subgroup besides `⊥`, this is `0`.

**注**: mathlib v4.30.0-rc2 の `Group.rank G` は **minimum generators 数** で別概念.
本 def の命名 `pRank` で衝突回避. -/
noncomputable def pRank (p : ℕ) : ℕ :=
  ⨆ A : {A : Subgroup G // A.IsElementaryAbelian p}, Nat.log p (Nat.card (A.val : Subgroup G))

/-- **Rank of a group** `r(G) = ⨆_p pRank G p` (BG §4, p.33): the supremum of the `p`-ranks
over all primes `p`.

The supremum ranges over **all** natural numbers `p` (only primes contribute a nonzero
elementary abelian summand, so non-primes are harmless). -/
noncomputable def rank : ℕ :=
  ⨆ p : ℕ, pRank G p

variable {G}

section Properties

variable {p : ℕ}

/-- The trivial subgroup `⊥` is elementary abelian (every element is `1`). -/
theorem bot_isElementaryAbelian : (⊥ : Subgroup G).IsElementaryAbelian p :=
  ⟨fun x y => by
      have hx : (x : G) = 1 := Subgroup.mem_bot.mp x.2
      have hy : (y : G) = 1 := Subgroup.mem_bot.mp y.2
      apply Subtype.ext
      push_cast
      rw [hx, hy],
    fun x => by
      have hx : (x : G) = 1 := Subgroup.mem_bot.mp x.2
      apply Subtype.ext
      push_cast
      rw [hx, one_pow]⟩

/-- The index type of the `pRank` supremum is nonempty: the trivial subgroup `⊥` is
elementary abelian. -/
theorem pRank_index_nonempty :
    Nonempty {A : Subgroup G // A.IsElementaryAbelian p} :=
  ⟨⟨⊥, bot_isElementaryAbelian⟩⟩

/-- **BddAbove for `pRank`** (`[Finite G]`): every elementary abelian subgroup `A` satisfies
`log_p |A| ≤ log_p |G|`, so the family defining `pRank G p` is bounded above by `log_p |G|`.

Without finiteness the family can be unbounded and the `iSup` collapses to `0` (the `ℕ`
`sSup` convention), so this hypothesis is essential for `pRank` to be meaningful. -/
theorem pRank_bddAbove [Finite G] :
    BddAbove (Set.range fun A : {A : Subgroup G // A.IsElementaryAbelian p} =>
      Nat.log p (Nat.card (A.val : Subgroup G))) := by
  refine ⟨Nat.log p (Nat.card G), ?_⟩
  rintro _ ⟨A, rfl⟩
  exact Nat.log_mono_right (Subgroup.card_le_card_group A.val)

/-- The `pRank` summand of any elementary abelian subgroup is `≤ pRank G p` (`[Finite G]`). -/
theorem le_pRank [Finite G] (A : Subgroup G) (hA : A.IsElementaryAbelian p) :
    Nat.log p (Nat.card A) ≤ pRank G p :=
  le_ciSup pRank_bddAbove (⟨A, hA⟩ : {A : Subgroup G // A.IsElementaryAbelian p})

/-- **Evaluation lemma for `pRank`** (`[Finite G]`):
`pRank G p ≤ n ⟺ ∀ elementary abelian `A ≤ G`, `log_p |A| ≤ n`.

This is the workhorse characterisation used throughout BG §4: bounding the `p`-rank is
equivalent to bounding `log_p` of the order of every elementary abelian `p`-subgroup. -/
theorem pRank_le_iff [Finite G] {n : ℕ} :
    pRank G p ≤ n ↔ ∀ A : Subgroup G, A.IsElementaryAbelian p → Nat.log p (Nat.card A) ≤ n := by
  haveI := pRank_index_nonempty (G := G) (p := p)
  rw [pRank, ciSup_le_iff pRank_bddAbove]
  constructor
  · intro h A hA
    exact h ⟨A, hA⟩
  · intro h A
    exact h A.val A.2

/-- **`pRank` lower bound** (`[Finite G]`, `p` prime): an elementary abelian subgroup of
order `p ^ n` witnesses `n ≤ pRank G p`. This is the existence-side companion to the
evaluation lemma `pRank_le_iff`. -/
theorem pow_le_card_of_le_pRank [Finite G] [Fact p.Prime] {n : ℕ} (A : Subgroup G)
    (hA : A.IsElementaryAbelian p) (hcard : Nat.card A = p ^ n) :
    n ≤ pRank G p := by
  have := le_pRank A hA
  rwa [hcard, Nat.log_pow (Fact.out : p.Prime).one_lt] at this

/-- For an elementary abelian `p`-group, `log_p |G| ≤ pRank G p`: `G` is its own maximal
elementary abelian subgroup, so its rank is realised. Lets one bound `|G|` by a `pRank`
bound (`|G| = p^{log_p|G|} ≤ p^{pRank}`). -/
theorem IsElementaryAbelian.log_card_le_pRank [Finite G] [Fact p.Prime]
    (hG : IsElementaryAbelian p G) :
    Nat.log p (Nat.card G) ≤ pRank G p := by
  haveI : IsMulCommutative G := IsMulCommutative.of_comm hG.comm
  have htop : (⊤ : Subgroup G).IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv Subgroup.topEquiv.symm hG
  refine pow_le_card_of_le_pRank ⊤ htop ?_
  rw [Subgroup.card_top, hG.log_card_eq_finrank]
  exact hG.card_eq_pow_finrank

/-- **Monotonicity under subgroup inclusion** (`[Finite G]`): an injective homomorphism
`f : H →* G` (e.g. a subgroup inclusion) cannot increase the `p`-rank: `pRank H p ≤ pRank G p`.

Elementary abelian subgroups of `H` map injectively to elementary abelian subgroups of `G`
of the same order, so every `pRank H p` summand is realised in `G`. -/
theorem pRank_le_of_injective [Finite G] {H : Type*} [Group H] [Finite H]
    {f : H →* G} (hf : Function.Injective f) :
    pRank H p ≤ pRank G p := by
  rw [pRank_le_iff]
  intro A hA
  -- `A.map f ≤ G` is elementary abelian of the same order as `A`.
  have hmap : (A.map f).IsElementaryAbelian p := Subgroup.IsElementaryAbelian.map hf hA
  have hcard : Nat.card (A.map f) = Nat.card A :=
    Subgroup.card_map_of_injective hf
  calc
    Nat.log p (Nat.card A) = Nat.log p (Nat.card (A.map f)) := by rw [hcard]
    _ ≤ pRank G p := le_pRank (A.map f) hmap

/-- **Monotonicity under subgroup inclusion** (`[Finite G]`), subgroup form:
`pRank H p ≤ pRank G p` for `H ≤ G`, via the inclusion `H.subtype`. -/
theorem pRank_mono_of_le [Finite G] (H : Subgroup G) :
    pRank H p ≤ pRank G p :=
  pRank_le_of_injective H.subtype_injective

end Properties

section Rank

variable {p : ℕ}

/-- **Uniform `pRank` bound** (`[Finite G]`, `2 ≤ p`): `pRank G p ≤ Nat.log 2 |G|`.

Since any elementary abelian `p`-subgroup `A` has `|A| ≤ |G|` and `Nat.log p ≤ Nat.log 2`
for `p ≥ 2`, every `p`-rank is bounded by `Nat.log 2 |G|` *independently of `p`*; this is the
key bound making the all-primes supremum `rank G` well-defined (`rank_bddAbove`). -/
theorem pRank_le_log_two [Finite G] (hp : 2 ≤ p) :
    pRank G p ≤ Nat.log 2 (Nat.card G) := by
  rw [pRank_le_iff]
  intro A _
  calc
    Nat.log p (Nat.card A) ≤ Nat.log 2 (Nat.card A) :=
      Nat.log_anti_left (by norm_num) hp
    _ ≤ Nat.log 2 (Nat.card G) := Nat.log_mono_right (Subgroup.card_le_card_group A)

/-- `pRank G p = 0` for `p < 2` (i.e. `p = 0` or `p = 1`): no nontrivial elementary abelian
`p`-subgroup contributes. We bound the whole family `p ↦ pRank G p` by `Nat.log 2 |G|`. -/
theorem rank_bddAbove [Finite G] :
    BddAbove (Set.range fun p : ℕ => pRank G p) := by
  refine ⟨Nat.log 2 (Nat.card G), ?_⟩
  rintro _ ⟨p, rfl⟩
  rcases Nat.lt_or_ge p 2 with hp | hp
  · -- `p = 0` or `p = 1`: `Nat.log p _ = 0`, so each summand is `0`.
    interval_cases p
    · rw [pRank_le_iff]; intro A _; simp
    · rw [pRank_le_iff]; intro A _; simp
  · exact pRank_le_log_two hp

/-- The `p`-rank is `≤ rank G` for every prime `p` (`[Finite G]`). -/
theorem pRank_le_rank [Finite G] (p : ℕ) : pRank G p ≤ rank G :=
  le_ciSup rank_bddAbove p

/-- **Evaluation lemma for `rank`** (`[Finite G]`):
`rank G ≤ n ⟺ ∀ p, pRank G p ≤ n`. -/
theorem rank_le_iff [Finite G] {n : ℕ} :
    rank G ≤ n ↔ ∀ p : ℕ, pRank G p ≤ n := by
  rw [rank, ciSup_le_iff rank_bddAbove]

/-- **Monotonicity of `rank` under an injective homomorphism** (`[Finite G]`):
`rank H ≤ rank G` whenever `f : H →* G` is injective. -/
theorem rank_le_of_injective [Finite G] {H : Type*} [Group H] [Finite H]
    {f : H →* G} (hf : Function.Injective f) :
    rank H ≤ rank G := by
  rw [rank_le_iff]
  intro p
  exact (pRank_le_of_injective hf).trans (pRank_le_rank p)

/-- **Monotonicity of `rank` under subgroup inclusion** (`[Finite G]`). -/
theorem rank_mono_of_le [Finite G] (H : Subgroup G) :
    rank H ≤ rank G :=
  rank_le_of_injective H.subtype_injective

end Rank

end OddOrder.GroupTheory
