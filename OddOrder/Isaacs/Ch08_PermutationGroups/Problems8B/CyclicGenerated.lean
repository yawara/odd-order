/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Isaacs Problems 8B (pp. 248–249) — `n`-巡回が生成する原始群

**Problem 8B.8**。`ZMod n` 上の `n`-巡回 `x = (+1)` と, 先頭区間 `S` 上推移的で `S` の
外を各点固定する部分群 `H` が生成する群は原始的。

## Main results

- `subset_of_isBlock_of_mem_of_notMem` — block が `S` の内外の点を同時に含めば
  `S` を丸ごと含む。
- `isBlock_smul_set` — block の translate は block。
- `exists_not_mem_iff_add_mem` — `ZMod n` の先頭区間は非自明な平行移動で不変にならない。
- `addRight_one_pow_apply`, `isPreprimitive_sup_zpowers_addRight_one` — **8B.8**。
- `mCycleFun`, `mCycleInv`, `mCycle`, `val_add_one_of_lt`, `val_sub_one_of_ne_zero` —
  **8B.9 への準備**: `ZMod n` 上の `m`-巡回 `(0, 1, …, m-1)` (残りは固定)。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

section /- Problems 8B (pp. 248-249) -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-! ### Problem 8B.8 — `n`-巡回と部分推移群が生成する群は原始的 -/

/-- **8B.8 の Hint 後半**: block `Λ` が `S` の点と `S` 外の点を同時に含み, `H ≤ G` が
`S` の外を各点固定して `S` 上に推移的なら, **`S ⊆ Λ`**。

`S` の外を固定する元 `g` で `S` 上推移的に動かせるとき, `g` は `Λ` の外側の点 `j` を
固定するので `g • Λ` は `Λ` と交わり, block ゆえ `g • Λ = Λ`。したがって `Λ` はそれらの
元で不変で, `S` 上の推移性から `S ⊆ Λ`。 -/
lemma subset_of_isBlock_of_mem_of_notMem {Λ S : Set Ω} (hΛ : IsBlock G Λ)
    (htrans : ∀ γ ∈ S, ∀ δ ∈ S, ∃ g : G, g • γ = δ ∧ ∀ ε ∉ S, g • ε = ε)
    {i j : Ω} (hi : i ∈ S) (hiΛ : i ∈ Λ) (hj : j ∉ S) (hjΛ : j ∈ Λ) : S ⊆ Λ := by
  intro δ hδ
  obtain ⟨g, hgi, hgfix⟩ := htrans i hi δ hδ
  have hsm : g • Λ = Λ := hΛ.smul_eq_of_mem hjΛ (by rw [hgfix j hj]; exact hjΛ)
  rw [← hgi, ← hsm]
  exact Set.smul_mem_smul_set hiΛ

/-- block の translate はふたたび block。 -/
lemma isBlock_smul_set {B : Set Ω} (hB : IsBlock G B) (g : G) : IsBlock G (g • B) := by
  intro g₁ g₂ h
  have hne : (g₁ * g) • B ≠ (g₂ * g) • B := by rwa [mul_smul, mul_smul]
  have := hB hne
  rwa [mul_smul, mul_smul] at this

/-- **8B.8 の Hint 前半の核**: `ZMod n` の「先頭区間」`{c | c.val < m}` (`1 ≤ m < n`) は
`0` でない平行移動 `+d` で不変にならない。

不変とすると `0` から `d.val < m`, `-1 ∉ S` から `(d-1).val ≥ m` が出るが,
`d ≠ 0` なので `(d-1).val = d.val - 1 < m` で矛盾。 -/
lemma exists_not_mem_iff_add_mem {n m : ℕ} [NeZero n] (hm : 1 ≤ m) (hmn : m < n)
    {d : ZMod n} (hd : d ≠ 0) :
    ¬ (∀ c : ZMod n, (c.val < m ↔ (c + d).val < m)) := by
  intro hcon
  have hn1 : 1 ≤ n := NeZero.one_le
  have hdv : 1 ≤ d.val :=
    Nat.one_le_iff_ne_zero.mpr fun h => hd ((ZMod.val_eq_zero d).mp h)
  have hdlt : d.val < n := ZMod.val_lt d
  have hcast : ((d.val : ℕ) : ZMod n) = d := ZMod.natCast_rightInverse d
  -- `0 ∈ S` から `d ∈ S`。
  have hd0 : d.val < m := by
    have h0 : ((0 : ZMod n)).val < m := by rw [ZMod.val_zero]; omega
    simpa using (hcon 0).mp h0
  -- `-1 ∉ S` から `d - 1 ∉ S`。
  have hnegval : ((-1 : ZMod n)).val = n - 1 := by
    have heq : (-1 : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
      rw [Nat.cast_sub hn1, ZMod.natCast_self, Nat.cast_one, zero_sub]
    rw [heq, ZMod.val_natCast_of_lt (by omega)]
  have hneg : ¬ (((-1 : ZMod n)).val < m) := by rw [hnegval]; omega
  refine (fun h => hneg ((hcon (-1)).mpr h)) ?_
  have hval : ((-1 : ZMod n) + d) = ((d.val - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub hdv, hcast, Nat.cast_one]
    ring
  rw [hval, ZMod.val_natCast_of_lt (by omega)]
  omega

/-- `n`-巡回 `x = (+1)` の冪の作用。 -/
lemma addRight_one_pow_apply {n : ℕ} (j : ℕ) (c : ZMod n) :
    ((Equiv.addRight (1 : ZMod n)) ^ j) c = c + (j : ZMod n) := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih,
      show (Equiv.addRight (1 : ZMod n)) (c + (k : ZMod n)) = c + (k : ZMod n) + 1 from rfl]
    push_cast
    ring

/-- **Isaacs Problem 8B.8** (p. 249) 🎉: `x` を `ZMod n` の `n`-巡回 (`+1`),
`S = {c | c.val < m}` (`2 ≤ m < n`) とする。`H ≤ Sym(ZMod n)` が `S` 上推移的で
`S` の外を各点固定するなら, **`G = ⟨H, x⟩` は原始的**。

block `Δ` で `|Δ| > 1` なら `u ≠ v ∈ Δ` を取り `d := v - u ≠ 0`。`S` は `+d` で不変で
ないので (`exists_not_mem_iff_add_mem`), `Δ` の適当な translate `Λ` が `S` の内外の点を
同時に含む。すると `subset_of_isBlock_of_mem_of_notMem` から `S ⊆ Λ`, 特に `0, 1 ∈ Λ`
(`m ≥ 2`) なので `x • Λ = Λ`, したがって `Λ = ZMod n` で `Δ` も全体。 -/
theorem isPreprimitive_sup_zpowers_addRight_one {n m : ℕ} [NeZero n]
    (hm : 2 ≤ m) (hmn : m < n) (H : Subgroup (Equiv.Perm (ZMod n)))
    (hHfix : ∀ h ∈ H, ∀ c : ZMod n, m ≤ c.val → h c = c)
    (hHtrans : ∀ c : ZMod n, c.val < m → ∀ d : ZMod n, d.val < m → ∃ h ∈ H, h c = d) :
    IsPreprimitive ↥(H ⊔ Subgroup.zpowers (Equiv.addRight (1 : ZMod n))) (ZMod n) := by
  classical
  have hxG : (Equiv.addRight (1 : ZMod n)) ∈
      H ⊔ Subgroup.zpowers (Equiv.addRight (1 : ZMod n)) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  set xg : ↥(H ⊔ Subgroup.zpowers (Equiv.addRight (1 : ZMod n))) := ⟨_, hxG⟩ with hxg
  have hxpow : ∀ (j : ℕ) (c : ZMod n), (xg ^ j) • c = c + (j : ZMod n) := by
    intro j c
    have : ((xg ^ j : ↥(H ⊔ Subgroup.zpowers (Equiv.addRight (1 : ZMod n)))) :
        Equiv.Perm (ZMod n)) = (Equiv.addRight (1 : ZMod n)) ^ j := by
      rw [SubmonoidClass.coe_pow]
    change ((xg : Equiv.Perm (ZMod n)) ^ j) c = _
    rw [hxg]
    exact addRight_one_pow_apply j c
  have hcast : ∀ c : ZMod n, ((c.val : ℕ) : ZMod n) = c := ZMod.natCast_rightInverse
  haveI hpre : IsPretransitive
      ↥(H ⊔ Subgroup.zpowers (Equiv.addRight (1 : ZMod n))) (ZMod n) := by
    refine ⟨fun c d => ⟨xg ^ (d - c).val, ?_⟩⟩
    rw [hxpow, hcast]
    ring
  refine { isTrivialBlock_of_isBlock := fun {Δ} hΔ => ?_ }
  rcases Set.subsingleton_or_nontrivial Δ with hsub | ⟨u, hu, v, hv, huv⟩
  · exact Or.inl hsub
  refine Or.inr ?_
  -- `d := v - u ≠ 0` と `S` の非不変性から, 内外を跨ぐ translate を作る。
  set d : ZMod n := v - u with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  obtain ⟨c, hc⟩ : ∃ c : ZMod n, ¬ (c.val < m ↔ (c + d).val < m) := by
    by_contra hcon
    push Not at hcon
    exact exists_not_mem_iff_add_mem (by omega) hmn hd0 hcon
  set g : ↥(H ⊔ Subgroup.zpowers (Equiv.addRight (1 : ZMod n))) := xg ^ (c - u).val with hg
  set Λ : Set (ZMod n) := g • Δ with hΛdef
  have hgu : g • u = c := by rw [hg, hxpow, hcast]; ring
  have hgv : g • v = c + d := by rw [hg, hxpow, hcast, hd]; ring
  have hcΛ : c ∈ Λ := hgu ▸ Set.smul_mem_smul_set hu
  have hcdΛ : c + d ∈ Λ := hgv ▸ Set.smul_mem_smul_set hv
  have hΛblock : IsBlock _ Λ := isBlock_smul_set hΔ g
  -- `S ⊆ Λ`
  have hS : {e : ZMod n | e.val < m} ⊆ Λ := by
    have htrans : ∀ γ ∈ {e : ZMod n | e.val < m}, ∀ δ ∈ {e : ZMod n | e.val < m},
        ∃ k : ↥(H ⊔ Subgroup.zpowers (Equiv.addRight (1 : ZMod n))),
          k • γ = δ ∧ ∀ ε ∉ {e : ZMod n | e.val < m}, k • ε = ε := by
      intro γ hγ δ hδ
      obtain ⟨h, hhH, hhγ⟩ := hHtrans γ hγ δ hδ
      exact ⟨⟨h, Subgroup.mem_sup_left hhH⟩, hhγ, fun ε hε => hHfix h hhH ε (by simpa using hε)⟩
    rcases Classical.em (c.val < m) with hcm | hcm
    · exact subset_of_isBlock_of_mem_of_notMem hΛblock htrans hcm hcΛ
        (by simpa using fun hcon => hc ⟨fun _ => hcon, fun _ => hcm⟩) hcdΛ
    · exact subset_of_isBlock_of_mem_of_notMem hΛblock htrans
        (by simpa using (by tauto : (c + d).val < m)) hcdΛ (by simpa using hcm) hcΛ
  -- `0, 1 ∈ Λ` ⟹ `x • Λ = Λ` ⟹ `Λ = univ`
  have h0 : (0 : ZMod n) ∈ Λ := hS (by simp only [Set.mem_setOf_eq, ZMod.val_zero]; omega)
  have h1val : ((1 : ZMod n)).val = 1 := by
    haveI : Fact (1 < n) := ⟨by omega⟩
    exact ZMod.val_one n
  have h1 : (1 : ZMod n) ∈ Λ := hS (by simp only [Set.mem_setOf_eq, h1val]; omega)
  have hxΛ : xg • Λ = Λ := by
    refine hΛblock.smul_eq_of_mem h0 ?_
    have : xg • (0 : ZMod n) = 1 := by
      have := hxpow 1 (0 : ZMod n)
      simpa using this
    rw [this]
    exact h1
  have hΛuniv : Λ = Set.univ := by
    have hall : ∀ k : ℕ, (xg ^ k) • (0 : ZMod n) ∈ Λ := by
      intro k
      induction k with
      | zero => simpa using h0
      | succ j ih =>
        have hstep : (xg ^ (j + 1)) • (0 : ZMod n) = xg • ((xg ^ j) • (0 : ZMod n)) := by
          rw [pow_succ', mul_smul]
        rw [hstep, ← hxΛ]
        exact Set.smul_mem_smul_set ih
    refine Set.eq_univ_of_forall fun e => ?_
    have h := hall e.val
    rwa [hxpow, zero_add, hcast] at h
  -- `Δ` は `Λ` の translate
  have : Δ = Set.univ := by
    have : Δ = g⁻¹ • Λ := by rw [hΛdef, inv_smul_smul]
    rw [this, hΛuniv]
    simp
  exact this

/-! ### Problem 8B.9 への準備 — `ZMod n` 上の `m`-巡回 -/

section MCycle

variable {n m : ℕ} [NeZero n]

/-- `ZMod n` 上の `m`-巡回 `(0, 1, …, m-1)`。`c.val ≥ m` の点は固定する。 -/
def mCycleFun (n m : ℕ) [NeZero n] (c : ZMod n) : ZMod n :=
  if c.val + 1 < m then c + 1 else if c.val + 1 = m then 0 else c

/-- `mCycleFun` の逆写像。 -/
def mCycleInv (n m : ℕ) [NeZero n] (c : ZMod n) : ZMod n :=
  if c = 0 then ((m - 1 : ℕ) : ZMod n) else if c.val < m then c - 1 else c

lemma val_add_one_of_lt {c : ZMod n} (h : c.val + 1 < n) : (c + 1).val = c.val + 1 := by
  have h1 : ((1 : ℕ) : ZMod n) = 1 := Nat.cast_one
  have : c + 1 = ((c.val + 1 : ℕ) : ZMod n) := by
    push_cast
    rw [ZMod.natCast_rightInverse c]
  rw [this, ZMod.val_natCast_of_lt h]

lemma val_sub_one_of_ne_zero {c : ZMod n} (h : c ≠ 0) : (c - 1).val = c.val - 1 := by
  have hv : 1 ≤ c.val := Nat.one_le_iff_ne_zero.mpr fun hc => h ((ZMod.val_eq_zero c).mp hc)
  have hlt : c.val < n := ZMod.val_lt c
  have : c - 1 = ((c.val - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub hv, ZMod.natCast_rightInverse c, Nat.cast_one]
  rw [this, ZMod.val_natCast_of_lt (by omega)]

lemma mCycleInv_mCycleFun (hm : m ≤ n) (c : ZMod n) :
    mCycleInv n m (mCycleFun n m c) = c := by
  have hlt : c.val < n := ZMod.val_lt c
  unfold mCycleFun mCycleInv
  by_cases h1 : c.val + 1 < m
  · have hval : (c + 1).val = c.val + 1 := val_add_one_of_lt (by omega)
    have hne : c + 1 ≠ 0 := fun hc => by
      rw [hc] at hval; simp only [ZMod.val_zero] at hval; omega
    simp only [h1, if_true, hne, if_false, hval]
    ring
  · by_cases h2 : c.val + 1 = m
    · rw [if_neg h1, if_pos h2, if_pos rfl, show m - 1 = c.val by omega,
        ZMod.natCast_rightInverse c]
    · rw [if_neg h1, if_neg h2]
      by_cases h0 : c = 0
      · subst h0
        simp only [ZMod.val_zero] at h1 h2
        rw [if_pos rfl, show m = 0 by omega]
        simp
      · rw [if_neg h0, if_neg (by omega)]

lemma mCycleFun_mCycleInv (hm : m ≤ n) (c : ZMod n) :
    mCycleFun n m (mCycleInv n m c) = c := by
  have hlt : c.val < n := ZMod.val_lt c
  unfold mCycleFun mCycleInv
  by_cases h0 : c = 0
  · subst h0
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp
    · have hmv : ((m - 1 : ℕ) : ZMod n).val = m - 1 := ZMod.val_natCast_of_lt (by omega)
      rw [if_pos rfl, hmv, if_neg (by omega), if_pos (by omega)]
  · rw [if_neg h0]
    by_cases h1 : c.val < m
    · have hval : (c - 1).val = c.val - 1 := val_sub_one_of_ne_zero h0
      have hv : 1 ≤ c.val := Nat.one_le_iff_ne_zero.mpr fun hc => h0 ((ZMod.val_eq_zero c).mp hc)
      rw [if_pos h1, hval, if_pos (by omega)]
      ring
    · rw [if_neg h1, if_neg (by omega), if_neg (by omega)]

/-- `ZMod n` 上の `m`-巡回 `(0, 1, …, m-1)` (`c.val ≥ m` は固定)。 -/
def mCycle (n m : ℕ) [NeZero n] (hm : m ≤ n) : Equiv.Perm (ZMod n) where
  toFun := mCycleFun n m
  invFun := mCycleInv n m
  left_inv := mCycleInv_mCycleFun hm
  right_inv := mCycleFun_mCycleInv hm

@[simp] lemma mCycle_apply (hm : m ≤ n) (c : ZMod n) :
    mCycle n m hm c = mCycleFun n m c := rfl

@[simp] lemma mCycle_symm_apply (hm : m ≤ n) (c : ZMod n) :
    (mCycle n m hm).symm c = mCycleInv n m c := rfl

end MCycle

end

end OddOrder.Isaacs.Ch08
