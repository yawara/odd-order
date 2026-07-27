/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.Perm.Cycle.Type
import OddOrder.Isaacs.Ch08_PermutationGroups.CycleCommutators
import OddOrder.Isaacs.Ch08_PermutationGroups.Problems8A.CosetOrbits

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
- `mCycleFun`, `mCycleInv`, `mCycle`, `mCycle_apply_of_le`, `mCycle_pow_apply`,
  `exists_mem_zpowers_mCycle_smul` — **8B.9 への準備**: `ZMod n` 上の `m`-巡回
  `(0, 1, …, m-1)` (残りは固定) と, その冪が先頭区間上で推移的なこと。
- `isPreprimitive_zpowers_mCycle_sup_zpowers_addRight_one` — **8B.9 の step 1**:
  `m`-巡回と `n`-巡回が生成する群は原始的。
- `zPerm`, `zPerm_apply_of_lt` / `_of_mem` / `_top`, `zPerm_apply_eq_self_iff`,
  `mCycle_apply_eq_self_iff` — **8B.9 の step 2**: `z := y⁻¹ x` は巡回
  `(m-1, m, …, n-1)` で, `y` と `z` の共通可動点は `m-1` ただ一つ。
- `alternatingGroup_le_zpowers_mCycle_sup_zpowers_addRight_one` — **8B.9 の step 2–4**:
  `⁅y, z⁆` は 3-cycle (Isaacs Lem 8.25) なので Jordan の定理で交代群を含む。
- `support_mCycle`, `isCycle_mCycle`, `sign_mCycle`, `support_addRight_one`,
  `isCycle_addRight_one`, `sign_addRight_one`,
  `eq_top_zpowers_mCycle_sup_zpowers_addRight_one`,
  `eq_alternatingGroup_zpowers_mCycle_sup_zpowers_addRight_one` — **8B.9**:
  `m` か `n` が偶なら `S_n`, ともに奇なら `A_n`。
- `eq_stabilizer_of_index_eq_of_fixed`, `not_fixed_of_index_eq_of_ne_stabilizer` —
  **8B.10 への準備**: `S_n` の指数 `n` の部分群が点を固定すればそれは点安定化群
  そのもの (⟹ 点安定化群でなければ固定点をもたない)。
- `choose_two_le_choose`, `lt_choose_of_two_le_of_le_sub_two` — **8B.10 の counting**:
  `4 ≤ N` かつ `2 ≤ k ≤ N - 2` なら `N < C(N, k)`。
- `card_le_factorial_mul_factorial_of_invariant`,
  `isPretransitive_of_index_eq_of_ne_stabilizer` — **8B.10 の step 1**: `Sym(α)` の
  指数 `|α|` の部分群で点安定化群でないものは推移的。
- `exists_perm_apply_eq_apply_eq`, `two_transitive_of_index_eq_of_ne_stabilizer`,
  `isPreprimitive_of_index_eq_of_ne_stabilizer` — **8B.10 の step 2–3**: 同じ部分群は
  Problem 8A.16 により 2-transitive、したがって原始的。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise commutatorElement

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

lemma mCycleFun_of_le {c : ZMod n} (h : m ≤ c.val) : mCycleFun n m c = c := by
  unfold mCycleFun
  rw [if_neg (by omega), if_neg (by omega)]

lemma mCycle_apply_of_le (hm : m ≤ n) {c : ZMod n} (h : m ≤ c.val) : mCycle n m hm c = c :=
  mCycleFun_of_le h

/-- `m`-巡回の冪の作用: 先頭区間の上では `val` を `mod m` で `+k` する。 -/
lemma mCycle_pow_apply (hm : m ≤ n) (hm1 : 1 ≤ m) (k : ℕ) {c : ZMod n} (hc : c.val < m) :
    ((mCycle n m hm) ^ k) c = (((c.val + k) % m : ℕ) : ZMod n) := by
  induction k with
  | zero =>
    simp only [pow_zero, Equiv.Perm.one_apply, Nat.add_zero, Nat.mod_eq_of_lt hc]
    exact (ZMod.natCast_rightInverse c).symm
  | succ j ih =>
    have hmod : (c.val + j) % m < m := Nat.mod_lt _ (by omega)
    have hval : ((((c.val + j) % m : ℕ) : ZMod n)).val = (c.val + j) % m :=
      ZMod.val_natCast_of_lt (by omega)
    have hstep : (c.val + (j + 1)) % m = ((c.val + j) % m + 1) % m := by
      rw [Nat.mod_add_mod, Nat.add_assoc]
    rw [pow_succ', Equiv.Perm.mul_apply, ih, mCycle_apply]
    unfold mCycleFun
    rw [hval]
    by_cases h : (c.val + j) % m + 1 < m
    · rw [if_pos h, hstep, Nat.mod_eq_of_lt h]
      push_cast
      ring
    · have hm' : (c.val + j) % m + 1 = m := by omega
      rw [if_neg h, if_pos hm', hstep, hm', Nat.mod_self]
      simp

/-- 先頭区間の点は `m`-巡回の冪で `0` から到達できる。 -/
lemma exists_mCycle_pow_smul (hm : m ≤ n) (hm1 : 1 ≤ m) {d : ZMod n} (hd : d.val < m) :
    ((mCycle n m hm) ^ d.val) 0 = d := by
  have h0 : ((0 : ZMod n)).val = 0 := ZMod.val_zero
  rw [mCycle_pow_apply hm hm1 _ (by rw [h0]; omega), h0, Nat.zero_add,
    Nat.mod_eq_of_lt hd]
  exact ZMod.natCast_rightInverse d

/-- `⟨m`-巡回`⟩` は先頭区間 `S = {c | c.val < m}` 上で推移的。 -/
lemma exists_mem_zpowers_mCycle_smul (hm : m ≤ n) (hm1 : 1 ≤ m) {c d : ZMod n}
    (hc : c.val < m) (hd : d.val < m) :
    ∃ h ∈ Subgroup.zpowers (mCycle n m hm), h c = d := by
  refine ⟨(mCycle n m hm) ^ d.val * ((mCycle n m hm) ^ c.val)⁻¹, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
  · have hinv : ((mCycle n m hm) ^ c.val)⁻¹ c = 0 :=
      Equiv.Perm.inv_eq_iff_eq.mpr (exists_mCycle_pow_smul hm hm1 hc).symm
    rw [Equiv.Perm.mul_apply, hinv, exists_mCycle_pow_smul hm hm1 hd]

/-- **Isaacs Problem 8B.9 の step 1**: `m`-巡回 `(0,…,m-1)` と `n`-巡回 `(+1)` が生成する
群は **原始的** (8B.8 をそのまま適用)。 -/
theorem isPreprimitive_zpowers_mCycle_sup_zpowers_addRight_one {n m : ℕ} [NeZero n]
    (hm : 2 ≤ m) (hmn : m < n) :
    IsPreprimitive ↥(Subgroup.zpowers (mCycle n m hmn.le) ⊔
      Subgroup.zpowers (Equiv.addRight (1 : ZMod n))) (ZMod n) := by
  refine isPreprimitive_sup_zpowers_addRight_one hm hmn _ ?_ ?_
  · rintro h ⟨k, rfl⟩ c hc
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (mCycle_apply_of_le hmn.le hc) k
  · intro c hc d hd
    exact exists_mem_zpowers_mCycle_smul hmn.le (by omega) hc hd

/-! ### `z := y⁻¹ x` は巡回 `(m-1, m, …, n-1)` -/

lemma add_one_eq_zero_of_val_succ {c : ZMod n} (h : c.val + 1 = n) : c + (1 : ZMod n) = 0 := by
  have hc : c + 1 = ((c.val + 1 : ℕ) : ZMod n) := by
    push_cast
    rw [ZMod.natCast_rightInverse c]
  rw [hc, h, ZMod.natCast_self]

/-- 8B.9 の補助置換 `z := y⁻¹ x`。 -/
def zPerm (n m : ℕ) [NeZero n] (hm : m ≤ n) : Equiv.Perm (ZMod n) :=
  (mCycle n m hm)⁻¹ * Equiv.addRight (1 : ZMod n)

lemma zPerm_apply (hm : m ≤ n) (c : ZMod n) : zPerm n m hm c = mCycleInv n m (c + 1) := rfl

/-- `c.val < m - 1` の点は `z` の固定点。 -/
lemma zPerm_apply_of_lt (hm : m ≤ n) {c : ZMod n} (h : c.val + 1 < m) :
    zPerm n m hm c = c := by
  have hlt : c.val + 1 < n := by omega
  have hval : (c + 1).val = c.val + 1 := val_add_one_of_lt hlt
  have hne : c + 1 ≠ 0 := fun hc => by rw [hc, ZMod.val_zero] at hval; omega
  rw [zPerm_apply]
  unfold mCycleInv
  rw [if_neg hne, if_pos (by omega : (c + 1).val < m)]
  ring

/-- `m - 1 ≤ c.val ≤ n - 2` の点では `z` は `+1`。 -/
lemma zPerm_apply_of_mem (hm : m ≤ n) {c : ZMod n} (h1 : m ≤ c.val + 1)
    (h2 : c.val + 1 < n) : zPerm n m hm c = c + 1 := by
  have hval : (c + 1).val = c.val + 1 := val_add_one_of_lt h2
  have hne : c + 1 ≠ 0 := fun hc => by rw [hc, ZMod.val_zero] at hval; omega
  rw [zPerm_apply]
  unfold mCycleInv
  rw [if_neg hne, if_neg (by omega : ¬ (c + 1).val < m)]

/-- 最後の点 `n-1` は `m-1` に送られる。 -/
lemma zPerm_apply_top (hm : m ≤ n) {c : ZMod n} (h : c.val + 1 = n) :
    zPerm n m hm c = ((m - 1 : ℕ) : ZMod n) := by
  rw [zPerm_apply, add_one_eq_zero_of_val_succ h]
  unfold mCycleInv
  rw [if_pos rfl]

/-- `z` が動かす点はちょうど `{c | m - 1 ≤ c.val}`。 -/
lemma zPerm_apply_eq_self_iff (hm : 2 ≤ m) (hmn : m < n) {c : ZMod n} :
    zPerm n m hmn.le c = c ↔ c.val + 1 < m := by
  have hcv : c.val < n := ZMod.val_lt c
  constructor
  · intro hfix
    by_contra hcon
    rcases Nat.lt_or_ge (c.val + 1) n with h2 | h2
    · rw [zPerm_apply_of_mem hmn.le (by omega) h2] at hfix
      have := val_add_one_of_lt h2
      rw [hfix] at this
      omega
    · have hn : c.val + 1 = n := by omega
      rw [zPerm_apply_top hmn.le hn] at hfix
      have hmv : (((m - 1 : ℕ) : ZMod n)).val = m - 1 := ZMod.val_natCast_of_lt (by omega)
      rw [hfix] at hmv
      omega
  · exact zPerm_apply_of_lt hmn.le

/-- `y` が動かす点はちょうど `{c | c.val < m}`。 -/
lemma mCycle_apply_eq_self_iff (hm : 2 ≤ m) (hmn : m < n) {c : ZMod n} :
    mCycle n m hmn.le c = c ↔ m ≤ c.val := by
  have hcv : c.val < n := ZMod.val_lt c
  constructor
  · intro hfix
    by_contra hcon
    rw [mCycle_apply] at hfix
    unfold mCycleFun at hfix
    by_cases h1 : c.val + 1 < m
    · rw [if_pos h1] at hfix
      have := val_add_one_of_lt (show c.val + 1 < n by omega)
      rw [hfix] at this
      omega
    · have h2 : c.val + 1 = m := by omega
      rw [if_neg h1, if_pos h2] at hfix
      rw [← hfix, ZMod.val_zero] at h2
      omega
  · exact mCycle_apply_of_le hmn.le

/-! ### 3-cycle と Jordan の定理 -/

/-- **Isaacs Problem 8B.9 の step 2–4**: `m`-巡回と `n`-巡回が生成する群は
**交代群を含む**。

`y = m`-巡回, `z = y⁻¹ x` とすると `y` の可動点は `{c | c.val < m}`,
`z` の可動点は `{c | m - 1 ≤ c.val}` なので **共通可動点は `m-1` ただ一つ**。
Isaacs Lem 8.25 (`isThreeCycle_commutator_of_unique_common_moved`) で `⁅y, z⁆` は
3-cycle になり, 原始性 (step 1) と合わせて Jordan の定理が使える。 -/
theorem alternatingGroup_le_zpowers_mCycle_sup_zpowers_addRight_one {n m : ℕ} [NeZero n]
    (hm : 2 ≤ m) (hmn : m < n) :
    alternatingGroup (ZMod n) ≤ Subgroup.zpowers (mCycle n m hmn.le) ⊔
      Subgroup.zpowers (Equiv.addRight (1 : ZMod n)) := by
  classical
  have hav : (((m - 1 : ℕ) : ZMod n)).val = m - 1 := ZMod.val_natCast_of_lt (by omega)
  have hya : mCycle n m hmn.le ((m - 1 : ℕ) : ZMod n) ≠ ((m - 1 : ℕ) : ZMod n) := by
    rw [Ne, mCycle_apply_eq_self_iff hm hmn, hav]
    omega
  have hza : zPerm n m hmn.le ((m - 1 : ℕ) : ZMod n) ≠ ((m - 1 : ℕ) : ZMod n) := by
    rw [Ne, zPerm_apply_eq_self_iff hm hmn, hav]
    omega
  have huniq : ∀ b : ZMod n, b ≠ ((m - 1 : ℕ) : ZMod n) →
      mCycle n m hmn.le b = b ∨ zPerm n m hmn.le b = b := by
    intro b hb
    rcases Nat.lt_or_ge (b.val + 1) m with h | h
    · exact Or.inr (zPerm_apply_of_lt hmn.le h)
    · rcases Nat.lt_or_ge b.val m with h2 | h2
      · exact absurd (by rw [show m - 1 = b.val by omega, ZMod.natCast_rightInverse b]) hb
      · exact Or.inl (mCycle_apply_of_le hmn.le h2)
  have h3 : (⁅mCycle n m hmn.le, zPerm n m hmn.le⁆ : Equiv.Perm (ZMod n)).IsThreeCycle :=
    isThreeCycle_commutator_of_unique_common_moved hya hza huniq
  have hyG : mCycle n m hmn.le ∈ Subgroup.zpowers (mCycle n m hmn.le) ⊔
      Subgroup.zpowers (Equiv.addRight (1 : ZMod n)) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hxG : Equiv.addRight (1 : ZMod n) ∈ Subgroup.zpowers (mCycle n m hmn.le) ⊔
      Subgroup.zpowers (Equiv.addRight (1 : ZMod n)) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hzG : zPerm n m hmn.le ∈ Subgroup.zpowers (mCycle n m hmn.le) ⊔
      Subgroup.zpowers (Equiv.addRight (1 : ZMod n)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hyG) hxG
  refine Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (isPreprimitive_zpowers_mCycle_sup_zpowers_addRight_one hm hmn) h3 ?_
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyG hzG)
    (Subgroup.inv_mem _ hyG)) (Subgroup.inv_mem _ hzG)

/-! ### 符号による `S_n` / `A_n` の判定 -/

lemma card_filter_val_lt (hmn : m < n) :
    (Finset.univ.filter (fun c : ZMod n => c.val < m)).card = m := by
  have himg : Finset.univ.filter (fun c : ZMod n => c.val < m)
      = (Finset.range m).image (fun i : ℕ => (i : ZMod n)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_range]
    constructor
    · exact fun h => ⟨c.val, h, ZMod.natCast_rightInverse c⟩
    · rintro ⟨i, hi, rfl⟩
      rw [ZMod.val_natCast_of_lt (by omega)]
      exact hi
  rw [himg, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have h := congrArg ZMod.val hab
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h

lemma support_mCycle (hm : 2 ≤ m) (hmn : m < n) :
    (mCycle n m hmn.le).support = Finset.univ.filter (fun c : ZMod n => c.val < m) := by
  ext c
  rw [Equiv.Perm.mem_support, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Ne, mCycle_apply_eq_self_iff hm hmn]
  omega

lemma isCycle_mCycle (hm : 2 ≤ m) (hmn : m < n) : (mCycle n m hmn.le).IsCycle := by
  refine ⟨0, ?_, fun y hy => ?_⟩
  · rw [Ne, mCycle_apply_eq_self_iff hm hmn, ZMod.val_zero]
    omega
  · rw [Ne, mCycle_apply_eq_self_iff hm hmn] at hy
    refine ⟨(y.val : ℤ), ?_⟩
    rw [zpow_natCast]
    exact exists_mCycle_pow_smul (d := y) hmn.le (by omega) (by omega)

lemma sign_mCycle (hm : 2 ≤ m) (hmn : m < n) :
    Equiv.Perm.sign (mCycle n m hmn.le) = -(-1 : ℤˣ) ^ m := by
  rw [(isCycle_mCycle hm hmn).sign, support_mCycle hm hmn, card_filter_val_lt hmn]
  rfl

lemma support_addRight_one (hn : 2 ≤ n) :
    (Equiv.addRight (1 : ZMod n)).support = Finset.univ := by
  ext c
  simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true, Ne,
    Equiv.coe_addRight]
  intro hc
  have : (1 : ZMod n) = 0 := by
    have := congrArg (fun z => z - c) hc
    simpa using this
  have h1 : ((1 : ZMod n)).val = 1 := by
    haveI : Fact (1 < n) := ⟨by omega⟩
    exact ZMod.val_one n
  rw [this, ZMod.val_zero] at h1
  omega

lemma isCycle_addRight_one (hn : 2 ≤ n) : (Equiv.addRight (1 : ZMod n)).IsCycle := by
  refine ⟨0, ?_, fun y _ => ⟨(y.val : ℤ), ?_⟩⟩
  · simp only [Ne, Equiv.coe_addRight, zero_add]
    intro hc
    have h1 : ((1 : ZMod n)).val = 1 := by
      haveI : Fact (1 < n) := ⟨by omega⟩
      exact ZMod.val_one n
    rw [hc, ZMod.val_zero] at h1
    omega
  · rw [zpow_natCast, addRight_one_pow_apply, zero_add]
    exact ZMod.natCast_rightInverse y

lemma sign_addRight_one (hn : 2 ≤ n) :
    Equiv.Perm.sign (Equiv.addRight (1 : ZMod n)) = -(-1 : ℤˣ) ^ n := by
  rw [(isCycle_addRight_one hn).sign, support_addRight_one hn, Finset.card_univ,
    ZMod.card n]
  rfl

/-- 交代群を含み奇置換をもつ部分群は `S_n` 全体。 -/
lemma eq_top_of_alternatingGroup_le_of_sign_ne_one {α : Type*} [DecidableEq α] [Fintype α]
    {K : Subgroup (Equiv.Perm α)} (hA : alternatingGroup α ≤ K) {g : Equiv.Perm α}
    (hg : g ∈ K) (hsg : Equiv.Perm.sign g ≠ 1) : K = ⊤ := by
  refine eq_top_iff.mpr fun h _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign h) with hh | hh
  · exact hA (Equiv.Perm.mem_alternatingGroup.mpr hh)
  · have hsg' : Equiv.Perm.sign g = -1 :=
      (Int.units_eq_one_or (Equiv.Perm.sign g)).resolve_left hsg
    have : g⁻¹ * h ∈ K := hA (Equiv.Perm.mem_alternatingGroup.mpr (by
      rw [map_mul, map_inv, hsg', hh]
      decide))
    simpa using Subgroup.mul_mem _ hg this

/-- **Isaacs Problem 8B.9** (p. 249) 🎉 前半: `m` か `n` が**偶**なら
`⟨m`-巡回, `n`-巡回`⟩` は対称群全体。 -/
theorem eq_top_zpowers_mCycle_sup_zpowers_addRight_one {n m : ℕ} [NeZero n]
    (hm : 2 ≤ m) (hmn : m < n) (heven : Even m ∨ Even n) :
    Subgroup.zpowers (mCycle n m hmn.le) ⊔
      Subgroup.zpowers (Equiv.addRight (1 : ZMod n)) = ⊤ := by
  have hA := alternatingGroup_le_zpowers_mCycle_sup_zpowers_addRight_one hm hmn
  rcases heven with he | he
  · refine eq_top_of_alternatingGroup_le_of_sign_ne_one hA
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) ?_
    have h1 : ((-1 : ℤˣ)) ^ m = 1 := he.neg_one_pow
    rw [sign_mCycle hm hmn, h1]
    decide
  · refine eq_top_of_alternatingGroup_le_of_sign_ne_one hA
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) ?_
    have h1 : ((-1 : ℤˣ)) ^ n = 1 := he.neg_one_pow
    rw [sign_addRight_one (by omega), h1]
    decide

/-- **Isaacs Problem 8B.9** (p. 249) 🎉 後半: `m`, `n` がともに**奇**なら
`⟨m`-巡回, `n`-巡回`⟩` は交代群。 -/
theorem eq_alternatingGroup_zpowers_mCycle_sup_zpowers_addRight_one {n m : ℕ} [NeZero n]
    (hm : 2 ≤ m) (hmn : m < n) (hmo : Odd m) (hno : Odd n) :
    Subgroup.zpowers (mCycle n m hmn.le) ⊔
      Subgroup.zpowers (Equiv.addRight (1 : ZMod n)) = alternatingGroup (ZMod n) := by
  refine le_antisymm (sup_le ?_ ?_)
    (alternatingGroup_le_zpowers_mCycle_sup_zpowers_addRight_one hm hmn)
  · refine Subgroup.zpowers_le.mpr (Equiv.Perm.mem_alternatingGroup.mpr ?_)
    have h1 : ((-1 : ℤˣ)) ^ m = -1 := hmo.neg_one_pow
    rw [sign_mCycle hm hmn, h1]
    decide
  · refine Subgroup.zpowers_le.mpr (Equiv.Perm.mem_alternatingGroup.mpr ?_)
    have h1 : ((-1 : ℤˣ)) ^ n = -1 := hno.neg_one_pow
    rw [sign_addRight_one (by omega), h1]
    decide

end MCycle

/-! ### Problem 8B.10 への準備 — 指数 `n` の部分群 -/

section IndexN

variable {α : Type*} [Finite α]

/-- `S_n` の指数 `n` の部分群が点 `a` を固定すれば, それは `a` の点安定化群そのもの。

`H ≤ G_a` かつ `[S_n : G_a] = n = [S_n : H]` なので相対指数が `1` になる。 -/
lemma eq_stabilizer_of_index_eq_of_fixed {H : Subgroup (Equiv.Perm α)}
    (hidx : H.index = Nat.card α) {a : α} (hfix : ∀ h ∈ H, h a = a) :
    H = MulAction.stabilizer (Equiv.Perm α) a := by
  have hle : H ≤ MulAction.stabilizer (Equiv.Perm α) a := fun h hh =>
    MulAction.mem_stabilizer_iff.mpr (hfix h hh)
  have hstab : (MulAction.stabilizer (Equiv.Perm α) a).index = Nat.card α :=
    MulAction.index_stabilizer_of_transitive _ a
  have hmul := Subgroup.relIndex_mul_index hle
  rw [hstab, hidx] at hmul
  haveI : Nonempty α := ⟨a⟩
  have hpos : 0 < Nat.card α := Nat.card_pos
  have hrel : H.relIndex (MulAction.stabilizer (Equiv.Perm α) a) = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [hmul, one_mul])
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hrel)

/-- `S_n` の指数 `n` の部分群が点安定化群でなければ, **固定点をもたない**
(したがってすべての軌道は 2 点以上)。 -/
lemma not_fixed_of_index_eq_of_ne_stabilizer {H : Subgroup (Equiv.Perm α)}
    (hidx : H.index = Nat.card α)
    (hns : ∀ a : α, H ≠ MulAction.stabilizer (Equiv.Perm α) a) (a : α) :
    ∃ h ∈ H, h a ≠ a := by
  by_contra hcon
  push Not at hcon
  exact hns a (eq_stabilizer_of_index_eq_of_fixed hidx hcon)

/-! ### 二項係数の不等式 (8B.10 の counting) -/

/-- 二項係数は中央まで単調: `2 ≤ k ≤ n / 2` なら `C(n, 2) ≤ C(n, k)`。 -/
lemma choose_two_le_choose {N : ℕ} : ∀ k : ℕ, 2 ≤ k → k ≤ N / 2 →
    N.choose 2 ≤ N.choose k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ j ih =>
    intro h2 hk
    rcases Nat.lt_or_ge j 2 with hj | hj
    · rw [show j + 1 = 2 by omega]
    · exact (ih hj (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- `N ≥ 4` かつ `2 ≤ k ≤ N - 2` なら **`N < C(N, k)`**。

対称性 `C(N,k) = C(N,N-k)` で `k ≤ N/2` に帰着し, 単調性で `C(N,2) ≤ C(N,k)`。
`C(N,2) = N(N-1)/2 > N` は `N ≥ 4` から。 -/
lemma lt_choose_of_two_le_of_le_sub_two {N k : ℕ} (h2 : 2 ≤ k) (hk : k ≤ N - 2)
    (hN : 4 ≤ N) : N < N.choose k := by
  have hchoose2 : N < N.choose 2 := by
    rw [Nat.choose_two_right]
    have h1 : N * (N - 1) = N * 2 + N * (N - 3) := by
      rw [show N - 1 = 2 + (N - 3) by omega, Nat.mul_add]
    have h3 : 2 ≤ N * (N - 3) := by
      calc 2 ≤ 4 * 1 := by omega
        _ ≤ N * (N - 3) := Nat.mul_le_mul (by omega) (by omega)
    omega
  rcases Nat.lt_or_ge k (N / 2 + 1) with h | h
  · exact hchoose2.trans_le (choose_two_le_choose k h2 (by omega))
  · rw [← Nat.choose_symm (by omega)]
    exact hchoose2.trans_le (choose_two_le_choose (N - k) (by omega) (by omega))

/-- `H ≤ Sym(α)` が集合 `S` を保つなら `|H| ≤ |S|! · |Sᶜ|!`
(`h ↦ (h|_S, h|_{Sᶜ})` が単射)。 -/
lemma card_le_factorial_mul_factorial_of_invariant {H : Subgroup (Equiv.Perm α)} {S : Set α}
    (hinv : ∀ h ∈ H, ∀ x : α, x ∈ S ↔ (h : Equiv.Perm α) x ∈ S) :
    Nat.card ↥H ≤ (Nat.card ↥S).factorial * (Nat.card ↥(Sᶜ)).factorial := by
  classical
  have hcompl : ∀ h ∈ H, ∀ x : α, x ∈ Sᶜ ↔ (h : Equiv.Perm α) x ∈ Sᶜ := by
    intro h hh x
    simp only [Set.mem_compl_iff, not_iff_not]
    exact hinv h hh x
  have hinj : Function.Injective (fun h : ↥H =>
      (((h : Equiv.Perm α).subtypePerm (fun x => (hinv (h : Equiv.Perm α) h.2 x).symm),
        (h : Equiv.Perm α).subtypePerm (fun x => (hcompl (h : Equiv.Perm α) h.2 x).symm)) :
          Equiv.Perm ↥S × Equiv.Perm ↥(Sᶜ))) := by
    intro h₁ h₂ heq
    refine Subtype.ext (Equiv.ext fun x => ?_)
    by_cases hx : x ∈ S
    · have h := congrArg (fun p : Equiv.Perm ↥S × Equiv.Perm ↥(Sᶜ) =>
        ((p.1 ⟨x, hx⟩ : ↥S) : α)) heq
      simpa using h
    · have h := congrArg (fun p : Equiv.Perm ↥S × Equiv.Perm ↥(Sᶜ) =>
        ((p.2 ⟨x, hx⟩ : ↥(Sᶜ)) : α)) heq
      simpa using h
  calc Nat.card ↥H ≤ Nat.card (Equiv.Perm ↥S × Equiv.Perm ↥(Sᶜ)) :=
        Nat.card_le_card_of_injective _ hinj
    _ = (Nat.card ↥S).factorial * (Nat.card ↥(Sᶜ)).factorial := by
        rw [Nat.card_prod, Nat.card_perm, Nat.card_perm]

/-- **Isaacs Problem 8B.10 の step 1**: `Sym(α)` の指数 `|α|` の部分群で点安定化群で
ないものは `α` に**推移的**。

非推移なら軌道 `S` は `H`-不変な真部分集合で, 固定点をもたないことから `S` も `Sᶜ` も
2 点以上。すると `|H| ≤ |S|!·|Sᶜ|!` と `|H|·n = n!` から `C(n,|S|) ≤ n` となり,
`lt_choose_of_two_le_of_le_sub_two` に矛盾。 -/
theorem isPretransitive_of_index_eq_of_ne_stabilizer {H : Subgroup (Equiv.Perm α)}
    (hidx : H.index = Nat.card α)
    (hns : ∀ a : α, H ≠ MulAction.stabilizer (Equiv.Perm α) a) :
    MulAction.IsPretransitive ↥H α := by
  classical
  by_contra hcon
  have hnot : ¬ (∀ a b : α, ∃ h : ↥H, h • a = b) := fun h => hcon ⟨fun a b => h a b⟩
  push Not at hnot
  obtain ⟨a, b, hab⟩ := hnot
  set S : Set α := MulAction.orbit ↥H a with hS
  have hbS : b ∉ S := fun ⟨h, hh⟩ => hab h hh
  have haS : a ∈ S := MulAction.mem_orbit_self a
  have hinv : ∀ h ∈ H, ∀ x : α, x ∈ S ↔ (h : Equiv.Perm α) x ∈ S := by
    intro h hh x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨h, hh⟩ * k, mul_smul _ _ _⟩
    · rintro ⟨k, hk⟩
      refine ⟨(⟨h, hh⟩ : ↥H)⁻¹ * k, ?_⟩
      change ((⟨h, hh⟩ : ↥H)⁻¹ * k) • a = x
      rw [mul_smul, show (k : ↥H) • a = (⟨h, hh⟩ : ↥H) • x from hk,
        inv_smul_smul]
  -- `S`, `Sᶜ` はともに 2 点以上。
  have htwo : ∀ (T : Set α), (∀ h ∈ H, ∀ x : α, x ∈ T ↔ (h : Equiv.Perm α) x ∈ T) →
      ∀ c ∈ T, 2 ≤ T.ncard := by
    intro T hT c hc
    obtain ⟨h, hh, hne⟩ := not_fixed_of_index_eq_of_ne_stabilizer hidx hns c
    have hsub : ({c, (h : Equiv.Perm α) c} : Set α) ⊆ T := by
      rintro z (rfl | hz)
      · exact hc
      · rw [Set.mem_singleton_iff] at hz
        exact hz ▸ (hT h hh c).mp hc
    calc 2 = ({c, (h : Equiv.Perm α) c} : Set α).ncard := (Set.ncard_pair (Ne.symm hne)).symm
      _ ≤ T.ncard := Set.ncard_le_ncard hsub (Set.toFinite T)
  have hScard : 2 ≤ S.ncard := htwo S hinv a haS
  have hCcard : 2 ≤ (Sᶜ : Set α).ncard := by
    refine htwo Sᶜ (fun h hh x => ?_) b hbS
    simp only [Set.mem_compl_iff, not_iff_not]
    exact hinv h hh x
  have hsum : S.ncard + (Sᶜ : Set α).ncard = Nat.card α := Set.ncard_add_ncard_compl S
  have hn4 : 4 ≤ Nat.card α := by omega
  -- 位数評価
  have hSc : Nat.card ↥S = S.ncard := Nat.card_coe_set_eq S
  have hCc : Nat.card ↥(Sᶜ : Set α) = (Sᶜ : Set α).ncard := Nat.card_coe_set_eq _
  have hbound : Nat.card ↥H ≤ (S.ncard).factorial * ((Sᶜ : Set α).ncard).factorial := by
    rw [← hSc, ← hCc]
    exact card_le_factorial_mul_factorial_of_invariant hinv
  have hHcard : Nat.card ↥H * Nat.card α = (Nat.card α).factorial := by
    have h1 : Nat.card ↥H * H.index = Nat.card (Equiv.Perm α) := Subgroup.card_mul_index H
    rw [hidx, Nat.card_perm] at h1
    exact h1
  have hchoose : (Nat.card α).choose S.ncard * ((S.ncard).factorial *
      ((Nat.card α - S.ncard)).factorial) = (Nat.card α).factorial := by
    rw [← mul_assoc]
    exact Nat.choose_mul_factorial_mul_factorial (by omega)
  have hcompl_eq : (Sᶜ : Set α).ncard = Nat.card α - S.ncard := by omega
  rw [hcompl_eq] at hbound
  have hpos : 0 < (S.ncard).factorial * ((Nat.card α - S.ncard)).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hle : (Nat.card α).choose S.ncard ≤ Nat.card α := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc (Nat.card α).choose S.ncard *
          ((S.ncard).factorial * ((Nat.card α - S.ncard)).factorial)
        = Nat.card ↥H * Nat.card α := by rw [hchoose, ← hHcard]
      _ ≤ ((S.ncard).factorial * ((Nat.card α - S.ncard)).factorial) * Nat.card α :=
          Nat.mul_le_mul_right _ hbound
      _ = Nat.card α * ((S.ncard).factorial * ((Nat.card α - S.ncard)).factorial) := by ring
  exact absurd hle (Nat.not_le.mpr
    (lt_choose_of_two_le_of_le_sub_two hScard (by omega) hn4))

omit [Finite α] in
/-- `Sym(α)` は 2-transitive (相異なる 2 点の組を相異なる 2 点の組に移す)。 -/
lemma exists_perm_apply_eq_apply_eq {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : Equiv.Perm α, g a = c ∧ g b = d := by
  classical
  have hσa : (Equiv.swap a c) a = c := Equiv.swap_apply_left a c
  have hσb : (Equiv.swap a c) b ≠ c := fun h =>
    hab (((Equiv.swap a c).injective (h.trans hσa.symm)).symm)
  refine ⟨Equiv.swap ((Equiv.swap a c) b) d * Equiv.swap a c, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hσa,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hσb) hcd]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

/-- **Isaacs Problem 8B.10 の step 2**: 指数 `|α|` の非点安定化群は **2-transitive**
(教科書 Hint どおり Problem 8A.16 を適用)。 -/
theorem two_transitive_of_index_eq_of_ne_stabilizer {H : Subgroup (Equiv.Perm α)}
    (hidx : H.index = Nat.card α)
    (hns : ∀ a : α, H ≠ MulAction.stabilizer (Equiv.Perm α) a) :
    ∀ a b c d : α, a ≠ b → c ≠ d → ∃ h : ↥H, h • a = c ∧ h • b = d := by
  haveI := isPretransitive_of_index_eq_of_ne_stabilizer hidx hns
  refine two_transitive_of_coprime_index
    (fun a b c d hab hcd => exists_perm_apply_eq_apply_eq hab hcd) ?_
  rw [hidx]
  have h1 : 1 ≤ Nat.card α := by
    by_contra hc
    have : Nat.card α = 0 := by omega
    rw [this] at hidx
    exact absurd hidx H.index_ne_zero_of_finite
  rcases Nat.exists_eq_add_of_le h1 with ⟨k, hk⟩
  rw [hk]
  simp

/-- **Isaacs Problem 8B.10 の step 3**: 指数 `|α|` の非点安定化群は**原始的**
(2-transitive から)。 -/
theorem isPreprimitive_of_index_eq_of_ne_stabilizer {H : Subgroup (Equiv.Perm α)}
    (hidx : H.index = Nat.card α)
    (hns : ∀ a : α, H ≠ MulAction.stabilizer (Equiv.Perm α) a) :
    MulAction.IsPreprimitive ↥H α := by
  haveI := isPretransitive_of_index_eq_of_ne_stabilizer hidx hns
  haveI : MulAction.IsMultiplyPretransitive ↥H α 2 :=
    MulAction.is_two_pretransitive_iff.mpr
      (fun {a b c d} hab hcd =>
        two_transitive_of_index_eq_of_ne_stabilizer hidx hns a b c d hab hcd)
  exact MulAction.isPreprimitive_of_is_two_pretransitive inferInstance

end IndexN

end

end OddOrder.Isaacs.Ch08
