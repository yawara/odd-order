/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch09_MoreSubnormality.OrderBound
import OddOrder.Isaacs.Ch09_MoreSubnormality.InnerAutomorphisms

/-!
# Isaacs Ch. 9 — §9B: Theorem 9.10 (Wielandt automorphism tower), p. 278

`Z(G) = 1` の有限群 `G` に対し automorphism tower
`G_1 = G`, `G_{i+1} = Aut(G_i)` は同型を除いて有限種しか含まない.

本ファイルはまず**型族そのもの**を構成する. 書籍が「`G` を `Inn(G)` と同一視して
`G_i ◁ G_{i+1}` の鎖を得る」と書く部分は, Lean では
「各段の `Group` instance を伴う型の再帰」を先に作らないと `MulAut (G_i)` すら書けない.

## 実装ノート — なぜ `GroupPkg` を経由するか

`autTowerType G (n+1) = MulAut (autTowerType G n)` を型だけの再帰で書こうとすると,
`MulAut X` の形成に `Group X` instance が要るため, 定義と instance が相互再帰になる.
`Type u` と `Group` を 1 つの structure に束ねて**同時に再帰**すればこれを回避できる.
(mathlib の `Bundled`/`GroupCat` と同型の手法だが, 圏の重い API を引かずに済ませる.)
-/

namespace OddOrder.Isaacs.Ch09

open Subgroup

open scoped Nat

universe u

section /- 9B: automorphism tower の型族 (Thm 9.10 の土台) -/

/-- 群を carrier と `Group` instance の組として束ねた package.

`autTowerPkg` の再帰で「型」と「その群構造」を同時に運ぶために使う
(型だけの再帰では `MulAut` が形成できない — 上の実装ノート参照). -/
structure GroupPkg : Type (u + 1) where
  /-- 台となる型. -/
  carrier : Type u
  /-- `carrier` の群構造. -/
  [group : Group carrier]

attribute [instance] GroupPkg.group

variable (G : Type u) [Group G]

/-- automorphism tower の第 `n` 段を package として構成:
`0 ↦ G`, `n+1 ↦ MulAut (第 n 段)`. -/
def autTowerPkg : ℕ → GroupPkg.{u}
  | 0 => ⟨G⟩
  | n + 1 => letI := (autTowerPkg n).group; ⟨MulAut (autTowerPkg n).carrier⟩

/-- **automorphism tower の第 `n` 段** `G_{n+1}` (書籍の添字は 1 始まり, ここは 0 始まり):
`autTowerType G 0 = G`, `autTowerType G (n+1) = Aut(autTowerType G n)`. -/
abbrev autTowerType (n : ℕ) : Type u := (autTowerPkg G n).carrier

instance instGroupAutTowerType (n : ℕ) : Group (autTowerType G n) := (autTowerPkg G n).group

variable {G}

@[simp] theorem autTowerType_zero : autTowerType G 0 = G := rfl

@[simp] theorem autTowerType_succ (n : ℕ) :
    autTowerType G (n + 1) = MulAut (autTowerType G n) := rfl

/-- 各段は有限 (`Aut` of finite is finite). -/
instance instFiniteAutTowerType [Finite G] (n : ℕ) : Finite (autTowerType G n) := by
  induction n with
  | zero => exact ‹Finite G›
  | succ n IH =>
    haveI := IH
    change Finite (MulAut (autTowerType G n))
    exact Finite.of_injective (fun f : MulAut (autTowerType G n) => f.toEquiv)
      (fun _ _ h => MulEquiv.ext (fun x => congrArg (fun e : Equiv _ _ => e x) h))

/-- 各段は中心自明 (Lemma 9.11(d) の伝播). -/
theorem center_autTowerType_eq_bot (hZ : Subgroup.center G = ⊥) (n : ℕ) :
    Subgroup.center (autTowerType G n) = ⊥ := by
  induction n with
  | zero => exact hZ
  | succ n IH => exact center_mulAut_eq_bot IH

end

section /- 9B: tower の埋め込み鎖 `G_n ↪ G_{n+1}` (書籍 p. 278 の同一視) -/

variable (G : Type u) [Group G]

/-- 各段の埋め込み `G_n ↪ G_{n+1}`: 内部自己同型 `g ↦ τ_g`.

`autTowerType G (n+1)` は**定義上** `MulAut (autTowerType G n)` なので
`MulAut.conj` がそのまま `G_n →* G_{n+1}` として使える. -/
def autTowerStep (n : ℕ) : autTowerType G n →* autTowerType G (n + 1) :=
  MulAut.conj

/-- `m` 段目から `m + k` 段目への合成埋め込み (`k` に関する再帰).

`m ≤ r` を `r = m + k` の形で扱うのは, `autTowerType G (m + (k+1))` と
`autTowerType G ((m + k) + 1)` が定義上同一で段差の付け替えが不要なため. -/
def autTowerEmb (m : ℕ) : ∀ k : ℕ, autTowerType G m →* autTowerType G (m + k)
  | 0 => MonoidHom.id _
  | k + 1 => (autTowerStep G (m + k)).comp (autTowerEmb m k)

variable {G}

@[simp] theorem autTowerEmb_zero (m : ℕ) : autTowerEmb G m 0 = MonoidHom.id _ := rfl

theorem autTowerEmb_succ (m k : ℕ) :
    autTowerEmb G m (k + 1) = (autTowerStep G (m + k)).comp (autTowerEmb G m k) := rfl

/-- 各段の埋め込みは単射 (`Z(G_n) = 1` ゆえ; Lemma 9.11). -/
theorem autTowerStep_injective (hZ : Subgroup.center G = ⊥) (n : ℕ) :
    Function.Injective (autTowerStep G n) :=
  conj_injective (center_autTowerType_eq_bot hZ n)

/-- 合成埋め込みも単射. -/
theorem autTowerEmb_injective (hZ : Subgroup.center G = ⊥) (m : ℕ) :
    ∀ k, Function.Injective (autTowerEmb G m k)
  | 0 => Function.injective_id
  | k + 1 => (autTowerStep_injective hZ (m + k)).comp (autTowerEmb_injective hZ m k)

/-- `G_n` の `G_{n+1}` での像はちょうど `Inn(G_n)`. -/
theorem range_autTowerStep (n : ℕ) : (autTowerStep G n).range = innAut (autTowerType G n) := rfl

/-- 添字が等しければ段も等しい (`m = n` に沿った同型).

`autTowerEmb` は `G_m →* G_{m+k}` の形でしか作れないが, 鎖を `G_r` の中で扱うには
`m + (r - m) = r` の付け替えが要る. 型の等式を直接 `cast` すると扱いにくいので
`MulEquiv` として持つ. -/
def autTowerCongr {m n : ℕ} (h : m = n) : autTowerType G m ≃* autTowerType G n := by
  subst h; exact MulEquiv.refl _

@[simp] theorem autTowerCongr_refl (m : ℕ) :
    autTowerCongr (G := G) (rfl : m = m) = MulEquiv.refl _ := rfl

theorem autTowerCongr_injective {m n : ℕ} (h : m = n) :
    Function.Injective (autTowerCongr (G := G) h) := (autTowerCongr h).injective

variable (G) in
/-- `m ≤ r` のときの埋め込み `G_m ↪ G_r` (`autTowerEmb` に添字の付け替えを合成). -/
def autTowerEmbLe {m r : ℕ} (h : m ≤ r) : autTowerType G m →* autTowerType G r :=
  (autTowerCongr (Nat.add_sub_cancel' h)).toMonoidHom.comp (autTowerEmb G m (r - m))

/-- `G_m ↪ G_r` は単射. -/
theorem autTowerEmbLe_injective (hZ : Subgroup.center G = ⊥) {m r : ℕ} (h : m ≤ r) :
    Function.Injective (autTowerEmbLe G h) :=
  (autTowerCongr_injective _).comp (autTowerEmb_injective hZ m (r - m))

end

section /- 9B: 単射 hom に沿った centralizer 条件の押し出し -/

/-- 正規化条件は準同型像に移る: `A ≤ N_H(B)` ⇒ `f A ≤ N_K(f B)`
(`f a · f B · f a⁻¹ = f (a B a⁻¹) = f B`). 単射性は不要. -/
theorem map_le_normalizer_map {H K : Type*} [Group H] [Group K] (f : H →* K) {A B : Subgroup H}
    (h : A ≤ Subgroup.normalizer (B : Set H)) :
    A.map f ≤ Subgroup.normalizer ((B.map f : Subgroup K) : Set K) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  have ha' := Subgroup.mem_normalizer_iff.mp (h ha)
  intro x
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨a * b * a⁻¹, (ha' b).mp hb, by simp only [map_mul, map_inv]⟩
  · rintro ⟨b, hb, hbx⟩
    refine ⟨a⁻¹ * b * a, (ha' (a⁻¹ * b * a)).mpr ?_, ?_⟩
    · rw [show a * (a⁻¹ * b * a) * a⁻¹ = b by group]; exact hb
    · simp only [map_mul, map_inv, hbx]; group

/-- 単射準同型は「`C_G(A) ⊓ B = 1`」を像に移す:
`f` 単射, `C_H(A) ⊓ B = ⊥` ⇒ `C_K(f A) ⊓ f B = ⊥`.

`x = f b` が `f A` の全元と可換 ⟺ `f (b*a) = f (a*b)` ⟺ `b*a = a*b` (単射性),
つまり `b ∈ C_H(A) ⊓ B = ⊥`. 鎖の条件 (9.12 の第 3 仮説) を段ごとに押し上げるのに使う. -/
theorem centralizer_map_inf_map_eq_bot {H K : Type*} [Group H] [Group K] {f : H →* K}
    (hf : Function.Injective f) {A B : Subgroup H}
    (h : Subgroup.centralizer (A : Set H) ⊓ B = ⊥) :
    Subgroup.centralizer ((A.map f : Subgroup K) : Set K) ⊓ B.map f = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxC, hxB⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨b, hbB, rfl⟩ := hxB
  rw [Subgroup.mem_centralizer_iff] at hxC
  have hbC : b ∈ Subgroup.centralizer (A : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hcomm := hxC (f a) ⟨a, ha, rfl⟩
    apply hf
    rw [map_mul, map_mul]
    exact hcomm
  have hb1 : b = 1 := by
    have hmem : b ∈ Subgroup.centralizer (A : Set H) ⊓ B := Subgroup.mem_inf.mpr ⟨hbC, hbB⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  rw [Subgroup.mem_bot, hb1, map_one]

end

section /- 9B: `G_{m+k}` の中の鎖 (9.12 に食わせる形) -/

variable (G : Type u) [Group G]

/-- **tower の鎖**: `chainAux G m k j` = `G_{m+j}` の `G_{m+k}` での像 (`j ≥ k` なら `⊤`).

環境を `m + k` の形に固定したまま `k` で再帰し, `j` はパラメータのまま持つのが要点.
`(autTowerEmbLe (j ≤ r)).range` として定義すると `S j ◁ S (j+1)` を出す分解に
`m + (k+1)` ↔ `(m+1) + k` の付け替えが入り, 鎖の 4 条件すべてに transport が波及する
(`Nat.add` は第 2 引数で再帰するので前者しか定義的簡約しない). この形なら
**添字の付け替えが一切出ない**.

検算: `chainAux 0 1 0 = ⊤.map (step 0) = Inn(G_0)`, `chainAux 0 1 1 = ⊤`,
`chainAux 0 2 1 = ⊤.map (step 1) = Inn(G_1)`, `chainAux 0 2 2 = ⊤`. -/
def chainAux (m : ℕ) : ∀ k : ℕ, ℕ → Subgroup (autTowerType G (m + k))
  | 0, _ => ⊤
  | k + 1, j =>
      if k + 1 ≤ j then ⊤ else (chainAux m k j).map (autTowerStep G (m + k))

variable {G}

@[simp] theorem chainAux_zero (m j : ℕ) : chainAux G m 0 j = ⊤ := rfl

theorem chainAux_succ_of_le {m k j : ℕ} (h : k + 1 ≤ j) : chainAux G m (k + 1) j = ⊤ := by
  rw [chainAux, if_pos h]

theorem chainAux_succ_of_lt {m k j : ℕ} (h : j < k + 1) :
    chainAux G m (k + 1) j = (chainAux G m k j).map (autTowerStep G (m + k)) := by
  rw [chainAux, if_neg (Nat.not_le.mpr h)]

/-- 鎖の上端は `⊤` (9.12 の `S r = ⊤`). -/
@[simp] theorem chainAux_self (m k : ℕ) : chainAux G m k k = ⊤ := by
  cases k with
  | zero => rfl
  | succ k => exact chainAux_succ_of_le le_rfl

/-- 9.12 の第 1 仮説: `S j ≤ S (j+1)` (`j < k`). -/
theorem chainAux_le_succ (m : ℕ) :
    ∀ (k j : ℕ), j < k → chainAux G m k j ≤ chainAux G m k (j + 1)
  | 0, j, hj => absurd hj (Nat.not_lt_zero j)
  | k + 1, j, hj => by
      rcases Nat.lt_or_ge (j + 1) (k + 1) with h | h
      · rw [chainAux_succ_of_lt (Nat.lt_of_succ_lt h), chainAux_succ_of_lt h]
        exact Subgroup.map_mono (chainAux_le_succ m k j (Nat.lt_of_succ_lt_succ h))
      · rw [chainAux_succ_of_le h]
        exact le_top

/-- 9.12 の第 2 仮説: `S (j+1) ≤ N(S j)` (`j < k`).

上端 (`j = k`) は `S k = Inn(G_{m+k})` が環境に normal (`innAut.normal`),
帰納段は正規化条件を像に押す (`map_le_normalizer_map`). -/
theorem chainAux_le_normalizer (m : ℕ) :
    ∀ (k j : ℕ), j < k →
      chainAux G m k (j + 1) ≤ Subgroup.normalizer ((chainAux G m k j : Subgroup _) : Set _)
  | 0, j, hj => absurd hj (Nat.not_lt_zero j)
  | k + 1, j, hj => by
      rcases Nat.lt_or_ge (j + 1) (k + 1) with h | h
      · rw [chainAux_succ_of_lt (Nat.lt_of_succ_lt h), chainAux_succ_of_lt h]
        exact map_le_normalizer_map _ (chainAux_le_normalizer m k j (Nat.lt_of_succ_lt_succ h))
      · -- `j = k`: `S (k+1) = ⊤`, `S k = ⊤.map (step (m+k)) = Inn(G_{m+k})` は normal
        have hjk : j = k := Nat.le_antisymm (Nat.lt_succ_iff.mp hj) (Nat.succ_le_succ_iff.mp h)
        subst hjk
        -- `⊤.map (step n) = (step n).range = Inn(G_n)` (`step` は全射でないので
        -- `map_top_of_surjective` ではなく `range_eq_map` を使う)
        rw [chainAux_succ_of_le h, chainAux_succ_of_lt (Nat.lt_succ_self j), chainAux_self,
          ← MonoidHom.range_eq_map, range_autTowerStep]
        exact le_of_eq (Subgroup.normalizer_eq_top_iff.mpr innAut.normal).symm

/-- 9.12 の第 3 仮説: `C(S j) ⊓ S (j+1) = ⊥` (`j < k`).

上端は Lemma 9.11(c) (`centralizer_innAut_eq_bot`) そのもの,
帰納段は `centralizer_map_inf_map_eq_bot` (単射 hom で押す). -/
theorem chainAux_centralizer_inf (hZ : Subgroup.center G = ⊥) (m : ℕ) :
    ∀ (k j : ℕ), j < k →
      Subgroup.centralizer ((chainAux G m k j : Subgroup _) : Set _) ⊓ chainAux G m k (j + 1) = ⊥
  | 0, j, hj => absurd hj (Nat.not_lt_zero j)
  | k + 1, j, hj => by
      rcases Nat.lt_or_ge (j + 1) (k + 1) with h | h
      · rw [chainAux_succ_of_lt (Nat.lt_of_succ_lt h), chainAux_succ_of_lt h]
        exact centralizer_map_inf_map_eq_bot (autTowerStep_injective hZ (m + k))
          (chainAux_centralizer_inf hZ m k j (Nat.lt_of_succ_lt_succ h))
      · have hjk : j = k := Nat.le_antisymm (Nat.lt_succ_iff.mp hj) (Nat.succ_le_succ_iff.mp h)
        subst hjk
        rw [chainAux_succ_of_le h, chainAux_succ_of_lt (Nat.lt_succ_self j), chainAux_self,
          ← MonoidHom.range_eq_map, range_autTowerStep, inf_top_eq]
        exact centralizer_innAut_eq_bot (center_autTowerType_eq_bot hZ (m + j))

/-- 鎖の底は `G_m` の像そのもの. -/
theorem chainAux_zero_eq_range (m : ℕ) :
    ∀ k : ℕ, chainAux G m k 0 = (autTowerEmb G m k).range
  | 0 => by rw [chainAux_zero]; exact (MonoidHom.range_eq_top.mpr Function.surjective_id).symm
  | k + 1 => by
      rw [chainAux_succ_of_lt (Nat.succ_pos k), chainAux_zero_eq_range m k, autTowerEmb_succ,
        MonoidHom.range_comp]

/-- **Lemma 9.12 の適用**: 鎖の底の中心化群は自明 — `C_{G_{m+k}}(G_m の像) = 1`.

`k = 0` は `C(⊤) = Z(G_m) = 1` (中心自明), `k > 0` は
`centralizer_eq_bot_of_chain` に 4 仮説を渡すだけ. -/
theorem centralizer_chainAux_zero_eq_bot (hZ : Subgroup.center G = ⊥) (m k : ℕ) :
    Subgroup.centralizer (↑(chainAux G m k 0) : Set (autTowerType G (m + k))) = ⊥ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [chainAux_zero, Subgroup.coe_top, Subgroup.centralizer_univ]
    exact center_autTowerType_eq_bot hZ (m + 0)
  · exact centralizer_eq_bot_of_chain hk (chainAux G m k)
      (fun i hi => chainAux_le_succ m k i hi)
      (fun i hi => chainAux_le_normalizer m k i hi)
      (fun i hi => chainAux_centralizer_inf hZ m k i hi)
      (chainAux_self m k)

/-- 鎖の各項は環境に subnormal (`S j ◁ S (j+1) ◁ ⋯ ◁ S k = ⊤` を上から降ろす).

`d` (= `k - j`) に関する帰納法. `IsSubnormal.step` は上から下へ降ろす形なので,
`j + d = k` をパラメータに取るのが素直. -/
theorem chainAux_isSubnormal (m k : ℕ) :
    ∀ (d j : ℕ), j + d = k → (chainAux G m k j).IsSubnormal
  | 0, j, hjd => by
      have : j = k := by omega
      subst this
      rw [chainAux_self]
      exact Subgroup.IsSubnormal.top
  | d + 1, j, hjd => by
      have hjk : j < k := by omega
      refine Subgroup.IsSubnormal.step _ (chainAux G m k (j + 1)) (chainAux_le_succ m k j hjk)
        (chainAux_isSubnormal m k d (j + 1) (by omega)) ?_
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer (chainAux_le_succ m k j hjk)).mpr
        (chainAux_le_normalizer m k j hjk)

/-- `G_m` の像は環境 `G_{m+k}` に subnormal. -/
theorem chainAux_zero_isSubnormal (m k : ℕ) : (chainAux G m k 0).IsSubnormal :=
  chainAux_isSubnormal m k k 0 (Nat.zero_add k)

/-- 鎖の底の nilpotent residual は `G_m^∞` と同型 (単射 hom の像なので). -/
noncomputable def nilpotentResidualChainAuxEquiv [Finite G] (hZ : Subgroup.center G = ⊥)
    (m k : ℕ) :
    ↥(nilpotentResidual (chainAux G m k 0))
      ≃* ↥(nilpotentResidual (⊤ : Subgroup (autTowerType G m))) := by
  rw [chainAux_zero_eq_range, MonoidHom.range_eq_map, ← map_nilpotentResidual]
  exact (Subgroup.equivMapOfInjective _ _ (autTowerEmb_injective hZ m k)).symm

/-- **一様上界** (Thm 9.10 の核): `|G_{m+k}|` は `k` に依らず `G_m` だけで抑えられる.

subnormal 版 9.13 (`card_le_factorial_of_isSubnormal`) を
「`G_m` の像 ◁◁ `G_{m+k}`, その中心化群は自明」に当て,
`(G_m の像)^∞ ≃* G_m^∞` で右辺から `k` を消す. -/
theorem card_autTowerType_add_le [Finite G] (hZ : Subgroup.center G = ⊥) (m k : ℕ) :
    Nat.card (autTowerType G (m + k))
      ≤ (Nat.card (Subgroup.center ↥(nilpotentResidual (⊤ : Subgroup (autTowerType G m))))
          * Nat.card (MulAut ↥(nilpotentResidual (⊤ : Subgroup (autTowerType G m)))))! := by
  have h := card_le_factorial_of_isSubnormal (chainAux_zero_isSubnormal m k)
    (centralizer_chainAux_zero_eq_bot hZ m k)
  rwa [Nat.card_congr (Subgroup.centerCongr (nilpotentResidualChainAuxEquiv hZ m k)).toEquiv,
    Nat.card_congr (mulAutEquivCongr (nilpotentResidualChainAuxEquiv hZ m k))] at h

/-- **Isaacs Theorem 9.10** (Wielandt automorphism tower, p. 278).

`G` を有限群, `Z(G) = 1` とし `G_1 = G`, `G_{i+1} = Aut(G_i)` とすると,
**`|G_i|` は `i` に依らない上界を持つ**. 特に `G_i` は同型を除いて有限種しかない
(位数が有界な有限群は同型類が有限個).

上界は `(|Z(G^∞)| · |Aut(G^∞)|)!` と明示的に取れる. -/
theorem exists_card_autTowerType_le [Finite G] (hZ : Subgroup.center G = ⊥) :
    ∃ n : ℕ, ∀ i : ℕ, Nat.card (autTowerType G i) ≤ n :=
  ⟨(Nat.card (Subgroup.center ↥(nilpotentResidual (⊤ : Subgroup (autTowerType G 0))))
      * Nat.card (MulAut ↥(nilpotentResidual (⊤ : Subgroup (autTowerType G 0)))))!,
    fun i => by simpa using card_autTowerType_add_le hZ 0 i⟩

end

end OddOrder.Isaacs.Ch09
