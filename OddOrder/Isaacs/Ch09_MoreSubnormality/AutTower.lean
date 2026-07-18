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

end OddOrder.Isaacs.Ch09
