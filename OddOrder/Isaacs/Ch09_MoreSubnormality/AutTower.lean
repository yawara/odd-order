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

end OddOrder.Isaacs.Ch09
