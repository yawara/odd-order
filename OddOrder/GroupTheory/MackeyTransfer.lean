/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.DoubleCoset
import OddOrder.GroupTheory.TransferTransitivity

/-!
# Mackey transfer (Isaacs Thm 10.10) — WIP skeleton

**Isaacs, Finite Group Theory, Thm 10.10** (Mackey transfer): `H, K ≤ G` with
`|G : H| < ∞`, `X` a set of `(H,K)`-double-coset representatives, `V : G → H` a
pretransfer, and `W_x : K → K ∩ Hˣ` pretransfers. Then for `k ∈ K`,
`V(k) ≡ ∏_{x ∈ X} x·W_x(k)·x⁻¹ mod H'`.

## mathlib 形 (左剰余類 mirror)

mathlib の transfer は左剰余類 `G ⧸ H` ベースなので、Isaacs の右剰余類
`(H,K)`-double coset `HxK` を `(K,H)`-double coset `KxH` に鏡映する:
`k ∈ K` に対し

`transfer ϕ k = ∏_{q : DoubleCoset.Quotient K H} transfer (mackeyRes ϕ q.out) ⟨k, hk⟩`

— `mackeyRes ϕ x : ↥((conjSubgroup x H) ⊓ K).subgroupOf K →* A`,
`w ↦ ϕ ⟨x⁻¹ · w · x, _⟩` (`conjSubgroup x H = x H x⁻¹` は `xH`-剰余類の
`K`-固定化群)。

## 証明計画 (issue 9105; `TransferTransitivity` と同型の fibration 論法)

1. `G ⧸ H` は `K`-軌道 (= `(K,H)`-double coset) 上に fiber 化され、`q = KxH` 上の
   fiber は `↥K ⧸ (x•H ⊓ K).subgroupOf K` (軌道-固定化群対応)。
2. 各 double coset の代表 `x` と fiber section `s_q` から `G ⧸ H` の合成 section
   `q ↦ (代表) · (fiber 代表)` を作る (`compSection` の double-coset 版)。
3. `diff ϕ (合成 section) (k • 合成 section)` を fibration に沿って二重積に
   並べ替えると、`q`-fiber の内積が `transfer (mackeyRes ϕ x) ⟨k⟩` の
   `diff`-展開と因子単位で一致 (`k • ` が double coset を保つことがポイント —
   `k ∈ K` の左乗法は各 `KxH` を保存)。
4. `transfer_def` で両辺を結ぶ。

現状: statement + データ定義のみ (証明は `sorry`、issue 9105 で追跡)。
-/

namespace OddOrder.GroupTheory

open Subgroup MulAction
open scoped Pointwise

variable {G : Type*} [Group G] {H K : Subgroup G} {A : Type*} [CommGroup A]

section MackeyTransfer

/-- The stabilizer subgroup datum of the Mackey decomposition at a double-coset
representative `x`: the conjugate `x H x⁻¹` (the stabilizer in `G` of the left
coset `xH`), to be intersected with `K`. -/
def conjSubgroup (x : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj x).toMonoidHom

lemma mem_conjSubgroup {x g : G} :
    g ∈ conjSubgroup x H ↔ x⁻¹ * g * x ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    have h1 : x⁻¹ * ((MulAut.conj x).toMonoidHom h) * x = h := by
      show x⁻¹ * (x * h * x⁻¹) * x = h
      group
    rwa [h1]
  · intro hg
    refine ⟨x⁻¹ * g * x, hg, ?_⟩
    show x * (x⁻¹ * g * x) * x⁻¹ = g
    group

/-- The Mackey coefficient datum at a representative `x`: the restriction of
`ϕ : H →* A` to `(x H x⁻¹ ⊓ K).subgroupOf K` along conjugation by `x⁻¹`. -/
def mackeyRes (ϕ : ↥H →* A) (x : G) :
    ↥((conjSubgroup x H ⊓ K).subgroupOf K) →* A where
  toFun w := ϕ ⟨x⁻¹ * (w : G) * x, mem_conjSubgroup.mp w.2.1⟩
  map_one' := by
    have h1 : (⟨x⁻¹ * ((1 : ↥((conjSubgroup x H ⊓ K).subgroupOf K)) : G) * x,
        mem_conjSubgroup.mp (1 : ↥((conjSubgroup x H ⊓ K).subgroupOf K)).2.1⟩ : ↥H)
        = 1 := by
      ext
      show x⁻¹ * _ * x = 1
      norm_num
    rw [h1, map_one]
  map_mul' w₁ w₂ := by
    rw [← map_mul]
    refine congrArg ϕ (Subtype.ext ?_)
    show x⁻¹ * _ * x = (x⁻¹ * _ * x) * (x⁻¹ * _ * x)
    push_cast
    group

/-- **Isaacs Theorem 10.10 (Mackey transfer)** — statement, proof WIP
(issue 9105): for `k ∈ K`, the transfer `G →* A` of `ϕ : H →* A` evaluates as
the product over `(K,H)`-double cosets of the `K`-level transfers of the
conjugated data `mackeyRes ϕ x`.

Instances: `[Fintype (DoubleCoset.Quotient (K : Set G) H)]` and the finite
index of each `(x•H ⊓ K).subgroupOf K` follow from `[H.FiniteIndex]`; they are
taken as hypotheses here to keep the statement elaboration direct. -/
theorem transfer_eq_prod_doubleCoset (ϕ : ↥H →* A) [H.FiniteIndex]
    [Fintype (DoubleCoset.Quotient (K : Set G) H)]
    [∀ q : DoubleCoset.Quotient (K : Set G) H,
      ((conjSubgroup q.out H ⊓ K).subgroupOf K).FiniteIndex]
    {k : G} (hk : k ∈ K) :
    MonoidHom.transfer ϕ k
      = ∏ q : DoubleCoset.Quotient (K : Set G) H,
          MonoidHom.transfer (mackeyRes ϕ q.out) ⟨k, hk⟩ := by
  sorry

end MackeyTransfer

end OddOrder.GroupTheory
