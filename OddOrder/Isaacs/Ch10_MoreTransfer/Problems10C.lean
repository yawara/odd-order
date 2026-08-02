/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.AugmentationIdeal

/-!
# Isaacs, *Finite Group Theory*, Problems 10C (pp. 324)

第 10 章末の問題集 §10C — 群環 `ℤ[G]` と増大イデアル `Δ(G)` の周辺。

## Main results

* `OddOrder.Isaacs.Ch10.mapDomainAlgHom_of` — **Problem 10C.1 (a)**:
  群準同型 `φ : G → H` は環準同型 `θ : ℤ[G] → ℤ[H]` に延長される
  (mathlib の `MonoidAlgebra.mapDomainAlgHom` がその延長で, 基底元の上で `φ` に一致)
* `OddOrder.Isaacs.Ch10.ker_mapDomainAlgHom_eq_mul_top` /
  `OddOrder.Isaacs.Ch10.ker_mapDomainAlgHom_eq_top_mul` — **Problem 10C.1 (b)**:
  `Δ(N)ℤ[G] = ker θ = ℤ[G]Δ(N)`, ここで `N = ker φ`

**Problem 10C.2** (有限生成自由アーベル群の `ℤ`-基底はすべて同じ有限濃度) は
mathlib にそのまま在るので, 本リポジトリでは薄いラッパーを書かず対応だけ記録する
(開発規約「ラッパー方針」):

* 有限性 = `LinearIndependent.finite`
  (`[Module.Finite ℤ A]` のもとで `b.linearIndependent.finite : Finite ι`)
* 濃度の一致 = `Module.Basis.indexEquiv`
  (`b.indexEquiv b' : ι ≃ ι'`; `ℤ` は `StrongRankCondition` を満たす)

書籍のヒント (`A/pA` を `𝔽_p`-ベクトル空間と見る) は, mathlib では
`StrongRankCondition` → `mk_eq_mk_of_basis` の一般論に置き換わっている。
-/

set_option autoImplicit false

namespace OddOrder.Isaacs.Ch10

open OddOrder.Algebra MonoidAlgebra

section Problem10C1

variable {G H : Type*} [Group G] [Group H] (φ : G →* H)

/-! ### Problem 10C.1

`φ : G → H` を群準同型, `N = ker φ` とする。`φ` は環準同型
`θ : ℤ[G] → ℤ[H]` に延長され (これは mathlib の
`MonoidAlgebra.mapDomainAlgHom ℤ ℤ φ`), その核は

  `ker θ = Δ(N) ℤ[G] = ℤ[G] Δ(N)`

証明の要は「各基底元 `g` をその `φ`-ファイバーの代表元 `s g` へ潰す」`ℤ`-線形写像
`mapDomain s` である (`s g := φ⁻¹(φ g)`, `Function.invFun` で選ぶ)。

* `α - mapDomain s α` は**常に** `Δ(N)ℤ[G]` にも `ℤ[G]Δ(N)` にも属する
  (`of g - of (s g) = (of (g (s g)⁻¹) - 1) * of (s g) = of (s g) * (of ((s g)⁻¹ g) - 1)`)
* `s = (φ の切断) ∘ φ` と分解するので, `θ α = 0` ならば
  `mapDomain s α = mapDomain (切断) (θ α) = 0`

したがって `θ α = 0` ⟹ `α = α - mapDomain s α ∈ Δ(N)ℤ[G] ∩ ℤ[G]Δ(N)`。
逆の包含は生成元 `n - 1` (`n ∈ N`) が `θ` で消えることから直ちに従う。 -/

/-- **Isaacs Problem 10C.1 (a)**: 群準同型 `φ : G →* H` の環準同型への延長
`θ = MonoidAlgebra.mapDomainAlgHom ℤ ℤ φ` は基底元の上で `φ` に一致する。 -/
theorem mapDomainAlgHom_of (g : G) :
    MonoidAlgebra.mapDomainAlgHom ℤ ℤ φ (MonoidAlgebra.of ℤ G g)
      = MonoidAlgebra.of ℤ H (φ g) := by
  simp [MonoidAlgebra.mapDomainAlgHom, MonoidAlgebra.mapDomainRingHom,
    MonoidAlgebra.of_apply]

/-- `φ` のファイバー代表: `fiberRep φ g` は `φ g` の (`Function.invFun` で選んだ)
固定の原像。`φ ∘ fiberRep φ = φ` かつ `fiberRep φ` は `φ` を経由して分解する。 -/
noncomputable def fiberRep (g : G) : G := Function.invFun (φ : G → H) (φ g)

theorem apply_fiberRep (g : G) : φ (fiberRep φ g) = φ g :=
  Function.invFun_eq ⟨g, rfl⟩

theorem fiberRep_eq_comp :
    fiberRep φ = Function.invFun (φ : G → H) ∘ (φ : G → H) := rfl

theorem mul_inv_fiberRep_mem_ker (g : G) : g * (fiberRep φ g)⁻¹ ∈ φ.ker := by
  simp [MonoidHom.mem_ker, apply_fiberRep]

theorem inv_fiberRep_mul_mem_ker (g : G) : (fiberRep φ g)⁻¹ * g ∈ φ.ker := by
  simp [MonoidHom.mem_ker, apply_fiberRep]

/-- 基底元を `φ`-ファイバー代表へ潰す写像は, 生成元ごとの所属さえ言えれば
任意の `α` について差 `α - mapDomain (fiberRep φ) α` の所属を与える。 -/
theorem sub_mapDomain_fiberRep_mem {L : Submodule ℤ (MonoidAlgebra ℤ G)}
    (hL : ∀ g : G,
      MonoidAlgebra.of ℤ G g - MonoidAlgebra.of ℤ G (fiberRep φ g) ∈ L)
    (α : MonoidAlgebra ℤ G) :
    α - MonoidAlgebra.mapDomain (fiberRep φ) α ∈ L := by
  induction α using MonoidAlgebra.induction_linear with
  | zero =>
    rw [MonoidAlgebra.mapDomain_zero, sub_zero]
    exact L.zero_mem
  | add x y hx hy =>
    have hxy : x + y - MonoidAlgebra.mapDomain (fiberRep φ) (x + y)
        = (x - MonoidAlgebra.mapDomain (fiberRep φ) x)
          + (y - MonoidAlgebra.mapDomain (fiberRep φ) y) := by
      rw [MonoidAlgebra.mapDomain_add]
      abel
    rw [hxy]
    exact Submodule.add_mem _ hx hy
  | single g c =>
    rw [MonoidAlgebra.mapDomain_single]
    have hkey : MonoidAlgebra.single g c
          - MonoidAlgebra.single (fiberRep φ g) c
        = c • (MonoidAlgebra.of ℤ G g
            - MonoidAlgebra.of ℤ G (fiberRep φ g)) := by
      rw [← MonoidAlgebra.smul_of g c, ← MonoidAlgebra.smul_of (fiberRep φ g) c]
      exact (smul_sub c _ _).symm
    rw [hkey]
    exact Submodule.smul_mem _ _ (hL g)

/-- **Isaacs Problem 10C.1 (b), 左側**: `ker θ = Δ(N) ℤ[G]` (`N = ker φ`). -/
theorem ker_mapDomainAlgHom_eq_mul_top :
    LinearMap.ker (MonoidAlgebra.mapDomainAlgHom ℤ ℤ φ).toLinearMap
      = augmentationIdealOf G φ.ker
        * (⊤ : Submodule ℤ (MonoidAlgebra ℤ G)) := by
  apply le_antisymm
  · intro α hα
    rw [LinearMap.mem_ker] at hα
    have hzero : MonoidAlgebra.mapDomain (fiberRep φ) α = 0 := by
      rw [fiberRep_eq_comp, show (MonoidAlgebra.mapDomain
          (Function.invFun (φ : G → H) ∘ (φ : G → H)) α : MonoidAlgebra ℤ G)
          = MonoidAlgebra.mapDomain (Function.invFun (φ : G → H))
              (MonoidAlgebra.mapDomain (φ : G → H) α) from Finsupp.mapDomain_comp]
      have : (MonoidAlgebra.mapDomain (φ : G → H) α : MonoidAlgebra ℤ H) = 0 := hα
      rw [this, MonoidAlgebra.mapDomain_zero]
    have hmem := sub_mapDomain_fiberRep_mem φ
      (L := augmentationIdealOf G φ.ker * (⊤ : Submodule ℤ (MonoidAlgebra ℤ G)))
      (fun g => by
        have hfac : MonoidAlgebra.of ℤ G g - MonoidAlgebra.of ℤ G (fiberRep φ g)
            = (MonoidAlgebra.of ℤ G (g * (fiberRep φ g)⁻¹) - 1)
              * MonoidAlgebra.of ℤ G (fiberRep φ g) := by
          rw [sub_mul, one_mul, ← map_mul, inv_mul_cancel_right]
        rw [hfac]
        exact Submodule.mul_mem_mul
          (sub_one_mem_augmentationIdealOf G φ.ker (mul_inv_fiberRep_mem_ker φ g))
          Submodule.mem_top) α
    rwa [hzero, sub_zero] at hmem
  · apply Submodule.mul_le.mpr
    intro m hm x _
    have hker : MonoidAlgebra.mapDomainAlgHom ℤ ℤ φ m = 0 := by
      induction hm using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨n, rfl⟩ := hy
        rw [map_sub, map_one, mapDomainAlgHom_of]
        have hn : φ (n : G) = 1 := n.2
        rw [hn, map_one, sub_self]
      | zero => rw [map_zero]
      | add y z _ _ ihy ihz => rw [map_add, ihy, ihz, add_zero]
      | smul d y _ ihy => rw [map_smul, ihy]; simp
    refine LinearMap.mem_ker.mpr ?_
    rw [AlgHom.toLinearMap_apply, map_mul]
    rw [hker, zero_mul]

/-- **Isaacs Problem 10C.1 (b), 右側**: `ker θ = ℤ[G] Δ(N)` (`N = ker φ`). -/
theorem ker_mapDomainAlgHom_eq_top_mul :
    LinearMap.ker (MonoidAlgebra.mapDomainAlgHom ℤ ℤ φ).toLinearMap
      = (⊤ : Submodule ℤ (MonoidAlgebra ℤ G))
        * augmentationIdealOf G φ.ker := by
  apply le_antisymm
  · intro α hα
    rw [LinearMap.mem_ker] at hα
    have hzero : MonoidAlgebra.mapDomain (fiberRep φ) α = 0 := by
      rw [fiberRep_eq_comp, show (MonoidAlgebra.mapDomain
          (Function.invFun (φ : G → H) ∘ (φ : G → H)) α : MonoidAlgebra ℤ G)
          = MonoidAlgebra.mapDomain (Function.invFun (φ : G → H))
              (MonoidAlgebra.mapDomain (φ : G → H) α) from Finsupp.mapDomain_comp]
      have : (MonoidAlgebra.mapDomain (φ : G → H) α : MonoidAlgebra ℤ H) = 0 := hα
      rw [this, MonoidAlgebra.mapDomain_zero]
    have hmem := sub_mapDomain_fiberRep_mem φ
      (L := (⊤ : Submodule ℤ (MonoidAlgebra ℤ G)) * augmentationIdealOf G φ.ker)
      (fun g => by
        have hfac : MonoidAlgebra.of ℤ G g - MonoidAlgebra.of ℤ G (fiberRep φ g)
            = MonoidAlgebra.of ℤ G (fiberRep φ g)
              * (MonoidAlgebra.of ℤ G ((fiberRep φ g)⁻¹ * g) - 1) := by
          rw [mul_sub, mul_one, ← map_mul, mul_inv_cancel_left]
        rw [hfac]
        exact Submodule.mul_mem_mul Submodule.mem_top
          (sub_one_mem_augmentationIdealOf G φ.ker (inv_fiberRep_mul_mem_ker φ g))) α
    rwa [hzero, sub_zero] at hmem
  · apply Submodule.mul_le.mpr
    intro x _ m hm
    have hker : MonoidAlgebra.mapDomainAlgHom ℤ ℤ φ m = 0 := by
      induction hm using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨n, rfl⟩ := hy
        rw [map_sub, map_one, mapDomainAlgHom_of]
        have hn : φ (n : G) = 1 := n.2
        rw [hn, map_one, sub_self]
      | zero => rw [map_zero]
      | add y z _ _ ihy ihz => rw [map_add, ihy, ihz, add_zero]
      | smul d y _ ihy => rw [map_smul, ihy]; simp
    refine LinearMap.mem_ker.mpr ?_
    rw [AlgHom.toLinearMap_apply, map_mul]
    rw [hker, mul_zero]

/-- **Isaacs Problem 10C.1 (b)**: `N ◁ G` に対し `Δ(N)ℤ[G] = ℤ[G]Δ(N)`
(どちらも `ker θ` に等しい)。 -/
theorem augmentationIdealOf_ker_mul_top_eq_top_mul :
    augmentationIdealOf G φ.ker * (⊤ : Submodule ℤ (MonoidAlgebra ℤ G))
      = (⊤ : Submodule ℤ (MonoidAlgebra ℤ G)) * augmentationIdealOf G φ.ker := by
  rw [← ker_mapDomainAlgHom_eq_mul_top, ← ker_mapDomainAlgHom_eq_top_mul]

end Problem10C1

end OddOrder.Isaacs.Ch10
