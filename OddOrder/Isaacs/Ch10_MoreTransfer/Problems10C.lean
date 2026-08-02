/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.AugmentationIdeal
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic

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

section Problem10C3

variable {G : Type*} [Group G]

/-! ### Problem 10C.3

`U = U(ℤ[G])` を単元群, `H ≤ U` が `ℤ[G]` の加法群の `ℤ`-基底になっているとする。
このとき `K ≤ U` で `K ≅ H`, `K` も `ℤ`-基底, かつ `δ(k) = 1` (`∀ k ∈ K`) なるものがある。

構成は `h ↦ δ(h) h`。`h` は単元なので `δ(h) ∈ ℤˣ = {±1}`, 特に `δ(h)` は
`ℤ[G]` の中心にあり `h ↦ δ(h) h` は群準同型になる。基底を単元倍しても基底
(`Module.Basis.unitsSMul`) であり, `δ(δ(h) h) = δ(h)² = 1`。単射性は
「`-1 ∈ H` なら `1, -1 ∈ H` が一次従属」から従う。 -/

/-- `H ≤ U(ℤ[G])` が `ℤ[G]` の加法群の `ℤ`-基底になっている, という条件
(Isaacs Problems 10C.3 / 10C.4 の共通仮定)。 -/
structure IsUnitBasis (H : Subgroup (MonoidAlgebra ℤ G)ˣ) : Prop where
  /-- 基底元の族 `h ↦ h` は `ℤ` 上一次独立。 -/
  linearIndependent :
    LinearIndependent ℤ
      (fun h : H => ((h : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G))
  /-- 基底元の族は `ℤ[G]` を張る。 -/
  span_eq_top :
    Submodule.span ℤ (Set.range
      (fun h : H => ((h : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G))) = ⊤

variable {H : Subgroup (MonoidAlgebra ℤ G)ˣ}

/-- `IsUnitBasis H` が与える `ℤ[G]` の `ℤ`-基底 (添字集合は `H` 自身)。 -/
noncomputable def IsUnitBasis.basis (hb : IsUnitBasis H) :
    Module.Basis H ℤ (MonoidAlgebra ℤ G) :=
  Module.Basis.mk hb.linearIndependent (by rw [hb.span_eq_top])

@[simp]
theorem IsUnitBasis.basis_apply (hb : IsUnitBasis H) (h : H) :
    hb.basis h = ((h : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G) :=
  Module.Basis.mk_apply _ _ _

/-- 増大写像 `δ` が単元群の上に誘導する準同型 `U(ℤ[G]) →* ℤˣ = {±1}`。 -/
noncomputable def augUnits : (MonoidAlgebra ℤ G)ˣ →* ℤˣ :=
  Units.map (augmentation G : MonoidAlgebra ℤ G →+* ℤ)

@[simp]
theorem augUnits_coe (u : (MonoidAlgebra ℤ G)ˣ) :
    ((augUnits u : ℤˣ) : ℤ) = augmentation G (u : MonoidAlgebra ℤ G) := rfl

/-- `ℤˣ` を `ℤ[G]` の (中心的な) 単元として埋め込む。 -/
noncomputable def unitsAlgebraMap : ℤˣ →* (MonoidAlgebra ℤ G)ˣ :=
  Units.map (algebraMap ℤ (MonoidAlgebra ℤ G))

@[simp]
theorem unitsAlgebraMap_coe (w : ℤˣ) :
    ((unitsAlgebraMap w : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G)
      = algebraMap ℤ (MonoidAlgebra ℤ G) (w : ℤ) := rfl

theorem unitsAlgebraMap_commute (w : ℤˣ) (u : (MonoidAlgebra ℤ G)ˣ) :
    (unitsAlgebraMap w : (MonoidAlgebra ℤ G)ˣ) * u
      = u * (unitsAlgebraMap w : (MonoidAlgebra ℤ G)ˣ) := by
  refine Units.ext ?_
  simp only [Units.val_mul, unitsAlgebraMap_coe]
  exact Algebra.commutes _ _

@[simp]
theorem unitsAlgebraMap_neg_one :
    (unitsAlgebraMap (-1) : (MonoidAlgebra ℤ G)ˣ) = -1 := by
  refine Units.ext ?_
  simp

/-- `u ↦ δ(u) u`: 単元をその増大 `±1` 倍して増大を `1` に正規化する準同型。
`δ(u) = ±1` は中心的なのでこれは群準同型になる。 -/
noncomputable def augNormalize :
    (MonoidAlgebra ℤ G)ˣ →* (MonoidAlgebra ℤ G)ˣ where
  toFun u := unitsAlgebraMap (augUnits u) * u
  map_one' := by simp
  map_mul' u v := by
    have key : ∀ a b x y : (MonoidAlgebra ℤ G)ˣ, b * x = x * b →
        a * b * (x * y) = a * x * (b * y) := by
      intro a b x y hab
      rw [mul_assoc a b (x * y), ← mul_assoc b x y, hab, mul_assoc x b y,
        ← mul_assoc a x (b * y)]
    simp only [map_mul]
    exact key _ _ _ _ (unitsAlgebraMap_commute _ _)

theorem coe_augNormalize (u : (MonoidAlgebra ℤ G)ˣ) :
    ((augNormalize u : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G)
      = ((augUnits u : ℤˣ) : ℤ) • (u : MonoidAlgebra ℤ G) := by
  change ((unitsAlgebraMap (augUnits u) : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G)
      * (u : MonoidAlgebra ℤ G) = _
  rw [unitsAlgebraMap_coe, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rfl

/-- 正規化した単元の増大は `1`: `δ(δ(u) u) = δ(u)² = 1`. -/
theorem augmentation_augNormalize (u : (MonoidAlgebra ℤ G)ˣ) :
    augmentation G ((augNormalize u : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G)
      = 1 := by
  rw [coe_augNormalize, map_smul, smul_eq_mul, ← augUnits_coe]
  rcases Int.units_eq_one_or (augUnits u) with h | h <;> rw [h] <;> decide

/-- `H` が `ℤ`-基底なら `-1 ∉ H` (さもないと `1` と `-1` が一次従属)。 -/
theorem IsUnitBasis.neg_one_notMem (hb : IsUnitBasis H) :
    (-1 : (MonoidAlgebra ℤ G)ˣ) ∉ H := by
  classical
  intro hmem
  have hne : (-1 : (MonoidAlgebra ℤ G)ˣ) ≠ 1 := by
    intro h
    have : ((-1 : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G) = 1 := by rw [h, Units.val_one]
    rw [Units.val_neg, Units.val_one] at this
    exact (by decide : ¬ (-1 : ℤ) = 1)
      (by simpa using congrArg (augmentation G) this)
  set i : H := ⟨-1, hmem⟩ with hi
  set j : H := ⟨1, H.one_mem⟩ with hj
  have hij : i ≠ j := fun h => hne (congrArg Subtype.val h)
  have hli := hb.linearIndependent
  rw [linearIndependent_iff'] at hli
  have hsum : ∑ x ∈ ({i, j} : Finset H), (1 : ℤ) •
      ((x : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G) = 0 := by
    rw [Finset.sum_pair hij]
    simp [hi, hj]
  exact absurd (hli {i, j} (fun _ => 1) hsum i (by simp)) (by decide)

/-- `H` が `ℤ`-基底なら, 正規化 `h ↦ δ(h) h` は `H` の上で単射。 -/
theorem IsUnitBasis.injective_augNormalize (hb : IsUnitBasis H) :
    Function.Injective (augNormalize.comp H.subtype) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  have hh' : (unitsAlgebraMap (augUnits (h : (MonoidAlgebra ℤ G)ˣ)) :
      (MonoidAlgebra ℤ G)ˣ) * (h : (MonoidAlgebra ℤ G)ˣ) = 1 := hh
  have hheq : (h : (MonoidAlgebra ℤ G)ˣ)
      = (unitsAlgebraMap (augUnits (h : (MonoidAlgebra ℤ G)ˣ)))⁻¹ :=
    eq_inv_of_mul_eq_one_right hh'
  have hwinv : (augUnits (h : (MonoidAlgebra ℤ G)ˣ))⁻¹
      = augUnits (h : (MonoidAlgebra ℤ G)ˣ) := by
    rcases Int.units_eq_one_or (augUnits (h : (MonoidAlgebra ℤ G)ˣ)) with hw | hw <;>
      rw [hw] <;> decide
  rw [← map_inv, hwinv] at hheq
  rcases Int.units_eq_one_or (augUnits (h : (MonoidAlgebra ℤ G)ˣ)) with hw | hw
  · rw [hw, map_one] at hheq
    exact Subtype.ext hheq
  · rw [hw, unitsAlgebraMap_neg_one] at hheq
    exact absurd (hheq ▸ h.2) hb.neg_one_notMem

/-- **Isaacs Problem 10C.3**: `H ≤ U(ℤ[G])` が `ℤ`-基底なら, `H` と同型で
`ℤ`-基底でもあり増大がすべて `1` の部分群 `K ≤ U(ℤ[G])` が存在する。 -/
theorem exists_isUnitBasis_augmentation_eq_one (hb : IsUnitBasis H) :
    ∃ K : Subgroup (MonoidAlgebra ℤ G)ˣ, Nonempty (H ≃* K) ∧ IsUnitBasis K ∧
      ∀ k ∈ K, augmentation G ((k : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G)
        = 1 := by
  classical
  set f : H →* (MonoidAlgebra ℤ G)ˣ := augNormalize.comp H.subtype with hf
  have hinj : Function.Injective f := hb.injective_augNormalize
  set e : H ≃* f.range := MonoidHom.ofInjective hinj with he
  refine ⟨f.range, ⟨e⟩, ?_, ?_⟩
  · set bK : Module.Basis f.range ℤ (MonoidAlgebra ℤ G) :=
      (hb.basis.unitsSMul
        (fun h : H => augUnits (h : (MonoidAlgebra ℤ G)ˣ))).reindex e.toEquiv with hbK
    have hval : ⇑bK = fun k : f.range =>
        ((k : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G) := by
      funext k
      rw [hbK, Module.Basis.reindex_apply, Module.Basis.unitsSMul_apply,
        IsUnitBasis.basis_apply, Units.smul_def]
      have hk : ((e (e.symm k) : f.range) : (MonoidAlgebra ℤ G)ˣ)
          = ((k : (MonoidAlgebra ℤ G)ˣ)) := by rw [MulEquiv.apply_symm_apply]
      rw [← hk]
      exact (coe_augNormalize _).symm
    refine ⟨?_, ?_⟩
    · have := bK.linearIndependent
      rwa [hval] at this
    · have := bK.span_eq
      rwa [hval] at this
  · rintro k ⟨h, rfl⟩
    exact augmentation_augNormalize _

end Problem10C3

section Problem10C4

variable {G : Type*} [Group G] {H : Subgroup (MonoidAlgebra ℤ G)ˣ}

/-! ### Problem 10C.4

`H ≤ U(ℤ[G])` が `ℤ`-基底なら `G/G' ≅ H/H'`。

10C.3 により `δ(h) = 1` (`∀ h ∈ H`) と仮定してよい。このとき `H` の元を
`ℤ[G]` の単元とみなす準同型が誘導する代数準同型

  `Φ : ℤ[H] → ℤ[G]`,  `Φ (of h) = h`

は基底を基底へ移すので**全単射**であり, `δ_G ∘ Φ = δ_H` を満たす (基底の上で
両辺とも `1`)。したがって `Φ` は `Δ(H) ≅ Δ(G)`, `Δ(H)² ≅ Δ(G)²` を与え,

  `H/H' ≅ Δ(H)/Δ(H)² ≅ Δ(G)/Δ(G)² ≅ G/G'`   (Isaacs Thm 10.20 を両側で使う)

となる。 -/

/-- `H ≤ U(ℤ[G])` の元を `ℤ[G]` の元とみなす単位的準同型が誘導する代数準同型
`Φ : ℤ[H] → ℤ[G]`。 -/
noncomputable def unitBasisAlgHom (H : Subgroup (MonoidAlgebra ℤ G)ˣ) :
    MonoidAlgebra ℤ ↥H →ₐ[ℤ] MonoidAlgebra ℤ G :=
  MonoidAlgebra.lift ℤ (MonoidAlgebra ℤ G) ↥H
    ((Units.coeHom (MonoidAlgebra ℤ G)).comp H.subtype)

@[simp]
theorem unitBasisAlgHom_of (h : H) :
    unitBasisAlgHom H (MonoidAlgebra.of ℤ ↥H h)
      = ((h : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G) := by
  rw [unitBasisAlgHom, MonoidAlgebra.lift_of]
  rfl

/-- `Φ` は `ℤ[H]` の標準基底を `H` (これは仮定より `ℤ[G]` の基底) へ移すので全単射。 -/
theorem bijective_unitBasisAlgHom (hb : IsUnitBasis H) :
    Function.Bijective (unitBasisAlgHom H) := by
  have hlin : (unitBasisAlgHom H).toLinearMap
      = ((MonoidAlgebra.basis ↥H ℤ).equiv hb.basis (Equiv.refl ↥H)).toLinearMap := by
    refine (MonoidAlgebra.basis ↥H ℤ).ext fun h => ?_
    have hr : ((MonoidAlgebra.basis ↥H ℤ).equiv hb.basis (Equiv.refl ↥H))
        ((MonoidAlgebra.basis ↥H ℤ) h) = hb.basis h :=
      Module.Basis.equiv_apply _ _ _ _
    have hgoal : unitBasisAlgHom H (MonoidAlgebra.of ℤ ↥H h) = hb.basis h := by
      rw [unitBasisAlgHom_of, IsUnitBasis.basis_apply]
    exact hgoal.trans hr.symm
  have : Function.Bijective ((unitBasisAlgHom H).toLinearMap) := by
    rw [hlin]
    exact ((MonoidAlgebra.basis ↥H ℤ).equiv hb.basis (Equiv.refl ↥H)).bijective
  exact this

/-- 増大の正規化 `δ_G(h) = 1` のもとで `δ_G ∘ Φ = δ_H`。 -/
theorem augmentation_comp_unitBasisAlgHom
    (hδ : ∀ h : H, augmentation G ((h : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G)
      = 1) :
    (augmentation G).comp (unitBasisAlgHom H) = augmentation ↥H := by
  refine MonoidAlgebra.algHom_ext ?_
  intro h
  have h1 : MonoidAlgebra.single h (1 : ℤ) = MonoidAlgebra.of ℤ ↥H h := rfl
  rw [h1, AlgHom.comp_apply, unitBasisAlgHom_of, hδ h, augmentation_of]

/-- `Φ` の線形同値版。 -/
noncomputable def unitBasisLinearEquiv (hb : IsUnitBasis H) :
    MonoidAlgebra ℤ ↥H ≃ₗ[ℤ] MonoidAlgebra ℤ G :=
  LinearEquiv.ofBijective (unitBasisAlgHom H).toLinearMap
    (bijective_unitBasisAlgHom hb)

@[simp]
theorem unitBasisLinearEquiv_apply (hb : IsUnitBasis H)
    (α : MonoidAlgebra ℤ ↥H) :
    unitBasisLinearEquiv hb α = unitBasisAlgHom H α := rfl

/-- `Φ (Δ(H)) = Δ(G)`. -/
theorem map_augmentationIdeal (hb : IsUnitBasis H)
    (hδ : ∀ h : H, augmentation G ((h : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G)
      = 1) :
    Submodule.map (unitBasisLinearEquiv hb).toLinearMap (augmentationIdeal ↥H)
      = augmentationIdeal G := by
  have hcomm : ∀ α : MonoidAlgebra ℤ ↥H,
      augmentation G (unitBasisAlgHom H α) = augmentation ↥H α := fun α =>
    congrArg (fun f => f α) (augmentation_comp_unitBasisAlgHom hδ)
  apply le_antisymm
  · rintro _ ⟨α, hα, rfl⟩
    have hα' : augmentation ↥H α = 0 := hα
    have hgoal : augmentation G (unitBasisAlgHom H α) = 0 := by rw [hcomm, hα']
    exact hgoal
  · intro y hy
    obtain ⟨α, rfl⟩ := (bijective_unitBasisAlgHom hb).2 y
    refine ⟨α, ?_, rfl⟩
    change augmentation ↥H α = 0
    rw [← hcomm]
    exact hy

/-- `Δ(H)` から `Δ(G)` への `Φ` の制限 (線形同値)。 -/
noncomputable def augmentationIdealEquiv (hb : IsUnitBasis H)
    (hδ : ∀ h : H, augmentation G ((h : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G)
      = 1) :
    ↥(augmentationIdeal ↥H) ≃ₗ[ℤ] ↥(augmentationIdeal G) :=
  (Submodule.equivMapOfInjective (unitBasisLinearEquiv hb).toLinearMap
      (unitBasisLinearEquiv hb).injective (augmentationIdeal ↥H)).trans
    (LinearEquiv.ofEq _ _ (map_augmentationIdeal hb hδ))

@[simp]
theorem augmentationIdealEquiv_coe (hb : IsUnitBasis H)
    (hδ : ∀ h : H, augmentation G ((h : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G)
      = 1) (α : ↥(augmentationIdeal ↥H)) :
    ((augmentationIdealEquiv hb hδ α : ↥(augmentationIdeal G)) :
      MonoidAlgebra ℤ G) = unitBasisAlgHom H (α : MonoidAlgebra ℤ ↥H) := rfl

/-- `Φ (Δ(H)Δ(H)) = Δ(G)Δ(G)`. -/
theorem map_mul_augmentationIdeal (hb : IsUnitBasis H)
    (hδ : ∀ h : H, augmentation G ((h : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G)
      = 1) :
    Submodule.map (unitBasisAlgHom H).toLinearMap
        (augmentationIdeal ↥H * augmentationIdeal ↥H)
      = augmentationIdeal G * augmentationIdeal G := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.mul_le.mpr fun a ha b hb' => ?_
    have hfa : unitBasisAlgHom H a ∈ augmentationIdeal G :=
      (map_augmentationIdeal hb hδ) ▸ ⟨a, ha, rfl⟩
    have hfb : unitBasisAlgHom H b ∈ augmentationIdeal G :=
      (map_augmentationIdeal hb hδ) ▸ ⟨b, hb', rfl⟩
    have : unitBasisAlgHom H (a * b) ∈
        augmentationIdeal G * augmentationIdeal G := by
      rw [map_mul]
      exact Submodule.mul_mem_mul hfa hfb
    exact this
  · refine Submodule.mul_le.mpr fun x hx y hy => ?_
    obtain ⟨a, ha, rfl⟩ := (map_augmentationIdeal hb hδ).ge hx
    obtain ⟨b, hb', rfl⟩ := (map_augmentationIdeal hb hδ).ge hy
    refine ⟨a * b, Submodule.mul_mem_mul ha hb', ?_⟩
    simp only [LinearEquiv.coe_coe, unitBasisLinearEquiv_apply,
      AlgHom.toLinearMap_apply, map_mul]

/-- `Φ (Δ(H)²) = Δ(G)²` (部分加群 `augmentationIdealSq` のレベルで)。 -/
theorem map_augmentationIdealSq (hb : IsUnitBasis H)
    (hδ : ∀ h : H, augmentation G ((h : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G)
      = 1) :
    Submodule.map (augmentationIdealEquiv hb hδ).toLinearMap
        (augmentationIdealSq ↥H)
      = augmentationIdealSq G := by
  have hmul := map_mul_augmentationIdeal hb hδ
  apply le_antisymm
  · rintro _ ⟨α, hα, rfl⟩
    have hα' : (α : MonoidAlgebra ℤ ↥H)
        ∈ augmentationIdeal ↥H * augmentationIdeal ↥H := hα
    rw [mem_augmentationIdealSq, LinearEquiv.coe_coe, augmentationIdealEquiv_coe]
    exact hmul ▸ ⟨_, hα', rfl⟩
  · intro β hβ
    rw [mem_augmentationIdealSq, ← hmul] at hβ
    obtain ⟨α, hα, hαβ⟩ := hβ
    have hαmem : α ∈ augmentationIdeal ↥H := augmentationIdeal_sq_le ↥H hα
    refine ⟨⟨α, hαmem⟩, hα, ?_⟩
    refine Subtype.ext ?_
    rw [LinearEquiv.coe_coe, augmentationIdealEquiv_coe]
    exact hαβ

/-- `Δ(H)/Δ(H)² ≅ Δ(G)/Δ(G)²`. -/
noncomputable def augmentationQuotientEquiv (hb : IsUnitBasis H)
    (hδ : ∀ h : H, augmentation G ((h : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G)
      = 1) :
    AugmentationQuotient ↥H ≃ₗ[ℤ] AugmentationQuotient G :=
  Submodule.Quotient.equiv _ _ (augmentationIdealEquiv hb hδ)
    (map_augmentationIdealSq hb hδ)

/-- **Isaacs Problem 10C.4 (正規化された場合)**: `δ_G(h) = 1` (`∀ h ∈ H`) なら
`H/H' ≅ G/G'`。 -/
noncomputable def abelianizationEquivOfNormalized (hb : IsUnitBasis H)
    (hδ : ∀ h : H, augmentation G ((h : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G)
      = 1) :
    Abelianization ↥H ≃* Abelianization G :=
  (abelianizationEquivAugmentationQuotient ↥H).trans
    (((augmentationQuotientEquiv hb hδ).toAddEquiv.toMultiplicative).trans
      (abelianizationEquivAugmentationQuotient G).symm)

/-- **Isaacs Problem 10C.4**: `H ≤ U(ℤ[G])` が `ℤ[G]` の `ℤ`-基底なら
`G/G' ≅ H/H'`。 -/
theorem nonempty_abelianization_equiv_of_isUnitBasis (hb : IsUnitBasis H) :
    Nonempty (Abelianization ↥H ≃* Abelianization G) := by
  obtain ⟨K, ⟨e⟩, hbK, hδK⟩ := exists_isUnitBasis_augmentation_eq_one hb
  exact ⟨(MulEquiv.abelianizationCongr e).trans
    (abelianizationEquivOfNormalized hbK (fun k => hδK k k.2))⟩

end Problem10C4

section Problem10C5

open scoped Matrix

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### Problem 10C.5

`|G| = n`, `G = {g₁, …, gₙ}` と番号付けし, `a ∈ ℤ[G]` に対し `M(a)` を
「`(i, j)` 成分 = `gᵢ a` における `gⱼ` の係数」で定める。このとき

  `tr M(a) = n e`,  `e` = `a` における `1` の係数。

対角成分は `gᵢ a` における `gᵢ` の係数 = `a (gᵢ⁻¹ gᵢ) = a 1 = e` で `i` によらない。
(番号付け `Fin n ≃ G` は本質でないので添字集合は `G` 自身にとる。) -/

/-- Isaacs 10C.5/10C.6 の行列 `M(a)`: `(i, j)` 成分は `gᵢ a` における `gⱼ` の係数
(`M(a) i j = a (gᵢ⁻¹ gⱼ)`)。左正則表現の行列を反転 `g ↦ g⁻¹` で添字替えしたもので,
その形で作るので**環準同型であることが構成から従う**。 -/
noncomputable def regularMatrixHom :
    MonoidAlgebra ℤ G →ₐ[ℤ] Matrix G G ℤ :=
  ((Matrix.reindexAlgEquiv ℤ ℤ (Equiv.inv G)).toAlgHom).comp
    (((LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G ℤ)).toAlgHom).comp
      (Algebra.lmul ℤ (MonoidAlgebra ℤ G)))

/-- Isaacs 10C.5 の行列 `M(a)`. -/
noncomputable def regularMatrix (a : MonoidAlgebra ℤ G) : Matrix G G ℤ :=
  regularMatrixHom a

@[simp]
theorem regularMatrixHom_apply (a : MonoidAlgebra ℤ G) :
    regularMatrixHom a = regularMatrix a := rfl

theorem regularMatrix_apply (a : MonoidAlgebra ℤ G) (i j : G) :
    regularMatrix a i j = a (i⁻¹ * j) := by
  rw [regularMatrix, regularMatrixHom]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.inv_symm, Equiv.inv_apply, LinearMap.toMatrixAlgEquiv_apply,
    MonoidAlgebra.basis_apply]
  change (a * MonoidAlgebra.single j⁻¹ (1 : ℤ)) i⁻¹ = _
  rw [MonoidAlgebra.mul_single_apply, mul_one, inv_inv]

/-- **Isaacs Problem 10C.5**: `tr M(a) = n e`, ここで `n = |G|`,
`e` は `a` における `1` の係数。対角成分はどれも `a (gᵢ⁻¹ gᵢ) = a 1 = e`。 -/
theorem trace_regularMatrix (a : MonoidAlgebra ℤ G) :
    (regularMatrix a).trace = (Fintype.card G : ℤ) * a 1 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, regularMatrix_apply, inv_mul_cancel]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Problem10C5

section Problem10C6

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### Problem 10C.6

`a ∈ ℤ[G]` が `aᵐ = 1` (`m ≥ 1`) を満たすとき, `M(a)` の固有値はすべて 1 の冪根で,
`e = a(1) ∈ {-1, 0, 1}`。

`M` は環準同型 (`regularMatrixHom`) なので `M(a)ᵐ = M(1) = 1`。ℂ 上で見ると
特性多項式の根 `μ` は固有ベクトル `v ≠ 0` を持ち `μᵐ v = M(a)ᵐ v = v` ゆえ
`μᵐ = 1`, 特に `‖μ‖ = 1`。トレースは特性多項式の根の和なので

  `|n e| = |tr M(a)| = |Σ μ| ≤ Σ ‖μ‖ = n`,

よって `|e| ≤ 1`。 -/

/-- `Aᵐ = 1` なら `A` の特性多項式の根は 1 の `m` 乗根 (根は固有値なので,
固有ベクトル `v ≠ 0` に対し `v = Aᵐ v = μᵐ v`)。 -/
theorem pow_eq_one_of_isRoot_charpoly {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} {m : ℕ} (hA : A ^ m = 1) {μ : ℂ}
    (hμ : A.charpoly.IsRoot μ) : μ ^ m = 1 := by
  have hdet : (Matrix.scalar n μ - A).det = 0 := by
    rw [← Matrix.eval_charpoly]
    exact hμ
  obtain ⟨v, hv, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hAv : A.mulVec v = μ • v := by
    have h := hvz
    rw [Matrix.sub_mulVec, sub_eq_zero] at h
    rw [← h]
    funext i
    simp [Matrix.scalar, Matrix.mulVec_diagonal]
  have hpow : ∀ k : ℕ, (A ^ k).mulVec v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hAv,
        smul_smul, ← pow_succ]
  have hm := hpow m
  rw [hA, Matrix.one_mulVec] at hm
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hvi : v i = μ ^ m * v i := congrFun hm i
  have hzero : (μ ^ m - 1) * v i = 0 := by
    rw [sub_mul, one_mul, ← hvi, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hi

/-- `Aᵐ = 1` (`m ≥ 1`) なら `|tr A| ≤ n` (固有値の絶対値がすべて 1 だから)。 -/
theorem norm_trace_le_of_pow_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} {m : ℕ} (hm : 0 < m) (hA : A ^ m = 1) :
    ‖A.trace‖ ≤ (Fintype.card n : ℝ) := by
  have hroots : ∀ μ ∈ A.charpoly.roots, ‖μ‖ = 1 := by
    intro μ hμ
    have hμ1 : μ ^ m = 1 :=
      pow_eq_one_of_isRoot_charpoly hA (Polynomial.isRoot_of_mem_roots hμ)
    have h1 : ‖μ‖ ^ m = 1 := by rw [← norm_pow, hμ1, norm_one]
    rcases lt_trichotomy ‖μ‖ 1 with h | h | h
    · have := pow_lt_one₀ (norm_nonneg μ) h hm.ne'
      linarith
    · exact h
    · have := one_lt_pow₀ h hm.ne'
      linarith
  have hcard : (Multiset.card A.charpoly.roots : ℝ) = (Fintype.card n : ℝ) := by
    have hs : A.charpoly.roots.card = A.charpoly.natDegree :=
      Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits A.charpoly)
    rw [hs, Matrix.charpoly_natDegree_eq_dim]
  rw [Matrix.trace_eq_sum_roots_charpoly]
  refine (norm_multiset_sum_le _).trans ?_
  have hmap : A.charpoly.roots.map (fun μ : ℂ => ‖μ‖)
      = A.charpoly.roots.map (fun _ : ℂ => (1 : ℝ)) :=
    Multiset.map_congr rfl hroots
  rw [hmap, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one,
    hcard]

/-- `M(a)` を ℂ 係数に読み替えた行列。 -/
noncomputable def regularMatrixC (a : MonoidAlgebra ℤ G) : Matrix G G ℂ :=
  ((Int.castRingHom ℂ).mapMatrix) (regularMatrix a)

theorem regularMatrixC_pow (a : MonoidAlgebra ℤ G) {m : ℕ} (ha : a ^ m = 1) :
    regularMatrixC a ^ m = 1 := by
  rw [regularMatrixC, ← map_pow, ← regularMatrixHom_apply, ← map_pow, ha,
    map_one, map_one]

/-- **Isaacs Problem 10C.6 (前半)**: `aᵐ = 1` なら `M(a)` の固有値
(= 特性多項式の根) はすべて 1 の `m` 乗根。 -/
theorem pow_eq_one_of_isRoot_charpoly_regularMatrixC (a : MonoidAlgebra ℤ G)
    {m : ℕ} (ha : a ^ m = 1) {μ : ℂ}
    (hμ : (regularMatrixC a).charpoly.IsRoot μ) : μ ^ m = 1 :=
  pow_eq_one_of_isRoot_charpoly (regularMatrixC_pow a ha) hμ

theorem trace_regularMatrixC (a : MonoidAlgebra ℤ G) :
    (regularMatrixC a).trace = ((Fintype.card G : ℤ) * a 1 : ℤ) := by
  rw [← trace_regularMatrix a, regularMatrixC, Matrix.trace, Matrix.trace]
  push_cast
  rfl

end Problem10C6

section Problem10C6Conclusion

/-- **Isaacs Problem 10C.6 (後半)**: `aᵐ = 1` (`m ≥ 1`) なら
`a` における `1` の係数 `e` は `-1, 0, 1` のいずれか。 -/
theorem coeff_one_of_pow_eq_one {G : Type*} [Group G] [Finite G]
    (a : MonoidAlgebra ℤ G) {m : ℕ} (hm : 0 < m)
    (ha : a ^ m = 1) : a 1 = -1 ∨ a 1 = 0 ∨ a 1 = 1 := by
  classical
  have _ : Fintype G := Fintype.ofFinite G
  have hn : 0 < Fintype.card G := Fintype.card_pos
  have hbound := norm_trace_le_of_pow_eq_one (A := regularMatrixC a) hm
    (regularMatrixC_pow a ha)
  rw [trace_regularMatrixC] at hbound
  have hreal : |((Fintype.card G : ℤ) * a 1 : ℤ)| ≤ (Fintype.card G : ℤ) := by
    have : |(((Fintype.card G : ℤ) * a 1 : ℤ) : ℝ)| ≤ (Fintype.card G : ℝ) := by
      simpa [Complex.norm_intCast] using hbound
    exact_mod_cast this
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (Fintype.card G : ℤ))] at hreal
  have hcard : (0 : ℤ) < (Fintype.card G : ℤ) := by exact_mod_cast hn
  have habs : |a 1| ≤ 1 := le_of_mul_le_mul_left (by linarith) hcard
  have h1 : -1 ≤ a 1 := (abs_le.mp habs).1
  have h2 : a 1 ≤ 1 := (abs_le.mp habs).2
  omega

end Problem10C6Conclusion

end OddOrder.Isaacs.Ch10
