/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.AugmentationIdeal

/-!
# Towards the principal ideal theorem: `Δ(K)Δ(G)` for a normal subgroup

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) §10C (pp. 313-317),
Theorem 10.24 に向けた基盤。`K ⊴ G` のとき `Δ(K)Δ(G)` は `ℤ[G]` の左イデアル
(Isaacs p. 313: `gΔ(K) = Δ(K)g` と `gΔ(G) ⊆ Δ(G)`) であり、したがって
`Δ(G)‾ = Δ(G)/Δ(K)Δ(G)` は左 `ℤ[G]`-加群になる。ここでは

* `exists_of_mul_eq_mul_of` — `gΔ(K) = Δ(K)g` の元レベル形。
* `mul_mem_augmentationIdealOf_mul` — `Δ(K)Δ(G)` の左イデアル性。
* `AugmentationCoquotient G K` — `Δ(G)‾ = Δ(G)/Δ(K)Δ(G)`。
* `augmentationCoquotientMulLeft` — 左乗法 `ξ_x : Δ(G)‾ → Δ(G)‾` の降下
  (Theorem 10.24 の `Ξ` は `x = ∑_{t ∈ T} t` の場合)。

Theorem 10.24 (transfer との同型) 本体と 10.25/10.26 は後続。
-/

namespace OddOrder.Algebra

open MonoidAlgebra

variable (G : Type*) [Group G] (K : Subgroup G)

section NormalLeftIdeal

/-- For `K ⊴ G`, left multiplication by `g` carries `Δ(K)` to `Δ(K)·g`
elementwise: `g·m = m'·g` with `m' = gmg⁻¹ ∈ Δ(K)` (Isaacs p. 313,
`gΔ(K) = Δ(K)g`). -/
theorem exists_of_mul_eq_mul_of (hK : K.Normal) (g : G) {m : MonoidAlgebra ℤ G}
    (hm : m ∈ augmentationIdealOf G K) :
    ∃ m' ∈ augmentationIdealOf G K,
      MonoidAlgebra.of ℤ G g * m = m' * MonoidAlgebra.of ℤ G g := by
  refine ⟨MonoidAlgebra.of ℤ G g * m * MonoidAlgebra.of ℤ G g⁻¹, ?_, ?_⟩
  · induction hm using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      have hval : MonoidAlgebra.of ℤ G g * (MonoidAlgebra.of ℤ G ↑k - 1)
          * MonoidAlgebra.of ℤ G g⁻¹
          = MonoidAlgebra.of ℤ G (g * ↑k * g⁻¹) - 1 := by
        rw [mul_sub, sub_mul, mul_one, ← map_mul, ← map_mul,
          ← map_mul, mul_inv_cancel, map_one]
      rw [hval]
      exact sub_one_mem_augmentationIdealOf G K (hK.conj_mem ↑k k.2 g)
    | zero =>
      rw [mul_zero, zero_mul]
      exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      rw [mul_add, add_mul]
      exact Submodule.add_mem _ ihx ihy
    | smul c x hx ihx =>
      rw [mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ _ ihx
  · rw [mul_assoc, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

/-- For `K ⊴ G`, the additive group `Δ(K)Δ(G)` is a left ideal of `ℤ[G]`
(Isaacs p. 313). -/
theorem mul_mem_augmentationIdealOf_mul (hK : K.Normal)
    (x : MonoidAlgebra ℤ G) {α : MonoidAlgebra ℤ G}
    (hα : α ∈ augmentationIdealOf G K * augmentationIdeal G) :
    x * α ∈ augmentationIdealOf G K * augmentationIdeal G := by
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
    rw [zero_mul]
    exact Submodule.zero_mem _
  | add f g hf hg =>
    rw [add_mul]
    exact Submodule.add_mem _ hf hg
  | single g c =>
    have hsingle : MonoidAlgebra.single g c = c • MonoidAlgebra.of ℤ G g := by
      simp only [MonoidAlgebra.of_apply]
      exact ((MonoidAlgebra.smul_single' c g 1).trans (by rw [mul_one])).symm
    rw [hsingle, smul_mul_assoc]
    refine Submodule.smul_mem _ _ ?_
    -- reduce to `of g * α ∈ Δ(K)Δ(G)` via `mul_induction_on'`
    refine Submodule.mul_induction_on'
      (C := fun r _ => MonoidAlgebra.of ℤ G g * r
        ∈ augmentationIdealOf G K * augmentationIdeal G) ?_ ?_ hα
    · intro m hm n hn
      obtain ⟨m', hm', heq⟩ := exists_of_mul_eq_mul_of G K hK g hm
      have hval : MonoidAlgebra.of ℤ G g * (m * n)
          = m' * (MonoidAlgebra.of ℤ G g * n) := by
        rw [← mul_assoc, heq, mul_assoc]
      rw [hval]
      exact Submodule.mul_mem_mul hm'
        (mul_mem_augmentationIdeal_left G (MonoidAlgebra.of ℤ G g) hn)
    · intro y hy z hz ihy ihz
      rw [mul_add]
      exact Submodule.add_mem _ ihy ihz

end NormalLeftIdeal

section Coquotient

/-- `Δ(K)Δ(G)` pulled back to a submodule of `Δ(G)` (the denominator of
Isaacs' `Δ(G)‾`, p. 313). -/
noncomputable def augmentationCorel : Submodule ℤ ↥(augmentationIdeal G) :=
  (augmentationIdealOf G K * augmentationIdeal G).comap
    (augmentationIdeal G).subtype

theorem mem_augmentationCorel {G : Type*} [Group G] {K : Subgroup G}
    {α : ↥(augmentationIdeal G)} :
    α ∈ augmentationCorel G K
      ↔ (α : MonoidAlgebra ℤ G)
          ∈ augmentationIdealOf G K * augmentationIdeal G :=
  Iff.rfl

/-- Isaacs' `Δ(G)‾ = Δ(G)/Δ(K)Δ(G)` (p. 313), as a `ℤ`-module quotient. -/
abbrev AugmentationCoquotient :=
  ↥(augmentationIdeal G) ⧸ augmentationCorel G K

/-- Left multiplication by `x : ℤ[G]` as a `ℤ`-linear endomorphism of `Δ(G)`
(well-defined since `Δ(G)` is a left ideal). -/
noncomputable def augmentationIdealMulLeft' (x : MonoidAlgebra ℤ G) :
    ↥(augmentationIdeal G) →ₗ[ℤ] ↥(augmentationIdeal G) :=
  (LinearMap.mulLeft ℤ x).restrict fun _ hβ =>
    mul_mem_augmentationIdeal_left G x hβ

/-- For `K ⊴ G`, left multiplication by `x : ℤ[G]` descends to Isaacs'
`Δ(G)‾ = Δ(G)/Δ(K)Δ(G)`; Theorem 10.24's `Ξ` is the case
`x = ∑_{t ∈ T} t`. -/
noncomputable def augmentationCoquotientMulLeft (hK : K.Normal)
    (x : MonoidAlgebra ℤ G) :
    AugmentationCoquotient G K →ₗ[ℤ] AugmentationCoquotient G K :=
  Submodule.mapQ (augmentationCorel G K) (augmentationCorel G K)
    (augmentationIdealMulLeft' G x)
    (fun _ hα => mem_augmentationCorel.mpr
      (mul_mem_augmentationIdealOf_mul G K hK x (mem_augmentationCorel.mp hα)))

@[simp]
theorem augmentationCoquotientMulLeft_mk (hK : K.Normal)
    (x : MonoidAlgebra ℤ G) (α : ↥(augmentationIdeal G)) :
    augmentationCoquotientMulLeft G K hK x (Submodule.Quotient.mk α)
      = Submodule.Quotient.mk (augmentationIdealMulLeft' G x α) := rfl

end Coquotient

end OddOrder.Algebra
