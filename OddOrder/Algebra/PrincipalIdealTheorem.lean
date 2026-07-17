/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Maps
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
* `transversalInvSum` — `σ = ∑_{t ∈ T} t` (右 transversal `T = S⁻¹` の和)。
* `transferXi` — Isaacs の `Ξ = σ·(-) : Δ(G)‾ → Δ(G)‾`。
* `transferXi_mk_sub_one` — **Theorem 10.24 の核心恒等式**
  `Ξ((g-1)‾) = ι(θ(v(g)))` (`θ` = Corollary 10.23 の同型 `K/K' ≅ Δ(K)‾`、
  `v` = transfer)。

右 transversal を左 transversal `S` の逆元集合 `S⁻¹` に取ると、
`σ(g-1) ≡ ∑_q (k_q - 1) mod Δ(K)Δ(G)` の因子
`k_q = (S q)⁻¹ · g · S(g⁻¹ • q)` が mathlib の transfer
(`Subgroup.leftTransversals.diff`) の因子と一致し、規約の橋渡しが不要になる。

Theorem 10.24 (range の同型) の仕上げと 10.25/10.26 は後続。
-/

namespace OddOrder.Algebra

open MonoidAlgebra

open scoped commutatorElement

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
theorem augmentationIdealMulLeft'_coe (x : MonoidAlgebra ℤ G)
    (α : ↥(augmentationIdeal G)) :
    (augmentationIdealMulLeft' G x α : MonoidAlgebra ℤ G) = x * α := rfl

@[simp]
theorem augmentationCoquotientMulLeft_mk (hK : K.Normal)
    (x : MonoidAlgebra ℤ G) (α : ↥(augmentationIdeal G)) :
    augmentationCoquotientMulLeft G K hK x (Submodule.Quotient.mk α)
      = Submodule.Quotient.mk (augmentationIdealMulLeft' G x α) := rfl

/-- `K` acts trivially on `Δ(G)‾`: left multiplication by `k ∈ K` descends to
the identity (Isaacs p. 313: `(k-1)ᾱ = 0`, so `kᾱ = ᾱ`). -/
theorem augmentationCoquotientMulLeft_of_mem (hK : K.Normal) {k : G}
    (hk : k ∈ K) :
    augmentationCoquotientMulLeft G K hK (MonoidAlgebra.of ℤ G k)
      = LinearMap.id := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [augmentationCoquotientMulLeft_mk, LinearMap.id_apply,
    Submodule.Quotient.eq]
  have hval : ((augmentationIdealMulLeft' G (MonoidAlgebra.of ℤ G k) α - α :
        ↥(augmentationIdeal G)) : MonoidAlgebra ℤ G)
      = (MonoidAlgebra.of ℤ G k - 1) * (α : MonoidAlgebra ℤ G) := by
    push_cast
    change MonoidAlgebra.of ℤ G k * (α : MonoidAlgebra ℤ G) - _ = _
    rw [sub_mul, one_mul]
  rw [mem_augmentationCorel, hval]
  exact Submodule.mul_mem_mul (sub_one_mem_augmentationIdealOf G K hk) α.2

/-- The natural map `Δ(K)‾ →ₗ[ℤ] Δ(G)‾` induced by `Δ(K) ⊆ Δ(G)` (both
quotients are by `Δ(K)Δ(G)`). -/
noncomputable def augmentationCoquotientInclusion :
    AugmentationQuotientOf G K →ₗ[ℤ] AugmentationCoquotient G K :=
  Submodule.mapQ (augmentationIdealOfRel G K) (augmentationCorel G K)
    (Submodule.inclusion (augmentationIdealOf_le G K))
    (fun _ hα => hα)

@[simp]
theorem augmentationCoquotientInclusion_mk (α : ↥(augmentationIdealOf G K)) :
    augmentationCoquotientInclusion G K (Submodule.Quotient.mk α)
      = Submodule.Quotient.mk
          (Submodule.inclusion (augmentationIdealOf_le G K) α) := rfl

/-- The map `Δ(K)‾ → Δ(G)‾` is injective (second isomorphism theorem: the
kernel of `Δ(K) → Δ(G)‾` is `Δ(K)Δ(G) ∩ Δ(K)`, which is exactly the relation
defining `Δ(K)‾`). -/
theorem augmentationCoquotientInclusion_injective :
    Function.Injective (augmentationCoquotientInclusion G K) := by
  intro q₁ q₂ h
  obtain ⟨α₁, rfl⟩ := Submodule.Quotient.mk_surjective _ q₁
  obtain ⟨α₂, rfl⟩ := Submodule.Quotient.mk_surjective _ q₂
  rw [augmentationCoquotientInclusion_mk, augmentationCoquotientInclusion_mk,
    Submodule.Quotient.eq] at h
  rw [Submodule.Quotient.eq]
  exact h

end Coquotient

section TransferBridge

/-! ### Isaacs Theorem 10.24 (pp. 313-314): 核心恒等式 `Ξ((g-1)‾) = ι(θ(v(g)))` -/

/-- Each transfer factor `(S q)⁻¹ · g · S(g⁻¹ • q)` (the `diff` factor of
mathlib's `MonoidHom.transfer`) lies in `K`. -/
theorem transferFactor_mem (S : K.LeftTransversal) (g : G) (q : G ⧸ K) :
    (S.2.leftQuotientEquiv q : G)⁻¹
      * (g * (S.2.leftQuotientEquiv (g⁻¹ • q) : G)) ∈ K := by
  have h : g * (S.2.leftQuotientEquiv (g⁻¹ • q) : G)
      = ((g • S).2.leftQuotientEquiv q : G) := by
    rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul]
  rw [h]
  exact QuotientGroup.leftRel_apply.mp (Quotient.exact'
    ((S.2.quotientGroupMk_leftQuotientEquiv q).trans
      ((g • S).2.quotientGroupMk_leftQuotientEquiv q).symm))

/-- `ψ = ι ∘ θ : K/K' →* Δ(G)‾` — the composite of the isomorphism `θ` of
Corollary 10.23 with the inclusion `ι : Δ(K)‾ → Δ(G)‾` (written
multiplicatively). Injective by `abelianizationToCoquotient_injective`. -/
noncomputable def abelianizationToCoquotient :
    Abelianization K →* Multiplicative (AugmentationCoquotient G K) :=
  (AddMonoidHom.toMultiplicative
      (augmentationCoquotientInclusion G K).toAddMonoidHom).comp
    (abelianizationEquivAugmentationQuotientOf G K).toMonoidHom

@[simp]
theorem abelianizationToCoquotient_apply (a : Abelianization K) :
    abelianizationToCoquotient G K a
      = Multiplicative.ofAdd (augmentationCoquotientInclusion G K
          (abelianizationEquivAugmentationQuotientOf G K a).toAdd) := rfl

theorem abelianizationToCoquotient_injective :
    Function.Injective (abelianizationToCoquotient G K) := by
  intro a b h
  rw [abelianizationToCoquotient_apply, abelianizationToCoquotient_apply] at h
  exact (abelianizationEquivAugmentationQuotientOf G K).injective
    (Multiplicative.toAdd.injective
      (augmentationCoquotientInclusion_injective G K
        (Multiplicative.ofAdd.injective h)))

variable [K.FiniteIndex]

/-- The sum `σ ∈ ℤ[G]` of the inverses of a left transversal `S` for `K` in
`G` — equivalently, the sum of the elements of the right transversal `S⁻¹`
(Isaacs p. 313, `σ = ∑_{t ∈ T} t`). -/
noncomputable def transversalInvSum (S : K.LeftTransversal) :
    MonoidAlgebra ℤ G :=
  letI := K.fintypeQuotientOfFiniteIndex
  ∑ q : G ⧸ K, MonoidAlgebra.of ℤ G (S.2.leftQuotientEquiv q : G)⁻¹

/-- `∑_q (k_q - 1) ∈ ℤ[G]` where `k_q = (S q)⁻¹ · g · S(g⁻¹ • q) ∈ K` are the
transfer factors of `g` — the additive avatar of the pretransfer
`V(g) = ∏_q k_q` (Isaacs p. 314). -/
noncomputable def transferFactorSum (S : K.LeftTransversal) (g : G) :
    MonoidAlgebra ℤ G :=
  letI := K.fintypeQuotientOfFiniteIndex
  ∑ q : G ⧸ K,
    (MonoidAlgebra.of ℤ G
        ((S.2.leftQuotientEquiv q : G)⁻¹
          * (g * (S.2.leftQuotientEquiv (g⁻¹ • q) : G))) - 1)

theorem transferFactorSum_mem (S : K.LeftTransversal) (g : G) :
    transferFactorSum G K S g ∈ augmentationIdealOf G K := by
  letI := K.fintypeQuotientOfFiniteIndex
  exact Submodule.sum_mem _ fun q _ =>
    sub_one_mem_augmentationIdealOf G K (transferFactor_mem G K S g q)

/-- **Isaacs p. 314** (core computation in the proof of Theorem 10.24):
`σ(g - 1) ≡ ∑_q (k_q - 1) mod Δ(K)Δ(G)`. -/
theorem transversalInvSum_mul_sub_one_sub_mem (S : K.LeftTransversal)
    (g : G) :
    transversalInvSum G K S * (MonoidAlgebra.of ℤ G g - 1)
        - transferFactorSum G K S g
      ∈ augmentationIdealOf G K * augmentationIdeal G := by
  letI := K.fintypeQuotientOfFiniteIndex
  have key : transversalInvSum G K S * (MonoidAlgebra.of ℤ G g - 1)
      - transferFactorSum G K S g
      = ∑ q : G ⧸ K,
          (MonoidAlgebra.of ℤ G
              ((S.2.leftQuotientEquiv q : G)⁻¹
                * (g * (S.2.leftQuotientEquiv (g⁻¹ • q) : G))) - 1)
            * (MonoidAlgebra.of ℤ G (S.2.leftQuotientEquiv (g⁻¹ • q) : G)⁻¹
                - 1) := by
    have hreindex : (∑ q : G ⧸ K,
          MonoidAlgebra.of ℤ G (S.2.leftQuotientEquiv q : G)⁻¹)
        = ∑ q : G ⧸ K,
            MonoidAlgebra.of ℤ G (S.2.leftQuotientEquiv (g⁻¹ • q) : G)⁻¹ :=
      (Equiv.sum_comp (MulAction.toPerm g).symm fun p =>
        MonoidAlgebra.of ℤ G (S.2.leftQuotientEquiv p : G)⁻¹).symm
    rw [transversalInvSum, transferFactorSum, Finset.sum_mul]
    rw [show (∑ q : G ⧸ K,
          MonoidAlgebra.of ℤ G (S.2.leftQuotientEquiv q : G)⁻¹
            * (MonoidAlgebra.of ℤ G g - 1))
        = ∑ q : G ⧸ K,
            (MonoidAlgebra.of ℤ G ((S.2.leftQuotientEquiv q : G)⁻¹ * g)
              - MonoidAlgebra.of ℤ G (S.2.leftQuotientEquiv q : G)⁻¹) from
      Finset.sum_congr rfl fun q _ => by rw [mul_sub, mul_one, ← map_mul]]
    rw [Finset.sum_sub_distrib, hreindex, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hgrp : ((S.2.leftQuotientEquiv q : G)⁻¹
          * (g * (S.2.leftQuotientEquiv (g⁻¹ • q) : G)))
          * (S.2.leftQuotientEquiv (g⁻¹ • q) : G)⁻¹
        = (S.2.leftQuotientEquiv q : G)⁻¹ * g := by
      rw [mul_assoc, mul_inv_cancel_right]
    rw [mul_sub, sub_mul, one_mul, mul_one, ← map_mul, hgrp]
  rw [key]
  exact Submodule.sum_mem _ fun q _ =>
    Submodule.mul_mem_mul
      (sub_one_mem_augmentationIdealOf G K (transferFactor_mem G K S g q))
      (sub_one_mem_augmentationIdeal G _)

/-- **Isaacs p. 314** (proof of Theorem 10.24): under the isomorphism
`K/K' ≅ Δ(K)‾` of Corollary 10.23, the transfer `v(g)` corresponds to the
class of `∑_q (k_q - 1)` (multiplicativity of `k ↦ (k-1)‾` turns the
pretransfer product `V(g) = ∏ k_q` into this sum). -/
theorem abelianizationEquiv_transfer (S : K.LeftTransversal) (g : G) :
    abelianizationEquivAugmentationQuotientOf G K
        (MonoidHom.transfer (Abelianization.of : K →* Abelianization K) g)
      = Multiplicative.ofAdd (Submodule.Quotient.mk
          ⟨transferFactorSum G K S g, transferFactorSum_mem G K S g⟩) := by
  letI := K.fintypeQuotientOfFiniteIndex
  have hprod : MonoidHom.transfer
        (Abelianization.of : K →* Abelianization K) g
      = ∏ q : G ⧸ K, Abelianization.of
          (⟨(S.2.leftQuotientEquiv q : G)⁻¹
              * (g * (S.2.leftQuotientEquiv (g⁻¹ • q) : G)),
            transferFactor_mem G K S g q⟩ : K) := by
    rw [MonoidHom.transfer_def _ S g]
    simp only [Subgroup.leftTransversals.diff]
    refine Finset.prod_congr rfl fun q _ => congrArg _ ?_
    simp only [Subtype.mk.injEq]
    rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul]
  rw [hprod, map_prod]
  simp only [abelianizationEquivAugmentationQuotientOf_of]
  rw [← ofAdd_sum]
  congr 1
  have hmk : (∑ q : G ⧸ K, (Submodule.Quotient.mk
        ⟨MonoidAlgebra.of ℤ G
            ((S.2.leftQuotientEquiv q : G)⁻¹
              * (g * (S.2.leftQuotientEquiv (g⁻¹ • q) : G))) - 1,
          sub_one_mem_augmentationIdealOf G K (transferFactor_mem G K S g q)⟩
        : AugmentationQuotientOf G K))
      = Submodule.Quotient.mk (∑ q : G ⧸ K,
          (⟨MonoidAlgebra.of ℤ G
              ((S.2.leftQuotientEquiv q : G)⁻¹
                * (g * (S.2.leftQuotientEquiv (g⁻¹ • q) : G))) - 1,
            sub_one_mem_augmentationIdealOf G K (transferFactor_mem G K S g q)⟩
            : ↥(augmentationIdealOf G K))) := by
    simp only [← Submodule.mkQ_apply, map_sum]
  rw [hmk]
  congr 1
  refine Subtype.ext ?_
  rw [AddSubmonoidClass.coe_finsetSum]
  exact Finset.sum_congr rfl fun q _ => rfl

/-- Isaacs' `Ξ : Δ(G)‾ → Δ(G)‾` (p. 313) — the descent of left
multiplication by the transversal sum `σ` (Theorem 10.24 の `Ξ`). -/
noncomputable def transferXi (hK : K.Normal) (S : K.LeftTransversal) :
    AugmentationCoquotient G K →ₗ[ℤ] AugmentationCoquotient G K :=
  augmentationCoquotientMulLeft G K hK (transversalInvSum G K S)

/-- **Isaacs Theorem 10.24** (p. 314), core identity: `Ξ((g-1)‾) = ι(θ(v(g)))`
where `θ : K/K' ≅ Δ(K)‾` is the isomorphism of Corollary 10.23, `ι` the
inclusion `Δ(K)‾ → Δ(G)‾`, and `v` the transfer `G → K/K'`. The isomorphism
`v(G) ≅ Ξ(Δ(G)‾)` follows since `ι ∘ θ` is injective. -/
theorem transferXi_mk_sub_one (hK : K.Normal) (S : K.LeftTransversal)
    (g : G) :
    transferXi G K hK S (Submodule.Quotient.mk
        ⟨MonoidAlgebra.of ℤ G g - 1, sub_one_mem_augmentationIdeal G g⟩)
      = augmentationCoquotientInclusion G K
          (abelianizationEquivAugmentationQuotientOf G K
              (MonoidHom.transfer
                (Abelianization.of : K →* Abelianization K) g)).toAdd := by
  rw [abelianizationEquiv_transfer G K S g, toAdd_ofAdd, transferXi,
    augmentationCoquotientMulLeft_mk, augmentationCoquotientInclusion_mk,
    Submodule.Quotient.eq, mem_augmentationCorel]
  have hcoe : ((augmentationIdealMulLeft' G (transversalInvSum G K S)
          ⟨MonoidAlgebra.of ℤ G g - 1, sub_one_mem_augmentationIdeal G g⟩
        - Submodule.inclusion (augmentationIdealOf_le G K)
            ⟨transferFactorSum G K S g, transferFactorSum_mem G K S g⟩ :
        ↥(augmentationIdeal G)) : MonoidAlgebra ℤ G)
      = transversalInvSum G K S * (MonoidAlgebra.of ℤ G g - 1)
        - transferFactorSum G K S g := rfl
  rw [hcoe]
  exact transversalInvSum_mul_sub_one_sub_mem G K S g

/-- Restatement of `transferXi_mk_sub_one` via `ψ`:
`Ξ((g-1)‾) = (ψ(v(g))).toAdd`. -/
theorem transferXi_mk_sub_one_eq_toAdd (hK : K.Normal) (S : K.LeftTransversal)
    (g : G) :
    transferXi G K hK S (Submodule.Quotient.mk
        ⟨MonoidAlgebra.of ℤ G g - 1, sub_one_mem_augmentationIdeal G g⟩)
      = (abelianizationToCoquotient G K
          (MonoidHom.transfer
            (Abelianization.of : K →* Abelianization K) g)).toAdd := by
  rw [transferXi_mk_sub_one G K hK S g, abelianizationToCoquotient_apply,
    toAdd_ofAdd]

/-- The image `Ξ(Δ(G)‾)` consists exactly of the elements `Ξ((g-1)‾)`
(Isaacs p. 314: `Ξ` carries the generators `(g-1)‾` of `Δ(G)‾` onto the
subgroup `X ≅ v(G)`, so the image of `Ξ` is all of `X`). -/
theorem exists_of_mem_transferXi_range (hK : K.Normal) (S : K.LeftTransversal)
    {y : AugmentationCoquotient G K}
    (hy : y ∈ LinearMap.range (transferXi G K hK S)) :
    ∃ g : G, y = transferXi G K hK S (Submodule.Quotient.mk
      ⟨MonoidAlgebra.of ℤ G g - 1, sub_one_mem_augmentationIdeal G g⟩) := by
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨β, hβ⟩ := α
  have hspan : β ∈ Submodule.span ℤ
      (Set.range fun g : G => MonoidAlgebra.of ℤ G g - 1) := by
    rw [← augmentationIdeal_eq_span]; exact hβ
  revert hβ
  induction hspan using Submodule.span_induction with
  | mem z hz =>
    intro hβ
    obtain ⟨g, rfl⟩ := hz
    exact ⟨g, rfl⟩
  | zero =>
    intro hβ
    refine ⟨1, ?_⟩
    have h0 : (⟨(0 : MonoidAlgebra ℤ G), hβ⟩ : ↥(augmentationIdeal G))
        = ⟨MonoidAlgebra.of ℤ G 1 - 1, sub_one_mem_augmentationIdeal G 1⟩ :=
      Subtype.ext (show (0 : MonoidAlgebra ℤ G)
        = MonoidAlgebra.of ℤ G 1 - 1 by rw [map_one, sub_self])
    rw [h0]
  | add x y hxs hys ihx ihy =>
    intro hβ
    have hx : x ∈ augmentationIdeal G := by
      rw [augmentationIdeal_eq_span]; exact hxs
    have hy' : y ∈ augmentationIdeal G := by
      rw [augmentationIdeal_eq_span]; exact hys
    obtain ⟨gx, ex⟩ := ihx hx
    obtain ⟨gy, ey⟩ := ihy hy'
    refine ⟨gx * gy, ?_⟩
    have hsplit : (⟨x + y, hβ⟩ : ↥(augmentationIdeal G))
        = ⟨x, hx⟩ + ⟨y, hy'⟩ := rfl
    rw [hsplit, Submodule.Quotient.mk_add, map_add, ex, ey,
      transferXi_mk_sub_one_eq_toAdd, transferXi_mk_sub_one_eq_toAdd,
      transferXi_mk_sub_one_eq_toAdd, map_mul, map_mul, toAdd_mul]
  | smul c x hxs ihx =>
    intro hβ
    have hx : x ∈ augmentationIdeal G := by
      rw [augmentationIdeal_eq_span]; exact hxs
    obtain ⟨gx, ex⟩ := ihx hx
    refine ⟨gx ^ c, ?_⟩
    have hsplit : (⟨c • x, hβ⟩ : ↥(augmentationIdeal G)) = c • ⟨x, hx⟩ := rfl
    rw [hsplit, Submodule.Quotient.mk_smul, map_smul, ex,
      transferXi_mk_sub_one_eq_toAdd, transferXi_mk_sub_one_eq_toAdd,
      map_zpow, map_zpow, toAdd_zpow]

/-- The forward homomorphism of Theorem 10.24: `v(G) →* Ξ(Δ(G)‾)`,
`v(g) ↦ Ξ((g-1)‾) = (ψ(v(g))).toAdd`. -/
noncomputable def transferRangeToXiRange (hK : K.Normal)
    (S : K.LeftTransversal) :
    ↥(MonoidHom.transfer (Abelianization.of : K →* Abelianization K)).range
      →* Multiplicative ↥(LinearMap.range (transferXi G K hK S)) where
  toFun y := Multiplicative.ofAdd
    ⟨(abelianizationToCoquotient G K ↑y).toAdd, by
      obtain ⟨g, hg⟩ := y.2
      exact ⟨Submodule.Quotient.mk
          ⟨MonoidAlgebra.of ℤ G g - 1, sub_one_mem_augmentationIdeal G g⟩,
        (transferXi_mk_sub_one_eq_toAdd G K hK S g).trans (by rw [hg])⟩⟩
  map_one' := by
    rw [← ofAdd_zero]
    refine congrArg _ (Subtype.ext ?_)
    have hv : (abelianizationToCoquotient G K (1 : Abelianization K)).toAdd
        = 0 := by rw [map_one, toAdd_one]
    exact hv
  map_mul' y₁ y₂ := by
    rw [← ofAdd_add]
    refine congrArg _ (Subtype.ext ?_)
    have hv : (abelianizationToCoquotient G K
          ((y₁ : Abelianization K) * (y₂ : Abelianization K))).toAdd
        = (abelianizationToCoquotient G K y₁).toAdd
          + (abelianizationToCoquotient G K y₂).toAdd := by
      rw [map_mul, toAdd_mul]
    exact hv

theorem transferRangeToXiRange_bijective (hK : K.Normal)
    (S : K.LeftTransversal) :
    Function.Bijective (transferRangeToXiRange G K hK S) := by
  constructor
  · intro y₁ y₂ h
    have hval : (abelianizationToCoquotient G K ↑y₁).toAdd
        = (abelianizationToCoquotient G K ↑y₂).toAdd :=
      congrArg Subtype.val (Multiplicative.ofAdd.injective h)
    exact Subtype.ext (abelianizationToCoquotient_injective G K
      (Multiplicative.toAdd.injective hval))
  · intro x
    obtain ⟨g, hg⟩ := exists_of_mem_transferXi_range G K hK S x.toAdd.2
    refine ⟨⟨MonoidHom.transfer (Abelianization.of : K →* Abelianization K) g,
      ⟨g, rfl⟩⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    refine Subtype.ext ?_
    have hv : (abelianizationToCoquotient G K
          (MonoidHom.transfer
            (Abelianization.of : K →* Abelianization K) g)).toAdd
        = (x.toAdd : AugmentationCoquotient G K) := by
      rw [← transferXi_mk_sub_one_eq_toAdd G K hK S g, ← hg]
    exact hv

/-- **Isaacs Theorem 10.24** (p. 314): `v(G) ≅ Ξ(Δ(G)‾)` — the image of the
transfer homomorphism `v : G → K/K'` (for `K ⊴ G` of finite index) is
isomorphic to the image of `Ξ : Δ(G)‾ → Δ(G)‾`, left multiplication by the
sum of a transversal for `K` in `G`. -/
noncomputable def transferRangeEquivXiRange (hK : K.Normal)
    (S : K.LeftTransversal) :
    ↥(MonoidHom.transfer (Abelianization.of : K →* Abelianization K)).range
      ≃* Multiplicative ↥(LinearMap.range (transferXi G K hK S)) :=
  MulEquiv.ofBijective _ (transferRangeToXiRange_bijective G K hK S)

end TransferBridge

section CoquotientModule

/-! ### `Δ(G)‾` as a `ℤ[G/K]`-module (Isaacs p. 316)

`K` は `Δ(G)‾` に自明に作用するので、`G/K` の作用が降下し、`Δ(G)‾` は
`ℤ[G/K]` 上の加群になる。Theorem 10.25 はこの構造の上で Theorem 10.26
(`FiniteIndexAnnihilator.lean`) を `R = ℤ[G/K]` (可換、`G' ≤ K` のとき) に
適用する。instance にはせず (`ℤ`-module 構造との diamond を避ける)、
`Module.compHom` の値として提供し、使用側で `letI` する。 -/

variable [hK : K.Normal]

/-- Left multiplication as a monoid homomorphism
`G →* End_ℤ(Δ(G)‾)` (Isaacs p. 313: `Δ(G)‾` is a left `ℤ[G]`-module). -/
noncomputable def augmentationCoquotientGAction :
    G →* Module.End ℤ (AugmentationCoquotient G K) where
  toFun g := augmentationCoquotientMulLeft G K hK (MonoidAlgebra.of ℤ G g)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [augmentationCoquotientMulLeft_mk, Module.End.one_apply]
    exact congrArg _ (Subtype.ext (by
      rw [augmentationIdealMulLeft'_coe, map_one, one_mul]))
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Module.End.mul_apply, augmentationCoquotientMulLeft_mk,
      augmentationCoquotientMulLeft_mk, augmentationCoquotientMulLeft_mk]
    exact congrArg _ (Subtype.ext (by
      simp only [augmentationIdealMulLeft'_coe, map_mul, mul_assoc]))

@[simp]
theorem augmentationCoquotientGAction_apply (g : G)
    (x : AugmentationCoquotient G K) :
    augmentationCoquotientGAction G K g x
      = augmentationCoquotientMulLeft G K hK (MonoidAlgebra.of ℤ G g) x := rfl

/-- The `G`-action on `Δ(G)‾` descends to `G/K` (Isaacs p. 313: `K` acts
trivially). -/
noncomputable def augmentationCoquotientQuotientAction :
    G ⧸ K →* Module.End ℤ (AugmentationCoquotient G K) :=
  QuotientGroup.lift K (augmentationCoquotientGAction G K)
    (fun k hk => by
      refine LinearMap.ext fun x => ?_
      rw [augmentationCoquotientGAction_apply,
        augmentationCoquotientMulLeft_of_mem G K hK hk, Module.End.one_apply,
        LinearMap.id_apply])

@[simp]
theorem augmentationCoquotientQuotientAction_mk (g : G)
    (x : AugmentationCoquotient G K) :
    augmentationCoquotientQuotientAction G K (↑g : G ⧸ K) x
      = augmentationCoquotientMulLeft G K hK (MonoidAlgebra.of ℤ G g) x := rfl

/-- The action of the group ring `ℤ[G/K]` on `Δ(G)‾`, as an algebra
homomorphism into `End_ℤ(Δ(G)‾)` (Isaacs p. 316: `A = Δ(G)‾` is a left
module for `R = ℤ[G/K]`). -/
noncomputable def augmentationCoquotientAlgHom :
    MonoidAlgebra ℤ (G ⧸ K) →ₐ[ℤ] Module.End ℤ (AugmentationCoquotient G K) :=
  MonoidAlgebra.lift ℤ (Module.End ℤ (AugmentationCoquotient G K)) (G ⧸ K)
    (augmentationCoquotientQuotientAction G K)

@[simp]
theorem augmentationCoquotientAlgHom_of (g : G) :
    augmentationCoquotientAlgHom G K
        (MonoidAlgebra.of ℤ (G ⧸ K) (↑g : G ⧸ K))
      = augmentationCoquotientMulLeft G K hK (MonoidAlgebra.of ℤ G g) := by
  refine LinearMap.ext fun x => ?_
  rw [augmentationCoquotientAlgHom, MonoidAlgebra.lift_of,
    augmentationCoquotientQuotientAction_mk]

/-- `Δ(G)‾` as a `ℤ[G/K]`-module.  Not an instance: use
`letI := augmentationCoquotientModule G K` locally. -/
@[reducible]
noncomputable def augmentationCoquotientModule :
    Module (MonoidAlgebra ℤ (G ⧸ K)) (AugmentationCoquotient G K) :=
  Module.compHom _ (augmentationCoquotientAlgHom G K).toRingHom

/-- Left multiplication `ℤ[G] →ₐ[ℤ] End_ℤ(Δ(G)‾)` (the `ℤ[G]`-module
structure of Isaacs p. 313, in algebra-homomorphism form). -/
noncomputable def augmentationCoquotientAlgHomG :
    MonoidAlgebra ℤ G →ₐ[ℤ] Module.End ℤ (AugmentationCoquotient G K) :=
  MonoidAlgebra.lift ℤ (Module.End ℤ (AugmentationCoquotient G K)) G
    (augmentationCoquotientGAction G K)

/-- Left multiplication `x ↦ (ᾱ ↦ x·ᾱ)` as a `ℤ`-linear map in `x`. -/
noncomputable def augmentationCoquotientMulLeftLinear :
    MonoidAlgebra ℤ G →ₗ[ℤ] Module.End ℤ (AugmentationCoquotient G K) where
  toFun x := augmentationCoquotientMulLeft G K hK x
  map_add' x y := by
    refine LinearMap.ext fun w => ?_
    obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [LinearMap.add_apply, augmentationCoquotientMulLeft_mk,
      augmentationCoquotientMulLeft_mk, augmentationCoquotientMulLeft_mk,
      ← Submodule.Quotient.mk_add]
    exact congrArg _ (Subtype.ext (by
      simp only [augmentationIdealMulLeft'_coe, Submodule.coe_add, add_mul]))
  map_smul' c x := by
    refine LinearMap.ext fun w => ?_
    obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [RingHom.id_apply]
    change augmentationCoquotientMulLeft G K hK (c • x) (Submodule.Quotient.mk α)
      = c • augmentationCoquotientMulLeft G K hK x (Submodule.Quotient.mk α)
    rw [augmentationCoquotientMulLeft_mk, augmentationCoquotientMulLeft_mk]
    have hstep : augmentationIdealMulLeft' G (c • x) α
        = c • augmentationIdealMulLeft' G x α :=
      Subtype.ext (by
        simp only [augmentationIdealMulLeft'_coe, SetLike.val_smul,
          smul_mul_assoc])
    rw [hstep]
    exact map_smul (augmentationCorel G K).mkQ c
      (augmentationIdealMulLeft' G x α)

theorem augmentationCoquotientAlgHomG_apply (x : MonoidAlgebra ℤ G) :
    augmentationCoquotientAlgHomG G K x
      = augmentationCoquotientMulLeft G K hK x := by
  have hext : (augmentationCoquotientAlgHomG G K).toLinearMap
      = augmentationCoquotientMulLeftLinear G K := by
    refine MonoidAlgebra.lhom_ext' fun g => LinearMap.ext_ring ?_
    have h1 : augmentationCoquotientAlgHomG G K (MonoidAlgebra.of ℤ G g)
        = augmentationCoquotientMulLeft G K hK (MonoidAlgebra.of ℤ G g) :=
      MonoidAlgebra.lift_of _ _
    exact h1
  exact DFunLike.congr_fun hext x

/-- Left multiplication by an element of `Δ(K)` annihilates `Δ(G)‾`
(Isaacs p. 313: `(k-1)ᾱ = 0`, extended `ℤ`-linearly to all of `Δ(K)`). -/
theorem augmentationCoquotientMulLeft_eq_zero_of_mem
    {x : MonoidAlgebra ℤ G} (hx : x ∈ augmentationIdealOf G K) :
    augmentationCoquotientMulLeft G K hK x = 0 := by
  have key : augmentationCoquotientMulLeftLinear G K x = 0 := by
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      have hof : augmentationCoquotientMulLeftLinear G K
          (MonoidAlgebra.of ℤ G ↑k) = LinearMap.id :=
        augmentationCoquotientMulLeft_of_mem G K hK k.2
      have h1 : augmentationCoquotientMulLeftLinear G K
          (1 : MonoidAlgebra ℤ G) = LinearMap.id := by
        have h := augmentationCoquotientMulLeft_of_mem G K hK K.one_mem
        rwa [map_one] at h
      rw [map_sub, hof, h1, sub_self]
    | zero => exact map_zero _
    | add x y _ _ ihx ihy => rw [map_add, ihx, ihy, add_zero]
    | smul c x _ ihx => rw [map_smul, ihx]; exact smul_zero c
  exact key

/-- Left multiplication by an element of the left ideal `Δ(K)·ℤ[G]`
annihilates `Δ(G)‾` (Isaacs p. 313). -/
theorem augmentationCoquotientAlgHomG_eq_zero_of_mem_mul
    {z : MonoidAlgebra ℤ G}
    (hz : z ∈ augmentationIdealOf G K
      * (⊤ : Submodule ℤ (MonoidAlgebra ℤ G))) :
    augmentationCoquotientAlgHomG G K z = 0 := by
  refine Submodule.mul_induction_on' (fun a ha b _ => ?_)
    (fun x y _ _ hx hy => ?_) hz
  · rw [map_mul]
    have h0 : augmentationCoquotientAlgHomG G K a = 0 := by
      rw [augmentationCoquotientAlgHomG_apply]
      exact augmentationCoquotientMulLeft_eq_zero_of_mem G K ha
    rw [h0, zero_mul]
  · rw [map_add, hx, hy, add_zero]

/-- **Transversal independence of `Ξ`** (Isaacs p. 313): if two elements of
`ℤ[G]` differ by an element of the left ideal `Δ(K)·ℤ[G]`, then they induce
the same left-multiplication map on `Δ(G)‾`.  In particular the sum of a
transversal for `K` in `G` induces a well-defined `Ξ`, independent of the
choice of transversal. -/
theorem augmentationCoquotientMulLeft_eq_of_sub_mem
    {x y : MonoidAlgebra ℤ G}
    (h : x - y ∈ augmentationIdealOf G K
      * (⊤ : Submodule ℤ (MonoidAlgebra ℤ G))) :
    augmentationCoquotientMulLeft G K hK x
      = augmentationCoquotientMulLeft G K hK y := by
  have hzero : augmentationCoquotientAlgHomG G K (x - y) = 0 :=
    augmentationCoquotientAlgHomG_eq_zero_of_mem_mul G K h
  rw [map_sub, augmentationCoquotientAlgHomG_apply,
    augmentationCoquotientAlgHomG_apply] at hzero
  exact sub_eq_zero.mp hzero

/-- Left multiplication by an element of the right ideal `ℤ[G]·Δ(K)`
annihilates `Δ(G)‾`: `w·(k-1)·ᾱ = w·((k-1)ᾱ) = 0`. -/
theorem augmentationCoquotientAlgHomG_eq_zero_of_mem_mul_right
    {z : MonoidAlgebra ℤ G}
    (hz : z ∈ (⊤ : Submodule ℤ (MonoidAlgebra ℤ G))
      * augmentationIdealOf G K) :
    augmentationCoquotientAlgHomG G K z = 0 := by
  refine Submodule.mul_induction_on' (fun a _ b hb => ?_)
    (fun x y _ _ hx hy => ?_) hz
  · rw [map_mul]
    have h0 : augmentationCoquotientAlgHomG G K b = 0 := by
      rw [augmentationCoquotientAlgHomG_apply]
      exact augmentationCoquotientMulLeft_eq_zero_of_mem G K hb
    rw [h0, mul_zero]
  · rw [map_add, hx, hy, add_zero]

/-- Right-ideal counterpart of `augmentationCoquotientMulLeft_eq_of_sub_mem`:
elements of `ℤ[G]` differing by an element of the right ideal `ℤ[G]·Δ(K)`
induce the same map on `Δ(G)‾`.  Used to prove `Ξ` is independent of the
transversal (two transversal sums differ by such an element). -/
theorem augmentationCoquotientMulLeft_eq_of_sub_mem_right
    {x y : MonoidAlgebra ℤ G}
    (h : x - y ∈ (⊤ : Submodule ℤ (MonoidAlgebra ℤ G))
      * augmentationIdealOf G K) :
    augmentationCoquotientMulLeft G K hK x
      = augmentationCoquotientMulLeft G K hK y := by
  have hzero : augmentationCoquotientAlgHomG G K (x - y) = 0 :=
    augmentationCoquotientAlgHomG_eq_zero_of_mem_mul_right G K h
  rw [map_sub, augmentationCoquotientAlgHomG_apply,
    augmentationCoquotientAlgHomG_apply] at hzero
  exact sub_eq_zero.mp hzero

/-- Compatibility of the `ℤ[G/K]`-action with the projection
`π : ℤ[G] → ℤ[G/K]`: the coset `Kg` acts as `g` does (Isaacs p. 316). -/
theorem augmentationCoquotientAlgHom_mapDomain (x : MonoidAlgebra ℤ G) :
    augmentationCoquotientAlgHom G K
        (MonoidAlgebra.mapDomainAlgHom ℤ ℤ (QuotientGroup.mk' K) x)
      = augmentationCoquotientMulLeft G K hK x := by
  rw [← augmentationCoquotientAlgHomG_apply]
  have hcomp : (augmentationCoquotientAlgHom G K).comp
      (MonoidAlgebra.mapDomainAlgHom ℤ ℤ (QuotientGroup.mk' K))
      = augmentationCoquotientAlgHomG G K := by
    refine MonoidAlgebra.algHom_ext fun g => ?_
    simp only [AlgHom.coe_comp, Function.comp_apply,
      MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single,
      QuotientGroup.mk'_apply]
    rw [← MonoidAlgebra.of_apply, ← MonoidAlgebra.of_apply,
      augmentationCoquotientAlgHom_of]
    exact (augmentationCoquotientAlgHomG_apply G K _).symm
  exact DFunLike.congr_fun hcomp x

/-- The projection `π : ℤ[G] → ℤ[G/K]` preserves the augmentation. -/
theorem augmentation_mapDomain (x : MonoidAlgebra ℤ G) :
    augmentation (G ⧸ K)
        (MonoidAlgebra.mapDomainAlgHom ℤ ℤ (QuotientGroup.mk' K) x)
      = augmentation G x := by
  have hcomp : (augmentation (G ⧸ K)).comp
      (MonoidAlgebra.mapDomainAlgHom ℤ ℤ (QuotientGroup.mk' K))
      = augmentation G := by
    refine MonoidAlgebra.algHom_ext fun g => ?_
    simp only [AlgHom.coe_comp, Function.comp_apply,
      MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single,
      QuotientGroup.mk'_apply]
    rw [← MonoidAlgebra.of_apply, ← MonoidAlgebra.of_apply, augmentation_of,
      augmentation_of]
  exact DFunLike.congr_fun hcomp x

end CoquotientModule

section TransversalIndependence

/-! ### `Ξ` is independent of the transversal (Isaacs p. 313)

Isaacs' `Ξ` is left multiplication by the sum of *any* transversal for `K`
in `G`; here we show this map depends only on the transversal up to the coset
of each representative, and identify Theorem 10.24's `Ξ = transferXi`
(built from a left transversal via inverses) with the sum over an arbitrary
system of coset representatives `f : G/K → G`. -/

variable [hK : K.Normal] [K.FiniteIndex]

/-- The transversal sum `∑_q of(f q)` over a system of coset representatives
`f : G/K → G` (Isaacs' `σ = ∑_{t ∈ T} t`). -/
noncomputable def sectionSum (f : G ⧸ K → G) : MonoidAlgebra ℤ G :=
  letI := K.fintypeQuotientOfFiniteIndex
  ∑ q : G ⧸ K, MonoidAlgebra.of ℤ G (f q)

/-- `Ξ` is independent of the transversal: if `f₁ q` and `f₂ q` lie in the
same coset for every `q`, the two transversal sums induce the same
left-multiplication map on `Δ(G)‾` (Isaacs p. 313). -/
theorem augmentationCoquotientMulLeft_sectionSum_congr
    {f₁ f₂ : G ⧸ K → G} (h : ∀ q, (↑(f₁ q) : G ⧸ K) = ↑(f₂ q)) :
    augmentationCoquotientMulLeft G K hK (sectionSum G K f₁)
      = augmentationCoquotientMulLeft G K hK (sectionSum G K f₂) := by
  apply augmentationCoquotientMulLeft_eq_of_sub_mem_right
  letI := K.fintypeQuotientOfFiniteIndex
  rw [sectionSum, sectionSum, ← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro q _
  have hk : (f₁ q)⁻¹ * f₂ q ∈ K := QuotientGroup.eq.mp (h q)
  have hval : MonoidAlgebra.of ℤ G (f₁ q) - MonoidAlgebra.of ℤ G (f₂ q)
      = -(MonoidAlgebra.of ℤ G (f₁ q)
          * (MonoidAlgebra.of ℤ G ((f₁ q)⁻¹ * f₂ q) - 1)) := by
    rw [mul_sub, mul_one, ← map_mul, mul_inv_cancel_left, neg_sub]
  rw [hval]
  exact Submodule.neg_mem _ (Submodule.mul_mem_mul Submodule.mem_top
    (sub_one_mem_augmentationIdealOf G K hk))

/-- **Theorem 10.24's `Ξ` equals the sum over an arbitrary system of coset
representatives** (Isaacs p. 313, transversal independence): for any
`f : G/K → G` with `f q` representing `q`, `transferXi = Ξ_f`.  This bridges
the left-transversal-inverse sum of Theorem 10.24 with the plain transversal
sum used in Lemma 10.27. -/
theorem transferXi_eq_mulLeft_sectionSum (S : K.LeftTransversal)
    {f : G ⧸ K → G} (hf : ∀ q, (↑(f q) : G ⧸ K) = q) :
    transferXi G K hK S
      = augmentationCoquotientMulLeft G K hK (sectionSum G K f) := by
  letI := K.fintypeQuotientOfFiniteIndex
  have hsec : transversalInvSum G K S
      = sectionSum G K (fun q => (S.2.leftQuotientEquiv q⁻¹ : G)⁻¹) := by
    rw [transversalInvSum, sectionSum]
    exact (Equiv.sum_comp (Equiv.inv (G ⧸ K))
      (fun q => MonoidAlgebra.of ℤ G (S.2.leftQuotientEquiv q : G)⁻¹)).symm
  rw [transferXi, hsec]
  apply augmentationCoquotientMulLeft_sectionSum_congr
  intro q
  rw [hf q, QuotientGroup.mk_inv, inv_eq_iff_eq_inv]
  exact S.2.quotientGroupMk_leftQuotientEquiv q⁻¹

end TransversalIndependence

section CoquotientSq

/-! ### The index `|Δ(G)‾ : Δ(G)²‾| = |G : G'|` (Isaacs p. 316)

Theorem 10.25 の証明で Theorem 10.26 に渡す index 計算:
`UA = Δ(G)²‾` (別補題) と `Δ(G)‾/Δ(G)²‾ ≅ Δ(G)/Δ(G)² ≅ G/G'`
(第三同型 + Theorem 10.20)。 -/

/-- The image `Δ(G)²‾` of `Δ(G)²` in `Δ(G)‾` (Isaacs p. 316:
`UA = Δ(G)A = Δ(G)²‾`). -/
noncomputable def augmentationCoquotientSqImage :
    Submodule ℤ (AugmentationCoquotient G K) :=
  (augmentationIdealSq G).map (augmentationCorel G K).mkQ

theorem augmentationCorel_le_sq :
    augmentationCorel G K ≤ augmentationIdealSq G :=
  Submodule.comap_mono (Submodule.mul_le.mpr fun _ hm _ hn =>
    Submodule.mul_mem_mul (augmentationIdealOf_le G K hm) hn)

/-- Third isomorphism theorem: `Δ(G)‾/Δ(G)²‾ ≃ Δ(G)/Δ(G)²`
(Isaacs p. 316: `|A : UA| = |Δ(G) : Δ(G)²|`, valid since
`Δ(K)Δ(G) ⊆ Δ(G)²`). -/
noncomputable def augmentationCoquotientSqQuotientEquiv :
    (AugmentationCoquotient G K ⧸ augmentationCoquotientSqImage G K)
      ≃ₗ[ℤ] AugmentationQuotient G :=
  Submodule.quotientQuotientEquivQuotient (augmentationCorel G K)
    (augmentationIdealSq G) (augmentationCorel_le_sq G K)

/-- `|Δ(G)‾ : Δ(G)²‾| = |G : G'|` (Isaacs p. 316, combining the third
isomorphism theorem with Theorem 10.20). -/
theorem nat_card_quotient_augmentationCoquotientSqImage :
    Nat.card (AugmentationCoquotient G K ⧸ augmentationCoquotientSqImage G K)
      = Nat.card (Abelianization G) :=
  Nat.card_congr ((augmentationCoquotientSqQuotientEquiv G K).toEquiv.trans
    (Multiplicative.ofAdd.trans
      (abelianizationEquivAugmentationQuotient G).toEquiv.symm))

theorem finite_quotient_augmentationCoquotientSqImage [Finite G] :
    Finite
      (AugmentationCoquotient G K ⧸ augmentationCoquotientSqImage G K) :=
  Finite.of_equiv (Abelianization G)
    ((augmentationCoquotientSqQuotientEquiv G K).toEquiv.trans
      (Multiplicative.ofAdd.trans
        (abelianizationEquivAugmentationQuotient G).toEquiv.symm)).symm

end CoquotientSq

section CommQuotient

/-! ### `G/K` abelian and `ℤ[G/K]` commutative when `G' ⊆ K` (Isaacs p. 316)

Theorem 10.25 applies Theorem 10.26 over `R = ℤ[G/K]`, which is commutative
precisely because `G' ⊆ K` makes `G/K` abelian. -/

variable [hK : K.Normal]

/-- `G/K` is abelian when `K` contains the commutator subgroup `G'`
(Isaacs p. 316).  Provided as a `def` for local `letI` use — a global
instance would fire speculatively on every normal-subgroup quotient. -/
@[reducible]
def quotientCommGroup (h : _root_.commutator G ≤ K) : CommGroup (G ⧸ K) :=
  { (inferInstance : Group (G ⧸ K)) with
    mul_comm := by
      intro a b
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hmem : ⁅y⁻¹, x⁻¹⁆ ∈ K :=
        h (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
          (Subgroup.mem_top _))
      have heq : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
        rw [commutatorElement_def, inv_inv, inv_inv]; group
      rwa [heq] }

/-- The augmentation ideal `Δ(G/K)` of `ℤ[G/K]` as a genuine ring ideal
(Isaacs' `U` in the proof of Theorem 10.25). -/
noncomputable def augmentationRingIdeal :
    Ideal (MonoidAlgebra ℤ (G ⧸ K)) :=
  RingHom.ker (augmentation (G ⧸ K)).toRingHom

theorem mem_augmentationRingIdeal {γ : MonoidAlgebra ℤ (G ⧸ K)} :
    γ ∈ augmentationRingIdeal G K ↔ augmentation (G ⧸ K) γ = 0 :=
  RingHom.mem_ker

/-- The augmentation ring ideal `Δ(G/K)` and the `ℤ`-submodule
`augmentationIdeal (G ⧸ K)` have the same underlying set. -/
theorem mem_augmentationRingIdeal_iff_mem_augmentationIdeal
    {γ : MonoidAlgebra ℤ (G ⧸ K)} :
    γ ∈ augmentationRingIdeal G K ↔ γ ∈ augmentationIdeal (G ⧸ K) := by
  rw [mem_augmentationRingIdeal, mem_augmentationIdeal_iff]

end CommQuotient

end OddOrder.Algebra
