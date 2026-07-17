/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer
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

end TransferBridge

end OddOrder.Algebra
