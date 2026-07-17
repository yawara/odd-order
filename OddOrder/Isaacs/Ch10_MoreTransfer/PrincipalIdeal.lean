/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.PrincipalIdealTheorem
import OddOrder.GroupTheory.TransferTransitivity

/-!
# Isaacs §10C — Principal ideal theorem (Furtwängler) and Alperin–Kuo (pp. 310-319)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 10 "More Transfer
Theory", §10C の結論部。群環側の重労働 (Lemma 10.19 – Theorem 10.25) は
`OddOrder/Algebra/AugmentationIdeal.lean` と
`OddOrder/Algebra/PrincipalIdealTheorem.lean` に実装済みで、本 leaf は
その群論的帰結を教科書の番号どおりに与える。

* **Theorem 10.18** (`transfer_commutator_eq_one`, Furtwängler の principal
  ideal theorem): 有限群 `G` の transfer `v : G → G'/G''` は自明写像。
  Theorem 10.25 (`OddOrder.Algebra.transfer_pow_relindex_eq_one`) の
  `K = G'` 特殊化 (`|K : G'| = 1`)。
* **Corollary 10.28** (`pow_index_commutator_inf_center_eq_one`, Alperin–Kuo):
  `A = G' ∩ Z(G)` に対し `g^{|G:A|} = 1` (∀ g ∈ G)。一般形
  (`pow_index_eq_one_of_le_commutator_le_center`, 任意の `A ≤ G' ∩ Z(G)`) を
  経由する。証明は教科書どおり: 中心部分群への transfer は `g ↦ g^{|G:A|}`
  (Thm 5.6 = mathlib `MonoidHom.transfer_eq_pow`)、transfer の推移性
  (Thm 10.8 = `OddOrder.GroupTheory.transfer_transfer`) で `V = W ∘ U` に
  分解し、Thm 10.18 で `U(g) ∈ G'' ⊆ ker W`。
-/

namespace OddOrder.Isaacs.Ch10

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- **Isaacs Theorem 10.18** (Furtwängler's principal ideal theorem, p. 310):
for a finite group `G`, the transfer homomorphism `v : G → G'/G''` into the
abelianization of the derived subgroup is the trivial map.

(In class field theory this is the *principal ideal theorem*: every ideal of a
number field becomes principal in its Hilbert class field.) -/
theorem transfer_commutator_eq_one [Finite G] (g : G) :
    MonoidHom.transfer
      (Abelianization.of :
        ↥(_root_.commutator G) →* Abelianization ↥(_root_.commutator G)) g = 1 := by
  have h := OddOrder.Algebra.transfer_pow_relindex_eq_one G (_root_.commutator G)
    le_rfl g
  rwa [Subgroup.relIndex_self, pow_one] at h

/-- **Isaacs Corollary 10.28** (Alperin–Kuo, p. 319), general form: if
`A ≤ G' ∩ Z(G)` then `g^{|G:A|} = 1` for every `g ∈ G`.

Proof: since `A` is central, the transfer `V : G → A` is `g ↦ g^{|G:A|}`
(Thm 5.6). By transitivity of transfer (Thm 10.8), `V` factors through the
transfer `U : G → G'/G''`, which is trivial by Theorem 10.18. -/
theorem pow_index_eq_one_of_le_commutator_le_center [Finite G] {A : Subgroup G}
    (hAK : A ≤ _root_.commutator G) (hAc : A ≤ Subgroup.center G) (g : G) :
    g ^ A.index = 1 := by
  classical
  haveI : IsMulCommutative ↥A :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hAc b.2) a.1)⟩⟩
  -- conjugates of `g ^ k` landing in the central subgroup `A` are fixed
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ A → g₀⁻¹ * g ^ k * g₀ = g ^ k := by
    intro k g₀ hk
    have hc := hAc hk
    rw [← mul_right_inj, ← hc.comm, mul_inv_cancel_right]
  -- the transfer `V : G → A` is `g ↦ g^{|G:A|}` (Isaacs Thm 5.6, central case)
  have hVpow : MonoidHom.transfer (MonoidHom.id ↥A) g
      = ⟨g ^ A.index, MonoidHom.transfer_eq_pow_aux g key⟩ :=
    MonoidHom.transfer_eq_pow (MonoidHom.id ↥A) g key
  -- `V` factors through the trivial transfer `G → G'/G''`, hence `V g = 1`
  have hV1 : MonoidHom.transfer (MonoidHom.id ↥A) g = 1 := by
    rw [← OddOrder.GroupTheory.transfer_transfer hAK (MonoidHom.id ↥A)]
    have hfact : (Abelianization.lift (MonoidHom.transfer
          (OddOrder.GroupTheory.transferRes hAK (MonoidHom.id ↥A)))).comp
          (Abelianization.of :
            ↥(_root_.commutator G) →* Abelianization ↥(_root_.commutator G))
        = MonoidHom.transfer
            (OddOrder.GroupTheory.transferRes hAK (MonoidHom.id ↥A)) :=
      MonoidHom.ext fun x => Abelianization.lift_apply_of _ _
    rw [← hfact, OddOrder.GroupTheory.transfer_comp_left, MonoidHom.comp_apply,
      transfer_commutator_eq_one g, map_one]
  have := hVpow.symm.trans hV1
  exact Subtype.ext_iff.mp this

/-- **Isaacs Corollary 10.28** (Alperin–Kuo, p. 319): let `G` be a finite group
and `A = G' ∩ Z(G)`. Then `g^{|G:A|} = 1` for all `g ∈ G`. -/
theorem pow_index_commutator_inf_center_eq_one [Finite G] (g : G) :
    g ^ (_root_.commutator G ⊓ Subgroup.center G).index = 1 :=
  pow_index_eq_one_of_le_commutator_le_center inf_le_left inf_le_right g

end OddOrder.Isaacs.Ch10
