/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.MixedCommutators

/-!
# Higman's Lemma 13: commuting factors in the exponent-two branch

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

At the end of the exponent-two branch, Higman constructs a new
`ξ`-length-two factor `U` which commutes elementwise with one of the original
factors `W`, while `U ∩ W = Φ(P)`. This leaf isolates the resulting
contradiction.

Both factors are honest `A(n, φ)` models. Actor transitivity therefore
provides square roots in both factors of one prescribed nonidentity Frattini
involution. If the factors commute, the quotient of those roots is an
involution outside `Φ(P)`, contradicting that every ambient involution lies
in the Frattini subgroup.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

section /- Higman Lemma 13 (p. 93) -/

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP uF uE

/-- **Higman Lemma 13 (p. 93), commuting-factor contradiction.**

Two invariant type-A factors which meet exactly in the ambient Frattini
subgroup cannot commute elementwise when all ambient involutions lie in that
subgroup and it has exponent two. -/
theorem exists_not_commute_of_typeA_factors_inf_eq_frattini
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {S T : Subgroup P}
    (hxi : IsXiActor Y)
    (hSinv : IsAInvariant Y.subtype S)
    (hTinv : IsAInvariant Y.subtype T)
    (hSTinf : S ⊓ T = frattini P)
    (dataS : XiLengthTwoTypeAData.{uP, uF} S)
    (dataT : XiLengthTwoTypeAData.{uP, uE} T)
    (hinvPhi : involutions P ⊆ frattini P)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    ∃ x : S, ∃ y : T, ¬ Commute (x : P) (y : P) := by
  let g : P := (dataS.squareWitness ^ 2 : S)
  have hgS : dataS.squareWitness ^ 2 ∈ involutions S :=
    dataS.squareWitness_sq_mem_involutions
  have hg : g ∈ involutions P := by
    refine ⟨?_, ?_⟩
    · simpa [g] using congrArg Subtype.val hgS.1
    · intro h
      apply hgS.2
      apply Subtype.ext
      simpa [g] using h
  obtain ⟨x, hx⟩ :=
    XiLengthTwoTypeAData.exists_sq_eq_of_mem_ambient_involutions
      hxi hSinv dataS hg
  obtain ⟨y, hy⟩ :=
    XiLengthTwoTypeAData.exists_sq_eq_of_mem_ambient_involutions
      hxi hTinv dataT hg
  have hxP : (x : P) ^ 2 = g := by simpa using hx
  have hyP : (y : P) ^ 2 = g := by simpa using hy
  refine ⟨x, y, ?_⟩
  intro hcomm
  let z : P := (x : P) * (y : P)⁻¹
  have hzNotPhi : z ∉ frattini P := by
    intro hzPhi
    have hzT : z ∈ T := by
      rw [← hSTinf] at hzPhi
      exact hzPhi.2
    have hxT : (x : P) ∈ T := by
      have hzy : z * (y : P) ∈ T :=
        T.mul_mem hzT y.property
      simpa [z, mul_assoc] using hzy
    have hxInf : (x : P) ∈ S ⊓ T := ⟨x.property, hxT⟩
    have hxPhi : (x : P) ∈ frattini P := by
      rw [← hSTinf]
      exact hxInf
    have hxPow : (x : P) ^ 2 = 1 := by
      simpa using congrArg Subtype.val
        (htwo ⟨(x : P), hxPhi⟩)
    exact hg.2 (hxP.symm.trans hxPow)
  have hzSq : z ^ 2 = 1 := by
    calc
      z ^ 2 = (x : P) ^ 2 * ((y : P)⁻¹) ^ 2 := by
        simpa only [z] using hcomm.inv_right.mul_pow 2
      _ = (x : P) ^ 2 * ((y : P) ^ 2)⁻¹ := by rw [inv_pow]
      _ = g * g⁻¹ := by rw [hxP, hyP]
      _ = 1 := mul_inv_cancel g
  have hzNe : z ≠ 1 := by
    intro hzOne
    exact hzNotPhi (hzOne ▸ (frattini P).one_mem)
  exact hzNotPhi (hinvPhi ⟨hzSq, hzNe⟩)

end

end OddOrder.Higman.Suzuki2Groups
