/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.SemilinearRealization
import OddOrder.Algebra.FixedPointsGalois

/-!
# `C_V(C_{Q₀}(P)) = PW` — the theorem of Galois in the semilinear model

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §1, Proposition, p. 117:

> By Chapter I, §2, Proposition 3, `V` then acts as a group of field
> automorphisms on `Q₀` and, by the theorem of Galois, `C_V(C_{Q₀}(P)) = P`.

Chapter I §2 Proposition 3 (`Hypothesis.exists_semilinear_equiv`) realises `Q₀`
as the additive group of a finite field `F` in such a way that `V̄ = V/W` acts
through a subgroup `A ≤ RingAut F`.  Under this dictionary `C_{Q₀}(P)` is the
fixed set of the image of `P`, so the Galois correspondence
(`OddOrder.RingAut.fixer_fixedSet`) computes its centralizer in `V` exactly.

The kernel of the action of `V` on `Q₀` is `W`, so the honest statement is
`C_V(C_{Q₀}(P)) = P ⊔ W`; the book's `= P` is the case `W = 1` that Ch. III §1
is in when it invokes this.

## Main results

* `Hypothesis.VtoVbar` — the map `V → V̄ = VW/W`, with kernel `W`.
* `Hypothesis.centralizer_V_centralizer_Q0` — `C_V(C_{Q₀}(P)) = P ⊔ W`.
* `Hypothesis.centralizer_V_centralizer_Q0_of_W_eq_bot` — the book's `= P`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.Isaacs.Ch01 (fitting)

namespace Hypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## The map `V → V̄` -/

/-- The map `V → V̄ = VW/W` induced by `V ≤ D`. -/
noncomputable def VtoVbar : ↥hyp.V →* ↥hyp.Vbar where
  toFun v :=
    ⟨QuotientGroup.mk (⟨(v : G), hyp.V_le_D v.2⟩ : ↥hyp.D),
      ⟨⟨(v : G), hyp.V_le_D v.2⟩, v.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    change QuotientGroup.mk _ = (1 : hyp.Dbar)
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.one_mem _
  map_mul' v w := by
    apply Subtype.ext
    change QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
    rw [← QuotientGroup.mk_mul]
    rfl

@[simp] lemma VtoVbar_coe (v : ↥hyp.V) :
    ((hyp.VtoVbar v : ↥hyp.Vbar) : hyp.Dbar) =
      QuotientGroup.mk (⟨(v : G), hyp.V_le_D v.2⟩ : ↥hyp.D) := rfl

lemma VtoVbar_eq_one_iff (v : ↥hyp.V) :
    hyp.VtoVbar v = 1 ↔ (v : G) ∈ hyp.W := by
  constructor
  · intro h
    have hval := congrArg (fun z : ↥hyp.Vbar => (z : hyp.Dbar)) h
    rw [VtoVbar_coe] at hval
    have : QuotientGroup.mk (⟨(v : G), hyp.V_le_D v.2⟩ : ↥hyp.D) =
        (1 : hyp.Dbar) := hval
    rw [QuotientGroup.eq_one_iff] at this
    exact this
  · intro h
    apply Subtype.ext
    change QuotientGroup.mk _ = (1 : hyp.Dbar)
    rw [QuotientGroup.eq_one_iff]
    exact h

/-! ## `V` is abelian when `W = 1` -/

/-- **Ch. I §2 Proposition 3**: `V̄ = V/W` is cyclic. -/
theorem isCyclic_Vbar : IsCyclic ↥hyp.Vbar := by
  obtain ⟨_F, _hF, _hFin, _A, _hcard, hcyc, -⟩ := hyp.exists_semilinear_equiv
  exact hcyc

/-- When `W = 1` the point stabilizer `V` is abelian: it embeds into the cyclic
group `V̄ = V/W` (`VtoVbar_eq_one_iff`, `isCyclic_Vbar`). -/
theorem isMulCommutative_V_of_W_eq_bot (hW : hyp.W = ⊥) :
    IsMulCommutative ↥hyp.V := by
  haveI := hyp.isCyclic_Vbar
  refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center hyp.VtoVbar ?_
  intro v hv
  have hvW : (v : G) ∈ hyp.W := (hyp.VtoVbar_eq_one_iff v).mp hv
  rw [hW, Subgroup.mem_bot] at hvW
  have : v = 1 := Subtype.ext hvW
  subst this
  exact Subgroup.one_mem _

/-- When `W = 1`, every subgroup of `V` is centralized by all of `V`. -/
theorem V_le_centralizer_of_le_V_of_W_eq_bot (hW : hyp.W = ⊥)
    {P : Subgroup G} (hPV : P ≤ hyp.V) :
    hyp.V ≤ Subgroup.centralizer (P : Set G) := by
  haveI := hyp.isMulCommutative_V_of_W_eq_bot hW
  intro v hv
  refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
  exact congrArg (Subtype.val (p := fun z => z ∈ hyp.V))
    (this.1.comm (⟨g, hPV hg⟩ : ↥hyp.V) ⟨v, hv⟩)

/-! ## The Galois computation -/

/-- **Peterfalvi Part II, Ch. III §1, Proposition** (p. 117): "`V` acts as a
group of field automorphisms on `Q₀` and, by the theorem of Galois,
`C_V(C_{Q₀}(P)) = P`".

Stated with the kernel `W` of the action made explicit.  The proof transports
the whole configuration through Ch. I §2 Proposition 3
(`exists_semilinear_equiv`): `Q₀` becomes the additive group of a finite field
`F`, `V` acts through `RingAut F` with kernel `W`, `C_{Q₀}(P)` becomes the fixed
set `F^B` of the image `B` of `P`, and `OddOrder.RingAut.fixer_fixedSet`
identifies the automorphisms fixing `F^B` with `B` itself. -/
theorem centralizer_V_centralizer_Q0 {P : Subgroup G} (hPV : P ≤ hyp.V) :
    hyp.V ⊓ Subgroup.centralizer
        ((hyp.Q0 ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) =
      P ⊔ hyp.W := by
  classical
  obtain ⟨F, hField, hFinite, A, _hcardF, _hVcyc, eQ, μ, νe, _hT, hE, _hκ,
      _eL, _hL1, _hL2, _hL3⟩ := hyp.exists_semilinear_equiv
  letI : Field F := hField
  letI : Finite F := hFinite
  -- the action of `V` on `Q₀` read in `RingAut F`
  set σ : ↥hyp.V →* RingAut F := A.subtype.comp (νe.toMonoidHom.comp hyp.VtoVbar)
    with hσdef
  have hσker : ∀ v : ↥hyp.V, σ v = 1 ↔ (v : G) ∈ hyp.W := by
    intro v
    rw [← hyp.VtoVbar_eq_one_iff v, hσdef]
    constructor
    · intro h
      have h1 : νe (hyp.VtoVbar v) = 1 := Subtype.ext h
      simpa using νe.injective (by simpa using h1)
    · intro h
      simp [h]
  have hbridge : ∀ (v : ↥hyp.V) (x : ↥hyp.Q0),
      eQ (hyp.conjQ0bar ((hyp.VtoVbar v : ↥hyp.Vbar) : hyp.Dbar) x) =
        fieldRingAutOnAdditive F (σ v) (eQ x) := by
    intro v x
    have happ := congrArg
      (fun e : ↥hyp.Q0 ≃* Multiplicative F => e x) (hE (hyp.VtoVbar v))
    simp only [MulEquiv.trans_apply] at happ
    have hinr : hyp.fittingSemidirectEquiv
        (SemidirectProduct.inr (hyp.VtoVbar v)) =
        ((hyp.VtoVbar v : ↥hyp.Vbar) : hyp.Dbar) := by
      change SemidirectProduct.mulEquivSubgroup _
        (SemidirectProduct.inr (hyp.VtoVbar v)) = _
      simp [SemidirectProduct.mulEquivSubgroup]
    have hract : SemidirectProduct.rightFactorAction hyp.fittingConjAction
        (hyp.conjQ0bar.comp hyp.fittingSemidirectEquiv.toMonoidHom)
        (hyp.VtoVbar v) =
        hyp.conjQ0bar ((hyp.VtoVbar v : ↥hyp.Vbar) : hyp.Dbar) := by
      change hyp.conjQ0bar
        (hyp.fittingSemidirectEquiv (SemidirectProduct.inr (hyp.VtoVbar v))) = _
      rw [hinr]
    rwa [hract] at happ
  -- conjugation by `v ∈ V` fixes `x ∈ Q₀` iff `σ v` fixes the coordinate of `x`
  have hfix : ∀ (v : ↥hyp.V) (x : ↥hyp.Q0),
      (v : G) * (x : G) * (v : G)⁻¹ = (x : G) ↔
        σ v (Multiplicative.toAdd (eQ x)) = Multiplicative.toAdd (eQ x) := by
    intro v x
    constructor
    · intro h
      have hx : hyp.conjQ0bar ((hyp.VtoVbar v : ↥hyp.Vbar) : hyp.Dbar) x = x :=
        Subtype.ext h
      have := hbridge v x
      rw [hx] at this
      exact (congrArg Multiplicative.toAdd this).symm
    · intro h
      have h2 : eQ (hyp.conjQ0bar ((hyp.VtoVbar v : ↥hyp.Vbar) : hyp.Dbar) x)
          = eQ x := by
        rw [hbridge v x]
        apply Multiplicative.toAdd.injective
        rw [fieldRingAutOnAdditive_apply]
        exact h
      exact congrArg (fun y : ↥hyp.Q0 => (y : G)) (eQ.injective h2)
  -- the image of `P`
  set B : Subgroup (RingAut F) := (P.subgroupOf hyp.V).map σ with hBdef
  -- `C_{Q₀}(P)` is the fixed set of `B`
  have hmemB : ∀ τ : RingAut F, τ ∈ B ↔ ∃ v : ↥hyp.V, (v : G) ∈ P ∧ σ v = τ := by
    intro τ
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
  have hfixedSet : ∀ x : ↥hyp.Q0,
      (x : G) ∈ Subgroup.centralizer (P : Set G) ↔
        Multiplicative.toAdd (eQ x) ∈ OddOrder.RingAut.fixedSet B := by
    intro x
    constructor
    · intro hx τ hτ
      obtain ⟨v, hvP, rfl⟩ := (hmemB τ).mp hτ
      refine (hfix v x).mp ?_
      have := Subgroup.mem_centralizer_iff.mp hx (v : G) hvP
      calc (v : G) * (x : G) * (v : G)⁻¹
          = ((x : G) * (v : G)) * (v : G)⁻¹ := by rw [this]
        _ = (x : G) := by group
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hgV : g ∈ hyp.V := hPV hg
      have hτ : σ ⟨g, hgV⟩ ∈ B := ⟨⟨g, hgV⟩, hg, rfl⟩
      have hconj := (hfix ⟨g, hgV⟩ x).mpr (hx _ hτ)
      calc g * (x : G) = (g * (x : G) * g⁻¹) * g := by group
        _ = (x : G) * g := by rw [hconj]
  -- every element of the fixed set is the coordinate of some `x ∈ C_{Q₀}(P)`
  have hsurj : ∀ a : F, a ∈ OddOrder.RingAut.fixedSet B →
      ∃ x : ↥hyp.Q0, (x : G) ∈ Subgroup.centralizer (P : Set G) ∧
        Multiplicative.toAdd (eQ x) = a := by
    intro a ha
    refine ⟨eQ.symm (Multiplicative.ofAdd a), ?_, ?_⟩
    · exact (hfixedSet _).mpr (by simpa [eQ.apply_symm_apply] using ha)
    · simp [eQ.apply_symm_apply]
  apply le_antisymm
  · rintro v ⟨hvV, hvC⟩
    have hσB : σ ⟨v, hvV⟩ ∈ B := by
      rw [← OddOrder.RingAut.fixer_fixedSet B]
      intro a ha
      obtain ⟨x, hxC, rfl⟩ := hsurj a ha
      refine (hfix ⟨v, hvV⟩ x).mp ?_
      have hxmem : (x : G) ∈ hyp.Q0 ⊓ Subgroup.centralizer (P : Set G) :=
        ⟨x.2, hxC⟩
      have := Subgroup.mem_centralizer_iff.mp hvC (x : G) hxmem
      calc v * (x : G) * v⁻¹ = ((x : G) * v) * v⁻¹ := by rw [this]
        _ = (x : G) := by group
    obtain ⟨w, hwP, hwv⟩ := (hmemB _).mp hσB
    have hquot : σ (w⁻¹ * ⟨v, hvV⟩ : ↥hyp.V) = 1 := by
      rw [map_mul, map_inv, hwv, inv_mul_cancel]
    have hW : (w : G)⁻¹ * v ∈ hyp.W := (hσker _).mp hquot
    have hveq : v = (w : G) * ((w : G)⁻¹ * v) := by group
    rw [hveq]
    exact Subgroup.mul_mem_sup hwP hW
  · refine sup_le ?_ ?_
    · intro g hg
      refine ⟨hPV hg, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact (Subgroup.mem_centralizer_iff.mp hy.2 g hg).symm
    · intro w hw
      refine ⟨hyp.W_le_V hw, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact (hyp.W_centralizes_Q0 hw hy.1).symm

/-- **The theorem of Galois** as Peterfalvi states it (Part II, Ch. III §1
Proposition, p. 117): when `W = 1`, `C_V(C_{Q₀}(P)) = P`. -/
theorem centralizer_V_centralizer_Q0_of_W_eq_bot (hW : hyp.W = ⊥)
    {P : Subgroup G} (hPV : P ≤ hyp.V) :
    hyp.V ⊓ Subgroup.centralizer
        ((hyp.Q0 ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) = P := by
  rw [hyp.centralizer_V_centralizer_Q0 hPV, hW, sup_bot_eq]

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
