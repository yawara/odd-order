/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3CorollaryOne

/-!
# Peterfalvi Part II, Ch. IV §3: the Proposition, and Corollary 1, off the model

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3, pp. 129–132.

`proposition_inverseFormula_of_ne_one` states the Proposition in the coordinates
Corollary 1 reads it in, but it takes the whole apparatus of Ch. III §3 clause by clause:
the cocycle `Φ`, its unitary form `Ψ`, the two conjugation formulas, the exponent `d`,
the normalization `ν c(s) = 1` and stage (3) at the base pair.  Corollary 2 has the same
appetite, and `PSU3CorollaryTwo` already assembles all of it from the single predicate
`IsStandardModel`.  This file reuses that assembly with the endpoint changed: out comes
the Proposition's formula itself, and then Corollary 1.

The one difference is `V = W`.  Corollary 2 lives in the case `V = W` and helps itself to
`h(ω) = ζ³` there (`h_mem_W_of_freeD`); the Proposition does not need it — its hypothesis
`h(ω) ∈ W` is exactly what those appeals were for.  So the assembly here asks for the
book's `h(ω) ∈ W` and never for `V = W`, which is what makes it available to §4.

## Main results

* `Hypothesis.proposition_of_standardModel` — the Proposition's formula on `Q^#`, from
  the model of Ch. III §3 and §3 (3), with the unitary coordinates built here.
* `Hypothesis.proposition_of_isStandardModel` — the same off the bundled predicate
  `IsStandardModel`, with the book's own hypothesis `f(ω) = (ω⁻¹)^ζ`, `h(ω) ∈ W`.
* `Hypothesis.nonempty_theoremAConclusion_of_isStandardModel` — **Corollary 1** from
  `IsStandardModel`: `O^{2′}(G) ≅ PSU(3, q)`, in the shape Theorem A's conclusion takes.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open OddOrder.GroupTheory.RankOneBNPair

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

section /- Ch. IV §3, the Proposition off the model (pp. 129–132) -/

/-- **The Proposition of Peterfalvi Part II, Ch. IV §3** (p. 129), on the output of the
Proposition of Ch. III §3.

This is `corollaryTwo_of_standardModel` with the endpoint changed: the same preamble
builds the unitary coordinates — `θ = 1` makes the cocycle `F`-bilinear, hence Hermitian
on the diagonal (`cocycle_diag_eq_norm`), that shape evaluates `d` as squaring
(`mu_K_zpow_eq_sq`), `exists_modelEquiv_conj` makes the conjugation pointwise,
`exists_unitaryModel_conj` moves to the book's `(a, y)` with `Tr y = a ā`, and the
normalization `s = (0, 1)` is imposed by taking `ν = c(s)⁻¹` — but instead of Corollary 2
the conclusion is the Proposition's formula itself, on the whole of `Q^#`.

The coordinates `u`, `Ψ` are produced here, so they are existentially quantified; that is
the form Corollary 1 (`nonempty_theoremAConclusion_psu3`) consumes.

`h(ω₀) ∈ W` is the book's hypothesis.  Corollary 2 derives it from `V = W`, which is why
that path carries `hVW` and this one does not. -/
theorem proposition_of_standardModel (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1) (hW1 : 1 < Nat.card ↥hyp.W)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    -- the model of Ch. III §3
    {φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)}
    (θm : M.E → M.E)
    (hsemi : ∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
      ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E), ∀ x y : M.E,
        ((φ (a * x) (b * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = a * θm b *
            ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hθ : ∀ a ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m, θm a = a)
    (haniso : ∀ x : M.E, x ≠ 0 → φ x x ≠ 0)
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ ρ : ↥hyp.Q, (Φ ρ).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) ρ)))
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hker : ∀ z : ↥(Subgroup.center hyp.Q),
      Φ (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩)
    (hW : ∀ (v : ↥hyp.W) (x y : M.E),
      ((φ (((M.mu (1, v) : M.Eˣ) : M.E) * x) (((M.mu (1, v) : M.Eˣ) : M.E) * y) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (Θ : ↥hyp.actualKActor × ↥hyp.W →*
      MulAut (Suzuki2Groups.BilinearTwistedProduct φ))
    (hΘq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (Θ kv p).quotient = ((M.mu kv : M.Eˣ) : M.E) * p.quotient)
    {d : ℤ}
    (hΘc : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (((Θ kv p).central :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = ((M.mu (kv.1, 1) ^ d : M.Eˣ) : M.E) *
            ((p.central :
              ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (uAut : MulAut (Suzuki2Groups.BilinearTwistedProduct φ))
    (huAut : uAut ∈
      (Suzuki2Groups.BilinearTwistedProduct.groupExtension φ).inducingIdAuts)
    (hconj : (((MulAut.congr Φ).toMonoidHom.comp (hyp.conjQHom)).range).map
      (MulAut.conj uAut).toMonoidHom = Θ.range)
    -- the Proposition's base pair, and stage (3) at it
    {ζ₀ ω₀ y₀ : G} (hζ₀ : ζ₀ ∈ hyp.W) (hζ₀1 : (⟨ζ₀, hζ₀⟩ : ↥hyp.W) ≠ 1)
    (hω₀Q : ω₀ ∈ hyp.Q) (hω₀Q0 : ω₀ ∉ hyp.Q0) (hy₀Q0 : y₀ ∈ hyp.Q0)
    (hsqω₀ : ω₀ * ω₀ = y₀) (hfω₀ : f ω₀ = ζ₀⁻¹ * (ω₀ * y₀) * ζ₀)
    (hhW₀ : h ω₀ ∈ hyp.W)
    (hα : hyp.centerCoord sfive M ι hy₀Q0 /
        hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ₀, hζ₀⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ₀, hζ₀⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹) :
    ∃ (u : M.E) (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
      (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
        (OddOrder.FiniteField.hermitianCocycle m M.card hu)),
      ∀ (ρ : G) (hρQ : ρ ∈ hyp.Q), ρ ≠ 1 →
        (Ψ ⟨f ρ, hfQ ρ hρQ⟩).quotient
            = (Ψ ⟨ρ, hρQ⟩).quotient /
              Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfQ ρ hρQ⟩)
            = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹ := by
  classical
  -- ### `θ = 1` makes the cocycle `F`-bilinear, hence Hermitian on the diagonal
  have hbil : ∀ a ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E),
      ∀ b ∈ (OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E), ∀ x y : M.E,
        ((φ (a * x) (b * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = a * b *
            ((φ x y : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) := by
    intro a ha b hb x y
    rw [hsemi a ha b hb x y, hθ b hb]
  have hone : ((φ 1 1 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      ≠ 0 := fun hc => haniso 1 one_ne_zero (Subtype.ext hc)
  have hnorm := hyp.cocycle_diag_eq_norm M hm θm hsemi hθ hW hmu hζ₀1
  -- ### the exponent `d` is squaring
  have hdsq := hyp.mu_K_zpow_eq_sq M hnorm hone Θ hΘq hΘc
  -- ### the book's normalization `ν c(s) = 1`
  set c : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) :=
    ι (Additive.ofMul (hyp.toCenter sfive hyp.distinguishedInvolution_mem_Q0)) with hcdef
  have hcval : ((c : M.E)) =
      hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 := rfl
  have hcs0 : hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 ≠ 0 :=
    hyp.centerCoord_distinguishedInvolution_ne_zero sfive M ι
  have hc0 : c ≠ 0 := fun hcc => hcs0 (by rw [← hcval, hcc]; simp)
  have hν : c⁻¹ ≠ 0 := inv_ne_zero hc0
  have hνval : ((c⁻¹ : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      = (hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0)⁻¹ := by
    rw [← hcval]
    push_cast
    ring
  have hs : ((c⁻¹ : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) *
      hyp.centerCoord sfive M ι hyp.distinguishedInvolution_mem_Q0 = 1 := by
    rw [hνval]
    exact inv_mul_cancel₀ hcs0
  -- ### the conjugation action, pointwise
  obtain ⟨Φ', hquot', hcentre', hconj'⟩ :=
    hyp.exists_modelEquiv_conj M Φ Θ uAut hquot hΘq huAut hconj hmu
  have hker' : ∀ z : ↥(Subgroup.center hyp.Q),
      Φ' (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩ := by
    intro z
    have hz : Φ.symm (⟨0, ι (Additive.ofMul z)⟩ :
        Suzuki2Groups.BilinearTwistedProduct φ) = (z : ↥hyp.Q) := by
      rw [← hker z, Φ.symm_apply_apply]
    rw [← hz]
    exact hcentre' _
  -- ### the unitary coordinates
  obtain ⟨u, hu, e, Ψ, hene, -, hΨq, hΨc, hconjq, hconjy⟩ :=
    hyp.exists_unitaryModel_conj M hm hbil hnorm hone hν Φ' Θ hΘq
      (fun kv => ((M.mu (kv.1, 1) ^ d : M.Eˣ) : M.E)) hΘc hconj'
  -- ### the base pair in the shape the Proposition uses, and stage (3) at it
  have hf₀ : f ω₀ = ζ₀⁻¹ * ω₀⁻¹ * ζ₀ :=
    hyp.f_eq_conj_inv_of_sq_eq hy₀Q0 hfω₀ hsqω₀
  have hstage3 : (Ψ ⟨ω₀, hω₀Q⟩).quotient ^ (2 ^ m + 1)
      = ((M.mu ((1 : ↥hyp.actualKActor), (⟨ζ₀, hζ₀⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
        + ((M.mu ((1 : ↥hyp.actualKActor),
          (⟨ζ₀, hζ₀⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹ := by
    rw [hyp.stepThree_quotient_norm sfive M Φ' ι hker' hu Ψ hΨq hΨc hω₀Q hy₀Q0 hsqω₀,
      ← hα, hνval, div_eq_mul_inv]
    exact mul_comm _ _
  exact ⟨u, hu, Ψ, fun ρ hρQ hρ1 =>
    hyp.proposition_inverseFormula_of_ne_one H hC2 sfive M hZc Φ' hquot' ι hker' hu Ψ
      hene hΨq hΨc hconjq hconjy d hequiv hdsq hs hm hQ0card hmu hKcard hWdvd hW1 hfQ
      hζ₀ hζ₀1 hω₀Q hω₀Q0 hf₀ hhW₀ hstage3 hρQ hρ1⟩

/-- **The Proposition of Peterfalvi Part II, Ch. IV §3, straight off `IsStandardModel`**
(pp. 129–132), with the book's own hypotheses:

> Suppose that there are elements `ω ∈ Q − Q₀` and `ζ ∈ W^#` such that `f(ω) = (ω⁻¹)^ζ`
> and `h(ω) ∈ W`.  Then `f(ρ) = (ρ̄/y, 1/y)` for all `ρ = (ρ̄, y) ∈ Q − Q₀`.

`IsStandardModel` — the Proposition of Ch. III §3 as a single predicate — is unpacked and
fed to `proposition_of_standardModel`, exactly as `corollaryTwo_of_isStandardModel` feeds
`corollaryTwo_of_sectionThree`.  The type-`B` scaling pair is not asked for: it is built
from the model's own coordinate (`exists_scalingPair_of_centerCoordinate`), and the book's
"`θ` is of odd order" comes with it (`odd_orderOf_scalingPair_of_model`), `K` being regular
on `Z(Q)^#`.  Stage (3) is then `stepThree_model`.

The base pair reaches `stepThree_model` in §2's shape, with `y₀ = ω²`: squares of `Q` lie
in `Q₀` (`sq_mem_Q0_of_lemmaFiveSetup`), so `ω⁴ = 1` and `ω ω² = ω⁻¹`.

The conclusion is stated on the whole of `Q^#`, the centre included — there the formula is
step (1) of §2 rather than §3 (`inverseFormula_of_mem_Q0`) — because that is what the
Lemma of §1 compares. -/
theorem proposition_of_isStandardModel (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcard : 3 ≤ Nat.card ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1) (hW1 : 1 < Nat.card ↥hyp.W)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    (x₀ : ↥(Subgroup.center hyp.Q)) (hmodel : hyp.IsStandardModel sfive M x₀)
    -- the book's hypothesis
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hhW : h ω ∈ hyp.W) :
    ∃ (u : M.E) (hu : OddOrder.FiniteField.frobTrace (E := M.E) m u = 1)
      (Ψ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct
        (OddOrder.FiniteField.hermitianCocycle m M.card hu)),
      ∀ (ρ : G) (hρQ : ρ ∈ hyp.Q), ρ ≠ 1 →
        (Ψ ⟨f ρ, hfQ ρ hρQ⟩).quotient
            = (Ψ ⟨ρ, hρQ⟩).quotient /
              Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩) ∧
          Suzuki2Groups.unitaryCoord m u (Ψ ⟨f ρ, hfQ ρ hρQ⟩)
            = (Suzuki2Groups.unitaryCoord m u (Ψ ⟨ρ, hρQ⟩))⁻¹ := by
  classical
  obtain ⟨φ, θm, Φ, Θ, uAut, ι, hsemi, haniso, -, hΘq, huAut, hconj, hquot, hW, hker,
    hdiagscale, d, hequiv, -, hΘc⟩ := hmodel
  -- ### the base pair in §2's shape: `y₀ = ω²`, and `ω ω² = ω⁻¹`
  have hy₀Q0 : ω * ω ∈ hyp.Q0 := hyp.sq_mem_Q0_of_lemmaFiveSetup sfive hωQ
  have hω₀inv : ω * (ω * ω) = ω⁻¹ := by
    have hy1 : (ω * ω) * (ω * ω) = 1 := by
      have hsq := hy₀Q0.1
      rwa [sq] at hsq
    calc ω * (ω * ω) = ((ω * ω) * (ω * ω)) * ω⁻¹ := by group
      _ = ω⁻¹ := by rw [hy1, one_mul]
  have hfω₀ : f ω = ζ⁻¹ * (ω * (ω * ω)) * ζ := by rw [hω₀inv]; exact hf
  -- ### the type-`B` scaling pair, for the model's own `ι` and `d`
  obtain ⟨σ, τ, hscale, hWinv⟩ :=
    hyp.exists_scalingPair_of_centerCoordinate sfive M ι d hequiv
  set θF : RingAut ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) :=
    (OddOrder.FiniteField.restrictToFrobFixed (m := m) σ)⁻¹ *
      OddOrder.FiniteField.restrictToFrobFixed (m := m) τ with hθFdef
  have hθF : ∀ a : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m),
      ((θF a : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = σ.symm (τ (a : M.E)) :=
    fun a => OddOrder.FiniteField.coe_restrictToFrobFixed_inv_mul σ τ a
  have hodd : Odd (orderOf θF) :=
    hyp.odd_orderOf_scalingPair_of_model hm hQ0card sfive M θm.toRingEquiv hsemi haniso
      (hyp.cocycle_scale_of_diagScale M sfive ι d hequiv hdiagscale) ι hequiv σ τ hscale
      θF hθF
  -- ### §3 (3)
  obtain ⟨hθ, hα⟩ := hyp.stepThree_model H hC2 hm hQ0card sfive M hZc hmu hcard θm
    hsemi haniso ι d hequiv hdiagscale σ τ hscale hWinv θF hθF hodd hζ hζ1 hωQ hωQ0
    hy₀Q0 rfl hfω₀ hhW
  exact hyp.proposition_of_standardModel H hC2 sfive M hZc hmu hm hQ0card hKcard hWdvd
    hW1 hfQ θm hsemi hθ haniso Φ hquot ι hker hW Θ hΘq hΘc hequiv uAut huAut hconj
    hζ hζ1 hωQ hωQ0 hy₀Q0 rfl hfω₀ hhW hα

/-- **🎯 Peterfalvi Part II, Ch. IV §3, Corollary 1, from `IsStandardModel`** (p. 132):

> Under the hypothesis of the proposition, `O^{2′}(G) ≅ PSU(3, q)`.

`proposition_of_isStandardModel` gives the Proposition's formula on `Q^#`, and
`nonempty_theoremAConclusion_psu3` reads it as "`Q` and `f` are the standard ones", which
is the input of the Lemma of §1.  Out comes `O^{2′}(G)` with the standard `PSU(3, q)`
action on `Ω`, i.e. Theorem A's conclusion.

Nothing here asks for `V = W`: the hypothesis is the book's `f(ω) = (ω⁻¹)^ζ`,
`h(ω) ∈ W`. -/
theorem nonempty_theoremAConclusion_of_isStandardModel
    (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (hn : 1 < m) (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcard : 3 ≤ Nat.card ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1) (hW1 : 1 < Nat.card ↥hyp.W)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    (x₀ : ↥(Subgroup.center hyp.Q)) (hmodel : hyp.IsStandardModel sfive M x₀)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hζ1 : (⟨ζ, hζ⟩ : ↥hyp.W) ≠ 1)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hhW : h ω ∈ hyp.W)
    (hQ2 : IsPGroup 2 ↥hyp.Q) :
    Nonempty (TheoremAConclusion G Ω) := by
  obtain ⟨u, hu, Ψ, hform⟩ :=
    hyp.proposition_of_isStandardModel H hC2 sfive M hZc hmu
      (Nat.zero_lt_one.trans hn).ne' hQ0card hcard hKcard hWdvd hW1 hfQ x₀ hmodel
      hζ hζ1 hωQ hωQ0 hf hhW
  exact hyp.nonempty_theoremAConclusion_psu3 H hn M hu Ψ hfQ hform hQ2

/-- **🎯 Corollary 1 in the case `V = W`** (Peterfalvi Part II, Ch. IV §3, p. 132):
`O^{2′}(G) ≅ PSU(3, q)`, with nothing of §2 or §3 owed.

`V = W` is the case §2 closes by itself: its Proposition (`exists_f_eq_conj_inv`, p. 129)
produces the pair `ω ∈ Q − Q₀`, `f(ω) = (ω⁻¹)^ζ` at a generator of `W`, and `h(ω) ∈ W`
comes free there (`h_mem_W_of_freeD`, `D` acting fixed-point-freely on `(Q/Q₀)^#`).  So
the hypothesis of the Proposition of §3 holds and
`nonempty_theoremAConclusion_of_isStandardModel` applies.

This is the exact analogue of `corollaryTwo_of_isStandardModel_of_closing`, whose
conclusion is Corollary 2; here the conclusion is Corollary 1.  Together with
`SectionFourSetup.nonempty_theoremAConclusion` (the case `V ≠ W`, Ch. IV §4) it covers
both halves of Ch. IV. -/
theorem nonempty_theoremAConclusion_of_isStandardModel_of_closing
    (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (hn : 1 < m) (sfive : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 3)
    (hcard : 3 ≤ Nat.card ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1) (hW1 : 1 < Nat.card ↥hyp.W)
    (hWcyc : IsCyclic ↥hyp.W)
    (hfQ : ∀ ρ : G, ρ ∈ hyp.Q → f ρ ∈ hyp.Q)
    (x₀ : ↥(Subgroup.center hyp.Q)) (hmodel : hyp.IsStandardModel sfive M x₀)
    (hQ2 : IsPGroup 2 ↥hyp.Q) :
    Nonempty (TheoremAConclusion G Ω) := by
  classical
  have hm : m ≠ 0 := (Nat.zero_lt_one.trans hn).ne'
  -- a generator of `W`, the book's `ζ`
  obtain ⟨w, hw⟩ := hWcyc.exists_generator
  have hwW : (w : G) ∈ hyp.W := w.2
  have hwcard : orderOf ((w : G)) = Nat.card ↥hyp.W := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hw]
  have hw1 : (⟨(w : G), hwW⟩ : ↥hyp.W) ≠ 1 := by
    intro hc
    have hval : (w : G) = 1 := by simpa using congrArg Subtype.val hc
    rw [hval, orderOf_one] at hwcard
    omega
  -- §2's closing Proposition supplies the pair
  obtain ⟨ω₁, hω₁Q, hω₁Q0⟩ := hyp.exists_mem_Q_notMem_Q0 hm hQ0card hcardQ
  obtain ⟨ω₀, hω₀Q, hω₀Q0, y₀, hy₀Q0, hsq₀, hfinv⟩ :=
    hyp.exists_f_eq_conj_inv M hZc H hC2 hVW hm hQ0card hmu hKcard hWdvd
      (fun x hx => hyp.sq_mem_Q0_of_lemmaFiveSetup sfive hx) hwW
      (fun hc => hw1 (Subtype.ext hc)) hwcard hω₁Q hω₁Q0
  exact hyp.nonempty_theoremAConclusion_of_isStandardModel H hC2 hn sfive M hZc hmu
    hQ0card hcard hKcard hWdvd hW1 hfQ x₀ hmodel hwW hw1 hω₀Q hω₀Q0 hfinv
    (hyp.h_mem_W_of_freeD H M hZc hmu hVW hwW hω₀Q hω₀Q0 hfinv) hQ2

end

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
