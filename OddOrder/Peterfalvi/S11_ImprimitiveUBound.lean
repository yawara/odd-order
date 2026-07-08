/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_MaximalII_III_IV
import OddOrder.GroupTheory.RepresentationTheory.TypePGaloisUBound
import OddOrder.GroupTheory.RepresentationTheory.LineScalarCharacter
import OddOrder.GroupTheory.RepresentationTheory.AInvariantSubrep

/-!
# Peterfalvi (9.7)(a): the non-Galois imprimitive `u`-bound `u ≤ (p^q − 1)/(p − 1)`

The non-Galois branch of the `typeP_Galois` `u`-bound dichotomy (issue 9000, W2 instance tail).  When
the `U`-action on the chief factor `H̄ = H/N` is imprimitive (Clifford case (a), `CliffordCaseAData`),
`H̄` decomposes into `q` order-`p` blocks `Hpart i` permuted by `W₁`, and the image `Ū` embeds into
`ℤ_{p-1}^{q-1}` via the block-scalar ratios, giving `|Ū| ≤ (p-1)^{q-1} ≤ (p^q-1)/(p-1)`.

This routes the S11 case-(a) block data through the generic σ-theory engine
`card_le_cyclotomicQuotient_of_blocks` (`TypePGaloisUBound`), via the subgroup→subrepresentation
bridge `aInvariantSubrep`.  The only genuinely §9-specific input is the "no global scalar" injectivity
(Coq `psi`, `PFsection9.v:442`) — the Frobenius fixed-point-freeness of the `W̄₁`-action on `Ū` — left
as the `sorry` inside the block engine's `hconst` argument (see `notes/peterfalvi/s11_9_7a_imprimitive_ubound.md`).
-/

namespace OddOrder.Peterfalvi.S11

open OddOrder.RepresentationTheory OddOrder.GroupTheory OddOrder.Isaacs.Ch03
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **Block scalars all equal ⟹ the representation acts by that single scalar.**  If `u` acts by the
same scalar `μ ∈ 𝔽_p^×` on every line `B i` of a family of subrepresentations whose submodules span
the whole space, then `ρ u = μ • id`.  (Two linear maps agreeing on a spanning family are equal;
`lineScalarChar_smul` gives the per-block agreement `ρ u x = μ • x`.)  The additive core of the
imprimitive `psi` injectivity: "no common scalar except the trivial one" then reduces to `μ = 1`. -/
theorem representation_eq_smul_id_of_block_scalars_const {p : ℕ} [Fact p.Prime] {U V : Type*}
    [Group U] [AddCommGroup V] [Module (ZMod p) V] (ρ : Representation (ZMod p) U V)
    {ι : Type*} (B : ι → Subrepresentation ρ)
    (hBline : ∀ i, Module.finrank (ZMod p) (B i).toSubmodule = 1)
    (hspan : ⨆ i, (B i).toSubmodule = ⊤) (u : U) (μ : (ZMod p)ˣ)
    (hconst : ∀ i, lineScalarChar (B i).toRepresentation (hBline i) u = μ) :
    ρ u = (μ : ZMod p) • LinearMap.id := by
  have hblock : ∀ i, ∀ x ∈ (B i).toSubmodule, ρ u x = (μ : ZMod p) • x := by
    intro i x hx
    have hs := lineScalarChar_smul (B i).toRepresentation (hBline i) u ⟨x, hx⟩
    rw [hconst i] at hs
    have hv := congrArg Subtype.val hs
    simpa [Subrepresentation.toRepresentation] using hv
  refine LinearMap.ext_on (s := ⋃ i, ((B i).toSubmodule : Set V)) ?_ ?_
  · rw [← Submodule.iSup_eq_span, hspan]
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rw [hblock i x hi, LinearMap.smul_apply, LinearMap.id_apply]

/-- Invariance under a hom `φ` transfers to invariance under the range inclusion `φ.range.subtype`:
`Ū = φ.range` acts by the same automorphisms as the image of `φ`, so a `φ`-invariant subgroup is
`Ū`-invariant. -/
theorem isAInvariant_range_subtype {A K : Type*} [Group A] [Group K] {φ : A →* MulAut K}
    {J : Subgroup K} (hJ : IsAInvariant φ J) :
    IsAInvariant (MonoidHom.range φ).subtype J := by
  rw [isAInvariant_iff_smul_mem]
  rintro ⟨_, a, rfl⟩ g hg
  exact hJ.smul_mem a hg

/-- **The `U`-action image `Ū = (uActionHom).range` is abelian.**  A commutator `⁅a, b⁆ ∈ [U, U]`
centralizes `H` (Peterfalvi (8.5.b), `typeP_commutator_U_centralizes_H`), so acts trivially on `H̄`,
i.e. `uActionHom ⁅a, b⁆ = 1`; hence the images `uActionHom a`, `uActionHom b` commute. -/
theorem uActionHom_range_comm [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    (chief : ChiefFactorData data) (s t : ↥(MonoidHom.range (uActionHom data chief))) :
    s * t = t * s := by
  haveI : chief.N.Normal := chief.N_normal
  set act := typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant with hact
  -- `uActionHom = act.φ.comp act.U.subtype` definitionally; work through `φU` to match its domain.
  set φU := act.φ.comp act.U.subtype with hφU
  have hcentral_triv : ∀ g : ↥(data.typeP.U ⊔ data.typeP.W1),
      (g : G) ∈ Subgroup.centralizer (data.typeP.H : Set G) → act.φ g = 1 := by
    intro g hg
    have hfix : ∀ x : ↥data.typeP.H, (typeP_conjAction data.typeP g) x = x := by
      intro x
      apply Subtype.ext
      rw [typeP_conjAction_apply]
      have hcom : (x : G) * (g : G) = (g : G) * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp hg) (x : G) x.2
      rw [← hcom, mul_assoc, mul_inv_cancel, mul_one]
    ext y
    refine QuotientGroup.induction_on y ?_
    intro x
    show (act.φ g) (QuotientGroup.mk' chief.N x) = QuotientGroup.mk' chief.N x
    have hstep : (act.φ g) (QuotientGroup.mk' chief.N x)
        = QuotientGroup.mk' chief.N ((typeP_conjAction data.typeP g) x) := rfl
    rw [hstep, hfix x]
  have hComm : ∀ a b : ↥act.U, Commute (φU a) (φU b) := by
    intro a b
    refine commutatorElement_eq_one_iff_commute.mp ?_
    rw [← map_commutatorElement φU a b]
    show act.φ (act.U.subtype ⁅a, b⁆) = 1
    apply hcentral_triv
    change ((data.typeP.U ⊔ data.typeP.W1).subtype.comp act.U.subtype) ⁅a, b⁆
        ∈ Subgroup.centralizer (data.typeP.H : Set G)
    rw [map_commutatorElement]
    exact typeP_commutator_U_centralizes_H data.typeP
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2))
  obtain ⟨_, a, rfl⟩ := s
  obtain ⟨_, b, rfl⟩ := t
  exact Subtype.ext (hComm a b)

open scoped Classical in
/-- **Peterfalvi (9.7.a): the imprimitive `u`-bound** `u ≤ (p^q − 1)/(p − 1)`.  From the case-(a)
Clifford block data (`CliffordCaseAData`), the image `Ū = U/C_U(H̄)` embeds into `ℤ_{p-1}^{q-1}` via
the block scalars, bounding `|Ū| = u`.  Discharges the `hReducible` branch of
`card_le_cyclotomicQuotient_of_faithful_fpf`, hence `basic_structure.u_bound` (issue 9000). -/
theorem caseA_u_le_cyclotomicQuotient [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    (caseA : CliffordCaseAData chars) :
    chars.u ≤ (chief.p ^ data.q - 1) / (chief.p - 1) := by
  haveI : Fact chief.p.Prime := ⟨chief.p_prime⟩
  haveI : chief.N.Normal := chief.N_normal
  -- `CommGroup H̄` and `CommGroup Ū` built over the *canonical* `Group` instances (via an explicit
  -- `inferInstance` base, not `set`-folded locals), so the `MulAut H̄` of `uActionHom`/`Ubar.subtype`
  -- and the ones `elabRepresentation`/the block engine expect agree with no instance diamond.
  letI : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := chief.quotient_elementaryAbelian.comm }
  letI : Module (ZMod chief.p) (Additive (↥data.H ⧸ chief.N)) :=
    chief.quotient_elementaryAbelian.zmodModule
  haveI : Finite ↥(MonoidHom.range (uActionHom data chief)) := inferInstance
  letI : CommGroup ↥(MonoidHom.range (uActionHom data chief)) :=
    { (inferInstance : Group ↥(MonoidHom.range (uActionHom data chief))) with
      mul_comm := uActionHom_range_comm chief }
  have hq1 : (data.q - 1) + 1 = data.q := Nat.sub_add_cancel data.nontrivial.2.1.pos
  -- apply the generic block engine at `n = q - 1`, reindexing `Fin q ≃ Fin ((q-1)+1)`
  have hbound : Nat.card ↥(MonoidHom.range (uActionHom data chief))
      ≤ (chief.p ^ ((data.q - 1) + 1) - 1) / (chief.p - 1) :=
    card_le_cyclotomicQuotient_of_blocks (p := chief.p) (n := data.q - 1)
      (elabRepresentation chief.p (MonoidHom.range (uActionHom data chief)).subtype)
      (fun i => aInvariantSubrep
        (isAInvariant_range_subtype (caseA.Hpart_aInvariant (finCongr hq1 i))))
      (fun i => (card_aInvariantSubrep _).trans (caseA.Hpart_order (finCongr hq1 i)))
      -- **hconst — the genuine §9 crux (Coq `psi` injectivity, `PFsection9.v:442-484`)**: no
      -- nonidentity `ū ∈ Ū` acts by one common scalar on every block.  A common scalar makes
      -- `ū = λ·(-)` central in `MulAut(H̄)`, hence `W̄₁`-conjugation-invariant, so `ū ∈ C_Ū(W̄₁) = 1`
      -- by the Frobenius `(U ⊔ W₁)/C = Ū ⋊ W̄₁` (`typeP_uW1_frobenius`).  The whole bound reduces to
      -- this one fact; see `notes/peterfalvi/s11_9_7a_imprimitive_ubound.md`.
      (fun u _hscal => by sorry)
  rw [hq1] at hbound
  rw [chars.u_eq_card_quotient]
  exact hbound

end OddOrder.Peterfalvi.S11
