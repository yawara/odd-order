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

The non-Galois branch of the `typeP_Galois` `u`-bound dichotomy (issue 9000, W2 instance tail).
When
the `U`-action on the chief factor `H̄ = H/N` is imprimitive (Clifford case (a),
`CliffordCaseAData`),
`H̄` decomposes into `q` order-`p` blocks `Hpart i` permuted by `W₁`, and the image `Ū` embeds into
`ℤ_{p-1}^{q-1}` via the block-scalar ratios, giving `|Ū| ≤ (p-1)^{q-1} ≤ (p^q-1)/(p-1)`.

This routes the S11 case-(a) block data through the generic σ-theory engine
`card_le_cyclotomicQuotient_of_blocks` (`TypePGaloisUBound`), via the subgroup→subrepresentation
bridge `aInvariantSubrep`. The only genuinely §9-specific input is the "no global scalar"
injectivity
(Coq `psi`, `PFsection9.v:442`) — the Frobenius fixed-point-freeness of the `W̄₁`-action on `Ū` —
proved below by turning a common block scalar into a central automorphism and applying the descended
Frobenius action (see `notes/peterfalvi/s11_9_7a_imprimitive_ubound.md`).
-/

namespace OddOrder.Peterfalvi.S11

open OddOrder.RepresentationTheory OddOrder.GroupTheory OddOrder.Isaacs.Ch03
open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk')
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

/-- **A pointwise global `ZMod p`-scalar is central in `MulAut`.**  If `l` acts on every element as
the scalar `μ`, then `φ l` commutes with every automorphism of `V`: automorphisms are additive maps,
and additive maps commute with `ZMod p`-scalar multiplication (`ZMod.map_smul`). -/
theorem commute_mulAut_of_elabRepresentation_apply_eq_smul {p : ℕ} {L V : Type*} [Group L]
    [CommGroup V] [Module (ZMod p) (Additive V)] (φ : L →* MulAut V) (l : L) (μ : ZMod p)
    (happly : ∀ x : V, Additive.ofMul ((φ l) x) = μ • Additive.ofMul x) (σ : MulAut V) :
    Commute σ (φ l) := by
  have : σ * (φ l) = (φ l) * σ := by
    refine MulEquiv.ext fun x => ?_
    change σ ((φ l) x) = (φ l) (σ x)
    calc σ ((φ l) x)
        = Additive.toMul ((MulEquiv.toAdditive σ) (Additive.ofMul ((φ l) x))) := rfl
      _ = Additive.toMul ((MulEquiv.toAdditive σ) (μ • Additive.ofMul x)) := by rw [happly]
      _ = Additive.toMul (μ • (MulEquiv.toAdditive σ) (Additive.ofMul x)) := by
          rw [ZMod.map_smul]
      _ = Additive.toMul (μ • Additive.ofMul (σ x)) := rfl
      _ = Additive.toMul (Additive.ofMul ((φ l) (σ x))) := by rw [← happly]
      _ = (φ l) (σ x) := rfl
  exact this

/-- **A global `ZMod p`-scalar is central in `MulAut`.**  Linear-map form of
`commute_mulAut_of_elabRepresentation_apply_eq_smul`. -/
theorem commute_mulAut_of_elabRepresentation_eq_smul_id {p : ℕ} {L V : Type*} [Group L]
    [CommGroup V] [Module (ZMod p) (Additive V)] (φ : L →* MulAut V) (l : L) (μ : ZMod p)
    (h : elabRepresentation p φ l = μ • LinearMap.id) (σ : MulAut V) :
    Commute σ (φ l) := by
  apply commute_mulAut_of_elabRepresentation_apply_eq_smul φ l μ ?_ σ
  intro x
  have hx := LinearMap.congr_fun h (Additive.ofMul x)
  rwa [LinearMap.smul_apply, LinearMap.id_apply, elabRepresentation_apply] at hx

/-- Unfolding `uActionHom` along the conjugation action of `L = U ⊔ W₁` on its normal subgroup
`U`: the action of a conjugate is the conjugate of the actions. -/
theorem uActionHom_conjNormal [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    (chief : ChiefFactorData data)
    [(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal]
    (l : ↥(data.typeP.U ⊔ data.typeP.W1))
    (x : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) :
    haveI : chief.N.Normal := chief.N_normal
    uActionHom data chief (MulAut.conjNormal l x)
      = quotientMulAutHom (N := chief.N) chief.N_aInvariant l
        * uActionHom data chief x
        * (quotientMulAutHom (N := chief.N) chief.N_aInvariant l)⁻¹ := by
  haveI : chief.N.Normal := chief.N_normal
  have hval : ((MulAut.conjNormal l x :
        ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) :
        ↥(data.typeP.U ⊔ data.typeP.W1))
      = l * (x : ↥(data.typeP.U ⊔ data.typeP.W1)) * l⁻¹ := MulAut.conjNormal_apply l x
  calc uActionHom data chief (MulAut.conjNormal l x)
      = quotientMulAutHom (N := chief.N) chief.N_aInvariant
          ((MulAut.conjNormal l x :
            ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) :
            ↥(data.typeP.U ⊔ data.typeP.W1)) := rfl
    _ = quotientMulAutHom (N := chief.N) chief.N_aInvariant
          (l * (x : ↥(data.typeP.U ⊔ data.typeP.W1)) * l⁻¹) := by rw [hval]
    _ = _ := by rw [map_mul, map_mul, map_inv]; rfl

/-- **The Frobenius fixed-point-freeness eliminates global scalars** (the multiplicative half of
the Coq `psi` injectivity, `PFsection9.v:442-484`).  If `g ∈ U` acts on the chief factor `H̄` by an
automorphism *central in `Aut(H̄)`* — e.g. a scalar power map — then it acts trivially.

Centrality makes the action of `g` invariant under `W̄₁`-conjugation, so the image `ḡ ∈ Ū = U/C`
lies in `C_Ū(W̄₁)`; the coprime fixed-point descent (Isaacs Cor 3.28,
`map_fixedSubgroup_eq_fixedSubgroup_quotient`) identifies `C_Ū(W̄₁)` with the image of `C_U(W₁)`,
which is trivial by the Frobenius fixed-point-freeness of `(U ⊔ W₁, U, W₁)`
(`typeP_uW1_frobenius`).  Hence `ḡ = 1`, i.e. `uActionHom g = 1`. -/
theorem uActionHom_eq_one_of_commute_mulAut [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (g : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
    (hcentral : ∀ σ : MulAut (↥data.H ⧸ chief.N), Commute (uActionHom data chief g) σ) :
    uActionHom data chief g = 1 := by
  haveI : chief.N.Normal := chief.N_normal
  have frob := typeP_uW1_frobenius data.typeP data.nontrivial.1
  haveI hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal := frob.isNormal
  -- The kernel `C = C_U(H̄)` of the `U`-action is invariant under `L`-conjugation.
  have hNinv : IsAInvariant
      (MulAut.conjNormal :
        ↥(data.typeP.U ⊔ data.typeP.W1)
          →* MulAut ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (uActionHom data chief).ker := by
    rw [isAInvariant_iff_smul_mem]
    intro l x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [uActionHom_conjNormal chief l x, hx, mul_one, mul_inv_cancel]
  -- Coprimality `|W₁| ⟂ |U|` and solvability of the cyclic `W₁`.
  have hCop : Nat.Coprime
      (Nat.card ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (Nat.card ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) :=
    frob.coprime_card_kernel_complement.symm
  haveI hXcyc : IsCyclic ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) := by
    haveI := data.typeP.W1_cyclic
    exact isCyclic_of_surjective _
      (Subgroup.subgroupOfEquivOfLe le_sup_right).symm.surjective
  have hSolv : IsSolvable ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
      ∨ IsSolvable ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) := by
    left
    letI := hXcyc.commGroup
    infer_instance
  -- `C_U(W₁) = 1`: the Frobenius fixed-point-freeness.
  have hfixbot : fixedSubgroup
      (MulAut.conjNormal :
        ↥(data.typeP.U ⊔ data.typeP.W1)
          →* MulAut ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_fixedSubgroup] at hx
    rw [Subgroup.mem_bot]
    by_contra hxne
    obtain ⟨w, hwW1, hwne⟩ :=
      data.typeP.W1.bot_or_exists_ne_one.resolve_left data.typeP.W1_nontrivial
    have hŵX : (⟨w, Subgroup.mem_sup_right hwW1⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))
        ∈ data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) :=
      Subgroup.mem_subgroupOf.mpr hwW1
    have hvaleq : (⟨w, Subgroup.mem_sup_right hwW1⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))
          * (x : ↥(data.typeP.U ⊔ data.typeP.W1))
          * (⟨w, Subgroup.mem_sup_right hwW1⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))⁻¹
        = (x : ↥(data.typeP.U ⊔ data.typeP.W1)) := by
      have h := congrArg Subtype.val (hx _ hŵX)
      rwa [MulAut.conjNormal_apply] at h
    exact frob.conj_frobenius _ hŵX (fun h => hwne (congrArg Subtype.val h))
      (x : ↥(data.typeP.U ⊔ data.typeP.W1)) x.2
      (fun h => hxne (OneMemClass.coe_eq_one.mp h)) hvaleq
  -- Descend: `C_Ū(W̄₁)` is the image of `C_U(W₁) = 1`.
  have hmap := map_fixedSubgroup_eq_fixedSubgroup_quotient hNinv hCop hSolv
  rw [hfixbot, Subgroup.map_bot] at hmap
  -- `ḡ` is `W̄₁`-fixed: centrality makes each `W₁`-conjugate of `g` agree with `g` mod `C`.
  have hgfix : QuotientGroup.mk' (uActionHom data chief).ker g
      ∈ fixedSubgroup (quotientMulAutHom hNinv)
        (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) := by
    rw [mem_fixedSubgroup]
    intro l hl
    rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_eq_mk']
    refine ⟨(MulAut.conjNormal l g)⁻¹ * g, ?_, mul_inv_cancel_left _ _⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, uActionHom_conjNormal chief l g,
      ← (hcentral (quotientMulAutHom (N := chief.N) chief.N_aInvariant l)).eq,
      mul_inv_cancel_right, inv_mul_cancel]
  rw [← hmap, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hgfix
  exact hgfix

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
    change (act.φ g) (QuotientGroup.mk' chief.N x) = QuotientGroup.mk' chief.N x
    have hstep : (act.φ g) (QuotientGroup.mk' chief.N x)
        = QuotientGroup.mk' chief.N ((typeP_conjAction data.typeP g) x) := rfl
    rw [hstep, hfix x]
  have hComm : ∀ a b : ↥act.U, Commute (φU a) (φU b) := by
    intro a b
    refine commutatorElement_eq_one_iff_commute.mp ?_
    rw [← map_commutatorElement φU a b]
    change act.φ (act.U.subtype ⁅a, b⁆) = 1
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
/-- **Peterfalvi (9.7.a): the qualitative block-scalar product embedding.**  The faithful image
`Ū = U/C_U(H̄)` of the `U`-action embeds into the product of `q - 1` copies of
`(𝔽_p)ˣ`.  The homomorphism is the normalized scalar ratio
`ū ↦ (φ_{i+1}(ū) / φ_0(ū))_i` on the `q` order-`p` Clifford summands.

This exposes the actual injective group homomorphism behind `caseA_u_dvd_pred_pow`.  In
Peterfalvi (14.6), a Sylow subgroup is restricted along this map to obtain the qualitative
two-cyclic-factor structure; cardinality divisibility alone does not retain that information. -/
theorem caseA_exists_blockScalarRatioEmbedding [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    (caseA : CliffordCaseAData chars) :
    ∃ ψ : ↥(MonoidHom.range (uActionHom data chief)) →*
        (Fin (data.q - 1) → (ZMod chief.p)ˣ),
      Function.Injective ψ := by
  haveI : Fact chief.p.Prime := ⟨chief.p_prime⟩
  haveI : chief.N.Normal := chief.N_normal
  -- Build the vector-space structure over the canonical quotient-group instance, so the
  -- `MulAut H̄` used by `uActionHom` and by `elabRepresentation` agrees definitionally.
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
  refine exists_blockScalarRatioEmbedding_of_blocks (p := chief.p) (n := data.q - 1)
    (elabRepresentation chief.p (MonoidHom.range (uActionHom data chief)).subtype)
    (fun i => aInvariantSubrep
      (isAInvariant_range_subtype (caseA.Hpart_aInvariant (finCongr hq1 i))))
    (fun i => (card_aInvariantSubrep _).trans
      (caseA.Hpart_order (finCongr hq1 i))) ?_
  -- **The genuine §9 crux** (Coq `psi`, `PFsection9.v:442-484`): no nonidentity
  -- `ū ∈ Ū` acts by one common scalar on every block.
  intro u hscal
  let B := fun i : Fin ((data.q - 1) + 1) =>
    aInvariantSubrep (p := chief.p)
      (φ := (MonoidHom.range (uActionHom data chief)).subtype)
      (isAInvariant_range_subtype (caseA.Hpart_aInvariant (finCongr hq1 i)))
  let μ : (ZMod chief.p)ˣ := lineScalarChar (B 0).toRepresentation
    (finrank_eq_one_of_card_eq_prime
      ((card_aInvariantSubrep _).trans
        (caseA.Hpart_order (finCongr hq1 0)))) u
  have hscalB : ∀ i, lineScalarChar (B i).toRepresentation
      (finrank_eq_one_of_card_eq_prime
        ((card_aInvariantSubrep _).trans
          (caseA.Hpart_order (finCongr hq1 i)))) u = μ := by
    intro i
    simpa only [B, μ] using hscal i
  -- On each Clifford summand, the action is the common scalar `μ`.
  have hblock (i : Fin ((data.q - 1) + 1)) (x : ↥data.H ⧸ chief.N)
      (hx : x ∈ caseA.Hpart (finCongr hq1 i)) :
      (elabRepresentation chief.p
          (MonoidHom.range (uActionHom data chief)).subtype u).toFun
          (Additive.ofMul x) = (μ : ZMod chief.p) • Additive.ofMul x := by
    have hxB : Additive.ofMul x ∈
        (B i).toSubmodule.carrier := by
      have hm := (mem_symm_elabSubmoduleSubgroupEquiv (p := chief.p)
        (caseA.Hpart (finCongr hq1 i)) (Additive.ofMul x)).mpr (by simpa using hx)
      exact hm
    have hs := lineScalarChar_smul_coe_of_card_eq_prime
      (elabRepresentation chief.p
        (MonoidHom.range (uActionHom data chief)).subtype) (B i)
      ((card_aInvariantSubrep _).trans
        (caseA.Hpart_order (finCongr hq1 i))) u
      ⟨Additive.ofMul x, hxB⟩
    rw [hscalB i] at hs
    exact hs
  -- The summands span `H̄`; subgroup induction extends the scalar identity to every vector.
  have hpoint : ∀ x : ↥data.H ⧸ chief.N,
      (elabRepresentation chief.p
          (MonoidHom.range (uActionHom data chief)).subtype u).toFun
          (Additive.ofMul x) = (μ : ZMod chief.p) • Additive.ofMul x := by
    intro x
    have hre : ⨆ i : Fin ((data.q - 1) + 1), caseA.Hpart (finCongr hq1 i) = ⊤ := by
      rw [Equiv.iSup_comp (finCongr hq1) (g := caseA.Hpart)]
      exact caseA.Hpart_iSup
    have hx : x ∈ ⨆ i : Fin ((data.q - 1) + 1),
        caseA.Hpart (finCongr hq1 i) := hre ▸ Subgroup.mem_top x
    refine Subgroup.iSup_induction
      (C := fun z =>
        (elabRepresentation chief.p
            (MonoidHom.range (uActionHom data chief)).subtype u).toFun
            (Additive.ofMul z) = (μ : ZMod chief.p) • Additive.ofMul z)
      (fun i => caseA.Hpart (finCongr hq1 i)) hx hblock ?_ ?_
    · simpa using
        (elabRepresentation chief.p
          (MonoidHom.range (uActionHom data chief)).subtype u).map_zero
    · intro a b ha hb
      change
        (elabRepresentation chief.p
            (MonoidHom.range (uActionHom data chief)).subtype u).toFun
            (Additive.ofMul a + Additive.ofMul b)
          = (μ : ZMod chief.p) • (Additive.ofMul a + Additive.ofMul b)
      calc
        _ = (elabRepresentation chief.p
              (MonoidHom.range (uActionHom data chief)).subtype u).toFun (Additive.ofMul a)
            + (elabRepresentation chief.p
              (MonoidHom.range (uActionHom data chief)).subtype u).toFun
                (Additive.ofMul b) :=
            (elabRepresentation chief.p
              (MonoidHom.range (uActionHom data chief)).subtype u).map_add _ _
        _ = (μ : ZMod chief.p) • Additive.ofMul a
            + (μ : ZMod chief.p) • Additive.ofMul b := by rw [ha, hb]
        _ = (μ : ZMod chief.p) • (Additive.ofMul a + Additive.ofMul b) :=
            (smul_add _ _ _).symm
  -- A global scalar is central in `MulAut(H̄)`; Frobenius fpf forces `u = 1`.
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp u.2
  have hone : uActionHom data chief g = 1 :=
    uActionHom_eq_one_of_commute_mulAut chief g (fun σ => by
      rw [hg]
      exact (commute_mulAut_of_elabRepresentation_apply_eq_smul
        (MonoidHom.range (uActionHom data chief)).subtype u (μ : ZMod chief.p)
        (fun x => by simpa [elabRepresentation_apply] using hpoint x) σ).symm)
  exact Subtype.ext (hg ▸ hone)

open scoped Classical in
/-- **Peterfalvi (9.7.a): imprimitive block-scalar order divisibility.**  From the case-(a) Clifford
data, the image `Ū = U/C_U(H̄)` embeds as a subgroup of `((𝔽_p)ˣ)^{q-1}`; hence its order
`u = |Ū|` divides `(p - 1)^{q-1}`.  This strengthened form retains the odd-part information used
in Peterfalvi (13.13). -/
theorem caseA_u_dvd_pred_pow [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    (caseA : CliffordCaseAData chars) :
    chars.u ∣ (chief.p - 1) ^ (data.q - 1) := by
  haveI : Fact chief.p.Prime := ⟨chief.p_prime⟩
  obtain ⟨ψ, hψ⟩ := caseA_exists_blockScalarRatioEmbedding chars caseA
  have hunits : Nat.card (ZMod chief.p)ˣ = chief.p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime chief.p_prime]
  have hdiv := Subgroup.card_dvd_of_injective ψ hψ
  rw [Nat.card_pi, hunits] at hdiv
  have hu : chars.u = Nat.card ↥(uActionHom data chief).range :=
    chars.u_eq_card_quotient
  rw [hu]
  simpa using hdiv

/-- **Peterfalvi (9.7.a): the imprimitive `u`-bound** `u ≤ (p^q − 1)/(p − 1)`.  This is the
cardinality consequence of `caseA_u_dvd_pred_pow`, followed by the elementary cyclotomic bound
`(p - 1)^{q-1} ≤ (p^q - 1)/(p - 1)`. -/
theorem caseA_u_le_cyclotomicQuotient [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    (caseA : CliffordCaseAData chars) :
    chars.u ≤ (chief.p ^ data.q - 1) / (chief.p - 1) := by
  have hpow : 0 < (chief.p - 1) ^ (data.q - 1) :=
    pow_pos (Nat.sub_pos_of_lt chief.p_prime.one_lt) _
  have hle : chars.u ≤ (chief.p - 1) ^ (data.q - 1) :=
    Nat.le_of_dvd hpow (caseA_u_dvd_pred_pow chars caseA)
  exact hle.trans (pow_sub_one_le_cyclotomicQuotient (p := chief.p) (q := data.q)
    chief.p_prime.two_le data.nontrivial.2.1.one_le)

/-- **Peterfalvi (9.7): the `u`-bound `u ≤ (p^q − 1)/(p − 1)`, unconditionally.**  The Clifford
dichotomy (`chiefFactor_clifford_U_dichotomy`) splits the `U`-action on the chief factor `H̄`:

* **irreducible** (Galois, case (b)): the Singer-field cyclic bound gives the divisibility
  `u ∣ (p^q − 1)/(p − 1)` (`chiefFactor_caseB_image_dvd_norm`);
* **imprimitive** (case (a)): the block-scalar ratio embedding `Ū ↪ ℤ_{p-1}^{q-1}` gives
  `u ≤ (p−1)^{q−1} ≤ (p^q − 1)/(p − 1)` (`caseA_u_le_cyclotomicQuotient`, via the case-(a)
  carrier `clifford_caseA_data`).

This is the upstream fact behind Peterfalvi (13.2.c) `basic_structure.u_bound` (issue 9000):
the §13/§15 consumer instantiates `chars` for the type-P₂ member `S` and cites this bound. -/
theorem u_le_cyclotomicQuotient [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief) :
    chars.u ≤ (chief.p ^ data.q - 1) / (chief.p - 1) := by
  rcases chiefFactor_clifford_U_dichotomy chief with hcaseB | ⟨S₀, hS₀ne, hS₀inv, hS₀card, hirr₀⟩
  · -- Galois / irreducible (case (b)): the Singer divisibility bound, weakened to `≤`.
    have hdvd := chiefFactor_caseB_image_dvd_norm chief hcaseB
    have hpos : 0 < (chief.p ^ data.q - 1) / (chief.p - 1) := by
      have hp2 := chief.p_prime.two_le
      have hq1 : 1 ≤ data.q := data.nontrivial.2.1.pos
      have hle : chief.p ≤ chief.p ^ data.q := Nat.le_self_pow (by omega) _
      exact Nat.div_pos (by omega) (by omega)
    rw [chars.u_eq_card_quotient]
    exact Nat.le_of_dvd hpos hdvd
  · -- imprimitive (case (a)): the block-scalar bound through the case-(a) carrier.
    exact caseA_u_le_cyclotomicQuotient chars
      (clifford_caseA_data chars hS₀ne hS₀inv hS₀card hirr₀)

/-- **`C_Ū(W̄₁) = 1`** — the fixed subgroup of the `W₁`-conjugation on the descended `U`-action
quotient `Ū = U/C_U(H̄)` is trivial.  The coprime fixed-point descent (Isaacs Cor 3.28,
`map_fixedSubgroup_eq_fixedSubgroup_quotient`) identifies `C_Ū(W̄₁)` with the image of `C_U(W₁)`,
which is trivial by the Frobenius fixed-point-freeness of `(U ⊔ W₁, U, W₁)`
(`typeP_uW1_frobenius`).  Extracted from the `hconst`-side argument
(`uActionHom_eq_one_of_commute_mulAut`) so that the orbit-count congruence
`card_uActionHom_range_modEq_one` can consume the same fixed-point-freeness. -/
theorem fixedSubgroup_quotient_uActionKer_eq_bot [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal]
    (hNinv : IsAInvariant
      (MulAut.conjNormal :
        ↥(data.typeP.U ⊔ data.typeP.W1)
          →* MulAut ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (uActionHom data chief).ker) :
    fixedSubgroup (quotientMulAutHom hNinv)
      (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) = ⊥ := by
  haveI : chief.N.Normal := chief.N_normal
  have frob := typeP_uW1_frobenius data.typeP data.nontrivial.1
  -- Coprimality `|W₁| ⟂ |U|` and solvability of the cyclic `W₁`.
  have hCop : Nat.Coprime
      (Nat.card ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (Nat.card ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) :=
    frob.coprime_card_kernel_complement.symm
  haveI hXcyc : IsCyclic ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) := by
    haveI := data.typeP.W1_cyclic
    exact isCyclic_of_surjective _
      (Subgroup.subgroupOfEquivOfLe le_sup_right).symm.surjective
  have hSolv : IsSolvable ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
      ∨ IsSolvable ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) := by
    left
    letI := hXcyc.commGroup
    infer_instance
  -- `C_U(W₁) = 1`: the Frobenius fixed-point-freeness.
  have hfixbot : fixedSubgroup
      (MulAut.conjNormal :
        ↥(data.typeP.U ⊔ data.typeP.W1)
          →* MulAut ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_fixedSubgroup] at hx
    rw [Subgroup.mem_bot]
    by_contra hxne
    obtain ⟨w, hwW1, hwne⟩ :=
      data.typeP.W1.bot_or_exists_ne_one.resolve_left data.typeP.W1_nontrivial
    have hŵX : (⟨w, Subgroup.mem_sup_right hwW1⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))
        ∈ data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) :=
      Subgroup.mem_subgroupOf.mpr hwW1
    have hvaleq : (⟨w, Subgroup.mem_sup_right hwW1⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))
          * (x : ↥(data.typeP.U ⊔ data.typeP.W1))
          * (⟨w, Subgroup.mem_sup_right hwW1⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))⁻¹
        = (x : ↥(data.typeP.U ⊔ data.typeP.W1)) := by
      have h := congrArg Subtype.val (hx _ hŵX)
      rwa [MulAut.conjNormal_apply] at h
    exact frob.conj_frobenius _ hŵX (fun h => hwne (congrArg Subtype.val h))
      (x : ↥(data.typeP.U ⊔ data.typeP.W1)) x.2
      (fun h => hxne (OneMemClass.coe_eq_one.mp h)) hvaleq
  -- Descend: `C_Ū(W̄₁)` is the image of `C_U(W₁) = 1`.
  have hmap := map_fixedSubgroup_eq_fixedSubgroup_quotient hNinv hCop hSolv
  rw [hfixbot, Subgroup.map_bot] at hmap
  exact hmap.symm

/-- **The `W₁`-orbit congruence `u ≡ 1 (mod q)`** (Coq `Frobenius_dvd_ker1 frobUW1bar`,
`PFsection11.v:1190`).  The `W₁`-conjugation on the `U`-action image `Ū = U/C_U(H̄)` is
fixed-point-free (`fixedSubgroup_quotient_uActionKer_eq_bot`), so the prime-order `W₁` partitions
`Ū \ {1}` into orbits of size `q = |W₁|`, giving `|Ū| ≡ 1 (mod q)`.

This is the `q ∣ u − 1` input of the Peterfalvi (11.9.c) non-Galois contradiction
`q ≤ u − 1 < u = a ≤ p − 1 < p` against (11.9.b) `p < q` (issue 1024). -/
theorem card_uActionHom_range_modEq_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    Nat.card ↥(MonoidHom.range (uActionHom data chief)) ≡ 1 [MOD data.q] := by
  classical
  haveI : chief.N.Normal := chief.N_normal
  have frob := typeP_uW1_frobenius data.typeP data.nontrivial.1
  haveI hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal := frob.isNormal
  -- The kernel `C = C_U(H̄)` of the `U`-action is invariant under `L`-conjugation.
  have hNinv : IsAInvariant
      (MulAut.conjNormal :
        ↥(data.typeP.U ⊔ data.typeP.W1)
          →* MulAut ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (uActionHom data chief).ker := by
    rw [isAInvariant_iff_smul_mem]
    intro l x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [uActionHom_conjNormal chief l x, hx, mul_one, mul_inv_cancel]
  set W₁sub := data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) with hW₁sub
  set Q := (↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
    ⧸ (uActionHom data chief).ker) with hQdef
  -- `W₁` acts on the quotient `Q = U/C` through the descended conjugation.
  letI : MulAction ↥W₁sub Q :=
    MulAction.compHom Q ((quotientMulAutHom hNinv).comp W₁sub.subtype)
  have hsmul : ∀ (w : ↥W₁sub) (x : Q), w • x = quotientMulAutHom hNinv (w : _) x := fun _ _ => rfl
  -- The fixed points are exactly `C_Ū(W̄₁) = 1`.
  have hfix : MulAction.fixedPoints ↥W₁sub Q = ({1} : Set Q) := by
    have hbot := fixedSubgroup_quotient_uActionKer_eq_bot chief hNinv
    ext x
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro h
      have hx : x ∈ fixedSubgroup (quotientMulAutHom hNinv) W₁sub := by
        rw [mem_fixedSubgroup]
        intro l hl
        have := h ⟨l, hl⟩
        rwa [hsmul] at this
      rwa [hbot, Subgroup.mem_bot] at hx
    · rintro rfl w
      rw [hsmul]
      exact map_one (quotientMulAutHom hNinv (w : _))
  -- `W₁sub` is a `q`-group of order exactly `q` (prime).
  haveI : Fact (data.q).Prime := ⟨data.nontrivial.2.1⟩
  have hW1card : Nat.card ↥W₁sub = data.q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hPG : IsPGroup data.q ↥W₁sub := IsPGroup.of_card (by rw [hW1card, pow_one])
  -- Orbit count: `|Q| ≡ |fixedPoints| = 1 (mod q)`.
  have hmod := hPG.card_modEq_card_fixedPoints Q
  have hfixcard : Nat.card (MulAction.fixedPoints ↥W₁sub Q) = 1 := by
    rw [hfix]
    exact Nat.card_unique
  rw [hfixcard] at hmod
  -- Transport along `Q ≅ Ū` (first isomorphism theorem).
  have hQcard : Nat.card Q = Nat.card ↥(MonoidHom.range (uActionHom data chief)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (uActionHom data chief)).toEquiv
  rwa [hQcard] at hmod

/-! ### The scalar-character ↔ restricted-automorphism order bridge (Peterfalvi (9.7.a), issue
1043)

The Clifford integer `a` of `CliffordCaseAData` is pinned as the order of the *automorphism* image
`|range (aInvariantRestrictAut S0_aInvariant)|`, while the (9.7.a) order-`a` ratio embedding
(`exists_blockScalarRatioEmbedding_of_blocks_pow_eq_one`, `TypePGaloisUBound`) consumes the order
of the *module scalar* image `|range (lineScalarChar (aInvariantSubrep …))|`.  These agree: the two
homomorphisms have the same domain and the **same kernel** — both kernels are "acts trivially on
the block" — so the first isomorphism theorem identifies the range cardinalities. -/

/-- **Triviality criterion for the restricted automorphism**: `aInvariantRestrictAut hS a = 1` iff
`a` fixes `S` pointwise (through `φ`). -/
theorem aInvariantRestrictAut_eq_one_iff {K A : Type*} [Group K] [Group A] {φ : A →* MulAut K}
    {S : Subgroup K} (hS : IsAInvariant φ S) (a : A) :
    aInvariantRestrictAut hS a = 1 ↔ ∀ x ∈ S, φ a x = x := by
  constructor
  · intro h x hx
    have hy := aInvariantRestrictAut_coe hS a ⟨x, hx⟩
    rw [h] at hy
    simpa using hy.symm
  · intro h
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [aInvariantRestrictAut_coe]
    exact h y y.2

/-- **Kernel agreement**: on an order-`p` (`𝔽_p`-line) invariant block `J`, the line scalar
character of the associated subrepresentation and the restricted automorphism hom have the same
kernel — both are "acts trivially on `J`" (`lineScalarChar_eq_one_iff` on the module side,
`aInvariantRestrictAut_eq_one_iff` on the group side, matched through `elabRepresentation`). -/
theorem lineScalarChar_aInvariantSubrep_ker_eq {A K : Type*} [Group A] [CommGroup K]
    {p : ℕ} [Fact p.Prime] [Module (ZMod p) (Additive K)] {φ : A →* MulAut K}
    {J : Subgroup K} (hJ : IsAInvariant φ J)
    (hdim : Module.finrank (ZMod p)
      (aInvariantSubrep (p := p) hJ).toSubmodule = 1) :
    (lineScalarChar (aInvariantSubrep (p := p) hJ).toRepresentation hdim).ker
      = (aInvariantRestrictAut hJ).ker := by
  ext a
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, lineScalarChar_eq_one_iff,
    aInvariantRestrictAut_eq_one_iff]
  constructor
  · intro h x hx
    have hv := congrArg Subtype.val
      (h ⟨Additive.ofMul x, (mem_symm_elabSubmoduleSubgroupEquiv J _).mpr hx⟩)
    have hv' : elabRepresentation p φ a (Additive.ofMul x) = Additive.ofMul x := hv
    rw [elabRepresentation_apply] at hv'
    exact Additive.ofMul.injective hv'
  · intro h v
    refine Subtype.ext ?_
    have hv : elabRepresentation p φ a (v : Additive K) = (v : Additive K) := by
      have hmem : Additive.toMul (v : Additive K) ∈ J :=
        (mem_symm_elabSubmoduleSubgroupEquiv J _).mp v.2
      calc elabRepresentation p φ a (v : Additive K)
          = elabRepresentation p φ a (Additive.ofMul (Additive.toMul (v : Additive K))) := rfl
        _ = Additive.ofMul (φ a (Additive.toMul (v : Additive K))) :=
            elabRepresentation_apply p φ a _
        _ = Additive.ofMul (Additive.toMul (v : Additive K)) := by rw [h _ hmem]
        _ = (v : Additive K) := rfl
    exact hv

/-- **Order bridge** (Peterfalvi (9.7.a), issue 1043 step 1): the image of the line scalar
character on an invariant `𝔽_p`-line block has the same cardinality as the image of the restricted
automorphism hom — first isomorphism theorem over the kernel agreement
`lineScalarChar_aInvariantSubrep_ker_eq`.  Instantiated at `J = S0` this pins the scalar-character
image order to the Clifford integer `a` (`CliffordCaseAData.a_eq_card_restrictAut_range`). -/
theorem card_range_lineScalarChar_aInvariantSubrep {A K : Type*} [Group A] [CommGroup K]
    {p : ℕ} [Fact p.Prime] [Module (ZMod p) (Additive K)] {φ : A →* MulAut K}
    {J : Subgroup K} (hJ : IsAInvariant φ J)
    (hdim : Module.finrank (ZMod p)
      (aInvariantSubrep (p := p) hJ).toSubmodule = 1) :
    Nat.card (lineScalarChar (aInvariantSubrep (p := p) hJ).toRepresentation hdim).range
      = Nat.card (aInvariantRestrictAut hJ).range := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (lineScalarChar (aInvariantSubrep (p := p) hJ).toRepresentation hdim)).toEquiv,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (aInvariantRestrictAut hJ)).toEquiv,
    lineScalarChar_aInvariantSubrep_ker_eq hJ hdim]

/-! ### Orbit transport of the block image order (Peterfalvi (9.7.a), issue 1043 step 2)

Peterfalvi p. 51: "As `H_i` is conjugate to `H₁` under `W₁`, `|U/C_U(H_i)| = a`."  The summands
are the `UW₁`-translates `Hpart j = q(orbitRep j) • S₀` (`CliffordCaseAData.Hpart_orbit`), and
`U ⊴ UW₁` (the Frobenius kernel, `typeP_uW1_frobenius`), so conjugating the acting element by
`orbitRep j` intertwines the restricted actions on `S₀` and on `Hpart j`; the two restriction
homs then differ by precomposition with a `MulAut` of the domain, leaving the kernel cardinality
— hence the image cardinality — unchanged. -/

section OrbitTransport

variable [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
  {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}

omit [Finite G] in
/-- **All Clifford summands have image order `a`** (Peterfalvi (9.7.a), "`U/C_U(H_i)` is ... of
order `a` for all `i`"): the `U`-action image on every block `Hpart j` has the cardinality of the
image on the orbit generator `S₀` — the Clifford integer `caseA.a`. -/
theorem caseA_card_range_restrictAut_Hpart (caseA : CliffordCaseAData chars) (j : Fin data.q) :
    Nat.card (aInvariantRestrictAut (caseA.Hpart_aInvariant j)).range = caseA.a := by
  classical
  haveI hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal :=
    (typeP_uW1_frobenius data.typeP data.nontrivial.1).isNormal
  set Γ := ↥(data.typeP.U ⊔ data.typeP.W1)
  set q' : Γ →* MulAut (↥data.H ⧸ chief.N) := quotientMulAutHom chief.N_aInvariant with hq'
  set r : Γ := caseA.orbitRep j with hr
  -- conjugation of the (normal) `U`-part domain by `r⁻¹`
  set c : MulAut ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    MulAut.conjNormal r⁻¹ with hc
  set f₁ := aInvariantRestrictAut (caseA.Hpart_aInvariant j) with hf₁
  set f₀ := aInvariantRestrictAut caseA.S0_aInvariant with hf₀
  set g := f₀.comp c.toMonoidHom with hg
  -- the acting automorphism of the conjugated element: `q'(ι(c u)) = q'(r)⁻¹ ∘ q'(ι u) ∘ q'(r)`
  have hact : ∀ u : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)),
      ∀ z : ↥data.H ⧸ chief.N,
      uActionHom data chief (c u) z = (q' r)⁻¹ (uActionHom data chief u (q' r z)) := by
    intro u z
    have hcoe : ((c u : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) : Γ)
        = r⁻¹ * (u : Γ) * r := by
      rw [hc, MulAut.conjNormal_apply, inv_inv]
    have : uActionHom data chief (c u) = q' (r⁻¹ * (u : Γ) * r) := by
      rw [uActionHom, MonoidHom.comp_apply]
      exact congrArg q' hcoe
    rw [this, map_mul, map_mul, map_inv]
    rfl
  -- kernels agree: both are "acts trivially on the translated block"
  have hker : f₁.ker = g.ker := by
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hg, MonoidHom.comp_apply, hf₁, hf₀,
      aInvariantRestrictAut_eq_one_iff, aInvariantRestrictAut_eq_one_iff]
    simp only [MulEquiv.coe_toMonoidHom]
    constructor
    · intro h y hy
      rw [hact u y]
      have hmem : q' r y ∈ caseA.Hpart j := by
        rw [caseA.Hpart_orbit j]
        exact Subgroup.smul_mem_pointwise_smul y (q' r) caseA.S0 hy
      rw [h _ hmem]
      exact (q' r).symm_apply_apply y
    · intro h x hx
      have hy : (q' r)⁻¹ x ∈ caseA.S0 := by
        rw [caseA.Hpart_orbit j] at hx
        exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hx
      have := h _ hy
      rw [hact u ((q' r)⁻¹ x)] at this
      have hxx : q' r ((q' r)⁻¹ x) = x := (q' r).apply_symm_apply x
      rw [hxx] at this
      exact (q' r)⁻¹.injective (by rw [this])
  -- first isomorphism theorem: equal kernels ⟹ equal image cardinalities
  have h1 : Nat.card f₁.range = Nat.card g.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f₁).toEquiv,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hker]
  -- precomposition with the domain automorphism does not change the range
  have h2 : g.range = f₀.range := by
    rw [hg, MonoidHom.range_comp]
    have : c.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr c.surjective
    rw [this]
    exact (MonoidHom.range_eq_map f₀).symm
  rw [h1, h2, ← caseA.a_eq_card_restrictAut_range]

end OrbitTransport

/-! ### The (9.7.a) order-`a` embedding (issue 1043 step 3)

Assembly: the block image orders pin `exp(Ū) ∣ a` (each block scalar has order dividing `a`, the
blocks span `H̄`, and `Ū` acts faithfully), and then **any** hom out of `Ū` — in particular the
ratio embedding of `caseA_exists_blockScalarRatioEmbedding` — automatically has `a`-torsion
values.  This realizes the book's "`Ū` is isomorphic to a subgroup of the direct product of
`q − 1` cyclic groups of order `a`" (p. 51) without re-running the `psi` injectivity crux. -/

section OrderAEmbedding

variable [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
  {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}

/-- Values of a homomorphism out of a finite group are killed by the image order:
`(f g) ^ |range f| = 1`. -/
theorem pow_card_range_eq_one {G' H' : Type*} [Group G'] [Group H'] [Finite H']
    (f : G' →* H') (g : G') : f g ^ Nat.card f.range = 1 := by
  have h := pow_card_eq_one' (G := f.range) (x := ⟨f g, ⟨g, rfl⟩⟩)
  have hval := congrArg Subtype.val h
  simpa using hval

/-- **Range invariance under the range-subtype re-basing**: restricting the action of the image
group `Ū = range φ` (through the inclusion) to an invariant block has the same automorphism range
as restricting the `φ`-action itself — `aInvariantRestrictAut` over `(range φ).subtype` at
`⟨φ a, _⟩` *is* `aInvariantRestrictAut` over `φ` at `a`. -/
theorem aInvariantRestrictAut_range_subtype_range_eq {A K : Type*} [Group A] [Group K]
    {φ : A →* MulAut K} {J : Subgroup K} (hJ : IsAInvariant φ J) :
    (aInvariantRestrictAut (isAInvariant_range_subtype hJ)).range
      = (aInvariantRestrictAut hJ).range := by
  have happ : ∀ a : A,
      aInvariantRestrictAut (isAInvariant_range_subtype hJ) ⟨φ a, ⟨a, rfl⟩⟩
        = aInvariantRestrictAut hJ a := by
    intro a
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [aInvariantRestrictAut_coe, aInvariantRestrictAut_coe]
    rfl
  ext f
  constructor
  · rintro ⟨⟨_, a, rfl⟩, rfl⟩
    exact ⟨a, (happ a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨φ a, ⟨a, rfl⟩⟩, happ a⟩

/-- **The Clifford integer kills `Ū`** (Peterfalvi (9.7.a)): `u ^ a = 1` for every
`u ∈ Ū = range (uActionHom)`.  Each block scalar has order dividing `a`
(`caseA_card_range_restrictAut_Hpart` + Lagrange), so `u ^ a` fixes every Clifford summand
pointwise; the summands span `H̄` (`Hpart_iSup`), and `Ū` acts faithfully (it *is* a subgroup of
`MulAut H̄`).  This is the exponent form of the book's embedding into `q − 1` cyclic groups of
order `a`. -/
theorem caseA_pow_a_eq_one (caseA : CliffordCaseAData chars)
    (u : ↥(MonoidHom.range (uActionHom data chief))) : u ^ caseA.a = 1 := by
  classical
  -- `u ^ a` fixes each summand pointwise
  have hblock : ∀ i : Fin data.q, ∀ x ∈ caseA.Hpart i,
      ((MonoidHom.range (uActionHom data chief)).subtype (u ^ caseA.a)) x = x := by
    intro i
    have hcard : Nat.card (aInvariantRestrictAut
        (isAInvariant_range_subtype (caseA.Hpart_aInvariant i))).range = caseA.a := by
      rw [aInvariantRestrictAut_range_subtype_range_eq (caseA.Hpart_aInvariant i),
        caseA_card_range_restrictAut_Hpart]
    have hone : aInvariantRestrictAut (isAInvariant_range_subtype (caseA.Hpart_aInvariant i))
        (u ^ caseA.a) = 1 := by
      rw [map_pow, ← hcard]
      exact pow_card_range_eq_one _ u
    exact (aInvariantRestrictAut_eq_one_iff _ _).mp hone
  -- the fixed locus is a subgroup; it contains every summand, hence `⊤`
  have htop : ∀ x : ↥data.H ⧸ chief.N,
      ((MonoidHom.range (uActionHom data chief)).subtype (u ^ caseA.a)) x = x := by
    have hle : (⊤ : Subgroup (↥data.H ⧸ chief.N)) ≤ MonoidHom.eqLocus
        ((MonoidHom.range (uActionHom data chief)).subtype
          (u ^ caseA.a) : MulAut (↥data.H ⧸ chief.N)).toMonoidHom
        (MonoidHom.id (↥data.H ⧸ chief.N)) := by
      rw [← caseA.Hpart_iSup]
      refine iSup_le fun i x hx => ?_
      exact hblock i x hx
    intro x
    exact hle (Subgroup.mem_top x)
  -- faithfulness: the subgroup inclusion into `MulAut H̄` is injective
  refine Subtype.ext ?_
  refine MulEquiv.ext fun x => ?_
  exact htop x

/-- **Peterfalvi (9.7.a), the order-`a` block-scalar ratio embedding** (issue 1043): `Ū` embeds
into `q − 1` copies of `(ZMod p)ˣ` with all component values killed by `a` — i.e. into the direct
product of `q − 1` copies of the unique **cyclic subgroup of order `a`** of `(ZMod p)ˣ`
(`a ∣ p − 1`, `caseA.a_dvd_p_sub_one`).  Refines `caseA_exists_blockScalarRatioEmbedding` with
the order information that Peterfalvi (14.6) consumes; immediate from the exponent fact
`caseA_pow_a_eq_one` (`(ψ u i) ^ a = ψ (u ^ a) i = 1`). -/
theorem caseA_exists_blockScalarRatioEmbedding_orderA (caseA : CliffordCaseAData chars) :
    ∃ ψ : ↥(MonoidHom.range (uActionHom data chief)) →*
        (Fin (data.q - 1) → (ZMod chief.p)ˣ),
      Function.Injective ψ ∧
        ∀ (u : ↥(MonoidHom.range (uActionHom data chief))) (i : Fin (data.q - 1)),
          (ψ u i) ^ caseA.a = 1 := by
  obtain ⟨ψ, hinj⟩ := caseA_exists_blockScalarRatioEmbedding chars caseA
  refine ⟨ψ, hinj, fun u i => ?_⟩
  have hpow : (ψ u i) ^ caseA.a = ψ (u ^ caseA.a) i := by
    rw [map_pow]
    rfl
  rw [hpow, caseA_pow_a_eq_one caseA u, map_one]
  rfl

omit [Finite G] in
/-- **Peterfalvi (9.7.a), "`U/C_U(H_i)` is cyclic"**: the `U`-action image on each Clifford
summand is a cyclic group (of order `a`, `caseA_card_range_restrictAut_Hpart`) — it is a subgroup
of `MulAut` of the order-`p` (hence cyclic) summand, and `MulAut(C_p) ≅ (ZMod p)ˣ` is cyclic
(`IsCyclic.mulAutMulEquiv` + units of the prime field). -/
theorem caseA_isCyclic_range_restrictAut_Hpart (caseA : CliffordCaseAData chars)
    (i : Fin data.q) :
    IsCyclic ↥(aInvariantRestrictAut (caseA.Hpart_aInvariant i)).range := by
  haveI : Fact chief.p.Prime := ⟨chief.p_prime⟩
  haveI : chief.N.Normal := chief.N_normal
  haveI hcyc : IsCyclic ↥(caseA.Hpart i) := isCyclic_of_prime_card (caseA.Hpart_order i)
  haveI : Fact (Nat.card ↥(caseA.Hpart i)).Prime := ⟨(caseA.Hpart_order i).symm ▸ chief.p_prime⟩
  haveI : IsCyclic (MulAut ↥(caseA.Hpart i)) := by
    have e := IsCyclic.mulAutMulEquiv (↥(caseA.Hpart i))
    exact isCyclic_of_injective e.toMonoidHom e.injective
  exact Subgroup.isCyclic _

end OrderAEmbedding

end OddOrder.Peterfalvi.S11
