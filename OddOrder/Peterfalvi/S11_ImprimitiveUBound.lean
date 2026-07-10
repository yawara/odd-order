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

/-- **A global `ZMod p`-scalar is central in `MulAut`.**  If `l` acts on the additive side as the
scalar `μ` (`ρ l = μ • id` for the descended representation `ρ = elabRepresentation p φ`), then
`φ l` commutes with every automorphism of `V`: automorphisms are additive maps, and additive maps
commute with `ZMod p`-scalar multiplication (`ZMod.map_smul`). -/
theorem commute_mulAut_of_elabRepresentation_eq_smul_id {p : ℕ} {L V : Type*} [Group L]
    [CommGroup V] [Module (ZMod p) (Additive V)] (φ : L →* MulAut V) (l : L) (μ : ZMod p)
    (h : elabRepresentation p φ l = μ • LinearMap.id) (σ : MulAut V) :
    Commute σ (φ l) := by
  have happly : ∀ x : V, Additive.ofMul ((φ l) x) = μ • Additive.ofMul x := by
    intro x
    have hx := LinearMap.congr_fun h (Additive.ofMul x)
    rwa [LinearMap.smul_apply, LinearMap.id_apply, elabRepresentation_apply] at hx
  have : σ * (φ l) = (φ l) * σ := by
    refine MulEquiv.ext fun x => ?_
    show σ ((φ l) x) = (φ l) (σ x)
    calc σ ((φ l) x)
        = Additive.toMul ((MulEquiv.toAdditive σ) (Additive.ofMul ((φ l) x))) := rfl
      _ = Additive.toMul ((MulEquiv.toAdditive σ) (μ • Additive.ofMul x)) := by rw [happly]
      _ = Additive.toMul (μ • (MulEquiv.toAdditive σ) (Additive.ofMul x)) := by
          rw [ZMod.map_smul]
      _ = Additive.toMul (μ • Additive.ofMul (σ x)) := rfl
      _ = Additive.toMul (Additive.ofMul ((φ l) (σ x))) := by rw [← happly]
      _ = (φ l) (σ x) := rfl
  exact this

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
      -- `ū = λ·(-)` central in `MulAut(H̄)` (`commute_mulAut_of_elabRepresentation_eq_smul_id`),
      -- hence `W̄₁`-conjugation-invariant, so `ū ∈ C_Ū(W̄₁) = 1` by the Frobenius fpf of
      -- `(U ⊔ W₁, U, W₁)` descended mod `C` (`uActionHom_eq_one_of_commute_mulAut`).
      (fun u hscal => by
        -- the blocks span `H̄`, so the common block scalar `μ` is a global scalar: `ρ u = μ • id`
        have hspan : ⨆ i : Fin ((data.q - 1) + 1),
            (aInvariantSubrep (p := chief.p) (isAInvariant_range_subtype
              (caseA.Hpart_aInvariant (finCongr hq1 i)))).toSubmodule = ⊤ := by
          have hre : ⨆ i : Fin ((data.q - 1) + 1), caseA.Hpart (finCongr hq1 i) = ⊤ := by
            rw [Equiv.iSup_comp (finCongr hq1) (g := caseA.Hpart)]
            exact caseA.Hpart_iSup
          calc ⨆ i : Fin ((data.q - 1) + 1),
              (aInvariantSubrep (p := chief.p) (isAInvariant_range_subtype
                (caseA.Hpart_aInvariant (finCongr hq1 i)))).toSubmodule
              = ⨆ i : Fin ((data.q - 1) + 1), (elabSubmoduleSubgroupEquiv chief.p).symm
                  (caseA.Hpart (finCongr hq1 i)) := rfl
            _ = (elabSubmoduleSubgroupEquiv chief.p).symm
                  (⨆ i : Fin ((data.q - 1) + 1), caseA.Hpart (finCongr hq1 i)) :=
                ((elabSubmoduleSubgroupEquiv chief.p).symm.map_iSup _).symm
            _ = ⊤ := by rw [hre, OrderIso.map_top]
        have hsmul := representation_eq_smul_id_of_block_scalars_const
          (elabRepresentation chief.p (MonoidHom.range (uActionHom data chief)).subtype)
          (fun i => aInvariantSubrep (isAInvariant_range_subtype
            (caseA.Hpart_aInvariant (finCongr hq1 i))))
          (fun i => finrank_eq_one_of_card_eq_prime
            ((card_aInvariantSubrep _).trans (caseA.Hpart_order (finCongr hq1 i))))
          hspan u _ hscal
        -- a global scalar is central in `MulAut(H̄)`, so the Frobenius fpf forces `u = 1`
        obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp u.2
        have hone : uActionHom data chief g = 1 :=
          uActionHom_eq_one_of_commute_mulAut chief g (fun σ => by
            rw [hg]
            exact (commute_mulAut_of_elabRepresentation_eq_smul_id _ u _ hsmul σ).symm)
        exact Subtype.ext (hg ▸ hone))
  rw [hq1] at hbound
  rw [chars.u_eq_card_quotient]
  exact hbound

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

end OddOrder.Peterfalvi.S11
