/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_MaximalII_III_IV
import OddOrder.Peterfalvi.S05_OmegaSigmaGrid
import Mathlib.GroupTheory.IsPerfect

/-!
# Peterfalvi Section 12: Maximal Subgroups of Types III, IV, and V

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 12, pp. 58--63.

This section begins the type-by-type character-theoretic elimination.  It works
under Hypothesis (10.1), where `M` is a maximal subgroup of type III, IV, or V,
fixes the type-`P` notation from (8.4), and studies the Dade isometry attached
to `A_0(M)`.  The main outputs are:

* (10.7): if `S` is of type II, then `[S,S]` is Frobenius with kernel `S_F`;
* (10.8): the character family `S` of Hypothesis (10.1) is not coherent;
* (10.10): maximal subgroups of type V do not occur.

The quotient-module and virtual-character calculations in (10.5)--(10.10) are
kept as named proposition fields in the scaffolding structures.  This preserves
the downstream theorem surface while avoiding fake definitions for `mu_ij`,
`omega_ij^sigma`, and the quotient `M'/M''` before the §3--§6 character API is
fully wired into this layer.
-/

namespace OddOrder.Peterfalvi.S12
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! Scoped finiteness instances (the `S15.FiniteInduce` pattern) so the
`Hypothesis` carrier of (10.1) can pin the genuine Dade isometry / induced family
without leaking the `noncomputable` `Fintype`/`Invertible` data globally. -/
namespace FiniteInduce

noncomputable scoped instance finiteSubFintype [Finite G] (H : Subgroup G) :
    Fintype ↥H := Fintype.ofFinite _

noncomputable scoped instance finiteGFintype [Finite G] : Fintype G :=
  Fintype.ofFinite _

noncomputable scoped instance natCardInvC [Finite G] (H : Subgroup G) :
    Invertible (Nat.card H : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

noncomputable scoped instance natCardInvCG [Finite G] :
    Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

end FiniteInduce

open scoped FiniteInduce in
/-- Peterfalvi's character family `S` of Hypothesis (10.1):
`{Ind_{M'}^M θ | θ ∈ Irr M', θ ≠ 1_{M'}}`, where `M' = [M,M]` is realised inside
`M` as `(derivedInG M).subgroupOf M`.  The induction is the canonical
`ClassFunction.induce`. -/
noncomputable def inducedFamily (M : Subgroup G) [Finite G] :
    Set (ClassFunction ↥M ℂ) :=
  { χ | ∃ θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M),
      θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
      χ = ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) }

open scoped FiniteInduce in
/-- **The induced family `S` is closed under complex conjugation** (Peterfalvi §10): for
`χ = Ind_{M'}^M θ ∈ S` with `θ ∈ Irr M'`, `θ ≠ 1`, the conjugate is `χ̄ = Ind_{M'}^M θ̄`
(`ClassFunction.induce_conj`), and `θ̄` is again a non-trivial irreducible of `M'`
(`IsIrreducibleCharacter.conj`, `irreducibleCharacter_conj_ne_trivial`).  This is the
`ζ̄ ∈ S` input to the `(α_{ij}^τ, (ζ−ζ̄)^τ)` step of the (10.5) `a = 0` argument. -/
theorem inducedFamily_closedUnderConjugate [Finite G] (M : Subgroup G) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (inducedFamily M) := by
  classical
  intro φ hφ
  obtain ⟨θ, hθ_ne, hφeq⟩ := hφ
  refine ⟨⟨(θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ).conj, θ.isIrreducible.conj⟩,
    ?_, ?_⟩
  · -- `θ̄ ≠ 1`: else `θ = θ̄̄ = 1̄ = 1` (the trivial character is real).
    intro h
    apply hθ_ne
    have hcoe : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ).conj
        = trivialClassFunction ↥((derivedInG M).subgroupOf M) := by
      simpa using congrArg
        (fun c : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          (c : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)) h
    apply Subtype.ext
    show (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)
      = trivialClassFunction ↥((derivedInG M).subgroupOf M)
    rw [← ClassFunction.conj_conj (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ), hcoe]
    exact trivialClassFunction_isReal
  · rw [hφeq]
    simpa using ClassFunction.induce_conj ((derivedInG M).subgroupOf M)
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)

/-! ## (10.1): the type III/IV/V hypothesis -/

open scoped FiniteInduce in
/-- **Peterfalvi (10.1)**: the common setup for a maximal subgroup of type III,
IV, or V.

Finiteness of `G` is carried as the instance field `finiteG` (the `S15`
`FiniteInduce` pattern), so that the *genuine* Dade isometry `tau`, the induced
family `Sset`, and the support `A0 = A_0(M)` can be defined as honest projections
(see `Hypothesis.tau`, `Hypothesis.Sset`, `Hypothesis.A0`) rather than carried as
unconstrained data.  `dadeData` is the (8.15) Dade support hypothesis for
`A_0(M)` (supplied by `S10.dadeSupportHypotheses_typeP`), and `hconj` is its
`L`-conjugation invariance, which together build the Dade isometry. -/
structure Hypothesis (M : Subgroup G) where
  [finiteG : Finite G]
  maximal : M ∈ maximalSubgroups G
  typeP : TypePData M
  type_alt : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M
  dadeData : OddOrder.Peterfalvi.S10.DadeSupportHypothesisData M (typePA0 M typeP)
  hconj : dadeData.dade.HConjInvariant

namespace Hypothesis

/-- Peterfalvi's `M'`, represented as an ambient subgroup. -/
def Mderiv {M : Subgroup G} (_hyp : Hypothesis M) : Subgroup G :=
  derivedInG M

/-- Peterfalvi's `M''`, represented as an ambient subgroup. -/
def Msecond {M : Subgroup G} (_hyp : Hypothesis M) : Subgroup G :=
  secondDerivedInAmbient M

/-- Peterfalvi's `W_1` from Definition (8.4). -/
def W1 {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.typeP.W1

/-- Peterfalvi's `W_2` from Definition (8.4). -/
def W2 {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.typeP.W2

/-- Peterfalvi's `V = W - (W_1 union W_2)`. -/
def V {M : Subgroup G} (hyp : Hypothesis M) : Set G :=
  typePV M hyp.typeP

/-- Peterfalvi's `w_1 = |W_1|`. -/
noncomputable def w1 {M : Subgroup G} (hyp : Hypothesis M) : ℕ :=
  Nat.card ↥hyp.W1

/-- Peterfalvi's `w_2 = |W_2|`. -/
noncomputable def w2 {M : Subgroup G} (hyp : Hypothesis M) : ℕ :=
  Nat.card ↥hyp.W2

/-- Peterfalvi's support `A_0(M)` from (8.10), as a subset of `M` (the
`supportInSubgroup` restriction of the ambient set `typePA0 M`).  This is the
genuine support for the Dade isometry, no longer an unconstrained field. -/
def A0 {M : Subgroup G} (hyp : Hypothesis M) : Set ↥M :=
  OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M

open scoped FiniteInduce in
/-- Peterfalvi's family `S` of (10.1), pinned to the genuine `inducedFamily M`
`= {Ind_{M'}^M θ | θ ∈ Irr M', θ ≠ 1}`, no longer an unconstrained field. -/
noncomputable def Sset {M : Subgroup G} (hyp : Hypothesis M) :
    Set (ClassFunction ↥M ℂ) :=
  haveI := hyp.finiteG
  inducedFamily M

open scoped FiniteInduce in
/-- Peterfalvi's Dade isometry `τ` relative to `(A_0(M), M, G)` from (10.1),
pinned to the genuine `S07.dadeIntegralCharacterMap` of the (8.15) support data
`dadeData` (no longer an unconstrained field). -/
noncomputable def tau {M : Subgroup G} (hyp : Hypothesis M) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G :=
  haveI := hyp.finiteG
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)

end Hypothesis

/-- Conjugation transports the centralizer of a singleton: `g · C_G(a) · g⁻¹ = C_G(g a g⁻¹)`.
(The singleton analogue of `BG.Ch3.S12.centralizer_conj_smul`.) -/
private theorem conj_smul_centralizer_singleton (g a : G) :
    MulAut.conj g • Subgroup.centralizer ({a} : Set G)
      = Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
  have hinv : (MulAut.conj g)⁻¹ • y = g⁻¹ * y * g := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  simp only [Set.mem_singleton_iff, forall_eq, hinv]
  constructor
  · intro h
    calc g * a * g⁻¹ * y
        = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * a) * g⁻¹ := by rw [h]
      _ = y * (g * a * g⁻¹) := by group
  · intro h
    calc a * (g⁻¹ * y * g)
        = g⁻¹ * (g * a * g⁻¹ * y) * g := by group
      _ = g⁻¹ * (y * (g * a * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * y * g * a := by group

/-- **Peterfalvi (8.14)/(8.15)**: the support kernel `R(x)` is `M`-conjugation equivariant.
`supportKernel M M X (g x g⁻¹) = g · supportKernel M M X x · g⁻¹` for `g ∈ M` and `X` an
`M`-invariant set.  `R(x) = M_F ⊓ C_G(x)` on the escaping-centralizer set (else `⊥`); the
escaping condition is `M`-invariant, `M_F` is `M`-normal, and the centralizer is equivariant. -/
private theorem supportKernel_conj_invariant {M : Subgroup G} {X : Set G} {g x : G}
    (hg : g ∈ M) (hmem : g * x * g⁻¹ ∈ X ↔ x ∈ X) :
    supportKernel M M X (g * x * g⁻¹) = MulAut.conj g • supportKernel M M X x := by
  have hMfix : MulAut.conj g • maxNilpotentNormalHall M = maxNilpotentNormalHall M :=
    conj_smul_eq_self_of_mem_normalizer
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M hg)
  have hMself : MulAut.conj g • M = M :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg)
  have hcent : (Subgroup.centralizer ({g * x * g⁻¹} : Set G) ≤ M)
      ↔ (Subgroup.centralizer ({x} : Set G) ≤ M) := by
    rw [← conj_smul_centralizer_singleton]
    conv_lhs => rw [← hMself]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff
  have hescape : (g * x * g⁻¹ ∈ escapingCentralizerSet M X)
      ↔ (x ∈ escapingCentralizerSet M X) := by
    simp only [escapingCentralizerSet, Set.mem_setOf_eq, hmem, hcent]
  unfold supportKernel
  by_cases hx : x ∈ escapingCentralizerSet M X
  · rw [if_pos (hescape.mpr hx), if_pos hx, Subgroup.smul_inf, hMfix,
        conj_smul_centralizer_singleton]
  · rw [if_neg (fun h => hx (hescape.mp h)), if_neg hx, Subgroup.smul_bot]

open scoped FiniteInduce in
/-- **Peterfalvi (10.1), existence**: every maximal subgroup `M` of type III, IV,
or V carries the (10.1) Hypothesis.  The character family, support, and Dade
isometry are now the genuine `inducedFamily`, `A_0(M)`, and
`S07.dadeIntegralCharacterMap`; the only inputs are the (8.15) Dade support data
(`S10.dadeSupportHypotheses_typeP`) and the conjugation invariance `hconj` of the
support kernels (a (8.14)/(8.15) fact). -/
theorem exists_hypothesis_of_typeIIIorIVorV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hType : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) :
    Nonempty (Hypothesis M) := by
  obtain ⟨data⟩ := typePData_of_isTypeNonI (Or.inr hType)
  obtain ⟨ptype, hptype⟩ : ∃ ptype : PeterfalviType, HasPeterfalviType ptype M := by
    rcases hType with h | h | h
    · exact ⟨.III, h⟩
    · exact ⟨.IV, h⟩
    · exact ⟨.V, h⟩
  obtain ⟨dadeData⟩ :=
    (OddOrder.Peterfalvi.S10.dadeSupportHypotheses_typeP hG hM data hptype).1
  -- (8.14)/(8.15): the support kernels `R(a)` are `M`-conjugation invariant.
  have hconj : dadeData.dade.HConjInvariant := by
    intro a l
    simp only [dadeData.H_eq_supportKernel]
    refine supportKernel_conj_invariant l.2 ?_
    exact ⟨fun h => by simpa using dadeData.dade.L_normalizes_A l⁻¹ h,
      fun h => dadeData.dade.L_normalizes_A l h⟩
  refine ⟨?_⟩
  exact
    { maximal := hM
      typeP := data
      type_alt := hType
      dadeData := dadeData
      hconj := hconj }

/-! ## §10 → §5 ω-grid bridge prerequisites (gate #3)

The Peterfalvi §10 character analysis ((10.2)–(10.10)) consumes the §5 `ω_{ij}` grid
(`S05.TICyclicHypothesis.omegaGrid` / `omegaSigmaGrid`) on `W = W₁ × W₂`.  Building the
bridge `Hypothesis → S05.TICyclicHypothesis` rests on the cyclic-`TI` structure of `(W, V)`,
whose first prerequisites are the disjointness and coprimality of the factors `W₁`, `W₂`.
See `notes/peterfalvi/s12_s10_character_bridge.md`. -/

/-- The cyclic factors `W₁`, `W₂` of a type-`P` maximal subgroup are disjoint:
`W₁` complements `M' = [M,M]` in `M` (`TypePData.M_complement`), and `W₂ ≤ M'`
(`W₂ ≤ H ⊓ M'' ≤ H ≤ M'`), so `W₁ ⊓ W₂ ≤ W₁ ⊓ M' = ⊥`. -/
theorem typePData_disjoint_W1_W2 {M : Subgroup G} (data : TypePData M) :
    Disjoint data.W1 data.W2 := by
  have hW2D : data.W2 ≤ derivedInG M :=
    data.W2_le.trans (inf_le_left.trans data.H_le)
  rw [Subgroup.disjoint_def]
  intro x hx1 hx2
  have hxM : x ∈ M := data.W1_le hx1
  have hdisj := data.M_complement.disjoint
  rw [Subgroup.disjoint_def] at hdisj
  have hmem1 : (⟨x, hxM⟩ : ↥M) ∈ (derivedInG M).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr (hW2D hx2)
  have hmem2 : (⟨x, hxM⟩ : ↥M) ∈ data.W1.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr hx1
  exact Subtype.ext_iff.mp (hdisj hmem1 hmem2)

/-- The cyclic factors `W₁`, `W₂` of a type-`P` maximal subgroup have coprime orders.
`W = W₁ × W₂` is cyclic (`TypePData.W_cyclic`) and `W₁`, `W₂` are disjoint
(`typePData_disjoint_W1_W2`), so the multiplication map `↥W₁ × ↥W₂ →* ↥W` is injective;
a group embedding into the cyclic `↥W` is cyclic, and a finite cyclic product forces
coprime factor orders (`coprime_card_of_isCyclic_prod`). -/
theorem typePData_coprime_card_W1_W2 [Finite G] {M : Subgroup G} (data : TypePData M) :
    Nat.Coprime (Nat.card ↥data.W1) (Nat.card ↥data.W2) := by
  haveI hcyc : IsCyclic ↥data.W := data.W_cyclic
  letI : CommGroup ↥data.W := hcyc.commGroup
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have hdisj := typePData_disjoint_W1_W2 data
  have hinj : Function.Injective
      ((Subgroup.inclusion hW1le).coprod (Subgroup.inclusion hW2le)) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    rw [MonoidHom.coprod_apply] at hab
    have hG : (a : G) * (b : G) = 1 := by
      have h2 := congrArg (Subtype.val (p := fun x => x ∈ data.W)) hab
      simpa [Subgroup.coe_inclusion] using h2
    have ha1 : (a : G) = 1 := by
      have haW2 : (a : G) ∈ data.W2 := by
        rw [mul_eq_one_iff_eq_inv.mp hG]; exact data.W2.inv_mem b.2
      have hmem : (a : G) ∈ data.W1 ⊓ data.W2 := ⟨a.2, haW2⟩
      rw [disjoint_iff.mp hdisj] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hb1 : (b : G) = 1 := by rw [ha1, one_mul] at hG; exact hG
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  haveI : IsCyclic (↥data.W1 × ↥data.W2) := isCyclic_of_injective _ hinj
  exact coprime_card_of_isCyclic_prod (↥data.W1) (↥data.W2)

/-- The cyclic factor product `W = W₁ × W₂` of a type-`P` maximal subgroup has odd order.
`W ≤ G`, so `|W| ∣ |G|`, and `G` has odd order; a divisor of an odd number is odd. -/
theorem typePData_W_card_odd [Finite G] {M : Subgroup G} (data : TypePData M)
    (hodd : Odd (Nat.card G)) : Odd (Nat.card ↥data.W) :=
  hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card data.W)

/-- For a type-`P` maximal subgroup the exceptional set `V = W − (W₁ ∪ W₂)` is nonempty:
the product `x·y` of a nontrivial `x ∈ W₁` and a nontrivial `y ∈ W₂` lies in `W` but in neither
factor, since `W₁` and `W₂` are disjoint (`typePData_disjoint_W1_W2`). -/
theorem typePData_typePV_nonempty {M : Subgroup G} (data : TypePData M) :
    (typePV M data).Nonempty := by
  obtain ⟨x, hxW1, hxne⟩ := (data.W1.bot_or_exists_ne_one).resolve_left data.W1_nontrivial
  obtain ⟨y, hyW2, hyne⟩ := (data.W2.bot_or_exists_ne_one).resolve_left data.W2_nontrivial
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have hdisj := disjoint_iff.mp (typePData_disjoint_W1_W2 data)
  refine ⟨x * y, ?_⟩
  simp only [typePV, Set.mem_diff, Set.mem_union, SetLike.mem_coe, not_or]
  refine ⟨mul_mem (hW1le hxW1) (hW2le hyW2), ?_, ?_⟩
  · intro hxy
    have hy1 : y ∈ data.W1 := by
      have he : y = x⁻¹ * (x * y) := by group
      rw [he]; exact mul_mem (inv_mem hxW1) hxy
    exact hyne (Subgroup.mem_bot.mp (hdisj ▸ Subgroup.mem_inf.mpr ⟨hy1, hyW2⟩))
  · intro hxy
    have hx1 : x ∈ data.W2 := by
      have he : x = (x * y) * y⁻¹ := by group
      rw [he]; exact mul_mem hxy (inv_mem hyW2)
    exact hxne (Subgroup.mem_bot.mp (hdisj ▸ Subgroup.mem_inf.mpr ⟨hxW1, hx1⟩))

/-- An element of the exceptional set `V = W − (W₁ ∪ W₂)` of a type-`P` maximal subgroup lies
outside the derived subgroup `M' = [M,M]`.

Decompose `v ∈ W = W₁ ⊔ W₂` (cyclic, hence abelian) as `v = x·y` with `x ∈ W₁`, `y ∈ W₂`
(`Subgroup.mem_sup`).  Now `W₂ ≤ M'` (`W₂ ≤ H ⊓ M'' ≤ H ≤ M'`); if `v ∈ M'` then
`x = v·y⁻¹ ∈ M'`, so `x ∈ W₁ ⊓ M' = ⊥` (`M_complement` disjointness), i.e. `x = 1` and
`v = y ∈ W₂`, contradicting `v ∉ W₂`.

This is the structural fact behind `ζ` (induced from the normal `M'`) vanishing on `V`, used in the
Dade-image half of (10.5). -/
theorem typePData_typePV_not_mem_derived {M : Subgroup G} (data : TypePData M)
    {v : G} (hv : v ∈ typePV M data) : v ∉ derivedInG M := by
  simp only [typePV, Set.mem_diff, Set.mem_union, SetLike.mem_coe, not_or] at hv
  obtain ⟨hvW, _hvnW1, hvnW2⟩ := hv
  intro hvM'
  haveI hcyc : IsCyclic ↥data.W := data.W_cyclic
  letI : CommGroup ↥data.W := hcyc.commGroup
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  -- Decompose `v` in the abelian `↥W` along `W₁ ⊔ W₂ = ⊤`.
  have hsup : data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← data.W_eq, Subgroup.subgroupOf_self]
  have hvmem : (⟨v, hvW⟩ : ↥data.W) ∈
      data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W := by
    rw [hsup]; exact Subgroup.mem_top _
  rw [Subgroup.mem_sup] at hvmem
  obtain ⟨a, ha, b, hb, hab⟩ := hvmem
  have haW1 : ((a : ↥data.W) : G) ∈ data.W1 := Subgroup.mem_subgroupOf.mp ha
  have hbW2 : ((b : ↥data.W) : G) ∈ data.W2 := Subgroup.mem_subgroupOf.mp hb
  have habG : ((a : ↥data.W) : G) * ((b : ↥data.W) : G) = v := by
    have := congrArg (Subtype.val) hab
    simpa using this
  -- `W₂ ≤ M'`, so `b ∈ M'`; with `v ∈ M'` this forces `a = v·b⁻¹ ∈ M'`.
  have hW2D : data.W2 ≤ derivedInG M := data.W2_le.trans (inf_le_left.trans data.H_le)
  have haM' : ((a : ↥data.W) : G) ∈ derivedInG M := by
    have heq : ((a : ↥data.W) : G) = v * ((b : ↥data.W) : G)⁻¹ := by rw [← habG]; group
    rw [heq]; exact mul_mem hvM' (inv_mem (hW2D hbW2))
  -- `a ∈ W₁ ⊓ M' = ⊥` (the `M_complement` disjointness), hence `a = 1`.
  have haM : ((a : ↥data.W) : G) ∈ M := data.W1_le haW1
  have hdisj := data.M_complement.disjoint
  rw [Subgroup.disjoint_def] at hdisj
  have hm1 : (⟨(a : ↥data.W), haM⟩ : ↥M) ∈ (derivedInG M).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr haM'
  have hm2 : (⟨(a : ↥data.W), haM⟩ : ↥M) ∈ data.W1.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr haW1
  have ha1 : ((a : ↥data.W) : G) = 1 := Subtype.ext_iff.mp (hdisj hm1 hm2)
  -- Then `v = b ∈ W₂`, contradicting `v ∉ W₂`.
  exact hvnW2 (by rw [← habG, ha1, one_mul]; exact hbW2)

/-- **Peterfalvi (4.6.b) / (4.3.a), ambient version** (issue 1005): for a type-`P` maximal
subgroup, the exceptional set `V = W − (W₁ ∪ W₂)` is a TI-subset of `G` with normalizer-bound `W`.

Given `g` conjugating some `a ∈ V` into `V`, the singleton normalizer fact `N_G({a}) = W`
(`TypePData.normalizer_V`) forces `g` to normalize `W` — both `h ∈ W` and `g h g⁻¹ ∈ W` reduce to
`h a h⁻¹ = a`.  Since `W = W₁ × W₂` is cyclic with coprime factors, `W₁` and `W₂` are the *unique*
subgroups of their orders (`cyclic_subgroup_eq_of_card_eq`), hence characteristic, so `g` also
normalizes `W₁` and `W₂` and therefore `V`; finally `N_G(V) = W` (`normalizer_V` with `X = V`,
nonempty by `typePData_typePV_nonempty`) gives `g ∈ W`.

This discharges the last field of `typePData_toTICyclicHypothesis`, making the §10 → §5 ω-grid
bridge unconditional (closes issue 1005).  It also corrects the earlier diagnosis that
`normalizer_V` is strictly weaker than the TI property: that is true *without* cyclicity, but the
cyclic factor structure recovers the ambient TI. -/
theorem typePData_V_ti [Finite G] {M : Subgroup G} (data : TypePData M) :
    IsTISubset (typePV M data) data.W := by
  classical
  haveI : IsCyclic ↥data.W := data.W_cyclic
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  -- Singleton normalizer = pointwise stabilizer.
  have mem_norm_sing : ∀ c z : G,
      z ∈ Subgroup.normalizer ({c} : Set G) ↔ z * c * z⁻¹ = c := by
    intro c z
    rw [Subgroup.mem_set_normalizer_iff]
    constructor
    · intro hz
      have := (hz c).mp rfl
      simpa using this
    · intro hz h
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro rfl; exact hz
      · intro hh
        have hcc : z * h * z⁻¹ = z * c * z⁻¹ := by rw [hh, hz]
        exact mul_left_cancel (mul_right_cancel hcc)
  intro g hg
  obtain ⟨a, haV, hbV⟩ := hg
  have hNa : Subgroup.normalizer ({a} : Set G) = data.W :=
    data.normalizer_V {a} (Set.singleton_nonempty a) (Set.singleton_subset_iff.mpr haV)
  have hNb : Subgroup.normalizer ({g * a * g⁻¹} : Set G) = data.W :=
    data.normalizer_V {g * a * g⁻¹} (Set.singleton_nonempty _) (Set.singleton_subset_iff.mpr hbV)
  -- `g` normalizes `W` as a set: both sides reduce to `h * a * h⁻¹ = a`.
  have hgW : ∀ h, h ∈ data.W ↔ g * h * g⁻¹ ∈ data.W := by
    intro h
    have e1 : (h ∈ data.W) ↔ h * a * h⁻¹ = a := by rw [← hNa, mem_norm_sing]
    have e2 : (g * h * g⁻¹ ∈ data.W) ↔ h * a * h⁻¹ = a := by
      rw [← hNb, mem_norm_sing]
      have hexp : g * h * g⁻¹ * (g * a * g⁻¹) * (g * h * g⁻¹)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ := by
        group
      rw [hexp]
      constructor
      · intro hh; exact mul_left_cancel (mul_right_cancel hh)
      · intro hh; rw [hh]
    rw [e1, e2]
  -- Any subgroup `A ≤ W` is `g`-stable (cyclic uniqueness ⇒ `A` characteristic in `W`).
  have hstab : ∀ (A : Subgroup G), A ≤ data.W → ∀ x : G, g * x * g⁻¹ ∈ A ↔ x ∈ A := by
    intro A hAW
    have hmap_le : A.map (MulAut.conj g).toMonoidHom ≤ data.W := by
      rintro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hzA, rfl⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (hgW z).mp (hAW hzA)
    have hcard : Nat.card ↥(A.map (MulAut.conj g).toMonoidHom) = Nat.card ↥A :=
      (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv).symm
    have hsubeq : (A.map (MulAut.conj g).toMonoidHom).subgroupOf data.W
        = A.subgroupOf data.W := by
      apply OddOrder.BG.Ch3.S10.cyclic_subgroup_eq_of_card_eq (C := ↥data.W)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmap_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv, hcard]
    have hmapeq : A.map (MulAut.conj g).toMonoidHom = A := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hmap_le, hsubeq,
        Subgroup.map_subgroupOf_eq_of_le hAW]
    intro x
    constructor
    · intro hx
      have hmem : g * x * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := by rw [hmapeq]; exact hx
      rw [Subgroup.mem_map] at hmem
      obtain ⟨z, hzA, hz⟩ := hmem
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hz
      have hzx : z = x := mul_left_cancel (mul_right_cancel hz)
      rwa [hzx] at hzA
    · intro hx
      have hmem : (MulAut.conj g).toMonoidHom x ∈ A.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hmapeq] at hmem
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
  -- `g` normalizes `V`, so `g ∈ N_G(V) = W`.
  rw [← data.normalizer_V (typePV M data) ⟨a, haV⟩ Set.Subset.rfl,
    Subgroup.mem_set_normalizer_iff]
  intro h
  simp only [typePV, Set.mem_diff, Set.mem_union, SetLike.mem_coe]
  rw [hgW h, hstab data.W1 hW1le h, hstab data.W2 hW2le h]

/-- `W₂ ≤ M` for type-`P` data (`W₂ ≤ H ⊓ M'' ≤ M' ≤ M`). -/
theorem typePData_W2_le_self {M : Subgroup G} (data : TypePData M) : data.W2 ≤ M :=
  (data.W2_le.trans (le_trans inf_le_right (Subgroup.map_subtype_le _))).trans
    (Subgroup.map_subtype_le _)

/-- `W ≤ M` for type-`P` data (`W = W₁ ⊔ W₂`, both `≤ M`). -/
theorem typePData_W_le_self {M : Subgroup G} (data : TypePData M) : data.W ≤ M :=
  data.W_eq ▸ sup_le data.W1_le (typePData_W2_le_self data)

/-- The §6 `↥M`-level `W = W₁.subgroupOf M ⊔ W₂.subgroupOf M` is `W.subgroupOf M`: the `subgroupOf`
order-iso on subgroups `≤ M` preserves joins. -/
theorem typePData_sup_subgroupOf_eq {M : Subgroup G} (data : TypePData M) :
    data.W1.subgroupOf M ⊔ data.W2.subgroupOf M = data.W.subgroupOf M := by
  rw [← Subgroup.subgroupOf_sup data.W1_le (typePData_W2_le_self data), ← data.W_eq]

open scoped FiniteInduce in
/-- **§10 → §5 ω-grid bridge (gate #3)**: a type-`P` maximal subgroup's cyclic factor
`W = W₁ × W₂`, with the exceptional set `V = W − (W₁ ∪ W₂)`, is a Peterfalvi (3.1) TI-cyclic
normalizer setup in the ambient group `G`.  Every structural field is read off from the
`TypePData`: the `W`-block is disjoint (`typePData_disjoint_W1_W2`) / coprime
(`typePData_coprime_card_W1_W2`) / cyclic (`W_cyclic`), oddness comes from `Odd |G|`, and `V` is
`W`-normalized because the cyclic `W` is abelian.

The ambient TI property `V_ti : IsTISubset V W` — Peterfalvi (4.6.b), the `G`-version of (4.3.a) —
is the one field that does not read off directly from the `TypePData` fields; it is supplied by the
companion `typePData_V_ti`, which derives it from `normalizer_V` together with the cyclic factor
structure (`W₁`, `W₂` are the unique, hence characteristic, subgroups of their orders in the cyclic
`W`).  This makes the bridge **unconditional** (no external TI hypothesis; closes issue 1005).

Through this bridge the entire §5 ω/σ-grid (`TICyclicHypothesis.omegaGrid`, `omegaSigmaGrid`,
`sigmaIntegral`) becomes available for the §10 character analysis ((10.2)–(10.10)). -/
noncomputable def typePData_toTICyclicHypothesis [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G)) :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis G where
  W := data.W
  W1 := data.W1
  W2 := data.W2
  W1_le_W := by rw [data.W_eq]; exact le_sup_left
  W2_le_W := by rw [data.W_eq]; exact le_sup_right
  W1_nontrivial := data.W1_nontrivial
  W2_nontrivial := data.W2_nontrivial
  W_sup := data.W_eq.symm
  W_disjoint := typePData_disjoint_W1_W2 data
  W_card_coprime := typePData_coprime_card_W1_W2 data
  W_card_odd := typePData_W_card_odd data hodd
  W_cyclic := data.W_cyclic
  V := typePV M data
  V_subset_sharp := by
    intro v hv
    rw [OddOrder.Peterfalvi.S04.mem_sharp]
    refine ⟨Set.mem_univ v, fun heq => hv.2 (Or.inl ?_)⟩
    rw [heq]; exact data.W1.one_mem
  V_subset_W := fun _ hv => hv.1
  W_normalizes_V := by
    intro w v hv
    have hcomm : Commute (w : G) v :=
      S06.commute_of_mem_of_isCyclic data.W_cyclic w.2 hv.1
    have h3 : (w : G) * v * (w : G)⁻¹ = v := by rw [hcomm.eq, mul_inv_cancel_right]
    rw [h3]; exact hv
  V_ti := typePData_V_ti data

/-! ## §10 → §6 (4.2)+Dade bridge (μ-grid unlock)

Peterfalvi (10.1) states that Hypothesis (4.6) holds with `L = M`, `H = K = M' = [M,M]`.  Once that
instantiation is realised, the §6 certain-type apparatus (the `μ_{ij}`/`ω_{ij}`/`ζ` families, the
Brauer permutation lemma, the Clifford inertia computation) supplies (10.2), (10.3) and the `μ`-grid
directly.  This bridge builds the §6 *structural* Hypothesis (4.2) `S06.Hypothesis ↥M` from the
`TypePData`, then combines it with the §10 Dade datum (`dadeData.dade`, already a
`S04.Hypothesis G (A₀(M)) M`) into a `S06.CertainTypeHypothesis`.  See
`notes/peterfalvi/s12_s10_character_bridge.md` §6. -/

/-- **Peterfalvi (4.2.a) Hall coprimality** (issue 1006): for a type-`P` maximal subgroup `M`,
`gcd(|M'|, |W₁|) = 1`, i.e. `W₁` is a *Hall* complement to `M' = [M,M]` in `M`.

A bare complement need not be Hall, but the κ-Hall structure of a type-`P` maximal supplies it: a
Hall `κ(M)`-subgroup `K ≤ M` (`exists_isHallSubgroup_kappa_ge`) is cyclic (BG Theorem A,
`theoremA_maximal_structure` — cited here even though its proof currently carries a `sorry`, since
its statement is the correct BG result and the dependency is honest), so it complements `M'` in `M`
(`typeP_derivedInG_isComplement_kappaHall`); hence `gcd(|K|, |M'|) = 1`
(`IsHallSubgroup.coprime_index`), and `|K| = [M:M'] = |W₁|` (`card_kappaHall_eq_derived_index`,
`TypePData.card_W1_eq_derived_index`).  Discharges the `hHall` obligation of the §10 → §6 bridge. -/
theorem typePData_W1_hall_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : OddOrder.BG.Ch4.S14.IsTypeP M) (data : TypePData M) :
    Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- A Hall `κ(M)`-subgroup `K ≤ M`.
  obtain ⟨K, hKM, hK, -⟩ :=
    OddOrder.BG.Ch4.S14.exists_isHallSubgroup_kappa_ge hG hM (X := ⊥) bot_le (by simp)
  -- A `(κ(M) ∪ σ(M))'`-Hall subgroup `U` (needed only to invoke BG Theorem A).
  obtain ⟨U', hU'hall, -⟩ :=
    Ch03.hall_D (G := ↥M)
      (π := (OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U := ⊥) (by simp)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'hall
  -- `K` is cyclic by BG Theorem A.
  haveI : IsCyclic ↥K := (OddOrder.BG.Ch4.S16.theoremA_maximal_structure hG hM hK rfl hU).2.1
  -- Coprimality `gcd(|K|, |M'|) = 1` from the κ-Hall complement (mirrors S14_TypePComplement).
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hcompl := OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hK
  have hidx : (K.subgroupOf M).index = Nat.card ↥(derivedInG M) := by
    rw [hcompl.index_eq_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv
  have hCop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(derivedInG M)) := by
    have hco := hK.coprime_index
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hidx] at hco
  -- `|K| = [M:M'] = |W₁|`.
  have hKW1 : Nat.card ↥K = Nat.card ↥data.W1 := by
    rw [OddOrder.BG.Ch4.S16.card_kappaHall_eq_derived_index hG hM hP hKM hK,
      data.card_W1_eq_derived_index]
  rw [Nat.coprime_comm, ← hKW1]; exact hCop

/-- **§10 → §6 (4.2) bridge, structural part**: build the Peterfalvi Hypothesis (4.2)
`S06.Hypothesis ↥M` from a type-`P` maximal subgroup's `TypePData`, with `L = M`, `K = M' = [M,M]`
and the (8.4) cyclic factors `W₁, W₂` transported into `↥M` via `subgroupOf`.  Structural fields
come from `TypePData`: `M_complement → isComplement`, `centralizer_W1 → centralizer_W2` (through the
ambient↔`↥M` centralizer transport `S03h.centralizer_subgroupOf`), and cyclicity / oddness through
the order-preserving `subgroupOfEquivOfLe`; `K ⊴ ↥M` because `K = commutator ↥M`.

The Hall coprimality `card_coprime` (`gcd(|M'|,|W₁|) = 1`, i.e. `W₁` is a *Hall* complement to `M'`
in `M`) is **not** derivable from `TypePData` alone — a complement need not be Hall — so it is taken
as the input `hHall`.  This is the Peterfalvi (4.2.a) Hall condition, dischargeable at call sites
from the κ-Hall structure of a type-`P` maximal (`typeP_derivedInG_isComplement_kappaHall` +
`IsHallSubgroup.coprime_index`, since `|W₁| = [M:M'] = |κ-Hall K|`).  See issue 1006. -/
def typePData_toS06Hypothesis [Finite G] {M : Subgroup G} (data : TypePData M)
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1)) :
    OddOrder.Peterfalvi.S06.Hypothesis ↥M := by
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hW2leM' : data.W2 ≤ derivedInG M :=
    data.W2_le.trans (le_trans inf_le_right (Subgroup.map_subtype_le _))
  have hW2leM : data.W2 ≤ M := hW2leM'.trans hM'le
  haveI := data.W1_cyclic
  haveI := data.W2_cyclic
  exact
    { K := (derivedInG M).subgroupOf M
      W1 := data.W1.subgroupOf M
      W2 := data.W2.subgroupOf M
      K_normal := by
        rw [show (derivedInG M).subgroupOf M = commutator ↥M by
          rw [derivedInG, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
        infer_instance
      isComplement := data.M_complement
      W1_nontrivial := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        exact fun hdisj => data.W1_nontrivial (disjoint_self.mp (hdisj.mono_right data.W1_le))
      W1_cyclic := isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe data.W1_le).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe data.W1_le).injective
      card_coprime := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.W1_le).toEquiv]
        exact hHall
      W2_nontrivial := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        exact fun hdisj => data.W2_nontrivial (disjoint_self.mp (hdisj.mono_right hW2leM))
      W2_cyclic := isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hW2leM).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hW2leM).injective
      W2_le_K := Subgroup.comap_mono hW2leM'
      centralizer_W2 := by
        intro x hx1 hx2
        have hxW1 : (x : G) ∈ data.W1 := Subgroup.mem_subgroupOf.mp hx1
        have hxne : (x : G) ≠ 1 := fun h => hx2 (Subtype.ext h)
        have hamb : Subgroup.centralizer ({(x : G)} : Set G) ⊓ derivedInG M = data.W2 := by
          rw [inf_comm]; exact data.centralizer_W1 (x : G) hxW1 hxne
        rw [OddOrder.BG.Ch1.S03h.centralizer_subgroupOf, Set.image_singleton]
        simp only [Subgroup.subgroupOf, ← Subgroup.comap_inf, Subgroup.coe_subtype, hamb]
      W_odd := by
        rw [← Subgroup.subgroupOf_sup data.W1_le hW2leM,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le data.W1_le hW2leM)).toEquiv,
          ← data.W_eq]
        exact typePData_W_card_odd data hodd }

/-- The §10 Hypothesis (10.1) for a type III/IV/V maximal subgroup `M` exhibits `M` as a *BG*
type-`P` maximal (`(κ(M)).Nonempty`).  By BG Proposition 16.1
(`proposition_type_classification`, cited even though it currently carries a `sorry`), each
Peterfalvi type III/IV/V maps to `S14.IsTypeP1`, hence to `S14.IsTypeP`.  This is the BG type-`P`
input needed to discharge the Hall coprimality `typePData_W1_hall_coprime`. -/
theorem Hypothesis.bgTypeP [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) : OddOrder.BG.Ch4.S14.IsTypeP M := by
  have hclass := OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.maximal
  rcases hyp.type_alt with h | h | h
  · exact (hclass.2.2.1.mp (Or.inl h)).1.1
  · exact (hclass.2.2.1.mp (Or.inr h)).1.1
  · exact (hclass.2.2.2.1.mp h).1.1

open scoped FiniteInduce in
/-- **§10 → §6 (4.2)+Dade bridge**: from the §10 Hypothesis (10.1) for a type-`P` maximal subgroup
`M`, build the §6 certain-type Hypothesis `S06.CertainTypeHypothesis (A₀(M)) M`.  The structural
(4.2) part is `typePData_toS06Hypothesis`; the Dade datum is the §10 `dadeData.dade` (already a
`S04.Hypothesis G (typePA0 M typeP) M`), so no new Dade construction is needed.  This unlocks the
entire §6 μ/ω/ζ machinery with `L = M`, the common source of (10.2), (10.3) and the `μ`-grid.

The Hall coprimality is discharged internally via `typePData_W1_hall_coprime` (using the BG
type-`P` from `Hypothesis.bgTypeP`), so this bridge is **unconditional** — no external `hHall`
input (closes issue 1006 for the §10 consumer). -/
def Hypothesis.toCertainTypeHypothesis [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) :
    OddOrder.Peterfalvi.S06.CertainTypeHypothesis (typePA0 M hyp.typeP) M :=
  haveI := hyp.finiteG
  { toHypothesis := typePData_toS06Hypothesis hyp.typeP hodd
      (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)
    dade := hyp.dadeData.dade }

/-- **A finite non-perfect group has a non-trivial linear character.**  If `commutator K ≠ ⊤`
(the abelianization `K/[K,K]` is non-trivial), there is a non-trivial degree-one irreducible
character of `K`: a non-trivial element of `K/[K,K]` is separated by some `φ : (K/[K,K]) →* ℂˣ`
(Pontryagin duality over `ℂ`, `exists_apply_ne_one_of_hasEnoughRootsOfUnity`), pulled back along
`K ↠ K/[K,K]`.  This supplies the non-principal degree-`1` character of `M' = [M,M]` whose induction
to `M` is the (10.2) character `ζ`. -/
theorem exists_nontrivial_linearIrreducibleCharacter {K : Type*} [Group K] [Finite K]
    (hK : commutator K ≠ ⊤) :
    ∃ θ : IrreducibleCharacter K, θ ≠ trivialIrreducibleCharacter K ∧
      (θ : ClassFunction K ℂ) 1 = 1 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : K, a ∉ commutator K := by
    by_contra h
    push_neg at h
    exact hK (top_le_iff.mp fun x _ => h x)
  haveI : Finite (Abelianization K) := Quotient.finite _
  have hā : (Abelianization.of a) ≠ 1 := by
    rw [ne_eq, ← MonoidHom.mem_ker, Abelianization.ker_of]; exact ha
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (G := Abelianization K) (M := ℂ) hā
  set ψ : K →* ℂˣ := φ.comp Abelianization.of with hψdef
  have hψ : ψ ≠ 1 := fun h => hφ (by rw [← MonoidHom.comp_apply, ← hψdef, h, MonoidHom.one_apply])
  refine ⟨linearIrreducibleCharacter ψ, ?_, linearIrreducibleCharacter_apply_one ψ⟩
  rw [ne_eq, linearIrreducibleCharacter_eq_trivial_iff]
  exact hψ

open scoped FiniteInduce in
/-- **Peterfalvi (10.2)**: the family `S = {Ind_{M'}^M θ | θ ∈ Irr M', θ ≠ 1}` contains an
irreducible character `ζ` of degree `w₁ = |W₁|`.

Take a non-principal degree-`1` character `θ` of `M' = [M,M]` (exists since `M'` is not perfect:
`M'' < M'`, via `exists_nontrivial_linearIrreducibleCharacter`).  By the §6 Clifford engine `θ` is
none of the `chiRestrict χ₂` (the `W₁^#`-fixed irreducibles of `M'`): the trivial column gives
`chiRestrict 1 = Res_{M'} μ_{00} = Res_{M'} 1_M = 1_{M'}` (Peterfalvi (4.4) anchor), avoided since
`θ ≠ 1`; a non-trivial column `χ₂` gives `chiRestrict χ₂ = Res_{M'} μ_{0j}` of degree
`μ_{0j}(1) > 1` (else `μ_{0j}` is linear ⇒ `M'`-trivial ⇒ a column-`0` character by (4.4),
contradicting `columnFamily_mu_ne`), avoided by degree.  Hence `Ind_{M'}^M θ` is irreducible
(`induce_isIrreducible_of_forall_chiRestrict_ne`) of degree `[M:M']·1 = |W₁|` (`induce_apply_one`
and `TypePData.card_W1_eq_derived_index`).  The §6 hypothesis is supplied by the §10→§6 bridge
`typePData_toS06Hypothesis` (so `K = M'`), needing the same `hodd`/`hHall` inputs. -/
theorem exists_zeta_in_inducedFamily_degree_w1 [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1)) :
    ∃ ζ : ClassFunction ↥M ℂ, ζ ∈ inducedFamily M ∧ IsIrreducibleCharacter ζ ∧
      ζ 1 = (Nat.card ↥data.W1 : ℂ) := by
  classical
  let h : OddOrder.Peterfalvi.S06.Hypothesis ↥M := typePData_toS06Hypothesis data hodd hHall
  haveI hNeZ : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hKeq : h.K = (derivedInG M).subgroupOf M := rfl
  have hKcomm : h.K = commutator ↥M := by
    rw [hKeq, derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  -- `M'` is not perfect (issue 7008, replacing the deleted `fitting_lt_derived`): `M' = M_F ⋊ U`
  -- is solvable — `M_F` nilpotent (`maxNilpotentNormalHall_isNilpotent`) is the normal kernel and the
  -- quotient `M'/M_F ≃ U` is nilpotent (`U_nilpotent`) via `derived_complement` — and nontrivial
  -- (`W₂ ≠ ⊥`, `W₂ ≤ M_F ≤ M'`); a nontrivial solvable group is not perfect.
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  haveI hHnorm : (data.H.subgroupOf (derivedInG M)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer data.H_le).mpr ?_
    rw [data.H_eq]
    exact hM'le.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M)
  haveI : IsSolvable ↥(data.H.subgroupOf (derivedInG M)) := by
    haveI : Group.IsNilpotent ↥data.H := by
      rw [data.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent M
    haveI : IsSolvable ↥data.H := IsNilpotent.to_isSolvable
    exact solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe data.H_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe data.H_le).injective
  haveI : IsSolvable ↥(data.U.subgroupOf (derivedInG M)) := by
    haveI : Group.IsNilpotent ↥data.U := data.U_nilpotent
    haveI : IsSolvable ↥data.U := IsNilpotent.to_isSolvable
    exact solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe data.U_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe data.U_le).injective
  haveI : IsSolvable (↥(derivedInG M) ⧸ data.H.subgroupOf (derivedInG M)) :=
    solvable_of_solvable_injective
      (f := data.derived_complement.symm.QuotientMulEquiv.toMonoidHom)
      data.derived_complement.symm.QuotientMulEquiv.injective
  haveI : IsSolvable ↥(derivedInG M) :=
    solvable_of_ker_le_range ((data.H.subgroupOf (derivedInG M)).subtype)
      (QuotientGroup.mk' (data.H.subgroupOf (derivedInG M)))
      (by rw [QuotientGroup.ker_mk']; exact (data.H.subgroupOf (derivedInG M)).range_subtype.ge)
  haveI : Nontrivial ↥(derivedInG M) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr fun hbot =>
      data.W2_nontrivial (le_bot_iff.mp (hbot ▸ data.W2_le.trans (inf_le_left.trans data.H_le)))
  have hcomm_K : commutator ↥h.K ≠ ⊤ := by
    intro hperf
    have hperfM' : Group.IsPerfect ↥(derivedInG M) := by
      haveI : Group.IsPerfect ↥((derivedInG M).subgroupOf M) := ⟨hperf⟩
      exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hM'le).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hM'le).surjective
    exact absurd hperfM'.commutator_eq_top
      (IsSolvable.commutator_lt_top_of_nontrivial ↥(derivedInG M)).ne
  obtain ⟨θ, hθne, hθ1⟩ := exists_nontrivial_linearIrreducibleCharacter hcomm_K
  -- the crux: `θ` avoids every `chiRestrict χ₂`.
  have havoid : ∀ χ₂, h.chiRestrict χ₂ ≠ θ := by
    intro χ₂ heq
    by_cases hχ₂ : χ₂ = 1
    · subst hχ₂
      refine hθne ?_
      rw [← heq]
      apply IrreducibleCharacter.ext
      rw [OddOrder.Peterfalvi.S06.Hypothesis.coe_chiRestrict, (h.certainType_zero_column_anchor).2,
        OddOrder.Peterfalvi.S03.restrict_trivialClassFunction]
      rfl
    · have hmu1 : ((h.columnFamily χ₂).mu 0 : ClassFunction ↥M ℂ) (1 : ↥M) = 1 := by
        have hval := congrArg
          (fun c : IrreducibleCharacter ↥h.K => (c : ClassFunction ↥h.K ℂ) (1 : ↥h.K)) heq
        simp only [OddOrder.Peterfalvi.S06.Hypothesis.coe_chiRestrict, ClassFunction.restrict_apply,
          Subgroup.coe_one] at hval
        rw [hval, hθ1]
      have hker : (h.K : Set ↥M) ⊆ OddOrder.Peterfalvi.S03.characterKernel
          ((h.columnFamily χ₂).mu 0 : ClassFunction ↥M ℂ) := by
        intro x hx
        have hx1 := ((h.columnFamily χ₂).mu 0).isIrreducible
          |>.apply_eq_one_of_mem_commutator_of_apply_one_eq_one hmu1 (hKcomm ▸ hx)
        rw [OddOrder.Peterfalvi.S03.mem_characterKernel, hx1,
          OddOrder.Peterfalvi.S03.characterDegree_def, hmu1]
      obtain ⟨i, hi⟩ := h.exists_certainType_zero_column_eq_of_subset_characterKernel _ hker
      exact h.columnFamily_mu_ne hχ₂ 0 i hi.symm
  refine ⟨ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ), ⟨θ, hθne, rfl⟩,
    h.induce_isIrreducible_of_forall_chiRestrict_ne havoid, ?_⟩
  rw [ClassFunction.induce_apply_one, hθ1, mul_one, hKeq, ← data.card_W1_eq_derived_index]

/-! ## (10.2)--(10.4): basic character parameters and coherent extension -/

/-- **Pontryagin reindex** (the §5/§6 "`W₂`-dual ↔ `Fin w₂`" bridge): for a finite abelian group
`C`, the index set `Fin |C|` is equivalent to the character group `C →* ℂˣ`.  Since `ℂ` is
algebraically closed it has enough roots of unity, so `C ≃* (C →* ℂˣ)`
(`CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity`); composing with `C ≃ Fin |C|` reindexes
the character group by `Fin |C|`.  This is what lets the §6 `columnFamily` (indexed by `W₂`-duals)
populate the `Fin w₂`-indexed `μ`-grid of `CharacterParameters`.

The bijection is normalized to send `0` to the trivial character `1`
(`finCardEquivCharacterGroup_zero`, by composing with the transposition `(0 ↔ e⁻¹ 1)`), matching
Peterfalvi's convention that column `0` is the trivial column (`δ_0 = 1`, `μ_{00} = 1`, by (4.4))
and `0 < j < w₂` are the nontrivial columns of common degree `d` (10.3). -/
noncomputable def finCardEquivCharacterGroup (C : Type*) [CommGroup C] [Finite C]
    [NeZero (Nat.card C)] : Fin (Nat.card C) ≃ (C →* ℂˣ) :=
  let e : Fin (Nat.card C) ≃ (C →* ℂˣ) :=
    (Finite.equivFin C).symm.trans
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity C ℂ).some.toEquiv.symm
  (Equiv.swap (0 : Fin (Nat.card C)) (e.symm 1)).trans e

/-- The normalized Pontryagin reindex sends `0` to the trivial character (Peterfalvi's column-`0`
convention). -/
theorem finCardEquivCharacterGroup_zero (C : Type*) [CommGroup C] [Finite C]
    [NeZero (Nat.card C)] : finCardEquivCharacterGroup C 0 = 1 := by
  simp only [finCardEquivCharacterGroup, Equiv.trans_apply, Equiv.swap_apply_left,
    Equiv.apply_symm_apply]

instance instNeZeroW1 {M : Subgroup G} (hyp : Hypothesis M) : NeZero hyp.w1 := by
  haveI := hyp.finiteG
  exact ⟨Nat.card_pos.ne'⟩

instance instNeZeroW2 {M : Subgroup G} (hyp : Hypothesis M) : NeZero hyp.w2 := by
  haveI := hyp.finiteG
  exact ⟨Nat.card_pos.ne'⟩

open scoped FiniteInduce in
/-- **§10 μ-grid materialization** (Peterfalvi (10.1)/(4.3.b)): the `Fin w₁ × Fin w₂`-indexed family
of induced characters `μ_{ij}` of `M`, read off from the §6 `columnFamily` of the (now
unconditional) §10→§6 bridge `Hypothesis.toCertainTypeHypothesis`, reindexed by
`finCardEquivCharacterGroup` (the `W₂`-dual ↔ `Fin w₂` Pontryagin bijection) on the column index and
by the order identity `|W₁| = w₁` on the row index.  This is the genuine source for
`CharacterParameters.mu`. -/
noncomputable def Hypothesis.muGrid [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) :
    Fin hyp.w1 → Fin hyp.w2 → ClassFunction ↥M ℂ := by
  haveI := hyp.finiteG
  classical
  intro i j
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  exact ((h.columnFamily χ₂).mu (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ)

open scoped FiniteInduce in
/-- **§10 ω^σ-grid materialization** (Peterfalvi (3.6)): the `Fin w₁ × Fin w₂`-indexed family of
virtual characters `ω_{ij}^σ` of `G`, read off from the §5 `TICyclicHypothesis.omegaSigmaGrid` of
the (now unconditional) §10→§5 bridge `typePData_toTICyclicHypothesis`.  The required §4 Dade
application is built directly: the TI-cyclic Dade hypothesis has trivial local subgroups
(`HConjInvariant.of_forall_H_eq_bot`), so `Hypothesis.fullDadeIsometryData` applies.  Its index set
`Fin |W₁| × Fin |W₂|` is definitionally `Fin w₁ × Fin w₂`.  This is the genuine source for
`CharacterParameters.omegaSigma`. -/
noncomputable def Hypothesis.omegaSigmaGrid [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) :
    Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ := by
  haveI := hyp.finiteG
  classical
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    ⟨tic.toDadeHypothesis.fullDadeIsometryData
      (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl))⟩
  have hVeq : tic.V = tic.Vdiff := rfl
  exact fun i j => tic.omegaSigmaGrid hVeq app i j

open scoped FiniteInduce in
/-- **§10 aligned ω^σ-grid** (producer-local alignment fix for (10.5)): the §5 `σ`-image of the
*same* ω that `muGrid` is built from — `h.chiColumn χ₂ i` (`χ₂ = finCardEquivCharacterGroup j`,
`i` via `w1CharEquiv`) — transported from the §6 `↥M`-level `W = W₁ ⊔ W₂` to the §10 `G`-level
`tic.W = data.W` along the `W ≤ M ≤ G` isomorphism `e` (`subgroupOfEquivOfLe` ∘ `subgroupCongr` of
`typePData_sup_subgroupOf_eq`).

Unlike `omegaSigmaGrid` (which reindexes via the *independent* §5 `charEquiv`), this grid shares
`muGrid`'s indexing by construction, so on `V` it satisfies `alignedOmegaSigma_{ij}(v) =
chiColumn(v)` — matching `(μ_{ij} − δ·μ_{i0})(v) = δ·(chiColumn_{ij} − chiColumn_{i0})(v)` ((4.3.c))
needed by the (10.5) Dade-image identity.  This is the genuine `CharacterParameters.omegaSigma`. -/
noncomputable def Hypothesis.alignedOmegaSigmaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ := by
  haveI := hyp.finiteG
  classical
  intro i j
  -- §6 host (the source of `muGrid`'s ω `chiColumn`) — mirror `muGrid`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  -- §5 `G`-level TI-cyclic hypothesis (for `σ`) — mirror `omegaSigmaGrid`.
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    ⟨tic.toDadeHypothesis.fullDadeIsometryData
      (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl))⟩
  -- the `W ≤ M ≤ G` isomorphism `↥tic.W ≃* ↥(h.W₁ ⊔ h.W₂)`.
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- `σ` of the transported `chiColumn` (= `muGrid`'s own ω).
  exact tic.sigmaIntegral rfl app
    (ClassFunction.compHom e.toMonoidHom
      (h.chiColumn χ₂ (finCongr hcardW1.symm i) : ClassFunction h.sdiffTICyclicHypothesis.W ℂ))

open scoped FiniteInduce in
/-- The canonical `(3.2)` Dade application of the type-`P` `TICyclicHypothesis`: the source of the
`σ`-grids (`omegaSigmaGrid`, `alignedOmegaSigmaGrid`).  The TI-cyclic Dade hypothesis has trivial
local subgroups (`HConjInvariant.of_forall_H_eq_bot`), so `Hypothesis.fullDadeIsometryData` applies.
Definitionally equal to the `app` reconstructed inline in the grids, so any `σ`-machinery lemma
(`chiFam`, `sigma`, `sigmaCoeff`) stated with this `app` aligns with the grids by `rfl`. -/
noncomputable def Hypothesis.canonicalFullDadeApp [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication
      (typePData_toTICyclicHypothesis hyp.typeP hodd) :=
  ⟨(typePData_toTICyclicHypothesis hyp.typeP hodd).toDadeHypothesis.fullDadeIsometryData
    (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl))⟩

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), aligned ω^σ-grid is a `χ`-family member** (the §10 analogue of the §6
`certainTypeOmegaSigma_eq_chiFam`): `alignedOmegaSigmaGrid i j` is the `σ`-image of the irreducible
(linear) character `η = compHom e (chiColumn χ₂ i)` of `tic.W` — `chiColumn` is `ω(omegaProdChar …)`
hence a `linearIrreducibleCharacter`, and `compHom` of a linear character is again linear
(`compHom_linearIrreducibleCharacter`).  By `sigma_irreducibleCharacter` it is the orthonormal family
vector `χ_P` at the index `P = omegaIrrEquiv.symm η`.  This is what lets the (10.5) Dade-image
trichotomy reuse the §6 `(4.8)` endgame (`sigmaCoeff_psi_eq`, `grid_trichotomy`). -/
theorem Hypothesis.exists_alignedOmegaSigmaGrid_chiFam_family [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) :
    ∃ P : Fin hyp.w2 →
        (((typePData_toTICyclicHypothesis hyp.typeP hodd).W1.subgroupOf
            (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ) ×
          (((typePData_toTICyclicHypothesis hyp.typeP hodd).W2.subgroupOf
            (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ),
      Function.Injective P ∧
        ∀ j, hyp.alignedOmegaSigmaGrid hG hodd i j
          = (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
              (hyp.canonicalFullDadeApp hG hodd) (P j) := by
  haveI := hyp.finiteG
  classical
  -- reconstruct the lets of `alignedOmegaSigmaGrid`
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : Fin hyp.w2 → (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    fun j => finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- the transported `chiColumn` is the linear (irreducible) character `η j` of `tic.W`.
  let η : Fin hyp.w2 → IrreducibleCharacter ↥tic.W := fun j =>
    linearIrreducibleCharacter
      ((h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm i)) (χ₂ j)).comp
        e.toMonoidHom)
  refine ⟨fun j => tic.omegaIrrEquiv.symm (η j), ?_, ?_⟩
  · -- injectivity: peel off the injective maps `omegaIrrEquiv.symm`, `linearIrreducibleCharacter`,
    -- precompose-`e`, `omegaProdChar(·, ·)`, `finCardEquivCharacterGroup`, `finCongr`.
    intro j j' hjj'
    have h1 : η j = η j' := tic.omegaIrrEquiv.symm.injective hjj'
    have h2 := linearIrreducibleCharacter_injective h1
    have h3 := (MonoidHom.cancel_right (MulEquiv.surjective e)).mp h2
    have h4 := (h.sdiffTICyclicHypothesis.omegaProdChar_inj h3).2
    exact (finCongr hcardW2sub.symm).injective ((finCardEquivCharacterGroup _).injective h4)
  · -- value: `alignedOmegaSigmaGrid i j = σ(η j) = χ_{omegaIrrEquiv.symm (η j)}`.
    intro j
    have step1 : hyp.alignedOmegaSigmaGrid hG hodd i j
        = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (η j : ClassFunction ↥tic.W ℂ) := by
      change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd) (η j : ClassFunction ↥tic.W ℂ)
          = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (η j : ClassFunction ↥tic.W ℂ)
      rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
    rw [step1, OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_irreducibleCharacter]

open scoped FiniteInduce in
/-- **§10 within-column degree constancy** (Peterfalvi (4.5.a), the `i`-independence half of
(10.3)): within a fixed `W₂`-column `j`, the degree `μ_{ij}(1)` of the materialized `μ`-grid does
not depend on the row `i`.  This is the §6 fact `columnFamily_difference_apply_one` (the
within-column difference `μ_{ij} − μ_{0j}` vanishes at `1`) read through the `muGrid` definition. -/
theorem Hypothesis.muGrid_apply_one_within_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    hyp.muGrid hG hodd i j 1 = hyp.muGrid hG hodd 0 j 1 := by
  haveI := hyp.finiteG
  classical
  have key : ∀ (h : OddOrder.Peterfalvi.S06.Hypothesis (↥M)) [NeZero (Nat.card h.W1)]
      (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (k : Fin (Nat.card h.W1)),
      ((h.columnFamily χ₂).mu k : ClassFunction (↥M) ℂ) 1
        = ((h.columnFamily χ₂).mu 0 : ClassFunction (↥M) ℂ) 1 := by
    intro h _ χ₂ k
    have hd := h.columnFamily_difference_apply_one χ₂ k
    simp only [SignedIrreducibleDifferenceFamily.difference_apply,
      SignedIrreducibleDifferenceFamily.classFunction_apply, ClassFunction.sub_apply] at hd
    exact sub_eq_zero.mp hd
  unfold Hypothesis.muGrid
  simp only [key]

open OddOrder.Peterfalvi.S06 in
/-- The `k`-th power of the row-`0` product source `ω(1, χ₂)` is the row-`0` source of the
`k`-th power dual: `(omegaProdChar 1 χ₂)^k = omegaProdChar 1 (χ₂^k)` (on the §6 `toTICyclicHypothesis`).
Row `0` is the trivial `W₁`-dual, fixed by powering, so only the `W₂`-factor `χ₂` is raised. -/
theorem omegaProdChar_one_pow {L : Type*} [Group L] [Fintype L]
    (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (k : ℕ) :
    (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) ^ k
      = h.toTICyclicHypothesis.omegaProdChar 1 (χ₂ ^ k) := by
  rw [h.toTICyclicHypothesis.omegaProdChar_one_left,
    h.toTICyclicHypothesis.omegaProdChar_one_left]
  refine MonoidHom.ext fun w => ?_
  rw [MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact (MonoidHom.pow_apply χ₂ k _).symm

open OddOrder.Peterfalvi.S06 in
/-- **§6 cross-column degree constancy** (Peterfalvi (10.3) via (3.9.b) + (4.3.b)): the degree
`μ_{0j}(1)` of the column-`0` certain-type character is unchanged when the `W₂`-dual `χ₂` indexing
the column is replaced by a Galois power `χ₂ ^ k` (with `k` coprime to the order of the row-`0`
source character).  This is the cross-column half of (10.3): by (3.9.b) there is a ring
automorphism `u` of `ℂ` with `σ(ω_{0,χ₂^k}) = (σ(ω_{0,χ₂}))^u`, hence by (4.3.b)
`δ_{χ₂^k}·μ_{0,χ₂^k} = (δ_{χ₂}·μ_{0,χ₂})^u`; evaluating at `1` and using that `u` fixes the
integer `δ·μ(1)` (degrees are positive, signs `±1`) forces `μ_{0,χ₂^k}(1) = μ_{0,χ₂}(1)`. -/
theorem columnFamily_mu_zero_apply_one_pow {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    [NeZero (Nat.card h.W1)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) {k : ℕ}
    (hk : k.Coprime (orderOf (h.toTICyclicHypothesis.omegaProdChar 1 χ₂))) :
    ((h.columnFamily (χ₂ ^ k)).mu 0 : ClassFunction L ℂ) 1
      = ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ) 1 := by
  classical
  -- (3.9.b): the Galois automorphism `u` relating the row-`0` source to its `k`-th power
  obtain ⟨u, hu, -⟩ := h.toTICyclicHypothesis.exists_mapRingEquiv_sigma_omega_pow rfl
    h.toTICyclicFullDadeApplication (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) hk
  -- the `k`-th power of the row-`0` source is the row-`0` source of column `χ₂ ^ k`
  rw [omegaProdChar_one_pow h χ₂ k] at hu
  -- (4.3.b) at row `0`, stated in `omega`/source form (`chiColumn ψ 0 = ω(omegaProdChar 1 ψ)`)
  have e43 : ∀ ψ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ,
      h.toTICyclicHypothesis.sigma rfl h.toTICyclicFullDadeApplication
          (h.toTICyclicHypothesis.omega (h.toTICyclicHypothesis.omegaProdChar 1 ψ) :
            ClassFunction h.toTICyclicHypothesis.W ℂ)
        = (h.columnFamily ψ).sign • ((h.columnFamily ψ).mu 0 : ClassFunction L ℂ) := by
    intro ψ
    have hψ := h.sigma_chiColumn_eq_certainType ψ 0
    rw [h.chiColumn_zero] at hψ
    exact hψ
  rw [e43 (χ₂ ^ k), e43 χ₂] at hu
  -- `hu : δ' • μ'_0 = (δ • μ_0)^u`; evaluate at `1`
  have h1 := congrArg (fun f : ClassFunction L ℂ => (f : L → ℂ) (1 : L)) hu
  simp only at h1
  obtain ⟨d, hd_pos, hd⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily χ₂).mu 0)
  obtain ⟨d', hd'_pos, hd'⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily (χ₂ ^ k)).mu 0)
  rw [ClassFunction.zsmul_apply, ClassFunction.mapRingEquiv_apply, ClassFunction.zsmul_apply,
    zsmul_eq_mul, zsmul_eq_mul, hd, hd'] at h1
  -- `h1 : δ' * d' = u (δ * d)`; `u` fixes the integer `δ * d`
  rw [← Int.cast_natCast (R := ℂ) d, ← Int.cast_natCast (R := ℂ) d', ← Int.cast_mul,
    ← Int.cast_mul, map_intCast] at h1
  have hZ : (h.columnFamily (χ₂ ^ k)).sign * (d' : ℤ) = (h.columnFamily χ₂).sign * (d : ℤ) :=
    Int.cast_injective h1
  -- magnitudes: signs are `±1`, degrees positive, so `d' = d`
  rw [hd, hd']
  have hdd : d' = d := by
    have habs := congrArg Int.natAbs hZ
    rw [Int.natAbs_mul, Int.natAbs_mul] at habs
    rcases (h.columnFamily (χ₂ ^ k)).sign_eq with hs | hs <;>
      rcases (h.columnFamily χ₂).sign_eq with hs' | hs' <;>
        simp only [hs, hs'] at habs <;> simpa using habs
  rw [hdd]

open OddOrder.Peterfalvi.S06 in
/-- **§6 cross-column *sign* constancy** (Peterfalvi (10.3), the `δ`-part of the (3.9.b) argument):
the sign `δ_{χ₂}` of the column-`0` certain-type difference family is unchanged when the `W₂`-dual
`χ₂` is replaced by a Galois power `χ₂ ^ k` (`k` coprime to the order of the row-`0` source).

This is the sign companion of `columnFamily_mu_zero_apply_one_pow`: the same (3.9.b)+(4.3.b) Galois
identity `δ_{χ₂^k}·μ_{0,χ₂^k} = (δ_{χ₂}·μ_{0,χ₂})^u`, evaluated at `1` and read in `ℤ`, gives
`δ_{χ₂^k}·d' = δ_{χ₂}·d`; since the degrees agree (`d' = d > 0`) the signs agree.  Peterfalvi's
(10.3): "It follows that `δ_j = δ_1` and `μ_{0j}(1) = μ_{01}(1)`." -/
theorem columnFamily_mu_zero_sign_pow {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    [NeZero (Nat.card h.W1)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) {k : ℕ}
    (hk : k.Coprime (orderOf (h.toTICyclicHypothesis.omegaProdChar 1 χ₂))) :
    (h.columnFamily (χ₂ ^ k)).sign = (h.columnFamily χ₂).sign := by
  classical
  obtain ⟨u, hu, -⟩ := h.toTICyclicHypothesis.exists_mapRingEquiv_sigma_omega_pow rfl
    h.toTICyclicFullDadeApplication (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) hk
  rw [omegaProdChar_one_pow h χ₂ k] at hu
  have e43 : ∀ ψ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ,
      h.toTICyclicHypothesis.sigma rfl h.toTICyclicFullDadeApplication
          (h.toTICyclicHypothesis.omega (h.toTICyclicHypothesis.omegaProdChar 1 ψ) :
            ClassFunction h.toTICyclicHypothesis.W ℂ)
        = (h.columnFamily ψ).sign • ((h.columnFamily ψ).mu 0 : ClassFunction L ℂ) := by
    intro ψ
    have hψ := h.sigma_chiColumn_eq_certainType ψ 0
    rw [h.chiColumn_zero] at hψ
    exact hψ
  rw [e43 (χ₂ ^ k), e43 χ₂] at hu
  have h1 := congrArg (fun f : ClassFunction L ℂ => (f : L → ℂ) (1 : L)) hu
  simp only at h1
  obtain ⟨d, hd_pos, hd⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily χ₂).mu 0)
  obtain ⟨d', hd'_pos, hd'⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily (χ₂ ^ k)).mu 0)
  rw [ClassFunction.zsmul_apply, ClassFunction.mapRingEquiv_apply, ClassFunction.zsmul_apply,
    zsmul_eq_mul, zsmul_eq_mul, hd, hd'] at h1
  rw [← Int.cast_natCast (R := ℂ) d, ← Int.cast_natCast (R := ℂ) d', ← Int.cast_mul,
    ← Int.cast_mul, map_intCast] at h1
  have hZ : (h.columnFamily (χ₂ ^ k)).sign * (d' : ℤ) = (h.columnFamily χ₂).sign * (d : ℤ) :=
    Int.cast_injective h1
  -- the degrees agree (same Galois argument); cancel the positive degree to equate the signs
  have hdd : (d' : ℤ) = (d : ℤ) := by
    have habs := congrArg Int.natAbs hZ
    rw [Int.natAbs_mul, Int.natAbs_mul] at habs
    rcases (h.columnFamily (χ₂ ^ k)).sign_eq with hs | hs <;>
      rcases (h.columnFamily χ₂).sign_eq with hs' | hs' <;>
        simp only [hs, hs'] at habs <;> simp_all
  rw [hdd] at hZ
  have hdne : (d : ℤ) ≠ 0 := by exact_mod_cast hd_pos.ne'
  exact mul_right_cancel₀ hdne hZ

open OddOrder.Peterfalvi.S06 in
/-- **§6 cross-column sign constancy, prime-order form** (Peterfalvi (10.3)): when the `W₂`-dual
group has prime order, every nontrivial column shares the common sign `δ`.  Mirrors
`columnFamily_mu_zero_apply_one_eq_of_ne_one` (any two nontrivial duals are coprime powers of each
other) but for the sign via `columnFamily_mu_zero_sign_pow`. -/
theorem columnFamily_mu_zero_sign_eq_of_ne_one {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    [NeZero (Nat.card h.W1)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (hp : (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).Prime)
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1) :
    (h.columnFamily χ₂').sign = (h.columnFamily χ₂).sign := by
  classical
  haveI : Finite ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
    (Nat.card_pos_iff.mp hp.pos).2
  have hord : orderOf χ₂ = Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := by
    rcases (hp.eq_one_or_self_of_dvd _ (orderOf_dvd_natCard χ₂)) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hχ₂
    · exact h1
  have hgen : χ₂' ∈ Submonoid.powers χ₂ := by
    rw [mem_powers_iff_mem_zpowers]
    have htop : Subgroup.zpowers χ₂ = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord])
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk_eq⟩ := hgen
  have hcop : k.Coprime (orderOf χ₂) := by
    rw [hord, Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdvd
    rw [← hord] at hdvd
    exact hχ₂' (hk_eq ▸ orderOf_dvd_iff_pow_eq_one.mp hdvd)
  have hsdvd : orderOf (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) ∣ orderOf χ₂ := by
    apply orderOf_dvd_of_pow_eq_one
    rw [omegaProdChar_one_pow h χ₂ (orderOf χ₂), pow_orderOf_eq_one χ₂]
    exact h.toTICyclicHypothesis.omegaProdChar_one_one
  rw [← hk_eq]
  exact columnFamily_mu_zero_sign_pow h χ₂ (hcop.coprime_dvd_right hsdvd)

open OddOrder.Peterfalvi.S06 in
/-- **§6 cross-column degree constancy, prime-order form** (Peterfalvi (10.3)): when the `W₂`-dual
group has prime order (`w₂` prime), every nontrivial column shares the common degree.  Any two
nontrivial duals `χ₂`, `χ₂'` are powers of each other (the dual group is cyclic of prime order, so
a nontrivial element generates), with the power coprime to `w₂`;
`columnFamily_mu_zero_apply_one_pow` then equates the column-`0` degrees.  This is the full
cross-column (j-independence) half of (10.3):
all the columns `0 < j < w₂` have degree `d = μ_{0j}(1)` independent of `j`. -/
theorem columnFamily_mu_zero_apply_one_eq_of_ne_one {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    [NeZero (Nat.card h.W1)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (hp : (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).Prime)
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1) :
    ((h.columnFamily χ₂').mu 0 : ClassFunction L ℂ) 1
      = ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ) 1 := by
  classical
  -- a prime cardinality forces the dual group to be finite
  haveI : Finite ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
    (Nat.card_pos_iff.mp hp.pos).2
  -- `orderOf χ₂ = |D|` (a nontrivial element of a prime-order group generates it)
  have hord : orderOf χ₂ = Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := by
    rcases (hp.eq_one_or_self_of_dvd _ (orderOf_dvd_natCard χ₂)) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hχ₂
    · exact h1
  -- `χ₂'` is a power of `χ₂`
  have hgen : χ₂' ∈ Submonoid.powers χ₂ := by
    rw [mem_powers_iff_mem_zpowers]
    have htop : Subgroup.zpowers χ₂ = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord])
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk_eq⟩ := hgen
  -- `k` is coprime to `orderOf χ₂ = |D| = p`
  have hcop : k.Coprime (orderOf χ₂) := by
    rw [hord, Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdvd
    rw [← hord] at hdvd
    exact hχ₂' (hk_eq ▸ orderOf_dvd_iff_pow_eq_one.mp hdvd)
  -- transfer coprimality to the order of the row-`0` source character
  have hsdvd : orderOf (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) ∣ orderOf χ₂ := by
    apply orderOf_dvd_of_pow_eq_one
    rw [omegaProdChar_one_pow h χ₂ (orderOf χ₂), pow_orderOf_eq_one χ₂]
    exact h.toTICyclicHypothesis.omegaProdChar_one_one
  rw [← hk_eq]
  exact columnFamily_mu_zero_apply_one_pow h χ₂ (hcop.coprime_dvd_right hsdvd)

open scoped FiniteInduce in
open OddOrder.Peterfalvi.S06 in
/-- **§10 cross-column degree constancy** (Peterfalvi (10.3), the `j`-independence half at the
materialized `μ`-grid level): the degree `μ_{0j}(1)` of the row-`0` materialized `μ`-grid is
independent of the *nontrivial* column `0 < j < w₂`.

This wires the §6 prime-order corollary `columnFamily_mu_zero_apply_one_eq_of_ne_one` through the
`muGrid` materialization.  The required prime cardinality of the `W₂`-dual group is supplied by the
Pontryagin count `|Ŵ₂| = |W₂| = w₂` (`card_charGroup_W2`) together with the hypothesis `hw2` that
`w₂` is prime (Theorem (8.8), supplied at producer-construction time to avoid the
`no_typeV_maximal` → parameter-producer dependency cycle); the two columns are nontrivial duals
because the `Fin w₂`-reindex `finCardEquivCharacterGroup` is injective and sends only `0` to the
trivial character.  Together with `muGrid_apply_one_within_column` this gives the full (10.3) degree
independence `μ_{ij}(1) = d` for all `0 ≤ i < w₁`, `0 < j < w₂`. -/
theorem Hypothesis.muGrid_apply_one_cross_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (hw2 : (hyp.w2).Prime) {j j' : Fin hyp.w2}
    (hj : j ≠ 0) (hj' : j' ≠ 0) :
    hyp.muGrid hG hodd 0 j 1 = hyp.muGrid hG hodd 0 j' 1 := by
  haveI := hyp.finiteG
  classical
  -- Reconstruct the §6 host and the instances exactly as in `Hypothesis.muGrid`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- The `W₂`-dual group has prime cardinality `w₂` (Pontryagin count + (8.8)).
  have hp : (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).Prime := by
    rw [h.card_charGroup_W2,
      ← (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : h.W2 ≤ h.W1 ⊔ h.W2)).toEquiv),
      hcardW2sub]
    exact hw2
  -- A nontrivial column index gives a nontrivial `W₂`-dual.
  have hcol_ne : ∀ (k : Fin hyp.w2), k ≠ 0 →
      finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm k) ≠ 1 := by
    intro k hk heq
    rw [← finCardEquivCharacterGroup_zero (h.W2.subgroupOf (h.W1 ⊔ h.W2))] at heq
    have hk0 : finCongr hcardW2sub.symm k = 0 := (finCardEquivCharacterGroup _).injective heq
    apply hk
    have hval : (k : ℕ) = 0 := by simpa using congrArg Fin.val hk0
    exact Fin.ext hval
  -- The within-column degree-constancy key (Peterfalvi (4.5.a)), as in
  -- `muGrid_apply_one_within_column`, used here only to strip the row index to `0`.
  have key : ∀ (h' : OddOrder.Peterfalvi.S06.Hypothesis (↥M)) [NeZero (Nat.card h'.W1)]
      (χ : (h'.W2.subgroupOf (h'.W1 ⊔ h'.W2)) →* ℂˣ) (k : Fin (Nat.card h'.W1)),
      ((h'.columnFamily χ).mu k : ClassFunction (↥M) ℂ) 1
        = ((h'.columnFamily χ).mu 0 : ClassFunction (↥M) ℂ) 1 := by
    intro h' _ χ k
    have hd := h'.columnFamily_difference_apply_one χ k
    simp only [SignedIrreducibleDifferenceFamily.difference_apply,
      SignedIrreducibleDifferenceFamily.classFunction_apply, ClassFunction.sub_apply] at hd
    exact sub_eq_zero.mp hd
  unfold Hypothesis.muGrid
  simp only [key]
  exact (columnFamily_mu_zero_apply_one_eq_of_ne_one h hp (hcol_ne j hj) (hcol_ne j' hj')).symm

/-- **§10 degree independence** (Peterfalvi (10.3), full statement at the materialized `μ`-grid
level): for nontrivial columns (`0 < j, j' < w₂`) the common degree `μ_{ij}(1) = d` is independent
of *both* the row `i` and the (nontrivial) column `j`.  This is the genuine (10.3) degree constancy,
combining the within-column constancy `muGrid_apply_one_within_column` (the `i`-independence (4.5.a))
with the cross-column constancy `muGrid_apply_one_cross_column` (the `j`-independence via Theorem
(8.8) `w₂` prime + Pontryagin).  It is exactly what populates `CharacterParameters.degree_independent`
once the common value `d` is named (at producer-construction time, where `hw2` is available). -/
theorem Hypothesis.muGrid_apply_one_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (hw2 : (hyp.w2).Prime) (i i' : Fin hyp.w1) {j j' : Fin hyp.w2}
    (hj : j ≠ 0) (hj' : j' ≠ 0) :
    hyp.muGrid hG hodd i j 1 = hyp.muGrid hG hodd i' j' 1 := by
  rw [hyp.muGrid_apply_one_within_column hG hodd i j,
    hyp.muGrid_apply_one_cross_column hG hodd hw2 hj hj',
    ← hyp.muGrid_apply_one_within_column hG hodd i' j']

open scoped FiniteInduce in
/-- **§10 column sign** (Peterfalvi (10.3) `δ_j`): the sign `δ_j ∈ {±1}` of the `j`-th materialized
column, read off from the §6 `columnFamily` of the §10→§6 bridge (the same reconstruction as
`Hypothesis.muGrid`).  This is the genuine source for `CharacterParameters.delta`. -/
noncomputable def Hypothesis.muColumnSign [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (j : Fin hyp.w2) : ℤ := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  exact (h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).sign

open scoped FiniteInduce in
open OddOrder.Peterfalvi.S06 in
/-- **§10 cross-column sign constancy** (Peterfalvi (10.3), the `δ_j`-independence): the column sign
`δ_j` is independent of the nontrivial column `0 < j < w₂`.  Wires the §6 prime-order sign corollary
`columnFamily_mu_zero_sign_eq_of_ne_one` through the `muColumnSign` materialization (same Pontryagin
prime count + nontrivial-dual argument as `muGrid_apply_one_cross_column`). -/
theorem Hypothesis.muColumnSign_eq_of_ne [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (hw2 : (hyp.w2).Prime) {j j' : Fin hyp.w2}
    (hj : j ≠ 0) (hj' : j' ≠ 0) :
    hyp.muColumnSign hG hodd j = hyp.muColumnSign hG hodd j' := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hp : (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).Prime := by
    rw [h.card_charGroup_W2,
      ← (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : h.W2 ≤ h.W1 ⊔ h.W2)).toEquiv),
      hcardW2sub]
    exact hw2
  have hcol_ne : ∀ (k : Fin hyp.w2), k ≠ 0 →
      finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm k) ≠ 1 := by
    intro k hk heq
    rw [← finCardEquivCharacterGroup_zero (h.W2.subgroupOf (h.W1 ⊔ h.W2))] at heq
    have hk0 : finCongr hcardW2sub.symm k = 0 := (finCardEquivCharacterGroup _).injective heq
    apply hk
    have hval : (k : ℕ) = 0 := by simpa using congrArg Fin.val hk0
    exact Fin.ext hval
  unfold Hypothesis.muColumnSign
  exact columnFamily_mu_zero_sign_eq_of_ne_one h hp (hcol_ne j' hj') (hcol_ne j hj)

open scoped FiniteInduce in
/-- **§10 column-`0` sign** (Peterfalvi (10.3) / (4.4) `δ_0 = 1`): the sign `δ_0` of the trivial
column is `1`.  The column-`0` dual is the trivial character (`finCardEquivCharacterGroup_zero`), and
the trivial column has sign `1` (`certainType_zero_column_anchor.1`, the `μ_{00} = 1_L` anchor).
This is the `δ_0 = 1` normalisation used by the (10.5) Dade-image identity (the column-`0` term in
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` is reconciled against `ω_{i0}^σ` with unit sign). -/
theorem Hypothesis.muColumnSign_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    hyp.muColumnSign hG hodd 0 = 1 := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  have esign : hyp.muColumnSign hG hodd 0
      = (h.columnFamily (finCardEquivCharacterGroup _
          (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).sign := by
    unfold Hypothesis.muColumnSign; rfl
  rw [esign, hdual0]
  exact h.certainType_zero_column_anchor.1

open scoped FiniteInduce in
/-- **§10 μ-grid normalization** (Peterfalvi (4.1)/(4.3.b)): each materialized certain-type
character `μ_{ij}` is an irreducible character of `M`, hence has norm one, `(μ_{ij}, μ_{ij}) = 1`.
Read off the §6 `columnFamily` (whose `mu` are irreducible) through the `muGrid` reconstruction. -/
theorem Hypothesis.muGrid_inner_self [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    ClassFunction.inner (hyp.muGrid hG hodd i j) (hyp.muGrid hG hodd i j) = 1 := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  rw [emj, OddOrder.RepresentationTheory.irreducibleCharacter_inner, if_pos rfl]

open scoped FiniteInduce in
/-- **§10 μ-grid cross-column orthogonality** (Peterfalvi (4.3.b)): certain-type characters from
*different* `W₂`-columns are orthogonal, `(μ_{ij}, μ_{i'j'}) = 0` for `j ≠ j'` (any rows `i, i'`).
The §6 `columnFamily_cross_products_zero` (via (4.1)), read through `muGrid`, with a case split on
which rows are `0`.  In particular `(μ_{ij}, μ_{i0}) = 0` for `0 < j`, the cross term in the
norm `‖α_{ij}‖² = 2 + n²` of the (10.5) Dade-image argument. -/
theorem Hypothesis.muGrid_inner_cross_column [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i i' : Fin hyp.w1) {j j' : Fin hyp.w2} (hjj' : j ≠ j') :
    ClassFunction.inner (hyp.muGrid hG hodd i j) (hyp.muGrid hG hodd i' j') = 0 := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- The two `W₂`-duals differ (different columns).
  have hχne : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2)) (finCongr hcardW2sub.symm j)
      ≠ finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2)) (finCongr hcardW2sub.symm j') :=
    fun heq => hjj' ((finCongr hcardW2sub.symm).injective
      ((finCardEquivCharacterGroup _).injective heq))
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have emj' : hyp.muGrid hG hodd i' j'
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j'))).mu
          (finCongr hcardW1.symm i') : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  rw [emj, emj']
  have hz : (⟨1, h.one_lt_card_W1⟩ : Fin (Nat.card h.W1)) ≠ 0 := Fin.ne_of_val_ne (by simp)
  rcases eq_or_ne (finCongr hcardW1.symm i) 0 with hi | hi <;>
    rcases eq_or_ne (finCongr hcardW1.symm i') 0 with hi' | hi'
  · rw [hi, hi']; exact (h.columnFamily_cross_products_zero hχne hz hz).2.2.2
  · rw [hi]; exact (h.columnFamily_cross_products_zero hχne hz hi').2.2.1
  · rw [hi']; exact (h.columnFamily_cross_products_zero hχne hi hz).2.1
  · exact (h.columnFamily_cross_products_zero hχne hi hi').1

open scoped FiniteInduce in
/-- **§10 μ-grid within-column orthogonality** (Peterfalvi (4.3.b)): distinct rows of the same
`W₂`-column give orthogonal certain-type characters, `(μ_{ij}, μ_{i'j}) = 0` for `i ≠ i'`.  The
§6 `columnFamily` `mu` are distinct irreducibles (`irreducibleCharacter_inner` + the family's
`injective` field), read through `muGrid`.  With `muGrid_inner_self` this completes the
orthonormality of the full `μ`-grid. -/
theorem Hypothesis.muGrid_inner_within_column [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {i i' : Fin hyp.w1} (j : Fin hyp.w2) (hii' : i ≠ i') :
    ClassFunction.inner (hyp.muGrid hG hodd i j) (hyp.muGrid hG hodd i' j) = 0 := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hrowne : (finCongr hcardW1.symm i) ≠ (finCongr hcardW1.symm i') :=
    fun heq => hii' ((finCongr hcardW1.symm).injective heq)
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have emj' : hyp.muGrid hG hodd i' j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i') : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  rw [emj, emj', OddOrder.RepresentationTheory.irreducibleCharacter_inner,
    if_neg (fun heq => hrowne ((h.columnFamily _).injective heq))]

open scoped FiniteInduce in
/-- **§10 μ-grid entries are irreducible** (Peterfalvi (4.3.b)): each `μ_{ij}` is an irreducible
character of `M`, being the §6 certain-type character `(columnFamily χ₂).mu i` (an
`IrreducibleCharacter`).  This is the `μ_{ij} ∈ ℤ[Irr M]` input that makes `α_{ij}^τ` a virtual
character of `G`, hence the inner products of the (10.5) `a = 0` argument integers. -/
theorem Hypothesis.muGrid_isIrreducible [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    IsIrreducibleCharacter (hyp.muGrid hG hodd i j) := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  rw [show hyp.muGrid hG hodd i j
    = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
        (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) from by unfold Hypothesis.muGrid; rfl]
  exact OddOrder.RepresentationTheory.IrreducibleCharacter.isIrreducible _

open scoped FiniteInduce in
/-- **§10 column sum is induced from `M'`, hence vanishes off `M'`** (Peterfalvi (10.5)/(4.5.a)):
the `W₂`-column sum `μ_k = ∑_{0≤i<w₁} μ_{ik}` equals the induced character `Ind_{M'}^M (Res_{M'} μ_{0k})`
(`induce_restrict_certainType_eq`), so it vanishes on every `x ∉ M' = [M,M]`.

This is the structural fact making `μ_k − dζ̄` `A_0`-supported in the (10.5) `a = 0` argument (both
`μ_k` and `ζ̄` vanish off `M'`, and the degrees cancel) — so the Dade isometry `τ` transfers it
(`tau_inner_eq_of_supported`), with no Dade–coherence adjunction needed. -/
theorem Hypothesis.muGrid_column_sum_vanishes_off_derived [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (k : Fin hyp.w2)
    {x : ↥M} (hx : x ∉ (derivedInG M).subgroupOf M) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) x = 0 := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- The column sum is the induced character `Ind_{M'}^M (Res_{M'} μ_{0k})` (`induce_restrict`).
  have hsum : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      = ClassFunction.induce h.K
          (ClassFunction.restrict h.K
            ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu 0
              : ClassFunction ↥M ℂ)) := by
    rw [h.induce_restrict_certainType_eq, ← Equiv.sum_comp (finCongr hcardW1.symm)
      (fun i' => ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu i'
        : ClassFunction ↥M ℂ))]
    exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)
  rw [hsum]
  -- `K = M' = [M,M]` is normal, so the induced character vanishes off it.
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  haveI : h.K.Normal := hKnormal
  exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hx

open scoped FiniteInduce in
/-- **§10 column sum lies in the family `S`** (Peterfalvi (10.5)/(4.5.a)): for `0 < k < w₂`, the
`W₂`-column sum `μ_k = ∑_{i} μ_{ik}` is the induced character `Ind_{M'}^M θ` of a *non-trivial*
irreducible `θ` of `M'` (`exists_irreducible_restrict_certainType`), hence lies in
`S = inducedFamily M`.  Non-triviality follows from the degree: `θ(1) = (Res_{M'} μ_{0k})(1) =
μ_{0k}(1) ≠ 1` (the caller supplies `μ_{0k}(1) = d > 1` from (10.3)).

This is the `μ_k ∈ ℤ[S]` input that the coherent extension `τ₁` consumes: it lets `μ_k^{τ₁}`
participate in the isometry (`‖μ_k^{τ₁}‖² = ‖μ_k‖² = w₁`) and the `(μ_k − dζ̄)^τ = μ_k^{τ₁} −
dζ̄^{τ₁}` split of the (10.5) `a = 0` argument. -/
theorem Hypothesis.muGrid_column_sum_mem_inducedFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (k : Fin hyp.w2)
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) ∈ inducedFamily M := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨θ, hθeq, hind⟩ :=
    h.exists_irreducible_restrict_certainType (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))
  -- row-0 entry equals the certain-type character `μ_{0k}` (`finCongr` fixes `0`).
  have hrow0 : hyp.muGrid hG hodd 0 k
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu 0
          : ClassFunction ↥M ℂ) := by
    have hfc : (finCongr hcardW1.symm (0 : Fin hyp.w1)) = (0 : Fin (Nat.card h.W1)) := by simp
    rw [show hyp.muGrid hG hodd 0 k
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu
          (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) from by unfold Hypothesis.muGrid; rfl, hfc]
  -- `θ ≠ 1`: else `μ_{0k}(1) = θ(1) = 1`, contradicting `hdk1`.
  have hθne : θ ≠ trivialIrreducibleCharacter ↥h.K := by
    intro htriv
    apply hdk1
    rw [hrow0]
    have h2 : (ClassFunction.restrict h.K
        ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu 0
          : ClassFunction ↥M ℂ)) (1 : ↥h.K) = (θ : ClassFunction ↥h.K ℂ) (1 : ↥h.K) := by
      rw [hθeq]
    rw [ClassFunction.restrict_apply] at h2
    rw [htriv] at h2
    simpa using h2
  -- The column sum is `Ind_{M'}^M θ`, so it lies in `S`.
  refine ⟨θ, hθne, ?_⟩
  show (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
    = ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)
  rw [hind, ← Equiv.sum_comp (finCongr hcardW1.symm)
    (fun i' => ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu i'
      : ClassFunction ↥M ℂ))]
  exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)

open scoped FiniteInduce in
/-- **§10 column-sum norm** (Peterfalvi (10.5)/(10.6), `‖μ_k‖² = w₁`): the `W₂`-column sum
`μ_k = ∑_{0≤i<w₁} μ_{ik}` has squared norm `w₁`, since its `w₁` summands are orthonormal
(`muGrid_inner_self` on the diagonal, `muGrid_inner_within_column` off it).  This is the
`‖μ_k^{τ₁}‖² = w₁` factor in the Cauchy–Schwarz bound of the (10.5) `a = 0` argument. -/
theorem Hypothesis.muGrid_column_sum_inner_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (j : Fin hyp.w2) :
    ClassFunction.inner (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j)
        (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) = (hyp.w1 : ℂ) := by
  haveI := hyp.finiteG
  classical
  -- per-pair inner products: `1` on the diagonal, `0` off it.
  have hpair : ∀ i i' : Fin hyp.w1, ClassFunction.inner (hyp.muGrid hG hodd i j)
      (hyp.muGrid hG hodd i' j) = (if i' = i then 1 else 0) := by
    intro i i'
    by_cases h : i' = i
    · subst h; rw [if_pos rfl]; exact hyp.muGrid_inner_self hG hodd i' j
    · rw [if_neg h]; exact hyp.muGrid_inner_within_column hG hodd j (Ne.symm h)
  have hrow : ∀ i : Fin hyp.w1, ClassFunction.inner (hyp.muGrid hG hodd i j)
      (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j) = 1 := by
    intro i
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl (fun i' _ => hpair i i'), Finset.sum_ite_eq' Finset.univ i]
    simp
  rw [OddOrder.RepresentationTheory.inner_sum_left,
    Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

open scoped FiniteInduce in
/-- **§10 μ-grid ⊥ a degree-distinct irreducible** (Peterfalvi (10.5), `(μ_{ij}, ζ) = 0`): the
certain-type character `μ_{ij}` is orthogonal to any irreducible character `χ` of a *different*
degree.  Both are irreducible, so `(μ_{ij}, χ) ∈ {0, 1}` and equals `1` only if `μ_{ij} = χ`; a
degree mismatch `μ_{ij}(1) ≠ χ(1)` rules that out.

This is the orthogonality `(μ_{ij}, ζ) = 0` (and `(μ_{ij}, ζ̄) = 0`) to the degree-`w₁` member
`ζ ∈ S` in the norm `‖α_{ij}‖² = 2 + n²` of the (10.5) `a = 0` argument: the caller supplies the
degree mismatch (`μ_{i0}(1) = 1 ≠ w₁`, and `μ_{ij}(1) = d ≠ w₁` since `n·w₁ = d − δ`, `d > 1`,
`w₁ > 1`).  It needs no Clifford theory — only orthonormality of irreducibles. -/
theorem Hypothesis.muGrid_inner_eq_zero_of_apply_one_ne [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {χ : ClassFunction ↥M ℂ} (hχirr : IsIrreducibleCharacter χ)
    (hne : hyp.muGrid hG hodd i j 1 ≠ χ 1) :
    ClassFunction.inner (hyp.muGrid hG hodd i j) χ = 0 := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have hμirr : IsIrreducibleCharacter (hyp.muGrid hG hodd i j) := by
    rw [emj]; exact OddOrder.RepresentationTheory.IrreducibleCharacter.isIrreducible _
  rw [OddOrder.RepresentationTheory.irr_cf_inner hμirr hχirr,
    if_neg (fun heq => hne (by rw [heq]))]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖α_{ij}‖² = 2 + n²`**: the squared norm of the virtual character
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ`.  The triple `{μ_{ij}, μ_{i0}, ζ}` is orthonormal — `μ_{ij}` and
`μ_{i0}` are orthonormal certain-type characters (`muGrid_inner_self` / `muGrid_inner_cross_column`,
`j ≠ 0`), and both are orthogonal to the degree-distinct irreducible `ζ`
(`muGrid_inner_eq_zero_of_apply_one_ne`, from the degree mismatches `hdζ`/`h0ζ`) — so
`‖α‖² = 1 + δ² + n² = 2 + n²` (`δ² = 1`).  The reversed inner products use `inner_conj_symm`.

This is the `‖α_{ij}^τ‖²` input to the Cauchy–Schwarz bound of the (10.5) `a = 0` argument (the
Dade isometry `τ` preserves the norm).  The caller supplies the degree mismatches
`μ_{i0}(1) = 1 ≠ w₁` and `μ_{ij}(1) = d ≠ w₁` (from `n·w₁ = d − δ`, `d > 1`, `w₁ > 1`). -/
theorem Hypothesis.muGridAlpha_inner_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) {δ : ℤ} {n : ℕ}
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = 2 + (n : ℂ) ^ 2 := by
  haveI := hyp.finiteG
  classical
  have hA := hyp.muGrid_inner_self hG hodd i j
  have hB := hyp.muGrid_inner_self hG hodd i 0
  have hZ : ClassFunction.inner ζ ζ = 1 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]
  have hP := hyp.muGrid_inner_cross_column hG hodd i i hj0
  have hP' := hyp.muGrid_inner_cross_column hG hodd i i (Ne.symm hj0)
  have hQ := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hζirr hdζ
  have hR := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr h0ζ
  have hQ' : ClassFunction.inner ζ (hyp.muGrid hG hodd i j) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i j) ζ, hQ, star_zero]
  have hR' : ClassFunction.inner ζ (hyp.muGrid hG hodd i 0) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i 0) ζ, hR, star_zero]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    hA, hB, hZ, hP, hP', hQ, hQ', hR, hR', star_intCast, star_natCast,
    mul_zero, zero_mul, sub_zero, zero_sub, mul_one, mul_neg, neg_neg, neg_zero]
  rcases hδpm with h | h <;> subst h <;> push_cast <;> ring

open scoped FiniteInduce in
/-- **§10 `W₁`-vanishing of the column difference** (Peterfalvi (10.5), first step, via (4.3.c) +
(4.4)): on `W₁^#`, the materialized character `μ_{ij}` equals `δ_j` times the column-`0` character
`μ_{i0}`.  Indeed `x ∈ W₁^# ⊆ V = W − W₂`, so (4.3.c) gives `μ_{ij}(x) = δ_j·ω_{ij}(x)` and
`μ_{i0}(x) = δ_0·ω_{i0}(x) = ω_{i0}(x)` (`δ_0 = 1` by (4.4)); on `W₁` the linear characters `ω_{ij}`
and `ω_{i0}` agree (the `W₂`-dual is trivial on `W₁`, `wSnd = 1`), so `μ_{ij}(x) = δ_j·μ_{i0}(x)`.
This is the `μ`-grid form of the (10.5) claim that `α_{ij}` vanishes on `W₁`. -/
theorem Hypothesis.muGrid_apply_eq_columnSign_mul_zeroColumn_of_mem_W1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {x : ↥M} (hxW1 : (x : G) ∈ hyp.typeP.W1) (hx1 : x ≠ 1) :
    hyp.muGrid hG hodd i j x
      = (hyp.muColumnSign hG hodd j : ℂ) * hyp.muGrid hG hodd i 0 x := by
  haveI := hyp.finiteG
  classical
  -- Reconstruct the §6 host and instances exactly as in `Hypothesis.muGrid`/`muColumnSign`
  -- (instances synthesized, *not* provided explicitly, to match the def's `unfold; rfl`).
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- `x` as an element of `h.W1` and of `sdiff.V = W − W₂`.
  have hxhW1 : x ∈ h.W1 := Subgroup.mem_subgroupOf.mpr hxW1
  have hxV : x ∈ h.sdiffTICyclicHypothesis.V := by
    refine ⟨(le_sup_left : h.W1 ≤ _) hxhW1, fun hxW2 => hx1 ?_⟩
    exact Subgroup.mem_bot.mp (h.W_disjoint.le_bot (Subgroup.mem_inf.mpr ⟨hxhW1, hxW2⟩))
  -- The generic `W₁`-collapse: `(columnFamily χ).mu k x = δ_χ · (columnFamily 1).mu k x`.
  have keyW1 : ∀ (χ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (k : Fin (Nat.card h.W1)),
      ((h.columnFamily χ).mu k : ClassFunction ↥M ℂ) x
        = ((h.columnFamily χ).sign : ℂ) * ((h.columnFamily 1).mu k : ClassFunction ↥M ℂ) x := by
    intro χ k
    have hwsub : (⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩ : ↥h.sdiffTICyclicHypothesis.W)
        ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W :=
      Subgroup.mem_subgroupOf.mpr hxhW1
    have hwsnd : h.sdiffTICyclicHypothesis.wSnd
        ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩ = 1 :=
      h.sdiffTICyclicHypothesis.wSnd_eq_one_of_mem_W1 hwsub
    -- chiColumn value formula (inline, valid for the bare `Hypothesis`).
    have hchiform : ∀ (χ' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ),
        (h.chiColumn χ' k : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
            ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩
          = ((h.w1CharEquiv k) (h.sdiffTICyclicHypothesis.wFst
              ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩) : ℂ)
            * (χ' (h.sdiffTICyclicHypothesis.wSnd
              ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩) : ℂ) := by
      intro χ'
      rw [OddOrder.Peterfalvi.S06.Hypothesis.chiColumn, h.sdiffTICyclicHypothesis.omega_apply]
      change (((h.w1CharEquiv k) (h.sdiffTICyclicHypothesis.wFst _)
          * χ' (h.sdiffTICyclicHypothesis.wSnd _) : ℂˣ) : ℂ) = _
      rw [Units.val_mul]
    -- the `W₂`-dual factor is trivial on `W₁` (`wSnd = 1`), so the value is `χ`-independent.
    have hsnd1 : ∀ (χ' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ),
        (χ' (h.sdiffTICyclicHypothesis.wSnd ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩) : ℂˣ)
          = 1 := fun χ' => by rw [hwsnd]; exact map_one χ'
    have hchieq : (h.chiColumn χ k : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩
        = (h.chiColumn 1 k : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩ := by
      rw [hchiform χ, hchiform 1, hsnd1 χ, hsnd1 1]
    rw [h.certainType_apply_eq_of_mem_V χ k hxV, h.certainType_apply_eq_of_mem_V 1 k hxV,
      h.certainType_zero_column_anchor.1, hchieq, Int.cast_one, one_mul]
  -- Evaluate `muGrid`/`muColumnSign` in `columnFamily` terms (the `unfold; rfl` idiom of the
  -- producer's `hmg`), then apply `keyW1` (column `0` is the trivial dual).
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have em0 : hyp.muGrid hG hodd i 0
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have esign : hyp.muColumnSign hG hodd j
      = (h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).sign := by
    unfold Hypothesis.muColumnSign; rfl
  rw [emj, em0, esign, hdual0]
  exact keyW1 _ _

open scoped FiniteInduce in
/-- **§10 reconciliation on `V`** (the M-side ↔ σ-side link of (10.5)): for `v ∈ V = typePV`,
`μ_{ij}(v) = δ_j · ω_{ij}^σ(v)` where `ω^σ = alignedOmegaSigmaGrid`.  Both sides reduce to the §6
column character `chiColumn χ₂ i` evaluated at `v`: the M-side by (4.3.c)
(`certainType_apply_eq_of_mem_V`, giving `μ_{ij}(v) = δ_j·chiColumn(v)`), the σ-side because
`alignedOmegaSigma` is `σ_∫` of the transported `chiColumn`, restored on `V` by
`sigmaIntegral_apply_of_mem_V`; the `W ≤ M ≤ G` isomorphism `e` carries `v` to itself, so the two
`chiColumn` arguments agree.  This is the alignment that makes the (10.5) Dade-image identity hold
(impossible with the independently-indexed `omegaSigmaGrid`). -/
theorem Hypothesis.muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {v : G} (hv : v ∈ typePV M hyp.typeP) (hvM : v ∈ M) :
    hyp.muGrid hG hodd i j ⟨v, hvM⟩
      = (hyp.muColumnSign hG hodd j : ℂ) * hyp.alignedOmegaSigmaGrid hG hodd i j v := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    ⟨tic.toDadeHypothesis.fullDadeIsometryData
      (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl))⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  set χ₂ := finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2)) (finCongr hcardW2sub.symm j)
    with hχ₂
  have hvtic : v ∈ tic.V := hv
  have hWeq : h.W1 ⊔ h.W2 = hyp.typeP.W.subgroupOf M := typePData_sup_subgroupOf_eq hyp.typeP
  have hvW : (⟨v, hvM⟩ : ↥M) ∈ h.W1 ⊔ h.W2 := by
    rw [hWeq, Subgroup.mem_subgroupOf]; exact hv.1
  -- `⟨v, hvM⟩ ∈ sdiff.V = W − W₂` (`v ∈ typePV = W − (W₁ ∪ W₂) ⊆ W − W₂`).
  have hvsdiffV : (⟨v, hvM⟩ : ↥M) ∈ h.sdiffTICyclicHypothesis.V := by
    refine ⟨hvW, ?_⟩
    intro hvW2
    exact hv.2 (Or.inr (Subgroup.mem_subgroupOf.mp hvW2))
  -- the transport `e` carries `v` to itself (same underlying `G`-element).
  have he_coe : ((e ⟨v, tic.V_subset_W hvtic⟩ : ↥(h.W1 ⊔ h.W2)) : ↥M) = ⟨v, hvM⟩ := by
    apply Subtype.ext
    show ((MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm
        ((Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm
          ⟨v, tic.V_subset_W hvtic⟩) : ↥M) : G) = v
    rw [MulEquiv.subgroupCongr_apply]; rfl
  -- the two `chiColumn` arguments (from (4.3.c) and from `e`) agree.
  have harg : (⟨⟨v, hvM⟩, h.sdiffTICyclicHypothesis.V_subset_W hvsdiffV⟩
        : ↥h.sdiffTICyclicHypothesis.W)
      = e ⟨v, tic.V_subset_W hvtic⟩ := by
    apply Subtype.ext; rw [he_coe]
  -- unfold `alignedOmegaSigma` to `chiColumn (e ⟨v⟩)` on `V`.
  have eaos : hyp.alignedOmegaSigmaGrid hG hodd i j v
      = (h.chiColumn χ₂ (finCongr hcardW1.symm i) : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          (e ⟨v, tic.V_subset_W hvtic⟩) := by
    unfold Hypothesis.alignedOmegaSigmaGrid
    rw [tic.sigmaIntegral_apply_of_mem_V rfl app _ hvtic, ClassFunction.compHom_apply]
    rfl
  -- unfold `muGrid`/`muColumnSign` and apply (4.3.c); the two `chiColumn` arguments agree.
  have emj : hyp.muGrid hG hodd i j = (h.columnFamily χ₂).mu (finCongr hcardW1.symm i) := by
    unfold Hypothesis.muGrid; rfl
  have esign : hyp.muColumnSign hG hodd j = (h.columnFamily χ₂).sign := by
    unfold Hypothesis.muColumnSign; rfl
  rw [emj, esign, eaos,
    h.certainType_apply_eq_of_mem_V χ₂ (finCongr hcardW1.symm i) hvsdiffV, harg]

open scoped FiniteInduce in
/-- **§10 column-`0` degree** (Peterfalvi (4.4)): `μ_{i0}(1) = 1`.  The column-`0` character is
`K`-trivial (`μ_{00} = 1_L` by the (4.4) anchor), of degree `1`; by within-column degree constancy
(`muGrid_apply_one_within_column`) every `μ_{i0}` has the same degree. -/
theorem Hypothesis.muGrid_zero_column_apply_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) :
    hyp.muGrid hG hodd i 0 1 = 1 := by
  haveI := hyp.finiteG
  classical
  rw [hyp.muGrid_apply_one_within_column hG hodd i 0]
  -- Reconstruct the §6 host, as in `Hypothesis.muGrid`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  have hrow0 : (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 0 := by apply Fin.ext; simp
  have e00 : hyp.muGrid hG hodd 0 0
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).mu
          (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  rw [e00, hdual0, hrow0, h.certainType_zero_column_anchor.2,
    OddOrder.RepresentationTheory.trivialClassFunction_apply]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), support half**: the virtual character
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` (for `ζ` induced from `M'`, the materialized degrees `d`, sign
`δ_j = δ`, and `n` with `n·w₁ = d − δ`) is supported on `A_0(M)`.

This is the **dade0-free** half of (10.5), following Peterfalvi's argument verbatim:
* `α_{ij}` vanishes at `1` (by `n·w₁ = d − δ` and `μ_{i0}(1) = 1`) and on `W₁^#`
  (`muGrid_apply_eq_columnSign_mul_zeroColumn_of_mem_W1` and `ζ` vanishing off `M'`);
* `ζ`, being induced from the normal `M'`, vanishes off `M'`, so a support point `z ∉ M'` is, by
  (2.1) (`mem_compl_conj_into_W`), `M`-conjugate to `x·y` with `x ∈ W₁^#`, `y ∈ W₂`; `y ≠ 1` (else
  `z` is conjugate into `W₁^#`, where `α` vanishes), so `x·y ∈ V` and `z ∈ V^M`;
* a support point `z ∈ M'` lies in `(M')^# ⊆ A(M)` (it centralizes itself).

Hence `Supp(α_{ij}) ⊆ A(M) ∪ V^G = A_0(M)`. -/
theorem Hypothesis.muGrid_alpha_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {i : Fin hyp.w1} {j : Fin hyp.w2} (_hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ) :
    (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ).support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  classical
  -- `ζ` is induced from the normal `M'`, hence vanishes off `M'`.
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  -- the §6 host (for (2.1)) and the abbreviation `α`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  set α : ClassFunction ↥M ℂ :=
    hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ with hαdef
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `α(1) = 0`, hence `z ≠ 1`.
  have hα1 : α 1 = 0 := by
    rw [hαdef, ClassFunction.sub_apply, ClassFunction.sub_apply, ClassFunction.smul_apply,
      ClassFunction.smul_apply, hdeg, hμ0, hζ1, mul_one]
    have hnfC : (n : ℂ) * (hyp.w1 : ℂ) = (d : ℂ) - (δ : ℂ) := by exact_mod_cast hnf
    rw [hnfC]; ring
  have hz1 : z ≠ 1 := fun h0 => hz (h0 ▸ hα1)
  show (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  by_cases hzM' : (z : G) ∈ derivedInG M
  · -- `z ∈ M'`: lands in `A(M)` (it centralizes itself).
    left
    exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
      ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  · -- `z ∉ M'`: use (2.1) to conjugate into `W`, landing in `V^M`.
    right
    have hzK : z ∉ h.K := fun hk => hzM' (Subgroup.mem_subgroupOf.mp hk)
    obtain ⟨c, x, hxW1, hx1, y, hyW2, hconj⟩ := h.mem_compl_conj_into_W hzK
    have hxG : (x : G) ∈ hyp.typeP.W1 := Subgroup.mem_subgroupOf.mp hxW1
    have hyG : (y : G) ∈ hyp.typeP.W2 := Subgroup.mem_subgroupOf.mp hyW2
    -- `α` is conjugation-invariant, so `α z = α (x·y)`.
    have hconjα : α z = α (x * y) := by
      rw [← hconj]
      have hce := α.conj_eq z c⁻¹
      rw [inv_inv] at hce
      exact hce.symm
    -- `x ∉ M'` (`W₁ ∩ M' = 1`, `M_complement`), so `ζ` also vanishes at `x`.
    have hxK : x ∉ h.K := fun hk =>
      hx1 ((Subgroup.disjoint_def.mp h.isComplement.disjoint) hk hxW1)
    -- `y ≠ 1`: otherwise `α z = α x = 0`, contradicting `z ∈ Supp(α)`.
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hz
      rw [hconjα, mul_one, hαdef, ClassFunction.sub_apply, ClassFunction.sub_apply,
        ClassFunction.smul_apply, ClassFunction.smul_apply,
        hyp.muGrid_apply_eq_columnSign_mul_zeroColumn_of_mem_W1 hG hodd i j hxG hx1, hδj,
        hζvanish hxK]
      ring
    -- `x·y ∈ V`, so `z ∈ V^M`.
    rw [OddOrder.GroupTheory.mem_conjClassSet]
    refine ⟨(x : G) * (y : G), ?_, (c : G), ?_⟩
    · -- `(x:G)·(y:G) ∈ typePV`
      have hxyW : (x : G) * (y : G) ∈ hyp.typeP.W := by
        rw [hyp.typeP.W_eq]; exact mul_mem (Subgroup.mem_sup_left hxG) (Subgroup.mem_sup_right hyG)
      simp only [typePV, Set.mem_diff, Set.mem_union, SetLike.mem_coe, not_or]
      refine ⟨hxyW, ?_, ?_⟩
      · intro hmem
        apply hy1
        have hyW1 : (y : G) ∈ hyp.typeP.W1 := by
          have heq : (y : G) = (x : G)⁻¹ * ((x : G) * (y : G)) := by group
          rw [heq]; exact mul_mem (inv_mem hxG) hmem
        have := (typePData_disjoint_W1_W2 hyp.typeP).le_bot (Subgroup.mem_inf.mpr ⟨hyW1, hyG⟩)
        rw [Subgroup.mem_bot] at this
        exact Subtype.ext this
      · intro hmem
        apply hx1
        have hxW2 : (x : G) ∈ hyp.typeP.W2 := by
          have heq : (x : G) = ((x : G) * (y : G)) * (y : G)⁻¹ := by group
          rw [heq]; exact mul_mem hmem (inv_mem hyG)
        have := (typePData_disjoint_W1_W2 hyp.typeP).le_bot (Subgroup.mem_inf.mpr ⟨hxG, hxW2⟩)
        rw [Subgroup.mem_bot] at this
        exact Subtype.ext this
    · -- `(c:G)·((x:G)·(y:G))·(c:G)⁻¹ = (z:G)`
      have hconjG : (c : G)⁻¹ * (z : G) * (c : G) = (x : G) * (y : G) := by
        have := congrArg (M.subtype) hconj
        rwa [map_mul, map_mul, map_inv] at this
      rw [← hconjG]; group

/-- The character parameters obtained in Peterfalvi (10.2)--(10.3).

The arithmetic fields are now de-opaqued to genuine identities: `degree_independent` is the
degree constancy `μ_{ij}(1) = d` (4.5.a), `n_formula` is `n·w₁ = d − δ`, and `alpha` is the
genuine virtual character `μ_{ij} − δ·μ_{i0} − n·ζ` (10.5).  The `δ_j`-independence (10.3) is now a
genuine clause of `w2_prime_and_parameter_independence` (via `Hypothesis.muColumnSign`), no longer a
placeholder field. -/
structure CharacterParameters {M : Subgroup G} (hyp : Hypothesis M) where
  zeta : ClassFunction ↥M ℂ
  zeta_mem_S : zeta ∈ hyp.Sset
  /-- (10.2): `ζ` is irreducible.  De-opaqued from a placeholder `Prop` to the genuine
  irreducibility predicate, now that `exists_zeta_in_inducedFamily_degree_w1` constructs such a
  `ζ`. -/
  zeta_irreducible : IsIrreducibleCharacter zeta
  d : ℕ
  delta : ℤ
  n : ℕ
  w2_prime : hyp.w2.Prime
  d_gt_one : 1 < d
  mu : Fin hyp.w1 → Fin hyp.w2 → ClassFunction ↥M ℂ
  omegaSigma : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ
  /-- (10.3) degree independence (4.5.a): `d = μ_{ij}(1)` is independent of the indices, for
  `0 ≤ i < w₁` and `0 < j < w₂`.  De-opaqued from a placeholder `Prop` to the genuine degree
  identity. -/
  degree_independent : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → mu i j 1 = (d : ℂ)
  /-- (10.3) the index relation `n = (d − δ)/w₁ ∈ ℕ`, in the cleared form `n·w₁ = d − δ`.
  De-opaqued from a placeholder `Prop`. -/
  n_formula : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - delta
  /-- (10.5): `α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ`.  De-opaqued from a free field + placeholder
  formula to the genuine definition in terms of the `μ`-grid, `δ`, `n` and `ζ`. -/
  alpha : Fin hyp.w1 → Fin hyp.w2 → ClassFunction ↥M ℂ :=
    fun i j => mu i j - (delta : ℂ) • mu i 0 - (n : ℂ) • zeta
  alpha_def : ∀ i j, alpha i j = mu i j - (delta : ℂ) • mu i 0 - (n : ℂ) • zeta := by
    intro i j; rfl
  /-- (10.5), support half: for `0 < j < w₂`, `α_{ij}` is supported on `A_0(M)`.  De-opaqued (and
  dade0-free) — materialized in the producer from `Hypothesis.muGrid_alpha_support`. -/
  alpha_support : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → (alpha i j).support ⊆ hyp.A0
  zeta_tau1_norm_bound : Prop
  orthogonality_w1_lt_w2 : Prop
  typeV_parameter_formula : Prop
  typeV_coherence_formula : Prop

/-- **Peterfalvi (10.4)**: the coherent-extension hypothesis for the family of
characters in (10.1).

De-opaqued: instead of an unconstrained `tau1` field plus an opaque `tau1_extends_tau_on_S : Prop`,
this carries the *genuine* coherence datum `IsCoherent hyp.tau hyp.Sset hyp.A0` (Peterfalvi (5.1)).
Its bundled `extension` is Peterfalvi's `τ₁`, exposed as `CoherentHypothesis.tau1`: a lattice
isometry on `ℤ[S]` (`coherent.extension_inner_eq`) extending `τ` on the supported lattice
`ℤ[S, A₀]` (`coherent.extends_on_supported`).  This is exactly the content of (10.4.b) ("`S` is
coherent and `τ₁` is an extension of `τ` to `ℤ[S]`"), no longer a free map + placeholder `Prop`. -/
structure CoherentHypothesis {M : Subgroup G} [Fintype G] [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis M) (params : CharacterParameters hyp) where
  /-- (10.4.b): the family `S` is coherent; the bundled `extension` is Peterfalvi's `τ₁`. -/
  coherent : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0

namespace CoherentHypothesis

/-- **Peterfalvi's `τ₁`** (10.4.b): the coherent extension of the Dade isometry `τ` to `ℤ[S]`,
projected out of the bundled `IsCoherent` datum.  It is a lattice isometry on `ℤ[S]` and agrees
with `τ` on the supported lattice `ℤ[S, A₀(M)]`. -/
noncomputable def tau1 {M : Subgroup G} [Fintype G] [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G :=
  coh.coherent.extension

end CoherentHypothesis

/-- **Peterfalvi (8.8) for `M`, used at the start of (10.3)**: there is a maximal subgroup `S` of `G`
of **Type II** such that `|S : [S,S]| = w₂`.

This is exactly the opening sentence of the proof of (10.3) ("By Theorem (8.8), there is a maximal
subgroup `S` of `G` of Type II such that `|S:[S,S]| = w₂`"): the type-`P` maximal `M` of (10.1)
participates in the case-(b) configuration of Theorem (8.8), one of whose two maximal subgroups is
of Type II and shares the cyclic factor order `w₂`.  Tying the generic case-(b) datum
(`theorem88_caseB_holds`) to the *given* `M` is the content of (8.8)/(8.13) applied to `M`; it is
recorded here as a faithful obligation (its proof is currently a `sorry`, gated on the BG §16
partner-existence behind `theorem88_caseB_holds`). -/
theorem Hypothesis.exists_typeII_maximal_with_w2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ S : Subgroup G, S ∈ maximalSubgroups G ∧ IsTypeII S ∧
      ((derivedInG S).subgroupOf S).index = hyp.w2 := by
  -- The `M`-specific (8.8) partner now lives in §8 (`S10.exists_typeII_maximal_with_w2_of_typeP`),
  -- stated on the bare `TypePData`; here `hyp.w2 = |W₂(hyp.typeP)|`.
  simpa only [Hypothesis.w2, Hypothesis.W2] using
    OddOrder.Peterfalvi.S10.exists_typeII_maximal_with_w2_of_typeP hG hyp.typeP hyp.maximal
      hyp.type_alt

/-- **Peterfalvi (10.3), first clause**: `w₂` is prime.

By Theorem (8.8) there is a Type-II maximal subgroup `S` with `|S:[S,S]| = w₂`
(`exists_typeII_maximal_with_w2`); a Type-II maximal's cyclic factor `W₁(S)` has prime order
(Peterfalvi (8.6.a), carried by `TypePNontrivialCore`) and equals `|S:[S,S]|`
(`card_W1_eq_derived_index`), so `w₂` is prime.

This follows Peterfalvi's own proof of (10.3) verbatim and is **non-circular**: it does *not* route
through `no_typeV_maximal` (the way a generic case-(b) datum would, since `TypeVData` carries no
prime-order field), so it may be used to populate `CharacterParameters.w2_prime` *upstream* of the
(10.10) Type-V elimination — which is what unblocks the (10.2)/(10.3) producer below. -/
theorem Hypothesis.w2_prime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) : (hyp.w2).Prime := by
  obtain ⟨S, -, hSII, hindex⟩ := hyp.exists_typeII_maximal_with_w2 hG
  obtain ⟨dataII⟩ := hSII
  have hcard : Nat.card ↥dataII.typeP.W1 = hyp.w2 := by
    rw [dataII.typeP.card_W1_eq_derived_index]; exact hindex
  rw [← hcard]
  exact dataII.common.2.1

open scoped FiniteInduce in
/-- **Peterfalvi (10.3), arithmetic data**: the common nontrivial-column degree `d`, the sign
`δ`, and the integer `n = (d − δ)/w₁`, materialized from the §6 column family.

We pick a nontrivial column `j₀` (which exists because `w₂` is prime, hence `≥ 2`) and read off
`d = μ_{0 j₀}(1)` as a natural number (the degree of an irreducible character,
`exists_natDegree_characterDegree_dvd_card`).  `d > 1` is Peterfalvi (4.4): if `μ_{0 j₀}` had degree
`1` it would be linear, hence `K`-trivial, hence a column-`0` character — contradicting `χ₂ ≠ 1`
(`columnFamily_mu_ne`); this mirrors the crux of `exists_zeta_in_inducedFamily_degree_w1`.  `δ` is the
column sign; and the congruence `μ_{0 j₀}(1) ≡ δ (mod w₁)` (Peterfalvi (4.3.d),
`certainType_degree_modEq`) gives `n` with `n·w₁ = d − δ`.  The degree independence
`μ_{ij}(1) = d` for all `i` and all nontrivial `j` is the materialized (10.3) constancy
`muGrid_apply_one_eq`. -/
theorem Hypothesis.exists_charParamArith [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    ∃ (d : ℕ) (delta : ℤ) (n : ℕ), 1 < d ∧ (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - delta ∧
      (∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → hyp.muGrid hG hodd i j 1 = (d : ℂ)) ∧
      (∀ (j : Fin hyp.w2), j ≠ 0 → hyp.muColumnSign hG hodd j = delta) := by
  haveI := hyp.finiteG
  classical
  have hw2 := hyp.w2_prime hG
  have hw2ge : 2 ≤ hyp.w2 := hw2.two_le
  -- a nontrivial column index `j₀`
  let j₀ : Fin hyp.w2 := ⟨1, by omega⟩
  have hj₀ : j₀ ≠ 0 := Fin.ne_of_val_ne (by simp [j₀])
  -- Reconstruct the §6 host and instances exactly as in `Hypothesis.muGrid`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j₀)
  let k₀ : Fin (Nat.card h.W1) := finCongr hcardW1.symm 0
  -- `χ₂` is a nontrivial dual (the column-`0` dual is the trivial one).
  have hχ₂ne : χ₂ ≠ 1 := by
    intro heq
    rw [← finCardEquivCharacterGroup_zero (h.W2.subgroupOf (h.W1 ⊔ h.W2))] at heq
    have hk0 : finCongr hcardW2sub.symm j₀ = 0 := (finCardEquivCharacterGroup _).injective heq
    have : (j₀ : ℕ) = 0 := by simpa using congrArg Fin.val hk0
    exact hj₀ (Fin.ext this)
  -- `muGrid 0 j₀ = (h.columnFamily χ₂).mu k₀` definitionally.
  have hmg : hyp.muGrid hG hodd 0 j₀ = ((h.columnFamily χ₂).mu k₀ : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid
    rfl
  -- `h.K = commutator ↥M` (so (4.4) applies).
  have hKeq : h.K = (derivedInG M).subgroupOf M := rfl
  have hKcomm : h.K = commutator ↥M := by
    rw [hKeq, derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  -- `d := μ_{0 j₀}(1) ∈ ℕ`.
  obtain ⟨d, hd0, hdeg, -⟩ :=
    OddOrder.Peterfalvi.S03.exists_natDegree_characterDegree_dvd_card
      ((h.columnFamily χ₂).mu k₀)
  rw [OddOrder.Peterfalvi.S03.characterDegree_def] at hdeg
  -- `d > 1` by (4.4): a nontrivial column is not linear (mirrors the `exists_zeta` crux).
  have hne1 : ((h.columnFamily χ₂).mu k₀ : ClassFunction ↥M ℂ) 1 ≠ 1 := by
    intro hmu1
    have hker : (h.K : Set ↥M) ⊆ OddOrder.Peterfalvi.S03.characterKernel
        ((h.columnFamily χ₂).mu k₀ : ClassFunction ↥M ℂ) := by
      intro x hx
      have hx1 := ((h.columnFamily χ₂).mu k₀).isIrreducible
        |>.apply_eq_one_of_mem_commutator_of_apply_one_eq_one hmu1 (hKcomm ▸ hx)
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel, hx1,
        OddOrder.Peterfalvi.S03.characterDegree_def, hmu1]
    obtain ⟨i, hi⟩ := h.exists_certainType_zero_column_eq_of_subset_characterKernel _ hker
    exact h.columnFamily_mu_ne hχ₂ne k₀ i hi.symm
  have hd1 : 1 < d := by
    rw [hdeg] at hne1
    have : d ≠ 1 := fun hd => hne1 (by rw [hd]; norm_num)
    omega
  -- (4.3.d): `μ_{0 j₀}(1) = δ + w₁·a`.
  obtain ⟨a, ha⟩ := h.certainType_degree_modEq χ₂ k₀
  have hcardW1c : (Nat.card ↥h.W1 : ℂ) = (hyp.w1 : ℂ) := by exact_mod_cast hcardW1
  have hcombine : (d : ℂ) = ((h.columnFamily χ₂).sign : ℂ) + (hyp.w1 : ℂ) * (a : ℂ) := by
    rw [← hdeg, ha, hcardW1c]
  have hZ : (d : ℤ) = (h.columnFamily χ₂).sign + (hyp.w1 : ℤ) * a := by exact_mod_cast hcombine
  -- `a ≥ 0` (so `n := a.toNat` realizes `n·w₁ = d − δ`).
  have hw1posN : 0 < hyp.w1 := Nat.pos_of_ne_zero (NeZero.ne hyp.w1)
  have hw1pos : (0 : ℤ) < (hyp.w1 : ℤ) := by exact_mod_cast hw1posN
  have hdsign : (0 : ℤ) < (d : ℤ) - (h.columnFamily χ₂).sign := by
    rcases (h.columnFamily χ₂).sign_eq with hs | hs <;> rw [hs] <;> omega
  have hapos : 0 ≤ a := by
    by_contra hlt
    push_neg at hlt
    have hwa : (hyp.w1 : ℤ) * a < 0 := mul_neg_of_pos_of_neg hw1pos hlt
    linarith [hZ, hdsign, hwa]
  -- degree independence (the materialized (10.3) constancy).
  have hdi : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
      hyp.muGrid hG hodd i j 1 = (d : ℂ) := by
    intro i j hj
    rw [hyp.muGrid_apply_one_eq hG hodd hw2 i 0 hj hj₀, hmg]
    exact hdeg
  refine ⟨d, (h.columnFamily χ₂).sign, a.toNat, hd1, ?_, hdi, ?_⟩
  · rw [Int.toNat_of_nonneg hapos, mul_comm]
    linarith [hZ]
  · -- `δ_k = δ_{j₀} = δ` for every nontrivial column `k` (the (10.3) sign-independence).
    intro k hk
    refine (hyp.muColumnSign_eq_of_ne hG hodd hw2 hk hj₀).trans ?_
    unfold Hypothesis.muColumnSign
    rfl

open scoped FiniteInduce in
/-- **Peterfalvi (10.2)+(10.3), the character parameters of (10.4)**: assemble a genuine
`CharacterParameters` for the §10 Hypothesis from the materialized §6 data.

`ζ` is the degree-`w₁` irreducible of (10.2) (`exists_zeta_in_inducedFamily_degree_w1`), the `μ`- and
`ω^σ`-grids are `muGrid`/`omegaSigmaGrid`, `w₂` is prime by the non-circular (10.3) first clause
(`Hypothesis.w2_prime`), and the degree data `d > 1`, `n·w₁ = d − δ`, `μ_{ij}(1) = d` come from
`exists_charParamArith`.  The `δ_j`-independence `δ_j = δ_{j'}` (10.3) is the genuine
`muColumnSign_eq_of_ne`.  Only the `τ₁`-level `Prop` placeholders remain trivial, pending the
(10.5)/(10.6) Dade calculations. -/
theorem Hypothesis.exists_charParameters [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ params : CharacterParameters hyp,
      (params.zeta ∈ hyp.Sset ∧ IsIrreducibleCharacter params.zeta ∧
          params.zeta 1 = ((hyp.w1 : ℕ) : ℂ)) ∧
        (1 < params.d ∧
          (∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → params.mu i j 1 = (params.d : ℂ)) ∧
          (∀ (j j' : Fin hyp.w2), j ≠ 0 → j' ≠ 0 →
              hyp.muColumnSign hG hG.odd j = hyp.muColumnSign hG hG.odd j') ∧
          ((params.n : ℤ) * (hyp.w1 : ℤ) = (params.d : ℤ) - params.delta)) := by
  haveI := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  obtain ⟨ζ, hζS, hζirr, hζdeg⟩ := exists_zeta_in_inducedFamily_degree_w1 hyp.typeP hodd
    (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)
  obtain ⟨d, delta, n, hd1, hnf, hdi, hδindep⟩ := hyp.exists_charParamArith hG hodd
  exact ⟨{ zeta := ζ
           zeta_mem_S := hζS
           zeta_irreducible := hζirr
           d := d
           delta := delta
           n := n
           w2_prime := hyp.w2_prime hG
           d_gt_one := hd1
           mu := hyp.muGrid hG hodd
           omegaSigma := hyp.omegaSigmaGrid hG hodd
           degree_independent := hdi
           n_formula := hnf
           alpha_support := fun i j hj =>
             hyp.muGrid_alpha_support hG hodd hj hζS (hdi i j hj)
               (hyp.muGrid_zero_column_apply_one hG hodd i) hζdeg hnf (hδindep j hj)
           zeta_tau1_norm_bound := True
           orthogonality_w1_lt_w2 := True
           typeV_parameter_formula := True
           typeV_coherence_formula := True },
    ⟨hζS, hζirr, hζdeg⟩, hd1, hdi,
    (fun _ _ hj hj' => hyp.muColumnSign_eq_of_ne hG hG.odd (hyp.w2_prime hG) hj hj'), hnf⟩

/-- **Peterfalvi (10.2)**: the family `S` contains an irreducible character
`zeta` of degree `w_1`. -/
theorem exists_zeta_degree_w1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ params : CharacterParameters hyp,
      params.zeta ∈ hyp.Sset ∧ IsIrreducibleCharacter params.zeta ∧
        params.zeta 1 = ((hyp.w1 : ℕ) : ℂ) := by
  obtain ⟨params, h1, -⟩ := hyp.exists_charParameters hG
  exact ⟨params, h1⟩

/-- **Peterfalvi (10.3)**: `w_2` is prime and the parameters `d`, `delta`, and
`n = (d - delta) / w_1` are well-defined and independent of the indices. -/
theorem w2_prime_and_parameter_independence [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ params : CharacterParameters hyp,
      hyp.w2.Prime ∧ 1 < params.d ∧
        (∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → params.mu i j 1 = (params.d : ℂ)) ∧
        (∀ (j j' : Fin hyp.w2), j ≠ 0 → j' ≠ 0 →
            hyp.muColumnSign hG hG.odd j = hyp.muColumnSign hG hG.odd j') ∧
        ((params.n : ℤ) * (hyp.w1 : ℤ) = (params.d : ℤ) - params.delta) := by
  obtain ⟨params, -, h2⟩ := hyp.exists_charParameters hG
  exact ⟨params, hyp.w2_prime hG, h2⟩

/-! ## (10.5)--(10.6): Dade-isometry calculations -/

/-- **Peterfalvi (10.5), support half**: for `0 < j < w₂`, the virtual character `α_{ij}` is
supported on `A_0(M)`.  This is now a genuine (dade0-free) theorem, carried by the
`CharacterParameters` field `alpha_support` and discharged in the producer from
`Hypothesis.muGrid_alpha_support`. -/
theorem alpha_support [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} (params : CharacterParameters hyp) :
    ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → (params.alpha i j).support ⊆ hyp.A0 :=
  params.alpha_support

open scoped FiniteInduce in
/-- **§10 Dade value on `V`** (Peterfalvi's "by definition of `τ`").  For a class function `φ` on
`M` supported on `A_0(M)`, the Dade image `φ^τ = hyp.tau φ` *restores* `φ`'s value at any
`v ∈ V = typePV M`: `(φ^τ)(v) = φ(v)`.

Since `V = typePV ⊆ conjClassSet (typePV) ⊆ A_0(M)` (`subset_conjClassSet`), this is exactly the
value-on-support property `dadeIntegralCharacterMap_apply_mem` of the genuine §10 Dade isometry
`hyp.tau`.  It is the reusable "agrees/vanishes on `V` by definition of `τ`" step underlying the
Dade-image half of (10.5) (`α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ)` vanishes on `V`), and the (10.6.b) /
(10.9) value computations. -/
theorem Hypothesis.tau_apply_of_mem_typePV [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {φ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0)
    {v : G} (hv : v ∈ typePV M hyp.typeP) (hvM : v ∈ M) :
    hyp.tau φ v = φ ⟨v, hvM⟩ := by
  haveI := hyp.finiteG
  have hvA0 : v ∈ typePA0 M hyp.typeP := by
    rw [typePA0]
    exact Set.mem_union_right _ (OddOrder.GroupTheory.subset_conjClassSet hv)
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_mem hyp.dadeData.dade
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) hφ hvA0

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), the Dade-image value on `V`** (the "vanishes on `V`" leg of the Dade-image
half): on the exceptional set `V = typePV`, the Dade image `α_{ij}^τ` of the virtual character
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` equals `δ·(ω_{ij}^σ − ω_{i0}^σ)`, where `ω^σ` is the *aligned*
σ-grid `alignedOmegaSigmaGrid` (the σ-image of the same ω that `μ` is built from).

This is Peterfalvi's step *"By (3.2.c), (4.3.c) and the definition of `τ`, `α_{ij}^τ − δ(ω_{ij}^σ −
ω_{i0}^σ)` vanishes on `V`"*, assembled from:
* the cornerstone `tau_apply_of_mem_typePV` — `α` is supported on `A_0(M)` (the support half,
  `muGrid_alpha_support`), so `τ` restores `α`'s value on `V`;
* the reconciliation `muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV` —
  `μ_{ij}(v) = δ_j·ω_{ij}^σ(v)` on `V`, both at `j` and at column `0`;
* `muColumnSign_zero` — `δ_0 = 1`;
* `ζ` vanishing on `V` — `ζ` is induced from the normal `M' = [M,M]` and `v ∉ M'`
  (`typePData_typePV_not_mem_derived`).

It is the reusable on-`V` identity feeding the `(10.5)`/`(10.6.b)`/`(10.9)` value computations; the
*global* Dade-image identity additionally requires the `a = 0` norm/Cauchy–Schwarz argument and the
(3.8) trichotomy. -/
theorem Hypothesis.tau_muGridAlpha_apply_eq_on_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {i : Fin hyp.w1} {j : Fin hyp.w2} (hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    {v : G} (hv : v ∈ typePV M hyp.typeP) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) v
      = ((δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
          - hyp.alignedOmegaSigmaGrid hG hodd i 0)) v := by
  haveI := hyp.finiteG
  classical
  -- `v ∈ M` (`V ⊆ W ⊆ M`).
  have hvM : v ∈ M := typePData_W_le_self hyp.typeP (SetLike.mem_coe.mp hv.1)
  -- The (10.5) support half, so `τ` restores `α` on `V`.
  have hsupp := hyp.muGrid_alpha_support hG hodd hj hζS hdeg hμ0 hζ1 hnf hδj
  rw [hyp.tau_apply_of_mem_typePV hsupp hv hvM]
  -- `ζ` vanishes on `V`: induced from the normal `M'`, and `v ∉ M'`.
  have hζv : ζ ⟨v, hvM⟩ = 0 := by
    obtain ⟨θ, _hθne, hζeq⟩ := hζS
    have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
    have hnotmem : (⟨v, hvM⟩ : ↥M) ∉ (derivedInG M).subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]
      exact typePData_typePV_not_mem_derived hyp.typeP hv
    rw [hζeq]
    exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hnotmem
  -- Evaluate `α ⟨v⟩` via the reconciliation (`μ = δ_j·ω^σ`), `δ_0 = 1`, and `ζ(v) = 0`.
  rw [ClassFunction.sub_apply, ClassFunction.sub_apply, ClassFunction.smul_apply,
    ClassFunction.smul_apply,
    hyp.muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV hG hodd i j hv hvM,
    hyp.muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV hG hodd i 0 hv hvM,
    hδj, hyp.muColumnSign_zero hG hodd, hζv,
    ClassFunction.smul_apply, ClassFunction.sub_apply]
  push_cast
  ring

open scoped FiniteInduce in
/-- **§10 Dade isometry on the support lattice** (the inner-product half of (10.5)/(10.6)): the
genuine Dade map `τ = hyp.tau` preserves the class-function inner product on functions supported in
`A_0(M)`.  This is the §7 `dadeIntegralCharacterMap_inner_eq_on_supported_span` for the (8.15) Dade
data `hyp.dadeData`, instantiated on the two-element set `{φ, ψ}` whose members are `A_0`-supported.

It is the isometry input to the (10.5) `a = 0` argument: every `(α_{ij}^τ, …)` inner product is
computed on the `M`-side via this transfer, since `α_{ij}` is `A_0`-supported by
`muGrid_alpha_support`. -/
theorem Hypothesis.tau_inner_eq_of_supported [Finite G] {M : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M)
    {φ ψ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0) (hψ : ψ.support ⊆ hyp.A0) :
    ClassFunction.inner (hyp.tau φ) (hyp.tau ψ) = ClassFunction.inner φ ψ := by
  haveI := hyp.finiteG
  classical
  have hS : ∀ s ∈ ({φ, ψ} : Set (ClassFunction ↥M ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact hφ
    · exact hψ
  have hφ' : φ ∈ OddOrder.Peterfalvi.S07.zSpan ({φ, ψ} : Set (ClassFunction ↥M ℂ)) :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hψ' : ψ ∈ OddOrder.Peterfalvi.S07.zSpan ({φ, ψ} : Set (ClassFunction ↥M ℂ)) :=
    Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hyp.hconj hS hφ' hψ'

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖α_{ij}^τ‖² = 2 + n²`**: the Dade image `α_{ij}^τ` has the same norm as
`α_{ij}`.  The genuine Dade map `τ` is an isometry on `A_0`-supported functions
(`tau_inner_eq_of_supported`), and `α_{ij}` is `A_0`-supported (`muGrid_alpha_support`), so
`‖α_{ij}^τ‖² = ‖α_{ij}‖² = 2 + n²` (`muGridAlpha_inner_self`).  This is the `‖α_{ij}^τ‖²` factor of
the (10.5) Cauchy–Schwarz bound `d²a² ≤ ‖α_{ij}^τ‖²‖μ_k^{τ₁}‖² = (2 + n²)w₁`. -/
theorem Hypothesis.muGridAlpha_tau_inner_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      = 2 + (n : ℂ) ^ 2 := by
  haveI := hyp.finiteG
  classical
  have hsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  rw [hyp.tau_inner_eq_of_supported hsupp hsupp]
  exact hyp.muGridAlpha_inner_self hG hodd i hj0 hζirr hdζ h0ζ hδpm

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}, ζ − ζ̄) = −n`** (M-side): the inner product of
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` against `ζ − ζ̄`.  The certain-type characters `μ_{ij}`, `μ_{i0}`
are degree-distinct from `ζ` and its conjugate `ζ̄` (both of degree `w₁ = ζ(1)`), so they are
orthogonal to both (`muGrid_inner_eq_zero_of_apply_one_ne`); `ζ ≠ ζ̄` (no real characters) gives
`(ζ, ζ̄) = 0`, while `(ζ, ζ) = 1`.  The only surviving term is `−n·(ζ, ζ) = −n`.

This is the `M`-side of the `(α_{ij}^τ, (ζ−ζ̄)^τ) = (α_{ij}, ζ−ζ̄) = −n` step of the (10.5)
`a = 0` argument (`ζ − ζ̄` is `A_0`-supported, so the Dade isometry transfers it). -/
theorem Hypothesis.muGridAlpha_inner_zeta_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζne : ζ.conj ≠ ζ)
    {δ : ℤ} {n : ℕ}
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (ζ - ζ.conj) = -(n : ℂ) := by
  haveI := hyp.finiteG
  classical
  have hconjirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  -- `ζ̄(1) = ζ(1)`: the degree is a real natural number, fixed by `star`.
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  have hμijζ : ClassFunction.inner (hyp.muGrid hG hodd i j) ζ = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hζirr hdζ
  have hμi0ζ : ClassFunction.inner (hyp.muGrid hG hodd i 0) ζ = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr h0ζ
  have hμijζc : ClassFunction.inner (hyp.muGrid hG hodd i j) ζ.conj = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hconjirr (by rw [hconj1]; exact hdζ)
  have hμi0ζc : ClassFunction.inner (hyp.muGrid hG hodd i 0) ζ.conj = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hconjirr (by rw [hconj1]; exact h0ζ)
  have hζζ : ClassFunction.inner ζ ζ = 1 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]
  have hζζc : ClassFunction.inner ζ ζ.conj = 0 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hconjirr, if_neg (Ne.symm hζne)]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, hμijζ, hμi0ζ, hμijζc, hμi0ζc, hζζ, hζζc,
    star_intCast, star_natCast, mul_zero, zero_mul, sub_zero, zero_sub, mul_one]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}, μ_k − dζ̄) = 0`** (M-side, `0 < k < w₂`, `k ≠ j`): the inner
product of `α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` against `μ_k − dζ̄`, where `μ_k = ∑_{0≤i'<w₁} μ_{i'k}`
is the `W₂`-column-`k` sum.  Since `k ≠ j` and `k ≠ 0`, every `μ_{i'k}` is cross-column-orthogonal
to `μ_{ij}` and `μ_{i0}` (`muGrid_inner_cross_column`), and degree-distinct from `ζ`
(`hkζ`), so `(α_{ij}, μ_k) = 0`; and `(α_{ij}, ζ̄) = 0` (degree distinctness + `(ζ, ζ̄) = 0`), so
`(α_{ij}, dζ̄) = 0`.  Hence `(α_{ij}, μ_k − dζ̄) = 0`.

This is the `M`-side of the `(α_{ij}^τ, μ_k^{τ₁} − dζ̄^{τ₁}) = (α_{ij}, μ_k − dζ̄) = 0` step of
the (10.5) `a = 0` argument (whence `(α_{ij}^τ, μ_k^{τ₁}) = da`). -/
theorem Hypothesis.muGridAlpha_inner_muColumn_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j k : Fin hyp.w2)
    (hjk : j ≠ k) (hk0 : k ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζne : ζ.conj ≠ ζ)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    {δ : ℤ} {n d : ℕ} :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k) - (d : ℂ) • ζ.conj) = 0 := by
  haveI := hyp.finiteG
  classical
  have hconjirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  -- `(α_{ij}, ζ̄) = 0`: `μ_{ij}, μ_{i0}` degree-distinct from `ζ̄`, and `(ζ, ζ̄) = 0`.
  have hαζc : ClassFunction.inner
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ζ.conj = 0 := by
    have a1 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hconjirr (by rw [hconj1]; exact hdζ)
    have a2 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hconjirr (by rw [hconj1]; exact h0ζ)
    have a3 : ClassFunction.inner ζ ζ.conj = 0 := by
      rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hconjirr, if_neg (Ne.symm hζne)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, a1, a2, a3,
      mul_zero, sub_zero]
  -- `(α_{ij}, μ_{i'k}) = 0` for each `i'`: cross-column (`k ≠ j`, `k ≠ 0`) + degree (`k`-column ≠ ζ).
  have hrow : ∀ i' : Fin hyp.w1,
      ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (hyp.muGrid hG hodd i' k) = 0 := by
    intro i'
    have h1 := hyp.muGrid_inner_cross_column hG hodd i i' hjk
    have h2 := hyp.muGrid_inner_cross_column hG hodd i i' (Ne.symm hk0)
    have h3 : ClassFunction.inner ζ (hyp.muGrid hG hodd i' k) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i' k) ζ,
        hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i' k hζirr (hkζ i'), star_zero]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, h1, h2, h3,
      mul_zero, sub_zero]
  rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_sum_right,
    Finset.sum_eq_zero (fun i' _ => hrow i'),
    OddOrder.RepresentationTheory.inner_smul_right, hαζc, mul_zero, sub_zero]

open scoped FiniteInduce in
/-- **§10 support of `ζ − ζ̄`** (Peterfalvi (10.5), `a = 0` argument): the difference `ζ − ζ̄` of a
degree-`w₁` irreducible `ζ ∈ S` and its conjugate is supported in `A_0(M)`.  Both `ζ` and `ζ̄` are
induced from the normal `M' = [M,M]`, hence vanish off `M'`; and `(ζ − ζ̄)(1) = ζ(1) − ζ̄(1) = 0`
(equal degrees), so the support lies in `M'^# = M' − {1}`.  Every element of `M'^#` centralizes
itself, hence lies in `A(M) ⊆ A_0(M)` (the left disjunct of `typePA0`, as in `muGrid_alpha_support`).

This makes `ζ − ζ̄` `A_0`-supported, so the Dade isometry `τ` transfers it
(`tau_inner_eq_of_supported`) in the `(α_{ij}^τ, (ζ−ζ̄)^τ) = (α_{ij}, ζ−ζ̄)` step. -/
theorem Hypothesis.zeta_sub_conj_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ) :
    (ζ - ζ.conj).support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  -- `ζ̄(1) = ζ(1)`: the degree is a real natural number.
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `z ∈ M'`: else `ζ z = ζ̄ z = 0`.
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hζvanish hzK, star_zero, sub_zero]
  -- `z ≠ 1`: `(ζ − ζ̄)(1) = 0`.
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, hconj1, sub_self]
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  show (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
    ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}^τ, (ζ−ζ̄)^τ) = −n`**: the Dade-image inner product, transferred to
the `M`-side.  Both `α_{ij}` (`muGrid_alpha_support`) and `ζ − ζ̄` (`zeta_sub_conj_support`) are
`A_0`-supported, so the Dade isometry `τ` preserves their inner product
(`tau_inner_eq_of_supported`), and the `M`-side value is `−n`
(`muGridAlpha_inner_zeta_sub_conj`).  This is the `(α_{ij}^τ, (ζ−ζ̄)^τ) = (α_{ij}, ζ−ζ̄) = −n` step
of the (10.5) `a = 0` argument. -/
theorem Hypothesis.muGridAlpha_tau_inner_zeta_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau (ζ - ζ.conj)) = -(n : ℂ) := by
  haveI := hyp.finiteG
  classical
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hζsupp := hyp.zeta_sub_conj_support hG hodd hζS hζirr
  rw [hyp.tau_inner_eq_of_supported hαsupp hζsupp]
  exact hyp.muGridAlpha_inner_zeta_sub_conj hG hodd i j hζirr hζne hdζ h0ζ

open scoped FiniteInduce in
/-- **§10 support of `μ_k − dζ̄`** (Peterfalvi (10.5), `a = 0` argument): the column sum
`μ_k = ∑_{i} μ_{ik}` (an induced character of degree `dw₁`) minus `d` times the conjugate `ζ̄` (also
degree `w₁`) is supported in `A_0(M)`.  Both `μ_k` and `ζ̄` are induced from the normal `M'`, hence
vanish off `M'` (`muGrid_column_sum_vanishes_off_derived`, induced-from-`M'` for `ζ̄`); and the
degrees cancel, `(μ_k − dζ̄)(1) = dw₁ − dw₁ = 0`, so the support lies in `M'^# ⊆ A(M) ⊆ A_0(M)`.

This is the companion of `zeta_sub_conj_support`: it makes `μ_k − dζ̄` `A_0`-supported, so the Dade
isometry `τ` transfers `(α_{ij}, μ_k − dζ̄) = (α_{ij}^τ, (μ_k − dζ̄)^τ)` with no adjunction. -/
theorem Hypothesis.muColumn_sub_conj_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (k : Fin hyp.w2)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    {d : ℕ} (hcol1 : ∀ i, hyp.muGrid hG hodd i k 1 = (d : ℂ)) (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • ζ.conj).support ⊆ hyp.A0 := by
  haveI := hyp.finiteG
  classical
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  -- evaluation of a finite sum of class functions at a point is the sum of values.
  have hsumapply : ∀ (w : ↥M), (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) w
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k w := by
    intro w
    refine Finset.univ.induction_on (motive := fun s =>
      (∑ i ∈ s, hyp.muGrid hG hodd i k) w = ∑ i ∈ s, hyp.muGrid hG hodd i k w) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `z ∈ M'`: else `μ_k z = ζ̄ z = 0`.
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.conj_apply,
      hyp.muGrid_column_sum_vanishes_off_derived hG hodd k hzK, hζvanish hzK, star_zero,
      mul_zero, sub_zero]
  -- `z ≠ 1`: `(μ_k − dζ̄)(1) = dw₁ − dw₁ = 0`.
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.conj_apply, hζ1,
      hsumapply 1, Finset.sum_congr rfl (fun i _ => hcol1 i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, star_natCast]
    ring
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  show (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
    ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}^τ, (μ_k − dζ̄)^τ) = 0`** (`0 < k < w₂`, `k ≠ j`): the Dade-image
inner product, transferred to the `M`-side.  Both `α_{ij}` (`muGrid_alpha_support`) and `μ_k − dζ̄`
(`muColumn_sub_conj_support`) are `A_0`-supported, so the Dade isometry `τ` preserves their inner
product (`tau_inner_eq_of_supported`), and the `M`-side value is `0`
(`muGridAlpha_inner_muColumn_sub_conj`).

Since `μ_k`, `ζ̄ ∈ ℤ[S]`, on the coherent side `(μ_k − dζ̄)^τ = (μ_k − dζ̄)^{τ₁} = μ_k^{τ₁} − dζ̄^{τ₁}`
(the coherent extension agrees with `τ` on this `A_0`-supported lattice element), so this is the
`(α_{ij}^τ, μ_k^{τ₁} − dζ̄^{τ₁}) = 0` step of the (10.5) `a = 0` argument, whence
`(α_{ij}^τ, μ_k^{τ₁}) = da`.  No Dade–coherence adjunction is needed: the combination `μ_k − dζ̄`,
not `μ_k` alone, is supported. -/
theorem Hypothesis.muGridAlpha_tau_inner_muColumn_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ)) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k) - (d : ℂ) • ζ.conj)) = 0 := by
  haveI := hyp.finiteG
  classical
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hμsupp := hyp.muColumn_sub_conj_support hG hodd k hζS hζirr hcol1 hζ1
  rw [hyp.tau_inner_eq_of_supported hαsupp hμsupp]
  exact hyp.muGridAlpha_inner_muColumn_sub_conj hG hodd i j k hjk hk0 hζirr hζne hkζ hdζ h0ζ

/-- **§10 τ/τ₁ compatibility on `ζ − ζ̄`** (Peterfalvi (10.5), `a = 0` argument): the Dade image
`(ζ − ζ̄)^τ` equals `ζ^{τ₁} − ζ̄^{τ₁}` for the coherent extension `τ₁`.  Since `ζ ∈ S` and
`ζ̄ ∈ S` (`inducedFamily_closedUnderConjugate`), the difference `ζ − ζ̄` lies in the supported
lattice `ℤ[S, A_0]` (`zeta_sub_conj_support`), where `τ₁` agrees with `τ`
(`coherent.extends_on_supported`); linearity of `τ₁` (`map_sub`) then splits the image.

This converts the pure-`τ` identity `(α_{ij}^τ, (ζ−ζ̄)^τ) = −n`
(`muGridAlpha_tau_inner_zeta_sub_conj`) into the `τ₁` form, giving `(α_{ij}^τ, ζ̄^{τ₁}) = a`
(with `a − n := (α_{ij}^τ, ζ^{τ₁})`) in the (10.5) `a = 0` argument. -/
theorem Hypothesis.tau_zeta_sub_conj_eq_tau1 [Finite G] [Fintype G] {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ) :
    hyp.tau (ζ - ζ.conj) = coh.tau1 ζ - coh.tau1 ζ.conj := by
  have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζS
  have hspanζc : ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.subset_span (inducedFamily_closedUnderConjugate M hζS)
  have hmem : (ζ - ζ.conj) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Sset hyp.A0 :=
    ⟨Submodule.sub_mem _ hspanζ hspanζc, hyp.zeta_sub_conj_support hG hodd hζS hζirr⟩
  rw [← coh.coherent.extends_on_supported _ hmem, map_sub]
  rfl

open scoped FiniteInduce in
/-- **§10 τ/τ₁ compatibility on `μ_k − dζ̄`** (Peterfalvi (10.5), `a = 0` argument): the Dade image
`(μ_k − dζ̄)^τ` equals `μ_k^{τ₁} − dζ̄^{τ₁}` for the coherent extension `τ₁`.  Since
`μ_k = ∑_i μ_{ik} ∈ S` (`muGrid_column_sum_mem_inducedFamily`) and `ζ̄ ∈ S`
(`inducedFamily_closedUnderConjugate`), the combination `μ_k − dζ̄` lies in the supported lattice
`ℤ[S, A_0]` (`muColumn_sub_conj_support`), where `τ₁` agrees with `τ`
(`coherent.extends_on_supported`); `τ₁`-linearity (`map_sub`, `map_nsmul`) then splits the image.

This converts `(α_{ij}^τ, (μ_k − dζ̄)^τ) = 0` (`muGridAlpha_tau_inner_muColumn_sub_conj`) into the
`τ₁` form, giving `(α_{ij}^τ, μ_k^{τ₁}) = da` in the (10.5) `a = 0` argument. -/
theorem Hypothesis.tau_muColumn_sub_conj_eq_tau1 [Finite G] [Fintype G] {M : Subgroup G}
    [Fintype ↥M] [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (k : Fin hyp.w2) {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    {d : ℕ} (hcol1 : ∀ i, hyp.muGrid hG hodd i k 1 = (d : ℂ)) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • ζ.conj)
      = coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • coh.tau1 ζ.conj := by
  have hμkS := hyp.muGrid_column_sum_mem_inducedFamily hG hodd k hdk1
  have hspanμ : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hμkS
  have hspanζc : ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.subset_span (inducedFamily_closedUnderConjugate M hζS)
  have hsmulmem : (d : ℂ) • ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hspanζc d
  have hmem : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • ζ.conj)
      ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Sset hyp.A0 :=
    ⟨Submodule.sub_mem _ hspanμ hsmulmem,
      hyp.muColumn_sub_conj_support hG hodd k hζS hζirr hcol1 hζ1⟩
  rw [← coh.coherent.extends_on_supported _ hmem, map_sub]
  congr 1
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, Nat.cast_smul_eq_nsmul]
  rfl

/-- **The (10.5) `a = 0` numeric core.**  If `a ∈ ℤ` satisfies the Cauchy–Schwarz bound
`(d·a)² ≤ (2+n²)w₁` with `d = nw₁ + δ`, `δ = ±1`, `w₁ ≥ 3` (odd, since `|G|` is odd) and `n ≥ 2`
(even and positive), then `a = 0`.  Else `a² ≥ 1` gives `d² ≤ (2+n²)w₁`, but `d² = (nw₁+δ)² >
(2+n²)w₁` for `w₁ ≥ 3, n ≥ 2` — a contradiction (Peterfalvi: "`n < 2`, contradicting `n` even,
`n > 0`"). -/
private theorem cauchySchwarz_numeric {d n w₁ : ℕ} {δ a : ℤ}
    (hd : (d : ℤ) = (n : ℤ) * (w₁ : ℤ) + δ) (hδ : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ w₁) (hn2 : 2 ≤ n)
    (hbound : ((d : ℝ) * (a : ℝ)) ^ 2 ≤ (2 + (n : ℝ) ^ 2) * (w₁ : ℝ)) : a = 0 := by
  by_contra ha
  have ha1 : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ a ^ 2 := by
      rcases lt_or_gt_of_ne ha with h | h <;> nlinarith [sq_nonneg a]
    exact_mod_cast this
  have hdpos : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  have hd2 : ((d : ℝ)) ^ 2 ≤ (2 + (n : ℝ) ^ 2) * (w₁ : ℝ) := by nlinarith [hbound, ha1, hdpos]
  have hdR : (d : ℝ) = (n : ℝ) * (w₁ : ℝ) + (δ : ℝ) := by exact_mod_cast hd
  have hw1R : (3 : ℝ) ≤ (w₁ : ℝ) := by exact_mod_cast hw1
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hδR : (δ : ℝ) = 1 ∨ (δ : ℝ) = -1 := by rcases hδ with h | h <;> [left; right] <;> exact_mod_cast h
  rw [hdR] at hd2
  rcases hδR with hδ1 | hδ1 <;> rw [hδ1] at hd2 <;>
    nlinarith [hd2, hw1R, hn2R, mul_nonneg (by linarith : (0:ℝ) ≤ (w₁:ℝ) - 3) (by linarith : (0:ℝ) ≤ (n:ℝ) - 2),
      mul_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ) - 2) (by linarith : (0:ℝ) ≤ (n:ℝ) - 2),
      mul_nonneg (by linarith : (0:ℝ) ≤ (w₁:ℝ) - 3) (by linarith : (0:ℝ) ≤ (w₁:ℝ) - 3)]

/-- **Cauchy–Schwarz for the class-function inner product** (real-part form): for class functions
`φ, ψ` of any finite group `H`, `⟨φ, ψ⟩.re² ≤ ⟨φ, φ⟩.re · ⟨ψ, ψ⟩.re`.

Proof by the discriminant: the real quadratic `t ↦ ⟨φ − tψ, φ − tψ⟩.re = ⟨ψ,ψ⟩.re·t² −
2⟨φ,ψ⟩.re·t + ⟨φ,φ⟩.re` is `≥ 0` for every real `t` (positive semidefiniteness,
`inner_self_re_nonneg`), so its discriminant is `≤ 0` (`discrim_le_zero`).  This is the
`(α_{ij}^τ, μ_k^{τ₁})² ≤ ‖α_{ij}^τ‖²·‖μ_k^{τ₁}‖²` of the (10.5) `a = 0` argument. -/
private theorem classFunction_inner_re_sq_le {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (φ ψ : ClassFunction H ℂ) :
    (ClassFunction.inner φ ψ).re ^ 2
      ≤ (ClassFunction.inner φ φ).re * (ClassFunction.inner ψ ψ).re := by
  have hquad : ∀ t : ℝ, 0 ≤ (ClassFunction.inner ψ ψ).re * (t * t)
      + (-2 * (ClassFunction.inner φ ψ).re) * t + (ClassFunction.inner φ φ).re := by
    intro t
    have key : ClassFunction.inner (φ - (t : ℂ) • ψ) (φ - (t : ℂ) • ψ)
        = ClassFunction.inner φ φ - (t : ℂ) * ClassFunction.inner φ ψ
          - (t : ℂ) * ClassFunction.inner ψ φ + (t : ℂ) * (t : ℂ) * ClassFunction.inner ψ ψ := by
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
        Complex.star_def, Complex.conj_ofReal]
      ring
    have hre : (ClassFunction.inner (φ - (t : ℂ) • ψ) (φ - (t : ℂ) • ψ)).re
        = (ClassFunction.inner ψ ψ).re * (t * t)
          + (-2 * (ClassFunction.inner φ ψ).re) * t + (ClassFunction.inner φ φ).re := by
      rw [key, OddOrder.RepresentationTheory.inner_conj_symm φ ψ]
      simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
        zero_mul, mul_zero, sub_zero, add_zero]
      ring
    rw [← hre]
    exact inner_self_re_nonneg _
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith [hd]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}^τ, μ_k^{τ₁}) = da`** (`0 < k < w₂`, `k ≠ j`): the key inner
product of the (10.5) `a = 0` argument, where `a := (α_{ij}^τ, ζ^{τ₁}) + n`.

From the two pure-`τ` Dade-image identities and their `τ₁` forms:
* `(α_{ij}^τ, (ζ−ζ̄)^τ) = −n` (`muGridAlpha_tau_inner_zeta_sub_conj`) with `(ζ−ζ̄)^τ = ζ^{τ₁}−ζ̄^{τ₁}`
  (`tau_zeta_sub_conj_eq_tau1`) gives `(α_{ij}^τ, ζ̄^{τ₁}) = (α_{ij}^τ, ζ^{τ₁}) + n = a`;
* `(α_{ij}^τ, (μ_k−dζ̄)^τ) = 0` (`muGridAlpha_tau_inner_muColumn_sub_conj`) with
  `(μ_k−dζ̄)^τ = μ_k^{τ₁}−dζ̄^{τ₁}` (`tau_muColumn_sub_conj_eq_tau1`) gives
  `(α_{ij}^τ, μ_k^{τ₁}) = d·(α_{ij}^τ, ζ̄^{τ₁}) = d·a`.

This `d·a` is the `(α_{ij}^τ, μ_k^{τ₁})` term of the Cauchy–Schwarz bound
`d²a² ≤ ‖α_{ij}^τ‖²·‖μ_k^{τ₁}‖² = (2+n²)w₁`. -/
theorem Hypothesis.muGridAlpha_tau1_inner_muColumn [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k))
      = (d : ℂ) * (ClassFunction.inner
          (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
          (coh.tau1 ζ) + (n : ℂ)) := by
  -- `(α^τ, ζ̄^{τ₁}) = (α^τ, ζ^{τ₁}) + n` from the `ζ − ζ̄` identity.
  have h12 := hyp.muGridAlpha_tau_inner_zeta_sub_conj hG hodd i hj0 hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ
  rw [hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr,
    ClassFunction.inner_sub_right] at h12
  -- `(α^τ, μ_k^{τ₁}) = d·(α^τ, ζ̄^{τ₁})` from the `μ_k − dζ̄` identity.
  have h45 := hyp.muGridAlpha_tau_inner_muColumn_sub_conj hG hodd i hj0 k hjk hk0 hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1
  rw [hyp.tau_muColumn_sub_conj_eq_tau1 hG hodd k coh hζS hζirr hcol1 hζ1 hdk1,
    ClassFunction.inner_sub_right,
    OddOrder.RepresentationTheory.inner_smul_right, star_natCast] at h45
  linear_combination h45 - (d : ℂ) * h12

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖μ_k^{τ₁}‖² = w₁`** (`0 < k < w₂`): the coherent extension `τ₁` is an
isometry on `ℤ[S]`, and `μ_k = ∑_i μ_{ik} ∈ S` (`muGrid_column_sum_mem_inducedFamily`), so
`‖μ_k^{τ₁}‖² = ‖μ_k‖² = w₁` (`coherent.extension_inner_eq` + `muGrid_column_sum_inner_self`).

This is the `‖μ_k^{τ₁}‖²` factor of the (10.5) Cauchy–Schwarz bound
`d²a² = (α_{ij}^τ, μ_k^{τ₁})² ≤ ‖α_{ij}^τ‖²·‖μ_k^{τ₁}‖² = (2+n²)w₁`. -/
theorem Hypothesis.muColumn_tau1_inner_self [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (k : Fin hyp.w2) {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    ClassFunction.inner (coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k))
        (coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)) = (hyp.w1 : ℂ) := by
  have hμkS := hyp.muGrid_column_sum_mem_inducedFamily hG hodd k hdk1
  have hspan : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hμkS
  show ClassFunction.inner (coh.coherent.extension (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k))
      (coh.coherent.extension (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)) = (hyp.w1 : ℂ)
  rw [coh.coherent.extension_inner_eq _ _ hspan hspan]
  exact hyp.muGrid_column_sum_inner_self hG hodd k

open scoped FiniteInduce in
/-- **§10 `α_{ij}^τ` is a virtual character of `G`** (Peterfalvi (10.5)): `α_{ij} = μ_{ij} − δ·μ_{i0}
− n·ζ` is a virtual character of `M` (`muGrid_isIrreducible`, `ζ` irreducible) and is `A_0`-supported
(`muGrid_alpha_support`), so its Dade image lies in `ℤ[Irr G]`
(`dadeIntegralCharacterMap_mem_ZIrr_of_supported`).  Together with `ζ^{τ₁}, μ_k^{τ₁} ∈ ℤ[Irr G]` this
makes the inner products of the `a = 0` argument integers. -/
theorem Hypothesis.muGridAlpha_tau_mem_ZIrr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2}
    (hj0 : j ≠ 0) {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ∈ ZIrr G := by
  haveI := hyp.finiteG
  have hαZ : (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ∈ ZIrr ↥M := by
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (hyp.muGrid_isIrreducible hG hodd i j).mem_ZIrr ?_) ?_
    · rw [Int.cast_smul_eq_zsmul]
      exact zsmul_mem (hyp.muGrid_isIrreducible hG hodd i 0).mem_ZIrr δ
    · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hζirr.mem_ZIrr n
  have hsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dadeData.dade hyp.hconj hsupp hαZ

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `a = 0`**: the integer `a = (α_{ij}^τ, ζ^{τ₁}) + n` of the (10.5) Cauchy–
Schwarz argument vanishes, i.e. `(α_{ij}^τ, ζ^{τ₁}) = −n`.

`(α_{ij}^τ, ζ^{τ₁}) = m ∈ ℤ` (`α_{ij}^τ, ζ^{τ₁} ∈ ℤ[Irr G]`, `inner_mem_ZIrr_int`); set `a = m + n`.
Then `(α_{ij}^τ, μ_k^{τ₁}) = da` (`muGridAlpha_tau1_inner_muColumn`), and Cauchy–Schwarz
(`classFunction_inner_re_sq_le`) with `‖α_{ij}^τ‖² = 2 + n²` (`muGridAlpha_tau_inner_self`) and
`‖μ_k^{τ₁}‖² = w₁` (`muColumn_tau1_inner_self`) gives `(da)² ≤ (2+n²)w₁`.  By the numeric core
(`cauchySchwarz_numeric`; `d = nw₁+δ`, `δ = ±1`, `w₁ ≥ 3` odd, `n ≥ 2` even) this forces `a = 0`. -/
theorem Hypothesis.muGridAlpha_tau1_zeta_eq_neg_n [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ hyp.w1) (hn2 : 2 ≤ n) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.tau1 ζ) = -(n : ℂ) := by
  haveI := hyp.finiteG
  classical
  -- `(α^τ, ζ^{τ₁}) = m ∈ ℤ`.
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  have hζZ : coh.tau1 ζ ∈ ZIrr G := coh.coherent.extension_mem_ZIrr ζ (Submodule.subset_span hζS)
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hαZ hζZ
  -- `(α^τ, μ_k^{τ₁}) = d·(m + n)` and the two norms.
  have hda := hyp.muGridAlpha_tau1_inner_muColumn hG hodd i hj0 k hjk hk0 coh hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1 hdk1
  rw [hm] at hda
  have hnorm_a := hyp.muGridAlpha_tau_inner_self hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
    hdζ h0ζ hδpm
  have hnorm_mu := hyp.muColumn_tau1_inner_self hG hodd k coh hdk1
  -- Cauchy–Schwarz, with the three inner products substituted.
  have hcs := classFunction_inner_re_sq_le
    (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
    (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k))
  rw [hda, hnorm_a, hnorm_mu] at hcs
  have hre1 : ((d : ℂ) * ((m : ℂ) + (n : ℂ))).re = (d : ℝ) * ((m : ℝ) + (n : ℝ)) := by
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  have hre2 : ((2 : ℂ) + (n : ℂ) ^ 2).re = 2 + (n : ℝ) ^ 2 := by
    simp [Complex.add_re, pow_two, Complex.mul_re, Complex.mul_im]
  rw [hre1, hre2, Complex.natCast_re] at hcs
  -- Apply the numeric core with `a = m + n`.
  have ha0 : m + (n : ℤ) = 0 := by
    refine cauchySchwarz_numeric (d := d) (n := n) (w₁ := hyp.w1) (δ := δ) (a := m + n)
      (by linarith [hnf]) hδpm hw1 hn2 ?_
    push_cast
    convert hcs using 2
  rw [hm]
  have hmn : m = -(n : ℤ) := by omega
  rw [hmn]; push_cast; ring

open scoped FiniteInduce in
/-- **§10 `‖ζ^{τ₁}‖² = 1`** (Peterfalvi (10.5)): the coherent extension `τ₁` is an isometry on
`ℤ[S]` and `ζ ∈ S` is irreducible, so `‖ζ^{τ₁}‖² = ‖ζ‖² = 1`. -/
theorem Hypothesis.zeta_tau1_inner_self [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ) :
    ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ) = 1 := by
  have hspan : ζ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζS
  show ClassFunction.inner (coh.coherent.extension ζ) (coh.coherent.extension ζ) = 1
  rw [coh.coherent.extension_inner_eq _ _ hspan hspan,
    OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖X‖² = 2` and `X ⊥ ζ^{τ₁}`** where `X = α_{ij}^τ + n·ζ^{τ₁}`: with
`(α_{ij}^τ, ζ^{τ₁}) = −n` (`a = 0`, `muGridAlpha_tau1_zeta_eq_neg_n`), `‖α_{ij}^τ‖² = 2 + n²`
(`muGridAlpha_tau_inner_self`) and `‖ζ^{τ₁}‖² = 1` (`zeta_tau1_inner_self`):
`(X, ζ^{τ₁}) = (α_{ij}^τ, ζ^{τ₁}) + n‖ζ^{τ₁}‖² = −n + n = 0`, and
`‖X‖² = ‖α_{ij}^τ‖² + 2n·(α_{ij}^τ, ζ^{τ₁}) + n²‖ζ^{τ₁}‖² = (2+n²) − 2n² + n² = 2`.

So `α_{ij}^τ = X − n·ζ^{τ₁}` with `X` a virtual character of `G` orthogonal to `ζ^{τ₁}` of squared
norm `2` — the decomposition the (10.5) `(v)`/`(vi)` argument (`NC(ψ) ≤ 4`, (3.8)) operates on. -/
theorem Hypothesis.muGridAlpha_tau_X_inner [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ hyp.w1) (hn2 : 2 ≤ n) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ) (coh.tau1 ζ) = 0
    ∧ ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ)
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ) = 2 := by
  have ha0 := hyp.muGridAlpha_tau1_zeta_eq_neg_n hG hodd i hj0 k hjk hk0 coh hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1 hdk1 hδpm hw1 hn2
  have hnorm_a := hyp.muGridAlpha_tau_inner_self hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
    hdζ h0ζ hδpm
  have hzz := hyp.zeta_tau1_inner_self hG hodd coh hζS hζirr
  have ha0' : ClassFunction.inner (coh.tau1 ζ)
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)) = -(n : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, ha0, star_neg, star_natCast]
  constructor
  · simp only [ClassFunction.inner_add_left, ClassFunction.inner_smul_left, ha0, hzz, mul_one]
    ring
  · simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      ha0, ha0', hnorm_a, hzz, star_natCast, mul_one]
    ring

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), (vi) precursor — `ψ` vanishes on `V`**: the virtual character
`ψ = α_{ij}^τ + n·ζ^{τ₁} − δ(ω_{ij}^σ − ω_{i0}^σ)` (this is `X − δ(ω^σ diff)` of the (10.5) endgame,
since `α^τ = X − nζ^{τ₁}`) vanishes on `V`.

Combines the value-on-`V` leg `tau_muGridAlpha_apply_eq_on_typePV` (`α^τ = δ(ω^σ diff)` on `V`, by
(3.2.c)/(4.3.c) and the definition of `τ`) with the vanishing of `ζ^{τ₁}` on `V` (`hζvanish`, the
§5/§7 input of (10.5): "By (5.3.b), (5.5) and (3.2.d), `ζ^{τ₁}` vanishes on `V`").  The remaining
step to `alpha_tau_image` is `NC(ψ) ≤ 4 < 2·inf(w₁,w₂)` + Theorem (3.8)
(`S05.sigmaCoeff_trichotomy`, requiring a `FullDadeApplication` for the type-`P` `TICyclicHypothesis`)
forcing `ψ ⊥ ω^σ`, hence `ψ = 0`. -/
theorem Hypothesis.muGridPsi_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {i : Fin hyp.w1} {j : Fin hyp.w2} (hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hζvanish : ∀ v ∈ typePV M hyp.typeP, coh.tau1 ζ v = 0)
    {v : G} (hv : v ∈ typePV M hyp.typeP) :
    (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        + (n : ℂ) • coh.tau1 ζ
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
            - hyp.alignedOmegaSigmaGrid hG hodd i 0)) v = 0 := by
  have hleg := hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hj hζS hdeg hμ0 hζ1 hnf hδj hv
  simp only [ClassFunction.sub_apply, ClassFunction.add_apply, ClassFunction.smul_apply] at hleg ⊢
  rw [hleg, hζvanish v hv]
  simp

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(ζ − ζ̄)^τ` vanishes on `V`** (the "by definition of `τ`" step underlying
the (5.3.b)/(5.5)/(3.2.d) `ζ^{τ₁}`-vanishing argument).  Since `ζ` is induced from the normal
`M' = [M,M]` and every `v ∈ V = typePV` lies outside `M'` (`typePData_typePV_not_mem_derived`),
both `ζ` and its conjugate `ζ̄` vanish at `v`; the difference `ζ − ζ̄` is `A_0(M)`-supported
(`zeta_sub_conj_support`), so the Dade isometry restores its value at `v`
(`tau_apply_of_mem_typePV`), giving `(ζ − ζ̄)^τ(v) = 0`. -/
theorem Hypothesis.tau_zeta_sub_conj_vanishes_on_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) {v : G} (hv : v ∈ typePV M hyp.typeP) :
    hyp.tau (ζ - ζ.conj) v = 0 := by
  haveI := hyp.finiteG
  classical
  have hvM : v ∈ M := typePData_W_le_self hyp.typeP (SetLike.mem_coe.mp hv.1)
  have hsupp := hyp.zeta_sub_conj_support hG hodd hζS hζirr
  rw [hyp.tau_apply_of_mem_typePV hsupp hv hvM]
  -- `ζ` (induced from the normal `M'`) vanishes at `v ∉ M'`, hence so does `ζ̄ = star ∘ ζ`.
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hnotmem : (⟨v, hvM⟩ : ↥M) ∉ (derivedInG M).subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]
    exact typePData_typePV_not_mem_derived hyp.typeP hv
  have hζv : ζ ⟨v, hvM⟩ = 0 := by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hnotmem
  rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hζv, star_zero, sub_zero]

/-- **Norm-`1` projection orthogonality.**  If `a, s ∈ ℤ[Irr G]` with `‖a‖² = ‖b‖² = ‖s‖² = 1`,
`a ⊥ b`, and the difference `a − b` is orthogonal to `s`, then `a ⊥ s`.

Since `⟨a,s⟩ = ⟨b,s⟩ =: x ∈ ℤ` (`a, s ∈ ℤ[Irr G]`, `inner_mem_ZIrr_int`), the projection norm
`‖s − x·a − x·b‖² = 1 − 2x² ≥ 0` forces `2x² ≤ 1`, hence `x = 0`.  This is the integral-geometry
core that lets the §10 `ζ^{τ₁}`-vanishing argument bypass the (5.4)/(5.5) `R(ζ)` machinery:
applied with `a = ζ^{τ₁}`, `b = ζ̄^{τ₁}`, `s = ω^σ`, the orthogonality of `(ζ − ζ̄)^τ = a − b` to the
`σ`-image (Peterfalvi (5.3.b), via (3.8)) gives `ζ^{τ₁} ⊥ ω^σ` directly. -/
private theorem inner_left_eq_zero_of_inner_sub_eq_zero {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {a b s : ClassFunction G ℂ} (haZ : a ∈ ZIrr G) (hsZ : s ∈ ZIrr G)
    (ha1 : ClassFunction.inner a a = 1) (hb1 : ClassFunction.inner b b = 1)
    (hs1 : ClassFunction.inner s s = 1) (hab : ClassFunction.inner a b = 0)
    (hdiff : ClassFunction.inner (a - b) s = 0) :
    ClassFunction.inner a s = 0 := by
  obtain ⟨x, hx⟩ := ClassFunction.inner_mem_ZIrr_int haZ hsZ
  -- `⟨b,s⟩ = ⟨a,s⟩ = x` from `⟨a − b, s⟩ = 0`.
  have hbs : ClassFunction.inner b s = (x : ℂ) := by
    rw [ClassFunction.inner_sub_left, hx, sub_eq_zero] at hdiff
    exact hdiff.symm
  -- the conjugate-symmetric companions (`x` is real, being an integer).
  have hsa : ClassFunction.inner s a = (x : ℂ) := by
    rw [inner_conj_symm a s, hx, star_intCast]
  have hsb : ClassFunction.inner s b = (x : ℂ) := by
    rw [inner_conj_symm b s, hbs, star_intCast]
  have hba : ClassFunction.inner b a = 0 := by
    rw [inner_conj_symm a b, hab, star_zero]
  -- the projection norm `‖s − x·a − x·b‖² = 1 − 2x²`.
  have key : ClassFunction.inner (s - (x : ℂ) • a - (x : ℂ) • b)
      (s - (x : ℂ) • a - (x : ℂ) • b) = 1 - 2 * (x : ℂ) ^ 2 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      ha1, hb1, hs1, hab, hba, hx, hbs, hsa, hsb, star_intCast]
    ring
  have hnn := inner_self_re_nonneg (s - (x : ℂ) • a - (x : ℂ) • b)
  rw [key] at hnn
  have hcast : (1 : ℂ) - 2 * (x : ℂ) ^ 2 = ((1 - 2 * x ^ 2 : ℤ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.intCast_re] at hnn
  have hint : (0 : ℤ) ≤ 1 - 2 * x ^ 2 := by exact_mod_cast hnn
  have h0 : (0 : ℤ) ≤ x ^ 2 := sq_nonneg x
  have hsq : x ^ 2 = 0 := by omega
  have hx0 : x = 0 := by rw [pow_two] at hsq; exact mul_self_eq_zero.mp hsq
  rw [hx, hx0, Int.cast_zero]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `ζ^{τ₁}` vanishes on `V`** (the genuine §5/§7 input, the textbook's
"By (5.3.b), (5.5) and (3.2.d), `ζ^{τ₁}` vanishes on `V`").

Reorganized to avoid the (5.4)/(5.5) `R(ζ)`-extraction machinery, using the integral norm-`1`
projection (`inner_left_eq_zero_of_inner_sub_eq_zero`) instead:
* `(ζ − ζ̄)^τ = ζ^{τ₁} − ζ̄^{τ₁}` vanishes on `V` (`tau_zeta_sub_conj_vanishes_on_typePV`) and has
  `NC ≤ 2 < min(w₁, w₂)`: each of `ζ^{τ₁}`, `ζ̄^{τ₁}` is a norm-`1` virtual character with at most
  one nonzero `σ`-coefficient (`ncard_inner_chiFam_ne_zero_le_one`), so by the (3.8) corollary
  `sigmaCoeff_eq_zero_of_sigmaNC_lt` every `σ`-coefficient of `(ζ − ζ̄)^τ` vanishes (Peterfalvi
  (5.3.b));
* `ζ^{τ₁}, ζ̄^{τ₁}` are orthonormal norm-`1` virtual characters (coherence isometry on `ℤ[S]`), so
  the projection lemma upgrades `⟨ζ^{τ₁} − ζ̄^{τ₁}, χ_{pq}⟩ = 0` to `⟨ζ^{τ₁}, χ_{pq}⟩ = 0`
  (Peterfalvi (5.5));
* orthogonality to every `χ_{pq} = ω_{pq}^σ` forces `ζ^{τ₁}` to vanish on `V` (Peterfalvi (3.2.d),
  `eq_zero_of_mem_V_of_inner_chiFam_eq_zero`).

This is the last analytic input of the (10.5) Dade-image identity; with the value-on-`V` leg it
gives `ψ = X − δ(ω^σ diff)` vanishing on `V` (`muGridPsi_vanishes_on_typePV`), unconditionally. -/
theorem Hypothesis.tau1_zeta_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {v : G} (hv : v ∈ typePV M hyp.typeP) :
    coh.tau1 ζ v = 0 := by
  haveI := hyp.finiteG
  classical
  -- the §5 `G`-level TI-cyclic hypothesis + Dade application (the ready (10.5) `σ` pattern).
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    ⟨tic.toDadeHypothesis.fullDadeIsometryData
      (OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl))⟩
  have hVeq : tic.V = tic.Vdiff := rfl
  -- `ζ̄ ∈ S` irreducible; the `τ₁`-images are orthonormal norm-`1` virtual characters of `G`.
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have haZ : coh.tau1 ζ ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ (Submodule.subset_span hζS)
  have hbZ : coh.tau1 ζ.conj ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ.conj (Submodule.subset_span hζcS)
  have ha1 : ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ) = 1 :=
    hyp.zeta_tau1_inner_self hG hodd coh hζS hζirr
  have hb1 : ClassFunction.inner (coh.tau1 ζ.conj) (coh.tau1 ζ.conj) = 1 :=
    hyp.zeta_tau1_inner_self hG hodd coh hζcS hζcirr
  have hab : ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ.conj) = 0 := by
    change ClassFunction.inner (coh.coherent.extension ζ) (coh.coherent.extension ζ.conj) = 0
    rw [coh.coherent.extension_inner_eq _ _ (Submodule.subset_span hζS)
        (Submodule.subset_span hζcS),
      OddOrder.RepresentationTheory.irr_cf_inner hζirr hζcirr, if_neg (fun h => hζne h.symm)]
  -- `(ζ − ζ̄)^τ` vanishes on `V`, with `NC ≤ 2 < min(w₁, w₂)`.
  have hvanish : ∀ w ∈ tic.V, hyp.tau (ζ - ζ.conj) w = 0 := fun w hw =>
    hyp.tau_zeta_sub_conj_vanishes_on_typePV hG hodd hζS hζirr hw
  have hNC : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
      < min (Nat.card ↥tic.W1) (Nat.card ↥tic.W2) := by
    have hbound : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj)) ≤ 2 := by
      have hsub : {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0} ⊆
          {pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0} ∪
          {pq | ClassFunction.inner (coh.tau1 ζ.conj) (tic.chiFam hVeq app pq) ≠ 0} := by
        intro pq hpq
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
        apply hpq
        change ClassFunction.inner (hyp.tau (ζ - ζ.conj)) (tic.chiFam hVeq app pq) = 0
        rw [hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr,
          ClassFunction.inner_sub_left, hcon.1, hcon.2, sub_zero]
      calc tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
          = {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0}.ncard := rfl
        _ ≤ ({pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0} ∪
              {pq | ClassFunction.inner (coh.tau1 ζ.conj) (tic.chiFam hVeq app pq) ≠ 0}).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ {pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0}.ncard +
              {pq | ClassFunction.inner (coh.tau1 ζ.conj) (tic.chiFam hVeq app pq) ≠ 0}.ncard :=
            Set.ncard_union_le _ _
        _ ≤ 1 + 1 := by
            gcongr
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app haZ ha1
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app hbZ hb1
        _ = 2 := rfl
    have h3a := tic.three_le_card_W1
    have h3b := tic.three_le_card_W2
    omega
  -- (3.2.d): orthogonality to every `χ_{pq}` forces vanishing on `V`.
  refine tic.eq_zero_of_mem_V_of_inner_chiFam_eq_zero hVeq app (fun a' b' => ?_) hv
  have hL3 : tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) (a', b') = 0 :=
    tic.sigmaCoeff_eq_zero_of_sigmaNC_lt hVeq app hvanish hNC (a', b')
  have hdiff : ClassFunction.inner (coh.tau1 ζ - coh.tau1 ζ.conj)
      (tic.chiFam hVeq app (a', b')) = 0 := by
    rw [← hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr]; exact hL3
  have hsZ : tic.chiFam hVeq app (a', b') ∈ ZIrr G := (tic.chiFam_spec hVeq app).2.1 (a', b')
  have hs1 : ClassFunction.inner (tic.chiFam hVeq app (a', b'))
      (tic.chiFam hVeq app (a', b')) = 1 := by
    rw [(tic.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  exact inner_left_eq_zero_of_inner_sub_eq_zero haZ hsZ ha1 hb1 hs1 hab hdiff

/-- **Peterfalvi (10.5), Dade-image half**: under the coherent extension, `α_{ij}` has the stated
Dade image `δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}`.  (The support half is `alpha_support`.) -/
theorem alpha_tau_image [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) :
    ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
        hyp.tau (params.alpha i j) =
          (params.delta : ℂ) • (params.omegaSigma i j - params.omegaSigma i 0)
            - (params.n : ℂ) • coh.tau1 params.zeta := by
  sorry

/-- **Peterfalvi (10.6)**: the sums of `omega_ij^sigma` describe the `tau1`
images, and outside the tame support the value of `zeta^tau1` has norm at least
one. -/
theorem tau1_values_and_norm_bound [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) :
    (∀ (j : Fin hyp.w2), j ≠ 0 →
        coh.tau1 (∑ i : Fin hyp.w1, params.mu i j) =
          (params.delta : ℂ) • ∑ i : Fin hyp.w1, params.omegaSigma i j) ∧
      params.zeta_tau1_norm_bound := by
  sorry

/-! ## (10.7)--(10.8): Type II derived Frobenius and non-coherence -/

/-- A carrier for the conclusion of Peterfalvi (10.7): `[S,S]` is a Frobenius
group with kernel `S_F`. -/
structure DerivedFrobeniusData (S : Subgroup G) where
  kernel : Subgroup ↥(derivedInG S)
  complement : Subgroup ↥(derivedInG S)
  kernel_is_SF : Prop
  frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG S) kernel complement

/-- **Peterfalvi (10.7)**: if `S` is a maximal subgroup of type II, then
`[S,S]` is Frobenius with kernel `S_F`. -/
theorem typeII_derived_frobenius [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSType : IsTypeII S) :
    ∃ data : DerivedFrobeniusData S, data.kernel_is_SF := by
  sorry

/-- **Peterfalvi (10.8)**: under Hypothesis (10.1), the character family `S` is
not coherent. -/
theorem S_not_coherent [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis M) :
    ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0) := by
  sorry

/-! ## (10.9)--(10.11): the Type V elimination and the case-B remark -/

/-- **Peterfalvi (10.9)**: when `w_1 < w_2`, the residual character in
`(mu_0 - zeta)^tau` is orthogonal to `(Irr W)^sigma`. -/
theorem orthogonality_of_w1_lt_w2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {hyp : Hypothesis M} (params : CharacterParameters hyp)
    (hw : hyp.w1 < hyp.w2) :
    params.orthogonality_w1_lt_w2 := by
  sorry

/-- **Peterfalvi (10.10.1)--(10.10.4)**: if Hypothesis (10.1) holds with `M`
of type V, then the Type V parameter calculation forces `S` to be coherent. -/
theorem typeV_forces_coherence [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} (hV : IsTypeV M) (params : CharacterParameters hyp) :
    params.typeV_parameter_formula ∧ params.typeV_coherence_formula ∧
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0) := by
  sorry

open scoped FiniteInduce in
/-- **Peterfalvi (10.10)**: `G` has no maximal subgroup of type V.

By (10.8) (`S_not_coherent`) the family `S` of any type-III/IV/V maximal is not
coherent; but a type-V maximal forces `S` to be coherent by (10.10.1)–(10.10.4)
(`typeV_forces_coherence`).  These now refer to the *genuine* Dade isometry,
induced family, and support carried by the faithful (10.1) `Hypothesis` (built by
`exists_hypothesis_of_typeIIIorIVorV`), so the contradiction is honest. -/
theorem no_typeV_maximal [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M := by
  rintro ⟨M, hMmax, hMV⟩
  obtain ⟨hyp⟩ := exists_hypothesis_of_typeIIIorIVorV hG hMmax (Or.inr (Or.inr hMV))
  obtain ⟨params, -⟩ := w2_prime_and_parameter_independence hG hyp
  exact S_not_coherent hG hyp (typeV_forces_coherence hG hMV params).2.2

/-- The case-(b) data in Peterfalvi (8.8), used in the remark (10.11). -/
structure Theorem88CaseBData (G : Type*) [Group G] where
  S : Subgroup G
  T : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  S_maximal : S ∈ maximalSubgroups G
  T_maximal : T ∈ maximalSubgroups G
  S_ne_T : S ≠ T
  W_eq : W = W1 ⊔ W2
  W_cyclic : IsCyclic ↥W
  S_nonI : IsTypeNonI S
  T_nonI : IsTypeNonI T
  one_typeII : IsTypeII S ∨ IsTypeII T
  /-- (8.8.b1): `W₁ ≤ S` and `S = [S,S] ⋊ W₁` (so `W₁` complements `S' = [S,S]` in `S`). -/
  W1_le_S : W1 ≤ S
  W2_le_T : W2 ≤ T
  S_compl : Subgroup.IsComplement' ((derivedInG S).subgroupOf S) (W1.subgroupOf S)
  T_compl : Subgroup.IsComplement' ((derivedInG T).subgroupOf T) (W2.subgroupOf T)

/-- A non-type-I maximal subgroup that is not of type V (so of type II/III/IV) carries type-`P`
data whose `W₁` has prime order — Peterfalvi (8.6.a), via `TypePNontrivialCore`.  Type V is
excluded by Theorem (10.10) `no_typeV_maximal`. -/
private theorem caseB_typeP_prime_W1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hnonI : IsTypeNonI M) :
    ∃ data : TypePData M, (Nat.card ↥data.W1).Prime := by
  rcases hnonI with h | h | h | h
  · exact ⟨h.some.typeP, h.some.common.2.1⟩
  · exact ⟨h.some.typeP, h.some.common.2.1⟩
  · exact ⟨h.some.typeP, h.some.common.2.1⟩
  · exact absurd ⟨M, hM, h⟩ (no_typeV_maximal hG)

/-- **Peterfalvi (10.11), first assertion**: in case (b) of Theorem (8.8), the
orders of `W_1` and `W_2` are prime.

By Theorem (10.10) `no_typeV_maximal`, the non-type-I subgroups `S`, `T` are of type II/III/IV,
whose type-`P` `W₁` has prime order (8.6.a).  The case-(b) factors `W₁`, `W₂` complement the
derived subgroups of `S`, `T` (8.8.b1, `S_compl`/`T_compl`), so they share the orders
`|S : S'|`, `|T : T'|` with the respective type-`P` `W₁` (`card_W1_eq_derived_index`) — hence prime. -/
theorem theorem88_caseB_prime_orders [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (caseB : Theorem88CaseBData G) :
    (Nat.card ↥caseB.W1).Prime ∧ (Nat.card ↥caseB.W2).Prime := by
  have hW1 : Nat.card ↥caseB.W1 = ((derivedInG caseB.S).subgroupOf caseB.S).index := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe caseB.W1_le_S).toEquiv,
      ← caseB.S_compl.symm.index_eq_card]
  have hW2 : Nat.card ↥caseB.W2 = ((derivedInG caseB.T).subgroupOf caseB.T).index := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe caseB.W2_le_T).toEquiv,
      ← caseB.T_compl.symm.index_eq_card]
  refine ⟨?_, ?_⟩
  · obtain ⟨dataS, hSp⟩ := caseB_typeP_prime_W1 hG caseB.S_maximal caseB.S_nonI
    rw [hW1, ← dataS.card_W1_eq_derived_index]; exact hSp
  · obtain ⟨dataT, hTp⟩ := caseB_typeP_prime_W1 hG caseB.T_maximal caseB.T_nonI
    rw [hW2, ← dataT.card_W1_eq_derived_index]; exact hTp

/-- **Peterfalvi (10.11), Type II assertion**: for a type-II maximal subgroup,
the §11 family `S(H_0 C')` specializes to a coherent set. -/
theorem typeII_section11_coherence [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M}
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData data}
    (chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent chars.tau chars.S chars.H0CprimeSupport) := by
  exact ⟨OddOrder.Peterfalvi.S11.coherent_H0C_commutator chars⟩

end OddOrder.Peterfalvi.S12
