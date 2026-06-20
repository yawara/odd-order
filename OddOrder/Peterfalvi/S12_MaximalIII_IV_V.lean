/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_MaximalII_III_IV
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
  -- `M'` is not perfect: `M'' ≤ F(M) < M'`.
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hM''lt : secondDerivedInAmbient M < derivedInG M :=
    lt_of_le_of_lt (data.secondDerived_le_fitting.trans data.fitting_eq.ge) data.fitting_lt_derived
  have hcomm_K : commutator ↥h.K ≠ ⊤ := by
    intro hperf
    have hperfM' : Group.IsPerfect ↥(derivedInG M) := by
      haveI : Group.IsPerfect ↥((derivedInG M).subgroupOf M) := ⟨hperf⟩
      exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hM'le).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hM'le).surjective
    have heq : secondDerivedInAmbient M = derivedInG M := by
      rw [secondDerivedInAmbient, derivedInG, hperfM'.commutator_eq_top, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    exact hM''lt.ne heq
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

/-- The character parameters obtained in Peterfalvi (10.2)--(10.3).

The fields `degree_independent`, `delta_independent`, and `n_formula` name the
arithmetic conclusions whose detailed proofs come from (4.5.a) and the
automorphism calculation around (3.9). -/
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
  degree_independent : Prop
  degree_independent_holds : degree_independent
  delta_independent : Prop
  delta_independent_holds : delta_independent
  n_formula : Prop
  n_formula_holds : n_formula
  mu : Fin hyp.w1 → Fin hyp.w2 → ClassFunction ↥M ℂ
  omegaSigma : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ
  alpha : Fin hyp.w1 → Fin hyp.w2 → ClassFunction ↥M ℂ
  alpha_formula : Prop
  alpha_formula_holds : alpha_formula
  alpha_tau_formula : Prop
  mu_tau1_formula : Prop
  zeta_tau1_norm_bound : Prop
  orthogonality_w1_lt_w2 : Prop
  typeV_parameter_formula : Prop
  typeV_coherence_formula : Prop

/-- **Peterfalvi (10.4)**: the coherent-extension hypothesis for the family of
characters in (10.1). -/
structure CoherentHypothesis {M : Subgroup G} [Fintype G] [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis M) (params : CharacterParameters hyp) where
  coherent_S : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0)
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  tau1_extends_tau_on_S : Prop
  tau1_extends_tau_on_S_holds : tau1_extends_tau_on_S

/-- **Peterfalvi (10.2)**: the family `S` contains an irreducible character
`zeta` of degree `w_1`. -/
theorem exists_zeta_degree_w1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ params : CharacterParameters hyp,
      params.zeta ∈ hyp.Sset ∧ IsIrreducibleCharacter params.zeta ∧
        params.zeta 1 = ((hyp.w1 : ℕ) : ℂ) := by
  sorry

/-- **Peterfalvi (10.3)**: `w_2` is prime and the parameters `d`, `delta`, and
`n = (d - delta) / w_1` are well-defined and independent of the indices. -/
theorem w2_prime_and_parameter_independence [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ params : CharacterParameters hyp,
      hyp.w2.Prime ∧ 1 < params.d ∧ params.degree_independent ∧
        params.delta_independent ∧ params.n_formula := by
  sorry

/-! ## (10.5)--(10.6): Dade-isometry calculations -/

/-- **Peterfalvi (10.5)**: the virtual characters `alpha_ij` are supported on
`A_0(M)`, and under the coherent extension they have the stated Dade image. -/
theorem alpha_support_and_image [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) :
    (∀ i j, (params.alpha i j).support ⊆ hyp.A0) ∧ params.alpha_tau_formula := by
  sorry

/-- **Peterfalvi (10.6)**: the sums of `omega_ij^sigma` describe the `tau1`
images, and outside the tame support the value of `zeta^tau1` has norm at least
one. -/
theorem tau1_values_and_norm_bound [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) :
    params.mu_tau1_formula ∧ params.zeta_tau1_norm_bound := by
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
