import OddOrder.Peterfalvi.S15_CaseBReducibleCoherence

/-!
# Peterfalvi §9/§13 — the (9.11) caseA coherence campaign for the honest `S`-instance family

The non-Galois (caseA, Peterfalvi (9.11)) coherence of the honest §9 family `𝒮 = sSet`, its
case-combined assembly, and the (13.2.d) `τ₁` engines:

* **(9.11.1)**: the `𝒮₂ = 𝒮₁` saturated-bound extraction `nineElevenSTwoExtractionS`
  (axiom-clean) with its bricks `sOf_H0Uprime_subset_sSet` / `sSet_mem_Snorm_pos`.
* **(9.11.2)–(9.11.5)**: the equality-configuration refutation `nineElevenEqualityRefutationS`,
  assembled from the generic (9.11) apparatus (`S11.nineElevenTwo_two_summand_inertia`,
  `S11.nineElevenThree_orbit_split`, `S11.nineElevenCaseA_equality_refutation`) — no
  `htype`/`hncH0C` gate survives the definitional `sSet = 𝒮(H₀C′)` dictionary.
* **(9.11.4)**: the cleared Mackey-norm bundle `nineElevenFourNormInputsS` at the explicit
  TI-witness `cuSubOf caseA 0` (`cuSubOf_zero_tiWitness`, axiom-clean), with the `A(S)`-support
  residual `nineElevenAlphaSupportS` (the Coq gap-patch site `PFsection9.v:1478-1484`).
* **(9.11.6)**: the `𝒮₃`-coherence `sSet_sThree_coherent_dade` (the `τ₃`).
* **(9.11.4)–(9.11.8) residual**: the norm bound `nineElevenNormBoundS` (`|𝒮₄| ≤ ‖α^τ‖²`).
* **squeeze + case split**: `sSet_caseA_nineElevenRefutation` → `sSet_coherent_indS_caseA` →
  `sSet_coherent_indS_A`.
* **assembly**: the honest §9 character data `mkSection11CharacterDataS_honest`
  (`tau := Ind_S^G`, support `A(S)`), the packaged coherence `coherent_H0Cprime_S`, the coherent
  extension `tau1S_ofHonest`, and its (13.2.d) engines (`induce_H_mem_zSpan_S`,
  `tau1S_ofHonest_inner_induce`, `tau1S_ofHonest_induce_mem_ZIrr`) for the (13.3)
  `CharacterDegreeData` `τ₁`-fields.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The `𝒮(H₀U′)` stratum sits inside `𝒮 = 𝒮(H₀C′)`** (issue 1017): `C′ = [C,C] ≤ [U,U] = U′`
by commutator monotonicity (`cSub_le_U`), so `H₀ ⊔ C′ ≤ H₀ ⊔ U′` and `sOf` is antitone
(`sSet_eq_sOf_H0Cprime` dictionary).  Shared brick of the (9.11.1) extraction and the (9.11.3)
class-equation wiring. -/
theorem Hypothesis.sOf_H0Uprime_subset_sSet [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief) :
    OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG))
      ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG) := by
  rw [hyp.sSet_eq_sOf_H0Cprime hG chars]
  refine OddOrder.Peterfalvi.S11.sOf_antitone (hyp.toTypesIIIIIIVSetupS hG)
    (sup_le_sup_left ?_ chief.H0)
  change derivedInG (OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief)
    ≤ derivedInG (hyp.toTypesIIIIIIVSetupS hG).U
  rw [OddOrder.Peterfalvi.S11.derivedInG_eq_commutator
      (OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief),
    OddOrder.Peterfalvi.S11.derivedInG_eq_commutator (hyp.toTypesIIIIIIVSetupS hG).U]
  exact Subgroup.commutator_mono
    (OddOrder.Peterfalvi.S11.cSub_le_U (hyp.toTypesIIIIIIVSetupS hG) chief)
    (OddOrder.Peterfalvi.S11.cSub_le_U (hyp.toTypesIIIIIIVSetupS hG) chief)

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Every `𝒮 = sSet`-member has positive `Snorm` weight** (issue 1017; the `S`-instance mirror
of `S13.sOf_mem_Snorm_pos`): `Snorm χ = (χ(1).re)²/⟨χ,χ⟩.re` with `χ(1) = q·d` a positive
natural degree (`induceHU_apply_one_eq_q_mul`) and `⟨χ,χ⟩.re > 0` (the landed embedding
`sSet_subset_inducedKernelFamily` + `S08.inducedKernelFamily_inner_self_real_pos`). -/
theorem Hypothesis.sSet_mem_Snorm_pos [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {χ : ClassFunction ↥hyp.S ℂ}
    (hχ : χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) :
    0 < OddOrder.Peterfalvi.S07.Snorm χ := by
  haveI := hyp.finiteG
  classical
  have hpos := OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos
    (hyp.sSet_subset_inducedKernelFamily hG hχ)
  obtain ⟨ζ, hζ, rfl⟩ := hχ
  obtain ⟨dζ, hdpos, hdζ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ζ
  have hq : 0 < (hyp.toTypesIIIIIIVSetupS hG).q :=
    (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1.pos
  have hdeg : (induceHU (hyp.toTypesIIIIIIVSetupS hG)
      (ζ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ) : ↥hyp.S → ℂ) 1
      = (((hyp.toTypesIIIIIIVSetupS hG).q * dζ : ℕ) : ℂ) := by
    rw [induceHU_apply_one_eq_q_mul, hdζ]
    push_cast
    ring
  unfold OddOrder.Peterfalvi.S07.Snorm
  apply div_pos
  · rw [hdeg, Complex.natCast_re]
    exact pow_pos (Nat.cast_pos.mpr (Nat.mul_pos hq hdpos)) 2
  · exact hpos.2

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.1), the `𝒮₂ = 𝒮₁` extraction — `S`-instance residual** (issue 1017; the
`S`-mirror of the M-side `S13.caseA_sTwo_subset_degreeQaCut`, Coq `PFsection9.v:1626-1680`
`eqS12`).  At the equality configuration the degree-`qa` irreducible cut `𝒮₁′` of `𝒮(H₀U′)`
alone already saturates the (9.11.1) bound `2q²au` exactly (`sumnS_irreducible_constant_degree`
+ the (9.8.d) count equality `hcount` at `C = U′` and `2a = p−1`), so a `𝒮₂`-member outside
`𝒮₁′` would add its positive `Snorm` weight beyond `hFboundU` (positivity via the landed
`sSet_subset_inducedKernelFamily` + `S08.inducedKernelFamily_inner_self_real_pos`); hence
`𝒮₂ ⊆ 𝒮₁′`.  The M-side proof mirrors modulo the `sSet = 𝒮(H₀C′)` dictionary
(`sSet_eq_sOf_H0Cprime`) — no `htype`/`hncH0C` gate. -/
theorem Hypothesis.nineElevenSTwoExtractionS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars)
    (S₂ : Set (ClassFunction ↥hyp.S ℂ))
    (hS₁S₂ : hyp.sSetIrrDeg hG (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) ⊆ S₂)
    (hS₂S : S₂ ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (h2a : 2 * caseA.a = chief.p - 1)
    (hCUprime : chars.C = chars.Uprime)
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a)
        = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
          (hyp.toTypesIIIIIIVSetupS hG)).relIndex (hyp.toTypesIIIIIIVSetupS hG).U))
    (hFboundU : ∀ F : Finset (ClassFunction ↥hyp.S ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2
        * (caseA.a : ℝ) * (chars.u : ℝ)) :
    S₂ ⊆ {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
      IsIrreducibleCharacter χ ∧
        χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)} := by
  haveI := hyp.finiteG
  classical
  intro χ hχS₂
  by_contra hnot
  -- make the cut `𝒮₁′` an atom so cast rewrites cannot enter its set-builder
  set S1' : Set (ClassFunction ↥hyp.S ℂ) := {φ ∈ OddOrder.Peterfalvi.S11.sOf
      (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
      IsIrreducibleCharacter φ ∧
      φ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)} with hS1'def
  -- `𝒮₁′ ⊆ 𝒮₂` along `𝒮(H₀U′) ⊆ 𝒮` and the base cut `hS₁S₂`
  have hS1'sub : S1' ⊆ S₂ := fun φ hφ =>
    hS₁S₂ ⟨hyp.sOf_H0Uprime_subset_sSet hG chars hφ.1, hφ.2.1, hφ.2.2⟩
  have hS1'fin : S1'.Finite :=
    (sSet_finite (hyp.toTypesIIIIIIVSetupS hG)).subset fun φ hφ =>
      hyp.sOf_H0Uprime_subset_sSet hG chars hφ.1
  -- `sumnS 𝒮₁′ = |𝒮₁′|·(qa)²` (norm-one irreducibles of uniform degree `qa`)
  have hsum1' : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = (hS1'fin.toFinset.card : ℝ)
        * ((((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℝ)) ^ 2 :=
    OddOrder.Peterfalvi.S11.sumnS_irreducible_constant_degree hS1'fin.toFinset
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.1)
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.2)
  -- the count at `C = U′`: `|𝒮₁′|·a² = 2a·u` in `ℕ`
  have hrelu : (OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)).relIndex
      (hyp.toTypesIIIIIIVSetupS hG).U = chars.u := by
    have hUpC : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief
        = OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG) := hCUprime
    rw [← hUpC]
    exact OddOrder.Peterfalvi.S11.relIndex_cSub_U_eq_u chars
  have hcount' : S1'.ncard * (caseA.a * caseA.a) = 2 * caseA.a * chars.u := by
    rw [hcount, hrelu, ← h2a]
  -- `𝒮₁′` alone saturates the bound: `sumnS 𝒮₁′ = 2q²au` in `ℝ`
  have hsatur : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = 2 * (((hyp.toTypesIIIIIIVSetupS hG).q : ℝ)) ^ 2 * (caseA.a : ℝ) * (chars.u : ℝ) := by
    have hcast : ((S1'.ncard : ℝ)) * ((caseA.a : ℝ) * (caseA.a : ℝ))
        = 2 * (caseA.a : ℝ) * (chars.u : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcount'
    rw [hsum1', ← Set.ncard_eq_toFinset_card _ hS1'fin, Nat.cast_mul]
    linear_combination (((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2) * hcast
  -- the offending member: `χ ∈ 𝒮₂ ∖ 𝒮₁′` adds positive `Snorm` beyond the saturated bound
  have hχnot : χ ∉ hS1'fin.toFinset := fun hmem => hnot (hS1'fin.mem_toFinset.mp hmem)
  have hFsub : ↑(insert χ hS1'fin.toFinset) ⊆ S₂ := by
    rw [Finset.coe_insert]
    exact Set.insert_subset hχS₂
      (by rw [Set.Finite.coe_toFinset]; exact hS1'sub)
  have hbound := hFboundU _ hFsub
  have hsplit : OddOrder.Peterfalvi.S07.sumnS (insert χ hS1'fin.toFinset)
      = OddOrder.Peterfalvi.S07.Snorm χ
        + OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset := by
    unfold OddOrder.Peterfalvi.S07.sumnS
    exact Finset.sum_insert hχnot
  rw [hsplit, hsatur] at hbound
  linarith [hyp.sSet_mem_Snorm_pos hG (hS₂S hχS₂)]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.6), `𝒮₃`-coherence on the honest Dade map** (issue 1017; the `S`-instance
mirror of `S13.caseA_sThree_coherent`).  In the equality configuration every `𝒮₃ = 𝒮 ∖ 𝒮₂`-member
has uniform degree `q·u` (`hS3deg`), so the (5.7) norm-general coherence producer
`S07.uniform_degree_coherence_of_families` fires with an arbitrary pivot `χ₀ ∈ 𝒮₃`: per-member
(5.2.d) `R`-data from the case-agnostic `sSet_memberRFamily`, cross-orthogonality from
`sSet_memberRFamily_orthogonal`, the Dade isometry/`ℤ[Irr]` facts from
`dadeIntegralCharacterMap_*_of_supported`, and the equal-degree `A(S)`-difference supports from
`sSet_scaledDiff_support` at `c = 1`.  This is the `τ₃` of the (9.11.6) dichotomy: the coherent
extension of `𝒮₃` whose unit images the non-orthogonal branch counts against `‖α^τ‖²` (Bessel)
and whose orthogonal branch the (9.11.7)–(9.11.8) residual refutes. -/
theorem Hypothesis.sSet_sThree_coherent_dade [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    {S₂ : Set (ClassFunction ↥hyp.S ℂ)}
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₃ne : (sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂).Nonempty)
    (hS3deg : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      (χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)))
      (sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
  classical
  haveI := hyp.finiteG
  obtain ⟨χ₀, hχ₀⟩ := hS₃ne
  -- `𝒮₃` is conjugation-closed
  have hconj : ∀ a ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      a.conj ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂ := by
    intro a ha
    refine ⟨sSet_closedUnderConjugate _ ha.1, fun hc => ?_⟩
    have h := hS₂conj hc
    rw [ClassFunction.conj_conj] at h
    exact ha.2 h
  -- no member is real
  have hnr : ∀ a ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂, a ≠ a.conj :=
    fun a ha h => sSet_hasNoRealCharacters _ (hyp.oddCardS hG) ha.1 h.symm
  -- equal-degree differences are `A(S)`-supported (`sSet_scaledDiff_support` at `c = 1`)
  have hsuppdiff : ∀ a ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ∀ b ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ((a - b : ClassFunction ↥hyp.S ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S := by
    intro a ha b hb
    have h := hyp.sSet_scaledDiff_support hG ha.1 hb.1 (c := 1)
      (by rw [hS3deg a ha, hS3deg b hb, Nat.cast_one, one_mul])
    rwa [one_smul] at h
  -- pivot self-norm is a natural (`ℤ[Irr]` sum-of-squares)
  have hN : ∃ n : ℕ, ClassFunction.inner χ₀ χ₀ = (n : ℂ) := by
    obtain ⟨c, -, -, hcsum⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_self_eq_sum_sq
      (sSet_subset_ZIrr _ hχ₀.1)
    have hm0 : 0 ≤ ∑ x ∈ c.support, (c x) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine ⟨(∑ x ∈ c.support, (c x) ^ 2).toNat, ?_⟩
    rw [hcsum]
    exact_mod_cast (congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg hm0)).symm
  exact OddOrder.Peterfalvi.S07.uniform_degree_coherence_of_families
    ((sSet_finite _).subset Set.sdiff_subset)
    hχ₀
    (fun η hη => hyp.sSet_memberRFamily hG hη.1)
    (fun a ha b hb hab => by
      have h := sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) ha.1 hb.1 hab
      convert h using 2 <;> exact Subsingleton.elim _ _)
    hconj
    hnr
    hN
    (fun {φ ψ} hφ hψ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) hφ.2 hψ.2)
    (fun a ha b hb =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG)
        (hsuppdiff a ha b hb)
        (Submodule.sub_mem _ (sSet_subset_ZIrr _ ha.1) (sSet_subset_ZIrr _ hb.1)))
    hsuppdiff
    (fun {φ ξ} hφ hξ h1 h2 => hyp.sSet_memberRFamily_orthogonal hG hφ.1 hξ.1 h1 h2)
    (fun a ha => (hS3deg a ha).trans (hS3deg χ₀ hχ₀).symm)
    (by
      rw [hS3deg χ₀ hχ₀]
      exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero Nat.card_pos.ne'
        (OddOrder.Peterfalvi.S11.u_odd hG chars).pos.ne'))
    (by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
      simpa using honestTypeP2ASet_one_not_mem (M := hyp.S))
    (hconj χ₀ hχ₀)
    (fun h => hnr χ₀ hχ₀ h.symm)

open OddOrder.Peterfalvi.S11 in
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **The (9.11.2) TI-identity at the explicit witness `U₁ = C_U(H̄₀)`** (issue 1017).  The generic
producer `S11.nineElevenTwoTIWitness_of_degree_dichotomy` proves the (9.11.2) identity but returns
its witness behind an `∃`; the (9.11.4) `S`-instance support argument (`nineElevenAlphaSupportS`)
needs the witness **concretely** — `U₁ = cuSubOf caseA i` centralizes the chief-factor summand
`H̄ᵢ ≠ 1`, which is what puts `U₁^#` inside `A(S)` (coprime fixed-point lifting) — so this restates
the producer with the witness exposed at `i = 0`.  Proof = the producer's, verbatim;
upstream-merge candidate into `S11_NineElevenTIWitness` (issue 1017 update #51). -/
theorem cuSubOf_zero_tiWitness {M : Subgroup G} [Finite G]
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (hdeg : ∀ φ ∈ sOf data (chief.H0 ⊔ cSub data chief),
      (φ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ) ∨
      (φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ)) :
    ∀ w ∈ data.typeP.W1, w ≠ 1 →
      cuSubOf caseA ⟨0, data.nontrivial.2.1.pos⟩
          ⊓ MulAut.conj w • cuSubOf caseA ⟨0, data.nontrivial.2.1.pos⟩
        = cSub data chief := by
  classical
  have hq0 : 0 < data.q := data.nontrivial.2.1.pos
  by_cases hall : ∀ k, cuSubOf caseA k = cuSubOf caseA ⟨0, hq0⟩
  · -- all single-factor centralizers coincide: `C = U₁`, the TI-identity is trivial
    have hCeq : cSub data chief = cuSubOf caseA ⟨0, hq0⟩ := by
      apply le_antisymm (cSub_le_cuSubOf caseA ⟨0, hq0⟩)
      intro g hg
      exact mem_cSub_of_forall_mem_cuSubOf caseA (fun k => (hall k).symm ▸ hg)
    intro w hw _hne
    obtain ⟨j, hj⟩ := exists_conj_smul_cuSubOf_eq caseA hw ⟨0, hq0⟩
    rw [hj, hall j, inf_idem, ← hCeq]
  · -- some centralizer differs: the pair dichotomy resolves to index `u`
    push Not at hall
    obtain ⟨k₀, hk₀⟩ := hall
    intro w hw hne
    obtain ⟨j, hj⟩ := exists_conj_smul_cuSubOf_eq caseA hw ⟨0, hq0⟩
    -- `C_U(H_j) ≠ U₁`: else `⟨w⟩ = W₁` fixes `U₁` and transitivity collapses all
    have hjne : cuSubOf caseA j ≠ cuSubOf caseA ⟨0, hq0⟩ := by
      intro hjeq
      apply hk₀
      have hwfix : MulAut.conj w • cuSubOf caseA ⟨0, hq0⟩ = cuSubOf caseA ⟨0, hq0⟩ := by
        rw [hj, hjeq]
      have hallfix : ∀ v ∈ data.typeP.W1,
          MulAut.conj v • cuSubOf caseA ⟨0, hq0⟩ = cuSubOf caseA ⟨0, hq0⟩ := by
        intro v hv
        obtain ⟨n, rfl⟩ := exists_zpow_of_mem_W1 hw hne v hv
        rw [map_zpow]
        have hstab : MulAut.conj w
            ∈ MulAction.stabilizer (MulAut G) (cuSubOf caseA ⟨0, hq0⟩) :=
          MulAction.mem_stabilizer_iff.mpr hwfix
        exact MulAction.mem_stabilizer_iff.mp (zpow_mem hstab n)
      obtain ⟨w0, hw0W, hw0⟩ := exists_w1_rep_Hpart caseA k₀
      obtain ⟨wi, hwiW, hwi⟩ := exists_w1_rep_Hpart caseA ⟨0, hq0⟩
      have hvW : ((w0 * wi⁻¹ : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) ∈ data.typeP.W1 :=
        mul_mem hw0W (inv_mem hwiW)
      have hHk₀ : caseA.Hpart k₀ = quotientMulAutHom chief.N_aInvariant (w0 * wi⁻¹)
          • caseA.Hpart ⟨0, hq0⟩ := by
        rw [hw0, hwi, map_mul, mul_smul, map_inv, inv_smul_smul]
      have hdict := conj_smul_cuSubOf_of_Hpart_smul caseA (w0 * wi⁻¹).2 hHk₀
      rw [← hdict]
      exact hallfix _ hvW
    have hij : (⟨0, hq0⟩ : Fin data.q) ≠ j := fun h => hjne (by rw [h])
    rcases nineElevenTwo_relIndex_dichotomy caseA hij hdeg with hu | ha
    · -- index `u`: `C = U₁ ∩ U₁^w` by index equality
      have hCle : cSub data chief ≤ cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j :=
        le_inf (cSub_le_cuSubOf caseA ⟨0, hq0⟩) (cSub_le_cuSubOf caseA j)
      have hCeq : cSub data chief = cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j := by
        by_contra hne'
        have hlt := OddOrder.Peterfalvi.S07.relIndex_lt_relIndex_of_le_of_ne hCle
          (inf_le_left.trans (cuSubOf_le_U caseA ⟨0, hq0⟩)) (fun h => hne' h.symm)
        rw [hu, relIndex_cSub_U_eq_u chars] at hlt
        exact lt_irrefl _ hlt
      rw [hj, ← hCeq]
    · -- index `a`: would force `C_U(H_{i₀}) = C_U(H_j)`, contradicting `hjne`
      exfalso
      apply hjne
      have hi : cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j = cuSubOf caseA ⟨0, hq0⟩ := by
        by_contra hne'
        have hlt := OddOrder.Peterfalvi.S07.relIndex_lt_relIndex_of_le_of_ne
          (inf_le_left : cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j
            ≤ cuSubOf caseA ⟨0, hq0⟩)
          (cuSubOf_le_U caseA ⟨0, hq0⟩) (fun h => hne' h.symm)
        rw [relIndex_cuSubOf_U_eq_a caseA ⟨0, hq0⟩, ha] at hlt
        exact lt_irrefl _ hlt
      have hjeq : cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j = cuSubOf caseA j := by
        by_contra hne'
        have hlt := OddOrder.Peterfalvi.S07.relIndex_lt_relIndex_of_le_of_ne
          (inf_le_right : cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j ≤ cuSubOf caseA j)
          (cuSubOf_le_U caseA j) (fun h => hne' h.symm)
        rw [relIndex_cuSubOf_U_eq_a caseA j, ha] at hlt
        exact lt_irrefl _ hlt
      rw [← hjeq, hi]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.4), the `A(S)`-support of `α = γ − ψ₁` — `S`-instance residual**
(issue 1017; the Coq gap-patch site `PFsection9.v:1478-1484`).  For the explicit TI-witness
`U₁ = cuSubOf caseA i = C_U(H̄ᵢ)` and a degree-`qa` member `ψ₁ ∈ 𝒮`, the difference
`α = Ind_{HU₁}^S 1 − ψ₁` is supported in `A(S) = {y ∈ (S′)^# | ∃ x ∈ S_σ^#, y ∈ C(x)}`
(`mem_honestTypeP2ASet`; `H = S_σ = Msigma`).  The M-side dispatches this via
`A(M) = (M′)^#` (`mderivSharp_subset_A0`), **false** here (`A(S) ⊊ (S′)^#` strictly); the honest
route is the book's patched (9.11.4) argument: `supp γ ⊆ ⋃_g (HU₁)^g`
(`support_induce_subset_conjugatesInto`), and `HU₁^# ⊆ A(S)` by the commuting Hall decomposition
in `⟨y⟩` — a nontrivial `H`-part `h ∈ ⟨y⟩ ∩ H^#` gives `y ∈ C(h)` directly, while a σ′-element
`y` lies in a Hall-conjugate of `U₁` (solvable `HU₁`, Hall conjugacy) and `U₁ = C_U(H̄ᵢ)`
centralizes a nontrivial `H`-element by coprime fixed-point lifting; `ψ₁`'s support is
`A(S) ∪ {1}` (`sSet_member_support_subset`) and the value at `1` cancels
(`γ(1) = qa = ψ₁(1)`). -/
theorem Hypothesis.nineElevenAlphaSupportS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars) (i : Fin (hyp.toTypesIIIIIIVSetupS hG).q)
    {ψ₁ : ClassFunction ↥hyp.S ℂ}
    (hψ₁mem : ψ₁ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hψ₁deg : (ψ₁ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)) :
    (ClassFunction.induce
        ((hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S
          ⊔ (cuSubOf caseA i).subgroupOf hyp.S)
        (trivialClassFunction ↥((hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S
          ⊔ (cuSubOf caseA i).subgroupOf hyp.S))
      - ψ₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S := by
  sorry

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.4) at the `S`-instance: the cleared Mackey-norm bundle** (issue 1017; the
`S`-mirror of `S13.caseA_nineElevenFour_norm_inputs`).  In the equality configuration (`C = U′`,
the (9.8.d) count) there is `N : ℕ` with `N·u = (a+1)·u + (q−1)·a²`, realized as `N = ‖α‖²` for
the `A(S)`-supported virtual character `α = γ − ψ₁ ∈ ℤ[Irr S]` — `γ = Ind_{HU₁}^S 1` at the
explicit TI-witness `U₁ = cuSubOf caseA 0` (`cuSubOf_zero_tiWitness`), `ψ₁` a degree-`qa`
irreducible member from the (9.8.d) count.  Norm: `‖α‖² = ‖γ‖² + 1`
(`cfnorm_sub_irreducible_orthogonal`; orthogonality `nineElevenGamma_inner_induceHU`) and
`‖γ‖²·u = a·u + (q−1)·a²` (`nineElevenGamma_inner_self_mul_u`, the Mackey double-coset count at
the TI-identity); integrality by `mem_ZIrr_inner_self_eq_sum_sq`; support by the
`nineElevenAlphaSupportS` residual. -/
theorem Hypothesis.nineElevenFourNormInputsS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars)
    (hdich : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief),
      (φ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ) ∨
      (φ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ))
    (hCUprime : chars.C = chars.Uprime)
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a)
        = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
          (hyp.toTypesIIIIIIVSetupS hG)).relIndex (hyp.toTypesIIIIIIVSetupS hG).U)) :
    ∃ N : ℕ,
      N * chars.u = (caseA.a + 1) * chars.u
        + ((hyp.toTypesIIIIIIVSetupS hG).q - 1) * caseA.a ^ 2 ∧
      ∃ α : ClassFunction ↥hyp.S ℂ,
        α ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S ∧
        α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S ∧
        ClassFunction.inner α α = (N : ℂ) := by
  classical
  haveI := hyp.finiteG
  have hq0 : 0 < (hyp.toTypesIIIIIIVSetupS hG).q :=
    (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1.pos
  -- the explicit TI-witness `U₁ = cuSubOf caseA 0` and its (9.11.2) facts
  have hTI := cuSubOf_zero_tiWitness caseA hdich
  have hCU₁ : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief
      ≤ cuSubOf caseA ⟨0, hq0⟩ := cSub_le_cuSubOf caseA ⟨0, hq0⟩
  have hU₁U : cuSubOf caseA ⟨0, hq0⟩ ≤ (hyp.toTypesIIIIIIVSetupS hG).U :=
    cuSubOf_le_U caseA ⟨0, hq0⟩
  have hU₁a : (cuSubOf caseA ⟨0, hq0⟩).relIndex (hyp.toTypesIIIIIIVSetupS hG).U = caseA.a :=
    relIndex_cuSubOf_U_eq_a caseA ⟨0, hq0⟩
  have hUpU₁ : OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)
      ≤ cuSubOf caseA ⟨0, hq0⟩ := by
    have hUpC : OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)
        = OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief := hCUprime.symm
    rw [hUpC]; exact hCU₁
  -- `ψ₁ ∈ 𝒮₁`: the degree-`qa` irreducible family is nonempty by the (9.8.d) count
  have hrelne : (OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)).relIndex
      (hyp.toTypesIIIIIIVSetupS hG).U ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcne : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
      IsIrreducibleCharacter χ ∧
        χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcount
    have hp1 : 1 < chief.p := chief.p_prime.one_lt
    have hrpos := Nat.pos_of_ne_zero hrelne
    have : 0 < (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
        (hyp.toTypesIIIIIIVSetupS hG)).relIndex (hyp.toTypesIIIIIIVSetupS hG).U) :=
      Nat.mul_pos (by omega) hrpos
    omega
  obtain ⟨ψ₁, hψ₁sOf, hψ₁irr, hψ₁deg⟩ := Set.nonempty_of_ncard_ne_zero hcne
  obtain ⟨ζ, hζmem, hψ₁eq⟩ := hψ₁sOf
  have hζxi : ζ ∈ OddOrder.Peterfalvi.S11.xiSet (hyp.toTypesIIIIIIVSetupS hG) :=
    OddOrder.Peterfalvi.S11.xiOf_subset_xiSet (hyp.toTypesIIIIIIVSetupS hG) _ hζmem
  -- `γ = Ind_{HU₁}^S 1` and its landed (9.11.4) facts
  set K : Subgroup ↥hyp.S := (hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S
    ⊔ (cuSubOf caseA ⟨0, hq0⟩).subgroupOf hyp.S with hKdef
  set γ : ClassFunction ↥hyp.S ℂ :=
    ClassFunction.induce K (trivialClassFunction ↥K) with hγdef
  have hγZIrr : γ ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S :=
    nineElevenGamma_mem_ZIrr (hyp.toTypesIIIIIIVSetupS hG) (cuSubOf caseA ⟨0, hq0⟩)
  have hγ1 : γ (1 : ↥hyp.S) = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) :=
    nineElevenGamma_apply_one (hyp.toTypesIIIIIIVSetupS hG) hU₁U hU₁a
  have hγγu : ClassFunction.inner γ γ * (chars.u : ℂ)
      = ((caseA.a * chars.u
          + ((hyp.toTypesIIIIIIVSetupS hG).q - 1) * caseA.a ^ 2 : ℕ) : ℂ) :=
    nineElevenGamma_inner_self_mul_u chars hU₁U hUpU₁ hU₁a hTI
  have hindEq : induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ζ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
      = ClassFunction.induce (huSub (hyp.toTypesIIIIIIVSetupS hG))
        (ζ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ) := rfl
  -- orthogonality `⟨γ, ψ₁⟩ = 0` and the norm split `‖α‖² = ‖γ‖² + 1`
  have hγψ : ClassFunction.inner γ ψ₁ = 0 := by
    rw [hψ₁eq, hindEq]
    exact nineElevenGamma_inner_induceHU (hyp.toTypesIIIIIIVSetupS hG) hU₁U hζxi
  have hαα : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) = ClassFunction.inner γ γ + 1 :=
    cfnorm_sub_irreducible_orthogonal hψ₁irr hγψ
  -- `α ∈ ℤ[Irr S]` and the integrality of `‖α‖²`
  have hαZIrr : γ - ψ₁ ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S := by
    refine Submodule.sub_mem _ hγZIrr ?_
    rw [hψ₁eq]
    exact induceHU_mem_ZIrr (hyp.toTypesIIIIIIVSetupS hG) ζ
  obtain ⟨c, -, -, hcsum⟩ :=
    OddOrder.RepresentationTheory.mem_ZIrr_inner_self_eq_sum_sq hαZIrr
  have hm0 : 0 ≤ ∑ x ∈ c.support, (c x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmval : ClassFunction.inner (γ - ψ₁) (γ - ψ₁)
      = ((∑ x ∈ c.support, (c x) ^ 2 : ℤ) : ℂ) := by
    rw [hcsum]
    push_cast
    rfl
  set N : ℕ := (∑ x ∈ c.support, (c x) ^ 2).toNat with hNdef
  have hNval : ((N : ℕ) : ℂ) = ClassFunction.inner (γ - ψ₁) (γ - ψ₁) := by
    rw [hmval, hNdef]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg hm0)
  refine ⟨N, ?_, γ - ψ₁, hαZIrr, ?_, hNval.symm⟩
  · -- the cleared norm identity `N·u = (a+1)·u + (q−1)·a²`, by `ℕ`-cast injectivity
    have h2 : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) * (chars.u : ℂ)
        = ((caseA.a * chars.u
            + ((hyp.toTypesIIIIIIVSetupS hG).q - 1) * caseA.a ^ 2 : ℕ) : ℂ)
          + (chars.u : ℂ) := by
      rw [hαα, add_mul, one_mul, hγγu]
    have h3 : ((N * chars.u : ℕ) : ℂ)
        = (((caseA.a + 1) * chars.u
            + ((hyp.toTypesIIIIIIVSetupS hG).q - 1) * caseA.a ^ 2 : ℕ) : ℂ) := by
      push_cast at h2 ⊢
      rw [hNval]
      linear_combination h2
    exact Nat.cast_injective h3
  · -- `Supp(α) ⊆ A(S)`: the (9.11.4) support residual at the explicit witness
    have hψ₁mem : ψ₁ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) :=
      hyp.sOf_H0Uprime_subset_sSet hG chars ⟨ζ, hζmem, hψ₁eq⟩
    exact hyp.nineElevenAlphaSupportS hG chars caseA ⟨0, hq0⟩ hψ₁mem hψ₁deg

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.4)–(9.11.8), the norm bound — `S`-instance residual** (issue 1017; the
`S`-mirror of the M-side `S13.NineElevenNormBound` discharge
(`nineElevenNormBound_of_sevenEightRefutation` + `nineElevenSevenEightRefutation`, issue 9083
Phases D/E, both landed M-side)).  **(9.11.4)**: `α = Ind_{HU₁}^S 1 − ψ₁` is an `A(S)`-supported
virtual character with the cleared Mackey norm `N·u = (a+1)·u + (q−1)·a²` (mirror of
`caseA_nineElevenFour_norm_inputs`: the (9.11.2) TI-witness from
`S11.nineElevenTwoTIWitness_of_degree_dichotomy` at the `S`-instance degree dichotomy, the
double-coset count `S11.nineElevenGamma_inner_self_mul_u`, and `‖α‖² = ‖γ‖² + 1` via
`S11.cfnorm_sub_irreducible_orthogonal`).  **(9.11.5)–(9.11.8)**: `|𝒮₄| ≤ N = ‖α^τ‖²` — in the
orthogonal branch of the (9.11.6) dichotomy the projection budget
(`S13.exists_bridge_target_of_budget`) plus the union-pair extension
(`S13.isCoherent_union_pair_of_bridge`, suppliable via the case-agnostic `sSet_memberRFamily`)
would coherently adjoin a conjugate pair from `𝒮₄`, contradicting `hnopair`; in the
non-orthogonal branch distinct `𝒮₄`-members consume orthogonal integral slices of `α^τ` (Bessel,
`card_le_inner_self_re_of_orthonormal_inner_int_ne`).  Here `𝒮₄` is the irreducible part of the
`𝒮(H₀C)` stratum outside `𝒮₂` (the `S`-instance `nineElevenSFour`), whose `ncard` is exactly the
`S4` of the (9.11.3) class equation. -/
theorem Hypothesis.nineElevenNormBoundS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars)
    (S₂ : Set (ClassFunction ↥hyp.S ℂ))
    (hS₁S₂ : hyp.sSetIrrDeg hG (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) ⊆ S₂)
    (hS₂S : S₂ ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₂coh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS S₂
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)))
    (hS₃ne : (sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂).Nonempty)
    (hnopair : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS (S₂ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)))
    (h2a : 2 * caseA.a = chief.p - 1)
    (hCUprime : chars.C = chars.Uprime)
    (hS3deg : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      (χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ))
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a)
        = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
          (hyp.toTypesIIIIIIVSetupS hG)).relIndex (hyp.toTypesIIIIIIVSetupS hG).U))
    (hFboundU : ∀ F : Finset (ClassFunction ↥hyp.S ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2
        * (caseA.a : ℝ) * (chars.u : ℝ))
    (hS2deg : ∀ χ ∈ S₂,
      (χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)) :
    ∃ N : ℕ,
      N * chars.u = (caseA.a + 1) * chars.u
        + ((hyp.toTypesIIIIIIVSetupS hG).q - 1) * caseA.a ^ 2 ∧
      {φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) |
        IsIrreducibleCharacter φ ∧ φ ∉ S₂}.ncard ≤ N := by
  sorry

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.2)–(9.11.8), the `S`-instance equality-configuration refutation**
(issue 1017 step (c); the `S`-mirror of the M-side assembler
`S13.nineElevenEqualityRefutation_of_sTwoExtraction_normBound`).  The (9.11.1) squeeze in
`sSet_caseA_nineElevenRefutation` forces the *equality configuration* at any pair-refuted maximal
`𝒮₂` — `2a = p−1`, `C = U′`, every `𝒮₃ = 𝒮 ∖ 𝒮₂`-member of degree `q·u`, the count equality
`|𝒮₁(q·a)|·a² = (p−1)·[U:U′]`, and the saturated subfamily bound `sumnS F ≤ 2q²a·u`.  This
theorem refutes that configuration.

**Assembly (no `htype`/`hncH0C` gate).**  The generic (9.11) apparatus fires directly at
`data := toTypesIIIIIIVSetupS hG`: the `𝒮(H₀C)`-stratum degree dichotomy — from `hS3deg` and the
(9.11.1) `𝒮₂ = 𝒮₁` extraction `nineElevenSTwoExtractionS` through the `sSet = 𝒮(H₀C′)`
dictionary `sSet_eq_sOf_H0Cprime` — feeds the (9.11.2) inertia identity
`S11.nineElevenTwo_two_summand_inertia` and the (9.11.3) class equation
`S11.nineElevenThree_orbit_split`; the (9.11.4)–(9.11.8) norm bound `nineElevenNormBoundS`
supplies `hnorm`/`hle`; the tau-free arithmetic core `S11.nineElevenCaseA_equality_refutation`
closes.  The M-side `htype`/`hncH0C` inputs existed only to identify the `Hypothesis M`
packaging's `H₀C′` with the generic `cprimeSub` stratum (`C_eq_cSub_of_noncoherent`); the
`S`-instance dictionary is definitional, so they vanish.  Remaining named residuals:
`nineElevenSTwoExtractionS` and `nineElevenNormBoundS`. -/
theorem Hypothesis.nineElevenEqualityRefutationS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars)
    (S₂ : Set (ClassFunction ↥hyp.S ℂ))
    (hS₁S₂ : hyp.sSetIrrDeg hG (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) ⊆ S₂)
    (hS₂S : S₂ ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₂coh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS S₂
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)))
    (hS₃ne : (sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂).Nonempty)
    (hnopair : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS (S₂ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)))
    (h2a : 2 * caseA.a = chief.p - 1)
    (hCUprime : chars.C = chars.Uprime)
    (hS3deg : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      (χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ))
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a)
        = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
          (hyp.toTypesIIIIIIVSetupS hG)).relIndex (hyp.toTypesIIIIIIVSetupS hG).U))
    (hFboundU : ∀ F : Finset (ClassFunction ↥hyp.S ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2
        * (caseA.a : ℝ) * (chars.u : ℝ)) :
    False := by
  classical
  -- ── (9.11.1) `𝒮₂ = 𝒮₁`: the saturated-bound extraction (residual)
  have hS₂cut := hyp.nineElevenSTwoExtractionS hG chars caseA S₂ hS₁S₂ hS₂S h2a hCUprime
    hcount hFboundU
  have hS2deg : ∀ χ ∈ S₂,
      (χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) :=
    fun χ hχ => (hS₂cut hχ).2.2
  -- ── dictionary: the `𝒮(H₀C)` stratum sits inside `𝒮 = 𝒮(H₀C′)` (`C′ ≤ C`)
  have hsubC : OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief)
      ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG) := by
    rw [hyp.sSet_eq_sOf_H0Cprime hG chars]
    exact OddOrder.Peterfalvi.S11.sOf_antitone (hyp.toTypesIIIIIIVSetupS hG)
      (sup_le_sup_left chars.Cprime_le_C chief.H0)
  -- ── the `𝒮(H₀C)`-stratum degree dichotomy (`qu` outside `𝒮₂`, `qa` inside)
  have hdich : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief),
      (φ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ) ∨
      (φ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) := by
    intro φ hφ
    by_cases hφS₂ : φ ∈ S₂
    · exact Or.inr (hS2deg φ hφS₂)
    · exact Or.inl (hS3deg φ ⟨hsubC hφ, hφS₂⟩)
  -- ── (9.11.2): the two-summand inertia identity `C = K₁ ⊓ K₂`, `[U:Kᵢ] = a`
  obtain ⟨K₁, K₂, hK₁, hK₂, hCinf⟩ :=
    OddOrder.Peterfalvi.S11.nineElevenTwo_two_summand_inertia caseA hdich
  -- ── (9.11.3): the class equation at `n = |𝒮₄|·q + (p−1)`
  have hS₁'sub : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
      IsIrreducibleCharacter χ ∧
        χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)} ⊆ S₂ := fun χ hχ =>
    hS₁S₂ ⟨hyp.sOf_H0Uprime_subset_sSet hG chars hχ.1, hχ.2.1, hχ.2.2⟩
  have hCU : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief
      = OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG) := hCUprime
  have hclass := OddOrder.Peterfalvi.S11.nineElevenThree_orbit_split hG caseA hS₁'sub
    (fun χ hχ hn => hS3deg χ ⟨hsubC hχ, hn⟩) hS2deg hCU hcount
  -- ── (9.11.4)–(9.11.8): the norm bound `|𝒮₄| ≤ N` (residual)
  obtain ⟨N, hnorm, hleN⟩ := hyp.nineElevenNormBoundS hG chars caseA S₂ hS₁S₂ hS₂S hS₂conj
    hS₂coh hS₃ne hnopair h2a hCUprime hS3deg hcount hFboundU hS2deg
  -- ── numerics: `q ≥ 3` odd prime, `u ≥ 1`, `p = 2a+1`
  have hqp : ((hyp.toTypesIIIIIIVSetupS hG).q).Prime :=
    (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1
  have hqodd : Odd (hyp.toTypesIIIIIIVSetupS hG).q :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (hyp.toTypesIIIIIIVSetupS hG).typeP.W1)
  have hq3 : 3 ≤ (hyp.toTypesIIIIIIVSetupS hG).q := by
    obtain ⟨k, hk⟩ := hqodd
    have h2 := hqp.two_le
    omega
  have hu : 1 ≤ chars.u := (OddOrder.Peterfalvi.S11.u_odd hG chars).pos
  have hp1 : 1 < chief.p := chief.p_prime.one_lt
  have hpeq : chief.p = 2 * caseA.a + 1 := by omega
  -- ── the tau-free arithmetic core closes
  exact OddOrder.Peterfalvi.S11.nineElevenCaseA_equality_refutation caseA hq3 hu hpeq
    hK₁ hK₂ hCinf hclass rfl hnorm hleN

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.1)–(9.11.8), the `S`-instance equality-configuration refutation** (issue 1017,
the sole residual of `sSet_coherent_indS_caseA`, mirroring the M-instance
`nineElevenSevenEightRefutation` / `nineElevenEqualityRefutation_of_sevenEightRefutation`).

Given a maximal proper coherent conjugation-closed `𝒮₂` with the degree-`q·a` base cut
`S₁(q·a) ⊆ 𝒮₂ ⊊ 𝒮 = sSet`, `𝒮₃ = 𝒮 ∖ 𝒮₂ ≠ ∅` and *no* conjugate pair `{χ, χ̄}` (`χ ∈ 𝒮₃`)
coherently adjoinable, derive `False`.

**Reuse map (verified STEP-1 for the assembly, issue 1017 hub note).**  Via
`sSet_eq_sOf_H0Cprime` the full family `𝒮` *is* the `H₀C′` stratum `sOf data (chief.H₀ ⊔ chars.Cprime)`,
so the entire generic (9.11) apparatus — all phrased over `sOf data (chief.H₀ ⊔ …)`,
`{data}{chief}{chars}(caseA)`-parametrized, hence directly instantiable at `data :=
toTypesIIIIIIVSetupS hG` — applies:
* the (9.11.2)–(9.11.5) arithmetic contradiction `S11.nineElevenCaseA_equality_refutation`;
* the (9.11.1) squeeze `S11.nineElevenOne_configuration` + `S11.sumnS_irreducible_constant_degree`;
* the world-facts *from the degree dichotomy*: `S11.nineElevenTwoTIWitness_of_degree_dichotomy`
  (TI-witness), `S11.nineElevenTwo_two_summand_inertia` (inertia `C = K₁ ⊓ K₂`),
  `S11.nineElevenGamma_inner_self_mul_u` (Mackey norm), `S11.nineElevenThree_orbit_split` (class eq);
* the abstract projection budget `S13.exists_bridge_target_of_budget` and the (5.6.3) union-pair
  extension `S13.isCoherent_union_pair_of_bridge` for the (9.11.7)–(9.11.8) coherent-pair adjunction.
The genuinely `S`-specific pieces still to build are the caseA per-member Dade `R`-family (the
analogue of the M-side `sOf_H0Cprime_memberRFamily`, feeding `𝒮₃`-coherence and the coherent-image
cross-orthogonality) and the (5.6) pair-bound producer for the `indS`/`A(S)` world; the (9.11.7)–
(9.11.8) orthogonal branch is itself a residual on the M-side (issue 9083 Phase E). -/
theorem Hypothesis.sSet_caseA_nineElevenRefutation [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars)
    (S₂ : Set (ClassFunction ↥hyp.S ℂ))
    (hS₁S₂ : hyp.sSetIrrDeg hG (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) ⊆ S₂)
    (hS₂S : S₂ ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₂coh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS S₂
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)))
    (hS₃ne : (sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂).Nonempty)
    (hnopair : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS (S₂ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S))) :
    False := by
  classical
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- numeric positivity inputs of the (9.11.1) squeeze
  have hq : 0 < (hyp.toTypesIIIIIIVSetupS hG).q :=
    (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1.pos
  have hu : 0 < chars.u := (OddOrder.Peterfalvi.S11.u_odd hG chars).pos
  have hp1 : 0 < chief.p - 1 := Nat.sub_pos_of_lt chief.p_prime.one_lt
  -- strata collapse (issue 1017 step (a)): the generic (9.11) `U′`-anchor stratum is the full family
  have hcollapse : OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG))
      = sSet (hyp.toTypesIIIIIIVSetupS hG) := hyp.sOf_H0_uprime_eq_sSet hG chief
  -- the degree-`qa` anchor cut over the `U′`-stratum sits inside `𝒮₂` (it is `S₁(qa) ⊆ 𝒮₂`)
  have hS1'sub : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
        IsIrreducibleCharacter χ ∧
          χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)} ⊆ S₂ :=
    fun χ hχ => hS₁S₂ ⟨hcollapse ▸ hχ.1, hχ.2.1, hχ.2.2⟩
  have hS1'fin : ({χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
        IsIrreducibleCharacter χ ∧
          χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}).Finite :=
    (sSet_finite (hyp.toTypesIIIIIIVSetupS hG)).subset (fun χ hχ => hcollapse ▸ hχ.1)
  -- (9.11.5) left endpoint: `sumnS 𝒮₁′ = |𝒮₁′|·(qa)²` (norm-one uniform degree-`qa` irreducibles)
  have hsum1' : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = (hS1'fin.toFinset.card : ℝ)
        * (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℝ) ^ 2 :=
    OddOrder.Peterfalvi.S11.sumnS_irreducible_constant_degree hS1'fin.toFinset
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.1)
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.2)
  have hs1' : (({χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard : ℝ))
        * (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℝ) ^ 2
      ≤ OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset :=
    le_of_eq (by rw [Set.ncard_eq_toFinset_card _ hS1'fin, hsum1'])
  -- per-`χ` (9.11.1) squeeze: the (5.6) pair-bound + squeeze force the equality configuration
  have hconfig : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ∃ d : ℕ, ((χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * d : ℕ) : ℂ)) ∧
        (2 * caseA.a = chief.p - 1 ∧ chars.C = chars.Uprime ∧ d = chars.u ∧
          {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
              (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
              IsIrreducibleCharacter χ ∧
                χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard
            * (caseA.a * caseA.a)
            = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
              (hyp.toTypesIIIIIIVSetupS hG)).relIndex (hyp.toTypesIIIIIIVSetupS hG).U)) ∧
        (∀ F : Finset (ClassFunction ↥hyp.S ℂ), ↑F ⊆ S₂ →
          OddOrder.Peterfalvi.S07.sumnS F
            ≤ 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ)) := by
    intro χ hχ
    obtain ⟨d, hχdeg, hdu, hFbound⟩ :=
      hyp.nineElevenPairBoundS hG chars caseA S₂ hS₁S₂ hS₂S hS₂conj hS₂coh χ hχ (hnopair χ hχ)
    have hpair : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
        ≤ 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ) :=
      hFbound hS1'fin.toFinset (by rw [Set.Finite.coe_toFinset]; exact hS1'sub)
    exact ⟨d, hχdeg,
      OddOrder.Peterfalvi.S11.nineElevenOne_configuration hG caseA hq hu hp1 hdu hs1' hpair,
      hFbound⟩
  -- extract the global equality-configuration facts from a `𝒮₃`-witness
  obtain ⟨χ₀, hχ₀⟩ := hS₃ne
  obtain ⟨d₀, -, ⟨h2a, hCUprime, hd₀u, hcount⟩, hFbound₀⟩ := hconfig χ₀ hχ₀
  -- every `𝒮₃`-member has the uniform degree `qu` (the squeeze run per member)
  have hS3deg : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      (χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ) := by
    intro χ hχ
    obtain ⟨d, hχdeg, ⟨-, -, hdu, -⟩, -⟩ := hconfig χ hχ
    rwa [hdu] at hχdeg
  -- the saturated subfamily bound `sumnS F ≤ 2q²au`
  have hFboundU : ∀ F : Finset (ClassFunction ↥hyp.S ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F
        ≤ 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2 * (caseA.a : ℝ) * (chars.u : ℝ) := by
    intro F hF
    have h := hFbound₀ F hF
    rwa [hd₀u] at h
  -- hand the equality configuration to the (9.11.2)–(9.11.8) refutation residual
  exact hyp.nineElevenEqualityRefutationS hG chars caseA S₂ hS₁S₂ hS₂S hS₂conj hS₂coh
    ⟨χ₀, hχ₀⟩ hnopair h2a hCUprime hS3deg hcount hFboundU

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) non-Galois-branch coherence of the full family `𝒮 = sSet` on `Ind_S^G`** (issue 1017,
caseA of Peterfalvi (9.11) `Ptype_core_coherence`, Coq `PFsection9.v:1484`).  In the non-Galois case
(`CliffordCaseAData`) the honest §9 family `𝒮 = sSet` is **genuinely mixed-degree**: the degree-`q·a`
irreducibles fill `𝒮(H₀U′)` (at least `((p−1)/a)·(|U|/(a|U′|))` of them, `caseA_character_counts` /
`caseA_exists_irreducible_qa`) alongside the degree-`q·u` members of `𝒮(H₀C)` (the `p−1` reducible
μ_j residues plus an irreducible).  Because the degrees genuinely differ (`q·a ≠ q·u`), this is
**not** the uniform-degree Galois route (caseB `sSet_coherent_indS_caseB`,
`uniform_degree_coherence_of_families`): it is Peterfalvi's (9.11) **maximal-coherent-subfamily
refutation**, mirroring the M-instance non-Galois assembly (`S11_NineElevenAlphaBound.lean`), not the
uniform fold `caseB_coherent_sOf_H0Cprime_of_mixed`.

Honest route via `coherent_of_maximal_coherent_pair_refuted` (`S07_Subcoherent.lean:702`):
* **base** = the degree-`q·a` irreducible cut `S₁(q·a)` is the coherent conjugation-closed prefix
  (`sSetIrrDeg_qa_coherent_indS_caseA`, **landed sorry-free** modulo the accepted `dadeHypS` Dade
  foundation; conjugation-closure `sSetIrrDeg_closedUnderConjugate`, `q·a` positive real);
* **reduction** = the ambient family `𝒮` is finite (`sSet_finite`) and conjugation-closed
  (`sSet_closedUnderConjugate`), so a maximal proper coherent conj-closed intermediate `S₁ ⊆ 𝒮₂ ⊊ 𝒮`
  either equals `𝒮` (done) or is the (9.11) refutation target.

The reduction is landed sorry-free; the **sole residual** is the refuter, i.e. Peterfalvi's
(9.11.1)–(9.11.8) equality-configuration refutation for the honest Dade world (`indS`, `A(S)`).  The
`S`-instance-specific prerequisites for closing it (each still to be built in `b`-territory):
* the **caseA per-member Dade `R`-family** — the `CliffordCaseAData` analogue of the landed
  `sSet_caseB_memberRFamily` (`S15_CaseBReducibleCoherence.lean`), feeding the `Dmem`/`Da` of the
  (5.6) adjoining engine `xAdjoinStepW_k`;
* the **(9.11.1)–(9.11.6) squeeze assembly** for `indS`/`A(S)` — the analogue of the M-instance
  `nineElevenEqualityRefutation_of_sevenEightRefutation` (`S11_NineElevenAlphaBound.lean:1124`), whose
  bricks `lb0_le_lb1_of_degreeRatio_le` / `two_mul_le_of_dvd_of_odd` / `relIndex_le_relIndex_of_le` /
  `sumnS_of_norm_one_constant_degree` / `sumnS_le_of_subset` are already landed in `S07_Subcoherent`;
* the **(9.11.7)–(9.11.8) orthogonal-branch refutation** — the `S`-instance analogue of the M-instance
  `NineElevenSevenEightRefutation` (`S11_NineElevenAlphaBound.lean:786`), which is *itself* still a
  named residual on the M-side (issue 9083 Phase E), i.e. the deepest genuinely-unlanded piece of the
  whole non-Galois (9.11) — not an `S`-instance-only gap. -/
theorem Hypothesis.sSet_coherent_indS_caseA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
  classical
  -- Peterfalvi (9.11) non-Galois: the maximal-coherent-subfamily refutation.  The degree-`q·a`
  -- irreducible cut `S₁(q·a)` is the coherent conjugation-closed base prefix
  -- (`sSetIrrDeg_qa_coherent_indS_caseA`, landed); `coherent_of_maximal_coherent_pair_refuted`
  -- reduces coherence of the full mixed family `𝒮 = sSet` to refuting a maximal proper coherent
  -- conjugation-closed `𝒮₂ ⊇ S₁(q·a)` with `𝒮₃ = 𝒮 \ 𝒮₂ ≠ ∅` and no adjoinable conjugate pair.
  refine OddOrder.Peterfalvi.S07.coherent_of_maximal_coherent_pair_refuted
    (sSet_finite _)
    (sSet_closedUnderConjugate _)
    (hyp.sSetIrrDeg_subset_sSet hG (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ))
    (hyp.sSetIrrDeg_closedUnderConjugate hG (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)
      (star_natCast _))
    (hyp.sSetIrrDeg_qa_coherent_indS_caseA hG chars caseA)
    ?_
  -- The (9.11.1)–(9.11.8) refuter (sole residual): given a maximal proper coherent conjugation-closed
  -- `𝒮₂ ⊇ S₁(q·a)` with `𝒮₃ = 𝒮 \ 𝒮₂ ≠ ∅` and *no* conjugate pair `{χ, χ̄}` (`χ ∈ 𝒮₃`) coherently
  -- adjoinable, derive `False`.  Book argument: the (9.11.1) degree squeeze `lb0 = 2·q·a·χ(1) < sumnS 𝒮₂`
  -- would fire the (5.6) adjoining engine `xAdjoinStepW_k` on some `χ ∈ 𝒮₃` (contradicting `hnopair`),
  -- so every squeeze inequality `lb0 ≤ lb1 ≤ lb2 ≤ lb3 ≤ sumnS S₁′ ≤ sumnS 𝒮₂` is an equality — a
  -- configuration refuted by (9.11.7)–(9.11.8).  See the theorem docstring for the three remaining
  -- `b`-territory prerequisites (caseA `R`-family; (9.11.1)–(9.11.6) squeeze assembly for `indS`/`A(S)`;
  -- the (9.11.7)–(9.11.8) refutation, still a residual even on the M-side, issue 9083).
  intro S₂ hS₁S₂ hS₂S hS₂conj hS₂coh hS₃ne hnopair
  exact hyp.sSet_caseA_nineElevenRefutation hG chars caseA S₂ hS₁S₂ hS₂S hS₂conj hS₂coh hS₃ne hnopair
open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) coherence of the full honest §9 family `𝒮 = sSet` on `Ind_S^G`, unconditional** (issue
1017 — the honest S-instance Peterfalvi (9.11) `Ptype_core_coherence`, replacing the unsound
`sibleyTarget_H0C`).  Case-splits the Clifford dichotomy (9.7) (`clifford_dichotomy` on the honest
character data) and dispatches to the Galois branch (`sSet_coherent_indS_caseB`) or the non-Galois
branch (`sSet_coherent_indS_caseA`).  The map is the genuine induction `τ = Ind_S^G` (`indS`,
(13.2.e)) and the support is the honest Dade support `A(S)` (nonempty — unlike the degenerate
`(C′)^# = ∅`, which makes `IsCoherent`'s `nonzero` field unsatisfiable). -/
theorem Hypothesis.sSet_coherent_indS_A [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
  rcases clifford_dichotomy hG (hyp.mkSection11CharacterDataS_honest hG chief) with hA | hB
  · exact hyp.sSet_coherent_indS_caseA hG (hyp.mkSection11CharacterDataS_honest hG chief) hA.some
  · exact hyp.sSet_coherent_indS_caseB hG (hyp.mkSection11CharacterDataS_honest hG chief) hB.some

open scoped FiniteInduce in
/-- **(9.11)-coherence of the honest `S`-instance §9 data** (issue 2035 step 4; re-grounded off the
unsound `sibleyTarget_H0C`, issue 1017).  The `.some` of the honest unconditional
`sSet_coherent_indS_A`, yielding `IsCoherent Ind_S^G 𝒮 A(S)` — the Peterfalvi (13.2.d)⇐(9.11)
coherence for `𝒮(H₀C′) = 𝒮` (in the type-`P₂` `S`-instance, `H₀C′ = ⊥`) with the genuine Dade map
`τ = Ind_S^G` and the honest Dade support `A(S)`.

**This no longer routes through `coherent_H0C_commutator`/`sibleyTarget_H0C`** (the unsound (6.8)
shortcut whose target `IsCoherent Ind_S^G 𝒮 (C′)^# = IsCoherent Ind_S^G 𝒮 ∅` is uninhabited).  The
remaining gap is the honest (9.11) pair-adjoining assembly inside `sSet_coherent_indS_{caseA,caseB}`
(base coherences landed, the mixed-family lift sorried-cite), not a soundness defect. -/
noncomputable def Hypothesis.coherent_H0Cprime_S [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S07.IsCoherent (hyp.mkSection11CharacterDataS_honest hG chief).tau
      (hyp.mkSection11CharacterDataS_honest hG chief).S
      (hyp.mkSection11CharacterDataS_honest hG chief).H0CprimeSupport :=
  (hyp.sSet_coherent_indS_A hG chief).some

open scoped FiniteInduce in
/-- **The coherent extension `τ₁` for the honest `S`-instance** (issue 2035 step 4): the
`.extension` of the (9.11)-coherence `coherent_H0Cprime_S`.  This is the (13.2.d) `τ₁ :
IntegralCharacterMap ↥S G` that the (13.3) degree analysis threads (the `μ_j^{τ₁}` machinery).
Now grounded on the honest `sSet_coherent_indS_A` (base coherences landed, mixed-family lift
sorried-cite), no longer on the unsound `sibleyTarget_H0C`. -/
noncomputable def Hypothesis.tau1S_ofHonest [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.S G :=
  (hyp.coherent_H0Cprime_S hG chief).extension

open scoped FiniteInduce in
/-- **Type-alignment probe for the (13.3) `τ₁` route** (issue 2035 step 4 verification): confirms
`coherent_H0Cprime_S` obtains and its `.extension` is definitionally `tau1S_ofHonest`, of the
expected `IntegralCharacterMap ↥S G` type; and that `extends_on_supported` gives
`τ₁ φ = Ind_S^G φ` on the supported span (`tau1S_apply_induce` on the family) — the input to the
(13.3) `tau1S_apply_induce_sub` / `tau1S_inner_induce` / `tau1S_induce_mem_ZIrr` fields. -/
theorem Hypothesis.tau1S_ofHonest_extends_on_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (φ : ClassFunction ↥hyp.S ℂ)
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.mkSection11CharacterDataS_honest hG chief).S
      (hyp.mkSection11CharacterDataS_honest hG chief).H0CprimeSupport) :
    hyp.tau1S_ofHonest hG chief φ = ClassFunction.induce hyp.S φ := by
  have h := (hyp.coherent_H0Cprime_S hG chief).extends_on_supported φ hφ
  -- `.extension φ = chars.tau φ = indS φ = Ind_S^G φ`
  simpa [Hypothesis.tau1S_ofHonest, Hypothesis.mkSection11CharacterDataS_honest,
    Hypothesis.indS_apply] using h

set_option linter.unusedFintypeInType false in
/-- **Constituent kernel step for (1.5.a)** (Coq `S1cases` inner kernel argument), stated
generically.  For subgroups `P0, K'` of a finite group `Γ`, an irreducible `s ∈ Irr(Γ)`, and an
irreducible `θ'` of `K'` with `P0.subgroupOf K' ⊄ ker θ'`: if `θ'` is a constituent of
`Res_{K'} s` (`⟨θ', Res_{K'} s⟩ ≠ 0`), then `P0 ⊄ ker s`.

**Contrapositive.**  `P0 ⊆ ker s` makes `Res_{K'} s` trivial on `P0.subgroupOf K'`
(`characterKernel_restrict_subgroupOf`); `θ'`, a constituent of the genuine character `Res_{K'} s`
(`isCharacter_restrict`), inherits the containment
(`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), so `P0.subgroupOf K' ⊆ ker θ'`,
contradicting the hypothesis.  This is the `S`-instance analogue of the leaf
`PrimeTIResidue.constituent_P_not_subset_ker`, grounded on the honest `S'`-family — no
`PrimeTIResidueData` and no prime-TI dichotomy is used. -/
private theorem constituent_P_not_subset_characterKernel {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] (P0 K' : Subgroup Γ) [Fintype ↥K']
    [Invertible (Nat.card ↥K' : ℂ)]
    (θ' : ClassFunction ↥K' ℂ)
    (hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθ'P : ¬ ((P0.subgroupOf K' : Set ↥K') ⊆ OddOrder.Peterfalvi.S03.characterKernel θ'))
    (s : OddOrder.RepresentationTheory.IrreducibleCharacter Γ)
    (hs : ClassFunction.inner θ' (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) ≠ 0) :
    ¬ ((P0 : Set Γ) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction Γ ℂ)) := by
  intro hker
  have hResChar : IsCharacter (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) :=
    OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter K'
  have hinner' : ClassFunction.inner
      (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) θ' ≠ 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm]
    exact star_ne_zero.mpr hs
  have hResker : ((P0.subgroupOf K') : Set ↥K') ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) :=
    OddOrder.Peterfalvi.S08.characterKernel_restrict_subgroupOf K' hker
  exact hθ'P fun x hx =>
    OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
      hResChar hθ'irr hinner' (hResker hx)

open scoped FiniteInduce in
/-- **Peterfalvi (13.5) preamble / (1.5.a) — the family membership `Ind_{PC}^S θ ∈ ℤ[𝒮]`**
(issue 2035 step 5a).

For an irreducible character `θ` of `H = PC` **whose kernel does not contain `P`**, the induced
character `Ind_{PC}^S θ` lies in `ℤ[𝒮]` (`zSpan` of the honest §9 family `𝒮 = sSet`).  In
Coq's `PFsection13` this is `sS1S : {subset calS1 <= 'Z[calS]}` (with `calS1 = seqIndD H S P 1`,
`calS = seqIndD PU S P 1`), used implicitly throughout (13.5)–(13.8).

**Honest proof, grounded on the S06 §4 residue theory** (issue 9014 session 8).  The family
`𝒮 = sSet = {Ind_{S'}^S χ | χ ∈ Irr(S'), P ⊄ ker χ}` is *exactly* the set of inductions
from the derived subgroup `S' = huSub` of `P`-nonlinear irreducibles (`P = data.H`), so **membership
is by witness** — no dichotomy on the induced character is needed.  Writing the single-stage
`Ind_{PC}^S θ` as the two-stage `Ind_{S'}^S (Ind_{PC'}^{S'} θ')` (`induce_induce_subgroupOf`, with
`PC' = (PC).subgroupOf S'` and `θ'` the transport of `θ`) and expanding the inner induction into
`S'`-constituents `Ind_{PC'}^{S'} θ' = ∑_{s ∈ Irr(S')} ⟨θ', Res s⟩ • s`
(`induce_eq_sum_inner_restrict_smul`), each constituent `s` with nonzero (necessarily `ℕ`)
coefficient has `P ⊄ ker s` (`constituent_P_not_subset_characterKernel`), so `Ind_{S'}^S s`
lies in `sSet` by witness `s`; the coefficient-weighted `ℤ`-sum lands in `zSpan sSet`.  This
grounds the family
membership on the proven S06 setup (`typePData_toS06Hypothesis` for `S` supplies the certain-type
Hypothesis, though only its `S'`-family shape is needed here); no prime-TI residue dichotomy is used. -/
theorem Hypothesis.induce_H_mem_zSpan_S [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∈
      OddOrder.Peterfalvi.S07.zSpan (hyp.mkSection11CharacterDataS_honest hG chief).S := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Fintype ↥((derivedInG hyp.S).subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Fintype ↥(hyp.H.subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((derivedInG hyp.S).subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hyp.H.subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- Target family is `sSet data` with `data = toTypesIIIIIIVSetupS hG`.
  rw [OddOrder.Peterfalvi.S11.Section11CharacterData.S_eq]
  set data := hyp.toTypesIIIIIIVSetupS hG with hdata
  -- Work with the §9 induction carrier `HU = huSub data`, equal to `S' = derivedInG S` in `↥S`.
  set HU : Subgroup ↥hyp.S := OddOrder.Peterfalvi.S11.huSub data with hHU
  have hHUeq : HU = (derivedInG hyp.S).subgroupOf hyp.S :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf data
  letI : Fintype ↥HU := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥HU : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `PC = H.subgroupOf S ≤ S' = HU`.
  have hHderiv : hyp.H ≤ derivedInG hyp.S := by
    show hyp.P ⊔ hyp.C ≤ derivedInG hyp.S
    rw [hyp.S_deriv_eq_PU]
    exact sup_le le_sup_left (le_trans (hyp.C_eq ▸ inf_le_left) le_sup_right)
  have hKle : hyp.H.subgroupOf hyp.S ≤ HU := by
    rw [hHUeq]; exact Subgroup.subgroupOf_mono hyp.S hHderiv
  letI : Fintype ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- The transport `θ' = θ ∘ e` of `θ` onto `PC' = (PC).subgroupOf HU ≤ HU`.
  have hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hKle).surjective hθ
  -- Two-stage induction: `Ind_{PC}^S θ = Ind_{HU}^S (Ind_{PC'}^{HU} θ')`.
  rw [← OddOrder.RepresentationTheory.induce_induce_subgroupOf hKle θ]
  -- Expand the inner induction into `HU`-constituents and push `Ind_{HU}^S` inside.
  rw [OddOrder.RepresentationTheory.induce_eq_sum_inner_restrict_smul
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ),
    ClassFunction.induce_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [ClassFunction.induce_smul]
  -- The coefficient `⟨θ', Res s⟩` is a non-negative integer `(k : ℂ)`.
  have hResChar : IsCharacter (ClassFunction.restrict
      ((hyp.H.subgroupOf hyp.S).subgroupOf HU) (s : ClassFunction ↥HU ℂ)) :=
    OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter _
  obtain ⟨k, hk⟩ := hResChar.exists_natCast_inner_irreducible hθ'irr
  have hc : ClassFunction.inner
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
      (ClassFunction.restrict ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
        (s : ClassFunction ↥HU ℂ)) = (k : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hk, star_natCast]
  rw [hc, Nat.cast_smul_eq_nsmul ℂ k (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · simp [hk0]
  · refine nsmul_mem ?_ k
    -- `P (in HU) ⊄ ker s`: kernel step from `P ⊄ ker θ'` (from `hθP`) and constituent `θ'`.
    have hθ'P : ¬ ((((hyp.P.subgroupOf hyp.S).subgroupOf HU).subgroupOf
          ((hyp.H.subgroupOf hyp.S).subgroupOf HU) :
        Set ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)) := by
      rw [OddOrder.RepresentationTheory.subset_characterKernel_compHom_iff]
      -- The image of `((P.subgroupOf S).subgroupOf HU).subgroupOf (PC.subgroupOf HU)` under `e`
      -- is `(P.subgroupOf S).subgroupOf (PC.subgroupOf S)`, which `hθP` does not kill.
      have himg : (((hyp.P.subgroupOf hyp.S).subgroupOf HU).subgroupOf
            ((hyp.H.subgroupOf hyp.S).subgroupOf HU)).map
            (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
          = (hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) := by
        ext y
        rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
          Subgroup.mem_subgroupOf]
        rfl
      rw [himg]; exact hθP
    refine Submodule.subset_span ?_
    rw [OddOrder.Peterfalvi.S11.mem_sSet]
    refine ⟨s, ?_, rfl⟩
    -- `s ∈ xiSet data`: `hInHu data ⊄ ker s`, with `hInHu = (P.subgroupOf S).subgroupOf HU`.
    show ¬ ((OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction ↥HU ℂ))
    have hHInHu : (OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU)
        = ((hyp.P.subgroupOf hyp.S).subgroupOf HU : Set ↥HU) := by
      congr 1
      show (data.H.subgroupOf hyp.S).subgroupOf HU = (hyp.P.subgroupOf hyp.S).subgroupOf HU
      have hPeq : data.H = hyp.P := by
        show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
      rw [hPeq]
    rw [hHInHu]
    -- The generic kernel step: `θ'` is a constituent of `Res s` (coefficient `k > 0`), and
    -- `P (in HU) ⊄ ker θ'` (`hθ'P`), so `P (in HU) ⊄ ker s`.
    have hs : ClassFunction.inner
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
        (ClassFunction.restrict ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
          (s : ClassFunction ↥HU ℂ)) ≠ 0 := by
      rw [hc]; exact_mod_cast hk0.ne'
    exact constituent_P_not_subset_characterKernel ((hyp.P.subgroupOf hyp.S).subgroupOf HU)
      ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) hθ'irr hθ'P s hs

open scoped FiniteInduce in
/-- **(13.2.d) τ₁ isometry on the `H`-induced family** (issue 2035 step 5a): `τ₁ = tau1S_ofHonest`
preserves inner products of `Ind_{PC}^S θ` for irreducible `θ` of `H = PC` with `P ⊄ Ker θ`.  From
the coherence field `extension_inner_eq` (isometric on all of `ℤ[𝒮]`) together with the family
membership `induce_H_mem_zSpan_S`.  This is the honest engine for the `CharacterDegreeData`
`tau1S_inner_induce` field (with the `P ⊄ Ker` hypothesis the (13.3) consumers actually satisfy —
`μ_j`, `λ` all have `P ⊄ Ker`). -/
theorem Hypothesis.tau1S_ofHonest_inner_induce [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθ' : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hθ'P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ')) :
    ClassFunction.inner
        (hyp.tau1S_ofHonest hG chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ))
        (hyp.tau1S_ofHonest hG chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'))
      = ClassFunction.inner (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)
          (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') := by
  exact (hyp.coherent_H0Cprime_S hG chief).extension_inner_eq _ _
    (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP)
    (hyp.induce_H_mem_zSpan_S hG chief θ' hθ' hθ'P)

open scoped FiniteInduce in
/-- **(13.2.d) τ₁ sends the `H`-induced family into `ℤ[Irr G]`** (issue 2035 step 5a): for
irreducible `θ` of `H = PC` with `P ⊄ Ker θ`, `τ₁ (Ind_{PC}^S θ) ∈ ℤ[Irr G]`.  From the coherence
field `extension_mem_ZIrr` (virtual-character codomain on all of `ℤ[𝒮]`) and the family membership
`induce_H_mem_zSpan_S`.  Honest engine for the `CharacterDegreeData` `tau1S_induce_mem_ZIrr` field. -/
theorem Hypothesis.tau1S_ofHonest_induce_mem_ZIrr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    hyp.tau1S_ofHonest hG chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) ∈ ZIrr G :=
  (hyp.coherent_H0Cprime_S hG chief).extension_mem_ZIrr _
    (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP)

end OddOrder.Peterfalvi.S15
