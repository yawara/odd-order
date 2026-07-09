import OddOrder.Peterfalvi.S15_SAndT_Setup.CountingLayer

/-!
# Peterfalvi (13.5)-(13.10) — norm estimate tail

Split from the former monolithic `OddOrder.Peterfalvi.S15_SAndT_Setup` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ### The four (13.6)–(13.9) estimate producers

Each is a *faithful* statement of one textbook estimate in terms of the shared atoms; together
they assemble into `analyticInequalityEstimates` `sorry`-free.  Remaining gates, per producer:

* `analyticEstimate_lambda` (13.6): the (13.3) character `λ` (the `chars` fields are bare —
  `character_degree_analysis` is the upstream `sorry`) + the (13.5) ρ-machinery
  (`H_sharp_hypothesis76`, proven) + the `u`-bound `2u ≤ |P|−1` (issue 9000);
* `analyticEstimate_eta` (13.7)+(13.8): the T-side (13.5) machinery + the carried grid
  properties (`tau3_isometry`/`omega_orthonormal`, issue 3002 — now threaded);
* `analyticCounting_disjointCover` (13.9.a): pure group-theoretic counting of the disjoint
  cover `G = {1} ⊔ G₀ ⊔ (H#)^G ⊔ (Q#)^G` (TI-sets with normalizers `S`/`T`) + the (13.4)
  counting values;
* `analyticEstimate_galois` (13.9.b): the per-cyclic-class Galois bound
  (`sum_normSq_ge_ncard_of_isCharacter_of_cyclicClosed`) + the (13.9) nonvanishing dichotomy
  (`λ^{τ₁}`, `η₁₀` do not vanish simultaneously on `G₀`). -/

/-- The (13.4) case-(b) parameters, unpacked: `d = 1`, `v ≥ 2`, and (for the type-V exclusion
of the counting layer) `vd ≠ 1`. -/
theorem Hypothesis.caseB_vd_facts (hyp : Hypothesis (G := G))
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1)) :
    hyp.d = 1 ∧ 2 ≤ hyp.v ∧ hyp.v * hyp.d ≠ 1 := by
  have hd1 : hyp.d = 1 := by rw [hyp.d_eq_card_D, hD, Subgroup.card_bot]
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hqp_ge : hyp.q * hyp.q ≤ hyp.q ^ hyp.p := by
    calc hyp.q * hyp.q = hyp.q ^ 2 := (sq hyp.q).symm
      _ ≤ hyp.q ^ hyp.p := Nat.pow_le_pow_right (by omega)
        (by have := hyp.three_le_p; omega)
  have hv2 : 2 ≤ hyp.v := by
    rw [hv, Nat.le_div_iff_mul_le (by omega : 0 < hyp.q - 1)]
    have h3q : 3 * hyp.q ≤ hyp.q * hyp.q := Nat.mul_le_mul_right _ hq3
    omega
  exact ⟨hd1, hv2, by rw [hd1, mul_one]; omega⟩

/- `Hypothesis.eta10_mem_ZIrr` moved up next to the `eta10` definition (issue 2033:
the (1.10) congruence helper cites it). -/

open scoped FiniteInduce in
/-- **`‖η₁₀‖² = 1`** — real content of the 3002-threaded grid: `τ₃` is an isometry
(`tau3_isometry`) and the `ω`-grid is orthonormal (`omega_orthonormal`). -/
theorem Hypothesis.eta10_inner_self_one [Finite G] (hyp : Hypothesis (G := G)) :
    ClassFunction.inner hyp.eta10 hyp.eta10 = 1 := by
  rw [Hypothesis.eta10, hyp.eta_eq_tau_omega, hyp.tau3_isometry.inner_eq,
    hyp.omega_orthonormal]
  simp

open scoped FiniteInduce in
/-- **`λ^{τ₁}` is a norm-one virtual character** — the (13.2.d)/(13.3) coherence-isometry facts
for the distinguished `λ`: `τ₁` extends the Dade isometry isometrically on `ℤ[S] ∋ λ`, and `λ`
is irreducible.  Faithful producer; gated on the (13.3) analysis (`character_degree_analysis`)
pinning `tau1S` to the coherence extension of (13.2.d). -/
theorem lambda_tau1_norm_one [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (chars : CharacterDegreeData hyp) :
    chars.tau1S chars.lambda ∈ ZIrr G ∧
      ClassFunction.inner (chars.tau1S chars.lambda) (chars.tau1S chars.lambda) = 1 ∧
      ClassFunction.inner chars.lambda chars.lambda = 1 := by
  obtain ⟨θ, hθirr, -, hlamEq, -⟩ := chars.lambda_induced_from_PC_linear
  have hnorm : ClassFunction.inner chars.lambda chars.lambda = 1 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨chars.lambda, chars.lambda_irreducible⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      ⟨chars.lambda, chars.lambda_irreducible⟩
    simpa using h
  refine ⟨?_, ?_, hnorm⟩
  · rw [hlamEq]
    exact chars.tau1S_induce_mem_ZIrr θ hθirr
  · rw [hlamEq, chars.tau1S_inner_induce θ θ hθirr hθirr, ← hlamEq]
    exact hnorm

open scoped Classical in
/-- **Sharp-set sum transport** (subgroup-of form ↔ ambient form): for `K ≤ L`, a sum over the
nonidentity `K`-members *inside `↥L`* equals the sum over the ambient sharp `K^# ⊂ G`.  The
bridge between the (13.5)/(13.6) engines (stated inside the abstract ambient `↥S` with
`H.subgroupOf S`) and the (13.10) counting layer (stated over `sharpSubgroup K ⊂ G`). -/
theorem sum_apply_erase_one_filter_subgroupOf [Finite G] {M : Type*} [AddCommMonoid M]
    {K L : Subgroup G} [Fintype ↥L] (hKL : K ≤ L) (f : G → M) :
    ∑ x ∈ (Finset.univ.filter (· ∈ K.subgroupOf L)).erase 1, f ↑x
      = ∑ x ∈ (Set.toFinite (sharpSubgroup K)).toFinset, f x := by
  classical
  refine Finset.sum_bij' (fun x _ => (↑x : G))
    (fun y hy => (⟨y, hKL ((Set.Finite.mem_toFinset _).mp hy).1⟩ : ↥L)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx1, hxK⟩ := Finset.mem_erase.mp hx
    rw [Set.Finite.mem_toFinset]
    refine ⟨Subgroup.mem_subgroupOf.mp (Finset.mem_filter.mp hxK).2, ?_⟩
    intro h1
    rw [Set.mem_singleton_iff] at h1
    exact hx1 (Subtype.ext h1)
  · intro y hy
    obtain ⟨hyK, hy1⟩ := (Set.Finite.mem_toFinset _).mp hy
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Subgroup.mem_subgroupOf.mpr hyK⟩⟩
    intro h1
    exact hy1 (by simpa using congrArg (Subtype.val) h1)
  · intro x hx
    rfl
  · intro y hy
    rfl
  · intro x hx
    rfl

/-- **`2u ≤ |P| − 1`** (Peterfalvi (13.2.c) consequence): from the (13.2.e) bound
`u ≤ (p^q − 1)/(p − 1)` (`basic_structure`) and `p ≥ 3`, so `u ≤ (p^q−1)/2`. -/
theorem Hypothesis.two_mul_u_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : 2 * hyp.u ≤ hyp.p ^ hyp.q - 1 := by
  obtain ⟨-, -, -, -, hub, -⟩ := basic_structure hG hyp
  have hp3 := hyp.three_le_p
  have h1 : (hyp.p ^ hyp.q - 1) / (hyp.p - 1) ≤ (hyp.p ^ hyp.q - 1) / 2 :=
    Nat.div_le_div_left (by omega) (by omega)
  have h2 : (hyp.p ^ hyp.q - 1) / 2 * 2 ≤ hyp.p ^ hyp.q - 1 := Nat.div_mul_le_self _ _
  omega

open scoped Classical in
open scoped FiniteInduce in
/-- **The distinguished `λ`-index in the (7.6) family, membership half** (real): `λ = Ind_H^S θ`
(the materialized (13.3.b) field) appears at a family index (`zeta_family_cover`), at a
*positive* one (the base is pinned to `ζ₀ = Ind 1_H`, `H_sharp_zeta_zero`, which is `P`-kernel
while `λ` is not), and `P ⊄ Ker ζ_{i₁}` (kernel descent,
`mem_characterKernel_of_mem_characterKernel_induce`). -/
theorem exists_lambda_family_index [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) :
    ∃ i₁ : Fin ((H_sharp_hypothesis76 hG hyp).n + 1), 0 < i₁ ∧
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i₁)) ∧
      (H_sharp_hypothesis76 hG hyp).zeta i₁ = chars.lambda := by
  classical
  obtain ⟨θ, hθirr, hθ1, hlamEq, x₀, hx₀P, hx₀ker⟩ := chars.lambda_induced_from_PC_linear
  obtain ⟨i₁, hi₁⟩ := (H_sharp_hypothesis76 hG hyp).zeta_family_cover ⟨θ, hθirr⟩
  -- `ζ_{i₁} = Ind θ = λ` (instance bridge between the canonical and scoped `induce`s)
  have heq : (H_sharp_hypothesis76 hG hyp).zeta i₁ = chars.lambda := by
    rw [hi₁, hlamEq]
    congr! <;> exact Subsingleton.elim _ _
  -- `P ⊄ Ker ζ_{i₁}`: the witness `x₀ ∈ P ∖ Ker θ` survives kernel descent
  have hker : ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i₁)) := by
    intro hsub
    refine hx₀ker ?_
    have hx₀S : ((x₀ : ↥hyp.S)) ∈ hyp.P.subgroupOf hyp.S :=
      Subgroup.mem_subgroupOf.mpr hx₀P
    have hmem : ((x₀ : ↥hyp.S)) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) := by
      have h1 := hsub hx₀S
      rw [heq, hlamEq] at h1
      exact h1
    have hbridge := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      (L := ↥hyp.S) (H := hyp.H.subgroupOf hyp.S) hθirr x₀.2 hmem
    rwa [show (⟨((x₀ : ↥hyp.S)), x₀.2⟩ : ↥(hyp.H.subgroupOf hyp.S)) = x₀ from rfl] at hbridge
  -- positivity: `ζ₀ = Ind 1_H` is `P`-kernel, so `i₁ ≠ 0`
  refine ⟨i₁, ?_, hker, heq⟩
  rw [Fin.pos_iff_ne_zero]
  intro h0
  refine hker ?_
  rw [h0, H_sharp_zeta_zero hG hyp]
  intro y hyP
  have hyH : (y : ↥hyp.S) ∈ hyp.H.subgroupOf hyp.S := by
    have hPH : hyp.P ≤ hyp.H := le_sup_left
    exact Subgroup.mem_subgroupOf.mpr (hPH (Subgroup.mem_subgroupOf.mp hyP))
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
    OddOrder.Peterfalvi.S03.characterDegree_def,
    show ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter
        ↥(hyp.H.subgroupOf hyp.S)) : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
      = trivialClassFunction ↥(hyp.H.subgroupOf hyp.S) from rfl]
  rw [OddOrder.Peterfalvi.S09.Cert.induce_trivialChar_apply_eq_index _ hyH,
    OddOrder.Peterfalvi.S09.Cert.induce_trivialChar_apply_eq_index _
      (Subgroup.one_mem (hyp.H.subgroupOf hyp.S))]

open scoped Classical in
open scoped FiniteInduce in
/-- **The (7.7.a) coefficients of `λ^{τ₁}` at the distinguished index** (Peterfalvi (13.5),
"the hypothesis of (13.5) holds with `ζ₁ = λ`, `χ = λ^{τ₁}`, `a = 1` — since `𝒮` is coherent
and `𝒮₁ ⊂ ℤ[𝒮]`"): `c_{i₁} = ⟨τψ_{i₁}, λ^{τ₁}⟩ = 1` and every other `P`-non-kernel
coefficient vanishes.  The content is the τ₁-coherence semantics (τ₁ extends τ on family
differences + τ₁-isometry + distinct-induced orthogonality); faithful producer, gated on the
(13.3)/τ₁ fields (issue 2034 設計). -/
theorem lambda_tau1_cCoeff [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp)
    (i₁ : Fin ((H_sharp_hypothesis76 hG hyp).n + 1)) (hi₁pos : 0 < i₁)
    (hi₁eq : (H_sharp_hypothesis76 hG hyp).zeta i₁ = chars.lambda) :
    (H_sharp_hypothesis76 hG hyp).cCoeff (chars.tau1S chars.lambda) i₁ = 1 ∧
      (∀ i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)) →
        (H_sharp_hypothesis76 hG hyp).cCoeff (chars.tau1S chars.lambda) i = 0) := by
  classical
  obtain ⟨θl, hθlirr, -, hlamEq, x₀, hx₀P, hx₀ker⟩ := chars.lambda_induced_from_PC_linear
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S with hKdef
  -- the one-time spelling bridge (`(H76).H = hyp.H` definitionally)
  have hKJ : K = hyp.H.subgroupOf hyp.S := rfl
  haveI hKnorm : K.Normal := by rw [hKJ]; exact H_sharp_subgroupOf_normal hyp
  -- `K ≅ H` abelian ⟹ all family degrees are `[S:K]` ⟹ `d ≡ 1`
  haveI hKcomm : IsMulCommutative ↥K := by
    rw [hKJ]
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe (show hyp.H ≤ hyp.S from hyp.H_le_S)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  have hzeta_one : ∀ j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      (H_sharp_hypothesis76 hG hyp).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
    have hθ1 : (θ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        θ.2
    rw [hθ, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one]
  have hidx0 : (K.index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := K)
  have hd1 : ∀ j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      (H_sharp_hypothesis76 hG hyp).d j = 1 := by
    intro j
    have h := (H_sharp_hypothesis76 hG hyp).zeta_one_eq_d_mul j
    rw [hzeta_one j, hzeta_one 0] at h
    field_simp at h
    exact h.symm
  -- distinct induced characters of `K` are orthogonal
  have hInd0 : ∀ θ ψ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
          ≠ ClassFunction.induce K (ψ : ClassFunction ↥K ℂ) →
      ClassFunction.inner (ClassFunction.induce K (θ : ClassFunction ↥K ℂ))
        (ClassFunction.induce K (ψ : ClassFunction ↥K ℂ)) = 0 := by
    intro θ ψ hne
    refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj θ ψ
      (fun g heq => hne ?_)
    have h1 : ClassFunction.induce K
        ((OddOrder.RepresentationTheory.IrreducibleCharacter.conjBy g θ :
          OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) : ClassFunction ↥K ℂ)
        = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) := by
      rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy]
      exact OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq
        (G := ↥hyp.S) (H := K) g _
    rw [← h1, heq]
  -- the field-side data, transported into the `K`-spelling (syntactic via `hKJ`)
  have hθlK : ∃ θK : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      chars.lambda = ClassFunction.induce K (θK : ClassFunction ↥K ℂ) := by
    rw [hKJ]
    exact ⟨⟨θl, hθlirr⟩, hlamEq⟩
  obtain ⟨θlK, hlamK⟩ := hθlK
  have hζ0K : (H_sharp_hypothesis76 hG hyp).zeta 0
      = ClassFunction.induce K
          ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K :
            OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) :
              ClassFunction ↥K ℂ) := by
    rw [hKJ]
    exact H_sharp_zeta_zero hG hyp
  have hfield1 : ∀ θ θ' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      chars.tau1S (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
          - ClassFunction.induce K (θ' : ClassFunction ↥K ℂ))
        = ClassFunction.induce hyp.S
            (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
              - ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)) := by
    rw [hKJ]
    intro θ θ'
    have h := chars.tau1S_apply_induce_sub _ _ θ.2 θ'.2
    exact h.trans (by congr! <;> exact Subsingleton.elim _ _)
  have hfield2 : ∀ θ θ' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ClassFunction.inner (chars.tau1S (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)))
          (chars.tau1S (ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)))
        = ClassFunction.inner (ClassFunction.induce K (θ : ClassFunction ↥K ℂ))
            (ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)) := by
    rw [hKJ]
    intro θ θ'
    have h := chars.tau1S_inner_induce _ _ θ.2 θ'.2
    convert h using 1 <;> congr! <;> exact Subsingleton.elim _ _
  -- `λ ≠ ζ₀` (positivity of `i₁` + injectivity), so `⟨ζ₀, λ⟩ = 0`
  have hζi₁K : (H_sharp_hypothesis76 hG hyp).zeta i₁
      = ClassFunction.induce K (θlK : ClassFunction ↥K ℂ) := by
    rw [hi₁eq]
    exact hlamK
  have hθl_ne_triv : ClassFunction.induce K (θlK : ClassFunction ↥K ℂ)
      ≠ ClassFunction.induce K
          ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K :
            OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) :
              ClassFunction ↥K ℂ) := by
    intro heq
    have hzz : (H_sharp_hypothesis76 hG hyp).zeta i₁ = (H_sharp_hypothesis76 hG hyp).zeta 0 := by
      rw [hζi₁K, hζ0K, heq]
    exact (Fin.pos_iff_ne_zero.mp hi₁pos) ((H_sharp_hypothesis76 hG hyp).zeta_injective hzz)
  have hz0lam : ClassFunction.inner ((H_sharp_hypothesis76 hG hyp).zeta 0) chars.lambda = 0 := by
    rw [hζ0K, hlamK]
    exact hInd0 _ _ (Ne.symm hθl_ne_triv)
  -- the generic coefficient computation for a family index with known inducing character
  have hcoeff : ∀ (j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))
      (θ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K),
      (H_sharp_hypothesis76 hG hyp).zeta j = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) →
      (H_sharp_hypothesis76 hG hyp).cCoeff (chars.tau1S chars.lambda) j
        = ClassFunction.inner ((H_sharp_hypothesis76 hG hyp).zeta j) chars.lambda
          - ClassFunction.inner ((H_sharp_hypothesis76 hG hyp).zeta 0) chars.lambda := by
    intro j θ hζj
    rw [show (H_sharp_hypothesis76 hG hyp).cCoeff (chars.tau1S chars.lambda) j
        = ClassFunction.inner
            ((H_sharp_hypothesis76 hG hyp).hyp71.τ ((H_sharp_hypothesis76 hG hyp).psiSupp j))
            (chars.tau1S chars.lambda) from rfl]
    rw [show (H_sharp_hypothesis76 hG hyp).hyp71.τ = (H_sharp_hypothesis71 hG hyp).τ from rfl,
      H_sharp_tau_eq_induce hG hyp]
    have hψ : ((H_sharp_hypothesis76 hG hyp).psiSupp j : ClassFunction ↥hyp.S ℂ)
        = ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
          - ClassFunction.induce K
              ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K :
                OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) :
                  ClassFunction ↥K ℂ) := by
      rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1 j, one_smul, hζj, hζ0K]
    rw [hψ, ← hfield1 θ _, map_sub, ClassFunction.inner_sub_left, hlamK,
      hfield2 θ θlK, hfield2 _ θlK, ← hlamK, ← hζj, ← hζ0K]
  -- conjunct 1: `c_{i₁} = ⟨λ,λ⟩ − ⟨ζ₀,λ⟩ = 1 − 0`
  have hlamIrr : ClassFunction.inner chars.lambda chars.lambda = 1 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨chars.lambda, chars.lambda_irreducible⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      ⟨chars.lambda, chars.lambda_irreducible⟩
    simpa using h
  refine ⟨?_, ?_⟩
  · rw [hcoeff i₁ θlK hζi₁K, hi₁eq, hlamIrr, hz0lam, sub_zero]
  · intro i hipos hine _
    obtain ⟨θi0, hθi0⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced i
    have hθi : (H_sharp_hypothesis76 hG hyp).zeta i
        = ClassFunction.induce K (θi0 : ClassFunction ↥K ℂ) := by
      rw [hθi0]
    rw [hcoeff i θi0 hθi, hz0lam, sub_zero]
    have hne : ClassFunction.induce K (θi0 : ClassFunction ↥K ℂ)
        ≠ ClassFunction.induce K (θlK : ClassFunction ↥K ℂ) := by
      intro heq
      refine hine ((H_sharp_hypothesis76 hG hyp).zeta_injective ?_)
      rw [hθi, hζi₁K]
      exact heq
    rw [hθi, hlamK]
    exact hInd0 θi0 θlK hne

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3)/(13.5), the distinguished index of `λ`** — real assembly: the
membership half is `exists_lambda_family_index` (family cover + trivial base + kernel
descent, all proven); the coefficient half is the τ₁-coherence producer
`lambda_tau1_cCoeff`. -/
theorem exists_lambda_index [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) :
    ∃ i₁ : Fin ((H_sharp_hypothesis76 hG hyp).n + 1), 0 < i₁ ∧
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i₁)) ∧
      (H_sharp_hypothesis76 hG hyp).zeta i₁ = chars.lambda ∧
      (H_sharp_hypothesis76 hG hyp).cCoeff (chars.tau1S chars.lambda) i₁ = 1 ∧
      (∀ i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)) →
        (H_sharp_hypothesis76 hG hyp).cCoeff (chars.tau1S chars.lambda) i = 0) := by
  obtain ⟨i₁, hpos, hker, heq⟩ := exists_lambda_family_index hG chars
  obtain ⟨hc1, hmid⟩ := lambda_tau1_cCoeff hG chars i₁ hpos heq
  exact ⟨i₁, hpos, hker, heq, hc1, hmid⟩

open scoped Classical in
open scoped FiniteInduce in
/-- **`⟨Res_H λ, α⟩ = 0`** — the (13.5.a) `P`-kernel orthogonality for the `λ`-package: `λ`'s
`H`-restriction is the orbit character of the `P`-non-kernel `θ_{i₁}`, while `α` is supported
on `P`-kernel orbit characters; distinct orbits are orthogonal.  Real-provable from the orbit
machinery (distinct induced ⟹ disjoint orbits ⟹ orthogonal restrictions); kept as a named
producer pending the orbit-orthogonality lemma. -/
theorem lambda_alphaFun_inner_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) :
    (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
      chars.lambda x * (starRingEnd ℂ)
        (H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) x)) = 0 := by
  classical
  obtain ⟨i₁, -, hi₁ker, hi₁eq, -, -⟩ := exists_lambda_index hG chars
  -- `λ = ζ_{i₁}` vanishes off `H`, so the filtered sum extends to the full `↥S`-sum.
  have hvanish : ∀ x : ↥hyp.S, x ∉ hyp.H.subgroupOf hyp.S → chars.lambda x = 0 := by
    intro x hx
    rw [← hi₁eq]
    exact (H_sharp_hypothesis76 hG hyp).zeta_eq_zero_of_not_mem_H i₁ x
      (fun hmem => hx (Subgroup.mem_subgroupOf.mpr hmem))
  have hext : (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
      chars.lambda x * (starRingEnd ℂ)
        (H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) x))
      = ∑ x : ↥hyp.S, chars.lambda x * (starRingEnd ℂ)
          (H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) x) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ hyp.H.subgroupOf hyp.S)
      (fun x => chars.lambda x * (starRingEnd ℂ)
        (H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) x))]
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ hyp.H.subgroupOf hyp.S),
        chars.lambda x * (starRingEnd ℂ)
          (H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) x) = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      rw [hvanish x (Finset.mem_filter.mp hx).2, zero_mul]
    rw [h0, add_zero]
  rw [hext]
  -- The full sum is `|S|·⟨λ, α⟩`, and `⟨λ, α⟩ = 0` term by term.
  have hsum : ∑ x : ↥hyp.S, chars.lambda x * (starRingEnd ℂ)
      (H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) x)
      = ClassFunction.innerSum chars.lambda (H_sharp_alphaCF hG hyp (chars.tau1S chars.lambda)) := by
    rw [ClassFunction.innerSum]
    exact Finset.sum_congr rfl (fun x _ => by
      rw [H_sharp_alphaCF_apply, starRingEnd_apply])
  rw [hsum, ← ClassFunction.card_mul_inner]
  -- `⟨λ, α⟩ = Σ_j coeff·⟨ζ_{i₁}, ζ_j⟩ = 0` (distinct-fibre induced are orthogonal).
  have hinner0 : ClassFunction.inner chars.lambda
      (H_sharp_alphaCF hG hyp (chars.tau1S chars.lambda)) = 0 := by
    rw [H_sharp_alphaCF, inner_sum_right]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [OddOrder.RepresentationTheory.inner_smul_right]
    have hjker := (Finset.mem_filter.mp hj).2
    -- `ζ_{i₁} ≠ ζ_j` (`P`-kernel property differs), both induced ⟹ orthogonal.
    have hzne : (H_sharp_hypothesis76 hG hyp).zeta i₁ ≠ (H_sharp_hypothesis76 hG hyp).zeta j :=
      fun heq => hi₁ker (heq ▸ hjker)
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced i₁
    obtain ⟨θ', hθ'⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
    haveI : ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S).Normal :=
      H_sharp_subgroupOf_normal hyp
    have hz0 : ClassFunction.inner ((H_sharp_hypothesis76 hG hyp).zeta i₁)
        ((H_sharp_hypothesis76 hG hyp).zeta j) = 0 := by
      rw [hθ, hθ']
      refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj θ θ'
        (fun g hconj => ?_)
      refine hzne ?_
      rw [hθ, hθ', ← hconj, OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy,
        OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq]
    rw [← hi₁eq, hz0, mul_zero]
  rw [hinner0, mul_zero]

open scoped Classical in
open scoped FiniteInduce in
/-- **`λ` vanishes on the mixed products `W₂·W₁^#`** (Peterfalvi (13.6) proof, "`λ(xy) = 0`"):
`λ = ζ_{i₁}` is a member of the (7.6) family induced from `H` (`exists_lambda_index`), the
family vanishes off `H` (`zeta_eq_zero_of_not_mem_H`), and `x·y ∉ H` — `q` divides
`orderOf (x·y) = orderOf x · q` (commuting factors of coprime prime orders) while `q ∤ |H|`
(`q_not_dvd_card_H`). -/
theorem lambda_apply_mul_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp)
    {x y : G} (hx : x ∈ hyp.W2) (hy : y ∈ hyp.W1) (hy1 : y ≠ 1)
    (hxyS : x * y ∈ hyp.S) :
    chars.lambda ⟨x * y, hxyS⟩ = 0 := by
  obtain ⟨i₁, -, -, hi₁eq, -, -⟩ := exists_lambda_index hG chars
  rw [← hi₁eq]
  refine (H_sharp_hypothesis76 hG hyp).zeta_eq_zero_of_not_mem_H i₁ _ (fun hmem => ?_)
  have hmem' : x * y ∈ hyp.H := by
    rwa [show (H_sharp_hypothesis76 hG hyp).H = hyp.H from rfl] at hmem
  -- `orderOf y = q`
  have hyq : orderOf y = hyp.q := by
    have h2 : orderOf y = orderOf (⟨y, hy⟩ : ↥hyp.W1) :=
      orderOf_injective hyp.W1.subtype Subtype.coe_injective ⟨y, hy⟩
    have h1 : orderOf (⟨y, hy⟩ : ↥hyp.W1) ∣ hyp.q := by
      rw [hyp.q_eq_card_W1]; exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hyp.q_prime).mp h1 with h | h
    · exact absurd (congrArg Subtype.val (orderOf_eq_one_iff.mp h)) hy1
    · rw [h2, h]
  -- `orderOf x ∣ p`
  have hxord : orderOf x ∣ hyp.p := by
    have h2 : orderOf x = orderOf (⟨x, hx⟩ : ↥hyp.W2) :=
      orderOf_injective hyp.W2.subtype Subtype.coe_injective ⟨x, hx⟩
    rw [h2, hyp.p_eq_card_W2]
    exact orderOf_dvd_natCard _
  -- `q ∣ orderOf (x·y)`
  have hcomm : Commute y x := hyp.W1_commutes_W2 y hy x hx
  have hcop : Nat.Coprime (orderOf y) (orderOf x) := by
    rw [hyq]
    exact Nat.Coprime.coprime_dvd_right hxord
      ((Nat.coprime_primes hyp.q_prime hyp.p_prime).mpr (Ne.symm (hyp.p_ne_q)))
  have hqdvd : hyp.q ∣ orderOf (x * y) := by
    rw [show x * y = y * x from hcomm.eq.symm,
      hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hyq]
    exact dvd_mul_right _ _
  -- ... but every `H`-element has order prime to `q`
  have hdvdH : orderOf (x * y) ∣ Nat.card ↥hyp.H := by
    have h2 : orderOf (x * y) = orderOf (⟨x * y, hmem'⟩ : ↥hyp.H) :=
      orderOf_injective hyp.H.subtype Subtype.coe_injective ⟨x * y, hmem'⟩
    rw [h2]; exact orderOf_dvd_natCard _
  exact hyp.q_not_dvd_card_H hG (hqdvd.trans hdvdH)

open scoped FiniteInduce in
/-- **Peterfalvi (3.2.d)** (hypothesis-level): a class function of `G` orthogonal to the whole
`η`-grid vanishes on the regular set `Ŵ = W ∖ (W₁ ∪ W₂)` — every irreducible of `G` off the
`σ`-image vanishes on `Ŵ`, and the `η_{ij} = ω_{ij}^{τ₃}` enumerate the image.  Faithful
producer; the honest supply is `S05.eq_zero_of_mem_V_of_inner_chiFam_eq_zero` (proven) through
the spine's `ω`-grid ↔ character-pair identification (`gridEquivE`/`omegaProdChar` — the
issue-2033 threading pattern; the grid here is `Fin q × Fin p`-indexed while the S05 family is
hom-pair-indexed, and the enumerations correspond along `w1CharEquiv`/`chi2enum`). -/
theorem Hypothesis.vanish_of_inner_eta_eq_zero [Finite G] (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ)
    (horth : ∀ (i : Fin hyp.q) (j : Fin hyp.p), ClassFunction.inner (hyp.eta i j) χ = 0)
    {w : G} (hwW : w ∈ hyp.W) (hnot : w ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G)) :
    χ w = 0 := by
  refine hyp.eta_complete_vanish χ (fun i j => ?_) w hwW hnot
  rw [← hyp.eta_eq_tau_omega]
  exact horth i j

open scoped Classical in
open scoped FiniteInduce in
/-- **`λ^{τ₁}` vanishes on the mixed products `W₂^#·W₁^#`** (Peterfalvi (13.6) proof, "by
(3.2.d), (5.3.b) and (5.5), `λ^{τ₁}(xy) = 0`"): the coherence extension `τ₁` sends `ℤ[𝒮]`
to class functions whose values on the regular section `xy ∈ Ŵ` are controlled by the
`η`-grid, and `λ^{τ₁}` has no `η`-component there.  Faithful producer; gated on the
(13.2.d)/(5.3.b)/(5.5) coherence-support analysis (the same (13.3)-cluster gate as
`exists_lambda_index`). -/
theorem lambda_tau1_apply_mul_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp)
    {x y : G} (hx : x ∈ hyp.W2) (hy : y ∈ hyp.W1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    chars.tau1S chars.lambda (x * y) = 0 := by
  obtain ⟨θl, hθlirr, -, hlamEq, -⟩ := chars.lambda_induced_from_PC_linear
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hW2W : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  have hcomm : Commute y x := hyp.W1_commutes_W2 y hy x hx
  have hnot : x * y ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G) := by
    rw [show x * y = y * x from hcomm.eq.symm]
    exact hyp.mul_notMem_W1_union_W2 hy hx hy1 hx1
  refine hyp.vanish_of_inner_eta_eq_zero (chars.tau1S chars.lambda) (fun i j => ?_)
    (mul_mem (hW2W hx) (hW1W hy)) hnot
  rw [hlamEq]
  exact chars.tau1S_induce_inner_eta i j θl hθlirr

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (7.7.a) coefficients of any virtual character are integers** (general form; cf.
Peterfalvi (13.5) "`α(1) = qb` with `b` an integer"): `c_i = ⟨τψ_i, χ⟩` with both arguments
virtual characters — `ψ_i = ζ_i − d_i ζ_0` has `d_i = 1` (all degrees are `[S:K]` since
`K ≅ H` is abelian) and the Dade image `τψ_i ∈ ℤ[Irr G]` ((2.10)
`preserves_virtualCharacters`). -/
theorem H_sharp_cCoeff_int [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {χ : ClassFunction G ℂ} (hχ : χ ∈ ZIrr G) :
    ∀ i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      ∃ z : ℤ, (H_sharp_hypothesis76 hG hyp).cCoeff χ i = (z : ℂ) := by
  classical
  intro i
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S with hKdef
  haveI hKnorm : K.Normal := H_sharp_subgroupOf_normal hyp
  -- `K ≅ H` is abelian, so every `θ_j` is linear and all `ζ_j` have degree `[S:K]`.
  have hHS : hyp.H ≤ hyp.S := by
    have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    show hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]; exact le_trans inf_le_left hUS
  haveI hKcomm : IsMulCommutative ↥K := by
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe
      (show (H_sharp_hypothesis76 hG hyp).H ≤ hyp.S from hHS)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  -- Degrees: `ζ_j(1) = [S:K]` for every `j`, so the degree ratio is `1`.
  have hzeta_one : ∀ j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      (H_sharp_hypothesis76 hG hyp).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
    have hθ1 : (θ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        θ.2
    rw [hθ, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one]
  have hidx0 : (K.index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := K)
  have hd1 : (H_sharp_hypothesis76 hG hyp).d i = 1 := by
    have h := (H_sharp_hypothesis76 hG hyp).zeta_one_eq_d_mul i
    rw [hzeta_one i, hzeta_one 0] at h
    field_simp at h
    exact h.symm
  -- `ψ_i = ζ_i − ζ_0 ∈ ℤ[Irr S]`.
  have hzetaZ : ∀ j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      (H_sharp_hypothesis76 hG hyp).zeta j ∈ ZIrr ↥hyp.S := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
    rw [hθ]
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr K (θ.2.mem_ZIrr)
  have hψZ : ((H_sharp_hypothesis76 hG hyp).psiSupp i : ClassFunction ↥hyp.S ℂ)
      ∈ ZIrr ↥hyp.S := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1, one_smul]
    exact Submodule.sub_mem _ (hzetaZ i) (hzetaZ 0)
  -- The Dade image is a virtual character ((2.10) `preserves_virtualCharacters`).
  have hτeq : (H_sharp_hypothesis76 hG hyp).hyp71.τ
      = ((H_sharp_dadeHypothesis hG hyp).fullDadeIsometryData
          (H_sharp_hconj hG hyp)).toDadeIsometryData.toDadeMap := rfl
  have hpres : (H_sharp_hypothesis76 hG hyp).hyp71.τ
      ((H_sharp_hypothesis76 hG hyp).psiSupp i) ∈ ZIrr G := by
    rw [hτeq]
    exact ((H_sharp_dadeHypothesis hG hyp).fullDadeIsometryData
      (H_sharp_hconj hG hyp)).preserves_virtualCharacters _ hψZ
  -- `c_i = ⟨τψ_i, η₁₀⟩ ∈ ℤ`.
  rw [OddOrder.Peterfalvi.S09.Hypothesis76.cCoeff]
  exact ClassFunction.inner_mem_ZIrr_int hpres hχ


open scoped Classical in
open scoped FiniteInduce in
/-- **`α(1) ∈ ℤ` for the `λ`-package** (the (13.5) framing "`α(1) = qb` with `b` an integer",
integrality half): `α(1) = ∑_{P ⊆ ker ζᵢ} c̄ᵢ·ζᵢ(1)/‖ζᵢ‖²` with `cᵢ = ⟨τψᵢ, λ^{τ₁}⟩ ∈ ℤ`
(both virtual characters — `λ^{τ₁} ∈ ℤ[Irr G]` is `lambda_tau1_norm_one.1`, the `τψᵢ`
via `preserves_virtualCharacters` as in `eta10_cCoeff_int`) and `ζᵢ(1)/‖ζᵢ‖² = [S : I_S(θᵢ)]`
(the inertia-index identity `card_mul_inner_self_induce_eq_card_inertia` /
`card_smul_restrict_induce_eq_inertia_smul_orbitSum`).  Faithful producer; assembly pending
the per-index inertia bookkeeping. -/
theorem lambda_alphaFun_one_int [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) :
    ∃ m : ℤ, H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) 1 = (m : ℂ) := by
  classical
  obtain ⟨hZtau, -, -⟩ := lambda_tau1_norm_one hG chars
  have hcInt := H_sharp_cCoeff_int hG hyp hZtau
  -- `K = H.subgroupOf S` is abelian normal, so `ζ_j(1) = [S:K]` for every `j`
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S with hKdef
  haveI hKnorm : K.Normal := H_sharp_subgroupOf_normal hyp
  have hHS : hyp.H ≤ hyp.S := by
    have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    show hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]; exact le_trans inf_le_left hUS
  haveI hKcomm : IsMulCommutative ↥K := by
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe
      (show (H_sharp_hypothesis76 hG hyp).H ≤ hyp.S from hHS)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  have hzeta_one : ∀ j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      (H_sharp_hypothesis76 hG hyp).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
    have hθ1 : (θ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        θ.2
    rw [hθ, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one]
  -- the degree/norm ratio is the inertia index: `ζ_j(1)/‖ζ_j‖² = [S : I_S(θ_j)]`
  have hratio : ∀ j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      ∃ N : ℕ, (H_sharp_hypothesis76 hG hyp).zeta j 1
          / (H_sharp_hypothesis76 hG hyp).zetaNormSq j = (N : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
    refine ⟨(ClassFunction.inertia (θ : ClassFunction ↥K ℂ)).index, ?_⟩
    have hK0 : (Nat.card ↥K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hI0 : (Nat.card ↥(ClassFunction.inertia (θ : ClassFunction ↥K ℂ)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    -- inertia: `|K|·‖ζ_j‖² = |I|`
    have hns : (Nat.card ↥K : ℂ) * (H_sharp_hypothesis76 hG hyp).zetaNormSq j
        = (Nat.card ↥(ClassFunction.inertia (θ : ClassFunction ↥K ℂ)) : ℂ) := by
      rw [show (H_sharp_hypothesis76 hG hyp).zetaNormSq j
        = ClassFunction.inner ((H_sharp_hypothesis76 hG hyp).zeta j)
          ((H_sharp_hypothesis76 hG hyp).zeta j) from rfl, hθ]
      exact OddOrder.RepresentationTheory.card_mul_inner_self_induce_eq_card_inertia θ
    -- Lagrange twice: `|K|·[S:K] = |S| = |I|·[S:I]`
    have hKS : (Nat.card ↥K : ℂ) * (K.index : ℂ) = (Nat.card ↥hyp.S : ℂ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) (Subgroup.card_mul_index K)
    have hIS : (Nat.card ↥(ClassFunction.inertia (θ : ClassFunction ↥K ℂ)) : ℂ)
        * ((ClassFunction.inertia (θ : ClassFunction ↥K ℂ)).index : ℂ)
        = (Nat.card ↥hyp.S : ℂ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℂ)
        (Subgroup.card_mul_index (ClassFunction.inertia (θ : ClassFunction ↥K ℂ)))
    have hns0 : (H_sharp_hypothesis76 hG hyp).zetaNormSq j ≠ 0 := by
      intro h
      rw [h, mul_zero] at hns
      exact hI0 hns.symm
    rw [hzeta_one j, div_eq_iff hns0]
    have hmul : (Nat.card ↥K : ℂ) * (K.index : ℂ)
        = (Nat.card ↥K : ℂ)
          * (((ClassFunction.inertia (θ : ClassFunction ↥K ℂ)).index : ℂ)
              * (H_sharp_hypothesis76 hG hyp).zetaNormSq j) := by
      rw [hKS]
      calc (Nat.card ↥hyp.S : ℂ)
          = (Nat.card ↥(ClassFunction.inertia (θ : ClassFunction ↥K ℂ)) : ℂ)
            * ((ClassFunction.inertia (θ : ClassFunction ↥K ℂ)).index : ℂ) := hIS.symm
        _ = _ := by rw [← hns]; ring
    exact mul_left_cancel₀ hK0 hmul
  -- assemble: every `P`-kernel tail term is an integer, so the sum is
  have hmem : H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) 1
      ∈ (Int.castRingHom ℂ).range := by
    simp only [H_sharp_alphaFun]
    refine Subring.sum_mem _ (fun i _ => ?_)
    obtain ⟨z, hz⟩ := hcInt i
    obtain ⟨N, hN⟩ := hratio i
    refine ⟨z * N, ?_⟩
    show ((z * N : ℤ) : ℂ) = _
    push_cast
    rw [hz, star_intCast, div_mul_eq_mul_div, mul_div_assoc, hN]
  obtain ⟨m, hm⟩ := hmem
  exact ⟨m, hm.symm⟩

open scoped Classical in
open scoped FiniteInduce in
/-- **`α(1) ≡ 0 (mod q)` for the `λ`-package** (Peterfalvi (13.6) proof, the (1.10) congruence):
`λ(x) ≡ λ^{τ₁}(x) ≡ 0 (mod 1−ε)` on `W₂^#`, so `α(1) = α(x) = λ^{τ₁}(x) − λ(x) ≡ 0 (mod q)`.
Faithful producer; gated on the (1.10)/(3.2) grid congruences. -/
theorem exists_lambda_alphaFun_one_qb [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) :
    ∃ b : ℤ, H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) 1
      = (hyp.q : ℂ) * (b : ℂ) := by
  classical
  -- `α(1) = m ∈ ℤ` (integrality producer)
  obtain ⟨m, hm⟩ := lambda_alphaFun_one_int hG chars
  -- the distinguished index and the norm normalizations
  obtain ⟨i₁, hi₁pos, hi₁ker, hi₁eq, hi₁c, hmiddle⟩ := exists_lambda_index hG chars
  obtain ⟨hZtau, -, hnormLam⟩ := lambda_tau1_norm_one hG chars
  -- pick `x ∈ W₂^#`, `y ∈ W₁^#`
  obtain ⟨x', hx'⟩ : ∃ x' : ↥hyp.W2, x' ≠ 1 := by
    haveI : Nontrivial ↥hyp.W2 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.p_eq_card_W2]; exact hyp.p_prime.one_lt)
    exact exists_ne 1
  obtain ⟨y', hy'⟩ : ∃ y' : ↥hyp.W1, y' ≠ 1 := by
    haveI : Nontrivial ↥hyp.W1 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.q_eq_card_W1]; exact hyp.q_prime.one_lt)
    exact exists_ne 1
  have hxW2 : (x' : G) ∈ hyp.W2 := x'.2
  have hyW1 : (y' : G) ∈ hyp.W1 := y'.2
  have hx1 : (x' : G) ≠ 1 := fun h => hx' (Subtype.ext h)
  have hy1 : (y' : G) ≠ 1 := fun h => hy' (Subtype.ext h)
  -- memberships: `x ∈ P ≤ H ≤ S`, `y ∈ W₁ ≤ W ≤ S`
  have hxP : (x' : G) ∈ hyp.P := W2_le_P hG hyp hxW2
  have hPS : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hxS : (x' : G) ∈ hyp.S := hPS hxP
  have hxH : (x' : G) ∈ hyp.H := (le_sup_left : hyp.P ≤ hyp.H) hxP
  have hWS : hyp.W ≤ hyp.S := by rw [hyp.W_eq_inter]; exact inf_le_left
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hyS : (y' : G) ∈ hyp.S := hWS (hW1W hyW1)
  -- the point formula at `x`: `λ^{τ₁}(x) = λ(x) + α(x)` (with `c₁ = 1`, `‖ζ₁‖² = 1`)
  have hns : (H_sharp_hypothesis76 hG hyp).zetaNormSq i₁ = 1 := by
    rw [show (H_sharp_hypothesis76 hG hyp).zetaNormSq i₁
      = ClassFunction.inner ((H_sharp_hypothesis76 hG hyp).zeta i₁)
        ((H_sharp_hypothesis76 hG hyp).zeta i₁) from rfl, hi₁eq]
    exact hnormLam
  have hpf : chars.tau1S chars.lambda ((x' : G))
      = chars.lambda ⟨(x' : G), hxS⟩
        + H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) ⟨(x' : G), hxS⟩ := by
    have h := H_sharp_point_formula hG hyp (chars.tau1S chars.lambda) i₁ hi₁pos hi₁ker
      hmiddle ⟨(x' : G), hxS⟩
      (by rw [OddOrder.Peterfalvi.S04.mem_sharp]; exact ⟨hxH, hx1⟩)
    rwa [hi₁c, hns, star_one, div_one, one_mul, hi₁eq] at h
  -- `λ = ζ_{i₁} ∈ ℤ[Irr ↥S]` (for the `↥S`-level (1.10.a))
  have hZlam : chars.lambda ∈ ZIrr ↥hyp.S := by
    rw [← hi₁eq]
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced i₁
    rw [hθ]
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr _ (θ.2.mem_ZIrr)
  -- the primitive `q`-th root and the two (1.10.a) congruences at `x` vs `yx`
  have hε : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / hyp.q)) hyp.q :=
    Complex.isPrimitiveRoot_exp hyp.q hyp.q_prime.pos.ne'
  set ε : ℂ := Complex.exp (2 * Real.pi * Complex.I / hyp.q) with hεdef
  have hyq : (y' : G) ^ hyp.q = 1 := by
    have h1 : y' ^ hyp.q = 1 := by
      rw [hyp.q_eq_card_W1]; exact pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
  have hcommG : Commute ((y' : G)) ((x' : G)) := hyp.W1_commutes_W2 _ hyW1 _ hxW2
  -- τ₁-side (`G`-level): `λ^{τ₁}(x) = λ^{τ₁}(yx) − (1−ε)z₂ = −(1−ε)z₂`
  obtain ⟨z₂, hz₂int, hz₂⟩ :=
    OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute hyp.q_prime.pos hε
      hZtau hyq hcommG
  have htau0 : chars.tau1S chars.lambda ((y' : G) * (x' : G)) = 0 := by
    rw [hcommG.eq]
    exact lambda_tau1_apply_mul_eq_zero hG chars hxW2 hyW1 hx1 hy1
  -- λ-side (`↥S`-level): `λ(x) = λ(yx) − (1−ε)z₁ = −(1−ε)z₁`
  have hyqS : (⟨(y' : G), hyS⟩ : ↥hyp.S) ^ hyp.q = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hyq
  have hcommS : Commute (⟨(y' : G), hyS⟩ : ↥hyp.S) (⟨(x' : G), hxS⟩ : ↥hyp.S) :=
    Subtype.ext hcommG.eq
  obtain ⟨z₁, hz₁int, hz₁⟩ :=
    OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute hyp.q_prime.pos hε
      hZlam hyqS hcommS
  have hlam0 : chars.lambda ((⟨(y' : G), hyS⟩ : ↥hyp.S) * ⟨(x' : G), hxS⟩) = 0 := by
    have hmulS : ((⟨(y' : G), hyS⟩ : ↥hyp.S) * ⟨(x' : G), hxS⟩ : ↥hyp.S)
        = ⟨(x' : G) * (y' : G), mul_mem hxS hyS⟩ := Subtype.ext hcommG.eq
    rw [hmulS]
    exact lambda_apply_mul_eq_zero hG chars hxW2 hyW1 hy1 _
  -- combine: `α(1) = α(x) = λ^{τ₁}(x) − λ(x) = (1−ε)(z₁ − z₂)`
  have hconst := H_sharp_alphaFun_const_on_P hG hyp (chars.tau1S chars.lambda)
    ⟨(x' : G), hxS⟩ (Subgroup.mem_subgroupOf.mpr hxP)
  have hcast : ((m : ℤ) : ℂ) = (1 - ε) * (z₁ - z₂) := by
    rw [htau0, zero_sub] at hz₂
    rw [hlam0, zero_sub] at hz₁
    have e1 : chars.tau1S chars.lambda ((x' : G)) = -((1 - ε) * z₂) := by
      linear_combination -hz₂
    have e2 : chars.lambda ⟨(x' : G), hxS⟩ = -((1 - ε) * z₁) := by
      linear_combination -hz₁
    have e3 : H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) ⟨(x' : G), hxS⟩
        = (1 - ε) * (z₁ - z₂) := by
      have e4 := hpf
      rw [e1, e2] at e4
      linear_combination -e4
    rw [← hm, ← hconst, e3]
  -- (1.10.b): `q ∣ m`
  have hdvd : (hyp.q : ℤ) ∣ m :=
    OddOrder.RepresentationTheory.int_dvd_of_one_sub_primRoot_dvd hyp.q_prime hε
      (hz₁int.sub hz₂int) hcast
  obtain ⟨b, hb⟩ := hdvd
  refine ⟨b, ?_⟩
  rw [hm, hb]
  push_cast
  ring

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5.a)+(13.5.c) for `ζ₁ = λ`, `χ = λ^{τ₁}`, `a = 1`** — the correction datum
of the (13.6) estimate.

**Real assembly** from the distinguished-index atom (`exists_lambda_index`): with
`ζ_{i₁} = λ`, `c_{i₁} = 1`, and `‖ζ_{i₁}‖² = ⟨λ,λ⟩ = 1` (`lambda_tau1_norm_one`), the proven
point formula `H_sharp_point_formula` collapses to `λ^{τ₁} = λ + α` on `H^#` with
`α = H_sharp_alphaFun` the `P`-kernel tail; `λ` vanishes off `H` (`zeta_eq_zero_of_not_mem_H`);
the inner-product and congruence facts are the named producers
(`lambda_alphaFun_inner_zero` / `exists_lambda_alphaFun_one_qb`); the (13.5.c) inflation is
`H_sharp_alphaFun_inflation`. -/
theorem exists_caseB_data_lambda [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (chars : CharacterDegreeData hyp) :
    ∃ (α : ↥hyp.S → ℂ) (b : ℤ),
      (∀ x : ↥hyp.S, x ∉ hyp.H.subgroupOf hyp.S → chars.lambda x = 0) ∧
      (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
        chars.lambda x * (starRingEnd ℂ) (α x)) = 0 ∧
      (∀ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
        chars.tau1S chars.lambda ↑x = chars.lambda x + α x) ∧
      α 1 = (hyp.q : ℂ) * (b : ℂ) ∧
      ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * ((hyp.q : ℝ) * (b : ℝ)) ^ 2
        ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1, ‖α x‖ ^ 2 := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨i₁, hi₁pos, hi₁ker, hi₁eq, hi₁c, hmiddle⟩ := exists_lambda_index _hG chars
  obtain ⟨-, -, hinnerLam⟩ := lambda_tau1_norm_one _hG chars
  obtain ⟨b, hb⟩ := exists_lambda_alphaFun_one_qb _hG chars
  refine ⟨H_sharp_alphaFun _hG hyp (chars.tau1S chars.lambda), b, ?_, ?_, ?_, hb, ?_⟩
  · -- `λ = ζ_{i₁}` vanishes off `H`.
    intro x hx
    rw [← hi₁eq]
    exact (H_sharp_hypothesis76 _hG hyp).zeta_eq_zero_of_not_mem_H i₁ x
      (fun hmem => hx (Subgroup.mem_subgroupOf.mpr hmem))
  · exact lambda_alphaFun_inner_zero _hG chars
  · -- The point formula collapses: `c̄_{i₁}/‖ζ_{i₁}‖² = 1` and `ζ_{i₁} = λ`.
    intro x hx
    obtain ⟨hx1, hxmem⟩ := Finset.mem_erase.mp hx
    have hxH : (↑x : G) ∈ hyp.H :=
      Subgroup.mem_subgroupOf.mp (Finset.mem_filter.mp hxmem).2
    have hxsharp : (↑x : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) := by
      refine OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hxH, ?_⟩
      intro h1
      exact hx1 (Subtype.ext h1)
    have hpt := H_sharp_point_formula _hG hyp (chars.tau1S chars.lambda) i₁ hi₁pos hi₁ker
      hmiddle x hxsharp
    rw [hpt, hi₁c]
    have hnorm1 : (H_sharp_hypothesis76 _hG hyp).zetaNormSq i₁ = 1 := by
      rw [OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq, hi₁eq]
      exact hinnerLam
    rw [hnorm1, hi₁eq, star_one, div_one, one_mul]
    rfl
  · -- (13.5.c): the inflation bound for the concrete tail, with `α(1) = qb`.
    have hinfl := H_sharp_alphaFun_inflation _hG hyp (chars.tau1S chars.lambda)
    rw [hb] at hinfl
    have hval : ‖(hyp.q : ℂ) * (b : ℂ)‖ ^ 2 = ((hyp.q : ℝ) * (b : ℝ)) ^ 2 := by
      rw [norm_mul, mul_pow, Complex.norm_natCast, Complex.norm_intCast, sq_abs]
      push_cast
      ring
    rw [hval] at hinfl
    exact hinfl

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.6), textbook form**: `∑_{x∈H^#}|λ^{τ₁}(x)|² ≥ |S| − λ(1)²` (`λ(1) = uq`),
as a sum over the ambient sharp `H^# ⊂ G`.

**Real assembly** through the (13.5) engine `caseB_lambda_norm_bound` (inside `↥S`, with
`H.subgroupOf S`): the character-theoretic inputs are the (13.5)-for-`λ` package
(`exists_caseB_data_lambda`), the norm facts (`lambda_tau1_norm_one`: `‖λ‖² = 1` gives the
`S`-Parseval `∑_S|λ|² = |S|`), the degree `λ(1) = uq` (`lambda_degree`), and the `u`-bound
`2u ≤ |P| − 1 = p^q − 1` (`two_mul_u_le`, real from (13.2.e)); the engine output transports to
the ambient sharp by `sum_apply_erase_one_filter_subgroupOf`. -/
theorem lambda_tau1_sharp_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (chars : CharacterDegreeData hyp) :
    (Nat.card ↥hyp.S : ℝ) - ((hyp.u * hyp.q : ℕ) : ℝ) ^ 2
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset,
          ‖chars.tau1S chars.lambda x‖ ^ 2 := by
  classical
  obtain ⟨α, b, hvanish, hinner, hχ, hα1, hinfl⟩ := exists_caseB_data_lambda _hG chars
  obtain ⟨-, -, hinnerLam⟩ := lambda_tau1_norm_one _hG chars
  -- `H ≤ S`.
  have hUS : hyp.U ≤ hyp.S := by
    have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
    exact le_trans h1 (Subgroup.map_subtype_le _)
  have hHS : hyp.H ≤ hyp.S := by
    show hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]; exact le_trans inf_le_left hUS
  -- The `S`-Parseval total: `∑_{x:S}‖λ(x)‖² = |S|`.
  have hT : ∑ x : ↥hyp.S, ‖chars.lambda x‖ ^ 2 = ((Nat.card ↥hyp.S : ℕ) : ℝ) := by
    have h := sum_normSq_eq_card_mul_inner (H := ↥hyp.S) chars.lambda
    rw [hinnerLam, mul_one] at h
    exact_mod_cast h
  -- Degree facts.
  have hlamOne : chars.lambda 1 = ((hyp.u * hyp.q : ℕ) : ℂ) := chars.lambda_degree
  have hzetaOne : ‖chars.lambda 1‖ ^ 2 = (((hyp.u * hyp.q : ℕ) : ℝ)) ^ 2 := by
    rw [hlamOne, Complex.norm_natCast]
  have hcross : (chars.lambda 1 * (starRingEnd ℂ) (α 1)).re
      = ((hyp.u * hyp.q : ℕ) : ℝ) * ((hyp.q : ℝ) * (b : ℝ)) := by
    have hval : chars.lambda 1 * (starRingEnd ℂ) (α 1)
        = ((((hyp.u * hyp.q : ℕ) : ℝ) * ((hyp.q : ℝ) * (b : ℝ)) : ℝ) : ℂ) := by
      rw [hlamOne, hα1, map_mul]
      push_cast [map_natCast, map_intCast]
      ring
    rw [hval, Complex.ofReal_re]
  have hlam1 : ((hyp.u * hyp.q : ℕ) : ℝ) = (hyp.u : ℝ) * (hyp.q : ℝ) := by push_cast; ring
  -- The engine.
  have hu := hyp.two_mul_u_le _hG
  -- The engine (bridging the `Classical` decidability instances baked into its statement).
  have hengine : (Nat.card ↥hyp.S : ℝ) - ((hyp.u * hyp.q : ℕ) : ℝ) ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
          ‖chars.tau1S chars.lambda ↑x‖ ^ 2 := by
    have h := caseB_lambda_norm_bound (S := ↥hyp.S) (hyp.H.subgroupOf hyp.S)
      (fun x => chars.lambda x) α (fun x => chars.tau1S chars.lambda ↑x)
      (Scard := Nat.card ↥hyp.S) (Pm1 := hyp.p ^ hyp.q - 1)
      (u := hyp.u) (q := hyp.q) (lam1 := ((hyp.u * hyp.q : ℕ) : ℝ)) (b := b)
      hvanish (by convert hinner using 2 <;> congr!)
      (fun x hx => hχ x (by convert hx using 2 <;> congr!))
      hT hzetaOne hcross hlam1
      (by convert hinfl using 2 <;> congr!) hu
    convert h using 2 <;> congr!
  -- Transport to the ambient sharp set.
  rwa [sum_apply_erase_one_filter_subgroupOf hHS
    (fun y => ‖chars.tau1S chars.lambda y‖ ^ 2)] at hengine

open scoped Classical in
/-- `F`-parameterized form of `sum_filter_erase_one_normSq_eq` (instance-free interface): any
`Finset` with the sharp-membership characterization works. -/
theorem sum_finset_sharp_normSq_eq {L : Type*} [Group L] [Fintype L]
    {K : Subgroup L} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (F : Finset L) (hF : ∀ x : L, x ∈ F ↔ (x ∈ K ∧ x ≠ 1))
    (f : L → ℂ) (ψ : ClassFunction ↥K ℂ) (hagree : ∀ k : ↥K, f ↑k = ψ k)
    {n : ℕ} (hn : ClassFunction.inner ψ ψ = (n : ℂ)) :
    ∑ x ∈ F, ‖f x‖ ^ 2 = (Nat.card ↥K : ℝ) * (n : ℝ) - ‖f 1‖ ^ 2 := by
  classical
  have hFeq : F = (Finset.univ.filter (· ∈ K)).erase 1 := by
    ext x
    rw [hF, Finset.mem_erase, Finset.mem_filter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  rw [hFeq]
  exact sum_filter_erase_one_normSq_eq f ψ hagree hn

open scoped Classical in
/-- `F`-parameterized form of `sum_apply_erase_one_filter_subgroupOf` (instance-free
interface). -/
theorem sum_finset_sharp_transport [Finite G] {M : Type*} [AddCommMonoid M]
    {K L : Subgroup G} [Fintype ↥L] (hKL : K ≤ L)
    (F : Finset ↥L) (hF : ∀ x : ↥L, x ∈ F ↔ ((x : G) ∈ K ∧ x ≠ 1))
    (f : G → M) :
    ∑ x ∈ F, f ↑x = ∑ x ∈ (Set.toFinite (sharpSubgroup K)).toFinset, f x := by
  classical
  have hFeq : F = (Finset.univ.filter (· ∈ K.subgroupOf L)).erase 1 := by
    ext x
    rw [hF, Finset.mem_erase, Finset.mem_filter, Subgroup.mem_subgroupOf]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  rw [hFeq]
  exact sum_apply_erase_one_filter_subgroupOf hKL f

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- `F`-parameterized form of `H_sharp_alphaFun_inflation` (instance-free interface). -/
theorem H_sharp_alphaFun_inflation_finset [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ)
    (F : Finset ↥hyp.S) (hF : ∀ x : ↥hyp.S, x ∈ F ↔ ((x : G) ∈ hyp.H ∧ x ≠ 1)) :
    ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * ‖H_sharp_alphaFun hG hyp χ 1‖ ^ 2
      ≤ ∑ x ∈ F, ‖H_sharp_alphaFun hG hyp χ x‖ ^ 2 := by
  classical
  have hFeq : F = (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1 := by
    ext x
    rw [hF, Finset.mem_erase, Finset.mem_filter, Subgroup.mem_subgroupOf]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  rw [hFeq]
  exact H_sharp_alphaFun_inflation hG hyp χ

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (13.5) orthogonality hypothesis for `χ = η₁₀`** (Peterfalvi (13.7), first step):
`η₁₀` is orthogonal to `S^{τ₁}` by (5.3.b)+(5.5)+(13.3.c), so *every* `P`-non-kernel (7.7.a)
coefficient vanishes (`a = 0`).  Faithful producer; gated on the (13.3.c)/(5.3.b) grid
orthogonality. -/
theorem eta10_cCoeff_orthogonal [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chars : CharacterDegreeData hyp) :
    ∀ i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1), 0 < i →
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)) →
      (H_sharp_hypothesis76 hG hyp).cCoeff hyp.eta10 i = 0 := by
  classical
  intro j _ _
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S with hKdef
  have hKJ : K = hyp.H.subgroupOf hyp.S := rfl
  haveI hKnorm : K.Normal := by rw [hKJ]; exact H_sharp_subgroupOf_normal hyp
  haveI hKcomm : IsMulCommutative ↥K := by
    rw [hKJ]
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe (show hyp.H ≤ hyp.S from hyp.H_le_S)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  have hzeta_one : ∀ j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      (H_sharp_hypothesis76 hG hyp).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
    have hθ1 : (θ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        θ.2
    rw [hθ, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one]
  have hidx0 : (K.index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := K)
  have hd1 : (H_sharp_hypothesis76 hG hyp).d j = 1 := by
    have h := (H_sharp_hypothesis76 hG hyp).zeta_one_eq_d_mul j
    rw [hzeta_one j, hzeta_one 0] at h
    field_simp at h
    exact h.symm
  have hζ0K : (H_sharp_hypothesis76 hG hyp).zeta 0
      = ClassFunction.induce K
          ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K :
            OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) :
              ClassFunction ↥K ℂ) := by
    rw [hKJ]
    exact H_sharp_zeta_zero hG hyp
  have hfield1 : ∀ θ θ' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      chars.tau1S (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
          - ClassFunction.induce K (θ' : ClassFunction ↥K ℂ))
        = ClassFunction.induce hyp.S
            (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
              - ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)) := by
    rw [hKJ]
    intro θ θ'
    have h := chars.tau1S_apply_induce_sub _ _ θ.2 θ'.2
    exact h.trans (by congr! <;> exact Subsingleton.elim _ _)
  -- the (4.1)/(5.3.b) field, at the `η₁₀`-index
  have hfieldEta : ∀ θ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ClassFunction.inner hyp.eta10
        (chars.tau1S (ClassFunction.induce K (θ : ClassFunction ↥K ℂ))) = 0 := by
    rw [hKJ]
    intro θ
    have h := chars.tau1S_induce_inner_eta ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ _ θ.2
    convert h using 1 <;> congr! <;> exact Subsingleton.elim _ _
  obtain ⟨θj, hθj⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
  rw [show (H_sharp_hypothesis76 hG hyp).cCoeff hyp.eta10 j
      = ClassFunction.inner
          ((H_sharp_hypothesis76 hG hyp).hyp71.τ ((H_sharp_hypothesis76 hG hyp).psiSupp j))
          hyp.eta10 from rfl]
  rw [show (H_sharp_hypothesis76 hG hyp).hyp71.τ = (H_sharp_hypothesis71 hG hyp).τ from rfl,
    H_sharp_tau_eq_induce hG hyp]
  have hψ : ((H_sharp_hypothesis76 hG hyp).psiSupp j : ClassFunction ↥hyp.S ℂ)
      = ClassFunction.induce K (θj : ClassFunction ↥K ℂ)
        - ClassFunction.induce K
            ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K :
              OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) :
                ClassFunction ↥K ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1, one_smul, hθj, hζ0K]
  rw [hψ, ← hfield1 θj _, map_sub, ClassFunction.inner_sub_left]
  have h1 : ClassFunction.inner
      (chars.tau1S (ClassFunction.induce K (θj : ClassFunction ↥K ℂ))) hyp.eta10 = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm hyp.eta10 _, hfieldEta θj, star_zero]
  have h2 : ClassFunction.inner
      (chars.tau1S (ClassFunction.induce K
        ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K :
          OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) :
            ClassFunction ↥K ℂ))) hyp.eta10 = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm hyp.eta10 _, hfieldEta _, star_zero]
  rw [h1, h2, sub_zero]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (7.7.a) coefficients of `η₁₀` are integers**: `c_i = ⟨τ(ψ_i), η₁₀⟩` with
`η₁₀ ∈ ℤ[Irr G]` (real, `eta10_mem_ZIrr`) and `τ(ψ_i) ∈ ℤ[Irr G]` (the Dade image of the
virtual character `ψ_i = ζ_i − d_i ζ_0`, Peterfalvi (2.10)).  Faithful producer; the residual
is the `τ`-image virtuality (the (2.10) inclusion–exclusion is a `ℤ`-combination of
`Ind_{M(B)} α_B ∈ ℤ[Irr G]`, `induce_alphaB_mem_ZIrr`). -/
theorem eta10_cCoeff_int [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∀ i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      ∃ z : ℤ, (H_sharp_hypothesis76 hG hyp).cCoeff hyp.eta10 i = (z : ℂ) :=
  H_sharp_cCoeff_int hG hyp hyp.eta10_mem_ZIrr

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (13.7) correction is nonzero at `1`**: `α(1) ≡ 1 (mod q)` by the (1.10) congruence
(`η₁₀(x) ≡ ω₁₀(y) ≡ 1 (mod 1−ε)` on `W₂^#`-cosets), so `α(1) ≠ 0`.  Faithful producer; gated
on the (1.10)/(3.2.c) grid congruences. -/
theorem eta10_alphaCF_one_ne_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chars : CharacterDegreeData hyp) :
    H_sharp_alphaCF hG hyp hyp.eta10 1 ≠ 0 := by
  classical
  intro hzero
  -- pick `y ∈ W₂^#`
  obtain ⟨y', hy'⟩ : ∃ y' : ↥hyp.W2, y' ≠ 1 := by
    haveI : Nontrivial ↥hyp.W2 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.p_eq_card_W2]; exact hyp.p_prime.one_lt)
    exact exists_ne 1
  have hyW2 : (y' : G) ∈ hyp.W2 := y'.2
  have hy1 : (y' : G) ≠ 1 := fun h => hy' (Subtype.ext h)
  -- `y ∈ P ≤ H`, `y ∈ S`
  have hyP : (y' : G) ∈ hyp.P := W2_le_P hG hyp hyW2
  have hPS : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hyS : (y' : G) ∈ hyp.S := hPS hyP
  have hyH : (y' : G) ∈ hyp.H := (le_sup_left : hyp.P ≤ hyp.H) hyP
  -- kernel-only point formula (`eta10_cCoeff_orthogonal`): `η₁₀(y) = α(y)`
  have hval : hyp.eta10 ((⟨(y' : G), hyS⟩ : ↥hyp.S) : G)
      = H_sharp_alphaFun hG hyp hyp.eta10 ⟨(y' : G), hyS⟩ :=
    H_sharp_point_formula_kernel_only hG hyp hyp.eta10
      (eta10_cCoeff_orthogonal hG hyp chars) ⟨(y' : G), hyS⟩
      (by rw [OddOrder.Peterfalvi.S04.mem_sharp]; exact ⟨hyH, hy1⟩)
  -- `α(y) = α(1) = 0` (`P`-constancy + the assumption)
  have hconst := H_sharp_alphaFun_const_on_P hG hyp hyp.eta10 ⟨(y' : G), hyS⟩
    (Subgroup.mem_subgroupOf.mpr hyP)
  have halpha0 : H_sharp_alphaFun hG hyp hyp.eta10 1 = 0 := by
    rw [← H_sharp_alphaCF_apply hG hyp hyp.eta10 1]; exact hzero
  have heta0 : hyp.eta10 (y' : G) = 0 := by
    have := hval.trans (hconst.trans halpha0)
    exact this
  -- the (1.10) congruence: `η₁₀(y) ≡ 1 (mod (1 − ε))`, so `η₁₀(y) = 0` forces `q ∣ 1`
  obtain ⟨z, hzint, hz⟩ := hyp.eta10_apply_sub_one_integral
    (Complex.isPrimitiveRoot_exp hyp.q hyp.q_prime.pos.ne') hyW2 hy1
  rw [heta0, zero_sub] at hz
  have hdvd : (hyp.q : ℤ) ∣ (-1 : ℤ) :=
    OddOrder.RepresentationTheory.int_dvd_of_one_sub_primRoot_dvd hyp.q_prime
      (Complex.isPrimitiveRoot_exp hyp.q hyp.q_prime.pos.ne') hzint (by exact_mod_cast hz)
  have hle : (hyp.q : ℤ) ≤ 1 := Int.le_of_dvd one_pos (dvd_neg.mp hdvd)
  have := hyp.q_prime.one_lt
  omega

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **Peterfalvi (13.5) for `χ = η₁₀`, `a = 0`** — the correction datum of the (13.7) estimate.

Assembly target (WIP): the concrete correction `α = H_sharp_alphaFun` with the point formula
`η₁₀ = α` on `H^#` (`H_sharp_point_formula_kernel_only` + `eta10_cCoeff_orthogonal`),
`α|_H ∈ ℤ[Irr H]` (`H_sharp_alphaCF_restrict_mem_ZIrr` + `eta10_cCoeff_int`) giving
`n = ‖α‖² ∈ ℕ` (`exists_nat_inner_self_of_mem_ZIrr`) and `d = |α(1)|`
(`exists_int_apply_one_of_mem_ZIrr`), the Parseval bookkeeping
(`sum_filter_erase_one_normSq_eq`), the (13.5.c) inflation (`H_sharp_alphaFun_inflation`),
`α(1) ≠ 0` (`eta10_alphaCF_one_ne_zero`) forcing `n ≥ 1`, and `H` abelian
(`H_mulCommutative` + `apply_one_eq_one_of_isMulCommutative`) forcing `d² = 1` at `n = 1`.
The remaining glue is `Fintype`/`Decidable` instance canonicalization across the sum shapes —
**decided route (07-05 loop it.12)**: parameterize `sum_filter_erase_one_normSq_eq`,
`sum_apply_erase_one_filter_subgroupOf`, and `H_sharp_alphaFun_inflation` over an explicit
`F : Finset ↥S` with a membership characterization `hF : ∀ x, x ∈ F ↔ (↑x ∈ K ∧ x ≠ 1)`
(instance-free interfaces; each proof converts `F` to its local spelling by `Finset.ext hF`
within its own single elaboration context), then instantiate all three with one assembly-side
`F`.  Direct `rw`-joins across the lemmas' baked spellings fail on invisible
`Fintype`/`DecidablePred` instance differences even under shared `open scoped` context. -/
theorem exists_caseB_data_eta10 [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (chars : CharacterDegreeData hyp) :
    ∃ (α : G → ℂ) (d n s : ℕ),
      (∀ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, hyp.eta10 x = α x) ∧
      (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖α x‖ ^ 2 = (s : ℝ)) ∧
      1 ≤ n ∧ s + d ^ 2 = Nat.card ↥hyp.H * n ∧
      (hyp.p ^ hyp.q - 1) * d ^ 2 ≤ s ∧ (n = 1 → d ^ 2 = 1) := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set αS : ↥hyp.S → ℂ := H_sharp_alphaFun _hG hyp hyp.eta10 with hαSdef
  have hHS : hyp.H ≤ hyp.S := by
    have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    show hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]; exact le_trans inf_le_left hUS
  refine ⟨fun g => if h : g ∈ hyp.S then αS ⟨g, h⟩ else 0, ?_⟩
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 _hG hyp).H.subgroupOf hyp.S with hKdef
  haveI : Fintype ↥K := FiniteInduce.finiteSubFintype K
  -- The single sharp `Finset` all bookkeeping runs through.
  set F : Finset ↥hyp.S := (Finset.univ.filter (· ∈ K)).erase 1 with hFdef
  have hFK : ∀ x : ↥hyp.S, x ∈ F ↔ (x ∈ K ∧ x ≠ 1) := fun x => by
    rw [hFdef, Finset.mem_erase, Finset.mem_filter]
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h1, Finset.mem_univ _, h2⟩⟩
  have hFH : ∀ x : ↥hyp.S, x ∈ F ↔ ((x : G) ∈ hyp.H ∧ x ≠ 1) := fun x => by
    rw [hFK]
    exact and_congr_left (fun _ => Subgroup.mem_subgroupOf)
  set ψ : ClassFunction ↥K ℂ :=
    ClassFunction.restrict K (H_sharp_alphaCF _hG hyp hyp.eta10) with hψdef
  have hψZ : ψ ∈ ZIrr ↥K :=
    H_sharp_alphaCF_restrict_mem_ZIrr _hG hyp hyp.eta10 (eta10_cCoeff_int _hG hyp)
  obtain ⟨n, hn⟩ := exists_nat_inner_self_of_mem_ZIrr hψZ
  obtain ⟨z, hz⟩ := OddOrder.Algebra.exists_int_apply_one_of_mem_ZIrr hψZ
  have hψ1 : ψ 1 = αS 1 := by
    rw [hψdef, ClassFunction.restrict_apply, OneMemClass.coe_one, H_sharp_alphaCF_apply]
  have hcardK : Nat.card ↥K = Nat.card ↥hyp.H := by
    rw [hKdef]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show (H_sharp_hypothesis76 _hG hyp).H ≤ hyp.S from hHS)).toEquiv
  set d : ℕ := z.natAbs with hddef
  have hagree : ∀ k : ↥K, αS ↑k = ψ k := fun k => by
    rw [hψdef, ClassFunction.restrict_apply, H_sharp_alphaCF_apply]
  -- Bookkeeping over `F`.
  have hbook := sum_finset_sharp_normSq_eq (K := K) F hFK αS ψ hagree hn
  have hα1 : ‖αS 1‖ ^ 2 = (d : ℝ) ^ 2 := by
    have h2 : ((d : ℕ) : ℝ) ^ 2 = ((z : ℝ)) ^ 2 := by
      rw [hddef]
      have h0 : (((z.natAbs ^ 2 : ℕ) : ℤ) : ℝ) = ((z ^ 2 : ℤ) : ℝ) := by
        exact_mod_cast Int.natAbs_sq z
      push_cast at h0
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact h0
    rw [← hψ1, hz, Complex.norm_intCast, sq_abs, ← h2]
  have hsharp_nonneg : (0 : ℝ) ≤ ∑ x ∈ F, ‖αS x‖ ^ 2 :=
    Finset.sum_nonneg (fun x _ => by positivity)
  have hd2n : d ^ 2 ≤ Nat.card ↥hyp.H * n := by
    have h0 := hsharp_nonneg
    rw [hbook] at h0
    have h1 : (d : ℝ) ^ 2 ≤ (Nat.card ↥hyp.H : ℝ) * (n : ℝ) := by
      rw [← hα1, ← hcardK]
      linarith [h0]
    exact_mod_cast h1
  set s : ℕ := Nat.card ↥hyp.H * n - d ^ 2 with hsdef
  have hsval : (s : ℝ) = (Nat.card ↥hyp.H : ℝ) * (n : ℝ) - (d : ℝ) ^ 2 := by
    rw [hsdef, Nat.cast_sub hd2n]
    push_cast
    ring
  have hFsum : ∑ x ∈ F, ‖αS x‖ ^ 2 = (s : ℝ) := by
    rw [hbook, hα1, hsval, hcardK]
  -- Transport to the ambient sharp set.
  have hglue := sum_finset_sharp_transport (K := hyp.H) (L := hyp.S) hHS F hFH
    (fun g : G => ‖if h : g ∈ hyp.S then αS ⟨g, h⟩ else 0‖ ^ 2)
  have hGside : ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset,
      ‖if h : x ∈ hyp.S then αS ⟨x, h⟩ else 0‖ ^ 2 = (s : ℝ) := by
    rw [← hglue, ← hFsum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxS : ((x : ↥hyp.S) : G) ∈ hyp.S := x.2
    rw [dif_pos hxS]
  refine ⟨d, n, s, ?_, hGside, ?_, ?_, ?_, ?_⟩
  · -- The point formula: `η₁₀ = α` on `H^#`.
    intro x hx
    obtain ⟨hxH, hx1⟩ := (Set.Finite.mem_toFinset _).mp hx
    have hxS : x ∈ hyp.S := hHS hxH
    show hyp.eta10 x = if h : x ∈ hyp.S then αS ⟨x, h⟩ else 0
    rw [dif_pos hxS]
    have hxsharp : ((⟨x, hxS⟩ : ↥hyp.S) : G) ∈
        OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) :=
      OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hxH, hx1⟩
    have hpt := H_sharp_point_formula_kernel_only _hG hyp hyp.eta10
      (eta10_cCoeff_orthogonal _hG hyp chars) ⟨x, hxS⟩ hxsharp
    rw [hpt]
    rfl
  · -- `1 ≤ n`: else `ψ = 0` pointwise, contradicting `α(1) ≠ 0`.
    by_contra hn0
    push Not at hn0
    have hn00 : n = 0 := by omega
    subst hn00
    have hzero : ∑ k : ↥K, ‖ψ k‖ ^ 2 = 0 := by
      have h := sum_normSq_eq_card_mul_inner (H := ↥K) ψ
      rw [hn] at h
      have h0 : ((∑ k : ↥K, ‖ψ k‖ ^ 2 : ℝ) : ℂ) = 0 := by rw [h]; push_cast; ring
      exact_mod_cast h0
    have hψ10 : ψ 1 = 0 := by
      have h1 : ‖ψ 1‖ ^ 2 = 0 := by
        have hle : ‖ψ 1‖ ^ 2 ≤ ∑ k : ↥K, ‖ψ k‖ ^ 2 :=
          Finset.single_le_sum (f := fun k : ↥K => ‖ψ k‖ ^ 2)
            (fun k _ => by positivity) (Finset.mem_univ 1)
        have hge : (0 : ℝ) ≤ ‖ψ 1‖ ^ 2 := by positivity
        linarith [hzero ▸ hle]
      have h2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      simpa using h2
    refine eta10_alphaCF_one_ne_zero _hG hyp chars ?_
    rw [hψdef, ClassFunction.restrict_apply, OneMemClass.coe_one,
      H_sharp_alphaCF_apply] at hψ10
    rw [← H_sharp_alphaCF_apply _hG hyp hyp.eta10 1] at hψ10
    exact hψ10
  · -- Parseval: `s + d² = |H|·n`.
    omega
  · -- Inflation: `(p^q − 1)·d² ≤ s`.
    have hinfl := H_sharp_alphaFun_inflation_finset _hG hyp hyp.eta10 F hFH
    have h1 : ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * (d : ℝ) ^ 2 ≤ (s : ℝ) := by
      rw [← hα1, ← hFsum]
      exact hinfl
    exact_mod_cast h1
  · -- `n = 1 → d² = 1`: `ψ` is `±` an irreducible of the abelian `K`, hence linear.
    intro hn1
    subst hn1
    have hn' : ClassFunction.inner ψ ψ = 1 := by rw [hn]; norm_num
    obtain ⟨ε, ξ, hε, hψeq⟩ :=
      OddOrder.RepresentationTheory.exists_zsmul_irreducibleCharacter_of_inner_self_one hψZ hn'
    haveI : IsMulCommutative ↥K := by
      have hH := hyp.H_mulCommutative _hG
      have e := Subgroup.subgroupOfEquivOfLe
        (show (H_sharp_hypothesis76 _hG hyp).H ≤ hyp.S from hHS)
      exact ⟨⟨fun a b => e.injective (by
        rw [map_mul, map_mul]
        exact hH.is_comm.comm (e a) (e b))⟩⟩
    have hξ1 : (ξ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        ξ.2
    have hz2 : (z : ℂ) = (ε : ℂ) := by
      rw [← hz, hψeq,
        show ((ε • (ξ : ClassFunction ↥K ℂ)) 1) = (ε : ℂ) * (ξ : ClassFunction ↥K ℂ) 1 from by
          rw [← Int.cast_smul_eq_zsmul ℂ, ClassFunction.smul_apply],
        hξ1, mul_one]
    have hzε : z = ε := by exact_mod_cast hz2
    rcases hε with h | h <;>
      · rw [hddef, hzε, h]
        rfl

/-- **Peterfalvi (13.7), textbook form**: `∑_{x∈H^#}|η₁₀(x)|² ≥ |H^#|`, as a sum over the
ambient sharp `H^# ⊂ G`.

**Real assembly** through the (13.7) engine `caseB_eta_norm_bound` (stated over an abstract
`Finset`, instantiated with `H^# ⊂ G` directly): the character-theoretic inputs are the
(13.5)-for-`η₁₀` package (`exists_caseB_data_eta10`); `|H| ≥ 1` and `|P| = p^q ≥ 2` are
counting facts. -/
theorem eta10_sharp_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (chars : CharacterDegreeData hyp) :
    (Nat.card ↥hyp.H : ℝ) - 1
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖hyp.eta10 x‖ ^ 2 := by
  obtain ⟨α, d, n, s, hχ, hs, hn, hParseval, hInflation, habelian⟩ :=
    exists_caseB_data_eta10 _hG hyp chars
  have hH1 : 1 ≤ Nat.card ↥hyp.H := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hP2 : 2 ≤ hyp.p ^ hyp.q - 1 + 1 := by
    have hp3 := hyp.three_le_p
    have hq3 := hyp.three_le_q
    have h1 : 3 ≤ hyp.p ^ hyp.q := by
      calc 3 ≤ hyp.p := hp3
        _ ≤ hyp.p ^ hyp.q := Nat.le_self_pow (by omega) _
    omega
  haveI : Fintype G := Fintype.ofFinite G
  have h := caseB_eta_norm_bound (S := G) α (fun x => hyp.eta10 x)
    ((Set.toFinite (sharpSubgroup hyp.H)).toFinset)
    (Hcard := Nat.card ↥hyp.H) (P := hyp.p ^ hyp.q - 1 + 1) (d := d) (n := n) (s := s)
    hH1 (fun x hx => hχ x hx) hs hP2 hn hParseval (by simpa using hInflation) habelian
  exact h

/-- **`2v ≤ |Q| − 1`** — the `T`-side mirror of `two_mul_u_le`: from the (13.4) value
`v = (q^p − 1)/(q − 1)` and `q ≥ 3`, so `v ≤ (q^p−1)/2`. -/
theorem Hypothesis.two_mul_v_le (hyp : Hypothesis (G := G))
    (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1)) :
    2 * hyp.v ≤ hyp.q ^ hyp.p - 1 := by
  have hq3 := hyp.three_le_q
  have h1 : (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ≤ (hyp.q ^ hyp.p - 1) / 2 :=
    Nat.div_le_div_left (by omega) (by omega)
  have h2 : (hyp.q ^ hyp.p - 1) / 2 * 2 ≤ hyp.q ^ hyp.p - 1 := Nat.div_mul_le_self _ _
  omega

open scoped Classical in
open scoped FiniteInduce in
open scoped Classical in
open scoped FiniteInduce in
/-- **The `T`-side (13.3.c) distinguished index** — the `μ'_j` of the (13.8)-for-`T` estimate,
localized to the `(T, Q^#)` (7.6) family: a `Q`-non-kernel member `ζ_{i₁}` with
`‖ζ_{i₁}‖² = p`, degree `pv`, distinguished coefficient `⟨τψ_{i₁}, η₁₀⟩ = δ = ±1`, and all
other `Q`-non-kernel coefficients vanishing.  Faithful producer; gated on the `T`-side (13.3.c)
grid analysis. -/
theorem exists_muT_index [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp)
    (hvd : hyp.v * hyp.d ≠ 1) :
    ∃ (i₁ : Fin ((Q_sharp_hypothesis76 hG hyp hvd).n + 1)) (δ : ℤ), 0 < i₁ ∧
      ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((Q_sharp_hypothesis76 hG hyp hvd).zeta i₁)) ∧
      δ ^ 2 = 1 ∧
      (Q_sharp_hypothesis76 hG hyp hvd).cCoeff hyp.eta10 i₁ = (δ : ℂ) ∧
      (∀ i : Fin ((Q_sharp_hypothesis76 hG hyp hvd).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ((Q_sharp_hypothesis76 hG hyp hvd).zeta i)) →
        (Q_sharp_hypothesis76 hG hyp hvd).cCoeff hyp.eta10 i = 0) ∧
      (Q_sharp_hypothesis76 hG hyp hvd).zetaNormSq i₁ = (hyp.p : ℂ) ∧
      (Q_sharp_hypothesis76 hG hyp hvd).zeta i₁ 1 = ((hyp.p * hyp.v : ℕ) : ℂ) := by
  sorry

open scoped Classical in
open scoped FiniteInduce in
/-- **The `T`-side correction has integer value at `1`** — the `T`-side (13.5.a) integrality
(`α|_Q ∈ ℤ[Irr Q]` needs `Q` abelian, the gated (13.2.b)-dual; carried as an atom). -/
theorem exists_etaT_alphaFun_one_int [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (hvd : hyp.v * hyp.d ≠ 1) :
    ∃ α1 : ℤ, hypothesis76AlphaFun (Q_sharp_hypothesis76 hG hyp hvd)
      (hyp.Q.subgroupOf hyp.T) hyp.eta10 1 = (α1 : ℂ) := by
  sorry

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5) for the `T`-side, `χ = η₁₀`, `ζ = (1/p)·μ'_j`, `a = δ`** — the
correction datum of the (13.8)-for-`T` estimate.

**Real assembly** over the `T`-side ρ-machinery (`Q_sharp_hypothesis76`) and the generic
(13.5.a) cluster: `ζ := (1/p)·ζ_{i₁}` (`exists_muT_index`: `‖ζ_{i₁}‖² = p`, degree `pv`,
coefficient `δ`), `α` the `Q`-kernel tail (`hypothesis76AlphaFun`); the point formula is the
generic `hypothesis76_point_formula`, the first term is `(1/p²)(|T|·p − (pv)²) = |T'| − v²`
(Parseval + `card_T_eq_deriv_mul_p`), the inner-product vanishes by the distinct-fibre
orthogonality (S-level shortcut), and the inflation is the generic `F`-form with
`|Q| = q^p`. -/
theorem exists_caseB_data_eta10_T [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (chars : CharacterDegreeData hyp) :
    ∃ (ζ α : ↥hyp.T → ℂ) (α1 δ : ℤ),
      (∀ x : ↥hyp.T, x ∉ hyp.Q.subgroupOf hyp.T → ζ x = 0) ∧
      (∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
        ζ x * (starRingEnd ℂ) (α x)) = 0 ∧
      (∀ x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1,
        hyp.eta10 ↑x = (δ : ℂ) * ζ x + α x) ∧
      ((∑ x : ↥hyp.T, ‖ζ x‖ ^ 2) - ‖ζ 1‖ ^ 2
        = (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2) ∧
      ((ζ 1 * (starRingEnd ℂ) (α 1)).re = (hyp.v : ℝ) * (α1 : ℝ)) ∧
      δ ^ 2 = 1 ∧
      ((hyp.q ^ hyp.p - 1 : ℕ) : ℝ) * ((α1 : ℤ) : ℝ) ^ 2
        ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1, ‖α x‖ ^ 2 := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨hD, hv, hQcard⟩ := lambda_forces_T_caseB _hG chars
  obtain ⟨hd1, hv2, hvd⟩ := hyp.caseB_vd_facts hD hv
  obtain ⟨i₁, δ, hi₁pos, hi₁ker, hδ2, hi₁c, hmiddle, hnormP, hdeg⟩ :=
    exists_muT_index _hG chars hvd
  obtain ⟨α1, hα1⟩ := exists_etaT_alphaFun_one_int _hG (hyp := hyp) hvd
  have hp3 := hyp.three_le_p
  have hpC : (hyp.p : ℂ) ≠ 0 := by exact_mod_cast (by omega : hyp.p ≠ 0)
  have hpR : (hyp.p : ℝ) ≠ 0 := by exact_mod_cast (by omega : hyp.p ≠ 0)
  have hvanishZ : ∀ x : ↥hyp.T, x ∉ hyp.Q.subgroupOf hyp.T →
      (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x = 0 := fun x hx =>
    (Q_sharp_hypothesis76 _hG hyp hvd).zeta_eq_zero_of_not_mem_H i₁ x
      (fun hmem => hx (Subgroup.mem_subgroupOf.mpr hmem))
  refine ⟨fun x => ((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x,
    hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
      (hyp.Q.subgroupOf hyp.T) hyp.eta10, α1, δ, ?_, ?_, ?_, ?_, ?_, hδ2, ?_⟩
  · -- `ζ` vanishes off `Q`.
    intro x hx
    show ((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x = 0
    rw [hvanishZ x hx, mul_zero]
  · -- `⟨ζ, α⟩ = 0`: pull the `p⁻¹`, extend to the full sum, cite the generic orthogonality.
    have hfull := hypothesis76_zeta_inner_alphaFun_eq_zero
      (Q_sharp_hypothesis76 _hG hyp hvd) (hyp.Q.subgroupOf hyp.T) hyp.eta10 i₁ hi₁ker
    have hext : (∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
        (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x * (starRingEnd ℂ)
          (hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
            (hyp.Q.subgroupOf hyp.T) hyp.eta10 x))
        = ∑ x : ↥hyp.T, (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x * (starRingEnd ℂ)
            (hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
              (hyp.Q.subgroupOf hyp.T) hyp.eta10 x) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ hyp.Q.subgroupOf hyp.T)
        (fun x => (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x * (starRingEnd ℂ)
          (hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
            (hyp.Q.subgroupOf hyp.T) hyp.eta10 x))]
      have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ hyp.Q.subgroupOf hyp.T),
          (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x * (starRingEnd ℂ)
            (hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
              (hyp.Q.subgroupOf hyp.T) hyp.eta10 x) = 0 := by
        refine Finset.sum_eq_zero (fun x hx => ?_)
        rw [hvanishZ x (Finset.mem_filter.mp hx).2, zero_mul]
      rw [h0, add_zero]
    calc ∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
        ((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x * (starRingEnd ℂ)
          (hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
            (hyp.Q.subgroupOf hyp.T) hyp.eta10 x)
        = ((hyp.p : ℂ))⁻¹ * ∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
            (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x * (starRingEnd ℂ)
              (hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
                (hyp.Q.subgroupOf hyp.T) hyp.eta10 x) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x _ => by ring)
      _ = 0 := by rw [hext, hfull, mul_zero]
  · -- The point formula, with `c̄_{i₁}/‖ζ_{i₁}‖² = δ/p`.
    intro x hx
    obtain ⟨hx1, hxmem⟩ := Finset.mem_erase.mp hx
    have hxQ : (↑x : G) ∈ hyp.Q :=
      Subgroup.mem_subgroupOf.mp (Finset.mem_filter.mp hxmem).2
    have hxsharp : (↑x : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) := by
      refine OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hxQ, ?_⟩
      intro h1
      exact hx1 (Subtype.ext h1)
    show hyp.eta10 ↑x = (δ : ℂ)
        * (((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x)
      + hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
          (hyp.Q.subgroupOf hyp.T) hyp.eta10 x
    have hpt := hypothesis76_point_formula (Q_sharp_hypothesis76 _hG hyp hvd)
      (fun _ => rfl) (hyp.Q.subgroupOf hyp.T) hyp.eta10 i₁ hi₁pos hi₁ker hmiddle x hxsharp
    have htail : (∑ i ∈ (Finset.Ioi (0 : Fin ((Q_sharp_hypothesis76 _hG hyp hvd).n + 1))).filter
          (fun i => (hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
            OddOrder.Peterfalvi.S03.characterKernel
              ((Q_sharp_hypothesis76 _hG hyp hvd).zeta i)),
        (star ((Q_sharp_hypothesis76 _hG hyp hvd).cCoeff hyp.eta10 i) /
          (Q_sharp_hypothesis76 _hG hyp hvd).zetaNormSq i)
          * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i x)
        = hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
            (hyp.Q.subgroupOf hyp.T) hyp.eta10 x := rfl
    rw [hpt, htail, hi₁c, star_intCast, hnormP]
    ring
  · -- The first term: `(1/p²)(|T|·p − (pv)²) = |T'| − v²`.
    have hpars : ((∑ x : ↥hyp.T, ‖(Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x‖ ^ 2 : ℝ) : ℂ)
        = (Nat.card ↥hyp.T : ℂ) * (hyp.p : ℂ) := by
      rw [sum_normSq_eq_card_mul_inner, ← OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq,
        hnormP]
    have hparsR : ∑ x : ↥hyp.T, ‖(Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x‖ ^ 2
        = (Nat.card ↥hyp.T : ℝ) * (hyp.p : ℝ) := by exact_mod_cast hpars
    have hscale : ∀ x : ↥hyp.T,
        ‖((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x‖ ^ 2
        = ((hyp.p : ℝ))⁻¹ ^ 2 * ‖(Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x‖ ^ 2 := by
      intro x
      rw [norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
    have hζ1 : ‖((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ 1‖ ^ 2
        = (hyp.v : ℝ) ^ 2 := by
      rw [hdeg, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
      rw [show ((hyp.p * hyp.v : ℕ) : ℝ) = (hyp.p : ℝ) * (hyp.v : ℝ) from by push_cast; ring]
      field_simp
    have hTp : (Nat.card ↥hyp.T : ℝ) = (Nat.card ↥(derivedInG hyp.T) : ℝ) * (hyp.p : ℝ) := by
      exact_mod_cast hyp.card_T_eq_deriv_mul_p _hG
    rw [Finset.sum_congr rfl (fun x _ => hscale x), ← Finset.mul_sum, hparsR, hζ1, hTp]
    field_simp
  · -- The cross term: `ζ(1) = v` real, `α(1) = α1 ∈ ℤ`.
    have hζ1v : ((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ 1
        = ((hyp.v : ℕ) : ℂ) := by
      rw [hdeg, show ((hyp.p * hyp.v : ℕ) : ℂ) = (hyp.p : ℂ) * (hyp.v : ℂ) from by
        push_cast; ring]
      field_simp
    show ((((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ 1)
        * (starRingEnd ℂ) (hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
          (hyp.Q.subgroupOf hyp.T) hyp.eta10 1)).re = (hyp.v : ℝ) * (α1 : ℝ)
    rw [hζ1v, hα1]
    rw [show ((hyp.v : ℕ) : ℂ) = (((hyp.v : ℕ) : ℝ) : ℂ) from by push_cast; ring,
      show ((α1 : ℤ) : ℂ) = (((α1 : ℤ) : ℝ) : ℂ) from by push_cast; ring,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  · -- The inflation: generic `F`-form with `|Q| = q^p`.
    have hF : ∀ x : ↥hyp.T, x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1
        ↔ ((x : G) ∈ (Q_sharp_hypothesis76 _hG hyp hvd).H ∧ x ≠ 1) := by
      intro x
      rw [Finset.mem_erase, Finset.mem_filter]
      constructor
      · rintro ⟨h1, -, h2⟩
        exact ⟨Subgroup.mem_subgroupOf.mp h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨h1, Finset.mem_univ _, Subgroup.mem_subgroupOf.mpr h2⟩
    have hP'H : ∀ x : ↥hyp.T, x ∈ hyp.Q.subgroupOf hyp.T →
        (x : G) ∈ (Q_sharp_hypothesis76 _hG hyp hvd).H := fun x hx =>
      Subgroup.mem_subgroupOf.mp hx
    have hinfl := hypothesis76AlphaFun_inflation (Q_sharp_hypothesis76 _hG hyp hvd)
      (hyp.Q.subgroupOf hyp.T) hyp.eta10 _ hF hP'H
    have hcardQT : Nat.card ↥(hyp.Q.subgroupOf hyp.T) = hyp.q ^ hyp.p := by
      have hQT : hyp.Q ≤ hyp.T := by
        rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQT).toEquiv]
      exact hQcard
    have hqp1 : (1 : ℕ) ≤ hyp.q ^ hyp.p :=
      Nat.one_le_pow _ _ (by have := hyp.three_le_q; omega)
    have hcoeff : ((Nat.card ↥(hyp.Q.subgroupOf hyp.T) : ℝ)) - 1
        = ((hyp.q ^ hyp.p - 1 : ℕ) : ℝ) := by
      rw [hcardQT, Nat.cast_sub hqp1]
      norm_num
    have hval : ‖hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
        (hyp.Q.subgroupOf hyp.T) hyp.eta10 1‖ ^ 2 = ((α1 : ℤ) : ℝ) ^ 2 := by
      rw [hα1, Complex.norm_intCast, sq_abs]
    rw [← hval, ← hcoeff]
    exact hinfl


open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.8) applied to `T`**: `∑_{x∈Q^#}|η₁₀(x)|² ≥ |T'| − v²`, as a sum over the
ambient sharp `Q^# ⊂ G`.

**Real assembly** through the (13.8) engine `caseB_eta01_norm_bound` (inside `↥T`, with
`Q.subgroupOf T`): the character-theoretic inputs are the `T`-side (13.5) package
(`exists_caseB_data_eta10_T`, normalized `ζ` with first term `|T'| − v²`), and the `v`-bound
`2v ≤ |Q| − 1 = q^p − 1` (`two_mul_v_le`, real from the (13.4) value); the engine output
transports to the ambient sharp by `sum_apply_erase_one_filter_subgroupOf`. -/
theorem eta10_Qsharp_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖hyp.eta10 x‖ ^ 2 := by
  classical
  obtain ⟨chars⟩ := character_degree_analysis _hG hyp
  obtain ⟨-, hv, -⟩ := lambda_forces_T_caseB _hG chars
  obtain ⟨ζ, α, α1, δ, hvanish, hinner, hχ, hfirstTerm, hcross, hδ, hinfl⟩ :=
    exists_caseB_data_eta10_T _hG chars
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hu := hyp.two_mul_v_le hv
  -- The engine (bridging the `Classical` decidability instances baked into its statement).
  have hengine : (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1,
          ‖hyp.eta10 ↑x‖ ^ 2 := by
    have h := caseB_eta01_norm_bound (S := ↥hyp.T) (hyp.Q.subgroupOf hyp.T)
      ζ α (fun x => hyp.eta10 ↑x)
      (Pm1 := hyp.q ^ hyp.p - 1) (u := hyp.v)
      (firstTerm := (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)
      (α1 := α1) (δ := δ)
      hvanish (by convert hinner using 2 <;> congr!)
      (fun x hx => hχ x (by convert hx using 2 <;> congr!))
      hfirstTerm hcross hδ
      (by convert hinfl using 2 <;> congr!) hu
    convert h using 2 <;> congr!
  rwa [sum_apply_erase_one_filter_subgroupOf hQT
    (fun y => ‖hyp.eta10 y‖ ^ 2)] at hengine

open scoped FiniteInduce in
/-- **Peterfalvi (13.6) + Parseval, atom form**: `1 ≥ 1/|G| + slam + 1 − uq/(cp^q)`.

The (13.10.1) estimate: global Parseval for `λ^{τ₁}` (`global_normSq_split`, real), the
`‖λ^{τ₁}(1)‖² ≥ 1` term (`one_le_normSq_apply_one_of_mem_ZIrr_of_inner_self_one`, real from
`lambda_tau1_norm_one`), the `G₀`-sum read as the rational atom (`normSqSumQ_spec` +
`G0Finset_cyclicClosed` + Galois integrality, real), the `H^#`-sum bounded by (13.6)
(`lambda_tau1_sharp_norm_lower`), the `Q^#`-sum dropped, and `|S| = p^q(uc)q` (`card_S_val`). -/
theorem analyticEstimate_lambda [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (chars : CharacterDegreeData hyp) :
    (1 : ℚ) ≥ 1 / (Nat.card G : ℚ)
        + normSqSumQ hyp.G0Finset (chars.tau1S chars.lambda) / (Nat.card G : ℚ) + 1
        - (hyp.u : ℚ) * (hyp.q : ℚ) / ((hyp.c : ℚ) * (hyp.p : ℚ) ^ hyp.q) := by
  classical
  obtain ⟨hZ, hn, -⟩ := lambda_tau1_norm_one _hG chars
  obtain ⟨hD, hv, hQ⟩ := lambda_forces_T_caseB _hG chars
  obtain ⟨hd1, hv2, hvd⟩ := hyp.caseB_vd_facts hD hv
  set φ : ClassFunction G ℂ := chars.tau1S chars.lambda with hφdef
  -- Global Parseval split and the term bounds.
  have hsplit := hyp.global_normSq_split _hG φ hn hQ hvd
  have hone : (1 : ℝ) ≤ ‖φ 1‖ ^ 2 :=
    OddOrder.RepresentationTheory.one_le_normSq_apply_one_of_mem_ZIrr_of_inner_self_one hZ hn
  have hsharp := lambda_tau1_sharp_norm_lower _hG chars
  rw [← hφdef] at hsharp
  have hQnonneg : (0 : ℝ) ≤ (hyp.T.index : ℝ)
      * ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖φ x‖ ^ 2 := by
    have h1 : (0 : ℝ) ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖φ x‖ ^ 2 :=
      Finset.sum_nonneg fun x _ => by positivity
    positivity
  -- The rational atom is the `G₀`-sum.
  have hGal := OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZ
    hyp.G0Finset_cyclicClosed
  have hspec := normSqSumQ_spec hGal
  -- Cardinalities.
  have hg0 : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hGeq : (Nat.card G : ℝ)
      = (hyp.p : ℝ) ^ hyp.q * ((hyp.u : ℝ) * (hyp.c : ℝ)) * (hyp.q : ℝ)
        * (hyp.S.index : ℝ) := by
    have h := hyp.S.card_mul_index
    rw [hyp.card_S_val _hG] at h
    exact_mod_cast h.symm
  have hc0 : (0 : ℝ) < (hyp.c : ℝ) := by
    have : 0 < hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
    exact_mod_cast this
  have hp0 : (0 : ℝ) < (hyp.p : ℝ) := by
    have := hyp.three_le_p; exact_mod_cast (by omega : 0 < hyp.p)
  -- Assemble in ℝ, then cast.
  rw [ge_iff_le, ← Rat.cast_le (K := ℝ)]
  push_cast
  rw [hspec]
  set s : ℝ := ∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2 with hsdef
  set w : ℝ := (hyp.u : ℝ) * (hyp.q : ℝ) / ((hyp.c : ℝ) * (hyp.p : ℝ) ^ hyp.q) with hwdef
  -- `w·|G| = [G:S]·(uq)²`.
  have hwg : w * (Nat.card G : ℝ) = (hyp.S.index : ℝ) * ((hyp.u : ℝ) * (hyp.q : ℝ)) ^ 2 := by
    rw [hwdef, hGeq]
    field_simp
  -- `1 + s ≤ w·|G|` from the split.
  have hSidx0 : (0 : ℝ) ≤ (hyp.S.index : ℝ) := by positivity
  have hkey : 1 + s ≤ w * (Nat.card G : ℝ) := by
    rw [hwg]
    have hSGeq : (hyp.S.index : ℝ) * (Nat.card ↥hyp.S : ℝ) = (Nat.card G : ℝ) := by
      exact_mod_cast mul_comm (Nat.card ↥hyp.S) hyp.S.index ▸ hyp.S.card_mul_index
    have huq : ((hyp.u * hyp.q : ℕ) : ℝ) = (hyp.u : ℝ) * (hyp.q : ℝ) := by push_cast; ring
    rw [huq] at hsharp
    have hHbound := mul_le_mul_of_nonneg_left hsharp hSidx0
    rw [nsmul_eq_mul, nsmul_eq_mul] at hsplit
    linarith [hsplit, hone, hHbound, hQnonneg, hSGeq]
  -- Final division.
  have hdiv : (1 + s) / (Nat.card G : ℝ) ≤ w :=
    (div_le_iff₀ hg0).mpr (by linarith [hkey])
  calc 1 / (Nat.card G : ℝ) + s / (Nat.card G : ℝ) + 1 - w
      = (1 + s) / (Nat.card G : ℝ) + 1 - w := by rw [add_div]
    _ ≤ w + 1 - w := by linarith [hdiv]
    _ = 1 := by ring

open scoped FiniteInduce in
/-- **Peterfalvi (13.7)+(13.8) for `T` (`D = 1`), atom form**:
`1 ≥ 1/|G| + seta + HS + TT` with `TT` the (13.4) counting value.

The (13.10.2) estimate: global Parseval for `η₁₀` (`global_normSq_split`; the norm-one facts
are *real*, from the 3002-threaded grid: `eta10_mem_ZIrr`/`eta10_inner_self_one`), the
`G₀`-sum read as the rational atom, the `H^#`-sum bounded by (13.7) (`eta10_sharp_norm_lower`),
the `Q^#`-sum bounded by (13.8)-for-`T` (`eta10_Qsharp_norm_lower`), and the (13.4) values
collapsing `(|T'|−v²)/|T|` to the stated `TT`. -/
theorem analyticEstimate_eta [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (1 : ℚ) ≥ 1 / (Nat.card G : ℚ)
        + normSqSumQ hyp.G0Finset hyp.eta10 / (Nat.card G : ℚ)
        + ((Nat.card hyp.H - 1 : ℕ) : ℚ) / (Nat.card hyp.S : ℚ)
        + (1 / (hyp.p : ℚ) - 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1))
          + 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1) * (hyp.q : ℚ) ^ hyp.p)) := by
  classical
  obtain ⟨chars⟩ := character_degree_analysis _hG hyp
  obtain ⟨hD, hv, hQ⟩ := lambda_forces_T_caseB _hG chars
  obtain ⟨hd1, hv2, hvd⟩ := hyp.caseB_vd_facts hD hv
  have hZ := hyp.eta10_mem_ZIrr
  have hn := hyp.eta10_inner_self_one
  -- Global Parseval split and the term bounds.
  have hsplit := hyp.global_normSq_split _hG hyp.eta10 hn hQ hvd
  have hone : (1 : ℝ) ≤ ‖hyp.eta10 1‖ ^ 2 :=
    OddOrder.RepresentationTheory.one_le_normSq_apply_one_of_mem_ZIrr_of_inner_self_one hZ hn
  have hsharpH := eta10_sharp_norm_lower _hG hyp chars
  have hsharpQ := eta10_Qsharp_norm_lower _hG hyp
  -- The rational atom is the `G₀`-sum.
  have hGal := OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZ
    hyp.G0Finset_cyclicClosed
  have hspec := normSqSumQ_spec hGal
  -- Cardinalities and casts.
  have hg0 : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hp3 : 3 ≤ hyp.p := hyp.three_le_p
  have hqp1 : (1 : ℕ) ≤ hyp.q ^ hyp.p := Nat.one_le_pow _ _ (by omega)
  have hdvd : (hyp.q - 1) ∣ (hyp.q ^ hyp.p - 1) := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow hyp.q 1 hyp.p
  have hvq : (hyp.v : ℝ) * ((hyp.q : ℝ) - 1) = (hyp.q : ℝ) ^ hyp.p - 1 := by
    have h := Nat.div_mul_cancel hdvd
    rw [← hv] at h
    have := congrArg (Nat.cast (R := ℝ)) h
    push_cast [Nat.cast_sub (by omega : (1:ℕ) ≤ hyp.q), Nat.cast_sub hqp1] at this
    convert this using 2 <;> push_cast <;> ring
  have hderivT : (Nat.card ↥(derivedInG hyp.T) : ℝ) = (hyp.q : ℝ) ^ hyp.p * (hyp.v : ℝ) := by
    have h := hyp.card_deriv_T_eq _hG
    rw [hQ, hd1, mul_one] at h
    exact_mod_cast h
  have hTval : (Nat.card ↥hyp.T : ℝ) = (hyp.q : ℝ) ^ hyp.p * (hyp.v : ℝ) * (hyp.p : ℝ) := by
    have h := hyp.card_T_eq _hG
    rw [hQ, hd1, mul_one] at h
    exact_mod_cast h
  have hSGeq : (hyp.S.index : ℝ) * (Nat.card ↥hyp.S : ℝ) = (Nat.card G : ℝ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.S) hyp.S.index ▸ hyp.S.card_mul_index
  have hTGeq : (hyp.T.index : ℝ) * (Nat.card ↥hyp.T : ℝ) = (Nat.card G : ℝ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.T) hyp.T.index ▸ hyp.T.card_mul_index
  have hS0 : (0 : ℝ) < (Nat.card ↥hyp.S : ℝ) := by
    exact_mod_cast Nat.card_pos (α := ↥hyp.S)
  have hT0 : (0 : ℝ) < (Nat.card ↥hyp.T : ℝ) := by
    exact_mod_cast Nat.card_pos (α := ↥hyp.T)
  have hSidx0 : (0 : ℝ) < (hyp.S.index : ℝ) := by
    rcases (Nat.cast_pos (α := ℝ)).mpr (Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := hyp.S))) with h
    exact h
  have hTidx0 : (0 : ℝ) < (hyp.T.index : ℝ) := by
    rcases (Nat.cast_pos (α := ℝ)).mpr (Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := hyp.T))) with h
    exact h
  have hp0 : (0 : ℝ) < (hyp.p : ℝ) := by exact_mod_cast (by omega : 0 < hyp.p)
  have hq10 : (0 : ℝ) < (hyp.q : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (hyp.q : ℝ) := by exact_mod_cast hq3
    linarith
  have hqp0 : (0 : ℝ) < (hyp.q : ℝ) ^ hyp.p := by
    have : (0 : ℝ) < (hyp.q : ℝ) := by exact_mod_cast (by omega : 0 < hyp.q)
    positivity
  have hv0 : (0 : ℝ) < (hyp.v : ℝ) := by exact_mod_cast (by omega : 0 < hyp.v)
  -- Cast the goal to ℝ.
  rw [ge_iff_le, ← Rat.cast_le (K := ℝ)]
  push_cast
  rw [hspec]
  set s : ℝ := ∑ x ∈ hyp.G0Finset, ‖hyp.eta10 x‖ ^ 2 with hsdef
  set sH : ℝ := ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖hyp.eta10 x‖ ^ 2
    with hsHdef
  set sQ : ℝ := ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖hyp.eta10 x‖ ^ 2
    with hsQdef
  rw [nsmul_eq_mul, nsmul_eq_mul] at hsplit
  -- The `TT` value equals `(|T'| − v²)/|T|`.
  set TT : ℝ := 1 / (hyp.p : ℝ) - 1 / ((hyp.p : ℝ) * ((hyp.q : ℝ) - 1))
      + 1 / ((hyp.p : ℝ) * ((hyp.q : ℝ) - 1) * (hyp.q : ℝ) ^ hyp.p) with hTTdef
  have hveq : (hyp.v : ℝ) = ((hyp.q : ℝ) ^ hyp.p - 1) / ((hyp.q : ℝ) - 1) := by
    rw [eq_div_iff hq10.ne']
    exact hvq
  have hTT : TT = ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)
      / (Nat.card ↥hyp.T : ℝ) := by
    rw [hTTdef, hderivT, hTval, hveq]
    have hqp1' : (1 : ℝ) < (hyp.q : ℝ) ^ hyp.p := by
      have h1 : (1:ℕ) < hyp.q ^ hyp.p := by
        calc 1 < hyp.q := by omega
          _ ≤ hyp.q ^ hyp.p := Nat.le_self_pow (by omega) _
      exact_mod_cast h1
    have hnum0 : (hyp.q : ℝ) ^ hyp.p - 1 ≠ 0 := by linarith
    field_simp
    ring
  -- The `HS` term transported to `/|G|`.
  have hH1 : (1 : ℕ) ≤ Nat.card ↥hyp.H := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hterm3 : ((Nat.card ↥hyp.H - 1 : ℕ) : ℝ) / (Nat.card ↥hyp.S : ℝ)
      = (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1) / (Nat.card G : ℝ) := by
    rw [← hSGeq, Nat.cast_sub hH1, Nat.cast_one,
      mul_div_mul_left _ _ hSidx0.ne']
  have hterm4 : TT = (hyp.T.index : ℝ)
      * ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2) / (Nat.card G : ℝ) := by
    rw [hTT, ← hTGeq, mul_div_mul_left _ _ hTidx0.ne']
  -- Assemble.
  have hbound : 1 + s + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1)
      + (hyp.T.index : ℝ) * ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)
      ≤ (Nat.card G : ℝ) := by
    have hHb := mul_le_mul_of_nonneg_left hsharpH hSidx0.le
    have hQb := mul_le_mul_of_nonneg_left hsharpQ hTidx0.le
    nlinarith [hsplit, hone, hHb, hQb]
  rw [hterm3, hterm4]
  have hfinal : (1 + s + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1)
      + (hyp.T.index : ℝ) * ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2))
      / (Nat.card G : ℝ) ≤ 1 := by
    rw [div_le_one hg0]
    exact hbound
  calc 1 / (Nat.card G : ℝ) + s / (Nat.card G : ℝ)
        + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1) / (Nat.card G : ℝ)
        + (hyp.T.index : ℝ) * ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)
          / (Nat.card G : ℝ)
      = (1 + s + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1)
          + (hyp.T.index : ℝ) * ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2))
          / (Nat.card G : ℝ) := by
        rw [add_div, add_div, add_div]
    _ ≤ 1 := hfinal

/-- **Peterfalvi (13.9.a), atom form**: the disjoint-cover counting
`1 = 1/|G| + |G₀|/|G| + |H#|/|S| + |Q#|/|T|` with `|Q#|/|T|` collapsed to its (13.4) value
`(q−1)/(pq^p)`.

Assembled from the ℕ-count `card_univ_split` (the `f = 1` four-piece split over the TI
saturations), Lagrange (`card_mul_index` on `S` and `T`), the `|T|`-decomposition `card_T_eq`,
and the (13.4) values (`lambda_forces_T_caseB`: `D = 1`, `v = (q^p−1)/(q−1)`, `|Q| = q^p`). -/
theorem analyticCounting_disjointCover [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (1 : ℚ) = 1 / (Nat.card G : ℚ) + (hyp.G0Finset.card : ℚ) / (Nat.card G : ℚ)
        + ((Nat.card hyp.H - 1 : ℕ) : ℚ) / (Nat.card hyp.S : ℚ)
        + ((hyp.q : ℚ) - 1) / ((hyp.p : ℚ) * (hyp.q : ℚ) ^ hyp.p) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- (13.4) values.
  obtain ⟨chars⟩ := character_degree_analysis _hG hyp
  obtain ⟨hD, hv, hQ⟩ :=
    lambda_forces_T_caseB _hG chars
  have hd1 : hyp.d = 1 := by rw [hyp.d_eq_card_D, hD, Subgroup.card_bot]
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hp3 : 3 ≤ hyp.p := hyp.three_le_p
  -- `v ≥ 2` (so `vd ≠ 1`, excluding type V in the counting layer).
  have hqp_ge : hyp.q * hyp.q ≤ hyp.q ^ hyp.p := by
    calc hyp.q * hyp.q = hyp.q ^ 2 := (sq hyp.q).symm
      _ ≤ hyp.q ^ hyp.p := Nat.pow_le_pow_right (by omega) (by omega)
  have hv2 : 2 ≤ hyp.v := by
    rw [hv, Nat.le_div_iff_mul_le (by omega : 0 < hyp.q - 1)]
    have h3q : 3 * hyp.q ≤ hyp.q * hyp.q := Nat.mul_le_mul_right _ hq3
    omega
  have hvd : hyp.v * hyp.d ≠ 1 := by rw [hd1, mul_one]; omega
  -- The ℕ-count, cast to ℚ.
  have hsplit := hyp.card_univ_split _hG hQ hvd
  have key : (Nat.card G : ℚ) = 1 + (hyp.G0Finset.card : ℚ)
      + (hyp.S.index : ℚ) * ((Nat.card ↥hyp.H - 1 : ℕ) : ℚ)
      + (hyp.T.index : ℚ) * ((Nat.card ↥hyp.Q - 1 : ℕ) : ℚ) := by
    exact_mod_cast hsplit
  -- Nonvanishing.
  have hG0 : (0 : ℚ) < (Nat.card G : ℚ) := by exact_mod_cast Nat.card_pos (α := G)
  have hS0 : (0 : ℚ) < (Nat.card ↥hyp.S : ℚ) := by exact_mod_cast Nat.card_pos (α := ↥hyp.S)
  have hT0 : (0 : ℚ) < (Nat.card ↥hyp.T : ℚ) := by exact_mod_cast Nat.card_pos (α := ↥hyp.T)
  have hSidx : (hyp.S.index : ℚ) * (Nat.card ↥hyp.S : ℚ) = (Nat.card G : ℚ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.S) hyp.S.index ▸ hyp.S.card_mul_index
  have hTidx : (hyp.T.index : ℚ) * (Nat.card ↥hyp.T : ℚ) = (Nat.card G : ℚ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.T) hyp.T.index ▸ hyp.T.card_mul_index
  have hSidx0 : (hyp.S.index : ℚ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hSidx; exact hG0.ne' hSidx.symm
  have hTidx0 : (hyp.T.index : ℚ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hTidx; exact hG0.ne' hTidx.symm
  -- `v(q−1) = q^p − 1` in ℚ (exact ℕ-division).
  have hq1 : (1 : ℕ) ≤ hyp.q := by omega
  have hqp1 : (1 : ℕ) ≤ hyp.q ^ hyp.p := Nat.one_le_pow _ _ (by omega)
  have hdvd : (hyp.q - 1) ∣ (hyp.q ^ hyp.p - 1) := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow hyp.q 1 hyp.p
  have hvq : (hyp.v : ℚ) * ((hyp.q : ℚ) - 1) = (hyp.q : ℚ) ^ hyp.p - 1 := by
    have h := Nat.div_mul_cancel hdvd
    rw [← hv] at h
    have := congrArg (Nat.cast (R := ℚ)) h
    push_cast [Nat.cast_sub hq1, Nat.cast_sub hqp1] at this
    convert this using 2 <;> push_cast <;> ring
  -- `|T| = q^p·v·p` in ℚ.
  have hTval : (Nat.card ↥hyp.T : ℚ)
      = (hyp.q : ℚ) ^ hyp.p * (hyp.v : ℚ) * (hyp.p : ℚ) := by
    have h := hyp.card_T_eq _hG
    rw [hQ, hd1, mul_one] at h
    exact_mod_cast h
  -- `|Q^#|` in ℚ.
  have hQ1 : ((Nat.card ↥hyp.Q - 1 : ℕ) : ℚ) = (hyp.q : ℚ) ^ hyp.p - 1 := by
    rw [hQ, Nat.cast_sub hqp1]
    push_cast
    ring
  -- Term conversions: `S.index·(|H|−1)/|G| = (|H|−1)/|S|`, and the `Q`-term collapses to the
  -- (13.4) value.
  have hterm3 : ((Nat.card ↥hyp.H - 1 : ℕ) : ℚ) / (Nat.card ↥hyp.S : ℚ)
      = (hyp.S.index : ℚ) * ((Nat.card ↥hyp.H - 1 : ℕ) : ℚ) / (Nat.card G : ℚ) := by
    rw [← hSidx, mul_div_mul_left _ _ hSidx0]
  have hv0 : (hyp.v : ℚ) ≠ 0 := by
    have : (2 : ℚ) ≤ (hyp.v : ℚ) := by exact_mod_cast hv2
    linarith
  have hq10 : (hyp.q : ℚ) - 1 ≠ 0 := by
    have : (3 : ℚ) ≤ (hyp.q : ℚ) := by exact_mod_cast hq3
    linarith
  have hp0 : (hyp.p : ℚ) ≠ 0 := by
    have : (3 : ℚ) ≤ (hyp.p : ℚ) := by exact_mod_cast hp3
    linarith
  have hqp0 : (hyp.q : ℚ) ^ hyp.p ≠ 0 := by
    have : (1 : ℚ) ≤ (hyp.q : ℚ) ^ hyp.p := by exact_mod_cast hqp1
    linarith
  have hterm4 : ((hyp.q : ℚ) - 1) / ((hyp.p : ℚ) * (hyp.q : ℚ) ^ hyp.p)
      = (hyp.T.index : ℚ) * ((Nat.card ↥hyp.Q - 1 : ℕ) : ℚ) / (Nat.card G : ℚ) := by
    rw [hQ1, ← hvq, ← hTidx, hTval]
    field_simp
  -- Assemble.
  rw [hterm3, hterm4, ← add_div, ← add_div, ← add_div, ← key, div_self hG0.ne']

open scoped FiniteInduce in
/-- **The `λ^{τ₁}`-value off the `H^#`-saturation is `±` an `η`-column sum** (Peterfalvi
(13.9.a), first step): `(μ_j − λ)^{τ₁} = Ind_S^G(μ_j − λ)` vanishes off `(H^#)^G` — both are
induced from linear characters of `H = PC` ((13.3.a) via `mu_col_tau1_eta_col_one`), so the
difference is `H^#`-supported — whence `λ^{τ₁}(x) = δ ∑_i η_{i1}(x)` there by the (13.3.c)
column formula. -/
theorem lambda_tau1_apply_eq_of_not_mem_H_sat [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) {x : G}
    (hx : x ∉ OddOrder.GroupTheory.conjClassSet (sharpSubgroup hyp.H)) :
    ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧
      chars.tau1S chars.lambda x
        = (δ : ℂ) * ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x := by
  classical
  obtain ⟨j, δ, θμ, hδ, hθμirr, hθμ1, hμInd, hμτ⟩ := chars.mu_col_tau1_eta_col_one
  obtain ⟨θl, hθlirr, hθl1, hlamEq, -⟩ := chars.lambda_induced_from_PC_linear
  haveI hKnorm : (hyp.H.subgroupOf hyp.S).Normal := H_sharp_subgroupOf_normal hyp
  have hdiff : chars.tau1S (∑ i : Fin hyp.q, hyp.mu i j) - chars.tau1S chars.lambda
      = ClassFunction.induce hyp.S
          (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θμ
            - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θl) := by
    rw [← map_sub, hμInd, hlamEq]
    have h := chars.tau1S_apply_induce_sub θμ θl hθμirr hθlirr
    exact h.trans (by congr! <;> exact Subsingleton.elim _ _)
  have hsupp : ∀ w : ↥hyp.S, (w : G) ∉ sharpSubgroup hyp.H →
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θμ
        - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θl) w = 0 := by
    intro w hw
    rw [ClassFunction.sub_apply]
    by_cases hwH : (w : G) ∈ hyp.H
    · have hw1 : (w : G) = 1 := by
        by_contra hne
        exact hw ⟨hwH, fun h1 => hne (Set.mem_singleton_iff.mp h1)⟩
      have hw1' : w = 1 := Subtype.ext hw1
      subst hw1'
      rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply_one,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθμ1, hθl1, sub_self]
    · rw [OddOrder.RepresentationTheory.ClassFunction.induce_eq_zero_of_not_mem_normal _
          (fun h => hwH (Subgroup.mem_subgroupOf.mp h)),
        OddOrder.RepresentationTheory.ClassFunction.induce_eq_zero_of_not_mem_normal _
          (fun h => hwH (Subgroup.mem_subgroupOf.mp h)), sub_self]
  have hvan : ClassFunction.induce hyp.S
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θμ
        - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θl) x = 0 :=
    OddOrder.GroupTheory.IsTISubset.induce_apply_of_not_mem_conjClassSet _ hsupp hx
  refine ⟨δ, hδ, ?_⟩
  have hdv := congrArg (fun f : ClassFunction G ℂ => f x) hdiff
  simp only [ClassFunction.sub_apply] at hdv
  rw [hvan] at hdv
  have hμv := congrArg (fun f : ClassFunction G ℂ => f x) hμτ
  simp only [ClassFunction.smul_apply, smul_eq_mul,
    OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply] at hμv
  have hlamv : chars.tau1S chars.lambda x = chars.tau1S (∑ i : Fin hyp.q, hyp.mu i j) x :=
    (sub_eq_zero.mp hdv).symm
  exact hlamv.trans hμv

/-- **Peterfalvi (13.9.a), nonvanishing dichotomy**: on the generic set `G₀`, the characters
`λ^{τ₁}` and `η₁₀` do not vanish simultaneously.  Faithful producer of the textbook (13.9.a) —
the character content bottoms out at the (13.3.c) `μ_j^{τ₁} = δ·Σηᵢ₁` formula, the (13.2.e)
support fact for `(μ_j − λ)^τ`, the (3.2.c) regular-value formula, and the (3.9.b)/(3.4) grid
relations forcing `q·η₁₁(x) + 1 = 0` (impossible for an algebraic integer) in the doubly-vanishing
case. -/
theorem G0_nonvanishing_dichotomy [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (chars : CharacterDegreeData hyp) :
    ∀ x ∈ hyp.G0Finset, chars.tau1S chars.lambda x ≠ 0 ∨ hyp.eta10 x ≠ 0 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro x hxF
  have hxG0 : x ∈ hyp.G0 := (Set.Finite.mem_toFinset _).mp hxF
  obtain ⟨hx1, hxH, hxQ⟩ := (hyp.mem_G0_iff x).mp hxG0
  by_cases hreg : x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)))
  · -- regular-conjugate branch: `η₁₀(x) = ω₁₀(w) ≠ 0`
    right
    obtain ⟨w, hwmem, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hreg
    obtain ⟨hwW, hwnot⟩ := hwmem
    have hconjval : hyp.eta10 x = hyp.eta10 w := by
      rw [← hg]
      exact (OddOrder.RepresentationTheory.ClassFunction.of_isConj hyp.eta10
        (isConj_iff.mpr ⟨g, rfl⟩)).symm
    have hval : hyp.eta10 w
        = hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨w, hwW⟩ := by
      rw [show hyp.eta10 = hyp.eta ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ from rfl,
        hyp.eta_eq_tau_omega]
      exact hyp.tau3_apply_of_regular _ _ hwW hwnot
    rw [hconjval, hval]
    intro h0
    have hmul := hyp.omega_mul ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩
      ⟨w, hwW⟩ ⟨w, hwW⟩⁻¹
    rw [mul_inv_cancel, hyp.omega_apply_one, h0, zero_mul] at hmul
    exact one_ne_zero hmul
  · -- doubly-vanishing branch: contradiction via `q·η₀₁(x) = q − 1`
    by_contra hboth
    push Not at hboth
    obtain ⟨hl0, he0⟩ := hboth
    obtain ⟨δ, hδ, hlam⟩ := lambda_tau1_apply_eq_of_not_mem_H_sat _hG chars hxH
    have hδ0 : (δ : ℂ) ≠ 0 := by
      rcases hδ with rfl | rfl <;> norm_num
    have hsum0 : ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x = 0 := by
      have h := hlam.symm.trans hl0
      exact (mul_eq_zero.mp h).resolve_left hδ0
    have he10 : hyp.tau3 (hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩) x = 0 := by
      rw [← hyp.eta_eq_tau_omega]
      exact he0
    have hrow := hyp.eta_row_vanish_of_one_zero x he10
    have hcol1ne : (⟨1, hyp.p_prime.one_lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
      intro h
      exact absurd (congrArg Fin.val h) one_ne_zero
    have hfc : ∀ i : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
        hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x
          = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ x - 1 := by
      intro i hi
      have h4 := hyp.eta_fourcorner_vanish i ⟨1, hyp.p_prime.one_lt⟩ hi hcol1ne x hreg
      rw [hrow i hi] at h4
      rw [hyp.eta_eq_tau_omega, hyp.eta_eq_tau_omega]
      linear_combination h4
    -- split the sum at the `0`-row: `0 = q·η₀₁(x) − (q − 1)`
    have hsplit : (0 : ℂ)
        = (hyp.q : ℂ) * hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
          - ((hyp.q : ℂ) - 1) := by
      have hqpos : 0 < hyp.q := hyp.q_prime.pos
      have hcard : (Finset.univ.erase (⟨0, hqpos⟩ : Fin hyp.q)).card = hyp.q - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      calc (0 : ℂ) = ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x := hsum0.symm
        _ = hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            + ∑ i ∈ Finset.univ.erase (⟨0, hqpos⟩ : Fin hyp.q),
                hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
        _ = hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            + ∑ _i ∈ Finset.univ.erase (⟨0, hqpos⟩ : Fin hyp.q),
                (hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x - 1) := by
          congr 1
          exact Finset.sum_congr rfl (fun i hi =>
            hfc i (Finset.ne_of_mem_erase hi))
        _ = hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            + ((hyp.q - 1 : ℕ) : ℂ)
              * (hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x - 1) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ = (hyp.q : ℂ) * hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            - ((hyp.q : ℂ) - 1) := by
          have h1 : ((hyp.q - 1 : ℕ) : ℂ) = (hyp.q : ℂ) - 1 := by
            rw [Nat.cast_sub hyp.q_prime.one_lt.le, Nat.cast_one]
          rw [h1]
          ring
    -- `η₀₁(x)` is an algebraic integer, so `q ∣ q − 1` — impossible
    have hZ : hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ ∈ ZIrr G := by
      rw [hyp.eta_eq_tau_omega]
      exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ _)
    have hint := OddOrder.Algebra.isIntegral_apply_of_mem_ZIrr hZ x
    have hcast : (((hyp.q : ℤ) - 1 : ℤ) : ℂ)
        = ((hyp.q : ℤ) : ℂ)
          * hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ x := by
      push_cast
      linear_combination hsplit
    have hdvd := OddOrder.RepresentationTheory.int_dvd_of_intCast_eq_mul_isIntegral
      (by exact_mod_cast hyp.q_prime.pos.ne' : (hyp.q : ℤ) ≠ 0) hint hcast
    have hone : (hyp.q : ℤ) ∣ 1 := by
      have h2 : (hyp.q : ℤ) ∣ (hyp.q : ℤ) - ((hyp.q : ℤ) - 1) := dvd_sub dvd_rfl hdvd
      simpa using h2
    have := Int.le_of_dvd one_pos hone
    have := hyp.q_prime.one_lt
    omega

/-- **AM–GM via `log`** (analytic core of [Is] Lemma 3.14): for positive reals whose product is
`≥ 1`, the sum is at least the count.  This powers Peterfalvi (13.9.b): for a cyclic-equivalence
class `[a] = {a^k : gcd(k, |⟨a⟩|) = 1}`, the values `χ(a^k)` are the Galois conjugates of `χ(a)`,
so `∏_k |χ(a^k)|² = |N(χ(a))|² ≥ 1` whenever `χ(a) ≠ 0` (the field norm of a nonzero algebraic
integer is a nonzero rational integer), whence `∑_k |χ(a^k)|² ≥ φ(|⟨a⟩|) = |[a]|`; summing over the
cyclic classes gives `∑_{x∈A}|χ(x)|² ≥ |A|` for any cyclic-closed `A` with `χ ≠ 0` on `A`.
Proof: `log x ≤ x − 1` summed gives `0 ≤ log (∏ f) ≤ ∑ (f − 1) = ∑ f − |s|`. -/
theorem sum_ge_card_of_one_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < f i) (hprod : 1 ≤ ∏ i ∈ s, f i) :
    (s.card : ℝ) ≤ ∑ i ∈ s, f i := by
  have hlog : ∑ i ∈ s, Real.log (f i) ≤ ∑ i ∈ s, (f i - 1) :=
    Finset.sum_le_sum (fun i hi => Real.log_le_sub_one_of_pos (hpos i hi))
  have hprodlog : (0 : ℝ) ≤ ∑ i ∈ s, Real.log (f i) := by
    rw [← Real.log_prod (fun i hi => (hpos i hi).ne')]
    exact Real.log_nonneg hprod
  have hsum : (0 : ℝ) ≤ ∑ i ∈ s, (f i - 1) := le_trans hprodlog hlog
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  linarith

/-- **[Isaacs] Lemma 3.14 (sum form, virtual characters)**: a virtual character nowhere zero on
a cyclic-closed `Finset A` has `∑_{x∈A}‖φ(x)‖² ≥ |A|` — the `ℤ[Irr]` extension of
`sum_normSq_ge_ncard_of_isCharacter_of_cyclicClosed`, combining the Galois product bound
`one_le_prod_normSq_of_mem_ZIrr_of_cyclicClosed` with the AM–GM `sum_ge_card_of_one_le_prod`
(declared below; the two are independent). -/
theorem sum_normSq_ge_card_of_mem_ZIrr_of_cyclicClosed {H : Type*} [Group H] [Finite H]
    {φ : ClassFunction H ℂ} (hφ : φ ∈ ZIrr H) {A : Finset H}
    (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card H) → x ^ k ∈ A)
    (hne : ∀ x ∈ A, φ x ≠ 0) :
    (A.card : ℝ) ≤ ∑ x ∈ A, ‖φ x‖ ^ 2 :=
  sum_ge_card_of_one_le_prod A (fun x => ‖φ x‖ ^ 2)
    (fun x hx => pow_pos (norm_pos_iff.mpr (hne x hx)) 2)
    (OddOrder.Algebra.one_le_prod_normSq_of_mem_ZIrr_of_cyclicClosed hφ hclosed hne)

/-- **The nonvanishing locus of a virtual character inside a cyclic-closed set is cyclic-closed**
(Peterfalvi (1.9.b)): for `k` coprime to `|G|` there is `σ : ℂ ≃+* ℂ` with `σ(φ(x)) = φ(x^k)`
(`exists_complexRingEquiv_mapRingEquiv_eq_pow` with `a = |G|`, `b = 1`), and ring automorphisms
preserve nonvanishing. -/
theorem filter_ne_zero_cyclicClosed [Finite G] {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    {A : Finset G} (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card G) → x ^ k ∈ A) :
    ∀ x ∈ A.filter (fun y => φ y ≠ 0), ∀ k : ℕ, k.Coprime (Nat.card G) →
      x ^ k ∈ A.filter (fun y => φ y ≠ 0) := by
  classical
  intro x hx k hk
  obtain ⟨hxA, hxne⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hclosed x hxA k hk, ?_⟩
  obtain ⟨σ, hσ⟩ := OddOrder.RepresentationTheory.exists_complexRingEquiv_mapRingEquiv_eq_pow G
    (a := Nat.card G) (b := 1) (mul_one _).symm (Nat.coprime_one_right _) hk
  have hval : ClassFunction.mapRingEquiv σ φ x = φ (x ^ k) :=
    (hσ hφ x).1 (orderOf_dvd_natCard x)
  rw [ClassFunction.mapRingEquiv_apply] at hval
  rw [← hval]
  simpa using hxne

open scoped FiniteInduce in
/-- **Peterfalvi (13.9.b), atom form**: `|G₀|/|G| ≤ slam + seta`.

`G₀ = A ∪ B` with `A`/`B` the nonvanishing loci of `λ^{τ₁}`/`η₁₀`
(`G0_nonvanishing_dichotomy` = (13.9.a)); each locus is cyclic-closed
(`filter_ne_zero_cyclicClosed`, Pf (1.9.b)), so [Is] Lemma 3.14
(`sum_normSq_ge_card_of_mem_ZIrr_of_cyclicClosed`) bounds its cardinality by the norm sum. -/
theorem analyticEstimate_galois [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (chars : CharacterDegreeData hyp) :
    (hyp.G0Finset.card : ℚ) / (Nat.card G : ℚ)
      ≤ normSqSumQ hyp.G0Finset (chars.tau1S chars.lambda) / (Nat.card G : ℚ)
        + normSqSumQ hyp.G0Finset hyp.eta10 / (Nat.card G : ℚ) := by
  classical
  obtain ⟨hZlam, -, -⟩ := lambda_tau1_norm_one _hG chars
  have hZeta := hyp.eta10_mem_ZIrr
  set φ : ClassFunction G ℂ := chars.tau1S chars.lambda with hφdef
  set A : Finset G := hyp.G0Finset.filter (fun y => φ y ≠ 0) with hA
  set B : Finset G := hyp.G0Finset.filter (fun y => hyp.eta10 y ≠ 0) with hB
  -- The dichotomy: `G₀ ⊆ A ∪ B`.
  have hdich := G0_nonvanishing_dichotomy _hG chars
  have hcover : hyp.G0Finset ⊆ A ∪ B := by
    intro x hx
    rcases hdich x hx with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, by rw [← hφdef] at h; exact h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h⟩)
  have hcard : hyp.G0Finset.card ≤ A.card + B.card :=
    le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
  -- Per-locus Galois bounds.
  have hgeA : (A.card : ℝ) ≤ ∑ x ∈ A, ‖φ x‖ ^ 2 :=
    sum_normSq_ge_card_of_mem_ZIrr_of_cyclicClosed hZlam
      (filter_ne_zero_cyclicClosed hZlam hyp.G0Finset_cyclicClosed)
      (fun x hx => (Finset.mem_filter.mp hx).2)
  have hgeB : (B.card : ℝ) ≤ ∑ x ∈ B, ‖hyp.eta10 x‖ ^ 2 :=
    sum_normSq_ge_card_of_mem_ZIrr_of_cyclicClosed hZeta
      (filter_ne_zero_cyclicClosed hZeta hyp.G0Finset_cyclicClosed)
      (fun x hx => (Finset.mem_filter.mp hx).2)
  -- Locus sums are bounded by the `G₀` sums.
  have hsubA : ∑ x ∈ A, ‖φ x‖ ^ 2 ≤ ∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => by positivity)
  have hsubB : ∑ x ∈ B, ‖hyp.eta10 x‖ ^ 2 ≤ ∑ x ∈ hyp.G0Finset, ‖hyp.eta10 x‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => by positivity)
  -- The rational atoms.
  have hspecLam := normSqSumQ_spec
    (OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZlam
      hyp.G0Finset_cyclicClosed)
  have hspecEta := normSqSumQ_spec
    (OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZeta
      hyp.G0Finset_cyclicClosed)
  -- Assemble over ℝ.
  have hg0 : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  rw [← Rat.cast_le (K := ℝ)]
  push_cast
  rw [hspecLam, hspecEta, ← add_div]
  have hnum : (hyp.G0Finset.card : ℝ)
      ≤ (∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2) + ∑ x ∈ hyp.G0Finset, ‖hyp.eta10 x‖ ^ 2 := by
    have hcard' : (hyp.G0Finset.card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by
      exact_mod_cast hcard
    linarith [hgeA, hgeB, hsubA, hsubB]
  gcongr


/-- **Faithful (13.6)–(13.9) norm-estimate inputs to Peterfalvi (13.10)**.

The four estimates are the genuine character-theoretic / counting outputs of the norm cascade,
stated for the real atoms `slam = (1/|G|)·Σ_{G₀}‖λ^{τ₁}‖²`, `seta = (1/|G|)·Σ_{G₀}‖η₁₀‖²`,
`g0 = |G₀|/|G|`, `HS = |H#|/|S|` (with the (13.4) counting values `LS = uq/(cp^q)`,
`TT = 1/p − 1/(p(q−1)) + 1/(p(q−1)q^p)`, `QT = (q−1)/(pq^p)` substituted):

* `h1` — **(13.6)**: Parseval for `λ^{τ₁}` (`‖λ^{τ₁}‖² = 1`) with the norm bound
  `Σ_{H#}‖λ^{τ₁}‖² ≥ |S| − λ(1)²` (`caseB_lambda_norm_bound`);
* `h2` — **(13.7)+(13.8)** for `T` with `D = 1` (`caseB_eta_norm_bound`, `caseB_eta01_norm_core`);
* `h3` — **(13.9.a)**: the disjoint-union cover `G = {1} ⊔ G₀ ⊔ (H#)^G ⊔ (Q#)^G`;
* `h139b` — **(13.9.b)**: the Galois-integrality bound `|G₀|/|G| ≤ slam + seta`
  (`sum_ge_card_of_one_le_prod`).

Assembled `sorry`-free from the four named producers above (which carry the residual gates —
see their header).  The pure arithmetic that turns the four estimates into the `u/c` bound is
the `sorry`-free `analytic_inequality_arith`. -/
theorem analyticInequalityEstimates [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ slam seta g0 HS : ℚ,
      (1 : ℚ) ≥ 1 / (Nat.card G : ℚ) + slam + 1
          - (hyp.u : ℚ) * (hyp.q : ℚ) / ((hyp.c : ℚ) * (hyp.p : ℚ) ^ hyp.q) ∧
        (1 : ℚ) ≥ 1 / (Nat.card G : ℚ) + seta + HS
          + (1 / (hyp.p : ℚ) - 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1))
            + 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1) * (hyp.q : ℚ) ^ hyp.p)) ∧
        (1 : ℚ) = 1 / (Nat.card G : ℚ) + g0 + HS
          + ((hyp.q : ℚ) - 1) / ((hyp.p : ℚ) * (hyp.q : ℚ) ^ hyp.p) ∧
        g0 ≤ slam + seta := by
  obtain ⟨chars⟩ := character_degree_analysis _hG hyp
  exact ⟨normSqSumQ hyp.G0Finset (chars.tau1S chars.lambda) / (Nat.card G : ℚ),
    normSqSumQ hyp.G0Finset hyp.eta10 / (Nat.card G : ℚ),
    (hyp.G0Finset.card : ℚ) / (Nat.card G : ℚ),
    ((Nat.card hyp.H - 1 : ℕ) : ℚ) / (Nat.card hyp.S : ℚ),
    analyticEstimate_lambda _hG hyp chars,
    analyticEstimate_eta _hG hyp,
    analyticCounting_disjointCover _hG hyp,
    analyticEstimate_galois _hG hyp chars⟩


/-- **Peterfalvi (13.9.b) core** ([Is] Lemma 3.14, sum form): for a character `φ` that is nowhere
zero on a cyclic-closed `Finset A` (closed under `x ↦ x ^ k`, `k` coprime `|G|`), the squared-norm
sum over `A` is at least `|A|`.  Combines the Galois-integrality product bound
`one_le_prod_normSq_character_of_cyclicClosed` (`∏_{x∈A} ‖φ(x)‖² ≥ 1`, since the product of the
Galois conjugates is a nonzero rational integer) with the AM–GM `sum_ge_card_of_one_le_prod`.
This is the per-cyclic-class building block for the (13.9.b) bound `|G₀|/|G| ≤ slam + seta` in the
(13.10) analytic inequality (applied on each class to whichever of `λ^{τ₁}`, `η₁₀` is nonzero). -/
theorem sum_normSq_ge_ncard_of_isCharacter_of_cyclicClosed {H : Type*} [Group H] [Finite H]
    {φ : ClassFunction H ℂ} (hφ : OddOrder.RepresentationTheory.IsCharacter φ) {A : Finset H}
    (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card H) → x ^ k ∈ A)
    (hne : ∀ x ∈ A, φ x ≠ 0) :
    (A.card : ℝ) ≤ ∑ x ∈ A, ‖φ x‖ ^ 2 :=
  sum_ge_card_of_one_le_prod A (fun x => ‖φ x‖ ^ 2)
    (fun x hx => pow_pos (norm_pos_iff.mpr (hne x hx)) 2)
    (OddOrder.Algebra.one_le_prod_normSq_character_of_cyclicClosed hφ hclosed hne)

/-- **Peterfalvi (13.10), arithmetic core** (04.15 pp.85–86): the (13.6)–(13.9) norm estimates
together with the disjoint-union counting `G = {1} ⊔ G₀ ⊔ (H#)^G ⊔ (Q#)^G` and the (13.4) counting
identities force `u / c > m p^(q-1) / q`.

This is the faithful Lean encoding of Peterfalvi (13.10)'s derivation, with the **grid-dependent
character content fully isolated** into the concrete norm-sum hypotheses (the (13.6)/(13.7)/(13.8)
outputs and the (13.9.b) cover, to be supplied by the cascade producers once the grid τ-isometry /
orthogonality is carried) and the **group-counting identities** `hLS`/`hTT`/`hQT`.  No grid carrier
is needed here: this is a `sorry`-free reusable arithmetic lemma.  The abstract real atoms are
`gi = 1/|G|`, `slam = (1/|G|)·Σ_{G₀}|λ^{τ₁}(x)|²`, `seta = (1/|G|)·Σ_{G₀}|η₁₀(x)|²`,
`g0 = |G₀|/|G|`, `LS = λ(1)²/|S|`, `HS = |H#|/|S|`, `TT = (|T'|−v²)/|T|`, `QT = |Q#|/|T|`.

* `h1` — (13.10.1): `1 ≥ 1/|G| + (1/|G|)Σ_{G₀}|λ^{τ₁}|² + 1 − λ(1)²/|S|` (Parseval + (13.6));
* `h2` — (13.10.2): `1 ≥ 1/|G| + (1/|G|)Σ_{G₀}|η₁₀|² + |H#|/|S| + (|T'|−v²)/|T|`
  (Parseval + (13.7) + (13.8) for `T`, `D = 1`);
* `h3` — (13.10.3): the disjoint-union counting `1 = 1/|G| + |G₀|/|G| + |H#|/|S| + |Q#|/|T|`;
* `h139b` — (13.9.b): `|G₀|/|G| ≤ (1/|G|)(Σ_{G₀}|λ^{τ₁}|² + Σ_{G₀}|η₁₀|²)`.

**Stage A** (`linarith`): combining `h1 + h2 − h3` with `h139b` and `gi > 0` gives `LS > TT − QT`.
**Stage B**: the counting identities collapse `TT − QT` to `m/p`, and factoring out `q/p^q > 0`
turns `uq/(cp^q) > m/p` into `u/c > m p^(q-1)/q`. -/
theorem analytic_inequality_arith {p q u c : ℕ} {m gi slam seta g0 LS HS TT QT : ℚ}
    (hp2 : 2 ≤ p) (hq2 : 2 ≤ q) (hc0 : 0 < c)
    (h1 : 1 ≥ gi + slam + 1 - LS)
    (h2 : 1 ≥ gi + seta + HS + TT)
    (h3 : 1 = gi + g0 + HS + QT)
    (h139b : g0 ≤ slam + seta)
    (hgi : 0 < gi)
    (hLS : LS = ((u : ℚ) * (q : ℚ)) / ((c : ℚ) * (p : ℚ) ^ q))
    (hTT : TT = 1 / (p : ℚ) - 1 / ((p : ℚ) * ((q : ℚ) - 1))
      + 1 / ((p : ℚ) * ((q : ℚ) - 1) * (q : ℚ) ^ p))
    (hQT : QT = ((q : ℚ) - 1) / ((p : ℚ) * (q : ℚ) ^ p))
    (hm : m = 1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
      + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p)) :
    (u : ℚ) / (c : ℚ) > m * ((p : ℚ) ^ (q - 1)) / (q : ℚ) := by
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (show 0 < p by omega)
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (show 0 < q by omega)
  have hcQ : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hc0
  have hq1 : (0 : ℚ) < (q : ℚ) - 1 := by
    have h2q : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq2
    linarith
  have hqpowp : (0 : ℚ) < (q : ℚ) ^ p := by positivity
  have hppow1 : (0 : ℚ) < (p : ℚ) ^ (q - 1) := by positivity
  have hppowq : (0 : ℚ) < (p : ℚ) ^ q := by positivity
  -- Stage A: the (13.10.1)+(13.10.2)−(13.10.3)+(13.9.b) combination gives `LS > TT − QT`.
  have hStageA : LS > TT - QT := by linarith
  -- Stage B: the counting identities collapse `TT − QT` to `m / p`.
  have hTTQT : TT - QT = m / (p : ℚ) := by
    rw [hTT, hQT, hm]
    field_simp
    ring
  rw [hTTQT, hLS] at hStageA
  -- `hStageA : u q / (c p^q) > m / p`.  Factor out the positive `q / p^q`.
  have hpexp : (p : ℚ) ^ q = (p : ℚ) ^ (q - 1) * (p : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  have hfac : (0 : ℚ) < (q : ℚ) / (p : ℚ) ^ q := by positivity
  have e1 : ((u : ℚ) * (q : ℚ)) / ((c : ℚ) * (p : ℚ) ^ q)
      = ((u : ℚ) / (c : ℚ)) * ((q : ℚ) / (p : ℚ) ^ q) := by
    field_simp
  have e2 : m / (p : ℚ)
      = (m * ((p : ℚ) ^ (q - 1)) / (q : ℚ)) * ((q : ℚ) / (p : ℚ) ^ q) := by
    rw [hpexp]
    field_simp
  rw [e1, e2] at hStageA
  exact lt_of_mul_lt_mul_right hStageA (le_of_lt hfac)

/-- **Peterfalvi (13.10)**: the norm estimates imply `u / c > m p^(q-1) / q`.

The real inequality conclusion is discharged `sorry`-free from `analytic_inequality_arith` fed by
the faithful (13.6)–(13.9) estimates `analyticInequalityEstimates`; the opaque `NormCascadeData`
scaffold flags carry `True`. -/
theorem analytic_inequality [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : NormCascadeData hyp,
      data.analytic_inequality ∧
        (hyp.u : ℚ) / (hyp.c : ℚ) >
          hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ) := by
  obtain ⟨chars⟩ := character_degree_analysis _hG hyp
  obtain ⟨slam, seta, g0, HS, h1, h2, h3, h139b⟩ := analyticInequalityEstimates _hG hyp
  have hc0 : 0 < hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
  have hgi : (0 : ℚ) < 1 / (Nat.card G : ℚ) := by
    have : 0 < Nat.card G := Nat.card_pos
    positivity
  have hpq : ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) = (hyp.p : ℚ) ^ (hyp.q - 1) := by push_cast; ring
  refine ⟨{ chars := chars
            lambda_norm_lower := True
            eta10_norm_lower := True
            eta01_norm_lower := True
            global_cover := True
            global_norm_lower := True
            analytic_inequality := True }, trivial, ?_⟩
  rw [hpq]
  exact analytic_inequality_arith hyp.p_prime.two_le hyp.q_prime.two_le hc0
    h1 h2 h3 h139b hgi rfl rfl rfl hyp.m_eq

end OddOrder.Peterfalvi.S15
