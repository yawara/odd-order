import OddOrder.Peterfalvi.S15_SAndT_Setup.CountingLayer

/-!
# Canonicalization

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT_Setup.NormEstimates` (2000-line limit, issue 0103 第 2 パス).
-/

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
  exact chars.tau1S_induce_inner_eta i j θl hθlirr (hlamEq ▸ chars.lambda_irreducible)

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
    have h := chars.tau1S_induce_inner_eta_col_zero ⟨1, hyp.q_prime.one_lt⟩ _ θ.2
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

end OddOrder.Peterfalvi.S15
