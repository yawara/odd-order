/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_ComplementStructure

/-!
# Peterfalvi §15 — the bridge character: opening layer

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
-/

namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


/-- Carrier for the virtual character `beta_j` and `Gamma_j` in Peterfalvi (13.18).

**De-opacified (W3 §15); faithful to Peterfalvi (13.18) after the issue-3003 correction.**  This
carrier previously held six free `_formula : Prop` placeholders (the
[[scaffold-sorry-free-not-done]] convention).  Since `BetaData` has no external consumers (only
`beta_support_norm_and_remainder` produces it), the fields are now the **genuine Peterfalvi (13.18)
statements** about `β_j`/`Γ`, tied to `hyp`, the grid `hyp.eta`, and `S`:

* `support_formula` — **(13.18.a)** the support of `β_j` is contained in `S`'s η-carrier support;
* `norm_formula` — **(13.18.b)** `‖β_j‖²_S = (u−1)/q + 2` (its Frobenius `Ind` half is the
sorry-free
  `norm_induce_one_frobenius`);
* `Gamma_orthogonal_one` — **(13.18.c)** `(Γ, 1_G) = 0`, the residual is orthogonal to the
principal;
* `Gamma_real` — **(13.18.c)** `Γ` is real (`Γ.conj = Γ`);
* `Y_norm_bound` — **(13.18.d)** for any split `Γ = X + Y` (`X ⊥ Y`, `Y ⊥` grid), `‖Y‖² ≤ (u−1)/q`.

The remaining half of **(13.18.c)** — `Γ`'s `j`-independence (`defGamma`) — is the standalone proven
`gammaGrid_defGamma` (not a field here, to keep the `FiniteInduce` `τ_S` instances out of this
structure's explicit inner-product binders).  ⚠ The **removed** fields `Gamma_independent`
(`⟨Γ,η_ik⟩ = 0`) and the old `Y_norm_bound` (`‖Γ‖² ≤ (u−1)/q + 1`) were **overstatements** —
(13.18.c)
says `Γ` is independent of `j`, not grid-orthogonal, and (13.18.d) bounds the grid-orthogonal part
`Y`, not `‖Γ‖²` (issue 3003).

The genuine grid/Dade content bottoms out at the (3.2) τ-isometry (`tau3`, σ-pinned 2026-06-15) and
the (13.18.b) Frobenius norm; it is isolated into the single faithful producer
`betaData_of_grid`. -/
structure BetaData (hyp : Hypothesis (G := G)) where
  j : Fin hyp.p
  j_ne_zero : (j : ℕ) ≠ 0
  beta : ClassFunction ↥hyp.S ℂ
  Gamma : ClassFunction G ℂ
  /-- **(13.18.a)** support control: `β_j ∈ CF(S, P^# ∪ V_S)` — the Coq-faithful exact carrier
  (`PVSbeta`).  (The previous grid form `supp(β_j) ⊆ ⋃ᵢ supp(μ_{ij})` was an unfaithful
  restate; issue-3003 pattern.) -/
  support_formula : beta.support ⊆
    {z : ↥hyp.S |
      (z : G) ∈ OddOrder.GroupTheory.sharpSubgroup hyp.P ∪
        OddOrder.GroupTheory.conjClassSetIn hyp.S
          (OddOrder.GroupTheory.typePV hyp.S hyp.Sdata)}
  /-- **(13.18.b)** norm: `‖β_j‖²_S = (u−1)/q + 2`, whose `Ind_{PW₁}^S 1` half is
  `norm_induce_one_frobenius`. -/
  norm_formula :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner beta beta
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ)
  /-- **(13.18)** `Γ_j` is orthogonal to the principal character `1_G` (part of (13.18.c)). -/
  Gamma_orthogonal_one :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ClassFunction.inner Gamma (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0
  /-- **(13.18.c)** `Γ_j` is a real virtual character. -/
  Gamma_real : Gamma.conj = Gamma
  /-- **(13.18.d)** residual-norm bound: for any split `Γ = X + Y` with `X ⊥ Y` and `Y` orthogonal
  to the whole `η`-grid, `‖Y‖² ≤ (u−1)/q`.  This is the genuine (13.18.d) feeding the (14.14)
  case-`(c1)`/`(c2)` orthogonality switch.  (The previous field `‖Γ‖² ≤ (u−1)/q + 1` was **not**
  this statement — an overstatement, since `‖Γ‖² = ‖X‖² + ‖Y‖²` with `X` the nonzero grid-component;
  see issue 3003.  The (13.18.c) `j`-independence half is the standalone `gammaGrid_defGamma`.) -/
  Y_norm_bound :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (X Y : ClassFunction G ℂ), Gamma = X + Y → ClassFunction.inner X Y = 0 →
        (∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) →
        (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ)

/-- **`U ⋊ W₁` complements `P` in `S`** (structural bridge for (13.18.b), `S`-side form).  From the
`Sdata` complements `M' ⋊ W₁ = S` and `P ⋊ U = M'`, the subgroup `U ⊔ W₁` intersects `P = S_F`
trivially and joins with it to `S`.  This is the `↥S`-internal `IsComplement'` behind the Frobenius
quotient `S̄ = S/P ≅ U ⋊ W₁` used to evaluate `‖Ind_{PW₁}^S 1‖²`.  (Re-derived here in the (13.18)
carve-out rather than exposed from `coprime_card_P_card_UW1`, whose derivation it mirrors.) -/
theorem uW1_isComplement_P [Finite G] (hyp : Hypothesis (G := G)) :
    Subgroup.IsComplement' ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) (hyp.P.subgroupOf hyp.S) := by
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hU_le_M' : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have hP_le_S : hyp.P ≤ hyp.S := hP_le_M'.trans hM'_le_S
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hUW1_le_S : hyp.U ⊔ hyp.W1 ≤ hyp.S := sup_le (hU_le_M'.trans hM'_le_S) hW1_le_S
  have hdisj : hyp.P ⊓ hyp.U = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.derived_complement.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxH, hxU⟩
    have hxD : x ∈ derivedInG hyp.S := hyp.Sdata.H_le (by rwa [hyp.Sdata.H_eq, ← hyp.P_eq_SF])
    have hmem : (⟨x, hxD⟩ : ↥(derivedInG hyp.S)) ∈
        (hyp.Sdata.H.subgroupOf (derivedInG hyp.S)) ⊓ (hyp.Sdata.U.subgroupOf (derivedInG hyp.S)) :=
      ⟨Subgroup.mem_subgroupOf.mpr (by rwa [hyp.Sdata.H_eq, ← hyp.P_eq_SF]),
        Subgroup.mem_subgroupOf.mpr (hyp.Sdata_U_eq ▸ hxU)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  have hM'W1 : derivedInG hyp.S ⊓ hyp.W1 = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.M_complement.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxM', hxW1⟩
    have hxS : x ∈ hyp.S := hM'_le_S hxM'
    have hmem : (⟨x, hxS⟩ : ↥hyp.S) ∈
        ((derivedInG hyp.S).subgroupOf hyp.S) ⊓ (hyp.Sdata.W1.subgroupOf hyp.S) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxM', Subgroup.mem_subgroupOf.mpr (hyp.Sdata_W1_eq ▸ hxW1)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  have hSsup : hyp.P ⊔ (hyp.U ⊔ hyp.W1) = hyp.S := by
    have htop := hyp.Sdata.M_complement.sup_eq_top
    have hmap := congrArg (Subgroup.map hyp.S.subtype) htop
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hM'_le_S,
      Subgroup.map_subgroupOf_eq_of_le hyp.Sdata.W1_le, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
    rw [hyp.Sdata_W1_eq, hyp.S_deriv_eq_PU] at hmap
    rw [← sup_assoc]; exact hmap
  have hPUW1_disj : hyp.P ⊓ (hyp.U ⊔ hyp.W1) = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hxP, hxUW1⟩ := Subgroup.mem_inf.mp hx
    have hxUW1' : (x : G) ∈ (↑(hyp.U ⊔ hyp.W1) : Set G) := hxUW1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left hyp.U hyp.W1 hyp.W1_normalizes_U] at hxUW1'
    obtain ⟨u, hu, w, hw, huw⟩ := Set.mem_mul.mp hxUW1'
    have hwM' : w ∈ derivedInG hyp.S := by
      have : w = u⁻¹ * x := by rw [← huw]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hU_le_M' (SetLike.mem_coe.mp hu)))
        (hP_le_M' hxP)
    have hw1 : w = 1 := by
      have : w ∈ derivedInG hyp.S ⊓ hyp.W1 := Subgroup.mem_inf.mpr ⟨hwM', SetLike.mem_coe.mp hw⟩
      rwa [hM'W1, Subgroup.mem_bot] at this
    have hxu : x = u := by rw [← huw, hw1, mul_one]
    have hxPU : x ∈ hyp.P ⊓ hyp.U := Subgroup.mem_inf.mpr ⟨hxP, hxu ▸ SetLike.mem_coe.mp hu⟩
    rwa [hdisj, Subgroup.mem_bot] at hxPU
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff, eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hy
    have hyPU : (y : G) ∈ hyp.P ⊓ (hyp.U ⊔ hyp.W1) := ⟨hy.2, hy.1⟩
    rw [hPUW1_disj, Subgroup.mem_bot] at hyPU
    rw [Subgroup.mem_bot]; exact Subtype.ext hyPU
  · have hsup : ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) ⊔ (hyp.P.subgroupOf hyp.S) = ⊤ := by
      rw [sup_comm, ← Subgroup.subgroupOf_sup hP_le_S hUW1_le_S, hSsup, Subgroup.subgroupOf_self]
    rw [← Subgroup.mul_normal, hsup, Subgroup.coe_top]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The induced trivial character** `Ind_{P⋊W₁}^S(1)` of the subgroup `P ⋊ W₁ ≤ S`, the
positive part of the (13.18) bridge character `β_j`.  Its squared `S`-norm is the Frobenius
value `(u−1)/q + 1` (`norm_induce_one_frobenius` composed with the `S̄ = S/P = U⋊W₁` inflation). -/
noncomputable def indPW1 [Finite G] (hyp : Hypothesis (G := G)) : ClassFunction ↥hyp.S ℂ :=
  ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
    (trivialClassFunction ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S))

/-- **Peterfalvi (13.18) `S`-side virtual character** `β_j := Ind_{P⋊W₁}^S(1) − μ_{0j}`
(Coq `PFsection13.FTtypeP_bridge`).  The induced trivial character `indPW1 hyp` of `P ⋊ W₁ ≤ S`
minus the base-row grid irreducible `μ_{0j} = hyp.mu 0 j`. -/
noncomputable def betaGrid [Finite G] (hyp : Hypothesis (G := G)) (j : Fin hyp.p) :
    ClassFunction ↥hyp.S ℂ :=
  indPW1 hyp - hyp.mu ⟨0, hyp.q_prime.pos⟩ j

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The genuine `S`-side Dade image** `τ_S(β_{#1})` of the (13.18) bridge character at column
`#1`.  Uses the honest (13.2.e) Dade isometry `τ_S = dadeIntegralCharacterMap (hyp.dadeHypS0 hG) …`
— the `S`-instance of the (5.3) Dade map — **NOT** the off-path `= 0` placeholder `hyp.tauS`. -/
noncomputable def tauSbetaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ClassFunction G ℂ :=
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG))
    (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.18) residual** `Γ := τ_S(β_{#1}) − 1_G + η_{01}` (Coq
`PFsection13.FTtypeP_bridge_gap`).  `η_{01} = hyp.eta 0 1` is the (3.3) grid image `τ₃(ω_{01})`;
`1_G = constOne G`.  Note `Γ` does not depend on the column `j` of `βData`. -/
noncomputable def GammaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ClassFunction G ℂ :=
  tauSbetaGrid hG hyp - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
    + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.18.a), `[S : PW₁] = u`** (`S15` home; a copy temporarily also lives in
`S16_NonExistenceG/TGapCross` — redirect tracked cross-lane).  The index is read from
`|S| = p^q·u·q` and `|P W₁| = |P|·|W₁| = p^q·q`.  This is the degree of the permutation
character `Ind_{PW₁}^S 1`. -/
theorem PW1_index_eq_u_of_c_eq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).index = hyp.u := by
  have hD_le_S : OddOrder.GroupTheory.derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_D : hyp.P ≤ OddOrder.GroupTheory.derivedInG hyp.S := by
    rw [hyp.S_deriv_eq_PU]
    exact le_sup_left
  have hP_le_S : hyp.P ≤ hyp.S := hP_le_D.trans hD_le_S
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hW1norm : hyp.W1 ≤ Subgroup.normalizer (hyp.P : Set G) := hW1_le_S.trans hS_norm_P
  have hDW1 : OddOrder.GroupTheory.derivedInG hyp.S ⊓ hyp.W1 = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.M_complement.disjoint
    rw [eq_bot_iff]
    rintro x ⟨hxD, hxW1⟩
    have hxS : x ∈ hyp.S := hD_le_S hxD
    have hmem : (⟨x, hxS⟩ : ↥hyp.S) ∈
        ((OddOrder.GroupTheory.derivedInG hyp.S).subgroupOf hyp.S) ⊓
          (hyp.Sdata.W1.subgroupOf hyp.S) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxD,
        Subgroup.mem_subgroupOf.mpr (hyp.Sdata_W1_eq ▸ hxW1)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    simpa using Subtype.ext_iff.mp hmem
  have hPW1disj : Disjoint hyp.P hyp.W1 :=
    (disjoint_iff.mpr hDW1).mono hP_le_D (le_refl hyp.W1)
  have hcardPW1 : Nat.card ↥(hyp.P ⊔ hyp.W1) = hyp.p ^ hyp.q * hyp.q := by
    rw [sup_comm, OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint
      hW1norm (disjoint_iff.mp hPW1disj.symm),
      hyp.card_P_eq hG hyp.Sdata_W2_eq, ← hyp.q_eq_card_W1]
    exact Nat.mul_comm hyp.q (hyp.p ^ hyp.q)
  have hcardPW1S : Nat.card ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S) =
      hyp.p ^ hyp.q * hyp.q := by
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (sup_le hP_le_S hW1_le_S)).toEquiv, hcardPW1]
  have hm := Subgroup.card_mul_index ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
  rw [hcardPW1S, hyp.card_S_val hG, hc1, mul_one] at hm
  have hpos : 0 < hyp.p ^ hyp.q * hyp.q :=
    mul_pos (pow_pos hyp.p_prime.pos hyp.q) hyp.q_prime.pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    (hyp.p ^ hyp.q * hyp.q) * ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).index
        = hyp.p ^ hyp.q * (hyp.u * hyp.q) := by simpa [mul_assoc] using hm
    _ = (hyp.p ^ hyp.q * hyp.q) * hyp.u := by ring

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.18.a), the bridge character vanishes at `1`**: `β_j(1) = 0` — the two
degrees agree, `Ind_{PW₁}^S 1 (1) = [S:PW₁] = u = μ_{0j}(1)` (`PW1_index_eq_u`,
`mu_apply_one_eq_u`). -/
theorem betaGrid_apply_one_eq_zero_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    betaGrid hyp j 1 = 0 := by
  have hj0 : j ≠ ⟨0, hyp.p_prime.pos⟩ := fun h => hj (by simp [h])
  rw [betaGrid, OddOrder.RepresentationTheory.ClassFunction.sub_apply, indPW1,
    ClassFunction.induce_apply_one, PW1_index_eq_u_of_c_eq_one hG hyp hc1,
    trivialClassFunction_apply,
    mul_one, hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩ j hj0, sub_self]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.b), Frobenius half** (`FiniteInduce`-instance form):
`‖Ind_{PW₁}^S 1‖²_S = (u−1)/q + 1`.
The wrapper `indPW1_inner_self` bridges to arbitrary `Fintype`/`Invertible` instances. -/
private theorem indPW1_inner_self_aux [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
      ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) := by
  classical
  -- Structural setup: `U ⋊ W₁` complements `P` in `S`.
  have hcompl := uW1_isComplement_P hyp
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hP_le_S : hyp.P ≤ hyp.S := hP_le_M'.trans hM'_le_S
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hU_le_M' : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have hUW1_le_S : hyp.U ⊔ hyp.W1 ≤ hyp.S := sup_le (hU_le_M'.trans hM'_le_S) hW1_le_S
  have hW1_le_UW1 : hyp.W1 ≤ hyp.U ⊔ hyp.W1 := le_sup_right
  have hW1_le_PW1 : hyp.W1 ≤ hyp.P ⊔ hyp.W1 := le_sup_right
  have hP_le_PW1 : hyp.P ≤ hyp.P ⊔ hyp.W1 := le_sup_left
  have hPW1_le_S : hyp.P ⊔ hyp.W1 ≤ hyp.S := sup_le hP_le_S hW1_le_S
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  have hNA : hyp.P.subgroupOf hyp.S ≤ (hyp.P ⊔ hyp.W1).subgroupOf hyp.S :=
    Subgroup.comap_mono hP_le_PW1
  -- Step 1: `indPW1 = (Ind_{Ā}^{S̄} 1) ∘ mk'`, so its `S`-norm equals the `S̄`-norm (P2 + P1).
  rw [show indPW1 hyp = ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
        (trivialClassFunction _) from rfl,
    OddOrder.RepresentationTheory.induce_one_eq_compHom_induce_one_of_le hNA,
    OddOrder.RepresentationTheory.inner_compHom_mk'_eq]
  -- Step 2: `S̄ = S/P` is Frobenius via the iso `e : ↥(U⊔W₁) ≃* S̄`.
  -- The `U ⋊ W₁` Frobenius, read off `Sdata` sorry-free (`typeP_uW1_frobenius`), avoiding the
  -- §16-gated `basic_structure` so this stays honestly sorry-free.
  have hSdataUne : hyp.Sdata.U ≠ ⊥ := (hyp.toTypesIIIIIIVSetupS _hG).nontrivial.1
  have hUW1frob : Ch06.IsFrobeniusGroup ↥(hyp.U ⊔ hyp.W1)
      (hyp.U.subgroupOf (hyp.U ⊔ hyp.W1)) (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1)) := by
    have h := S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
    rw [hyp.Sdata_U_eq, hyp.Sdata_W1_eq] at h
    exact h
  set f : ↥(hyp.U ⊔ hyp.W1) →* (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) :=
    (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S)).comp (Subgroup.inclusion hUW1_le_S) with hf
  have he_apply : ∀ w : ↥(hyp.U ⊔ hyp.W1),
      f w = QuotientGroup.mk (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S) := by
    intro w
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    rw [he_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hw
    have hwUW1S : (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S) ∈ (hyp.U ⊔ hyp.W1).subgroupOf hyp.S := by
      rw [Subgroup.mem_subgroupOf]; exact w.2
    have hbot : (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S)
        ∈ ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) ⊓ (hyp.P.subgroupOf hyp.S) :=
      Subgroup.mem_inf.mpr ⟨hwUW1S, Subgroup.mem_subgroupOf.mpr hw⟩
    rw [disjoint_iff.mp hcompl.disjoint, Subgroup.mem_bot] at hbot
    exact Subtype.ext (by simpa using congrArg Subtype.val hbot)
  have hcard : Fintype.card ↥(hyp.U ⊔ hyp.W1)
      = Fintype.card (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      show Nat.card (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) = (hyp.P.subgroupOf hyp.S).index from rfl,
      hcompl.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW1_le_S).toEquiv]
  set e : ↥(hyp.U ⊔ hyp.W1) ≃* (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) :=
    MulEquiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩) with he
  have he_toMonoidHom : ∀ w, e.toMonoidHom w = f w := fun _ => rfl
  -- Transport the `U ⋊ W₁` Frobenius structure to `S̄`.
  have hFrob := Ch06.isFrobeniusGroup_map_equiv hUW1frob e
  -- The transported complement `W̄₁.map e` equals the (13.18) induction subgroup `Ā = (PW₁)/P`.
  have hAmatch : (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1)).map e.toMonoidHom
      = ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).map
          (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S)) := by
    apply le_antisymm
    · rintro _ ⟨w, hwW1, rfl⟩
      have hwW1' : (w : G) ∈ hyp.W1 := Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hwW1)
      refine Subgroup.mem_map.mpr ⟨⟨(w : G), hPW1_le_S (hW1_le_PW1 hwW1')⟩,
        Subgroup.mem_subgroupOf.mpr (hW1_le_PW1 hwW1'), ?_⟩
      rw [QuotientGroup.mk'_apply, he_toMonoidHom, he_apply]
    · rintro _ ⟨s, hsPW1, rfl⟩
      have hsG : (s : G) ∈ hyp.P ⊔ hyp.W1 :=
        Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hsPW1)
      have hsmem : (s : G) ∈ (↑(hyp.P ⊔ hyp.W1) : Set G) := hsG
      rw [Subgroup.coe_mul_of_right_le_normalizer_left hyp.P hyp.W1 (hW1_le_S.trans hS_norm_P)]
        at hsmem
      obtain ⟨p, hp, w, hw, hpw⟩ := Set.mem_mul.mp hsmem
      have hwW1 : w ∈ hyp.W1 := SetLike.mem_coe.mp hw
      have hpP : p ∈ hyp.P := SetLike.mem_coe.mp hp
      refine Subgroup.mem_map.mpr ⟨⟨w, hW1_le_UW1 hwW1⟩,
        Subgroup.mem_subgroupOf.mpr hwW1, ?_⟩
      have hs_eq : s = (⟨p, hP_le_S hpP⟩ : ↥hyp.S) * ⟨w, hW1_le_S hwW1⟩ :=
        Subtype.ext (by rw [Subgroup.coe_mul]; exact hpw.symm)
      have hp1 : QuotientGroup.mk' (hyp.P.subgroupOf hyp.S) ⟨p, hP_le_S hpP⟩ = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact Subgroup.mem_subgroupOf.mpr hpP
      rw [he_toMonoidHom, he_apply, ← QuotientGroup.mk'_apply, hs_eq, map_mul, hp1, one_mul]
  rw [hAmatch] at hFrob
  -- Frobenius norm on `S̄`.
  rw [norm_induce_one_frobenius hFrob]
  -- `|Ā| = |W₁| = q`.
  have hcardAmap : Nat.card ↥(((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).map
      (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S))) = hyp.q := by
    rw [← hAmatch,
      Nat.card_congr (Subgroup.equivMapOfInjective (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1))
        e.toMonoidHom e.injective).symm.toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1_le_UW1).toEquiv, ← hyp.q_eq_card_W1]
  -- `Ā.index = |Ū| = |U| = u` (using `c = 1`, Pf (13.12)).
  have hindexAmap : (((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).map
      (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S))).index = hyp.u := by
    rw [hFrob.isComplement.index_eq_card,
      Nat.card_congr (Subgroup.equivMapOfInjective (hyp.U.subgroupOf (hyp.U ⊔ hyp.W1))
        e.toMonoidHom e.injective).symm.toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : hyp.U ≤ _)).toEquiv,
      hyp.card_U_eq_uc, hc1, mul_one]
  rw [invOf_eq_inv, hcardAmap, hindexAmap]
  have hq : (hyp.q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.q_prime.pos.ne'
  push_cast
  field_simp
  ring

/-- **(13.18.b), Frobenius half**: `‖Ind_{PW₁}^S 1‖²_S = (u−1)/q + 1`.

By the inflation `Ind_{PW₁}^S 1 = Ind_{W̄₁}^{S̄} 1` inflated through `P` (P2
`induce_one_eq_compHom_induce_one_of_le` + P1 `inner_compHom_mk'_eq`), its `S`-norm equals
`‖Ind_{W̄₁}^{S̄} 1‖²` in the Frobenius quotient `S̄ = S/P ≅ U⋊W₁` (`uW1_isComplement_P` transported
by `isFrobeniusGroup_map_equiv`), which `norm_induce_one_frobenius` evaluates to
`(|U|−1)/|W₁| + 1 = (u−1)/q + 1` (using `c = 1`, Pf (13.12), so `|U| = u`).  The
`FiniteInduce`-instance content is `indPW1_inner_self_aux`; here we bridge to the caller's
`Fintype`/`Invertible` instances (both `Subsingleton`). -/
theorem indPW1_inner_self_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) := by
  intro _ _
  convert indPW1_inner_self_aux _hG hyp hc1 using 2
  exact Subsingleton.elim _ _

open OddOrder.Isaacs in
open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.a), the `W₁^#`-value of the induced trivial character** (Coq `gammaW1`):
`Ind_{P⋊W₁}^S 1 (x) = 1` for `x ∈ W₁^#`.  Mod-`P` inflation
(`induce_one_eq_compHom_induce_one_of_le`) turns the value into `γ(x̄)` for
`γ = Ind_{Ā}^{S̄} 1`; the `S̄ ≅ U ⋊ W₁` Frobenius transport (the `indPW1_inner_self_aux`
setup) and the Frobenius trivial-intersection complement value
(`induce_one_eq_one_of_mem_complement`) give `γ(x̄) = 1`, with `x̄ ≠ 1` because
`W₁ ⊓ P = ⊥` (`uW1_isComplement_P`). -/
theorem indPW1_apply_eq_one_of_mem_W1_sharp [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {x : ↥hyp.S} (hxW1 : (x : G) ∈ hyp.W1) (hx1 : x ≠ 1) :
    indPW1 hyp x = 1 := by
  classical
  -- Structural setup (the `indPW1_inner_self_aux` pattern).
  have hcompl := uW1_isComplement_P hyp
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hP_le_S : hyp.P ≤ hyp.S := hP_le_M'.trans hM'_le_S
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hU_le_M' : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have hUW1_le_S : hyp.U ⊔ hyp.W1 ≤ hyp.S := sup_le (hU_le_M'.trans hM'_le_S) hW1_le_S
  have hW1_le_UW1 : hyp.W1 ≤ hyp.U ⊔ hyp.W1 := le_sup_right
  have hW1_le_PW1 : hyp.W1 ≤ hyp.P ⊔ hyp.W1 := le_sup_right
  have hP_le_PW1 : hyp.P ≤ hyp.P ⊔ hyp.W1 := le_sup_left
  have hPW1_le_S : hyp.P ⊔ hyp.W1 ≤ hyp.S := sup_le hP_le_S hW1_le_S
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  have hNA : hyp.P.subgroupOf hyp.S ≤ (hyp.P ⊔ hyp.W1).subgroupOf hyp.S :=
    Subgroup.comap_mono hP_le_PW1
  -- Inflation: `indPW1 x = γ(x̄)`.
  rw [show indPW1 hyp = ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
        (trivialClassFunction _) from rfl,
    OddOrder.RepresentationTheory.induce_one_eq_compHom_induce_one_of_le hNA,
    OddOrder.RepresentationTheory.ClassFunction.compHom_apply]
  -- The `S̄ = Ū ⋊ W̄₁` Frobenius transport (`indPW1_inner_self_aux` pattern).
  have hSdataUne : hyp.Sdata.U ≠ ⊥ := (hyp.toTypesIIIIIIVSetupS _hG).nontrivial.1
  have hUW1frob : Ch06.IsFrobeniusGroup ↥(hyp.U ⊔ hyp.W1)
      (hyp.U.subgroupOf (hyp.U ⊔ hyp.W1)) (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1)) := by
    have h := S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
    rw [hyp.Sdata_U_eq, hyp.Sdata_W1_eq] at h
    exact h
  set f : ↥(hyp.U ⊔ hyp.W1) →* (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) :=
    (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S)).comp (Subgroup.inclusion hUW1_le_S) with hf
  have he_apply : ∀ w : ↥(hyp.U ⊔ hyp.W1),
      f w = QuotientGroup.mk (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S) := by
    intro w
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    rw [he_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hw
    have hwUW1S : (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S) ∈ (hyp.U ⊔ hyp.W1).subgroupOf hyp.S := by
      rw [Subgroup.mem_subgroupOf]; exact w.2
    have hbot : (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S)
        ∈ ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) ⊓ (hyp.P.subgroupOf hyp.S) :=
      Subgroup.mem_inf.mpr ⟨hwUW1S, Subgroup.mem_subgroupOf.mpr hw⟩
    rw [disjoint_iff.mp hcompl.disjoint, Subgroup.mem_bot] at hbot
    exact Subtype.ext (by simpa using congrArg Subtype.val hbot)
  have hcard : Fintype.card ↥(hyp.U ⊔ hyp.W1)
      = Fintype.card (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      show Nat.card (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) = (hyp.P.subgroupOf hyp.S).index from rfl,
      hcompl.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW1_le_S).toEquiv]
  set e : ↥(hyp.U ⊔ hyp.W1) ≃* (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) :=
    MulEquiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩) with he
  have he_toMonoidHom : ∀ w, e.toMonoidHom w = f w := fun _ => rfl
  have hFrob := Ch06.isFrobeniusGroup_map_equiv hUW1frob e
  have hAmatch : (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1)).map e.toMonoidHom
      = ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).map
          (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S)) := by
    apply le_antisymm
    · rintro _ ⟨w, hwW1, rfl⟩
      have hwW1' : (w : G) ∈ hyp.W1 := Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hwW1)
      refine Subgroup.mem_map.mpr ⟨⟨(w : G), hPW1_le_S (hW1_le_PW1 hwW1')⟩,
        Subgroup.mem_subgroupOf.mpr (hW1_le_PW1 hwW1'), ?_⟩
      rw [QuotientGroup.mk'_apply, he_toMonoidHom, he_apply]
    · rintro _ ⟨s, hsPW1, rfl⟩
      have hsG : (s : G) ∈ hyp.P ⊔ hyp.W1 :=
        Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hsPW1)
      have hsmem : (s : G) ∈ (↑(hyp.P ⊔ hyp.W1) : Set G) := hsG
      rw [Subgroup.coe_mul_of_right_le_normalizer_left hyp.P hyp.W1 (hW1_le_S.trans hS_norm_P)]
        at hsmem
      obtain ⟨p, hp, w, hw, hpw⟩ := Set.mem_mul.mp hsmem
      have hwW1 : w ∈ hyp.W1 := SetLike.mem_coe.mp hw
      have hpP : p ∈ hyp.P := SetLike.mem_coe.mp hp
      refine Subgroup.mem_map.mpr ⟨⟨w, hW1_le_UW1 hwW1⟩,
        Subgroup.mem_subgroupOf.mpr hwW1, ?_⟩
      have hs_eq : s = (⟨p, hP_le_S hpP⟩ : ↥hyp.S) * ⟨w, hW1_le_S hwW1⟩ :=
        Subtype.ext (by rw [Subgroup.coe_mul]; exact hpw.symm)
      have hp1 : QuotientGroup.mk' (hyp.P.subgroupOf hyp.S) ⟨p, hP_le_S hpP⟩ = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact Subgroup.mem_subgroupOf.mpr hpP
      rw [he_toMonoidHom, he_apply, ← QuotientGroup.mk'_apply, hs_eq, map_mul, hp1, one_mul]
  rw [hAmatch] at hFrob
  -- `x̄ ∈ Ā` and `x̄ ≠ 1`; conclude by the Frobenius complement value.
  have hxA : QuotientGroup.mk' (hyp.P.subgroupOf hyp.S) x
      ∈ ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).map
          (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S)) :=
    Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr (hW1_le_PW1 hxW1), rfl⟩
  have hx1' : QuotientGroup.mk' (hyp.P.subgroupOf hyp.S) x ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hxUW1S : x ∈ (hyp.U ⊔ hyp.W1).subgroupOf hyp.S :=
      Subgroup.mem_subgroupOf.mpr (hW1_le_UW1 hxW1)
    have hbot : x ∈ ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) ⊓ (hyp.P.subgroupOf hyp.S) :=
      Subgroup.mem_inf.mpr ⟨hxUW1S, h1⟩
    rw [disjoint_iff.mp hcompl.disjoint, Subgroup.mem_bot] at hbot
    exact hx1 hbot
  exact induce_one_eq_one_of_mem_complement hFrob hxA hx1'

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.a), vanishing of the induced trivial character on `S′ − P`** (the `PU`-case of the
Coq `PVSbeta`): `Ind_{P⋊W₁}^S 1 (z) = 0` for `z ∈ S′ ∖ P`.  The conjugator set is empty: a
conjugate `g⁻¹zg ∈ PW₁` also lies in the normal `S′`, and `(P ⊔ W₁) ⊓ S′ = P` by the Dedekind
modular law (`P ≤ S′`, `W₁ ⊓ S′ = ⊥` from the `M_complement` disjointness), so `z` would lie in
the normal `P` — contradiction. -/
theorem indPW1_apply_eq_zero_of_mem_derived_not_mem_P [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {z : ↥hyp.S} (hzS' : (z : G) ∈ derivedInG hyp.S) (hzP : (z : G) ∉ hyp.P) :
    indPW1 hyp z = 0 := by
  classical
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hP_le_S : hyp.P ≤ hyp.S := hP_le_M'.trans hM'_le_S
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  -- `W₁ ⊓ S′ = ⊥` (the `M_complement` disjointness, `uW1_isComplement_P` pattern).
  have hM'W1 : derivedInG hyp.S ⊓ hyp.W1 = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.M_complement.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxM', hxW1⟩
    have hxS : x ∈ hyp.S := hM'_le_S hxM'
    have hmem : (⟨x, hxS⟩ : ↥hyp.S) ∈
        ((derivedInG hyp.S).subgroupOf hyp.S) ⊓ (hyp.Sdata.W1.subgroupOf hyp.S) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxM', Subgroup.mem_subgroupOf.mpr (hyp.Sdata_W1_eq ▸ hxW1)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  -- Dedekind-style: an element of `(P ⊔ W₁) ⊓ S′` lies in `P` (factor `w = p·w₁` through the
  -- coset decomposition `PW₁ = P * W₁`, then `w₁ ∈ W₁ ⊓ S′ = ⊥`).
  have hPW1S' : ∀ {w : G}, w ∈ hyp.P ⊔ hyp.W1 → w ∈ derivedInG hyp.S → w ∈ hyp.P := by
    intro w hwPW1 hwS'
    have hwmem : w ∈ (↑(hyp.P ⊔ hyp.W1) : Set G) := hwPW1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left hyp.P hyp.W1
      (hW1_le_S.trans hS_norm_P)] at hwmem
    obtain ⟨p, hp, w1, hw1, hpw⟩ := Set.mem_mul.mp hwmem
    have hw1S' : w1 ∈ derivedInG hyp.S := by
      have hw1eq : w1 = p⁻¹ * w := by rw [← hpw]; group
      rw [hw1eq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hP_le_M' (SetLike.mem_coe.mp hp))) hwS'
    have hw1bot : w1 ∈ derivedInG hyp.S ⊓ hyp.W1 :=
      Subgroup.mem_inf.mpr ⟨hw1S', SetLike.mem_coe.mp hw1⟩
    rw [hM'W1, Subgroup.mem_bot] at hw1bot
    have hweq : w = p := by rw [← hpw, hw1bot, mul_one]
    rw [hweq]
    exact SetLike.mem_coe.mp hp
  rw [show indPW1 hyp = ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
        (trivialClassFunction _) from rfl, induce_one_apply]
  have hempty : (Finset.univ.filter
      (fun g : ↥hyp.S => g⁻¹ * z * g ∈ (hyp.P ⊔ hyp.W1).subgroupOf hyp.S)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro g _ hmem
    have hwPW1 : ((g⁻¹ * z * g : ↥hyp.S) : G) ∈ hyp.P ⊔ hyp.W1 :=
      Subgroup.mem_subgroupOf.mp hmem
    -- The conjugate stays in the normal `S′`.
    have hwS' : ((g⁻¹ * z * g : ↥hyp.S) : G) ∈ derivedInG hyp.S := by
      have hz' : z ∈ (derivedInG hyp.S).subgroupOf hyp.S := Subgroup.mem_subgroupOf.mpr hzS'
      have hconj := (inferInstance :
        ((derivedInG hyp.S).subgroupOf hyp.S).Normal).conj_mem z hz' g⁻¹
      rw [inv_inv] at hconj
      have : g⁻¹ * z * g ∈ (derivedInG hyp.S).subgroupOf hyp.S := hconj
      exact Subgroup.mem_subgroupOf.mp this
    -- Dedekind puts it in `P`, so `z` lies in the normal `P` — contradiction.
    have hwP : g⁻¹ * z * g ∈ hyp.P.subgroupOf hyp.S :=
      Subgroup.mem_subgroupOf.mpr (hPW1S' hwPW1 hwS')
    have hzback := hPnorm.conj_mem _ hwP g
    have hzz : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
    rw [hzz] at hzback
    exact hzP (Subgroup.mem_subgroupOf.mp hzback)
  rw [hempty, Finset.card_empty, Nat.cast_zero, mul_zero]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.18.a), exact `β`-support** (Coq `PVSbeta`, `PFsection13.v:1833`):
`supp(β_j) ⊆ P^# ∪ V_S^S` — the honest carrier `β_j ∈ CF(S, P^# ∪ V_S)`.

Fully proven: the group-theoretic skeleton conjugates every point outside `S′` to `x·y` with
`x ∈ W₁^#`, `y ∈ W₂` (Peterfalvi (2.1), `mem_compl_conj_into_W`); at `y = 1` the two proven
`W₁^#`-values cancel (`indPW1_apply_eq_one_of_mem_W1_sharp`, `mu_row0_apply_eq_one_of_mem_W1` —
the `(4.3.c)+(13.3.c)` value), otherwise `x·y ∈ V_S`; inside `S′` the two proven `S′−P`-values
cancel (`indPW1_apply_eq_zero_of_mem_derived_not_mem_P`,
`mu_row0_apply_eq_zero_of_mem_derived_not_mem_P` — the `(13.3.a)+(13.12)` vanishing), and at
`1` the degrees agree (`betaGrid_apply_one_eq_zero`).

⚠ The previous statement here (grid form `supp(β_j) ⊆ ⋃ᵢ supp(μ_{ij})`) was an unfaithful
restate (it would additionally require every point of `P^#` to carry a nonzero `μ`-value) —
replaced by the Coq-faithful carrier, issue-3003 pattern.  A hypothesis-parametrized copy of
this skeleton lives in `S16_NonExistenceG/TGapCross`
(`betaGrid_support_sharpP_union_typePV_of_values`) — cross-lane redirect tracked. -/
theorem betaGrid_support_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    (betaGrid hyp j).support ⊆
      {z : ↥hyp.S |
        (z : G) ∈ OddOrder.GroupTheory.sharpSubgroup hyp.P ∪
          OddOrder.GroupTheory.conjClassSetIn hyp.S
            (OddOrder.GroupTheory.typePV hyp.S hyp.Sdata)} := by
  classical
  have hj0 : j ≠ ⟨0, hyp.p_prime.pos⟩ := fun h => hj (by simp [h])
  intro z hz
  rw [OddOrder.RepresentationTheory.ClassFunction.mem_support] at hz
  by_cases hzD : (z : G) ∈ OddOrder.GroupTheory.derivedInG hyp.S
  · by_cases hzP : (z : G) ∈ hyp.P
    · by_cases hz1 : z = 1
      · exact absurd (hz1 ▸ betaGrid_apply_one_eq_zero_of_c_eq_one hG hyp hc1 j hj) hz
      · exact Or.inl ⟨hzP, fun h => hz1 (Subtype.ext h)⟩
    · exfalso
      apply hz
      rw [betaGrid, OddOrder.RepresentationTheory.ClassFunction.sub_apply,
        indPW1_apply_eq_zero_of_mem_derived_not_mem_P hG hyp hzD hzP,
        hyp.mu_row0_apply_eq_zero_of_mem_derived_not_mem_P_of_c_eq_one
          hG hc1 j hj0 z hzD hzP, sub_self]
  · set h := hyp.s06S hG with hs06
    have hzK : z ∉ h.K := fun hzK => hzD (Subgroup.mem_subgroupOf.mp hzK)
    obtain ⟨c, x, hxW1, hx1, y, hyW2, hconj⟩ := h.mem_compl_conj_into_W hzK
    have hxW1G : (x : G) ∈ hyp.W1 := by
      have hx := Subgroup.mem_subgroupOf.mp hxW1
      rwa [hyp.Sdata_W1_eq] at hx
    have hyW2G : (y : G) ∈ hyp.W2 := by
      have hy := Subgroup.mem_subgroupOf.mp hyW2
      rwa [hyp.Sdata_W2_eq] at hy
    have hconjβ : betaGrid hyp j z = betaGrid hyp j (x * y) := by
      rw [← hconj]
      have hc := (betaGrid hyp j).conj_eq z c⁻¹
      rw [inv_inv] at hc
      exact hc.symm
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hz
      rw [hconjβ, mul_one, betaGrid, OddOrder.RepresentationTheory.ClassFunction.sub_apply,
        indPW1_apply_eq_one_of_mem_W1_sharp hG hyp hxW1G hx1,
        hyp.mu_row0_apply_eq_one_of_mem_W1 hG j x hxW1G hx1, sub_self]
    right
    rw [OddOrder.GroupTheory.mem_conjClassSetIn]
    refine ⟨(x : G) * (y : G), ?_, (c : G), c.2, ?_⟩
    · have hxW1data : (x : G) ∈ hyp.Sdata.W1 := Subgroup.mem_subgroupOf.mp hxW1
      have hyW2data : (y : G) ∈ hyp.Sdata.W2 := Subgroup.mem_subgroupOf.mp hyW2
      have hxyW : (x : G) * (y : G) ∈ hyp.Sdata.W := by
        rw [hyp.Sdata.W_eq]
        exact mul_mem (Subgroup.mem_sup_left hxW1data) (Subgroup.mem_sup_right hyW2data)
      simp only [OddOrder.GroupTheory.typePV, Set.mem_sdiff, Set.mem_union,
        SetLike.mem_coe, not_or]
      refine ⟨hxyW, ?_, ?_⟩
      · intro hxyW1
        apply hy1
        have hyW1 : (y : G) ∈ hyp.Sdata.W1 := by
          have heq : (y : G) = (x : G)⁻¹ * ((x : G) * (y : G)) := by group
          rw [heq]
          exact mul_mem (inv_mem hxW1data) hxyW1
        have hbot := (OddOrder.Peterfalvi.S12.typePData_disjoint_W1_W2 hyp.Sdata).le_bot
          (Subgroup.mem_inf.mpr ⟨hyW1, hyW2data⟩)
        rw [Subgroup.mem_bot] at hbot
        exact Subtype.ext hbot
      · intro hxyW2
        apply hx1
        have hxW2 : (x : G) ∈ hyp.Sdata.W2 := by
          have heq : (x : G) = ((x : G) * (y : G)) * (y : G)⁻¹ := by group
          rw [heq]
          exact mul_mem hxyW2 (inv_mem hyW2data)
        have hbot := (OddOrder.Peterfalvi.S12.typePData_disjoint_W1_W2 hyp.Sdata).le_bot
          (Subgroup.mem_inf.mpr ⟨hxW1data, hxW2⟩)
        rw [Subgroup.mem_bot] at hbot
        exact Subtype.ext hbot
    · have hconjG : (c : G)⁻¹ * (z : G) * (c : G) = (x : G) * (y : G) := by
        have hc := congrArg hyp.S.subtype hconj
        rwa [map_mul, map_mul, map_inv] at hc
      rw [← hconjG]
      group



end OddOrder.Peterfalvi.S15
