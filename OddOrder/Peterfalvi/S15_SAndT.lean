/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_ComplementStructure

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT` (2000-line limit, issues 0103/0102).
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
* `norm_formula` — **(13.18.b)** `‖β_j‖²_S = (u−1)/q + 2` (its Frobenius `Ind` half is the sorry-free
  `norm_induce_one_frobenius`);
* `Gamma_orthogonal_one` — **(13.18.c)** `(Γ, 1_G) = 0`, the residual is orthogonal to the principal;
* `Gamma_real` — **(13.18.c)** `Γ` is real (`Γ.conj = Γ`);
* `Y_norm_bound` — **(13.18.d)** for any split `Γ = X + Y` (`X ⊥ Y`, `Y ⊥` grid), `‖Y‖² ≤ (u−1)/q`.

The remaining half of **(13.18.c)** — `Γ`'s `j`-independence (`defGamma`) — is the standalone proven
`gammaGrid_defGamma` (not a field here, to keep the `FiniteInduce` `τ_S` instances out of this
structure's explicit inner-product binders).  ⚠ The **removed** fields `Gamma_independent`
(`⟨Γ,η_ik⟩ = 0`) and the old `Y_norm_bound` (`‖Γ‖² ≤ (u−1)/q + 1`) were **overstatements** — (13.18.c)
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
theorem PW1_index_eq_u [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
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
  rw [hcardPW1S, hyp.card_S_val hG, c_eq_one hG hyp, mul_one] at hm
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
theorem betaGrid_apply_one_eq_zero [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    betaGrid hyp j 1 = 0 := by
  have hj0 : j ≠ ⟨0, hyp.p_prime.pos⟩ := fun h => hj (by simp [h])
  rw [betaGrid, OddOrder.RepresentationTheory.ClassFunction.sub_apply, indPW1,
    ClassFunction.induce_apply_one, PW1_index_eq_u hG hyp, trivialClassFunction_apply,
    mul_one, hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩ j hj0, sub_self]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.b), Frobenius half** (`FiniteInduce`-instance form): `‖Ind_{PW₁}^S 1‖²_S = (u−1)/q + 1`.
The wrapper `indPW1_inner_self` bridges to arbitrary `Fintype`/`Invertible` instances. -/
private theorem indPW1_inner_self_aux [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
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
      hyp.card_U_eq_uc, c_eq_one _hG hyp, mul_one]
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
theorem indPW1_inner_self [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) := by
  intro _ _
  convert indPW1_inner_self_aux _hG hyp using 2
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
theorem betaGrid_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
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
      · exact absurd (hz1 ▸ betaGrid_apply_one_eq_zero hG hyp j hj) hz
      · exact Or.inl ⟨hzP, fun h => hz1 (Subtype.ext h)⟩
    · exfalso
      apply hz
      rw [betaGrid, OddOrder.RepresentationTheory.ClassFunction.sub_apply,
        indPW1_apply_eq_zero_of_mem_derived_not_mem_P hG hyp hzD hzP,
        hyp.mu_row0_apply_eq_zero_of_mem_derived_not_mem_P hG j hj0 z hzD hzP, sub_self]
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

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`P ⊄ ker μ_{0j}`** (Pf (13.18.b) kernel step, `S`-side).  For `j ≠ 0`, the base-row grid
irreducible `μ_{0j}` does not have the Fitting kernel `P` in its character kernel.

Contrapositive of Peterfalvi's argument (mirroring `PrimeTIResidue.constituent_P_not_subset_ker`):
if `P ⊆ ker μ_{0j}` then `W₂ ⊆ P ⊆ ker μ_{0j}`, so `Res_{S'} μ_{0j}` is trivial on the `W₂`-part
(`characterKernel_restrict_subgroupOf`); its constituent `ψ` — the (4.5.a) source of
`μ_j = ∑_i μ_{ij} = Ind_{S'} ψ`, with `⟨Res_{S'} μ_{0j}, ψ⟩ = 1` by Frobenius reciprocity — inherits
that kernel containment (`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), contradicting the
`mu_colSum_eq_induce` clause `W₂ ⊄ ker ψ`. -/
theorem P_not_subset_characterKernel_mu [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)) := by
  classical
  set μ0 := hyp.mu ⟨0, hyp.q_prime.pos⟩ j with hμ0
  have hW2_le_P : hyp.W2 ≤ hyp.P := by
    have h := hyp.Sdata.W2_le
    rw [hyp.Sdata_W2_eq, hyp.Sdata.H_eq, ← hyp.P_eq_SF] at h
    exact h.trans inf_le_left
  intro hPker
  obtain ⟨psiS, hpsiIrr, hpsiInd, hpsiW2⟩ := hyp.mu_colSum_eq_induce j
  have hj' : j ≠ ⟨0, hyp.p_prime.pos⟩ := fun h => hj (by rw [h])
  have hW2notpsi := hpsiW2 hj'
  have hW2Sker : (hyp.W2.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel μ0 :=
    fun x hx => hPker (Subgroup.comap_mono hW2_le_P hx)
  have hRker := OddOrder.Peterfalvi.S08.characterKernel_restrict_subgroupOf
    ((derivedInG hyp.S).subgroupOf hyp.S) hW2Sker
  have hResChar := OddOrder.Peterfalvi.S08.isCharacter_restrict
    (hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j).isCharacter
    ((derivedInG hyp.S).subgroupOf hyp.S)
  -- `⟨∑_i μ_{ij}, μ_{0j}⟩ = 1` (orthonormality: only the `i = 0` term survives).
  have hmul : ClassFunction.inner (∑ i, hyp.mu i j) μ0 = 1 := by
    rw [inner_sum_left]
    refine (Finset.sum_eq_single ⟨0, hyp.q_prime.pos⟩ (fun i _ hi => ?_)
      (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    · have h := irreducibleCharacter_inner_eq_ite
        (⟨hyp.mu i j, hyp.mu_irreducible i j⟩ : IrreducibleCharacter ↥hyp.S)
        ⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
      rw [if_neg (fun heq => hi (hyp.mu_col_injective j
        (congrArg (fun χ : IrreducibleCharacter ↥hyp.S => (χ : ClassFunction ↥hyp.S ℂ)) heq)))] at h
      exact h
    · have h := irreducibleCharacter_inner_eq_ite
        (⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩ : IrreducibleCharacter ↥hyp.S)
        ⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
      simpa using h
  have hfrob := ClassFunction.inner_induce_eq_inner_restrict
    ((derivedInG hyp.S).subgroupOf hyp.S) psiS μ0
  rw [← hpsiInd, hmul] at hfrob
  have hinner : ClassFunction.inner
      (ClassFunction.restrict ((derivedInG hyp.S).subgroupOf hyp.S) μ0) psiS ≠ 0 := by
    rw [RepresentationTheory.inner_conj_symm, ← hfrob]; simp
  exact hW2notpsi (fun x hx =>
    OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
      hResChar hpsiIrr hinner (hRker hx))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.b) orthogonality half** (`FiniteInduce`-instance form). -/
private theorem indPW1_inner_mu_aux [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
      ClassFunction.inner (indPW1 hyp) (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
  classical
  have hP_le_S : hyp.P ≤ hyp.S :=
    (by rw [hyp.S_deriv_eq_PU]; exact le_sup_left : hyp.P ≤ derivedInG hyp.S).trans
      (Subgroup.map_subtype_le _)
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  have hNA : hyp.P.subgroupOf hyp.S ≤ (hyp.P ⊔ hyp.W1).subgroupOf hyp.S :=
    Subgroup.comap_mono le_sup_left
  rw [show indPW1 hyp = ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
        (trivialClassFunction _) from rfl,
    OddOrder.RepresentationTheory.induce_one_eq_compHom_induce_one_of_le hNA]
  exact OddOrder.RepresentationTheory.inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker _
    ⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ j, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
    (P_not_subset_characterKernel_mu _hG hyp j hj)

/-- **(13.18.b), orthogonality half**: `⟨Ind_{PW₁}^S 1, μ_{0j}⟩ = 0` for `j ≠ 0`.

`Ind_{PW₁}^S 1 = (Ind_{Ā}^{S̄} 1) ∘ mk'` (P2) is inflated from `S̄ = S/P`, so all its irreducible
constituents kill `P`; `μ_{0j}` does not (`P_not_subset_characterKernel_mu`), so they are orthogonal
(`inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker`).  `_aux` carries the `FiniteInduce`
instances; the wrapper bridges to the caller's (`Subsingleton`). -/
theorem indPW1_inner_mu [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (_hj : (j : ℕ) ≠ 0) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (indPW1 hyp) (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
  intro _ _
  convert indPW1_inner_mu_aux _hG hyp j _hj using 2
  exact Subsingleton.elim _ _

/-- **(13.18.b) norm**: `‖β_j‖²_S = (u−1)/q + 2`.

Genuine reduction: `β_j = Ind_{PW₁}^S 1 − μ_{0j}`, so by bilinearity
`‖β_j‖² = ‖Ind‖² − ⟨Ind,μ_{0j}⟩ − ⟨μ_{0j},Ind⟩ + ‖μ_{0j}‖²`.  Here `‖μ_{0j}‖² = 1` is **proven**
from `hyp.mu_irreducible` (via `irreducibleCharacter_inner_eq_ite`), `⟨μ_{0j},Ind⟩ = 0` follows
from `⟨Ind,μ_{0j}⟩ = 0` by conjugate symmetry, and the remaining `‖Ind‖² = (u−1)/q + 1`
(`indPW1_inner_self`) and `⟨Ind,μ_{0j}⟩ = 0` (`indPW1_inner_mu`) are the isolated §13 obligations.
`(u−1)/q + 1 + 1 = (u−1)/q + 2`. -/
theorem betaGrid_norm [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (betaGrid hyp j) (betaGrid hyp j)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ) := by
  intro _ _
  set μ := hyp.mu ⟨0, hyp.q_prime.pos⟩ j with hμdef
  have hμμ : ClassFunction.inner μ μ = 1 := by
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨μ, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      (⟨μ, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩)
    simpa using hite
  have hIμ : ClassFunction.inner (indPW1 hyp) μ = 0 := indPW1_inner_mu hG hyp j hj
  have hμI : ClassFunction.inner μ (indPW1 hyp) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hIμ, star_zero]
  have hII : ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
      = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) := indPW1_inner_self hG hyp
  have hbeta : betaGrid hyp j = indPW1 hyp - μ := rfl
  rw [hbeta, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hII, hIμ, hμI, hμμ]
  push_cast
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(4.8)/(5.3) prime-`TI` Dade cross-relation, `S`-side row-`0` form**:
`τ_S(μ_{0j} − μ_{01}) = η_{0j} − η_{01}` for `j ≠ 0`.

This is Coq `prDade_sub_TIirr` (`PFsection4.v:870`) `τ(μ2_{ij} − μ2_{ik}) = δ_j·(η_{ij} − η_{ik})`
specialized to row `i = 0`, columns `j` and `#1`, with the `FT`-context sign `δ_j = 1`.  It is the
single deep input behind (13.18.c)'s `j`-independence `gammaGrid_defGamma`.

✅ **Now on the correct Dade map** (issue 9076, 2026-07-08): `τ_S` is `dadeIntegralCharacterMap`
of the honest **`'A0(S)`-Dade** `dadeHypS0` (support `A₀(S) = A(S) ∪ V^S`), **not** the smaller
`'A(S)`-Dade `dadeHypS`.  The `μ`-column difference `μ_{0j} − μ_{01}` is supported on `P^# ∪ V_S`
(Coq `prDade_sub_TIirr_on`), and `V_S ⊄ S' ⊇ A(S)`, so with the old `dadeHypS` map the `V_S`-part
fell in the arbitrary linear-extension region and the statement was **unprovable as stated**; the
`'A0`-Dade correction fixes that (`dadeHypS0` inherits one deep FT-support pin,
`not_isConj_honestTypeP2ASet_typePV`).

Remaining to discharge the `sorry` (rigidity engine now available): `X := τ_S(μ-diff)` has
`‖X‖² = 2` (Dade isometry) and `X ∈ ZIrr`; it agrees with `η_{0j} − η_{01}` on the regular set via
`τ_S = Ind_S^G` on `A₀`-supported (`normedTI 'A0`, `H = ⊥`) + the prime-`TI` `μ`-value
`μ_{0j}|_V = ω`-value (Coq `prTIirr_id`, prime-`TI` theory — not yet ported, cf. 9014); then
`X = η_{0j} − η_{01}` by `S16.eta_diff_rigidity` (Peterfalvi (3.8), issue 9076 piece 4b). -/
theorem tauS_mu_row0_cross [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (_hj : (j : ℕ) ≠ 0) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG))
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      = hyp.eta ⟨0, hyp.q_prime.pos⟩ j
          - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ := by
  classical
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) with hD
  by_cases hj1 : j = ⟨1, by have := hyp.three_le_p; omega⟩
  · -- Trivial column `j = #1`: both `μ`- and `η`-differences vanish, and `τ_S 0 = 0`.
    simp only [hj1, sub_self, map_zero]
  · -- `j ≠ #1`: `X := τ_S(μ_{0j} − μ_{0,#1})` is a norm-`2` `ZIrr` character agreeing with
    -- `η_{0j} − η_{0,#1}` on the regular set `V`, so `S16.eta_diff_rigidity` (3.8) pins it.
    have hμaIrr : IsIrreducibleCharacter (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) :=
      hyp.mu_irreducible _ _
    have hμbIrr : IsIrreducibleCharacter
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) :=
      hyp.mu_irreducible _ _
    have hμne : hyp.mu ⟨0, hyp.q_prime.pos⟩ j
        ≠ hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ :=
      hyp.mu_row0_ne hj1
    have hsupp := hyp.tauS_mu_row0_diff_support hG j _hj
    have hZIrrS : (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        ∈ ZIrr (↥hyp.S) :=
      (ZIrr (↥hyp.S)).sub_mem hμaIrr.mem_ZIrr hμbIrr.mem_ZIrr
    -- (a) `X ∈ ZIrr G` (Dade sends supported virtual characters to virtual characters, `(2.6.b)`).
    have hXZ : D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) ∈ ZIrr G :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (hyp.dadeHypS0 hG) (hyp.dadeHypS0_hconj hG) hsupp hZIrrS
    -- (b) `‖μ_{0j} − μ_{0,#1}‖² = 2` (two distinct irreducibles).
    have hinner : ∀ φ ψ : ClassFunction ↥hyp.S ℂ, IsIrreducibleCharacter φ →
        IsIrreducibleCharacter ψ → ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥hyp.S)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥hyp.S)
      simp only [IrreducibleCharacter.coe_mk] at h
      rw [h]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have h_ab : ClassFunction.inner (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 := by
      rw [hinner _ _ hμaIrr hμbIrr, if_neg hμne]
    have h_ba : ClassFunction.inner
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [hinner _ _ hμbIrr hμaIrr, if_neg (Ne.symm hμne)]
    have hnorm2 : ClassFunction.inner
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 2 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h_ab, h_ba,
        hμaIrr.inner_self_eq_one, hμbIrr.inner_self_eq_one]
      ring
    have hX2 : ClassFunction.inner
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩))
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) = 2 := by
      rw [hD, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypS0 hG) (hyp.dadeHypS0_hconj hG) hsupp hsupp]
      exact hnorm2
    -- (c) `X − (η_{0j} − η_{0,#1})` vanishes on the regular set `V` (prime-`TI` `V`-value pin).
    have hvanish : ∀ x ∈ conjClassSet
          ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
              - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
          - ((1 : ℤ) : ℂ) • (hyp.eta ⟨0, hyp.q_prime.pos⟩ j
              - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) x = 0 := by
      intro x hx
      have hv := hyp.tauS_mu_row0_vanish_on_V hG j _hj x hx
      simpa [hD] using hv
    -- (3.8) rigidity: a norm-`2` `ZIrr` character agreeing with `η_{0j} − η_{0,#1}` on `V` is it.
    have hrig := OddOrder.Peterfalvi.S16.eta_diff_rigidity hyp hXZ hX2
      ⟨0, hyp.q_prime.pos⟩ hj1 (s := (1 : ℤ)) (Or.inl rfl) hvanish
    rw [Int.cast_one, one_smul] at hrig
    exact hrig

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c), `j`-independence** (`defGamma`): for every column `j ≠ 0`, the bridge residual
`τ_S(β_j) − 1_G + η_{0j}` equals the fixed gap `Γ = GammaGrid` (defined at column `#1`).

This is exactly Peterfalvi (13.18.c)'s "`Γ` is independent of `j`" (Coq `defGamma`,
`PFsection13.v:1905`), **NOT** grid-orthogonality: the previous scaffold field
`Gamma_independent : ⟨Γ, η_{ik}⟩ = 0` was an **overstatement** (issue 3003), refuted by the genuine
(13.18.d) `X + Y` decomposition where `Γ`'s grid-component `X` is nonzero.

Proof (sorry-free glue, one isolated obligation): `τ_S(β_j) − τ_S(β_{#1}) = τ_S(β_j − β_{#1})` by
`ℤ`-linearity of the Dade map (`map_sub`), and `β_j − β_{#1} = μ_{01} − μ_{0j} = −(μ_{0j} − μ_{01})`
(both share the `Ind_{PW₁}^S 1` positive part), so `τ_S(β_j − β_{#1}) = −(η_{0j} − η_{01}) =
η_{01} − η_{0j}` by the (4.8)/(5.3) cross-relation `tauS_mu_row0_cross`.  Cancelling the `−1_G`'s and
`abel` closes the goal. -/
theorem gammaGrid_defGamma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) (betaGrid hyp j)
        - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + hyp.eta ⟨0, hyp.q_prime.pos⟩ j
      = GammaGrid hG hyp := by
  have hcross := tauS_mu_row0_cross hG hyp j hj
  have hbeta : betaGrid hyp j - betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩
      = -(hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) := by
    simp only [betaGrid]; abel
  have key : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) (betaGrid hyp j)
      - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG))
          (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)
      = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
        - hyp.eta ⟨0, hyp.q_prime.pos⟩ j := by
    rw [← map_sub, hbeta, map_neg, hcross]; abel
  simp only [GammaGrid, tauSbetaGrid]
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
    ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) with hD
  rw [← sub_eq_zero, show
      (D (betaGrid hyp j) - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          + hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
        - (D (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)
          - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      = (D (betaGrid hyp j) - D (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩))
        - (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
          - hyp.eta ⟨0, hyp.q_prime.pos⟩ j) by abel, key, sub_self]

/-- **The Coq `A0beta` inclusion `P^# ∪ V_S ⊆ 'A0(S)`** (the final step of (13.18.a)): the sharp
Fitting kernel `P^#` and the `S`-class-closure of the cyclic-TI set `V = W − (W₁ ∪ W₂)` both land
in the honest `A₀(S) = A(S) ∪ V^S`.  The `V^S` part is the definitional right component (after the
`Sdata.W1/W2` synchronization); `P^#` lands in `A(S) = centralizerSupport (S_σ^#) S'` because
`P = S_F = S_σ` (type `P₂`, `maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II`), `P ≤ S' = P ⊔ U`,
and every element self-centralizes. -/
theorem sharpP_union_V_subset_A0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    sharpSubgroup hyp.P ∪
        conjClassSetIn hyp.S (typePV hyp.S hyp.Sdata)
      ⊆ honestTypeP2A0Set hyp.S hyp.Sdata := by
  have hPeq : hyp.P = OddOrder.BG.Ch3.S10.Msigma hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG
      hyp.S_maximal
      (Or.inr (OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2))
  intro z hz
  rcases hz with hzP | hzV
  · -- `P^# ⊆ A(S) ⊆ A₀(S)`.
    refine honestTypeP2ASet_subset_A0Set hyp.Sdata ?_
    obtain ⟨hzP_mem, hz1⟩ := hzP
    rw [Set.mem_singleton_iff] at hz1
    refine mem_honestTypeP2ASet.mpr ⟨?_, hz1, z, ⟨hPeq ▸ hzP_mem, ?_⟩, ?_⟩
    · have hPle : hyp.P ≤ derivedInG hyp.S := by
        rw [hyp.S_deriv_eq_PU]; exact le_sup_left
      exact hPle hzP_mem
    · rwa [Set.mem_singleton_iff]
    · exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
        rw [Set.mem_singleton_iff] at hw; subst hw; rfl
  · exact Set.mem_union_right _ hzV

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.a), `'A0(S)`-support form**: `supp(β_j) ⊆ 'A0(S)` for `j ≠ 0`.

The Coq `A0beta` (`PFsection13.v:1870`), obtained from `PVSbeta` (`β_j ∈ 'CF(S, P^# ∪ V_S)`,
`PFsection13.v:1833`) via `P^# ∪ V_S ⊆ 'A0(S)`.  `PVSbeta` cancels the induced permutation character
`Ind_{PW₁}^S 1` against `μ_{0j}` off `P^# ∪ V_S`, using the `W₁`-class `normedTI` structure in
`S̄ = S/P = Ū ⋊ W̄₁` (Coq `gammaW1`) together with the prime-`TI` residue value `prTIirr_id`; both
bottom out at the shared prime-`TI` residue content (issue 9014) that connects the free `μ`-grid to
the σ-residue theory.  **This single `'A0`-support obligation is what both `gammaGrid_orthogonal_one`
and `gammaGrid_Y_norm_bound` reduce to** (the honest `'A0`-Dade=Ind bridge
`sInstance_dade0_eq_induce`, issue 9076, then discharges the remaining Dade content). -/
theorem betaGrid_A0_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    (betaGrid hyp j).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2A0Set hyp.S hyp.Sdata) hyp.S := by
  intro z hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  exact sharpP_union_V_subset_A0 hG hyp (betaGrid_support hG hyp j hj hz)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c)** `⟨Γ, 1_G⟩ = 0`.

**De-scaffolded** (issue 9076): the `'A0(S)` `normedTI` content the old docstring flagged as
"missing" is now supplied by the honest `'A0`-Dade=Ind bridge `sInstance_dade0_eq_induce`.  Reduction
(Coq `oGamma1`): `⟨Γ,1⟩ = ⟨τ_S β_{#1},1⟩ − ⟨1,1⟩ + ⟨η_{01},1⟩`, and
* `⟨1,1⟩ = 1` (`constOne_inner_self_eq_one`);
* `⟨η_{01},1⟩ = 0` — grid orthogonality: `1_G = η_{00}` (`eta_principal_eq_trivial`) and `η_{01} ⊥
  η_{00}` (`eta_orthonormal`);
* `⟨τ_S β_{#1},1_G⟩ = 1` — the bridge gives `τ_S β_{#1} = Ind_S^G β_{#1}` (needs `β_{#1}` supported in
  `'A0(S)`, `betaGrid_A0_support`), so by Frobenius reciprocity (`inner_induce_eq_inner_restrict`)
  `⟨Ind_S^G β_{#1}, 1_G⟩ = ⟨β_{#1}, 1_S⟩ = ⟨Ind_{PW₁}^S 1, 1_S⟩ − ⟨μ_{01}, 1_S⟩ = 1 − 0`, where
  `⟨Ind 1, 1_S⟩ = 1` (`inner_induce_trivialChar_constOne_eq_one`) and `⟨μ_{01}, 1_S⟩ = 0` (`μ_{01}`
  irreducible and `≠ 1_S`, since `⟨Ind 1, μ_{01}⟩ = 0 ≠ 1`, `indPW1_inner_mu`).

The **single** remaining gate is `betaGrid_A0_support` (the (13.18.a) `'A0`-support). -/
private theorem gammaGrid_orthogonal_one_aux [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ClassFunction.inner (GammaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
  classical
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Fintype ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `⟨Ind_{PW₁}^S 1, 1_S⟩ = 1`.
  have hind : ClassFunction.inner (indPW1 hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S)) = 1 := by
    rw [indPW1, ← OddOrder.RepresentationTheory.IrreducibleCharacter.coe_trivialIrreducibleCharacter]
    exact OddOrder.Peterfalvi.S09.Cert.inner_induce_trivialChar_constOne_eq_one
      ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
  -- `⟨μ_{01}, 1_S⟩ = 0`: `μ_{01}` is irreducible and `≠ 1_S` (else `⟨Ind 1, μ_{01}⟩ = 1 ≠ 0`).
  have hmu : ClassFunction.inner
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S)) = 0 := by
    have hIμ : ClassFunction.inner (indPW1 hyp)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 :=
      indPW1_inner_mu hG hyp ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)
    have hne : (⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩,
          hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩⟩ :
          OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
        ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥hyp.S := by
      intro heq
      apply one_ne_zero (α := ℂ)
      have hcf : hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
          = OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S) :=
        congrArg (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S =>
          (χ : ClassFunction ↥hyp.S ℂ)) heq
      rw [hcf, hind] at hIμ
      exact hIμ
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩,
        hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥hyp.S)
    rw [if_neg hne] at hite
    exact hite
  -- `⟨τ_S(β_{#1}), 1_G⟩ = 1` via the `'A0`-Dade=Ind bridge + Frobenius reciprocity.
  have htau : ClassFunction.inner (tauSbetaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 1 := by
    have hbridge : tauSbetaGrid hG hyp
        = ClassFunction.induce hyp.S (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩) := by
      rw [tauSbetaGrid]
      exact hyp.sInstance_dade0_eq_induce hG
        (betaGrid_A0_support hG hyp ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num))
    rw [hbridge, ClassFunction.inner_induce_eq_inner_restrict]
    have hres : ClassFunction.restrict hyp.S
        (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
        = OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S) := by
      ext x; rw [ClassFunction.restrict_apply]; rfl
    rw [hres]
    simp only [betaGrid]
    rw [ClassFunction.inner_sub_left, hind, hmu, sub_zero]
  -- `⟨η_{01}, 1_G⟩ = 0`.
  have heta : ClassFunction.inner
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
    have h00 : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ := by
      rw [OddOrder.Peterfalvi.S16.eta_principal_eq_trivial hyp]; rfl
    rw [h00]
    have horth := OddOrder.Peterfalvi.S16.eta_orthonormal hyp
      ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.q_prime.pos⟩
      ⟨1, by have := hyp.three_le_p; omega⟩ ⟨0, hyp.p_prime.pos⟩
    rw [if_neg (by rintro ⟨-, h2⟩; exact absurd (congrArg Fin.val h2) (by norm_num))] at horth
    exact horth
  rw [GammaGrid, ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one, htau, heta]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c)** `⟨Γ, 1_G⟩ = 0` (public form).  Thin wrapper over `gammaGrid_orthogonal_one_aux`
that reconciles the caller's `Fintype G`/`Invertible (Nat.card G : ℂ)` instances with the
`FiniteInduce`-scoped ones the core proof uses (both are `Subsingleton`). -/
theorem gammaGrid_orthogonal_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ClassFunction.inner (GammaGrid hG hyp)
        (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
  intro _ _
  convert gammaGrid_orthogonal_one_aux hG hyp using 2 <;> exact Subsingleton.elim _ _

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c)** `Γ` is real: `Γ.conj = Γ` — fully proven (Coq `GammaReal`,
`PFsection13.v:1911`).

Conjugation commutes with the Dade lift on `A₀(S)`-supported inputs
(`dadeIntegralCharacterMap_conj_of_support` at `betaGrid_A0_support`) and with induction
(`induce_conj`, the trivial character being real), and sends grid entries to the negated index
(`mu_conj`/`eta_conj`, the CF-level (4.9.a)/(3.9.a) fields; `finNeg 0 = 0`).  So
`Γ̄ = τ_S(β_{−#1}) − 1_G + η_{0,−#1}`, which is `Γ` by the proven `j`-independence
`gammaGrid_defGamma` at the conjugate column `−#1 = p−1 ≠ 0`. -/
theorem gammaGrid_real [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (GammaGrid hG hyp).conj = GammaGrid hG hyp := by
  classical
  set j1 : Fin hyp.p := ⟨1, by have := hyp.three_le_p; omega⟩ with hj1def
  set j' : Fin hyp.p := OddOrder.Peterfalvi.S15.finNeg hyp.p_prime.pos j1 with hj'def
  have hp3 := hyp.three_le_p
  have hj'0 : (j' : ℕ) ≠ 0 := by
    simp only [hj'def, OddOrder.Peterfalvi.S15.finNeg, hj1def]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hneg0 : OddOrder.Peterfalvi.S15.finNeg hyp.q_prime.pos ⟨0, hyp.q_prime.pos⟩
      = ⟨0, hyp.q_prime.pos⟩ := by
    apply Fin.ext
    simp [OddOrder.Peterfalvi.S15.finNeg]
  -- the trivial pieces are real
  have hconst : (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G).conj
      = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G := by
    ext g
    simp [OddOrder.Peterfalvi.S09.Hypothesis71.constOne, ClassFunction.conj_apply]
  -- `β̄_{#1} = β_{−#1}`: `Ind_{PW₁}^S 1` is real, `μ̄_{01} = μ_{0,−#1}`
  have hbeta_conj : (betaGrid hyp j1).conj = betaGrid hyp j' := by
    rw [betaGrid, betaGrid, ClassFunction.conj_sub, hyp.mu_conj ⟨0, hyp.q_prime.pos⟩ j1,
      hneg0]
    congr 1
    rw [indPW1, ClassFunction.induce_conj]
    congr 1
    ext g
    simp [ClassFunction.conj_apply, trivialClassFunction]
  -- the Dade lift commutes with conjugation on the `A₀(S)`-supported `β_{#1}`
  have hDconj : (tauSbetaGrid hG hyp).conj
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG))
          (betaGrid hyp j') := by
    rw [tauSbetaGrid,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_conj_of_support _ _
        (betaGrid_A0_support hG hyp j1 (by simp [hj1def])),
      hbeta_conj]
  -- assemble and close by `defGamma` at the conjugate column
  rw [show GammaGrid hG hyp = tauSbetaGrid hG hyp
      - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
      + hyp.eta ⟨0, hyp.q_prime.pos⟩ j1 from rfl,
    ClassFunction.conj_add, ClassFunction.conj_sub, hDconj, hconst,
    hyp.eta_conj ⟨0, hyp.q_prime.pos⟩ j1, hneg0]
  exact gammaGrid_defGamma hG hyp j' hj'0

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The (13.18) residual `Γ` is a virtual character**: each constituent of
`Γ = τ_S(β_{#1}) − 1_G + η_{01}` lies in `ℤ[Irr G]` — the Dade image via the `'A0` Dade=Ind
bridge (`sInstance_dade0_eq_induce` + `induce_mem_ZIrr`, with `β_{#1} ∈ ℤ[Irr S]` from
`induce_mem_ZIrr` on the trivial character and irreducibility of `μ_{01}`), the trivial
character, and `η_{01} = τ₃(ω_{01})` (`tau3_mem_ZIrr` + `omega_mem_ZIrr`).  Feeds the
integrality of `⟨Γ, η_{01}⟩` in the (13.18.d) bound. -/
theorem gammaGrid_mem_ZIrr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    GammaGrid hG hyp ∈ OddOrder.RepresentationTheory.ZIrr G := by
  classical
  have hp3 := hyp.three_le_p
  set j1 : Fin hyp.p := ⟨1, by omega⟩ with hj1def
  have hj1ne : (j1 : ℕ) ≠ 0 := by simp [hj1def]
  have hβZ : betaGrid hyp j1 ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S := by
    refine Submodule.sub_mem _ ?_
      (OddOrder.RepresentationTheory.IsIrreducibleCharacter.mem_ZIrr
        (hyp.mu_irreducible _ j1))
    have htriv := (OddOrder.RepresentationTheory.trivialIrreducibleCharacter
      ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)).isIrreducible
    rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_trivialIrreducibleCharacter]
      at htriv
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr _
      (OddOrder.RepresentationTheory.IsIrreducibleCharacter.mem_ZIrr htriv)
  have hTZ : tauSbetaGrid hG hyp ∈ OddOrder.RepresentationTheory.ZIrr G := by
    rw [tauSbetaGrid,
      hyp.sInstance_dade0_eq_induce hG (betaGrid_A0_support hG hyp j1 hj1ne)]
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr _ hβZ
  rw [show GammaGrid hG hyp = tauSbetaGrid hG hyp
      - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
      + hyp.eta ⟨0, hyp.q_prime.pos⟩ j1 from rfl]
  refine Submodule.add_mem _ (Submodule.sub_mem _ hTZ ?_) ?_
  · have htriv := (OddOrder.RepresentationTheory.trivialIrreducibleCharacter G).isIrreducible
    rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_trivialIrreducibleCharacter]
      at htriv
    exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.mem_ZIrr htriv
  · rw [hyp.eta_eq_tau_omega]
    exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ j1)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- Core of the **(13.18.d) residual-norm bound**, with the `FiniteInduce`-scoped instances
(Coq `PFsection13.v:1915-1934`).  The chain: `‖τ_S β₁‖² = ‖β₁‖² = (u−1)/q + 2` (Dade isometry
on `A₀(S)`-support + `betaGrid_norm`); peel `1_G` (`⟨Γ,1⟩ = 0`, `⟨η_{01},1⟩ = 0`), peel `Y`
(`X ⊥ Y`, `Y ⊥ η`-grid); then split `X − η_{01} = X₁ + a·η_{0,−1} + (a−1)·η_{01}` where
`a = ⟨Γ, η_{01}⟩ ∈ ℤ` (`gammaGrid_mem_ZIrr`), using `Γ` real ((13.18.c)) and
`η̄_{01} = η_{0,−1} ⊥ η_{01}`; drop `‖X₁‖² ≥ 0` and close with the integer inequality
`a² + (a−1)² ≥ 1`. -/
private theorem gammaGrid_Y_norm_bound_aux [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (X Y : ClassFunction G ℂ) (defXY : GammaGrid hG hyp = X + Y)
    (oXY : ClassFunction.inner X Y = 0)
    (oYeta : ∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) :
    (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ) := by
  classical
  have hp3 := hyp.three_le_p
  set j1 : Fin hyp.p := ⟨1, by omega⟩ with hj1def
  set i0 : Fin hyp.q := ⟨0, hyp.q_prime.pos⟩ with hi0def
  set j' : Fin hyp.p := OddOrder.Peterfalvi.S15.finNeg hyp.p_prime.pos j1 with hj'def
  have hj1ne : (j1 : ℕ) ≠ 0 := by simp [hj1def]
  set η01 : ClassFunction G ℂ := hyp.eta i0 j1 with hη01def
  set η01' : ClassFunction G ℂ := hyp.eta i0 j' with hη01'def
  -- index bookkeeping: `j' ≠ j1`, `j1 ≠ 0`, `finNeg 0 = 0`
  have hj'ne : j' ≠ j1 := by
    intro h
    have hval := congrArg Fin.val h
    simp only [hj'def, OddOrder.Peterfalvi.S15.finNeg, hj1def] at hval
    rw [Nat.mod_eq_of_lt (by omega)] at hval
    omega
  have hneg0 : OddOrder.Peterfalvi.S15.finNeg hyp.q_prime.pos i0 = i0 := by
    apply Fin.ext
    simp [OddOrder.Peterfalvi.S15.finNeg, hi0def]
  -- `η̄_{01} = η_{0,−1}` (the (3.9.a) conj-pair field at `finNeg 0 = 0`)
  have hconj : η01.conj = η01' := by
    rw [hη01def, hyp.eta_conj i0 j1, hneg0, hη01'def, hj'def]
  -- grid orthonormality instances
  have h_11 : ClassFunction.inner η01 η01 = 1 := by
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j1 j1
    rw [if_pos ⟨rfl, rfl⟩] at h
    exact h
  have h_1'1 : ClassFunction.inner η01' η01 = 0 := by
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j' j1
    rw [if_neg (by rintro ⟨-, h2⟩; exact hj'ne h2)] at h
    exact h
  have h_11' : ClassFunction.inner η01 η01' = 0 := by
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j1 j'
    rw [if_neg (by rintro ⟨-, h2⟩; exact hj'ne h2.symm)] at h
    exact h
  have h_1'1' : ClassFunction.inner η01' η01' = 1 := by
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j' j'
    rw [if_pos ⟨rfl, rfl⟩] at h
    exact h
  -- `1_G = η_{00}` and its orthogonalities
  have hone : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
      = hyp.eta i0 ⟨0, hyp.p_prime.pos⟩ := by
    rw [OddOrder.Peterfalvi.S16.eta_principal_eq_trivial hyp]
    rfl
  have hη01_one : ClassFunction.inner η01
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
    rw [hone]
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j1 ⟨0, hyp.p_prime.pos⟩
    rw [if_neg (by
      rintro ⟨-, h2⟩
      exact hj1ne (by simpa using congrArg Fin.val h2))] at h
    exact h
  have hΓone : ClassFunction.inner (GammaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 :=
    gammaGrid_orthogonal_one hG hyp
  -- Pythagoras helper
  have pyth : ∀ A B : ClassFunction G ℂ, ClassFunction.inner A B = 0 →
      ClassFunction.inner (A + B) (A + B)
        = ClassFunction.inner A A + ClassFunction.inner B B := by
    intro A B hAB
    have hBA : ClassFunction.inner B A = 0 := by
      rw [ClassFunction.inner_star_comm, hAB, star_zero]
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, hAB, hBA]
    ring
  -- the isometry: `‖τ_S β₁‖² = ‖β₁‖² = (u−1)/q + 2`
  have hTT : ClassFunction.inner (tauSbetaGrid hG hyp) (tauSbetaGrid hG hyp)
      = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ) := by
    rw [tauSbetaGrid,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypS0 hG) (hyp.dadeHypS0_hconj hG)
        (betaGrid_A0_support hG hyp j1 hj1ne) (betaGrid_A0_support hG hyp j1 hj1ne)]
    exact betaGrid_norm hG hyp j1 hj1ne
  -- Pythagoras 1: `τ_S β₁ = (Γ − η_{01}) + 1_G`
  have hTdecomp : tauSbetaGrid hG hyp
      = (GammaGrid hG hyp - η01) + OddOrder.Peterfalvi.S09.Hypothesis71.constOne G := by
    rw [show GammaGrid hG hyp = tauSbetaGrid hG hyp
        - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + η01 from rfl]
    abel
  have hP1 : ClassFunction.inner (tauSbetaGrid hG hyp) (tauSbetaGrid hG hyp)
      = ClassFunction.inner (GammaGrid hG hyp - η01) (GammaGrid hG hyp - η01) + 1 := by
    rw [hTdecomp, pyth _ _ (by
      rw [ClassFunction.inner_sub_left, hΓone, hη01_one, sub_zero]),
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one]
  -- Pythagoras 2: `Γ − η_{01} = (X − η_{01}) + Y`
  have hP2 : ClassFunction.inner (GammaGrid hG hyp - η01) (GammaGrid hG hyp - η01)
      = ClassFunction.inner (X - η01) (X - η01) + ClassFunction.inner Y Y := by
    have hd : GammaGrid hG hyp - η01 = (X - η01) + Y := by rw [defXY]; abel
    have oY01 : ClassFunction.inner Y η01 = 0 := oYeta i0 j1
    rw [hd, pyth _ _ (by
      rw [ClassFunction.inner_sub_left, oXY]
      rw [show ClassFunction.inner η01 Y = 0 by
        rw [ClassFunction.inner_star_comm, oY01, star_zero]]
      ring)]
  -- the grid coefficient `a = ⟨Γ, η_{01}⟩` is an integer `m`
  have hηZ : η01 ∈ OddOrder.RepresentationTheory.ZIrr G := by
    rw [hη01def, hyp.eta_eq_tau_omega]
    exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr i0 j1)
  obtain ⟨m, hm⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int
    (gammaGrid_mem_ZIrr hG hyp) hηZ
  -- `⟨X, η_{01}⟩ = m` and `⟨X, η_{0,−1}⟩ = m` (the latter via `Γ` real + conj-pair)
  have hXη : ClassFunction.inner X η01 = (m : ℂ) := by
    have h := congrArg (fun φ : ClassFunction G ℂ => ClassFunction.inner φ η01) defXY
    simp only [ClassFunction.inner_add_left] at h
    have oY01 : ClassFunction.inner Y η01 = 0 := oYeta i0 j1
    rw [oY01, add_zero] at h
    rw [← h, hm]
  have hΓη' : ClassFunction.inner (GammaGrid hG hyp) η01' = (m : ℂ) := by
    rw [← hconj, ← gammaGrid_real hG hyp,
      OddOrder.RepresentationTheory.ClassFunction.inner_conj_conj,
      ClassFunction.inner_star_comm, hm, star_intCast]
  have hXη' : ClassFunction.inner X η01' = (m : ℂ) := by
    have h := congrArg (fun φ : ClassFunction G ℂ => ClassFunction.inner φ η01') defXY
    simp only [ClassFunction.inner_add_left] at h
    have oY01' : ClassFunction.inner Y η01' = 0 := oYeta i0 j'
    rw [oY01', add_zero] at h
    rw [← h, hΓη']
  -- Pythagoras 3+4: `X − η_{01} = (X₁ + m·η_{0,−1}) + (m−1)·η_{01}`
  set X1 : ClassFunction G ℂ := X - (m : ℂ) • η01 - (m : ℂ) • η01' with hX1def
  have hX1η : ClassFunction.inner X1 η01 = 0 := by
    rw [hX1def, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
      hXη, h_11, h_1'1]
    ring
  have hX1η' : ClassFunction.inner X1 η01' = 0 := by
    rw [hX1def, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
      hXη', h_11', h_1'1']
    ring
  have hXdecomp : X - η01 = (X1 + (m : ℂ) • η01') + ((m : ℂ) - 1) • η01 := by
    rw [hX1def, sub_smul, one_smul]
    abel
  have hstar_m : star ((m : ℂ)) = (m : ℂ) := star_intCast m
  have hstar_m1 : star ((m : ℂ) - 1) = (m : ℂ) - 1 := by
    rw [star_sub, star_one, hstar_m]
  have hP3 : ClassFunction.inner (X - η01) (X - η01)
      = ClassFunction.inner (X1 + (m : ℂ) • η01') (X1 + (m : ℂ) • η01')
        + ((m : ℂ) - 1) * ((m : ℂ) - 1) := by
    rw [hXdecomp, pyth _ _ (by
      rw [ClassFunction.inner_smul_right, ClassFunction.inner_add_left,
        ClassFunction.inner_smul_left, hX1η, h_1'1]
      ring)]
    rw [ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, hstar_m1, h_11]
    ring
  have hP4 : ClassFunction.inner (X1 + (m : ℂ) • η01') (X1 + (m : ℂ) • η01')
      = ClassFunction.inner X1 X1 + (m : ℂ) * (m : ℂ) := by
    rw [pyth _ _ (by rw [ClassFunction.inner_smul_right, hX1η', hstar_m]; ring),
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, hstar_m, h_1'1']
    ring
  -- assemble the ℂ-level identity and take real parts
  have hX1re := OddOrder.RepresentationTheory.ClassFunction.inner_self_eq_re X1
  have hchain : ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ)
      = (((ClassFunction.inner X1 X1).re : ℝ) : ℂ)
        + ((m * m + (m - 1) * (m - 1) : ℤ) : ℂ)
        + ClassFunction.inner Y Y + 1 := by
    rw [← hTT, hP1, hP2, hP3, hP4, ← hX1re]
    push_cast
    ring
  have hre := congrArg Complex.re hchain
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.intCast_re,
    Complex.ratCast_re] at hre
  -- final integer inequality `m² + (m−1)² ≥ 1` and the nonnegativity of `‖X₁‖²`
  have hmm1 : (1 : ℤ) ≤ m * m + (m - 1) * (m - 1) := by
    by_cases h : 1 ≤ m
    · nlinarith
    · have h' : m ≤ 0 := by omega
      nlinarith
  have hX1nonneg : 0 ≤ (ClassFunction.inner X1 X1).re :=
    OddOrder.RepresentationTheory.ClassFunction.inner_self_re_nonneg X1
  have hmm1' : (1 : ℝ) ≤ ((m * m + (m - 1) * (m - 1) : ℤ) : ℝ) := by exact_mod_cast hmm1
  have hgoal : (ClassFunction.inner Y Y).re
      = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℝ)
        - (ClassFunction.inner X1 X1).re
        - ((m * m + (m - 1) * (m - 1) : ℤ) : ℝ) - 1 := by linarith [hre]
  rw [hgoal]
  push_cast at hmm1' ⊢
  linarith

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.d) residual-norm bound**: for any split `Γ = X + Y` with `X ⊥ Y` and `Y` orthogonal
to the whole `η`-grid `{η_{ik}}`, `‖Y‖² ≤ (u−1)/q` — fully proven (Coq `PFsection13.v:1915-1934`;
the earlier `Re⟨Γ,Γ⟩ ≤ (u−1)/q + 1` overstatement was corrected in issue 3003: `‖Γ‖²` itself is
**not** bounded, only the grid-orthogonal residual `Y`).  Public form of
`gammaGrid_Y_norm_bound_aux`, reconciling the caller's `Fintype G`/`Invertible` instances with
the `FiniteInduce`-scoped ones (both are `Subsingleton`). -/
theorem gammaGrid_Y_norm_bound [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (X Y : ClassFunction G ℂ), GammaGrid hG hyp = X + Y →
        ClassFunction.inner X Y = 0 →
        (∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) →
        (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ) := by
  intro _ _ X Y defXY oXY oYeta
  have h := gammaGrid_Y_norm_bound_aux hG hyp X Y defXY
    (by convert oXY using 2; exact Subsingleton.elim _ _)
    (fun i k => by convert oYeta i k using 2; exact Subsingleton.elim _ _)
  convert h using 3
  exact Subsingleton.elim _ _

/-- **Faithful §13 producer for Peterfalvi (13.18).**  The (13.18) virtual characters `β_j`/`Γ`
and their genuine properties (support (13.18.a), the (13.18.b) norm `‖β_j‖² = (u−1)/q + 2`,
orthogonality of `Γ` to `1_G`, reality, and the (13.18.d) `‖Y‖²` residual bound) are supplied here.
The concrete `β_j = betaGrid hyp j` and `Γ = GammaGrid hG hyp` are built from the honest `S`-side
Dade isometry `τ_S` (`hyp.dadeHypS0`, **not** the `= 0` placeholder `hyp.tauS`) and the induced
trivial character `Ind_{PW₁}^S 1`.  The bundled properties are the precisely-isolated §13
obligations `betaGrid_support` / `betaGrid_norm` / `gammaGrid_orthogonal_one` /
`gammaGrid_real` / `gammaGrid_Y_norm_bound`; the (13.18.c) `j`-independence is the standalone
`gammaGrid_defGamma` (proven, modulo the (4.8)/(5.3) cross-relation `tauS_mu_row0_cross`).
Their deep content bottoms out at the (13.2.e) `A₀(S)` normedTI Dade=Ind bridge, the (5.3)
`S`↔`W` Dade cross-relation, and the Frobenius norm `norm_induce_one_frobenius`. -/
noncomputable def betaData_of_grid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    BetaData hyp where
  j := j
  j_ne_zero := hj
  beta := betaGrid hyp j
  Gamma := GammaGrid hG hyp
  support_formula := betaGrid_support hG hyp j hj
  norm_formula := betaGrid_norm hG hyp j hj
  Gamma_orthogonal_one := gammaGrid_orthogonal_one hG hyp
  Gamma_real := gammaGrid_real hG hyp
  Y_norm_bound := gammaGrid_Y_norm_bound hG hyp

/-- **Peterfalvi (13.18)**: the virtual character `beta_j` has controlled
support, norm, and orthogonal remainder.

De-opacified (W3 §15): the conclusions are the genuine (13.18) statements — `β_j`'s support
control (13.18.a), the (13.18.b) norm `‖β_j‖² = (u−1)/q + 2`, and the residual `Γ`'s orthogonality
to `1_G` (13.18.c), reality (13.18.c), and the (13.18.d) `‖Y‖²` bound — each about the produced
characters `data.beta`/`data.Gamma`.  They are the genuine fields of the faithful producer
`betaData_of_grid`; the (13.18.b) Frobenius induced-trivial norm half is the already-proven
`norm_induce_one_frobenius`.  The (13.18.c) `j`-independence half is the standalone
`gammaGrid_defGamma` (kept separate to avoid mixing the `FiniteInduce` `τ_S` instances with the
explicit inner-product instance binders here).  (The earlier grid-orthogonality and `‖Γ‖²`
conjuncts were overstatements — issue 3003.) -/
theorem beta_support_norm_and_remainder [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∃ data : BetaData hyp,
      (data.beta.support ⊆
        {z : ↥hyp.S |
          (z : G) ∈ OddOrder.GroupTheory.sharpSubgroup hyp.P ∪
            OddOrder.GroupTheory.conjClassSetIn hyp.S
              (OddOrder.GroupTheory.typePV hyp.S hyp.Sdata)}) ∧
        (∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
          ClassFunction.inner data.beta data.beta
            = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ)) ∧
        (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
          ClassFunction.inner data.Gamma
            (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0) ∧
        data.Gamma.conj = data.Gamma ∧
        (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
          ∀ (X Y : ClassFunction G ℂ), data.Gamma = X + Y →
            ClassFunction.inner X Y = 0 →
            (∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) →
            (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ)) := by
  -- The principal index `j = 1` (nonzero, using `p ≥ 3`).
  have hp3 : 3 ≤ hyp.p := hyp.three_le_p
  refine ⟨betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp),
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).support_formula,
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).norm_formula,
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).Gamma_orthogonal_one,
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).Gamma_real,
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).Y_norm_bound⟩

/-- The parity conclusion in Peterfalvi (13.19.c2): the character inner
product is an odd integer, recorded inside `ℂ`. -/
def OddIntegerInner (χ ψ : ClassFunction G ℂ) : Prop :=
  ∃ n : ℤ, Odd n ∧
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)], ClassFunction.inner χ ψ = (n : ℂ)

/-- Carrier for the type-I comparison in Peterfalvi (13.19). -/
structure TypeIOrthogonalityData (hyp : Hypothesis (G := G)) (L : Subgroup G) where
  typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L
  e : ℕ
  e_eq_index : Prop
  Lset : Set (ClassFunction ↥L ℂ)
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  phi : ClassFunction ↥L ℂ
  phi_mem : phi ∈ Lset
  phi_degree_eq_e : phi 1 = (e : ℂ)
  betaL : ClassFunction G ℂ
  betaS : ClassFunction G ℂ
  disjoint_support : Prop
  Ltau_orthogonal_eta : Prop
  betaL_eta_independent : Prop
  caseC1 : Prop
  caseC2 : Prop
  caseC2_eta0j_odd :
    caseC2 →
      ∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
  caseC1_bound :
    caseC1 →
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))
  caseC1_dual : Prop
  caseC2_dual : Prop
  caseC2_dual_etai0_odd :
    caseC2_dual →
      ∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
  caseC1_dual_bound :
    caseC1_dual →
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))

namespace TypeIOrthogonalityData

/-- **Peterfalvi (13.19.c)**, consumer form: any strict gap beyond the
case-(c1) bound forces the parity alternative (c2). -/
theorem caseC2_of_gap {hyp : Hypothesis (G := G)} {L : Subgroup G}
    (data : TypeIOrthogonalityData hyp L)
    (hcases : data.caseC1 ∨ data.caseC2)
    (hgap :
      ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ) <
        ((Nat.card ↥data.typeISetup.H - 1 : ℕ) : ℚ) / (data.e : ℚ)) :
    data.caseC2 := by
  rcases hcases with hcaseC1 | hcaseC2
  · exact False.elim ((not_lt_of_ge (data.caseC1_bound hcaseC1)) hgap)
  · exact hcaseC2

/-- **Peterfalvi (13.19.c)** after swapping `S` and `T`: any strict gap beyond
`(v - 1) / p` excludes the dual case-(c1) bound and forces the dual parity
alternative (c2), the source of the `eta_i0` congruences. -/
theorem caseC2_dual_of_gap {hyp : Hypothesis (G := G)} {L : Subgroup G}
    (data : TypeIOrthogonalityData hyp L)
    (hcases : data.caseC1_dual ∨ data.caseC2_dual)
    (hgap :
      ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ) <
        ((Nat.card ↥data.typeISetup.H - 1 : ℕ) : ℚ) / (data.e : ℚ)) :
    data.caseC2_dual := by
  rcases hcases with hcaseC1 | hcaseC2
  · exact False.elim ((not_lt_of_ge (data.caseC1_dual_bound hcaseC1)) hgap)
  · exact hcaseC2

/-- **Peterfalvi (13.19.c2)**: once both S- and T-side parity alternatives
hold, the two zero-axis families of `eta` have odd integer inner product with
`beta_L`. -/
theorem eta_axes_odd_of_caseC2_pair {hyp : Hypothesis (G := G)} {L : Subgroup G}
    (data : TypeIOrthogonalityData hyp L) (hcases : data.caseC2 ∧ data.caseC2_dual) :
    (∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner data.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧
      (∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner data.betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) := by
  exact ⟨data.caseC2_eta0j_odd hcases.1, data.caseC2_dual_etai0_odd hcases.2⟩

end TypeIOrthogonalityData

/-- **Faithful §13 grid/Dade producer for Peterfalvi (13.19).**

Given a type-I maximal subgroup `L` with its (12.1) `S14.Hypothesis` `typeISetup`, this bundles the
genuinely grid-dependent data and facts of (13.19) against a concrete kernel index `e`, family
`Lset` and generator `phi`:

* the Dade images `β_L`, `β_S`, disjoint-supported (13.18.a-style);
* `phi ∈ Lset` of degree `e = |L : H|`;
* **(13.19.a)** `L^{τ₁} ⊥ {η_ij}` and `β_L ⊥ {η_ij}` (grid orthogonality, the `Ltau_orthogonal_eta`
  / `betaL_eta_independent` content), bottoming out at the (3.9) `τ`-isometry (σ-pinned);
* **(13.19.c)** the S- and T-side dichotomies `caseC1 ∨ caseC2` where `caseC1` is the rational
  degree bound `(|H|−1)/e ≤ (u−1)/q` and `caseC2` is the genuine `η`-axis odd-integer parity
  `∀ j ≠ 0, ⟨β_L, η_0j⟩ ∈ 2ℤ+1` (dual: `(v−1)/p`, `η_i0`).

Everything grid-dependent is isolated here; the assembling theorem
`typeI_orthogonality_dichotomy` supplies the honest §14 `typeISetup`, the `τ₁ = typeISetup.tau`
Dade map, and reads the dichotomy implication fields off as identities (no over-claim). -/
structure TypeIOrthogonalityGridData (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) where
  e : ℕ
  e_eq_index : ((maxNilpotentNormalHall L).subgroupOf L).index = e
  Lset : Set (ClassFunction ↥L ℂ)
  phi : ClassFunction ↥L ℂ
  phi_mem : phi ∈ Lset
  phi_degree_eq_e : phi 1 = (e : ℂ)
  betaL : ClassFunction G ℂ
  betaS : ClassFunction G ℂ
  /-- The T-side companion `β_T^τ` (the S↔T-swapped `β_S^τ`), pairing with `φ^{τ₁}` in the dual
  (13.19.c1) parity. -/
  betaT : ClassFunction G ℂ
  disjoint_support : Disjoint betaL.support betaS.support
  /-- **(13.19)**: `β_L` is the Dade image `β_L^τ = (Ind_H^L 1_H − φ)^{τ₁}` (the extension
  `τ₁ = typeISetup.tau` agrees with `τ` on the `A(L)`-supported `Ind_H^L 1_H − φ`). -/
  betaL_eq :
    ∀ [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
      [Invertible (Nat.card ↥((typeISetup.H).subgroupOf L) : ℂ)],
      betaL = typeISetup.tau
        (ClassFunction.induce ((typeISetup.H).subgroupOf L)
          (trivialClassFunction ↥((typeISetup.H).subgroupOf L)) - phi)
  Ltau_orthogonal_eta :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i : Fin hyp.q) (j : Fin hyp.p),
        ClassFunction.inner (typeISetup.tau phi) (hyp.eta i j) = 0
  /-- **(13.19.c)**, first clause: `(β_L^τ, η_{0j})` is independent of `j` for `1 ≤ j < p`. -/
  betaL_eta0_row_constant :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (j j' : Fin hyp.p), (j : ℕ) ≠ 0 → (j' : ℕ) ≠ 0 →
        ClassFunction.inner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
          = ClassFunction.inner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j')
  /-- **(13.19.c)**, first clause after the S↔T swap: `(β_L^τ, η_{i0})` is independent of `i`
  for `1 ≤ i < q`. -/
  betaL_eta0_col_constant :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i i' : Fin hyp.q), (i : ℕ) ≠ 0 → (i' : ℕ) ≠ 0 →
        ClassFunction.inner betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
          = ClassFunction.inner betaL (hyp.eta i' ⟨0, hyp.p_prime.pos⟩)
  /-- **(13.19.c)** S-side dichotomy, faithful form: **(c1)** `(β_S^τ, φ^{τ₁}) ≡ 1 (mod 2)` and
  the degree bound `(|H|−1)/e ≤ (u−1)/q`, or **(c2)** the `η_{0j}` odd-parity and `p ≤ e`. -/
  caseC :
    (OddIntegerInner betaS (typeISetup.tau phi) ∧
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))) ∨
      ((∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧ hyp.p ≤ e)
  /-- **(13.19.c)** T-side (S↔T swapped) dichotomy, faithful form: **(c1)**
  `(β_T^τ, φ^{τ₁}) ≡ 1 (mod 2)` and `(|H|−1)/e ≤ (v−1)/p`, or **(c2)** the `η_{i0}` odd-parity
  and `q ≤ e`. -/
  caseC_dual :
    (OddIntegerInner betaT (typeISetup.tau phi) ∧
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))) ∨
      ((∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) ∧ hyp.q ≤ e)

/-- **Faithful §13 producer for Peterfalvi (13.19).**  The grid/Dade data and facts of (13.19) for a
type-I maximal `L` with its (12.1) Hypothesis `typeISetup`.  The construction is the §3/§4/§5
Dade-isometry layer for `L` (the (3.9) `τ`-isometry, σ-pinned via `S05_IntegralSigma`, giving the
`η`-grid orthogonality) plus the (13.19.c) degree/parity dichotomy from the coherence bounds;
this is the single isolated deep obligation.  Mirrors the `betaData_of_grid` /
`betaM_expansion_data` producer pattern. -/
noncomputable def typeIOrthogonalityGridData_of_typeISetup [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) :
    TypeIOrthogonalityGridData hyp typeISetup := sorry

/-- **Peterfalvi (13.19)**: a type-I maximal subgroup has `𝓛^{τ₁}` orthogonal to the `eta_ij`,
`(β_L^τ, η_{0j})` constant along each zero axis, and on each zero axis one of the two (13.19.c)
cases — the faithful conjunction forms `(c1) = parity ∧ degree bound` and
`(c2) = η-axis odd-parity ∧ p ≤ e` — holds.

De-opacified (W3 §15): the honest §14 content — the (12.1) `S14.Hypothesis` of `L`
(`S14.exists_typeI_hypothesis`) and its genuine Dade map `τ₁ = typeISetup.tau` —
is constructed here;
the opaque `Prop` fields of `TypeIOrthogonalityData` are instantiated to the **genuine** (13.19)
statements.  `betaL_eta_independent` is instantiated to the faithful (13.19.c) first clause — the
zero-axis **constancy** of `(β_L^τ, η_{0j})`/`(β_L^τ, η_{i0})` (NOT orthogonality: in case (c2)
these inner products are odd).  The dichotomy implication fields (`caseC1_bound`,
`caseC2_eta0j_odd`, dual) are the conjunction projections.  The grid-dependent atoms come from the
faithful producer `typeIOrthogonalityGridData_of_typeISetup`, whose type is the genuine (13.19)
grid content. -/
theorem typeI_orthogonality_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L) :
    ∃ data : TypeIOrthogonalityData hyp L,
      data.disjoint_support ∧ data.Ltau_orthogonal_eta ∧
        data.betaL_eta_independent ∧
          (data.caseC1 ∨ data.caseC2) ∧
            (data.caseC1_dual ∨ data.caseC2_dual) := by
  -- (12.1)/(14.*): the type-I maximal `L` carries a genuine `S14.Hypothesis` (honest own-logic).
  obtain ⟨typeISetup⟩ := OddOrder.Peterfalvi.S14.exists_typeI_hypothesis _hG hLmax hLI
  -- The grid/Dade atoms and facts (the single deep obligation).
  let g := typeIOrthogonalityGridData_of_typeISetup _hG hyp typeISetup
  -- Assemble `TypeIOrthogonalityData` with the genuine opaque-`Prop` choices and
  -- conjunction-projection dichotomy implication fields.
  refine ⟨{ typeISetup := typeISetup
            e := g.e
            e_eq_index := ((maxNilpotentNormalHall L).subgroupOf L).index = g.e
            Lset := g.Lset
            tau1 := typeISetup.tau
            phi := g.phi
            phi_mem := g.phi_mem
            phi_degree_eq_e := g.phi_degree_eq_e
            betaL := g.betaL
            betaS := g.betaS
            disjoint_support := Disjoint g.betaL.support g.betaS.support
            Ltau_orthogonal_eta :=
              ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
                ∀ (i : Fin hyp.q) (j : Fin hyp.p),
                  ClassFunction.inner (typeISetup.tau g.phi) (hyp.eta i j) = 0
            betaL_eta_independent :=
              (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
                ∀ (j j' : Fin hyp.p), (j : ℕ) ≠ 0 → (j' : ℕ) ≠ 0 →
                  ClassFunction.inner g.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
                    = ClassFunction.inner g.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j')) ∧
              (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
                ∀ (i i' : Fin hyp.q), (i : ℕ) ≠ 0 → (i' : ℕ) ≠ 0 →
                  ClassFunction.inner g.betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
                    = ClassFunction.inner g.betaL (hyp.eta i' ⟨0, hyp.p_prime.pos⟩))
            caseC1 :=
              OddIntegerInner g.betaS (typeISetup.tau g.phi) ∧
                (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (g.e : ℚ) ≤
                  ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))
            caseC2 :=
              (∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
                OddIntegerInner g.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧ hyp.p ≤ g.e
            caseC2_eta0j_odd := fun h => h.1
            caseC1_bound := fun h => h.2
            caseC1_dual :=
              OddIntegerInner g.betaT (typeISetup.tau g.phi) ∧
                (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (g.e : ℚ) ≤
                  ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))
            caseC2_dual :=
              (∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
                OddIntegerInner g.betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) ∧ hyp.q ≤ g.e
            caseC2_dual_etai0_odd := fun h => h.1
            caseC1_dual_bound := fun h => h.2 },
    g.disjoint_support, g.Ltau_orthogonal_eta,
    ⟨g.betaL_eta0_row_constant, g.betaL_eta0_col_constant⟩, g.caseC, g.caseC_dual⟩

end OddOrder.Peterfalvi.S15

