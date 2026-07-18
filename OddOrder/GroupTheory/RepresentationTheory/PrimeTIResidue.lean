/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.IsometryDifferencePair
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
import OddOrder.GroupTheory.RepresentationTheory.InducedTransport
import OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier
import OddOrder.Peterfalvi.S05_SigmaIsometry
import OddOrder.Peterfalvi.S06_CertainTypeClifford
import OddOrder.Peterfalvi.S06_CertainTypeSupport
import OddOrder.Peterfalvi.S07_Coherence
import OddOrder.Peterfalvi.S08_CoherenceCorePart1

/-!
# Prime-TI residue characters (Peterfalvi (4.5), Feit–Thompson (13.2–13.3))

This module ports the **core of the prime-TI residue theory** from mathcomp's
`character` library (`coq/theories/PFsection4.v`, definitions `primeTIred`,
`prTIres_irr_cases`, `cfInd_prTIres`), which Peterfalvi's `S1cases`
(`coq/theories/PFsection13.v:401-428`) depends on.

## Mathematical setup

Let `S = PU ⋊ W1` be a group with `W = W1 × W2` an abelian TI-subgroup of prime-order
cyclic factors (Peterfalvi Hypothesis (4.2) = Feit–Thompson (13.2)).  The **prime-TI
irreducibles** `mu2_ i j ∈ Irr(S)` (`i : Iirr W1`, `j : Iirr W2`) are the constituents of
the images `σ(w_ i j)` of the linear characters of `W` under the cyclic-TI isometry
`σ = cyclicTIiso`.  Their **column sums**

  `primeTIred j := μ_j := ∑_i mu2_ i j ∈ ℂ CF(S)`   (Coq `primeTIred`)

are *reducible* characters, and each `μ_j` is induced from an irreducible **residue**
`chi_ j ∈ Irr(PU)` of `PU = S'`:

  `Ind_{PU}^S (chi_ j) = μ_j`   (Coq `cfInd_prTIres`).

The constituent classification `prTIres_irr_cases` says: for every `θ ∈ Irr(PU)`, either
`θ = chi_ j` for some `j` (equivalently `Ind θ = μ_j`), or `Ind θ` is irreducible.

## What this file builds, and the port's shape

The construction of `mu2_ i j` itself sits on top of the **entire mathcomp cyclic-TI
isometry stack** (`cyclicTIiso`, `dirr_dIirr`, `PFsection3.v`), which is not yet in this
repo.  Following the established repo idiom for such deep character data
(`OddOrder.Peterfalvi.S06.Hypothesis46`, `SignedIrreducibleDifferenceFamily`,
`FullDadeIsometryData`), we **posit the (4.3.b)/(4.5.a) residue grid as fields** of a
structure `PrimeTIResidueData`, packaging the prime-TI irreducibles, their residues, and
their *defining relations* (each of which mathcomp's `primeTIirr_spec` / `prTIres_spec`
*proves*).  On top of these fields we then build, **sorry-free**, the derived residue API
that `S1cases` consumes:

* `primeTIred`, `prTIred_char`, `prTIred_neq0`, `prTIred_not_irr`;
* the inner products `cfdot_prTIirr_red`, `cfdot_prTIred`, `cfnorm_prTIred`, `prTIred_inj`;
* the induction formula `cfInd_prTIres` and restriction `cfRes_prTIred`;
* `prTIres0` (`chi_ 0 = 1`), `prTIred0`.

The single genuinely-deep sub-fact, `prTIres_irr_cases` (Peterfalvi (4.5.b), the inertia-group /
`p`-group fixed-point counting argument, Coq `PFsection4.v:620-665`), is **posited as the field
`PrimeTIResidueData.prTIres_irr_cases`** rather than derived: its mathcomp proof computes the
inertia group `'I_S[θ] = PU` from the cyclic-TI structure (`W1`, the decomposition
`S = PU ⋊ W1`, the `W1`-action on `Irr(PU)`, and `coprime |PU| |W1|`), which is exactly the data
that is abstracted away here and supplied by the constructor together with `mu2`/`chi`.  It is
therefore on the same honest footing as the other `cyclicTIiso`-provenance fields
(`mu2_orthonormal`, `chi_res`, `ind_chi`, `cfker_prTIres`), all of which are genuine mathcomp
theorems the constructor discharges.  With this the leaf is **sorry-free**.

The eventual **constructor** of `PrimeTIResidueData` (from a genuine
`primeTI_hypothesis`, via a Lean port of `cyclicTIiso` + `primeTIirr_spec`, which discharges
`prTIres_irr_cases` via `card_afix_irr_classes` + `IsPGroup.card_modEq_card_fixedPoints` and the
repo capstone `isIrreducibleCharacter_induce_of_inertia_eq`) is the multi-session continuation
tracked in `issues/9014-primeti-residue-api.md`.

## References

* Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §4,
  Theorems (4.3), (4.5).
* Coq: `coq/theories/PFsection4.v` (`primeTIred`, `cfInd_prTIres`, `prTIres_irr_cases`);
  `coq/theories/PFsection13.v:401-428` (`S1cases`, the consumer).
* `issues/9014-primeti-residue-api.md`.
-/

namespace OddOrder.RepresentationTheory

open scoped BigOperators
open OddOrder.Peterfalvi.S07 (zSpan)

/-! ### The prime-TI residue datum

`PrimeTIResidueData S PU q p` posits, over a group `S` with commutator-type subgroup
`PU ≤ S` (Coq `PU = S^(1)`), the prime-TI residue grid: `q = #|W1|` column-index bound
(indices `i : Fin q`), `p = #|W2|` residue-index bound (indices `j : Fin p`).  The fields
mirror the *conclusions* of `primeTIirr_spec` and `prTIres_spec`. -/

/-- **Prime-TI residue datum** (Peterfalvi (4.3.b)+(4.5.a), Coq `PFsection4.v`).

Bundles, over the pair `PU ≤ S`, the data that mathcomp derives from a
`primeTI_hypothesis` via `cyclicTIiso`:

* `mu2 i j ∈ Irr(S)` — the prime-TI irreducibles (`mu2_ i j`), `i : Fin q`, `j : Fin p`;
* `chi j ∈ Irr(PU)` — the residue characters (`chi_ j`), `j : Fin p`;

together with their defining relations (each a mathcomp theorem):

* `mu2_orthonormal`  : `⟨mu2 i j, mu2 i' j'⟩ = [i=i' ∧ j=j']`   (Coq `cfdot_prTIirr`);
* `chi_res`          : `chi j = Res_{PU} (mu2 0 j)`               (Coq `cfRes_prTIirr`);
* `ind_chi`          : `Ind_{PU}^S (chi j) = ∑_i mu2 i j`         (Coq `cfInd_prTIres`);
* `chi_zero`         : `chi 0 = 1_{PU}`                           (Coq `prTIres0`).

The grid columns `i ↦ mu2 i j` correspond to `SignedIrreducibleDifferenceFamily` columns
(cf. `OddOrder.Peterfalvi.S06.Hypothesis.columnFamily`). -/
structure PrimeTIResidueData (S : Type*) [Group S] [Fintype S]
    [Invertible (Nat.card S : ℂ)] (PU : Subgroup S) [Fintype ↥PU]
    [Invertible (Nat.card ↥PU : ℂ)] (q p : ℕ) [NeZero q] [NeZero p] where
  /-- The prime-TI irreducibles `mu2_ i j ∈ Irr(S)` (Coq `primeTIirr`). -/
  mu2 : Fin q → Fin p → IrreducibleCharacter S
  /-- The residue characters `chi_ j ∈ Irr(PU)` (Coq `primeTIres`). -/
  chi : Fin p → IrreducibleCharacter ↥PU
  /-- **(4.3.b)** Orthonormality `⟨mu2 i j, mu2 i' j'⟩ = [(i,j) = (i',j')]` (Coq
  `cfdot_prTIirr`): the `mu2 i j` are pairwise-distinct irreducibles. -/
  mu2_orthonormal : ∀ (i i' : Fin q) (j j' : Fin p),
    ClassFunction.inner (mu2 i j : ClassFunction S ℂ) (mu2 i' j' : ClassFunction S ℂ)
      = (if i = i' ∧ j = j' then 1 else 0)
  /-- **(4.5.a)** Restriction to `PU`: `chi j = Res_{PU} (mu2 0 j)` (Coq `cfRes_prTIirr` at
  `i = 0`; the restriction of `mu2 i j` to `PU` is independent of `i`). -/
  chi_res : ∀ j : Fin p,
    (chi j : ClassFunction ↥PU ℂ) = ClassFunction.restrict PU (mu2 0 j : ClassFunction S ℂ)
  /-- **(4.5.a)** Induction formula: `Ind_{PU}^S (chi j) = ∑_i mu2 i j` (Coq
  `cfInd_prTIres`). -/
  ind_chi : ∀ j : Fin p,
    ClassFunction.induce PU (chi j : ClassFunction ↥PU ℂ)
      = ∑ i : Fin q, (mu2 i j : ClassFunction S ℂ)
  /-- **(4.5.a)** The `0`-residue is the trivial character (Coq `prTIres0`). -/
  chi_zero : (chi 0 : ClassFunction ↥PU ℂ) = trivialClassFunction ↥PU
  /-- The Sylow `p`-subgroup `P ≤ PU` (`= S_F` realised inside `PU`), carrying the kernel
  condition of the `(P)`-nonlinear induced family `seqIndD PU S P 1`.  In the Feit–Thompson
  application `P = S_F` is the Fitting subgroup of `S` (elementary abelian of order `p^q`),
  and the residues `chi_ j` (`j ≠ 0`) are exactly the `Irr(PU)`-characters non-trivial on `P`. -/
  P : Subgroup ↥PU
  /-- **(4.5.b), kernel condition** (Coq `cfker_prTIres`, `PFsection4.v:801`): for `j ≠ 0` the
  residue `chi_ j` does **not** have `P` in its kernel (it is `P`-nonlinear).  Equivalently
  `P ⊄ ker (chi_ j)`, so `μ_j = Ind_{PU}^S (chi_ j) ∈ seqIndD PU S P 1`.  A genuine mathcomp
  theorem (the `j = 0` residue is trivial with full kernel by `chi_zero`; every other residue
  is a non-principal constituent of `Res_P (mu2 0 j)`, hence non-trivial on `P`). -/
  cfker_prTIres : ∀ j : Fin p, j ≠ 0 →
    ¬ ((P : Set ↥PU) ⊆ OddOrder.Peterfalvi.S03.characterKernel (chi j : ClassFunction ↥PU ℂ))
  /-- **Peterfalvi (4.5.b), `prTIres_irr_cases`** (Coq `PFsection4.v:620`, a genuine mathcomp
  `Theorem`).  The constituent classification of a prime-TI residue: for every irreducible
  `θ ∈ Irr(PU)`, exactly one of

  * **(residue case)** `θ = chi_ j` for some `j`  (equivalently `Ind_{PU}^S θ = μ_j`); or
  * **(induced-irreducible case)** `Ind_{PU}^S θ ∈ Irr(S)` and `Ind θ ≠ mu2 i j` for all
    `i, j` (a fresh irreducible, not a prime-TI constituent).

  This is the dichotomy `S1cases` uses to split the induced constituents of a member of
  `calS1` into the reducible `μ_j` family and the `𝒮 ∩ Irr(S)` part.

  **Why a posited field, not a derived theorem.**  The mathcomp proof establishes the
  *inertia group* `'I_S[θ] = PU` for `θ ∉ {chi_ j}` (whence `Ind θ` is irreducible by
  `inertia_Ind_irr`, whose repo analogue `isIrreducibleCharacter_induce_of_inertia_eq` is
  available) via a **`p`-group fixed-point count**: on the `W1`-conjugation action on
  `Irr(PU)`, the `z`-fixed irreducibles (`z ∈ W1` a `p`-element) equal the `z`-fixed classes
  (`card_afix_irr_classes`, repo
  `card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm`),
  and `sylow.pgroup_fix_mod` (mathlib `IsPGroup.card_modEq_card_fixedPoints`) with the
  coprimality `p ∤ |PU|` pins the fixed set to the residue image `{chi_ j}` of size `p`.  This
  computation consumes the **cyclic-TI structure** — the group `W1`, the decomposition
  `S = PU ⋊ W1`, the `W1`-action on `Irr(PU)`, and `coprime |PU| |W1|` — none of which is data
  of this structure (it is deliberately abstracted away, being supplied by the eventual
  `cyclicTIiso`-based constructor together with `mu2`/`chi`).  So the classification is not
  determined by the other fields; like `mu2_orthonormal`, `chi_res`, `ind_chi`, `cfker_prTIres`
  (all mathcomp theorems of the same `cyclicTIiso` provenance), it is posited here and
  discharged by the constructor.  See the module docstring / `issues/9014-primeti-residue-api.md`
  continuation #1–#2. -/
  prTIres_irr_cases : ∀ θ : IrreducibleCharacter ↥PU,
    (∃ j : Fin p, (θ : ClassFunction ↥PU ℂ) = (chi j : ClassFunction ↥PU ℂ))
      ∨ (IsIrreducibleCharacter (ClassFunction.induce PU (θ : ClassFunction ↥PU ℂ))
          ∧ ∀ (i : Fin q) (j : Fin p),
              ClassFunction.induce PU (θ : ClassFunction ↥PU ℂ)
                ≠ (mu2 i j : ClassFunction S ℂ))

namespace PrimeTIResidueData

variable {S : Type*} [Group S] [Fintype S] [Invertible (Nat.card S : ℂ)]
variable {PU : Subgroup S} [Fintype ↥PU] [Invertible (Nat.card ↥PU : ℂ)]
variable {q p : ℕ} [NeZero q] [NeZero p]
variable (D : PrimeTIResidueData S PU q p)

/-! ### `primeTIred`: the reducible column-sum characters `μ_j`

`primeTIred D j := ∑_i mu2 i j` (Coq `primeTIred`).  Below: it is a genuine character
(`prTIred_char`), reducible with `⟨μ_j⟩ = q > 1` (`cfnorm_prTIred`, `prTIred_not_irr`),
nonzero (`prTIred_neq0`), and injective in `j` (`prTIred_inj`). -/

/-- **Peterfalvi (4.5.a), `primeTIred`.** The reducible residue character
`μ_j := ∑_i mu2_ i j ∈ ℂ CF(S)` (Coq `primeTIred ptiW j`). -/
noncomputable def primeTIred (j : Fin p) : ClassFunction S ℂ :=
  ∑ i : Fin q, (D.mu2 i j : ClassFunction S ℂ)

theorem primeTIred_def (j : Fin p) :
    D.primeTIred j = ∑ i : Fin q, (D.mu2 i j : ClassFunction S ℂ) := rfl

/-- **`cfInd_prTIres`** (Coq `PFsection4.v:594`): `Ind_{PU}^S (chi_ j) = μ_j`.  Immediate
from the `ind_chi` field and the definition of `primeTIred`. -/
theorem cfInd_prTIres (j : Fin p) :
    ClassFunction.induce PU (D.chi j : ClassFunction ↥PU ℂ) = D.primeTIred j :=
  D.ind_chi j

/-- Each `μ_j` is a **genuine character** (Coq `prTIred_char`): a finite sum of
irreducible characters. -/
theorem prTIred_char (j : Fin p) : IsCharacter (D.primeTIred j) := by
  refine IsCharacter.sum fun i _ => ?_
  exact (D.mu2 i j).isIrreducible.isCharacter

/-- **`cfdot_prTIirr_red`** (Coq `PFsection4.v:452`): `⟨mu2 i j, μ_k⟩ = [j = k]`.

Expanding `μ_k = ∑_{i'} mu2 i' k` and using orthonormality of the `mu2`, the sum over `i'`
collapses to the single term `i' = i` (present iff `j = k`). -/
theorem cfdot_prTIirr_red (i : Fin q) (j k : Fin p) :
    ClassFunction.inner (D.mu2 i j : ClassFunction S ℂ) (D.primeTIred k)
      = (if j = k then 1 else 0) := by
  classical
  rw [primeTIred, inner_sum_right]
  -- each summand is the orthonormality value `[i = i' ∧ j = k]`
  have hval : ∀ i' : Fin q,
      ClassFunction.inner (D.mu2 i j : ClassFunction S ℂ) (D.mu2 i' k : ClassFunction S ℂ)
        = (if i = i' ∧ j = k then 1 else 0) := fun i' => D.mu2_orthonormal i i' j k
  rw [Finset.sum_congr rfl fun i' _ => hval i']
  by_cases hjk : j = k
  · -- only the `i' = i` term survives
    rw [if_pos hjk]
    have hcond : ∀ i' : Fin q, (i = i' ∧ j = k) ↔ i = i' := fun i' => by
      simp [hjk]
    simp only [hcond]
    rw [Finset.sum_ite_eq Finset.univ i (fun _ => (1 : ℂ)), if_pos (Finset.mem_univ i)]
  · -- every term vanishes
    rw [if_neg hjk]
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [if_neg fun h => hjk h.2]

/-- **`cfdot_prTIred`** (Coq `PFsection4.v:459`): `⟨μ_{j₁}, μ_{j₂}⟩ = [j₁ = j₂] · q`. -/
theorem cfdot_prTIred (j₁ j₂ : Fin p) :
    ClassFunction.inner (D.primeTIred j₁) (D.primeTIred j₂)
      = (if j₁ = j₂ then (q : ℂ) else 0) := by
  classical
  -- expand the left column-sum, then use `cfdot_prTIirr_red` termwise
  rw [primeTIred, inner_sum_left]
  rw [Finset.sum_congr rfl fun i _ => D.cfdot_prTIirr_red i j₁ j₂]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  by_cases hjk : j₁ = j₂
  · rw [if_pos hjk, if_pos hjk, nsmul_eq_mul, mul_one]
  · rw [if_neg hjk, if_neg hjk, nsmul_eq_mul, mul_zero]

/-- **`cfnorm_prTIred`** (Coq `PFsection4.v:465`): `⟨μ_j⟩ = q = #|W1|`. -/
theorem cfnorm_prTIred (j : Fin p) :
    ClassFunction.inner (D.primeTIred j) (D.primeTIred j) = (q : ℂ) := by
  rw [cfdot_prTIred, if_pos rfl]

/-- **`prTIred_neq0`** (Coq `PFsection4.v:468`): `μ_j ≠ 0`.  Its norm `q` is nonzero. -/
theorem prTIred_neq0 (j : Fin p) : D.primeTIred j ≠ 0 := by
  intro h
  have hnorm : ClassFunction.inner (D.primeTIred j) (D.primeTIred j) = (q : ℂ) :=
    D.cfnorm_prTIred j
  rw [h] at hnorm
  simp only [ClassFunction.inner_zero_left] at hnorm
  exact (NeZero.ne (q : ℂ)) hnorm.symm

/-- **`prTIred_not_irr`** (Coq `PFsection4.v:668`): `μ_j` is **not** irreducible.

If it were, its self-inner-product would be `1`; but it is `q > 1` (`W1` nontrivial, so
`q = #|W1| ≥ 2`).  We phrase the reducibility numerically via `cfnorm_prTIred`; combined
with `q ≠ 1` it excludes irreducibility for any predicate implying self-norm `1`. -/
theorem prTIred_not_irr (hq : 1 < q) (j : Fin p) :
    ClassFunction.inner (D.primeTIred j) (D.primeTIred j) ≠ 1 := by
  rw [cfnorm_prTIred]
  intro h
  have : (q : ℂ) = (1 : ℕ) := by exact_mod_cast h
  have hq1 : q = 1 := by exact_mod_cast this
  omega

/-- **`prTIred_inj`** (Coq `PFsection4.v:480`): `j ↦ μ_j` is injective.

If `μ_{j₁} = μ_{j₂}` then `⟨μ_{j₁}, μ_{j₂}⟩ = ⟨μ_{j₁}, μ_{j₁}⟩ = q ≠ 0`, but by
`cfdot_prTIred` the cross inner product is `0` unless `j₁ = j₂`. -/
theorem prTIred_inj (hq : q ≠ 0) : Function.Injective D.primeTIred := by
  intro j₁ j₂ hj
  by_contra hne
  have h0 : ClassFunction.inner (D.primeTIred j₁) (D.primeTIred j₂) = 0 := by
    rw [cfdot_prTIred, if_neg hne]
  rw [hj, D.cfnorm_prTIred j₂] at h0
  exact hq (by exact_mod_cast h0)

/-- **Entrywise distinctness of the prime-TI grid** (Coq `cfdot_prTIirr`, off-diagonal): distinct
grid positions carry distinct irreducibles, `mu2 i j ≠ mu2 i' j'` whenever `(i, j) ≠ (i', j')`.

Immediate from `mu2_orthonormal`: if the two coincide then their cross inner product is the self
inner product `1`, but the orthonormality value off the diagonal is `0`.  This is the residue-side
content of Peterfalvi (13.18)'s **row-`0` distinctness** pin (`S15.Hypothesis.mu_row0_ne`, the
special case `i = i' = 0`, `j ≠ j'`). -/
theorem mu2_ne {i i' : Fin q} {j j' : Fin p} (h : ¬ (i = i' ∧ j = j')) :
    (D.mu2 i j : ClassFunction S ℂ) ≠ (D.mu2 i' j' : ClassFunction S ℂ) := by
  intro heq
  have h1 := D.mu2_orthonormal i i' j j'
  rw [if_neg h] at h1
  rw [heq, D.mu2_orthonormal i' i' j' j', if_pos ⟨rfl, rfl⟩] at h1
  exact one_ne_zero h1

/-! ### The residue `chi_ 0` and `μ_0` -/

/-- **`prTIres0`** (Coq `PFsection4.v:608`): the `0`-residue is the trivial character. -/
theorem prTIres0 : (D.chi 0 : ClassFunction ↥PU ℂ) = trivialClassFunction ↥PU :=
  D.chi_zero

/-! ### The constituent classification `prTIres_irr_cases`

This is Peterfalvi (4.5.b) (Coq `PFsection4.v:620-665`), the single genuinely-deep sub-fact of
this port.  Its mathcomp proof is the inertia-group computation `'I_S[θ] = PU` (via `p`-group
fixed-point counting, `pgroup_fix_mod`, on the `W1`-action on `Irr(PU)`), which consumes the
cyclic-TI structure (`W1`, `S = PU ⋊ W1`, `coprime |PU| |W1|`) that is *not* data of
`PrimeTIResidueData` — it is supplied by the eventual `cyclicTIiso`-based constructor together
with `mu2`/`chi`.  Accordingly the classification is **posited as the field
`PrimeTIResidueData.prTIres_irr_cases`** (see its docstring for the full inertia/`pgroup_fix_mod`
provenance and why it is a field rather than a derivation), on the same honest footing as the
other `cyclicTIiso`-provenance fields `mu2_orthonormal`, `chi_res`, `ind_chi`, `cfker_prTIres`.
The constructor discharges all of them; this leaf is sorry-free.  `S1cases` below consumes the
field directly via `D.prTIres_irr_cases`. -/

/-! ### Membership of `μ_j` in `ℤ[Irr S]`

The `μ_j` are genuine characters (`prTIred_char`), hence virtual characters. -/

/-- Each `μ_j` is a **virtual character** (`μ_j ∈ ℤ[Irr S]`): it is a genuine character
(`prTIred_char`), and every genuine character lies in `ZIrr`. -/
theorem prTIred_mem_ZIrr (j : Fin p) : D.primeTIred j ∈ ZIrr S :=
  (D.prTIred_char j).mem_ZIrr

/-! ### The `(P)`-nonlinear induced family `calS = seqIndD PU S P 1`

`calS D := { Ind_{PU}^S ξ | ξ ∈ Irr(PU), P ⊄ ker ξ }` (Coq `seqIndD PU S P 1`, the reduced
family Peterfalvi's §13 coherence runs on).  This is the `PU`-level analogue of the S11 §9
family `sSet = Ind_{HU}^M 𝒳`; here the kernel condition is on the field `D.P ≤ PU`.  The
`μ_j` (`j ≠ 0`) are members (`FTseqInd_TIred`); more generally every `P`-nonlinear induction
`Ind_{PU}^S θ` lands in `calS D` and hence in `zSpan (calS D)` (`induce_mem_calS`,
`induce_mem_zSpan_calS`). -/

/-- **Peterfalvi §13 family `calS = seqIndD PU S P 1`** (Coq `PFsection13.v:157`): the set of
characters `Ind_{PU}^S ξ` induced from an irreducible `ξ ∈ Irr(PU)` whose kernel does **not**
contain `P` (the `(P)`-nonlinear residue family).  Mirrors the S11 `sSet` idiom. -/
noncomputable def calS : Set (ClassFunction S ℂ) :=
  { φ | ∃ ξ : IrreducibleCharacter ↥PU,
      ¬ ((D.P : Set ↥PU) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ξ : ClassFunction ↥PU ℂ))
        ∧ φ = ClassFunction.induce PU (ξ : ClassFunction ↥PU ℂ) }

theorem mem_calS {φ : ClassFunction S ℂ} :
    φ ∈ D.calS ↔ ∃ ξ : IrreducibleCharacter ↥PU,
      ¬ ((D.P : Set ↥PU) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ξ : ClassFunction ↥PU ℂ))
        ∧ φ = ClassFunction.induce PU (ξ : ClassFunction ↥PU ℂ) :=
  Iff.rfl

/-- **`induce_mem_calS`.** Any `P`-nonlinear induction is a family member: if `θ ∈ Irr(PU)` has
`P ⊄ ker θ`, then `Ind_{PU}^S θ ∈ calS D` (witness `ξ = θ`). -/
theorem induce_mem_calS (θ : IrreducibleCharacter ↥PU)
    (hθ : ¬ ((D.P : Set ↥PU) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥PU ℂ))) :
    ClassFunction.induce PU (θ : ClassFunction ↥PU ℂ) ∈ D.calS :=
  ⟨θ, hθ, rfl⟩

/-- **`FTseqInd_TIred`** (Coq `S1mu`, `PFsection13.v:391`): for `j ≠ 0`, the reducible residue
character `μ_j = primeTIred D j` lies in the family `calS D`.

`μ_j = Ind_{PU}^S (chi_ j)` (`cfInd_prTIres`) with the residue `chi_ j` `P`-nonlinear
(`cfker_prTIres`, valid for `j ≠ 0`); so `μ_j ∈ seqIndD PU S P 1 = calS D`. -/
theorem FTseqInd_TIred {j : Fin p} (hj : j ≠ 0) : D.primeTIred j ∈ D.calS := by
  refine ⟨D.chi j, D.cfker_prTIres j hj, ?_⟩
  exact (D.cfInd_prTIres j).symm

/-! ### The dichotomy `S1cases` and the membership `Ind θ ∈ zSpan calS`

`S1cases` (Coq `PFsection13.v:401-428`) classifies the induced character `Ind_{PU}^S θ` of an
irreducible `θ ∈ Irr(PU)` with `P ⊄ ker θ`, via `prTIres_irr_cases`, into two mutually
exclusive shapes — either `Ind θ = μ_j` for some `j ≠ 0`, or `Ind θ ∈ calS D ∩ Irr(S)` — both
of which lie in `calS D`.  This is the `PU`-level residue dichotomy on which Coq's
`sS1S : calS1 ⊆ ℤ[calS]` (and the S15 consumer `induce_H_mem_zSpan_S`) is built. -/

/-- **`S1cases` dichotomy** (Coq `PFsection13.v:401-428`).  For irreducible `θ ∈ Irr(PU)` with
`P ⊄ ker θ`, the induced character `Ind_{PU}^S θ` is classified as one of:

* **(residue / reducible case)** `∃ j ≠ 0, Ind_{PU}^S θ = μ_j`  (`θ = chi_ j`); or
* **(irreducible case)** `Ind_{PU}^S θ ∈ Irr(S)` **and** it is a family member `∈ calS D`
  (hence `∈ calS D ∩ Irr(S)`).

Uses `prTIres_irr_cases`: in the residue branch `θ = chi_ j`, and `j ≠ 0` follows since `θ`,
having `P ⊄ ker`, cannot be `chi_ 0 = 1` (whose kernel is everything); in the induced-irreducible
branch `Ind θ ∈ Irr(S)`, and membership in `calS D` is by `induce_mem_calS` (witness `θ`). -/
theorem S1cases (θ : IrreducibleCharacter ↥PU)
    (hθP : ¬ ((D.P : Set ↥PU) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥PU ℂ))) :
    (∃ j : Fin p, j ≠ 0 ∧
        ClassFunction.induce PU (θ : ClassFunction ↥PU ℂ) = D.primeTIred j)
      ∨ (IsIrreducibleCharacter (ClassFunction.induce PU (θ : ClassFunction ↥PU ℂ))
          ∧ ClassFunction.induce PU (θ : ClassFunction ↥PU ℂ) ∈ D.calS) := by
  rcases D.prTIres_irr_cases θ with ⟨j, hj⟩ | ⟨hirr, _⟩
  · -- residue case: `θ = chi_ j`; show `j ≠ 0` and `Ind θ = μ_j`
    refine Or.inl ⟨j, ?_, ?_⟩
    · -- `j ≠ 0`: otherwise `θ = chi_ 0 = 1`, whose kernel is all of `PU ⊇ P`, contradicting `hθP`
      rintro rfl
      exact hθP (by
        rw [hj, D.chi_zero, OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
        exact Set.subset_univ _)
    · -- `Ind θ = Ind (chi_ j) = μ_j`
      rw [hj]; exact D.cfInd_prTIres j
  · -- induced-irreducible case: `Ind θ ∈ Irr(S)` and `Ind θ ∈ calS D` (witness `θ`)
    exact Or.inr ⟨hirr, D.induce_mem_calS θ hθP⟩

/-- **`induce_mem_zSpan_calS`** (the `PU`-level `sS1S` engine).  For irreducible `θ ∈ Irr(PU)`
with `P ⊄ ker θ`, the induced character `Ind_{PU}^S θ` lies in `zSpan (calS D) = ℤ[calS]`.

This is the honest core the S15 consumer `induce_H_mem_zSpan_S` needs.  Via the `S1cases`
dichotomy both branches land in `calS D` itself (the residue `μ_j` is a member by
`FTseqInd_TIred`; the induced-irreducible is a member by `induce_mem_calS`), so the induction
is a single generator of the integral span. -/
theorem induce_mem_zSpan_calS (θ : IrreducibleCharacter ↥PU)
    (hθP : ¬ ((D.P : Set ↥PU) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥PU ℂ))) :
    ClassFunction.induce PU (θ : ClassFunction ↥PU ℂ) ∈ zSpan D.calS := by
  refine Submodule.subset_span ?_
  rcases D.S1cases θ hθP with ⟨j, hj, heq⟩ | ⟨_, hmem⟩
  · rw [heq]; exact D.FTseqInd_TIred hj
  · exact hmem

/-! ### The `H`-level lift `induce_H_mem_zSpan_calS`

Coq's `S1cases` is stated for a *smaller* group `H ≤ PU` than the induction target `PU`: it
classifies `Ind_H^S θ` (for irreducible `θ ∈ Irr(H)` with `P ⊄ ker θ`) into `zSpan (calS)`.  The
`PU`-level engine `induce_mem_zSpan_calS` above is the case `H = PU`; the general `H ≤ PU` case is
obtained by *induction in stages* and *constituent expansion* (Coq's `cfun_sum_constt` → `rpred_sum`
flow):

* `Ind_H^S θ = Ind_{PU}^S (Ind_H^{PU} θ)` — the two-stage induction (definitionally, via the
  `↥PU`-ambient `ClassFunction.induce`);
* `Ind_H^{PU} θ = ∑_{s ∈ Irr(PU)} ⟨θ, Res_H s⟩ • s` — the constituent (Fourier + Frobenius)
  decomposition `induce_eq_sum_inner_restrict_smul`, with non-negative integer coefficients;
* each constituent `s` with `⟨θ, Res_H s⟩ ≠ 0` has `P ⊄ ker s` (`constituent_P_not_subset_ker`,
  the kernel step: `θ` is a constituent of `Res_H s`, so `P ⊆ ker s ⟹ P ⊆ ker θ`, contradiction),
  hence `Ind_{PU}^S s ∈ zSpan (calS)` by the engine;
* `zSpan (calS)` is `ℤ`-closed, so the coefficient-weighted sum lands in it.

Here `H : Subgroup ↥PU` is an intermediate subgroup with `P ≤ H`, and `Ind_H^S θ` is written as the
honest two-stage induction `Ind_{PU}^S (Ind_H^{PU} θ)`.  Bridging this to the single-stage
`Ind_{(H.map PU.subtype)}^S` (as the S15 consumer `induce_H_mem_zSpan_S` phrases it) is
`induce_induce_subgroupOf` (`InducedTransport.lean`), applied on the S15 side. -/

/-- **Kernel step for the `H`-level lift** (Coq `S1cases` inner kernel argument).  Let `H ≤ PU`,
`θ` an irreducible character of `H` with `P ⊄ ker θ`.  If `s ∈ Irr(PU)` has `θ` as an irreducible
constituent of its restriction `Res_H s` — i.e. the Frobenius multiplicity `⟨θ, Res_H s⟩ ≠ 0`, which
is exactly the condition for `s` to appear with nonzero coefficient in the constituent expansion of
`Ind_H^{PU} θ` — then `P ⊄ ker s`.

**Contrapositive.**  If `P ⊆ ker s`, then `Res_H s` is trivial on `P.subgroupOf H`
(`characterKernel_restrict_subgroupOf`); and `θ`, being a constituent of the genuine character
`Res_H s` (`isCharacter_restrict`), inherits that kernel containment
(`characterKernel_subset_of_isCharacter_of_inner_ne_zero`, applied pointwise on `P.subgroupOf H`),
so `P.subgroupOf H ⊆ ker θ` — contradicting `P ⊄ ker θ`.  (`⟨θ, Res_H s⟩ ≠ 0` gives
`⟨Res_H s, θ⟩ ≠ 0` by conjugate symmetry.) -/
theorem constituent_P_not_subset_ker
    (H : Subgroup ↥PU) [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    (θ : ClassFunction ↥H ℂ) (hθirr : IsIrreducibleCharacter θ)
    (hθP : ¬ ((D.P.subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (s : IrreducibleCharacter ↥PU)
    (hs : ClassFunction.inner θ
        (ClassFunction.restrict H (s : ClassFunction ↥PU ℂ)) ≠ 0) :
    ¬ ((D.P : Set ↥PU) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction ↥PU ℂ)) := by
  haveI : Finite ↥PU := Finite.of_fintype _
  intro hker
  -- `Res_H s` is a genuine character, and `θ` is one of its constituents (`⟨Res_H s, θ⟩ ≠ 0`).
  have hResChar : IsCharacter (ClassFunction.restrict H (s : ClassFunction ↥PU ℂ)) :=
    OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter H
  have hinner' : ClassFunction.inner
      (ClassFunction.restrict H (s : ClassFunction ↥PU ℂ)) θ ≠ 0 := by
    rw [inner_conj_symm]
    exact fun h => hs (by rw [← star_star (ClassFunction.inner _ _), h, star_zero])
  -- `P ⊆ ker s` pushes to `P.subgroupOf H ⊆ ker (Res_H s)`.
  have hResker : (D.P.subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.restrict H (s : ClassFunction ↥PU ℂ)) :=
    OddOrder.Peterfalvi.S08.characterKernel_restrict_subgroupOf H hker
  -- Then `θ` (a constituent of `Res_H s`) also has `P.subgroupOf H` in its kernel — contradiction.
  exact hθP fun x hx =>
    OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
      hResChar hθirr hinner' (hResker hx)

set_option linter.unusedFintypeInType false in
/-- **`induce_H_mem_zSpan_calS`** — the `H`-level `sS1S` lift (Coq `S1cases`, `PFsection13.v:401`).
For an intermediate subgroup `H ≤ PU` with `P ≤ H` and an irreducible character `θ ∈ Irr(H)` whose
kernel does not contain `P`, the induced character `Ind_H^S θ`, written as the two-stage induction
`Ind_{PU}^S (Ind_H^{PU} θ)`, lies in `zSpan (calS D) = ℤ[calS]`.

**Proof** (Coq's `cfun_sum_constt` → `rpred_sum`, made concrete):

* the constituent decomposition `Ind_H^{PU} θ = ∑_{s ∈ Irr(PU)} ⟨θ, Res_H s⟩ • s`
  (`induce_eq_sum_inner_restrict_smul`) with non-negative integer coefficients;
* `Ind_{PU}^S` pushed through the sum and scalars (`induce_sum`, `induce_smul`);
* each coefficient `⟨θ, Res_H s⟩ = (k : ℂ)` (`k : ℕ`) by conjugate symmetry
  (`inner_conj_symm`) and `IsCharacter.exists_natCast_inner_irreducible` (`θ` irreducible,
  `Res_H s` genuine); when `k ≠ 0` the constituent has `P ⊄ ker s`
  (`constituent_P_not_subset_ker`), so `Ind_{PU}^S s ∈ zSpan (calS D)` by the `PU`-level engine
  `induce_mem_zSpan_calS`, and the `ℕ`-multiple stays in the span (`nsmul_mem`); when `k = 0`
  the summand is `0`.

The single-stage form `Ind_{(H.map PU.subtype)}^S θ` used by the S15 consumer
`induce_H_mem_zSpan_S` differs from this two-stage `Ind_{PU}^S (Ind_H^{PU} θ)` only by
`induce_induce_subgroupOf` (applied S15-side). -/
theorem induce_H_mem_zSpan_calS
    (H : Subgroup ↥PU) [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    (θ : ClassFunction ↥H ℂ) (hθirr : IsIrreducibleCharacter θ)
    (hθP : ¬ ((D.P.subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    ClassFunction.induce PU (ClassFunction.induce H θ) ∈ zSpan D.calS := by
  classical
  haveI : Finite ↥PU := Finite.of_fintype _
  haveI : Fintype (IrreducibleCharacter ↥PU) := Fintype.ofFinite _
  -- Constituent expansion `Ind_H^{PU} θ = ∑_s ⟨θ, Res_H s⟩ • s`, then push `Ind_{PU}^S` inside.
  rw [induce_eq_sum_inner_restrict_smul θ, ClassFunction.induce_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [ClassFunction.induce_smul]
  -- The coefficient `⟨θ, Res_H s⟩` is a non-negative integer `(k : ℂ)`.
  have hResChar : IsCharacter (ClassFunction.restrict H (s : ClassFunction ↥PU ℂ)) :=
    OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter H
  obtain ⟨k, hk⟩ := hResChar.exists_natCast_inner_irreducible hθirr
  have hc : ClassFunction.inner θ (ClassFunction.restrict H (s : ClassFunction ↥PU ℂ))
      = (k : ℂ) := by
    rw [inner_conj_symm, hk, Complex.star_def, Complex.conj_natCast]
  rw [hc, Nat.cast_smul_eq_nsmul ℂ k (ClassFunction.induce PU (s : ClassFunction ↥PU ℂ))]
  -- `k • Ind_{PU}^S s ∈ zSpan`: either `k = 0` (the term is `0`), or `P ⊄ ker s` and the engine
  -- fires.
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · simp [hk0]
  · refine nsmul_mem ?_ k
    refine D.induce_mem_zSpan_calS s ?_
    exact D.constituent_P_not_subset_ker H θ hθirr hθP s (by rw [hc]; exact_mod_cast hk0.ne')

end PrimeTIResidueData

end OddOrder.RepresentationTheory

/-! ## The `prTIres_irr_cases` dichotomy, assembled over the S06 certain-type `Hypothesis`

The genuinely-deep constituent classification `prTIres_irr_cases` (Peterfalvi (4.5.b)) — the crux
the
`PrimeTIResidueData` structure posits — is **already proven** as the inertia computation in
`S06_CertainTypeClifford`: a `χ ∈ Irr(K)` not among the residues `χ_j` has full inertia `I_L(χ) = K`
(`inertia_eq_K_of_forall_chiRestrict_ne`, the `p`-group fixed-point count via
`card_fixedPoints_conjByPermIrr…` + `IsPGroup.card_modEq_card_fixedPoints`), whence `Ind χ` is a
fresh
irreducible (`induce_isIrreducible_of_forall_chiRestrict_ne`) distinct from every `μ_{ij}`
(`induce_ne_certainType_of_forall_chiRestrict_ne`).  Assembling the residue case (by definition)
with
that induced-irreducible case gives exactly the dichotomy `PrimeTIResidueData.prTIres_irr_cases`
posits.  So the constructor of `PrimeTIResidueData` is a **bridge from an `S06.Hypothesis`**, not a
from-scratch `cyclicTIiso` port (issue 9014): the single genuinely-deep field is discharged by
`prTIres_irr_dichotomy` below. -/

namespace OddOrder.Peterfalvi.S06.Hypothesis

open OddOrder.RepresentationTheory

variable {L : Type*} [Group L] [Fintype L] (h : Hypothesis L)
  [Invertible (Nat.card L : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)]
  [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)] [Invertible (Nat.card ↥h.K : ℂ)]
  [NeZero (Nat.card h.W1)] [NeZero (Nat.card h.W2)]

omit [NeZero (Nat.card ↥h.W2)] in
/-- **Peterfalvi (4.5.b) `prTIres_irr_cases`, assembled.**  Every `χ ∈ Irr(K)` is either a residue
`χ_j` (`= chiRestrict χ₂` for some `W₂`-column `χ₂`) or induces to a *fresh* irreducible of `L`
distinct from every certain-type character `μ_{ij}`.  The residue case is by definition; the
induced-irreducible case is the S06 inertia computation
(`induce_isIrreducible_of_forall_chiRestrict_ne`
+ `induce_ne_certainType_of_forall_chiRestrict_ne`). This is the deep field of a
`PrimeTIResidueData`
constructor built from an `S06.Hypothesis` (issue 9014). -/
theorem prTIres_irr_dichotomy (χ : IrreducibleCharacter ↥h.K) :
    (∃ χ₂, h.chiRestrict χ₂ = χ) ∨
      (IsIrreducibleCharacter (ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ)) ∧
        ∀ (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)),
          ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ)
            ≠ ((h.columnFamily χ₂).mu i : ClassFunction L ℂ)) := by
  by_cases hcase : ∃ χ₂, h.chiRestrict χ₂ = χ
  · exact Or.inl hcase
  · push Not at hcase
    exact Or.inr ⟨h.induce_isIrreducible_of_forall_chiRestrict_ne hcase,
      fun χ₂ i => h.induce_ne_certainType_of_forall_chiRestrict_ne hcase χ₂ i⟩

/-! ### The `PrimeTIResidueData` constructor from an `S06.Hypothesis`

The residue grid `S = L`, `PU = K`, `q = |W₁|`, `p = |W₂|`.  The S06 grid is indexed by
`W₂`-columns `χ₂ ∈ Ŵ₂` (`h.columnFamily`/`h.chiRestrict`), of which there are exactly `|W₂| = p`
(`card_charGroup_W2`).  The bridge to the `Fin p` residue index is the equiv
`charGroupW2Equiv` below, normalized so the trivial column `1 : Ŵ₂` maps to index `0`
(so that `chi 0 = chiRestrict 1 = 1_K`, matching the `chi_zero` field). -/

/-- **Index bridge `Fin p ≃ Ŵ₂`** for the `PrimeTIResidueData` constructor.  From
`card_charGroup_W2 : |Ŵ₂| = |W₂| = p` we get an equiv `Fin p ≃ Ŵ₂`, then compose with a
transposition so that the trivial column `1 : Ŵ₂` sits at index `0` (`charGroupW2Equiv_zero`). -/
noncomputable def charGroupW2Equiv :
    Fin (Nat.card h.W2) ≃ ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
  haveI : Fintype ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Fintype.ofFinite _
  letI e0 : Fin (Nat.card h.W2) ≃ ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
    (Fintype.equivFinOfCardEq
      (by rw [← Nat.card_eq_fintype_card, h.card_charGroup_W2])).symm
  (Equiv.swap 0 (e0.symm 1)).trans e0

omit [NeZero (Nat.card ↥h.W1)] in
omit [Invertible (Nat.card L : ℂ)] in
omit [Fintype ↥(h.W1 ⊔ h.W2)] in
omit [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)] in
omit [Invertible (Nat.card ↥h.K : ℂ)] in
@[simp] theorem charGroupW2Equiv_zero :
    h.charGroupW2Equiv 0 = 1 := by
  classical
  simp only [charGroupW2Equiv, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

/-- **`PrimeTIResidueData` from the certain-type `S06.Hypothesis`** (the bridge of issue 9014,
discharging the deep field `prTIres_irr_cases` via `prTIres_irr_dichotomy`).  Given a subgroup
`H : Subgroup ↥h.K` with `W₂ ≤ H` (the (4.6.c) covering condition on the kernel family `P := H`),
assembles the residue grid `S = L`, `PU = K`, `q = |W₁|`, `p = |W₂|` from the S06 column machinery:
`mu2 i j := (columnFamily (e j)).mu i`, `chi j := chiRestrict (e j)` (`e = charGroupW2Equiv`).
Every field is a genuine S06 theorem — orthonormality (`columnFamily_mu_ne` + `injective`),
restriction (`coe_chiRestrict`), induction (`induce_restrict_certainType_eq`), the trivial residue
(`chiRestrict_one_eq_trivial` via `charGroupW2Equiv_zero`), the `(4.7)` kernel non-containment
(`not_subset_characterKernel_chiRestrict_of_ne_one`), and the `(4.5.b)` dichotomy
(`prTIres_irr_dichotomy`). -/
noncomputable def _root_.OddOrder.RepresentationTheory.PrimeTIResidueData.ofS06Hypothesis
    [Fintype ↥h.K] (H : Subgroup ↥h.K) (hW2H : h.W2.subgroupOf h.K ≤ H) :
    PrimeTIResidueData L h.K (Nat.card h.W1) (Nat.card h.W2) :=
  { mu2 := fun i j => (h.columnFamily (h.charGroupW2Equiv j)).mu i
    chi := fun j => h.chiRestrict (h.charGroupW2Equiv j)
    mu2_orthonormal := fun i i' j j' => by
      classical
      rw [irreducibleCharacter_inner_eq_ite]
      by_cases hjj' : j = j'
      · subst hjj'
        by_cases hii' : i = i'
        · subst hii'; simp
        · rw [if_neg (fun hc => hii' ((h.columnFamily (h.charGroupW2Equiv j)).injective hc)),
            if_neg (by simp [hii'])]
      · rw [if_neg (h.columnFamily_mu_ne (fun hc => hjj' (h.charGroupW2Equiv.injective hc)) i i'),
          if_neg (by simp [hjj'])]
    chi_res := fun j => h.coe_chiRestrict (h.charGroupW2Equiv j)
    ind_chi := fun j => by
      rw [h.coe_chiRestrict (h.charGroupW2Equiv j),
        h.induce_restrict_certainType_eq (h.charGroupW2Equiv j)]
    chi_zero := by
      rw [charGroupW2Equiv_zero, h.chiRestrict_one_eq_trivial,
        IrreducibleCharacter.coe_trivialIrreducibleCharacter]
    P := H
    cfker_prTIres := fun j hj => by
      have hne1 : h.charGroupW2Equiv j ≠ 1 := by
        rw [← charGroupW2Equiv_zero (h := h)]
        exact fun hc => hj (h.charGroupW2Equiv.injective hc)
      intro hHker
      exact h.not_subset_characterKernel_chiRestrict_of_ne_one hne1
        (Set.Subset.trans (SetLike.coe_subset_coe.mpr hW2H) hHker)
    prTIres_irr_cases := fun θ => by
      rcases h.prTIres_irr_dichotomy θ with ⟨χ₂, hχ₂⟩ | ⟨hirr, hne⟩
      · refine Or.inl ⟨h.charGroupW2Equiv.symm χ₂, ?_⟩
        rw [Equiv.apply_symm_apply, hχ₂]
      · exact Or.inr ⟨hirr, fun i j => hne (h.charGroupW2Equiv j) i⟩ }

/-- **Peterfalvi (4.3.c) in residue-grid form** (Coq `prTIirr_id`, issue 2038/9014): the
prime-TI irreducibles of the `ofS06Hypothesis` residue grid satisfy the value identity
`mu2 i j (x) = δ_j · ω_{ij}(x)` on the TI set `W ∖ W₂` (`= sdiffTICyclicHypothesis.V`).
The grid entry `mu2 i j` is definitionally the certain-type character
`(columnFamily (e j)).mu i` (`e = charGroupW2Equiv`), so this is
`certainType_apply_eq_of_mem_V` reindexed through the `Fin`-index bridge; `δ_j` is the
column sign `(columnFamily (e j)).sign` and `ω_{ij}` the column character
`chiColumn (e j) i` of `W = W₁ ⊔ W₂`.

This is the supply point of the `(13.18)` residue values (issue 2038 B-parts): the
`W₁^#`-values (`x ∈ W₁ ∖ {1} ⊆ W ∖ W₂`) and the column-sum (`primeTIred`) values follow by
evaluating the right-hand side. -/
theorem _root_.OddOrder.RepresentationTheory.PrimeTIResidueData.ofS06Hypothesis_mu2_apply_of_mem_V
    [Fintype ↥h.K] (H : Subgroup ↥h.K) (hW2H : h.W2.subgroupOf h.K ≤ H)
    (i : Fin (Nat.card h.W1)) (j : Fin (Nat.card h.W2))
    {v : L} (hv : v ∈ h.sdiffTICyclicHypothesis.V) :
    ((PrimeTIResidueData.ofS06Hypothesis h H hW2H).mu2 i j : ClassFunction L ℂ) v
      = ((h.columnFamily (h.charGroupW2Equiv j)).sign : ℂ)
        * (h.chiColumn (h.charGroupW2Equiv j) i :
            ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          ⟨v, h.sdiffTICyclicHypothesis.V_subset_W hv⟩ :=
  h.certainType_apply_eq_of_mem_V (h.charGroupW2Equiv j) i hv

end OddOrder.Peterfalvi.S06.Hypothesis

/-! ## Relocated from `S05_SigmaIsometry` (hub ruling 9014/fcfc0644): the `μ` extraction grid

The signed-irreducible extraction `ω^σ = ±μ` (`mu2Grid`) is the σ-grounding down-payment on the
prime-TI constructor (`cyclicTIiso` port), so it belongs with the prime-TI residue foundation
here rather than in lane-a's `S05_SigmaIsometry`.  Namespace and API are unchanged
(`TICyclicHypothesis.mu2Grid` etc.); only the file location moved. -/

namespace OddOrder.Peterfalvi.S05.TICyclicHypothesis

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

/-! ### The signed-irreducible extraction of (3.2): `ω^σ = ±μ` (the `dirr` step)

Peterfalvi §4 / Feit–Thompson §13 (Coq `primeTIirr_spec`, `PFsection4.v:288-387`, via
`dirr_dIirr`) refine the isometry (3.2) by showing that each basis image `ω^σ` is not merely a
virtual character but a **single signed irreducible** `δ · μ` (`δ = ±1`, `μ ∈ Irr(G)`), so that the
`μ` form an orthonormal system indexed by `Irr(W)` — the prime-TI irreducibles `mu2_ i j`.

This is exactly the norm-`1` classifier applied to `ω^σ`: `ω^σ ∈ ZIrr G` (`sigma_mem_ZIrr`) and
`‖ω^σ‖² = ‖ω‖² = 1` (isometry, `sigma_inner_irreducibleCharacter`), so by
`exists_zsmul_irreducibleCharacter_of_inner_self_one` (Peterfalvi (5.9.a)) it is `δ · μ`.  The
grid `mu2Grid`/`mu2GridSign` packages the extracted `μ`/`δ`, and `mu2Grid_orthonormal`
(= Coq `cfdot_prTIirr`) reads the orthonormality of the `μ` straight off the isometry.

These are reusable `σ`-side building blocks for the Peterfalvi §4 `dirr` extraction (the signed
irreducibles `μ` of the prime-TI grid, read off the (3.2) isometry).  Standalone, `sorry`-free;
currently unconsumed (the §4 prime-TI residue grid itself is carried by `S06`'s `certainType`/
`columnFamily` machinery, so these are kept only as a self-contained `σ`→signed-irreducible API). -/

/-- **Peterfalvi §4 `dirr` step** (existence form).  Each basis image `ω^σ` of the (3.2) isometry
is a single signed irreducible: there are a sign `δ = ±1` and an irreducible `μ ∈ Irr(G)` with
`ω^σ = δ • μ`.  (Coq `primeTIirr_spec` via `dirr_dIirr`: a norm-`1` element of `ℤ[Irr G]` lies in
`± Irr(G)`.) -/
theorem exists_sign_smul_irr_of_sigma_omega (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) :
    ∃ (δ : ℤ) (μ : IrreducibleCharacter G), (δ = 1 ∨ δ = -1) ∧
      hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) = δ • (μ : ClassFunction G ℂ) := by
  have hσZ : hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) ∈ ZIrr G :=
    hyp.sigma_mem_ZIrr hVeq app (IsIrreducibleCharacter.mem_ZIrr ω.2)
  have hσ1 : ClassFunction.inner (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
      (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)) = 1 := by
    rw [hyp.sigma_inner_irreducibleCharacter hVeq app, irreducibleCharacter_inner_eq_ite,
      if_pos rfl]
  exact exists_zsmul_irreducibleCharacter_of_inner_self_one hσZ hσ1

/-- **Peterfalvi §4 `dirr` step, grid form**: the extracted prime-TI irreducible `μ = mu2Grid ω`
(Coq `primeTIirr`), a choice of the single irreducible `μ` with `ω^σ = ±μ`
(`exists_sign_smul_irr_of_sigma_omega`). -/
noncomputable def mu2Grid (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) : IrreducibleCharacter G :=
  (hyp.exists_sign_smul_irr_of_sigma_omega hVeq app ω).choose_spec.choose

/-- The extracted sign `δ = mu2GridSign ω ∈ {±1}` of the `dirr` step. -/
noncomputable def mu2GridSign (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) : ℤ :=
  (hyp.exists_sign_smul_irr_of_sigma_omega hVeq app ω).choose

theorem mu2GridSign_eq (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) :
    hyp.mu2GridSign hVeq app ω = 1 ∨ hyp.mu2GridSign hVeq app ω = -1 :=
  (hyp.exists_sign_smul_irr_of_sigma_omega hVeq app ω).choose_spec.choose_spec.1

/-- The defining relation of the `dirr` extraction: `ω^σ = δ • μ` at the extracted `δ`/`μ`. -/
theorem sigma_omega_eq_mu2GridSign_smul_mu2Grid (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) :
    hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)
      = hyp.mu2GridSign hVeq app ω • (hyp.mu2Grid hVeq app ω : ClassFunction G ℂ) :=
  (hyp.exists_sign_smul_irr_of_sigma_omega hVeq app ω).choose_spec.choose_spec.2

/-- The extracted `μ = mu2Grid ω` recovers `ω^σ` up to its sign: `μ = δ • ω^σ` (using `δ² = 1`). -/
theorem mu2Grid_eq_sign_smul_sigma_omega (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) :
    (hyp.mu2Grid hVeq app ω : ClassFunction G ℂ)
      = hyp.mu2GridSign hVeq app ω • hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) := by
  rw [hyp.sigma_omega_eq_mu2GridSign_smul_mu2Grid hVeq app ω, smul_smul]
  rcases hyp.mu2GridSign_eq hVeq app ω with h | h <;> rw [h] <;> simp

open scoped Classical in
/-- **Peterfalvi (4.3.b) / Coq `cfdot_prTIirr`** (extraction form): the prime-TI irreducibles
`mu2Grid ω` form an orthonormal system indexed by `Irr(W)`,
`⟨mu2Grid ω, mu2Grid ω'⟩ = [ω = ω']`.  The diagonal is irreducibility; off the diagonal, if
`mu2Grid ω = mu2Grid ω'` then `⟨ω^σ, ω'^σ⟩ = δ_ω δ_ω' · 1 = ±1 ≠ 0`, contradicting
`⟨ω^σ, ω'^σ⟩ = ⟨ω, ω'⟩ = 0` (isometry). -/
theorem mu2Grid_orthonormal (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω ω' : IrreducibleCharacter hyp.W) :
    ClassFunction.inner (hyp.mu2Grid hVeq app ω : ClassFunction G ℂ)
        (hyp.mu2Grid hVeq app ω' : ClassFunction G ℂ)
      = if ω = ω' then 1 else 0 := by
  by_cases hωω' : ω = ω'
  · subst hωω'
    rw [if_pos rfl, irreducibleCharacter_inner_eq_ite, if_pos rfl]
  · rw [if_neg hωω', irreducibleCharacter_inner_eq_ite]
    -- Off-diagonal: show `mu2Grid ω ≠ mu2Grid ω'`, hence the `ite` is `0`.
    rw [if_neg ?_]
    intro hμ
    -- If the extracted irreducibles coincide, `⟨ω^σ, ω'^σ⟩` is a nonzero sign, but it is `0`.
    have hcross : ClassFunction.inner (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
        (hyp.sigma hVeq app (ω' : ClassFunction hyp.W ℂ)) = 0 := by
      rw [hyp.sigma_inner_irreducibleCharacter hVeq app, irreducibleCharacter_inner_eq_ite,
        if_neg hωω']
    rw [hyp.sigma_omega_eq_mu2GridSign_smul_mu2Grid hVeq app ω,
      hyp.sigma_omega_eq_mu2GridSign_smul_mu2Grid hVeq app ω', hμ,
      ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      irreducibleCharacter_inner_eq_ite, if_pos rfl, mul_one, star_intCast] at hcross
    -- `hcross : (δ_ω : ℂ) * (δ_ω' : ℂ) = 0`, impossible for signs `±1`.
    rcases hyp.mu2GridSign_eq hVeq app ω with hδ | hδ <;>
      rcases hyp.mu2GridSign_eq hVeq app ω' with hδ' | hδ' <;>
      rw [hδ, hδ'] at hcross <;> norm_num at hcross

/-- The grid `mu2Grid` is injective on `Irr(W)`: distinct linear characters `ω` give distinct
prime-TI irreducibles (immediate from `mu2Grid_orthonormal`). -/
theorem mu2Grid_injective (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) :
    Function.Injective (hyp.mu2Grid hVeq app) := by
  intro ω ω' hμ
  by_contra hne
  have h := hyp.mu2Grid_orthonormal hVeq app ω ω'
  rw [hμ, irreducibleCharacter_inner_eq_ite, if_pos rfl, if_neg hne] at h
  exact one_ne_zero h

end OddOrder.Peterfalvi.S05.TICyclicHypothesis
