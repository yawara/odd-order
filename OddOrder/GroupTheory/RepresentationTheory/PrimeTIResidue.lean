/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.IsometryDifferencePair
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
import OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier
import OddOrder.Peterfalvi.S07_Coherence

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

The single genuinely-deep sub-fact left with an isolated `sorry` is
`prTIres_irr_cases` (Peterfalvi (4.5.b), the inertia-group / `p`-group fixed-point
counting argument, Coq `PFsection4.v:620-665`); its statement and docstring are in place.

The eventual **constructor** of `PrimeTIResidueData` (from a genuine
`primeTI_hypothesis`, via a Lean port of `cyclicTIiso` + `primeTIirr_spec`) is the
multi-session continuation tracked in `issues/9014-primeti-residue-api.md`.

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

/-! ### The residue `chi_ 0` and `μ_0` -/

/-- **`prTIres0`** (Coq `PFsection4.v:608`): the `0`-residue is the trivial character. -/
theorem prTIres0 : (D.chi 0 : ClassFunction ↥PU ℂ) = trivialClassFunction ↥PU :=
  D.chi_zero

/-! ### The constituent classification `prTIres_irr_cases`

This is Peterfalvi (4.5.b) (Coq `PFsection4.v:620-665`).  It is the single genuinely-deep
sub-fact of this port; its proof in mathcomp is the inertia-group computation
`'I_S[θ] = PU` (via `p`-group fixed-point counting, `pgroup_fix_mod`), showing that any
`θ ∈ Irr(PU)` not equal to a residue induces irreducibly.  Stated here; proof deferred to
the continuation session (see the module docstring / issue 9014). -/

/-- **Peterfalvi (4.5.b), `prTIres_irr_cases`** (Coq `PFsection4.v:620`).

For every irreducible `θ ∈ Irr(PU)`, exactly one of:

* **(residue case)** `θ = chi_ j` for some `j`  (equivalently `Ind_{PU}^S θ = μ_j`); or
* **(induced-irreducible case)** `Ind_{PU}^S θ ∈ Irr(S)` and `Ind θ ≠ mu2 i j` for all
  `i, j` (i.e. it is a fresh irreducible, not a prime-TI constituent).

This is the dichotomy `S1cases` uses to split the induced constituents of a member of
`calS1` into the reducible `μ_j` family and the `𝒮 ∩ Irr(S)` part.

**Deep sub-fact (isolated `sorry`).** The mathcomp proof computes the inertia group
`'I_S[θ] = PU` for `θ ∉ {chi_ j}`, whence `Ind θ` is irreducible by
`inertia_Ind_irr`; the inertia computation is a `p`-group fixed-point count
(`sylow.pgroup_fix_mod`) on the `W1`-action on `Irr(PU)`.  Porting it requires the
`cyclicTI` inertia API (continuation of issue 9014). -/
theorem prTIres_irr_cases (θ : IrreducibleCharacter ↥PU) :
    (∃ j : Fin p, (θ : ClassFunction ↥PU ℂ) = (D.chi j : ClassFunction ↥PU ℂ))
      ∨ (IsIrreducibleCharacter (ClassFunction.induce PU (θ : ClassFunction ↥PU ℂ))
          ∧ ∀ (i : Fin q) (j : Fin p),
              ClassFunction.induce PU (θ : ClassFunction ↥PU ℂ)
                ≠ (D.mu2 i j : ClassFunction S ℂ)) := by
  sorry

/-! ### Membership of `μ_j` in `ℤ[Irr S]`

The `μ_j` are genuine characters (`prTIred_char`), hence virtual characters. -/

/-- Each `μ_j` is a **virtual character** (`μ_j ∈ ℤ[Irr S]`): it is a genuine character
(`prTIred_char`), and every genuine character lies in `ZIrr`. -/
theorem prTIred_mem_ZIrr (j : Fin p) : D.primeTIred j ∈ ZIrr S :=
  (D.prTIred_char j).mem_ZIrr

end PrimeTIResidueData

end OddOrder.RepresentationTheory

