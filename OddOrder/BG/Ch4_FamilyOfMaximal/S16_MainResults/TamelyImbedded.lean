/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults

/-! # BG §16, Remark after Theorem II: tamely imbedded subsets

**Bender–Glauberman, *Local Analysis for the Odd Order Theorem*** (LMS LNS 188), Chapter IV
§16, the *Remark* following Theorem II (mmd:4575):

> A subset `X` of `G` satisfying conditions (Ti)–(Tiii) of Theorem II is here called a
> *tamely imbedded subset* of `G` and the subgroups `Hᵢ` are said to form a *system of
> supporting subgroups* for `X`.  … Note that if `D` is empty, then `X` is a `TI`-subset in `G`.

This file packages that Remark as two definitions, faithful to the wording of Theorem II
(mmd:4555–4573).  It introduces **no new mathematics**: every clause is stated with the
existing repository objects.

* `escapingSharpSet M X` (= BG's `D = {x ∈ X# | C_G(x) ⊄ M}`, defined below with the `x ≠ 1`
  clause exactly as in the proved `theoremII_tame_embedding`; note this is **not**
  `escapingCentralizerSet`, which omits `x ≠ 1` and is therefore too large — since `1 ∈ A(M)`
  and `C_G(1) = G ⊄ M`, it would make `D` spuriously nonempty);
* `ASet` / `A0Set` (BG's `A(M)`, `A₀(M)`, Theorem E notation, `S16_MainResults.Notation`);
* `IsTISubset` (`OddOrder.GroupTheory.TISubset`);
* `maxNilpotentNormalHall` (= BG's `M_{iF} = H_i`, `OddOrder.GroupTheory`);
* `Subgroup.IsComplement'`, and the Peterfalvi type predicates
  `OddOrder.GroupTheory.IsTypeI` / `IsTypeII`.

## Deviation from FT (mmd:4577)

BG's condition (Tii)(d) — "`A₀(Mᵢ) − Hᵢ` is a nonempty `TI`-subset with normalizer `Mᵢ`" —
is **weaker** than the corresponding FT condition (Feit–Thompson, Definition 9.1(ii)(e),
pp. 803–804), which additionally requires that
`\widehat{M_i} = (⋃_{x ∈ H_i^#} C_{M_i}(x)) − H_i` be a nonempty `TI`-subset with
normalizer `M_i`.  As BG note (mmd:4577), the stronger FT condition "amounts to `Mᵢ` being
of Type I, a fact we cannot prove"; BG instead add (Tiii) (see `FrobeniusTypeIWithNonTIFitting`),
which Feit–Thompson confirmed suffices for FT Chapter V (§33).  The definitions below therefore
encode the **BG** conditions (Ti)–(Tiii), not the FT ones.
-/

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch4.S14
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Theorem II's set `D`** (mmd:4555): `D = {x ∈ X# | C_G(x) ⊄ M}`, the nonidentity elements
of `X` whose `G`-centralizer escapes `M`.  This matches the `D` inlined in the proved
`theoremII_tame_embedding` (with the `x ≠ 1` clause), and is deliberately **narrower** than
`escapingCentralizerSet M X` (which omits `x ≠ 1`). -/
def escapingSharpSet (M : Subgroup G) (X : Set G) : Set G :=
  {x | x ∈ X ∧ x ≠ 1 ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M}

/-! ## The Theorem II (Tiii) conclusion -/

/-- **BG Theorem II (Tiii) conclusion** (mmd:4573): `M` is a Frobenius group (thus of Type I)
with cyclic Frobenius complement, and `M_F` is not a `TI`-subset of `G`.

The Frobenius kernel is `M_F = maxNilpotentNormalHall M` (for a Type-I maximal `M_F = M_σ`);
`E` is the cyclic Frobenius complement.  "`M_F` is not a `TI`-subset in `G`" is encoded by the
repository's standard `¬ FittingIsTI M` predicate: `FittingIsTI M` is
`IsTISubset (F(M)^#) N_G(F(M))`
for the ambient Fitting subgroup `F(M) = fittingInAmbient M`, which the §15/§16 structure theorems
(Theorem A(8), 15.7, Theorem D(4)) all use for "the Fitting subgroup is/​is not a TI-subset".  For
the Type-I Frobenius `M` produced here, `F(M) = M_σ = M_F`, so `¬ FittingIsTI M` is exactly
"`M_F` is not a `TI`-subset". -/
def FrobeniusTypeIWithNonTIFitting (M : Subgroup G) : Prop :=
  IsTypeI M ∧
  (∃ E : Subgroup G, IsCyclic ↥E ∧
    Subgroup.IsComplement' ((maxNilpotentNormalHall M).subgroupOf M) (E.subgroupOf M) ∧
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
      ((maxNilpotentNormalHall M).subgroupOf M) (E.subgroupOf M)) ∧
  ¬ OddOrder.BG.Ch4.S15.FittingIsTI M

/-! ## System of supporting subgroups (Theorem II (Tii)) -/

/-- **BG Theorem II (Tii): a system of supporting subgroups for `X` relative to `M`**
(mmd:4571).  When `D = escapingCentralizerSet M X` is nonempty, there is a finite family of
maximal subgroups `M₁, …, Mₙ` of Type I or II, whose Fitting kernels `Hᵢ = M_{iF}` (=
`maxNilpotentNormalHall Mᵢ`) form the *supporting subgroups*, satisfying clauses (a)–(e).

The index type is `Fin n`; the field names track the book's labels (a)–(e). -/
structure SystemOfSupportingSubgroups (M : Subgroup G) (X : Set G) where
  /-- The number `n` of supporting maximal subgroups. -/
  n : ℕ
  /-- The maximal subgroups `M₁, …, Mₙ` (indexed by `Fin n`). -/
  Mfam : Fin n → Subgroup G
  /-- Each `Mᵢ` is a maximal subgroup of `G`. -/
  maximal : ∀ i, Mfam i ∈ maximalSubgroups G
  /-- Each `Mᵢ` is of Peterfalvi Type I or Type II. -/
  typeIorII : ∀ i, IsTypeI (Mfam i) ∨ IsTypeII (Mfam i)
  /-- **(a)** `(|Hᵢ|, |Hⱼ|) = 1` for `i ≠ j`, where `Hᵢ = M_{iF} = maxNilpotentNormalHall Mᵢ`. -/
  coprime_orders : ∀ i j, i ≠ j →
    Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall (Mfam i)))
      (Nat.card ↥(maxNilpotentNormalHall (Mfam j)))
  /-- **(b, factorization)** `Mᵢ = Hᵢ · (M ∩ Mᵢ)`: `Hᵢ` and `M ∩ Mᵢ` complement each other in
  `Mᵢ`. -/
  factorization : ∀ i,
    Subgroup.IsComplement' ((maxNilpotentNormalHall (Mfam i)).subgroupOf (Mfam i))
      ((M ⊓ Mfam i).subgroupOf (Mfam i))
  /-- **(b, disjointness)** `M ∩ Hᵢ = 1`. -/
  inf_M_supporting : ∀ i, M ⊓ maxNilpotentNormalHall (Mfam i) = ⊥
  /-- **(c)** `(|Hᵢ|, |C_M(x)|) = 1` for all `x ∈ X#`, where `C_M(x) = M ∩ C_G(x)`. -/
  coprime_centralizer : ∀ i, ∀ x ∈ X, x ≠ 1 →
    Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall (Mfam i)))
      (Nat.card ↥(M ⊓ Subgroup.centralizer ({x} : Set G)))
  /-- **(d)** `A₀(Mᵢ) − Hᵢ` is a nonempty `TI`-subset of `G` with normalizer `Mᵢ`, for a Hall
  `κ(Mᵢ)`-subgroup `K` witnessing `A₀(Mᵢ) = A0Set Mᵢ K`. -/
  a0_ti : ∀ i, ∃ K : Subgroup G,
    Ch03.IsHallSubgroup (S14.kappa (Mfam i)) (K.subgroupOf (Mfam i)) ∧
    (A0Set (Mfam i) K \ (maxNilpotentNormalHall (Mfam i) : Set G)).Nonempty ∧
    IsTISubset (A0Set (Mfam i) K \ (maxNilpotentNormalHall (Mfam i) : Set G)) (Mfam i)
  /-- **(e)** if `x ∈ D`, there is a conjugate `y` of `x` in `D` and an index `i` with
  `C_G(y) = C_{Hᵢ}(y) · C_M(y) ⊆ Mᵢ` (`C_{Hᵢ}(y) = Hᵢ ∩ C_G(y)`, `C_M(y) = M ∩ C_G(y)`,
  and the product is the pointwise set product). -/
  escape_centralizer : ∀ x ∈ escapingSharpSet M X,
    ∃ y ∈ escapingSharpSet M X, (∃ g : G, y = g * x * g⁻¹) ∧
      ∃ i, Subgroup.centralizer ({y} : Set G) ≤ Mfam i ∧
        (Subgroup.centralizer ({y} : Set G) : Set G) =
          ((maxNilpotentNormalHall (Mfam i) : Set G) ∩
              (Subgroup.centralizer ({y} : Set G) : Set G)) *
            ((M : Set G) ∩ (Subgroup.centralizer ({y} : Set G) : Set G))

/-! ## Tamely imbedded subset (Theorem II Remark) -/

/-- **BG §16, Remark after Theorem II** (mmd:4575): `X` is a *tamely imbedded subset* of `G`
relative to the maximal subgroup `M` iff conditions (Ti)–(Tiii) of Theorem II hold, namely:

* **(Ti)** whenever two elements of `X` are `G`-conjugate, they are already `M`-conjugate;
* **(Tii)+(Tiii)** if `D = escapingSharpSet M X` is nonempty, then there is a
  `SystemOfSupportingSubgroups M X` **(Tii)** such that, if some supporting maximal `Mᵢ` **of that
  system** is of Type II, then `M` is a Frobenius group of Type I with cyclic complement and `M_F`
  is not a `TI`-subset (`FrobeniusTypeIWithNonTIFitting M`) **(Tiii)**.

Note that (Tiii) is tied to the **existentially produced** family `Mᵢ` (the book's "the `Mᵢ`
in (Tii)"), not universally over all abstract systems: the structure `SystemOfSupportingSubgroups`
does not force its members to be genuine centralizer-neighbours, so a `∀ sys` reading would be
strictly stronger than — and generally not equivalent to — the book statement (and unprovable,
since a spurious Type-II member would force `M` Frobenius).

As the Remark notes, when `D` is empty this reduces to `X` being an ordinary `TI`-subset of
`G` (the (Tii)+(Tiii) clause is then vacuous). -/
def TamelyImbedded (M : Subgroup G) (X : Set G) : Prop :=
  -- (Ti): `G`-conjugate elements of `X` are `M`-conjugate.
  (∀ a ∈ X, ∀ b ∈ X, (∃ g : G, b = g * a * g⁻¹) → ∃ m ∈ M, b = m * a * m⁻¹) ∧
  -- (Tii)+(Tiii): a nonempty escaping set yields a system of supporting subgroups whose Type-II
  -- members force `M` Frobenius of Type I with non-TI `M_F`.
  (escapingSharpSet M X ≠ ∅ →
    ∃ sys : SystemOfSupportingSubgroups M X,
      ((∃ i, IsTypeII (sys.Mfam i)) → FrobeniusTypeIWithNonTIFitting M))

end OddOrder.BG.Ch4.S16
