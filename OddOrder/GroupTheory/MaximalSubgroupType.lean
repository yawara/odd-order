/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.MaxNilpotentNormalHall
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.GroupTheory.PRank
import OddOrder.GroupTheory.TISubset
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup

/-!
# Maximal subgroup types for BG/Peterfalvi

This file contains the shared scaffold for the maximal-subgroup type taxonomy
used by BG Chapter IV and Peterfalvi Sections 10--16.  The definitions follow
Peterfalvi Section 10 in the plain derived-series formulation; later BG files can
connect these predicates to the `sigma`/`kappa` language of local analysis.

The predicates are exposed as `Prop`s (`IsTypeI`, ..., `IsTypeV`) but their
faithful data is carried by `Type*Data` structures.  This avoids opaque
placeholders while still allowing downstream statements to quantify over the
mathematical witnesses (`H`, `U`, `W_1`, `W_2`, ...).
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-- The second derived subgroup `M''` of `M`, viewed in the ambient group.
(`M' = derivedInG M`, canonical in `GroupTheory.SubgroupInAmbient`, issue 0052.) -/
def secondDerivedInAmbient (M : Subgroup G) : Subgroup G :=
  derivedInG (derivedInG M)

/-- Nonidentity elements of a subgroup, as a subset of the ambient group. -/
def sharpSubgroup (H : Subgroup G) : Set G :=
  (H : Set G) \ {1}

/-- The conjugacy saturation of a subset of the ambient group. -/
def conjugacySaturation (A : Set G) : Set G :=
  {x | ∃ a ∈ A, ∃ g : G, x = g * a * g⁻¹}

/-- Peterfalvi's support relation: every element of `T` is conjugate to an
 element of `S`. -/
def Supports (T S : Set G) : Prop :=
  T ⊆ conjugacySaturation S

/-- A centralizer-union set: nonidentity elements of `host` centralizing some
 element of `source`.  This packages the repeated `A(M)` pattern in (8.10). -/
def centralizerSupport (source : Set G) (host : Subgroup G) : Set G :=
  {y | y ∈ host ∧ y ≠ 1 ∧ ∃ x ∈ source, y ∈ Subgroup.centralizer ({x} : Set G)}

/-- Elements of `X` whose ambient centralizer is not contained in `M`. -/
def escapingCentralizerSet (M : Subgroup G) (X : Set G) : Set G :=
  {x | x ∈ X ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M}

/-- Data for Peterfalvi (8.1), a solvable group of type `F`.

`H` is `M_F`, `U` is a Hall complement in `M`, `U_1` is the abelian normal
subgroup controlling centralizers of elements of `H#`, and `U_0` is the
Frobenius-complement realization with the same exponent as `U`. -/
structure TypeFData (M : Subgroup G) where
  H : Subgroup G
  U : Subgroup G
  U1 : Subgroup G
  U0 : Subgroup G
  H_eq : H = maxNilpotentNormalHall M
  H_nontrivial : H ≠ ⊥
  U_nontrivial : U ≠ ⊥
  H_le : H ≤ M
  U_le : U ≤ M
  U1_le : U1 ≤ U
  U0_le : U0 ≤ U
  complement : Subgroup.IsComplement' (H.subgroupOf M) (U.subgroupOf M)
  U1_normal : (U1.subgroupOf U).Normal
  U1_commutative : IsMulCommutative ↥U1
  centralizer_le_U1 : ∀ x ∈ H, x ≠ 1 → U ⊓ Subgroup.centralizer ({x} : Set G) ≤ U1
  exponent_eq : Monoid.exponent U0 = Monoid.exponent U
  frobenius_HU0 : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
    ↥(H ⊔ U0) (H.subgroupOf (H ⊔ U0)) (U0.subgroupOf (H ⊔ U0))

/-- Predicate form of Peterfalvi type `F`. -/
def IsTypeF (M : Subgroup G) : Prop :=
  Nonempty (TypeFData M)

/-- Data for Peterfalvi (8.3), type I. -/
structure TypeIData (M : Subgroup G) where
  typeF : TypeFData M
  alternative :
    IsTISubset (sharpSubgroup typeF.H) (Subgroup.normalizer (typeF.H : Set G)) ∨
    (IsMulCommutative ↥typeF.H ∧ rank ↥typeF.H = 2) ∨
    ((∀ p : ℕ, p.Prime → p ∈ (Nat.card ↥typeF.H).primeFactors →
        Monoid.exponent typeF.U ∣ p - 1) ∧
      ∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥typeF.H).primeFactors ∧
        IsCyclic ↥(opiCoreInG {p}ᶜ typeF.H))

/-- Predicate form of Peterfalvi type I. -/
def IsTypeI (M : Subgroup G) : Prop :=
  Nonempty (TypeIData M)

/-- Data for Peterfalvi (8.4), type `P`.

The fields mirror the derived-series presentation in the text: `M = M' W_1`,
`M' = H U`, `H = M_F`, `W_2 = C_{M'}(W_1#)`, and the set
`V = W - (W_1 union W_2)` has normalizer exactly `W` for every nonempty subset. -/
structure TypePData (M : Subgroup G) where
  H : Subgroup G
  U : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  H_eq : H = maxNilpotentNormalHall M
  H_le : H ≤ derivedInG M
  U_le : U ≤ derivedInG M
  W1_le : W1 ≤ M
  W2_le : W2 ≤ H ⊓ secondDerivedInAmbient M
  W_eq : W = W1 ⊔ W2
  W_cyclic : IsCyclic ↥W
  W1_nontrivial : W1 ≠ ⊥
  W2_nontrivial : W2 ≠ ⊥
  W1_cyclic : IsCyclic ↥W1
  W2_cyclic : IsCyclic ↥W2
  M_complement : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (W1.subgroupOf M)
  U_normal : (U.subgroupOf (derivedInG M)).Normal
  U_nilpotent : Group.IsNilpotent ↥U
  derived_complement :
    Subgroup.IsComplement' (H.subgroupOf (derivedInG M)) (U.subgroupOf (derivedInG M))
  H_noncyclic : ¬ IsCyclic ↥H
  secondDerived_le_fitting :
    secondDerivedInAmbient M ≤ H ⊔ (U ⊓ Subgroup.centralizer (H : Set G))
  fitting_eq : maxNilpotentNormalHall M = H ⊔ (U ⊓ Subgroup.centralizer (H : Set G))
  fitting_lt_derived : maxNilpotentNormalHall M < derivedInG M
  centralizer_W1 : ∀ x ∈ W1, x ≠ 1 →
    derivedInG M ⊓ Subgroup.centralizer ({x} : Set G) = W2
  normalizer_V : ∀ X : Set G, X.Nonempty →
    X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W

/-- Predicate form of Peterfalvi type `P`. -/
def IsTypeP (M : Subgroup G) : Prop :=
  Nonempty (TypePData M)

/-- Common type II--IV hypotheses from Peterfalvi (8.6). -/
def TypePNontrivialCore (M : Subgroup G) (data : TypePData M) : Prop :=
  data.U ≠ ⊥ ∧ (Nat.card ↥data.W1).Prime ∧
    IsTISubset (sharpSubgroup (maxNilpotentNormalHall M))
      (Subgroup.normalizer ((maxNilpotentNormalHall M : Subgroup G) : Set G))

/-- Data for Peterfalvi type II. -/
structure TypeIIData (M : Subgroup G) where
  typeP : TypePData M
  common : TypePNontrivialCore M typeP
  U_commutative : IsMulCommutative ↥typeP.U
  normalizer_not_le : ¬ Subgroup.normalizer (typeP.U : Set G) ≤ M
  derived_typeF : IsTypeF (derivedInG M)
  derived_fitting_eq : maxNilpotentNormalHall (derivedInG M) = typeP.H

/-- Data for Peterfalvi type III. -/
structure TypeIIIData (M : Subgroup G) where
  typeP : TypePData M
  common : TypePNontrivialCore M typeP
  U_commutative : IsMulCommutative ↥typeP.U
  normalizer_le : Subgroup.normalizer (typeP.U : Set G) ≤ M

/-- Data for Peterfalvi type IV. -/
structure TypeIVData (M : Subgroup G) where
  typeP : TypePData M
  common : TypePNontrivialCore M typeP
  U_not_commutative : ¬ IsMulCommutative ↥typeP.U
  normalizer_le : Subgroup.normalizer (typeP.U : Set G) ≤ M

/-- Data for Peterfalvi type V. -/
structure TypeVData (M : Subgroup G) where
  typeP : TypePData M
  U_eq_bot : typeP.U = ⊥
  alternative :
    IsTISubset (sharpSubgroup typeP.H) (Subgroup.normalizer (typeP.H : Set G)) ∨
    (∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥typeP.H).primeFactors ∧
      Nat.card ↥typeP.W1 ∣ p - 1 ∧ IsCyclic ↥(opiCoreInG {p}ᶜ typeP.H)) ∨
    (∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥typeP.H).primeFactors ∧
      Nat.card ↥(opiCoreInG {p} typeP.H) = p ^ 3 ∧ Nat.card ↥typeP.W1 ∣ p + 1 ∧
      IsCyclic ↥(opiCoreInG {p}ᶜ typeP.H))

/-- Predicate form of Peterfalvi type II. -/
def IsTypeII (M : Subgroup G) : Prop :=
  Nonempty (TypeIIData M)

/-- Predicate form of Peterfalvi type III. -/
def IsTypeIII (M : Subgroup G) : Prop :=
  Nonempty (TypeIIIData M)

/-- Predicate form of Peterfalvi type IV. -/
def IsTypeIV (M : Subgroup G) : Prop :=
  Nonempty (TypeIVData M)

/-- Predicate form of Peterfalvi type V. -/
def IsTypeV (M : Subgroup G) : Prop :=
  Nonempty (TypeVData M)

/-- The non-Type-I alternatives in Peterfalvi (8.8). -/
def IsTypeNonI (M : Subgroup G) : Prop :=
  IsTypeII M ∨ IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M

/-- The five named Peterfalvi maximal-subgroup types. -/
inductive PeterfalviType where
  | I | II | III | IV | V
  deriving DecidableEq, Repr

/-- Predicate selecting the corresponding type predicate. -/
def HasPeterfalviType (tau : PeterfalviType) (M : Subgroup G) : Prop :=
  match tau with
  | .I => IsTypeI M
  | .II => IsTypeII M
  | .III => IsTypeIII M
  | .IV => IsTypeIV M
  | .V => IsTypeV M

/-- Peterfalvi (8.10), the subgroup `M_s`: it is `M_F` for types I, II, V and
`M'` for types III, IV. -/
noncomputable def mainSubgroup (M : Subgroup G) (tau : PeterfalviType) : Subgroup G :=
  match tau with
  | .III => derivedInG M
  | .IV => derivedInG M
  | .I => maxNilpotentNormalHall M
  | .II => maxNilpotentNormalHall M
  | .V => maxNilpotentNormalHall M

/-- Peterfalvi (8.10), `A_1(M) = M_s#`. -/
def A1 (M : Subgroup G) (tau : PeterfalviType) : Set G :=
  sharpSubgroup (mainSubgroup M tau)

/-- The `A(M)` set associated to type I data. -/
def typeIA (M : Subgroup G) (data : TypeIData M) : Set G :=
  centralizerSupport (sharpSubgroup data.typeF.H) M

/-- The `A(M)` set associated to type `P` data. -/
def typePA (M : Subgroup G) (_data : TypePData M) : Set G :=
  centralizerSupport (sharpSubgroup M) (derivedInG M)

/-- The exceptional `V = W - (W_1 union W_2)` set attached to type `P` data. -/
def typePV (M : Subgroup G) (data : TypePData M) : Set G :=
  (data.W : Set G) \ ((data.W1 : Set G) ∪ (data.W2 : Set G))

/-- Peterfalvi (8.10), `A_0(M) = A(M) union V^G` for type `P` data. -/
def typePA0 (M : Subgroup G) (data : TypePData M) : Set G :=
  typePA M data ∪ conjugacySaturation (typePV M data)

end OddOrder.GroupTheory
