/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basis
import Mathlib.Tactic.Group

/-!
# Central elementary extensions are determined by their square map

Let `1 → W → E → V → 1` be a central extension in which `V` and `W` are
vector spaces over `F₂`.  Once the kernel and quotient coordinates are fixed,
the squaring map `V → W` determines the extension up to equivalence.

The proof uses an ordered basis of `V`.  Choose one lift of each basis vector
and write every quotient vector as the descending product of its active basis
lifts.  Collecting two such words only uses squares of basis lifts and their
pairwise commutators.  The latter are determined by squares through

`[x,y] = x² (x⁻¹y)² (y²)⁻¹`.

Thus two central elementary extensions with the same square coordinates have
the same collected multiplication law.  The main result
`GroupExtension.equivOfCommonSquareMap` constructs the actual equivalence of
short exact sequences; it does not assume a factor set or a posited
multiplication law.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

noncomputable section

open scoped BigOperators commutatorElement
open Module

universe uV uW uE uE'

section CoordinateExtension

variable {K : Type uW} [Group K]
variable {Q : Type uV} [Group Q]
variable {E : Type uE} [Group E]

/-- Package a normal subgroup and chosen kernel/quotient coordinates as a
short exact group extension.  Both coordinates are actual multiplicative
equivalences; no section or factor set is posited. -/
noncomputable def _root_.GroupExtension.ofNormalSubgroupCoordinates
    (N : Subgroup E) [N.Normal]
    (left : K ≃* N) (right : E ⧸ N ≃* Q) :
    GroupExtension K E Q where
  inl := N.subtype.comp left.toMonoidHom
  rightHom := right.toMonoidHom.comp (QuotientGroup.mk' N)
  inl_injective := N.subtype_injective.comp left.injective
  range_inl_eq_ker_rightHom := by
    ext e
    constructor
    · rintro ⟨k, rfl⟩
      simp
    · intro he
      rw [MonoidHom.mem_ker] at he
      have heq : QuotientGroup.mk' N e = 1 :=
        right.injective (by simpa using he)
      have heN : e ∈ N := (QuotientGroup.eq_one_iff e).mp heq
      refine ⟨left.symm ⟨e, heN⟩, ?_⟩
      simp
  rightHom_surjective :=
    right.surjective.comp (QuotientGroup.mk'_surjective N)

/-- The embedded kernel of `ofNormalSubgroupCoordinates` is the supplied
normal subgroup. -/
@[simp]
theorem _root_.GroupExtension.ofNormalSubgroupCoordinates_range_inl
    (N : Subgroup E) [N.Normal]
    (left : K ≃* N) (right : E ⧸ N ≃* Q) :
    (GroupExtension.ofNormalSubgroupCoordinates N left right).inl.range = N := by
  ext e
  constructor
  · rintro ⟨k, rfl⟩
    exact (left k).property
  · intro he
    obtain ⟨k, hk⟩ := left.surjective ⟨e, he⟩
    refine ⟨k, ?_⟩
    exact congrArg Subtype.val hk

end CoordinateExtension

section CollectedWords

variable {W : Type uW} [AddCommGroup W] [Module (ZMod 2) W]
variable {E : Type uE} [Group E]

/-- An `F₂` coefficient selects either the identity or one group element. -/
private def bitFactor (a : ZMod 2) (x : E) : E :=
  if a = 0 then 1 else x

private theorem zmodTwo_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Descending ordered word on `Fin n`: the last basis lift occurs first. -/
private def collectedWord : ∀ n : ℕ, (Fin n → E) → (Fin n → ZMod 2) → E
  | 0, _, _ => 1
  | n + 1, x, a =>
      bitFactor (a (Fin.last n)) (x (Fin.last n)) *
        collectedWord n (fun i => x i.castSucc) (fun i => a i.castSucc)

/-- Sum of entries selected by an `F₂` coefficient vector. -/
private def bitSum : ∀ n : ℕ, (Fin n → ZMod 2) → (Fin n → W) → W
  | 0, _, _ => 0
  | n + 1, a, d =>
      bitSum n (fun i => a i.castSucc) (fun i => d i.castSucc) +
        if a (Fin.last n) = 0 then 0 else d (Fin.last n)

/-- The universal kernel defect obtained when two descending binary words are
collected.  `diag i` records the square of generator `i`, while `cross i j`
records the cost of swapping generator `i` past generator `j` for `i < j`. -/
private def collectedDefect : ∀ n : ℕ, (Fin n → W) → (Fin n → Fin n → W) →
    (Fin n → ZMod 2) → (Fin n → ZMod 2) → W
  | 0, _, _, _, _ => 0
  | n + 1, diag, cross, a, b =>
      let a' : Fin n → ZMod 2 := fun i => a i.castSucc
      let b' : Fin n → ZMod 2 := fun i => b i.castSucc
      let diag' : Fin n → W := fun i => diag i.castSucc
      let cross' : Fin n → Fin n → W := fun i j => cross i.castSucc j.castSucc
      let old := collectedDefect n diag' cross' a' b'
      if b (Fin.last n) = 0 then old
      else
        bitSum n a' (fun i => cross i.castSucc (Fin.last n)) +
          (if a (Fin.last n) = 0 then 0 else diag (Fin.last n)) + old

private theorem add_self_eq_zero (w : W) : w + w = 0 := by
  calc
    w + w = 2 • w := (two_nsmul w).symm
    _ = (2 : ZMod 2) • w :=
      (Nat.cast_smul_eq_nsmul (ZMod 2) 2 w).symm
    _ = 0 := by rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_smul]

private theorem neg_eq_self (w : W) : -w = w := by
  exact neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero w)

variable (k : Multiplicative W →* E)

private abbrev kernelValue (w : W) : E := k (Multiplicative.ofAdd w)

omit [Module (ZMod 2) W] in
@[simp] private theorem kernelValue_zero : kernelValue k (0 : W) = 1 := by
  exact map_one k

omit [Module (ZMod 2) W] in
private theorem kernelValue_add (u v : W) :
    kernelValue k (u + v) = kernelValue k u * kernelValue k v := by
  exact map_mul k (Multiplicative.ofAdd u) (Multiplicative.ofAdd v)

omit [Module (ZMod 2) W] in
private theorem kernelValue_neg (u : W) :
    kernelValue k (-u) = (kernelValue k u)⁻¹ := by
  exact map_inv k (Multiplicative.ofAdd u)

omit [Module (ZMod 2) W] in
private theorem kernelValue_commute
    (hcentral : k.range ≤ Subgroup.center E) (w : W) (x : E) :
    Commute (kernelValue k w) x := by
  exact (Subgroup.mem_center_iff.mp
    (hcentral ⟨Multiplicative.ofAdd w, rfl⟩) x).symm

omit [Module (ZMod 2) W] in
/-- Moving one generator left through a descending collected word accumulates
exactly the selected pairwise swap costs. -/
private theorem collectedWord_mul_generator
    (hcentral : k.range ≤ Subgroup.center E) : ∀ n : ℕ,
    ∀ (x : Fin n → E) (a : Fin n → ZMod 2) (y : E) (d : Fin n → W),
      (∀ i, x i * y = kernelValue k (d i) * y * x i) →
      collectedWord n x a * y =
        kernelValue k (bitSum n a d) * y * collectedWord n x a := by
  intro n
  induction n with
  | zero =>
      intro x a y d hrel
      simp [collectedWord, bitSum]
  | succ n ih =>
      intro x a y d hrel
      let x' : Fin n → E := fun i => x i.castSucc
      let a' : Fin n → ZMod 2 := fun i => a i.castSucc
      let d' : Fin n → W := fun i => d i.castSucc
      have ih' := ih x' a' y d' (fun i => hrel i.castSucc)
      rcases zmodTwo_eq_zero_or_one (a (Fin.last n)) with ha | ha
      · simp only [collectedWord, bitFactor, ha, if_pos, one_mul, bitSum]
        simpa [a', d'] using ih'
      · simp only [collectedWord, bitFactor, ha, one_ne_zero, if_false, bitSum]
        have hc := kernelValue_commute k hcentral (bitSum n a' d') (x (Fin.last n))
        have hrelLast := hrel (Fin.last n)
        calc
          (x (Fin.last n) * collectedWord n x' a') * y =
              x (Fin.last n) * (collectedWord n x' a' * y) := by group
          _ = x (Fin.last n) *
              (kernelValue k (bitSum n a' d') * y * collectedWord n x' a') := by
                rw [ih']
          _ = (x (Fin.last n) * kernelValue k (bitSum n a' d')) * y *
              collectedWord n x' a' := by group
          _ = (kernelValue k (bitSum n a' d') * x (Fin.last n)) * y *
              collectedWord n x' a' := by rw [hc.eq.symm]
          _ = kernelValue k (bitSum n a' d') *
              (x (Fin.last n) * y) * collectedWord n x' a' := by group
          _ = kernelValue k (bitSum n a' d') *
              (kernelValue k (d (Fin.last n)) * y * x (Fin.last n)) *
                collectedWord n x' a' := by rw [hrelLast]
          _ = kernelValue k (bitSum n a' d' + d (Fin.last n)) * y *
              (x (Fin.last n) * collectedWord n x' a') := by
                rw [kernelValue_add]
                group
          _ = kernelValue k
                (bitSum n (fun i => a i.castSucc) (fun i => d i.castSucc) +
                  d (Fin.last n)) * y *
              (x (Fin.last n) *
                collectedWord n (fun i => x i.castSucc) (fun i => a i.castSucc)) := by
                rfl

omit [Module (ZMod 2) W] in
/-- Universal collection formula for descending binary words. -/
private theorem collectedWord_mul
    (hcentral : k.range ≤ Subgroup.center E) : ∀ n : ℕ,
    ∀ (x : Fin n → E) (diag : Fin n → W) (cross : Fin n → Fin n → W),
      (∀ i, x i ^ 2 = kernelValue k (diag i)) →
      (∀ i j, i < j → x i * x j = kernelValue k (cross i j) * x j * x i) →
      ∀ a b : Fin n → ZMod 2,
        collectedWord n x a * collectedWord n x b =
          kernelValue k (collectedDefect n diag cross a b) *
            collectedWord n x (a + b) := by
  intro n
  induction n with
  | zero =>
      intro x diag cross hsq hswap a b
      simp [collectedWord, collectedDefect]
  | succ n ih =>
      intro x diag cross hsq hswap a b
      let x' : Fin n → E := fun i => x i.castSucc
      let a' : Fin n → ZMod 2 := fun i => a i.castSucc
      let b' : Fin n → ZMod 2 := fun i => b i.castSucc
      let diag' : Fin n → W := fun i => diag i.castSucc
      let cross' : Fin n → Fin n → W := fun i j => cross i.castSucc j.castSucc
      have ih' := ih x' diag' cross'
        (fun i => hsq i.castSucc)
        (fun i j hij => hswap i.castSucc j.castSucc (by simpa using hij)) a' b'
      have hab' : a' + b' = fun i => (a + b) i.castSucc := by
        funext i
        rfl
      rcases zmodTwo_eq_zero_or_one (b (Fin.last n)) with hb | hb
      · simp only [collectedWord, bitFactor, hb, if_pos, one_mul, collectedDefect]
        rw [mul_assoc, ih']
        rcases zmodTwo_eq_zero_or_one (a (Fin.last n)) with ha | ha
        · simp only [ha, if_pos, Pi.add_apply, hb, add_zero, one_mul]
          simpa [a', b', diag', cross'] using congrArg
            (fun z => kernelValue k (collectedDefect n diag' cross' a' b') *
              collectedWord n x' z) hab'
        · have hc := kernelValue_commute k hcentral
            (collectedDefect n diag' cross' a' b') (x (Fin.last n))
          simp only [ha, one_ne_zero, if_false, Pi.add_apply, hb, add_zero]
          calc
            x (Fin.last n) *
                (kernelValue k (collectedDefect n diag' cross' a' b') *
                  collectedWord n x' (a' + b')) =
                (x (Fin.last n) *
                  kernelValue k (collectedDefect n diag' cross' a' b')) *
                    collectedWord n x' (a' + b') := by group
            _ = (kernelValue k (collectedDefect n diag' cross' a' b') *
                  x (Fin.last n)) * collectedWord n x' (a' + b') := by
                    rw [hc.eq.symm]
            _ = kernelValue k (collectedDefect n diag' cross' a' b') *
                (x (Fin.last n) *
                  collectedWord n x' (fun i => (a + b) i.castSucc)) := by
                    rw [hab']
                    group
      · simp only [collectedWord, bitFactor, hb, one_ne_zero, if_false,
          collectedDefect]
        have hmove := collectedWord_mul_generator k hcentral n x' a'
          (x (Fin.last n)) (fun i => cross i.castSucc (Fin.last n))
          (fun i => hswap i.castSucc (Fin.last n) (Fin.castSucc_lt_last i))
        rw [show
          ((if a (Fin.last n) = 0 then 1 else x (Fin.last n)) *
              collectedWord n x' a') *
              (x (Fin.last n) * collectedWord n x' b') =
            (if a (Fin.last n) = 0 then 1 else x (Fin.last n)) *
              (collectedWord n x' a' * x (Fin.last n)) * collectedWord n x' b' by
                group,
          hmove]
        rcases zmodTwo_eq_zero_or_one (a (Fin.last n)) with ha | ha
        · simp only [ha, if_pos, one_mul, zero_add, Pi.add_apply, hb]
          have hc := kernelValue_commute k hcentral
            (collectedDefect n diag' cross' a' b')
            (x (Fin.last n))
          calc
            (kernelValue k
                (bitSum n a' (fun i => cross i.castSucc (Fin.last n))) *
                  x (Fin.last n) * collectedWord n x' a') *
                    collectedWord n x' b' =
                kernelValue k
                    (bitSum n a' (fun i => cross i.castSucc (Fin.last n))) *
                  x (Fin.last n) *
                    (collectedWord n x' a' * collectedWord n x' b') := by group
            _ = kernelValue k
                    (bitSum n a' (fun i => cross i.castSucc (Fin.last n))) *
                  x (Fin.last n) *
                    (kernelValue k (collectedDefect n diag' cross' a' b') *
                      collectedWord n x' (a' + b')) := by rw [ih']
            _ = kernelValue k
                    (bitSum n a' (fun i => cross i.castSucc (Fin.last n))) *
                  kernelValue k (collectedDefect n diag' cross' a' b') *
                    x (Fin.last n) * collectedWord n x' (a' + b') := by
                      calc
                        kernelValue k
                              (bitSum n a'
                                (fun i => cross i.castSucc (Fin.last n))) *
                            x (Fin.last n) *
                              (kernelValue k
                                  (collectedDefect n diag' cross' a' b') *
                                collectedWord n x' (a' + b')) =
                            kernelValue k
                                (bitSum n a'
                                  (fun i => cross i.castSucc (Fin.last n))) *
                              (x (Fin.last n) *
                                kernelValue k
                                  (collectedDefect n diag' cross' a' b')) *
                                collectedWord n x' (a' + b') := by group
                        _ = kernelValue k
                                (bitSum n a'
                                  (fun i => cross i.castSucc (Fin.last n))) *
                              (kernelValue k
                                  (collectedDefect n diag' cross' a' b') *
                                x (Fin.last n)) *
                                  collectedWord n x' (a' + b') := by
                                    rw [hc.eq.symm]
                        _ = _ := by group
            _ = kernelValue k
                  (bitSum n a' (fun i => cross i.castSucc (Fin.last n)) +
                    collectedDefect n diag' cross' a' b') *
                (x (Fin.last n) *
                  collectedWord n x' (fun i => (a + b) i.castSucc)) := by
                    rw [kernelValue_add, hab']
                    group
            _ = kernelValue k
                  ((bitSum n (fun i => a i.castSucc)
                      (fun i => cross i.castSucc (Fin.last n)) + 0) +
                    collectedDefect n (fun i => diag i.castSucc)
                      (fun i j => cross i.castSucc j.castSucc)
                      (fun i => a i.castSucc) (fun i => b i.castSucc)) *
                (x (Fin.last n) *
                  collectedWord n (fun i => x i.castSucc)
                    (fun i => (a + b) i.castSucc)) := by
                      simp only [a', b', diag', cross', add_zero]
                      rfl
        · simp only [ha, one_ne_zero, if_false, Pi.add_apply, hb,
            show (1 + 1 : ZMod 2) = 0 by decide, if_pos, one_mul]
          have hc := kernelValue_commute k hcentral
            (bitSum n a' (fun i => cross i.castSucc (Fin.last n)))
            (x (Fin.last n))
          calc
            (x (Fin.last n) *
                (kernelValue k
                    (bitSum n a' (fun i => cross i.castSucc (Fin.last n))) *
                  x (Fin.last n) * collectedWord n x' a')) *
                    collectedWord n x' b' =
                kernelValue k
                    (bitSum n a' (fun i => cross i.castSucc (Fin.last n))) *
                  (x (Fin.last n) ^ 2) *
                    (collectedWord n x' a' * collectedWord n x' b') := by
                      calc
                        (x (Fin.last n) *
                            (kernelValue k
                                (bitSum n a'
                                  (fun i => cross i.castSucc (Fin.last n))) *
                              x (Fin.last n) * collectedWord n x' a')) *
                              collectedWord n x' b' =
                            (x (Fin.last n) *
                              kernelValue k
                                (bitSum n a'
                                  (fun i => cross i.castSucc (Fin.last n)))) *
                              x (Fin.last n) *
                                (collectedWord n x' a' * collectedWord n x' b') := by
                                  group
                        _ = (kernelValue k
                                (bitSum n a'
                                  (fun i => cross i.castSucc (Fin.last n))) *
                              x (Fin.last n)) * x (Fin.last n) *
                                (collectedWord n x' a' * collectedWord n x' b') := by
                                  rw [hc.eq.symm]
                        _ = _ := by rw [pow_two]; group
            _ = kernelValue k
                    (bitSum n a' (fun i => cross i.castSucc (Fin.last n))) *
                  kernelValue k (diag (Fin.last n)) *
                    (kernelValue k (collectedDefect n diag' cross' a' b') *
                      collectedWord n x' (a' + b')) := by
                        rw [hsq (Fin.last n), ih']
            _ = kernelValue k
                  ((bitSum n a' (fun i => cross i.castSucc (Fin.last n)) +
                      diag (Fin.last n)) +
                    collectedDefect n diag' cross' a' b') *
                collectedWord n x' (fun i => (a + b) i.castSucc) := by
                  rw [kernelValue_add, kernelValue_add, hab']
                  group
            _ = kernelValue k
                  ((bitSum n (fun i => a i.castSucc)
                      (fun i => cross i.castSucc (Fin.last n)) +
                      diag (Fin.last n)) +
                    collectedDefect n (fun i => diag i.castSucc)
                      (fun i j => cross i.castSucc j.castSucc)
                      (fun i => a i.castSucc) (fun i => b i.castSucc)) *
                collectedWord n (fun i => x i.castSucc)
                  (fun i => (a + b) i.castSucc) := by
                    simp only [a', b', diag', cross']
                    rfl

private theorem bitSum_eq_sum_smul : ∀ n : ℕ, ∀ (a : Fin n → ZMod 2) (d : Fin n → W),
    bitSum n a d = ∑ i, a i • d i := by
  intro n
  induction n with
  | zero =>
      intro a d
      simp [bitSum]
  | succ n ih =>
      intro a d
      rw [Fin.sum_univ_castSucc]
      rcases zmodTwo_eq_zero_or_one (a (Fin.last n)) with ha | ha
      · simp [bitSum, ih, ha]
      · simp [bitSum, ih, ha]

private theorem map_collectedWord {V : Type uV} [AddCommGroup V]
    (f : E →* Multiplicative V) : ∀ n : ℕ,
    ∀ (x : Fin n → E) (a : Fin n → ZMod 2) (d : Fin n → V),
      (∀ i, f (x i) = Multiplicative.ofAdd (d i)) →
      f (collectedWord n x a) = Multiplicative.ofAdd (bitSum n a d) := by
  intro n
  induction n with
  | zero =>
      intro x a d hx
      simp [collectedWord, bitSum]
  | succ n ih =>
      intro x a d hx
      rcases zmodTwo_eq_zero_or_one (a (Fin.last n)) with ha | ha
      · simp [collectedWord, bitFactor, bitSum, ha,
          ih (fun i => x i.castSucc) (fun i => a i.castSucc)
            (fun i => d i.castSucc) (fun i => hx i.castSucc)]
      · simp [collectedWord, bitFactor, bitSum, ha, hx,
          ih (fun i => x i.castSucc) (fun i => a i.castSucc)
            (fun i => d i.castSucc) (fun i => hx i.castSucc), add_comm]

@[simp] private theorem collectedWord_zero : ∀ n : ℕ, ∀ x : Fin n → E,
    collectedWord n x 0 = 1 := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      simp only [collectedWord, Pi.zero_apply, bitFactor, if_pos, one_mul]
      change collectedWord n (fun i ↦ x i.castSucc) 0 = 1
      exact ih (fun i ↦ x i.castSucc)

end CollectedWords

section Classification

variable {V : Type uV} [AddCommGroup V] [Module (ZMod 2) V]
variable {W : Type uW} [AddCommGroup W] [Module (ZMod 2) W]
variable {E : Type uE} [Group E]

/-- The kernel coordinate of the commutator forced by a square map. -/
private def squareCross (q : V → W) (u v : V) : W :=
  q u + q (u + v) + q v

/-- Arbitrarily lift each vector in a fixed basis through the quotient map. -/
private def basisLift {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (basis : Basis (Fin n) (ZMod 2) V) (i : Fin n) : E :=
  S.surjInvRightHom (Multiplicative.ofAdd (basis i))

omit [Module (ZMod 2) W] in
@[simp] private theorem rightHom_basisLift {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (basis : Basis (Fin n) (ZMod 2) V) (i : Fin n) :
    S.rightHom (basisLift S basis i) = Multiplicative.ofAdd (basis i) := by
  simp [basisLift]

/-- The descending basis word representing a quotient vector. -/
private def extensionWord {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (basis : Basis (Fin n) (ZMod 2) V) (v : V) : E :=
  collectedWord n (basisLift S basis) (basis.equivFun v)

omit [Module (ZMod 2) W] in
@[simp] private theorem rightHom_extensionWord {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (basis : Basis (Fin n) (ZMod 2) V) (v : V) :
    S.rightHom (extensionWord S basis v) = Multiplicative.ofAdd v := by
  rw [extensionWord,
    map_collectedWord S.rightHom n (basisLift S basis) (basis.equivFun v) basis
      (rightHom_basisLift S basis)]
  congr 1
  rw [bitSum_eq_sum_smul, basis.sum_equivFun]

private theorem mul_swap_of_squareMap
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (q : V → W)
    (hsq : ∀ e : E, e ^ 2 =
      S.inl (Multiplicative.ofAdd (q (S.rightHom e).toAdd)))
    (x y : E) :
    x * y = kernelValue S.inl
        (squareCross q (S.rightHom x).toAdd (S.rightHom y).toAdd) * y * x := by
  have hxy : (S.rightHom (x⁻¹ * y)).toAdd =
      (S.rightHom x).toAdd + (S.rightHom y).toAdd := by
    simp only [map_mul, map_inv]
    change -(S.rightHom x).toAdd + (S.rightHom y).toAdd = _
    rw [neg_eq_self]
  calc
    x * y = (x ^ 2 * (x⁻¹ * y) ^ 2 * (y ^ 2)⁻¹) * y * x := by
      simp only [pow_two, mul_inv_rev]
      group
    _ = (kernelValue S.inl (q (S.rightHom x).toAdd) *
          kernelValue S.inl (q (S.rightHom (x⁻¹ * y)).toAdd) *
          (kernelValue S.inl (q (S.rightHom y).toAdd))⁻¹) * y * x := by
            rw [hsq x, hsq (x⁻¹ * y), hsq y]
    _ = kernelValue S.inl
          (q (S.rightHom x).toAdd + q (S.rightHom (x⁻¹ * y)).toAdd -
            q (S.rightHom y).toAdd) * y * x := by
              simp only [sub_eq_add_neg]
              rw [← kernelValue_neg, ← kernelValue_add, ← kernelValue_add]
    _ = kernelValue S.inl
          (squareCross q (S.rightHom x).toAdd (S.rightHom y).toAdd) * y * x := by
            rw [hxy, sub_eq_add_neg, neg_eq_self]
            rfl

/-- The common defect in the basis-word multiplication law. -/
private def extensionDefect {n : ℕ} (q : V → W)
    (basis : Basis (Fin n) (ZMod 2) V)
    (a b : Fin n → ZMod 2) : W :=
  collectedDefect n (fun i ↦ q (basis i))
    (fun i j ↦ squareCross q (basis i) (basis j)) a b

private theorem extensionWord_mul {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (hcentral : S.inl.range ≤ Subgroup.center E)
    (q : V → W)
    (basis : Basis (Fin n) (ZMod 2) V)
    (hsq : ∀ e : E, e ^ 2 =
      S.inl (Multiplicative.ofAdd (q (S.rightHom e).toAdd)))
    (a b : Fin n → ZMod 2) :
    collectedWord n (basisLift S basis) a *
        collectedWord n (basisLift S basis) b =
      kernelValue S.inl (extensionDefect q basis a b) *
        collectedWord n (basisLift S basis) (a + b) := by
  apply collectedWord_mul S.inl hcentral n (basisLift S basis)
      (fun i ↦ q (basis i))
      (fun i j ↦ squareCross q (basis i) (basis j))
  · intro i
    simpa using hsq (basisLift S basis i)
  · intro i j hij
    simpa using mul_swap_of_squareMap S q hsq
      (basisLift S basis i) (basisLift S basis j)

omit [Module (ZMod 2) W] in
@[simp] private theorem extensionWord_zero {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (basis : Basis (Fin n) (ZMod 2) V) :
    extensionWord S basis 0 = 1 := by
  simp [extensionWord]

private theorem extensionWord_mul' {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (hcentral : S.inl.range ≤ Subgroup.center E)
    (q : V → W)
    (basis : Basis (Fin n) (ZMod 2) V)
    (hsq : ∀ e : E, e ^ 2 =
      S.inl (Multiplicative.ofAdd (q (S.rightHom e).toAdd)))
    (u v : V) :
    extensionWord S basis u * extensionWord S basis v =
      kernelValue S.inl
          (extensionDefect q basis (basis.equivFun u) (basis.equivFun v)) *
        extensionWord S basis (u + v) := by
  simpa only [extensionWord, map_add] using
    extensionWord_mul S hcentral q basis hsq (basis.equivFun u) (basis.equivFun v)

/-- Kernel coordinate in the normal form determined by the ordered basis. -/
private def extensionKernelCoord {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (basis : Basis (Fin n) (ZMod 2) V) (e : E) : W :=
  (Function.invFun S.inl
    (e * (extensionWord S basis (S.rightHom e).toAdd)⁻¹)).toAdd

omit [Module (ZMod 2) W] in
private theorem extensionRemainder_mem_range {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (basis : Basis (Fin n) (ZMod 2) V) (e : E) :
    e * (extensionWord S basis (S.rightHom e).toAdd)⁻¹ ∈ S.inl.range := by
  rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
    map_mul, map_inv, rightHom_extensionWord, ofAdd_toAdd, mul_inv_cancel]

omit [Module (ZMod 2) W] in
private theorem inl_extensionKernelCoord {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (basis : Basis (Fin n) (ZMod 2) V) (e : E) :
    kernelValue S.inl (extensionKernelCoord S basis e) =
      e * (extensionWord S basis (S.rightHom e).toAdd)⁻¹ := by
  apply Function.invFun_eq
  exact extensionRemainder_mem_range S basis e

omit [Module (ZMod 2) W] in
private theorem extension_decomposition {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (basis : Basis (Fin n) (ZMod 2) V) (e : E) :
    kernelValue S.inl (extensionKernelCoord S basis e) *
        extensionWord S basis (S.rightHom e).toAdd = e := by
  rw [inl_extensionKernelCoord]
  group

omit [Module (ZMod 2) W] in
private theorem extensionKernelCoord_eq_of_eq {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (basis : Basis (Fin n) (ZMod 2) V) (e : E) (w : W)
    (he : e = kernelValue S.inl w *
      extensionWord S basis (S.rightHom e).toAdd) :
    extensionKernelCoord S basis e = w := by
  apply Multiplicative.ofAdd.injective
  apply S.inl_injective
  change kernelValue S.inl (extensionKernelCoord S basis e) = kernelValue S.inl w
  rw [inl_extensionKernelCoord, he]
  simp only [map_mul, GroupExtension.rightHom_inl, one_mul,
    rightHom_extensionWord, ofAdd_toAdd]
  group

private theorem extension_mul_normalForm {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (hcentral : S.inl.range ≤ Subgroup.center E)
    (q : V → W)
    (basis : Basis (Fin n) (ZMod 2) V)
    (hsq : ∀ e : E, e ^ 2 =
      S.inl (Multiplicative.ofAdd (q (S.rightHom e).toAdd)))
    (e f : E) :
    e * f =
      kernelValue S.inl
          ((extensionKernelCoord S basis e + extensionKernelCoord S basis f) +
            extensionDefect q basis (basis.equivFun (S.rightHom e).toAdd)
              (basis.equivFun (S.rightHom f).toAdd)) *
        extensionWord S basis
          ((S.rightHom e).toAdd + (S.rightHom f).toAdd) := by
  have hc := kernelValue_commute S.inl hcentral
    (extensionKernelCoord S basis f)
    (extensionWord S basis (S.rightHom e).toAdd)
  calc
    e * f =
        (kernelValue S.inl (extensionKernelCoord S basis e) *
          extensionWord S basis (S.rightHom e).toAdd) *
        (kernelValue S.inl (extensionKernelCoord S basis f) *
          extensionWord S basis (S.rightHom f).toAdd) := by
            rw [extension_decomposition S basis e, extension_decomposition S basis f]
    _ = (kernelValue S.inl (extensionKernelCoord S basis e) *
          kernelValue S.inl (extensionKernelCoord S basis f)) *
        (extensionWord S basis (S.rightHom e).toAdd *
          extensionWord S basis (S.rightHom f).toAdd) := by
            calc
              kernelValue S.inl (extensionKernelCoord S basis e) *
                    extensionWord S basis (S.rightHom e).toAdd *
                  (kernelValue S.inl (extensionKernelCoord S basis f) *
                    extensionWord S basis (S.rightHom f).toAdd) =
                  kernelValue S.inl (extensionKernelCoord S basis e) *
                    (extensionWord S basis (S.rightHom e).toAdd *
                      kernelValue S.inl (extensionKernelCoord S basis f)) *
                    extensionWord S basis (S.rightHom f).toAdd := by group
              _ = kernelValue S.inl (extensionKernelCoord S basis e) *
                    (kernelValue S.inl (extensionKernelCoord S basis f) *
                      extensionWord S basis (S.rightHom e).toAdd) *
                    extensionWord S basis (S.rightHom f).toAdd := by
                      rw [hc.eq.symm]
              _ = _ := by group
    _ = kernelValue S.inl
          (extensionKernelCoord S basis e + extensionKernelCoord S basis f) *
        (extensionWord S basis (S.rightHom e).toAdd *
          extensionWord S basis (S.rightHom f).toAdd) := by
            rw [kernelValue_add]
    _ = kernelValue S.inl
          (extensionKernelCoord S basis e + extensionKernelCoord S basis f) *
        (kernelValue S.inl
            (extensionDefect q basis (basis.equivFun (S.rightHom e).toAdd)
              (basis.equivFun (S.rightHom f).toAdd)) *
          extensionWord S basis
            ((S.rightHom e).toAdd + (S.rightHom f).toAdd)) := by
              rw [extensionWord_mul' S hcentral q basis hsq]
    _ = kernelValue S.inl
          ((extensionKernelCoord S basis e + extensionKernelCoord S basis f) +
            extensionDefect q basis (basis.equivFun (S.rightHom e).toAdd)
              (basis.equivFun (S.rightHom f).toAdd)) *
        extensionWord S basis
          ((S.rightHom e).toAdd + (S.rightHom f).toAdd) := by
            calc
              kernelValue S.inl
                    (extensionKernelCoord S basis e + extensionKernelCoord S basis f) *
                  (kernelValue S.inl
                      (extensionDefect q basis (basis.equivFun (S.rightHom e).toAdd)
                        (basis.equivFun (S.rightHom f).toAdd)) *
                    extensionWord S basis
                      ((S.rightHom e).toAdd + (S.rightHom f).toAdd)) =
                  (kernelValue S.inl
                      (extensionKernelCoord S basis e + extensionKernelCoord S basis f) *
                    kernelValue S.inl
                      (extensionDefect q basis (basis.equivFun (S.rightHom e).toAdd)
                        (basis.equivFun (S.rightHom f).toAdd))) *
                    extensionWord S basis
                      ((S.rightHom e).toAdd + (S.rightHom f).toAdd) := by group
              _ = _ := by rw [← kernelValue_add]

private theorem extensionKernelCoord_mul {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (hcentral : S.inl.range ≤ Subgroup.center E)
    (q : V → W)
    (basis : Basis (Fin n) (ZMod 2) V)
    (hsq : ∀ e : E, e ^ 2 =
      S.inl (Multiplicative.ofAdd (q (S.rightHom e).toAdd)))
    (e f : E) :
    extensionKernelCoord S basis (e * f) =
      (extensionKernelCoord S basis e + extensionKernelCoord S basis f) +
        extensionDefect q basis (basis.equivFun (S.rightHom e).toAdd)
          (basis.equivFun (S.rightHom f).toAdd) := by
  apply extensionKernelCoord_eq_of_eq S basis
  simpa only [map_mul, toAdd_mul] using
    extension_mul_normalForm S hcentral q basis hsq e f

omit [Module (ZMod 2) W] in
@[simp] private theorem extensionKernelCoord_inl {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (basis : Basis (Fin n) (ZMod 2) V) (w : W) :
    extensionKernelCoord S basis (S.inl (Multiplicative.ofAdd w)) = w := by
  apply extensionKernelCoord_eq_of_eq S basis
  simp only [GroupExtension.rightHom_inl, toAdd_one, extensionWord_zero, mul_one]

private theorem normalForm_mul {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (hcentral : S.inl.range ≤ Subgroup.center E)
    (q : V → W)
    (basis : Basis (Fin n) (ZMod 2) V)
    (hsq : ∀ e : E, e ^ 2 =
      S.inl (Multiplicative.ofAdd (q (S.rightHom e).toAdd)))
    (w z : W) (u v : V) :
    (kernelValue S.inl w * extensionWord S basis u) *
        (kernelValue S.inl z * extensionWord S basis v) =
      kernelValue S.inl
          ((w + z) + extensionDefect q basis (basis.equivFun u) (basis.equivFun v)) *
        extensionWord S basis (u + v) := by
  have hc := kernelValue_commute S.inl hcentral z (extensionWord S basis u)
  calc
    (kernelValue S.inl w * extensionWord S basis u) *
          (kernelValue S.inl z * extensionWord S basis v) =
        (kernelValue S.inl w * kernelValue S.inl z) *
          (extensionWord S basis u * extensionWord S basis v) := by
            calc
              (kernelValue S.inl w * extensionWord S basis u) *
                    (kernelValue S.inl z * extensionWord S basis v) =
                  kernelValue S.inl w *
                    (extensionWord S basis u * kernelValue S.inl z) *
                    extensionWord S basis v := by group
              _ = kernelValue S.inl w *
                    (kernelValue S.inl z * extensionWord S basis u) *
                    extensionWord S basis v := by rw [hc.eq.symm]
              _ = _ := by group
    _ = kernelValue S.inl (w + z) *
          (extensionWord S basis u * extensionWord S basis v) := by
            rw [kernelValue_add]
    _ = kernelValue S.inl (w + z) *
          (kernelValue S.inl
              (extensionDefect q basis (basis.equivFun u) (basis.equivFun v)) *
            extensionWord S basis (u + v)) := by
              rw [extensionWord_mul' S hcentral q basis hsq]
    _ = kernelValue S.inl
          ((w + z) + extensionDefect q basis (basis.equivFun u) (basis.equivFun v)) *
        extensionWord S basis (u + v) := by
          calc
            kernelValue S.inl (w + z) *
                  (kernelValue S.inl
                      (extensionDefect q basis (basis.equivFun u) (basis.equivFun v)) *
                    extensionWord S basis (u + v)) =
                (kernelValue S.inl (w + z) *
                  kernelValue S.inl
                    (extensionDefect q basis (basis.equivFun u) (basis.equivFun v))) *
                  extensionWord S basis (u + v) := by group
            _ = _ := by rw [← kernelValue_add]

private def extensionComparisonHom {E' : Type uE'} [Group E'] {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (T : GroupExtension (Multiplicative W) E' (Multiplicative V))
    (hcentralS : S.inl.range ≤ Subgroup.center E)
    (hcentralT : T.inl.range ≤ Subgroup.center E')
    (q : V → W)
    (basis : Basis (Fin n) (ZMod 2) V)
    (hsqS : ∀ e : E, e ^ 2 =
      S.inl (Multiplicative.ofAdd (q (S.rightHom e).toAdd)))
    (hsqT : ∀ e : E', e ^ 2 =
      T.inl (Multiplicative.ofAdd (q (T.rightHom e).toAdd))) : E →* E' :=
  MonoidHom.mk'
    (fun e ↦ kernelValue T.inl (extensionKernelCoord S basis e) *
      extensionWord T basis (S.rightHom e).toAdd)
    (by
      intro e f
      rw [extensionKernelCoord_mul S hcentralS q basis hsqS]
      simp only [map_mul, toAdd_mul]
      exact (normalForm_mul T hcentralT q basis hsqT
        (extensionKernelCoord S basis e) (extensionKernelCoord S basis f)
        (S.rightHom e).toAdd (S.rightHom f).toAdd).symm)

/-- Two central extensions of elementary abelian `2`-groups with the same
square coordinate map are equivalent as short exact sequences. -/
noncomputable def _root_.GroupExtension.equivOfCommonSquareMap
    {E' : Type uE'} [Group E'] {n : ℕ}
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (T : GroupExtension (Multiplicative W) E' (Multiplicative V))
    (hcentralS : S.inl.range ≤ Subgroup.center E)
    (hcentralT : T.inl.range ≤ Subgroup.center E')
    (q : V → W)
    (basis : Basis (Fin n) (ZMod 2) V)
    (hsqS : ∀ e : E, e ^ 2 =
      S.inl (Multiplicative.ofAdd (q (S.rightHom e).toAdd)))
    (hsqT : ∀ e : E', e ^ 2 =
      T.inl (Multiplicative.ofAdd (q (T.rightHom e).toAdd))) :
    S.Equiv T := by
  let f := extensionComparisonHom S T hcentralS hcentralT q basis hsqS hsqT
  apply GroupExtension.Equiv.ofMonoidHom f
  · apply MonoidHom.ext
    intro w
    change kernelValue T.inl (extensionKernelCoord S basis (S.inl w)) *
      extensionWord T basis (S.rightHom (S.inl w)).toAdd = T.inl w
    simp only [GroupExtension.rightHom_inl, toAdd_one, extensionWord_zero, mul_one]
    have hc : extensionKernelCoord S basis (S.inl w) = w.toAdd := by
      simpa only [ofAdd_toAdd] using extensionKernelCoord_inl S basis w.toAdd
    rw [hc]
    change T.inl (Multiplicative.ofAdd w.toAdd) = T.inl w
    rw [ofAdd_toAdd]
  · apply MonoidHom.ext
    intro e
    change T.rightHom (f e) = S.rightHom e
    simp [f, extensionComparisonHom]

end Classification

end

end OddOrder.GroupTheory
