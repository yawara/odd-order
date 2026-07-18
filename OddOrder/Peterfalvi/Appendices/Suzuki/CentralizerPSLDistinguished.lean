/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerDistinguishedBridge
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerPSLRoot

/-!
# Peterfalvi Part II, Ch. I section 3: the distinguished PSL pair

In the `PSL(2,q)` alternative of Proposition 1(c), the distinguished
involution `s` and the fixed involution `t` have product of order three.
The root subgroup alone does not determine this fact: an arbitrary
equivalence between Sylow subgroups need not preserve the distinguished
pair.  Here we retain the ambient conjugation used to put `Q` into standard
upper-unipotent coordinates and transport `s`, `t`, and the structure
equation together.

In those coordinates write `s = [[1,x],[0,1]]` and lift `t` to a matrix
`T = [[a,b],[c,d]]` in `SL(2,F)`.  Since `t` lies outside `Q`, `c` is
nonzero.  Comparing the lower-left entries in

`t s t = r^-1 t r`, with `r` also upper unipotent, gives `x*c = 1`.
Consequently `s*t` has trace and determinant one, so Cayley--Hamilton gives
`(s*t)^3 = 1`; the product is nonidentity and therefore has order three.

This is exactly the `PSL(2,ell)` order calculation cited in T. Peterfalvi,
*Character Theory for the Odd Order Theorem*, Part II, Ch. I section 3,
Proposition 1(c), pp. 105--106.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open Matrix
open OddOrder.GroupTheory
open OddOrder.GroupTheory.SpecificGroups.ProjectiveSpecialLinear

open scoped CharTwo LinearAlgebra.Projectivization MatrixGroups Pointwise

universe u v

/-! ## The standard matrix calculation -/

/-- A two-by-two matrix over a characteristic-two field with trace and
determinant one has cube one. -/
private theorem matrix_cubed_eq_one_of_trace_det_eq_one
    {F : Type u} [Field F] [CharP F 2]
    (M : Matrix (Fin 2) (Fin 2) F) (htrace : M.trace = 1)
    (hdet : M.det = 1) : M ^ 3 = 1 := by
  have hch := Matrix.aeval_self_charpoly M
  rw [Matrix.charpoly_fin_two] at hch
  have hpoly : M ^ 2 + M + 1 = 0 := by
    simpa [htrace, hdet, CharTwo.neg_eq] using hch
  have hsq : M ^ 2 = M + 1 := by
    have hpoly' : M ^ 2 + (M + 1) = 0 := by
      simpa only [add_assoc] using hpoly
    have hneg := eq_neg_of_add_eq_zero_left hpoly'
    calc
      M ^ 2 = -(M + 1) := hneg
      _ = M + 1 := by
        ext i j
        simp [CharTwo.neg_eq]
  calc
    M ^ 3 = M ^ 2 * M := by rw [pow_succ]
    _ = (M + 1) * M := by rw [hsq]
    _ = M ^ 2 + M := by rw [add_mul, one_mul, pow_two]
    _ = (M + 1) + M := by rw [hsq]
    _ = 1 := by
      ext i j
      simp [Matrix.add_apply, Matrix.one_apply, add_comm]

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), PSL case.**
Let `U` be the standard upper-unipotent root subgroup of `PSL(2,F)`.
If `s,r` lie in `U`, `s` is nonidentity, `t` is an involution outside
`U`, and `tst = r^-1 t r`, then `st` has order three.

The hypothesis `t notin U` is essential: it is the ambient information
lost by an arbitrary equivalence of Sylow subgroup carriers. -/
theorem orderOf_root_mul_eq_three_of_structure
    {F : Type u} [Field F] [Finite F] [CharP F 2]
    {s t r : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F}
    (hsU : s ∈ rootSubgroup (F := F)) (hs1 : s ≠ 1)
    (ht2 : t ^ 2 = 1) (htU : t ∉ rootSubgroup (F := F))
    (hrU : r ∈ rootSubgroup (F := F))
    (hstructure : t * s * t = r⁻¹ * t * r) :
    orderOf (s * t) = 3 := by
  let SL := Matrix.SpecialLinearGroup (Fin 2) F
  let Z : Subgroup SL := Subgroup.center SL
  let pi : SL →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.mk' Z
  have hpi : Function.Injective pi := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact center_specialLinearGroup_fin_two_eq_bot (F := F)
  change s ∈ (rootHom (F := F)).range at hsU
  change r ∈ (rootHom (F := F)).range at hrU
  obtain ⟨x, rfl⟩ := hsU
  obtain ⟨y, rfl⟩ := hrU
  obtain ⟨T, rfl⟩ := QuotientGroup.mk'_surjective Z t
  let Ux : SL := Matrix.SpecialLinearGroup.transvection Fin.zero_ne_one x.toAdd
  let Uy : SL := Matrix.SpecialLinearGroup.transvection Fin.zero_ne_one y.toAdd
  have hs_pi : rootHom (F := F) x = pi Ux := rfl
  have hr_pi : rootHom (F := F) y = pi Uy := rfl
  have hT2 : T ^ 2 = 1 := by
    apply hpi
    simpa only [map_pow, map_one] using ht2
  have hstructureSL : T * Ux * T = Uy⁻¹ * T * Uy := by
    apply hpi
    rw [map_mul, map_mul, map_mul, map_mul, map_inv]
    rw [← hs_pi, ← hr_pi]
    exact hstructure
  have hUyInv : Uy⁻¹ =
      Matrix.SpecialLinearGroup.transvection Fin.zero_ne_one (-y.toAdd) := by
    dsimp only [Uy]
    exact Matrix.SpecialLinearGroup.transvection_inv Fin.zero_ne_one y.toAdd
  let a : F := (T : Matrix (Fin 2) (Fin 2) F) 0 0
  let b : F := (T : Matrix (Fin 2) (Fin 2) F) 0 1
  let c : F := (T : Matrix (Fin 2) (Fin 2) F) 1 0
  let d : F := (T : Matrix (Fin 2) (Fin 2) F) 1 1
  have hT2mat :
      (T : Matrix (Fin 2) (Fin 2) F) ^ 2 = 1 :=
    congrArg Subtype.val hT2
  have hT00 : a * a + b * c = 1 := by
    have h := congrArg
      (fun A : Matrix (Fin 2) (Fin 2) F => A 0 0) hT2mat
    simpa [a, b, c, d, pow_two, Matrix.mul_apply] using h
  have hT10 : c * a + d * c = 0 := by
    have h := congrArg
      (fun A : Matrix (Fin 2) (Fin 2) F => A 1 0) hT2mat
    simpa [a, b, c, d, pow_two, Matrix.mul_apply] using h
  have hT11 : c * b + d * d = 1 := by
    have h := congrArg
      (fun A : Matrix (Fin 2) (Fin 2) F => A 1 1) hT2mat
    simpa [a, b, c, d, pow_two, Matrix.mul_apply] using h
  have hc : c ≠ 0 := by
    intro hc0
    have ha2 : a ^ 2 = 1 := by
      simpa [pow_two, hc0] using hT00
    have hd2 : d ^ 2 = 1 := by
      simpa [pow_two, hc0] using hT11
    have ha : a = 1 := by
      rw [sq_eq_one_iff] at ha2
      rcases ha2 with ha | ha
      · exact ha
      · simpa only [CharTwo.neg_eq] using ha
    have hd : d = 1 := by
      rw [sq_eq_one_iff] at hd2
      rcases hd2 with hd | hd
      · exact hd
      · simpa only [CharTwo.neg_eq] using hd
    have hTtrans : T =
        Matrix.SpecialLinearGroup.transvection Fin.zero_ne_one b := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.transvection_coe, a, b, c, d,
          ha, hd, hc0]
    apply htU
    change pi T ∈ (rootHom (F := F)).range
    refine ⟨Multiplicative.ofAdd b, ?_⟩
    rw [hTtrans]
    rfl
  have hstructure10 :
      c * a + (c * x.toAdd + d) * c = c := by
    rw [hUyInv] at hstructureSL
    have hstructureMat :
        (T : Matrix (Fin 2) (Fin 2) F) *
            (Ux : Matrix (Fin 2) (Fin 2) F) *
              (T : Matrix (Fin 2) (Fin 2) F) =
          (Matrix.SpecialLinearGroup.transvection Fin.zero_ne_one
                (-y.toAdd) : SL) *
              (T : Matrix (Fin 2) (Fin 2) F) *
                (Uy : Matrix (Fin 2) (Fin 2) F) :=
      congrArg Subtype.val hstructureSL
    have h := congrArg
      (fun A : Matrix (Fin 2) (Fin 2) F => A 1 0) hstructureMat
    simpa [Ux, Uy, a, b, c, d,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      CharTwo.neg_eq] using h
  have hcxc : c * x.toAdd * c = c := by
    calc
      c * x.toAdd * c =
          (c * a + (c * x.toAdd + d) * c) - (c * a + d * c) := by ring
      _ = c - 0 := by rw [hstructure10, hT10]
      _ = c := sub_zero c
  have hxc : x.toAdd * c = 1 := by
    apply mul_right_cancel₀ hc
    simpa [mul_assoc, mul_comm, mul_left_comm] using hcxc
  let M : SL := Ux * T
  have htrace : (M : Matrix (Fin 2) (Fin 2) F).trace = 1 := by
    have hMcoe : (M : Matrix (Fin 2) (Fin 2) F) =
        (Ux : Matrix (Fin 2) (Fin 2) F) *
          (T : Matrix (Fin 2) (Fin 2) F) := rfl
    rw [hMcoe, Matrix.trace_fin_two]
    suffices (a + x.toAdd * c) + d = 1 by
      simpa [Ux, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply]
    have hacd : a + d = 0 := by
      apply mul_left_cancel₀ hc
      calc
        c * (a + d) = c * a + d * c := by ring
        _ = 0 := hT10
        _ = c * 0 := by simp
    rw [hxc]
    calc
      (a + 1) + d = (a + d) + 1 := by ring
      _ = 0 + 1 := by rw [hacd]
      _ = 1 := zero_add 1
  have hdet : (M : Matrix (Fin 2) (Fin 2) F).det = 1 := M.2
  have hM3 : M ^ 3 = 1 := by
    apply Subtype.ext
    exact matrix_cubed_eq_one_of_trace_det_eq_one (M : Matrix (Fin 2) (Fin 2) F)
      htrace hdet
  have hcube : (rootHom (F := F) x * pi T) ^ 3 = 1 := by
    change (pi Ux * pi T) ^ 3 = 1
    rw [← map_mul, ← map_pow, hM3, map_one]
  apply orderOf_eq_prime hcube
  intro hprod
  apply htU
  have htEq : pi T = (rootHom (F := F) x)⁻¹ := by
    have h := congrArg (fun z => (rootHom (F := F) x)⁻¹ * z) hprod
    simpa using h
  rw [htEq]
  exact (rootSubgroup (F := F)).inv_mem ⟨x, rfl⟩

namespace Hypothesis

variable {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
  [Finite G]

/-! ## Transporting the complete pair through a PSL target -/

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), PSL case.**
For a concrete `PSL(2,F)` Theorem A target, the distinguished product
`s*t` has order three.

Unlike `qMulEquivPSLRoot`, this proof keeps the ambient Sylow conjugator.
It therefore transports the structure equation and `t notin Q` together
with the root subgroup, which is exactly the additional information needed
to identify the distinguished standard pair. -/
theorem orderOf_distinguishedInvolution_mul_t_of_psl2Target
    (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    (data : PSL2InductionTarget (Omega := Omega) L) :
    orderOf (hyp.distinguishedInvolution * hyp.t) = 3 := by
  letI : Field data.F := data.fieldF
  letI : Finite data.F := data.finiteF
  letI : CharP data.F 2 := data.charTwoF
  have hcore := hyp.Q_and_residual_of_psl2_target L hLnormal hLodd
    data.cardF_gt_two data.groupEquiv data.actionEquiv
      data.actionEquiv_bijective
  obtain ⟨hQp, hQL, _, _⟩ := hcore
  let P : Sylow 2 G := Classical.choose (hyp.exists_sylow_two_eq_Q hQp)
  have hP : (P : Subgroup G) = hyp.Q :=
    Classical.choose_spec (hyp.exists_sylow_two_eq_Q hQp)
  have hPL : (P : Subgroup G) ≤ L := hP ▸ hQL
  let PL : Sylow 2 L := P.subtype hPL
  let Pbar : Sylow 2
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) data.F) :=
    Sylow.mapEquiv data.groupEquiv PL
  let g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) data.F :=
    Classical.choose (MulAction.exists_smul_eq _ Pbar
      (rootSylow (F := data.F)))
  have hg : g • Pbar = rootSylow (F := data.F) :=
    Classical.choose_spec (MulAction.exists_smul_eq _ Pbar
      (rootSylow (F := data.F)))
  let e : L ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) data.F :=
    data.groupEquiv.trans (MulAut.conj g)
  have hPLQ : (PL : Subgroup L) = hyp.Q.subgroupOf L := by
    dsimp only [PL]
    rw [Sylow.coe_subtype]
    ext x
    change (x : G) ∈ P ↔ (x : G) ∈ hyp.Q
    exact SetLike.ext_iff.mp hP (x : G)
  have hrootEq :
      (MulAut.conj g) • (Pbar : Subgroup
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) data.F)) =
        rootSubgroup (F := data.F) := by
    rw [← Sylow.coe_subgroup_smul, hg, coe_rootSylow]
  have hmem_root_iff (x : L) :
      e x ∈ rootSubgroup (F := data.F) ↔ (x : G) ∈ hyp.Q := by
    have hmap : data.groupEquiv x ∈ (Pbar : Subgroup
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) data.F)) ↔
          x ∈ (PL : Subgroup L) := by
      dsimp only [Pbar]
      rw [Sylow.coe_mapEquiv, Subgroup.mem_map_equiv]
      simp
    constructor
    · intro hx
      change (MulAut.conj g) • data.groupEquiv x ∈
        rootSubgroup (F := data.F) at hx
      rw [← hrootEq, Subgroup.smul_mem_pointwise_smul_iff] at hx
      have hxPL : x ∈ (PL : Subgroup L) := hmap.mp hx
      have hxQL : x ∈ hyp.Q.subgroupOf L :=
        (SetLike.ext_iff.mp hPLQ x).mp hxPL
      exact hxQL
    · intro hx
      change (MulAut.conj g) • data.groupEquiv x ∈
        rootSubgroup (F := data.F)
      rw [← hrootEq, Subgroup.smul_mem_pointwise_smul_iff]
      apply hmap.mpr
      apply (SetLike.ext_iff.mp hPLQ x).mpr
      exact hx
  have hsQ : hyp.distinguishedInvolution ∈ hyp.Q :=
    hyp.mem_Q_of_sq_eq_one_of_mem_H hyp.distinguishedInvolution_mem_H
      hyp.distinguishedInvolution_sq
  have hrQ : hyp.structureConjugator ∈ hyp.Q :=
    hyp.structureConjugator_mem_Q
  have hsL : hyp.distinguishedInvolution ∈ L := hQL hsQ
  have hrL : hyp.structureConjugator ∈ L := hQL hrQ
  have htL : hyp.t ∈ L := by
    obtain ⟨c, hc⟩ := isConj_iff.mp
      (hyp.isConj_of_involutions hyp.distinguishedInvolution_sq
        hyp.distinguishedInvolution_ne_one hyp.t_sq hyp.t_ne_one)
    rw [← hc]
    exact hLnormal.conj_mem hyp.distinguishedInvolution hsL c
  let sL : L := ⟨hyp.distinguishedInvolution, hsL⟩
  let rL : L := ⟨hyp.structureConjugator, hrL⟩
  let tL : L := ⟨hyp.t, htL⟩
  have hesU : e sL ∈ rootSubgroup (F := data.F) :=
    (hmem_root_iff sL).2 hsQ
  have herU : e rL ∈ rootSubgroup (F := data.F) :=
    (hmem_root_iff rL).2 hrQ
  have hetU : e tL ∉ rootSubgroup (F := data.F) := by
    intro ht
    exact hyp.t_not_mem_H (hyp.Q_le_H ((hmem_root_iff tL).1 ht))
  have hes1 : e sL ≠ 1 := by
    intro hs
    apply hyp.distinguishedInvolution_ne_one
    exact congrArg (fun z : L => (z : G))
      (e.injective (hs.trans (map_one e).symm))
  have het2 : (e tL) ^ 2 = 1 := by
    rw [← map_pow, show tL ^ 2 = 1 from Subtype.ext hyp.t_sq, map_one]
  have hstructureL : tL * sL * tL = rL⁻¹ * tL * rL :=
    Subtype.ext hyp.structure_equation
  have hstructureTarget :
      e tL * e sL * e tL = (e rL)⁻¹ * e tL * e rL := by
    simpa only [map_mul, map_inv] using congrArg e hstructureL
  have htarget : orderOf (e sL * e tL) = 3 :=
    orderOf_root_mul_eq_three_of_structure hesU hes1 het2 hetU herU
      hstructureTarget
  have hLorder : orderOf (sL * tL) = 3 := by
    rw [← orderOf_injective e.toMonoidHom e.injective]
    change orderOf (e (sL * tL)) = 3
    rw [map_mul]
    exact htarget
  calc
    orderOf (hyp.distinguishedInvolution * hyp.t) =
        orderOf (sL * tL) :=
      orderOf_injective L.subtype L.subtype_injective (sL * tL)
    _ = 3 := hLorder

/-! ## The faithful centralizer quotient -/

/-- **Peterfalvi Part II, Ch. I section 3, Proposition 1(c), PSL case.**
In the PSL branch of the induction conclusion for
`C_G(X)/N(C_G(X))`, the original distinguished product `s*t` has order
three.  The standard matrix calculation gives the order in the faithful
quotient, and `orderOf_distinguishedInvolution_mul_t_of_quotient_pow`
lifts it across the odd central kernel. -/
theorem orderOf_distinguishedInvolution_mul_t_of_centralizer_psl2Target
    (hyp : Hypothesis G Omega) {X : Subgroup G}
    (hXV : X ≤ hyp.V)
    (hA3 : ∃ E : Subgroup (Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (result :
      letI := hyp.centralizerQuotientMulAction hXV
      TheoremAConclusion (hyp.centralizerActionQuotient X)
        ↥(MulAction.fixedPoints X Omega))
    (data :
      letI := hyp.centralizerQuotientMulAction hXV
      PSL2InductionTarget (Omega := ↥(MulAction.fixedPoints X Omega)) result.L) :
    orderOf (hyp.distinguishedInvolution * hyp.t) = 3 := by
  letI := hyp.centralizerQuotientMulAction hXV
  let qhyp := hyp.centralizerQuotientHypothesis hXV hA3
  have hquotOrder :
      orderOf (qhyp.distinguishedInvolution * qhyp.t) = 3 :=
    qhyp.orderOf_distinguishedInvolution_mul_t_of_psl2Target
      result.L result.normal result.oddIndex data
  have hquotCube : (qhyp.distinguishedInvolution * qhyp.t) ^ 3 = 1 := by
    rw [← hquotOrder]
    exact pow_orderOf_eq_one _
  exact hyp.orderOf_distinguishedInvolution_mul_t_of_quotient_pow
    hXV hA3 Nat.prime_three hquotCube

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
