/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanCoverAbelian

/-!
# Higman Lemma 7: the cover power overlap

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 7,
p. 86; used in Peterfalvi, Appendix III.

If an abelian normal actor-invariant subgroup `A` is the Frattini subgroup
of a normal invariant cover `C` and `C' ≤ A²`, squaring induces the actual
equivariant isomorphism

`L₁(C) = C / Phi(C) ≃ A / A²`.

This file constructs that map, rather than postulating Higman's overlap of
composition factors, and then combines it with the second-layer Agemo bridge
and the spectral contradiction to prove Lemma 7.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped commutatorElement IsMulCommutative

universe u

variable {P X : Type*} [Group P] [Group X]

/-- Canonical-group version of `A/A²`, used internally so that subgroup
actions retain the inherited `Group A` instance. -/
private abbrev AgemoZeroQuotientRaw (A : Type*) [Group A] :=
  ↥(Agemo A 2 0) ⧸
    (Agemo A 2 1).subgroupOf (Agemo A 2 0)

/-- The first Agemo quotient embeds in the ambient quotient by the image of
`A²`. -/
private def agemoZeroQuotientToAmbientHom
    {A : Subgroup P} [A.Normal] :
    AgemoZeroQuotientRaw A →*
      P ⧸ (Agemo A 2 1).map A.subtype := by
  refine QuotientGroup.map
    ((Agemo A 2 1).subgroupOf (Agemo A 2 0))
    ((Agemo A 2 1).map A.subtype)
    (A.subtype.comp (Agemo A 2 0).subtype) ?_
  intro a ha
  change A.subtype ((a : Agemo A 2 0) : A) ∈
    (Agemo A 2 1).map A.subtype
  exact ⟨((a : Agemo A 2 0) : A), ha, rfl⟩

@[simp] private theorem agemoZeroQuotientToAmbientHom_mk
    {A : Subgroup P} [A.Normal] (a : Agemo A 2 0) :
    agemoZeroQuotientToAmbientHom
        (QuotientGroup.mk'
          ((Agemo A 2 1).subgroupOf (Agemo A 2 0)) a) =
      QuotientGroup.mk' ((Agemo A 2 1).map A.subtype) ((a : A) : P) :=
  rfl

private theorem agemoZeroQuotientToAmbientHom_injective
    {A : Subgroup P} [A.Normal] :
    Function.Injective
      (agemoZeroQuotientToAmbientHom (P := P) (A := A)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro q hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
      ((Agemo A 2 1).subgroupOf (Agemo A 2 0)) q
    rw [MonoidHom.mem_ker, agemoZeroQuotientToAmbientHom_mk] at hq
    have hq' : (((a : Agemo A 2 0) : A) : P) ∈
        (Agemo A 2 1).map A.subtype :=
      (QuotientGroup.eq_one_iff
        (((a : Agemo A 2 0) : A) : P)).mp hq
    rw [Subgroup.mem_bot]
    change QuotientGroup.mk'
      ((Agemo A 2 1).subgroupOf (Agemo A 2 0)) a = 1
    apply (QuotientGroup.eq_one_iff a).mpr
    change ((a : Agemo A 2 0) : A) ∈ Agemo A 2 1
    exact (Subgroup.mem_map_iff_mem A.subtype_injective).mp hq'
  · exact bot_le

/-- A square in `C`, regarded as an element of the zeroth Agemo term of
`A = Phi(C)`. -/
private def coverSquareRepresentative
    [Finite P] (hP : IsPGroup 2 P)
    {A C : Subgroup P}
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (c : C) : Agemo A 2 0 := by
  have hcPhi : c ^ 2 ∈ frattini C :=
    IsPGroup.pow_mem_frattini (hP.to_subgroup C) c
  have hcA : ((c : P) ^ 2) ∈ A := by
    rw [← hPhi]
    exact ⟨c ^ 2, hcPhi, rfl⟩
  exact ⟨⟨(c : P) ^ 2, hcA⟩, by
    rw [agemo_zero_eq_top]
    exact Subgroup.mem_top _⟩

@[simp] private theorem coverSquareRepresentative_val
    [Finite P] (hP : IsPGroup 2 P)
    {A C : Subgroup P}
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (c : C) :
    (((coverSquareRepresentative hP hPhi c : Agemo A 2 0) : A) : P) =
      (c : P) ^ 2 :=
  rfl

/-- Raw square homomorphism, before packaging the commutative structure of
`A`.  The assumption `C' ≤ A²` is exactly what makes squaring multiplicative
modulo `A²`. -/
private def coverSquareToAgemoZeroHomRaw
    [Finite P] (hP : IsPGroup 2 P)
    {A C : Subgroup P} [A.Normal]
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    C →* AgemoZeroQuotientRaw A where
  toFun c := QuotientGroup.mk'
    ((Agemo A 2 1).subgroupOf (Agemo A 2 0))
    (coverSquareRepresentative hP hPhi c)
  map_one' := by
    apply agemoZeroQuotientToAmbientHom_injective (P := P) (A := A)
    simp only [agemoZeroQuotientToAmbientHom_mk,
      coverSquareRepresentative_val, Subgroup.coe_one, one_pow, map_one]
  map_mul' x y := by
    apply agemoZeroQuotientToAmbientHom_injective (P := P) (A := A)
    simp only [agemoZeroQuotientToAmbientHom_mk,
      coverSquareRepresentative_val, map_mul]
    let pi : P →* P ⧸ (Agemo A 2 1).map A.subtype :=
      QuotientGroup.mk' ((Agemo A 2 1).map A.subtype)
    have hcomm : pi (x : P) * pi (y : P) =
        pi (y : P) * pi (x : P) := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [← map_commutatorElement]
      apply (QuotientGroup.eq_one_iff _).mpr
      apply hderived
      exact ⟨⁅x, y⁆,
        Subgroup.commutator_mem_commutator
          (Subgroup.mem_top x) (Subgroup.mem_top y), rfl⟩
    change pi (((x * y : C) : P) ^ 2) =
      pi ((x : P) ^ 2) * pi ((y : P) ^ 2)
    calc
      pi (((x * y : C) : P) ^ 2) =
          (pi (((x * y : C) : P))) ^ 2 := map_pow pi _ 2
      _ = (pi (((x : C) : P) * ((y : C) : P))) ^ 2 := rfl
      _ = (pi (x : P) * pi (y : P)) ^ 2 :=
        congrArg (fun z => z ^ 2)
          (map_mul pi ((x : C) : P) ((y : C) : P))
      _ = pi (x : P) ^ 2 * pi (y : P) ^ 2 :=
        (show Commute (pi (x : P)) (pi (y : P)) from hcomm).mul_pow 2
      _ = pi ((x : P) ^ 2) * pi ((y : P) ^ 2) := by
        rw [map_pow, map_pow]

@[simp] private theorem coverSquareToAgemoZeroHomRaw_apply
    [Finite P] (hP : IsPGroup 2 P)
    {A C : Subgroup P} [A.Normal]
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) (c : C) :
    coverSquareToAgemoZeroHomRaw hP hPhi hderived c =
      QuotientGroup.mk'
        ((Agemo A 2 1).subgroupOf (Agemo A 2 0))
        (coverSquareRepresentative hP hPhi c) :=
  rfl

private theorem coverSquareToAgemoZeroHomRaw_surjective
    [Finite P] (hP : IsPGroup 2 P)
    {A C : Subgroup P} [A.Normal]
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    Function.Surjective
      (coverSquareToAgemoZeroHomRaw hP hPhi hderived) := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
    ((Agemo A 2 1).subgroupOf (Agemo A 2 0)) q
  have haPhi : (((a : Agemo A 2 0) : A) : P) ∈
      NormalInvariantCover.ambientFrattini C := by
    rw [hPhi]
    exact (a : A).2
  obtain ⟨z, hzPhi, hza⟩ := haPhi
  have hzgen : z ∈ _root_.commutator C ⊔
      Subgroup.closure (Set.range (fun c : C => c ^ 2)) := by
    rw [OddOrder.BG.Ch1.S01.commutator_sup_pow_closure_eq_frattini
      (hP.to_subgroup C)]
    exact hzPhi
  obtain ⟨u, hu, v, hv, huv⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hzgen
  let sq : C →* AgemoZeroQuotientRaw A :=
    coverSquareToAgemoZeroHomRaw hP hPhi hderived
  let emb : AgemoZeroQuotientRaw A →*
      P ⧸ (Agemo A 2 1).map A.subtype :=
    agemoZeroQuotientToAmbientHom
  let pi : P →* P ⧸ (Agemo A 2 1).map A.subtype :=
    QuotientGroup.mk' ((Agemo A 2 1).map A.subtype)
  have hsquare (c : C) : emb (sq c) = pi ((c : P) ^ 2) := rfl
  have hvRange : ∃ w : C, pi (v : P) = emb (sq w) := by
    refine Subgroup.closure_induction
      (p := fun (t : C) _ => ∃ w : C, pi (t : P) = emb (sq w))
      ?_ ?_ ?_ ?_ hv
    · rintro t ⟨w, rfl⟩
      exact ⟨w, (hsquare w).symm⟩
    · exact ⟨1, by simp⟩
    · intro x y hx hy ihx ihy
      obtain ⟨wx, hwx⟩ := ihx
      obtain ⟨wy, hwy⟩ := ihy
      refine ⟨wx * wy, ?_⟩
      change pi ((x : P) * (y : P)) = emb (sq (wx * wy))
      rw [map_mul, map_mul, hwx, hwy]
      exact (map_mul emb (sq wx) (sq wy)).symm
    · intro x hx ihx
      obtain ⟨w, hw⟩ := ihx
      refine ⟨w⁻¹, ?_⟩
      change pi ((x : P)⁻¹) = emb (sq (w⁻¹))
      rw [map_inv, map_inv, hw]
      exact (map_inv emb (sq w)).symm
  obtain ⟨w, hw⟩ := hvRange
  have huK : ((u : C) : P) ∈ (Agemo A 2 1).map A.subtype := by
    apply hderived
    exact ⟨u, hu, rfl⟩
  have hpiu : pi ((u : C) : P) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr huK
  refine ⟨w, ?_⟩
  apply agemoZeroQuotientToAmbientHom_injective (P := P) (A := A)
  change emb (sq w) = pi (((a : Agemo A 2 0) : A) : P)
  calc
    emb (sq w) = pi (v : P) := hw.symm
    _ = 1 * pi (v : P) := (one_mul _).symm
    _ = pi ((u : C) : P) * pi (v : P) := by rw [hpiu]
    _ = pi (((u : C) : P) * (v : P)) :=
      (map_mul pi ((u : C) : P) (v : P)).symm
    _ = pi (((u : C) * v : C) : P) := rfl
    _ = pi (z : P) := by rw [huv]
    _ = pi (((a : Agemo A 2 0) : A) : P) :=
      congrArg (fun t : P => pi t) hza

/-- Raw descended square map on the actual first lower-central layer. -/
private def lowerCentralLayerZeroToAgemoZeroHomRaw
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P} [A.Normal]
    (h : NormalInvariantCover act A C)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    lowerCentralLayer C 0 →* AgemoZeroQuotientRaw A := by
  apply QuotientGroup.lift (lowerCentralLayerKernel C 0)
    ((coverSquareToAgemoZeroHomRaw hP hPhi hderived).comp
      (lowerCentralTerm C 0).subtype)
  intro x hx
  rw [MonoidHom.mem_ker]
  change coverSquareToAgemoZeroHomRaw hP hPhi hderived
    ((lowerCentralTerm C 0).subtype x) = 1
  rw [coverSquareToAgemoZeroHomRaw_apply]
  change QuotientGroup.mk'
    ((Agemo A 2 1).subgroupOf (Agemo A 2 0))
    (coverSquareRepresentative hP hPhi
      ((lowerCentralTerm C 0).subtype x)) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  change (((coverSquareRepresentative hP hPhi
    ((lowerCentralTerm C 0).subtype x) : Agemo A 2 0) : A)) ∈
      Agemo A 2 1
  have hx' : x ∈
      (lowerCentralLayerKernelInAmbient C 0).subgroupOf
        (lowerCentralTerm C 0) := by
    rw [lowerCentralLayerKernelInAmbient_subgroupOf]
    exact hx
  have hxA : (((x : lowerCentralTerm C 0) : C) : P) ∈ A := by
    change (x : C) ∈ lowerCentralLayerKernelInAmbient C 0 at hx'
    rw [layerKernel_zero_eq_subgroupOf_of_ambientFrattini_eq
      hP h.le hPhi] at hx'
    exact hx'
  let a : A := ⟨(((x : lowerCentralTerm C 0) : C) : P), hxA⟩
  have hrep :
      (coverSquareRepresentative hP hPhi
        ((lowerCentralTerm C 0).subtype x) : A) = a ^ 2 := by
    apply Subtype.ext
    simp [a]
  rw [hrep]
  exact Agemo.mem_of_eq_pow (G := A) (p := 2) (n := 1) a

@[simp] private theorem lowerCentralLayerZeroToAgemoZeroHomRaw_mk
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P} [A.Normal]
    (h : NormalInvariantCover act A C)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) (x : lowerCentralTerm C 0) :
    lowerCentralLayerZeroToAgemoZeroHomRaw hP h hPhi hderived
        (QuotientGroup.mk' (lowerCentralLayerKernel C 0) x) =
      coverSquareToAgemoZeroHomRaw hP hPhi hderived
        ((lowerCentralTerm C 0).subtype x) :=
  rfl

private theorem lowerCentralLayerZeroToAgemoZeroHomRaw_surjective
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P} [A.Normal]
    (h : NormalInvariantCover act A C)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    Function.Surjective
      (lowerCentralLayerZeroToAgemoZeroHomRaw hP h hPhi hderived) := by
  intro q
  obtain ⟨c, rfl⟩ :=
    coverSquareToAgemoZeroHomRaw_surjective hP hPhi hderived q
  let x : lowerCentralTerm C 0 := ⟨c, by simp [lowerCentralTerm]⟩
  exact ⟨QuotientGroup.mk' (lowerCentralLayerKernel C 0) x, rfl⟩

/-- The square map from the cover to the first power factor of its
Frattini subgroup. -/
def coverSquareToAgemoZeroHom
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P}
    (h : NormalInvariantCover act A C)
    (hAcomm : IsMulCommutative A)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    C →* AgemoSuccQuotient A 0 := by
  letI : A.Normal := h.left.1
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  exact coverSquareToAgemoZeroHomRaw hP hPhi hderived

/-- Squaring descends to the actual zeroth lower-central layer. -/
def lowerCentralLayerZeroToAgemoZeroHom
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P}
    (h : NormalInvariantCover act A C)
    (hAcomm : IsMulCommutative A)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    lowerCentralLayer C 0 →* AgemoSuccQuotient A 0 := by
  letI : A.Normal := h.left.1
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  exact lowerCentralLayerZeroToAgemoZeroHomRaw hP h hPhi hderived

@[simp] private theorem coverSquareToAgemoZeroHom_apply
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P}
    (h : NormalInvariantCover act A C)
    (hAcomm : IsMulCommutative A)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) (c : C) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    coverSquareToAgemoZeroHom hP h hAcomm hPhi hderived c =
      QuotientGroup.mk'
        ((Agemo A 2 1).subgroupOf (Agemo A 2 0))
        (coverSquareRepresentative hP hPhi c) := by
  letI : A.Normal := h.left.1
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  rfl

@[simp] private theorem lowerCentralLayerZeroToAgemoZeroHom_mk
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P}
    (h : NormalInvariantCover act A C)
    (hAcomm : IsMulCommutative A)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) (x : lowerCentralTerm C 0) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    lowerCentralLayerZeroToAgemoZeroHom hP h hAcomm hPhi hderived
        (QuotientGroup.mk' (lowerCentralLayerKernel C 0) x) =
      coverSquareToAgemoZeroHom hP h hAcomm hPhi hderived
        ((lowerCentralTerm C 0).subtype x) := by
  letI : A.Normal := h.left.1
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  rfl

private theorem lowerCentralLayerZeroToAgemoZeroHom_surjective
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P}
    (h : NormalInvariantCover act A C)
    (hAcomm : IsMulCommutative A)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    Function.Surjective
      (lowerCentralLayerZeroToAgemoZeroHom
        hP h hAcomm hPhi hderived) := by
  letI : A.Normal := h.left.1
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  exact lowerCentralLayerZeroToAgemoZeroHomRaw_surjective
    hP h hPhi hderived

/-- The descended square map intertwines the actor actions. -/
theorem lowerCentralLayerZeroToAgemoZeroHom_equivariant
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P}
    (h : NormalInvariantCover act A C)
    (hAcomm : IsMulCommutative A)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    ∀ (g : X) (q : lowerCentralLayer C 0),
      lowerCentralLayerZeroToAgemoZeroHom hP h hAcomm hPhi hderived
          (lowerCentralLayerAction h.right.2.restrict 0 g q) =
        agemoSuccQuotientAction h.left.2.restrict 0 g
          (lowerCentralLayerZeroToAgemoZeroHom
            hP h hAcomm hPhi hderived q) := by
  have hAinv : IsAInvariant act A := h.left.2
  have hCinv : IsAInvariant act C := h.right.2
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  change ∀ (g : X) (q : lowerCentralLayer C 0),
    lowerCentralLayerZeroToAgemoZeroHom hP h hAcomm hPhi hderived
        (lowerCentralLayerAction hCinv.restrict 0 g q) =
      agemoSuccQuotientAction hAinv.restrict 0 g
        (lowerCentralLayerZeroToAgemoZeroHom
          hP h hAcomm hPhi hderived q)
  intro g q
  refine QuotientGroup.induction_on q ?_
  intro x
  change lowerCentralLayerZeroToAgemoZeroHom
      hP h hAcomm hPhi hderived
      (lowerCentralLayerAction hCinv.restrict 0 g
        (QuotientGroup.mk' (lowerCentralLayerKernel C 0) x)) =
    agemoSuccQuotientAction hAinv.restrict 0 g
      (lowerCentralLayerZeroToAgemoZeroHom
        hP h hAcomm hPhi hderived
        (QuotientGroup.mk' (lowerCentralLayerKernel C 0) x))
  rw [lowerCentralLayerAction_apply_mk,
    lowerCentralLayerZeroToAgemoZeroHom_mk,
    lowerCentralLayerZeroToAgemoZeroHom_mk,
    coverSquareToAgemoZeroHom_apply,
    coverSquareToAgemoZeroHom_apply]
  apply congrArg (QuotientGroup.mk'
    ((Agemo A 2 1).subgroupOf (Agemo A 2 0)))
  apply Subtype.ext
  apply Subtype.ext
  change (act g (((x : lowerCentralTerm C 0) : C) : P)) ^ 2 =
    act g ((((x : lowerCentralTerm C 0) : C) : P) ^ 2)
  exact (map_pow (act g) _ 2).symm

/-- Linear form of the descended square map. -/
noncomputable def lowerCentralLayerZeroToAgemoZeroLinearMap
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P}
    (h : NormalInvariantCover act A C)
    (hAcomm : IsMulCommutative A)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    letI : IsMulCommutative (lowerCentralLayer C 0) :=
      lowerCentralLayerIsMulCommutative C 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer C 0)) :=
      lowerCentralLayerZmodModule C 0
    Additive (lowerCentralLayer C 0) →ₗ[ZMod 2]
      Additive (AgemoSuccQuotient A 0) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  letI : IsMulCommutative (lowerCentralLayer C 0) :=
    lowerCentralLayerIsMulCommutative C 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer C 0)) :=
    lowerCentralLayerZmodModule C 0
  exact (lowerCentralLayerZeroToAgemoZeroHom
    hP h hAcomm hPhi hderived).toAdditive.toZModLinearMap 2

@[simp] theorem lowerCentralLayerZeroToAgemoZeroLinearMap_apply
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P}
    (h : NormalInvariantCover act A C)
    (hAcomm : IsMulCommutative A)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype)
    (v : Additive (lowerCentralLayer C 0)) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    letI : IsMulCommutative (lowerCentralLayer C 0) :=
      lowerCentralLayerIsMulCommutative C 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer C 0)) :=
      lowerCentralLayerZmodModule C 0
    lowerCentralLayerZeroToAgemoZeroLinearMap
        hP h hAcomm hPhi hderived v =
      Additive.ofMul
        (lowerCentralLayerZeroToAgemoZeroHom
          hP h hAcomm hPhi hderived v.toMul) := by
  rfl

private theorem lowerCentralLayerZeroToAgemoZeroLinearMap_surjective
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P}
    (h : NormalInvariantCover act A C)
    (hAcomm : IsMulCommutative A)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    letI : IsMulCommutative (lowerCentralLayer C 0) :=
      lowerCentralLayerIsMulCommutative C 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer C 0)) :=
      lowerCentralLayerZmodModule C 0
    Function.Surjective
      (lowerCentralLayerZeroToAgemoZeroLinearMap
        hP h hAcomm hPhi hderived) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  letI : IsMulCommutative (lowerCentralLayer C 0) :=
    lowerCentralLayerIsMulCommutative C 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer C 0)) :=
    lowerCentralLayerZmodModule C 0
  intro q
  obtain ⟨v, hv⟩ :=
    lowerCentralLayerZeroToAgemoZeroHom_surjective
      hP h hAcomm hPhi hderived q.toMul
  refine ⟨Additive.ofMul v, ?_⟩
  apply Additive.toMul.injective
  exact hv

/-- The linear square map intertwines the two representations. -/
theorem lowerCentralLayerZeroToAgemoZeroLinearMap_equivariant
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P}
    (h : NormalInvariantCover act A C)
    (hAcomm : IsMulCommutative A)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    letI : IsMulCommutative (lowerCentralLayer C 0) :=
      lowerCentralLayerIsMulCommutative C 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer C 0)) :=
      lowerCentralLayerZmodModule C 0
    ∀ (g : X) (v : Additive (lowerCentralLayer C 0)),
      lowerCentralLayerZeroToAgemoZeroLinearMap
          hP h hAcomm hPhi hderived
          (lowerCentralLayerRepresentation h.right.2.restrict 0 g v) =
        agemoSuccQuotientRepresentation h.left.2.restrict 0 g
          (lowerCentralLayerZeroToAgemoZeroLinearMap
            hP h hAcomm hPhi hderived v) := by
  have hAinv : IsAInvariant act A := h.left.2
  have hCinv : IsAInvariant act C := h.right.2
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  letI : IsMulCommutative (lowerCentralLayer C 0) :=
    lowerCentralLayerIsMulCommutative C 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer C 0)) :=
    lowerCentralLayerZmodModule C 0
  change ∀ (g : X) (v : Additive (lowerCentralLayer C 0)),
    lowerCentralLayerZeroToAgemoZeroLinearMap
        hP h hAcomm hPhi hderived
        (lowerCentralLayerRepresentation hCinv.restrict 0 g v) =
      agemoSuccQuotientRepresentation hAinv.restrict 0 g
        (lowerCentralLayerZeroToAgemoZeroLinearMap
          hP h hAcomm hPhi hderived v)
  intro g v
  apply Additive.toMul.injective
  exact lowerCentralLayerZeroToAgemoZeroHom_equivariant
    hP h hAcomm hPhi hderived g v.toMul

/-- A nontrivial finite abelian 2-group has a nontrivial first power
factor. -/
private theorem agemoZeroQuotient_nontrivial_of_ne_bot
    [Finite P] (hP : IsPGroup 2 P)
    {A : Subgroup P} (hAcomm : IsMulCommutative A)
    (hAne : A ≠ ⊥) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    Nontrivial (AgemoSuccQuotient A 0) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  letI : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hAne
  have hAgemo_ne : Agemo A 2 1 ≠ ⊤ := by
    intro htop
    have hPhiTop : frattini A = ⊤ := by
      rw [NormalInvariantCover.frattini_eq_agemo_one
        (hP.to_subgroup A), htop]
    have hbotTop : (⊥ : Subgroup A) = ⊤ :=
      frattini_nongenerating (by rw [hPhiTop, bot_sup_eq])
    exact (bot_ne_top : (⊥ : Subgroup A) ≠ ⊤) hbotTop
  let N : Subgroup (Agemo A 2 0) :=
    (Agemo A 2 1).subgroupOf (Agemo A 2 0)
  have hNne : N ≠ ⊤ := by
    intro hNtop
    apply hAgemo_ne
    calc
      Agemo A 2 1 = N.map (Agemo A 2 0).subtype := by
        exact (Subgroup.map_subgroupOf_eq_of_le
          (Agemo.anti (Nat.zero_le 1))).symm
      _ = (⊤ : Subgroup (Agemo A 2 0)).map
          (Agemo A 2 0).subtype := by rw [hNtop]
      _ = Agemo A 2 0 := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = ⊤ := agemo_zero_eq_top
  have hex : ∃ a : Agemo A 2 0, a ∉ N := by
    by_contra h
    push Not at h
    apply hNne
    exact (Subgroup.eq_top_iff' N).mpr h
  obtain ⟨a, ha⟩ := hex
  let q : AgemoSuccQuotient A 0 := QuotientGroup.mk' N a
  have hq : q ≠ 1 := by
    intro hq1
    exact ha ((QuotientGroup.eq_one_iff a).mp hq1)
  exact ⟨⟨q, 1, hq⟩⟩

/-- The square-overlap isomorphism between the actual first
lower-central layer of the cover and the first power factor of A. -/
noncomputable def lowerCentralLayerZeroToAgemoZeroLinearEquiv
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P}
    (h : NormalInvariantCover act A C)
    (hAcomm : IsMulCommutative A) (hAne : A ≠ ⊥)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    letI : IsMulCommutative (lowerCentralLayer C 0) :=
      lowerCentralLayerIsMulCommutative C 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer C 0)) :=
      lowerCentralLayerZmodModule C 0
    Additive (lowerCentralLayer C 0) ≃ₗ[ZMod 2]
      Additive (AgemoSuccQuotient A 0) := by
  have hAinv : IsAInvariant act A := h.left.2
  have hCinv : IsAInvariant act C := h.right.2
  letI : A.Normal := h.left.1
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  letI : IsMulCommutative (lowerCentralLayer C 0) :=
    lowerCentralLayerIsMulCommutative C 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer C 0)) :=
    lowerCentralLayerZmodModule C 0
  letI : Nontrivial (AgemoSuccQuotient A 0) :=
    agemoZeroQuotient_nontrivial_of_ne_bot hP hAcomm hAne
  let f := lowerCentralLayerZeroToAgemoZeroLinearMap
    hP h hAcomm hPhi hderived
  let rho := lowerCentralLayerRepresentation hCinv.restrict 0
  let tau := agemoSuccQuotientRepresentation hAinv.restrict 0
  let F : Representation.IntertwiningMap rho tau :=
    f.intertwiningMap_of_isIntertwiningMap rho tau
      (lowerCentralLayerZeroToAgemoZeroLinearMap_equivariant
        hP h hAcomm hPhi hderived)
  have hsurj : Function.Surjective f :=
    lowerCentralLayerZeroToAgemoZeroLinearMap_surjective
      hP h hAcomm hPhi hderived
  letI : Representation.IsIrreducible rho :=
    NormalInvariantCover.lowerCentralLayerZeroRepresentation_isIrreducible
      hP h hPhi
  have hFne : F ≠ 0 := by
    intro hF
    have hlin : F.toLinearMap = 0 :=
      congrArg Representation.IntertwiningMap.toLinearMap hF
    exact LinearMap.ne_zero_of_surjective hsurj hlin
  have hinj : Function.Injective f := by
    exact
      (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right
        hFne
  exact LinearEquiv.ofBijective f ⟨hinj, hsurj⟩

/-- The square-overlap isomorphism intertwines the two actor
representations. -/
theorem lowerCentralLayerZeroToAgemoZeroLinearEquiv_equivariant
    [Finite P] (hP : IsPGroup 2 P)
    {act : X →* MulAut P} {A C : Subgroup P}
    (h : NormalInvariantCover act A C)
    (hAcomm : IsMulCommutative A) (hAne : A ≠ ⊥)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    letI : IsMulCommutative (lowerCentralLayer C 0) :=
      lowerCentralLayerIsMulCommutative C 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer C 0)) :=
      lowerCentralLayerZmodModule C 0
    ∀ (g : X) (v : Additive (lowerCentralLayer C 0)),
      lowerCentralLayerZeroToAgemoZeroLinearEquiv
          hP h hAcomm hAne hPhi hderived
          (lowerCentralLayerRepresentation h.right.2.restrict 0 g v) =
        agemoSuccQuotientRepresentation h.left.2.restrict 0 g
          (lowerCentralLayerZeroToAgemoZeroLinearEquiv
            hP h hAcomm hAne hPhi hderived v) := by
  have hAinv : IsAInvariant act A := h.left.2
  have hCinv : IsAInvariant act C := h.right.2
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  letI : IsMulCommutative (lowerCentralLayer C 0) :=
    lowerCentralLayerIsMulCommutative C 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer C 0)) :=
    lowerCentralLayerZmodModule C 0
  change ∀ (g : X) (v : Additive (lowerCentralLayer C 0)),
    lowerCentralLayerZeroToAgemoZeroLinearEquiv
        hP h hAcomm hAne hPhi hderived
        (lowerCentralLayerRepresentation hCinv.restrict 0 g v) =
      agemoSuccQuotientRepresentation hAinv.restrict 0 g
        (lowerCentralLayerZeroToAgemoZeroLinearEquiv
          hP h hAcomm hAne hPhi hderived v)
  intro g v
  exact lowerCentralLayerZeroToAgemoZeroLinearMap_equivariant
    hP h hAcomm hPhi hderived g v

local instance coverPowerLayerIsMulCommutative
    (H : Type*) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

noncomputable local instance coverPowerLayerModTwo
    (H : Type*) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- The spectral conclusion of Higman Lemma 7 once the equivariant
square-overlap isomorphism has been supplied. -/
private theorem higmanLemmaSeven_isMulCommutative_of_overlap
    {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (X : Subgroup (MulAut P))
    (hXcyc : IsCyclic X)
    (htransP : ActsTransitivelyOnInvolutions X)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (A C : Subgroup P)
    (hcover : NormalInvariantCover X.subtype A C)
    (hAcomm : IsMulCommutative A)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    ∀ (E0 : Additive (lowerCentralLayer C 0) ≃ₗ[ZMod 2]
        Additive (AgemoSuccQuotient A 0)),
      (∀ g q,
        E0 (lowerCentralLayerRepresentation hcover.right.2.restrict 0 g q) =
          agemoSuccQuotientRepresentation hcover.left.2.restrict 0 g
            (E0 q)) →
      IsMulCommutative C := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
  intro E0 hE0
  letI : A.Normal := hcover.left.1
  letI : IsCyclic X := hXcyc
  letI : CommGroup X := IsCyclic.commGroup
  by_contra hncomm
  have hCtwo : IsPGroup 2 C := hP.to_subgroup C
  letI : Nontrivial (lowerCentralLayer C 1) :=
    lowerCentralLayer_one_nontrivial_of_not_isMulCommutative hCtwo hncomm
  letI : Nontrivial (lowerCentralLayer C 0) :=
    NormalInvariantCover.lowerCentralLayerZero_nontrivial
      hP hcover hPhi
  letI : Nontrivial (AgemoSuccQuotient A 0) :=
    E0.symm.toEquiv.nontrivial
  obtain ⟨x, y, hx, hy, hxy⟩ := hmulti
  have hAne : A ≠ ⊥ := by
    intro hAbot
    have hmap_le : (_root_.commutator C).map C.subtype ≤ A :=
      hderived.trans (Subgroup.map_subtype_le _)
    rw [hAbot] at hmap_le
    have hmap_bot : (_root_.commutator C).map C.subtype = ⊥ :=
      le_bot_iff.mp hmap_le
    have hcomm_bot : _root_.commutator C = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (_root_.commutator C) C.subtype_injective).mp hmap_bot
    exact hncomm ((commutator_eq_bot_iff C).mp hcomm_bot)
  have hinvA : involutions P ⊆ A :=
    involutions_subset_of_nontrivial_invariant
      hP X htransP hcover.left.2 hAne
  have htransA : ∀ a ∈ involutions A, ∀ b ∈ involutions A,
      ∃ g : X, hcover.left.2.restrict g a = b := by
    intro a ha b hb
    have haP : (a : P) ∈ involutions P := by
      refine ⟨congrArg Subtype.val ha.1, ?_⟩
      intro ha1
      exact ha.2 (Subtype.ext ha1)
    have hbP : (b : P) ∈ involutions P := by
      refine ⟨congrArg Subtype.val hb.1, ?_⟩
      intro hb1
      exact hb.2 (Subtype.ext hb1)
    obtain ⟨g, hg⟩ := htransP (a : P) haP (b : P) hbP
    refine ⟨g, Subtype.ext ?_⟩
    exact hg
  obtain ⟨ι, hι, e, he, hε, classify⟩ :=
    exists_homocyclic_and_invariant_eq_agemo
      (hP.to_subgroup A) hcover.left.2.restrict htransA
  letI : Fintype ι := hι
  obtain ⟨ε⟩ := hε
  obtain ⟨s, hse, E2, hE2⟩ :=
    exists_lowerCentralLayerOne_linearEquiv_agemoSucc_of_classification
      X.subtype A C hAcomm hcover.left.2 hcover.right.2 classify hderived
  letI : Nontrivial (AgemoSuccQuotient A s) :=
    E2.symm.toEquiv.nontrivial
  let xA : A := ⟨x, hinvA hx⟩
  let yA : A := ⟨y, hinvA hy⟩
  have hxA : xA ∈ involutions A := by
    refine ⟨Subtype.ext hx.1, ?_⟩
    intro hx1
    exact hx.2 (congrArg Subtype.val hx1)
  have hyA : yA ∈ involutions A := by
    refine ⟨Subtype.ext hy.1, ?_⟩
    intro hy1
    exact hy.2 (congrArg Subtype.val hy1)
  have hxyA : xA ≠ yA := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have hncyc : ¬ IsCyclic (AgemoSuccQuotient A s) :=
    not_isCyclic_agemoQuotient_of_two_involutions
      ε (Nat.lt_succ_self s) (Nat.succ_le_of_lt hse) hxA hyA hxyA
  have hfinrank : 2 ≤ Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer C 1)) :=
    finrank_ge_two_of_linearEquiv_agemoSucc s E2 hncyc
  have htrans2 : ∀ v w : Additive (lowerCentralLayer C 1),
      v ≠ 0 → w ≠ 0 →
        ∃ g : X,
          lowerCentralLayerRepresentation hcover.right.2.restrict 1 g v = w :=
    transitive_nonzero_of_equivariant_agemoSucc
      (lowerCentralLayerRepresentation hcover.right.2.restrict 1)
      hcover.left.2.restrict ε htransA hse E2 hE2
  have htransA0 : ∀ v w : Additive (AgemoSuccQuotient A 0),
      v ≠ 0 → w ≠ 0 →
        ∃ g : X,
          agemoSuccQuotientRepresentation hcover.left.2.restrict 0 g v = w := by
    intro v w hv hw
    have hv' : v.toMul ≠ 1 := by simpa using hv
    have hw' : w.toMul ≠ 1 := by simpa using hw
    obtain ⟨g, hg⟩ :=
      agemoSuccQuotientAction_transitive_on_nonidentity
        hcover.left.2.restrict ε htransA he v.toMul w.toMul hv' hw'
    refine ⟨g, Additive.toMul.injective ?_⟩
    exact hg
  have hirrA0 : Representation.IsIrreducible
      (agemoSuccQuotientRepresentation hcover.left.2.restrict 0) :=
    representation_isIrreducible_of_transitive_nonzero
      (agemoSuccQuotientRepresentation hcover.left.2.restrict 0) htransA0
  obtain ⟨EA, hEA⟩ :=
    exists_agemoZero_linearEquiv_succ_of_irreducible
      hcover.left.2.restrict s hirrA0
  have hE2symm : ∀ g q,
      E2.symm (agemoSuccQuotientRepresentation
        hcover.left.2.restrict s g q) =
        lowerCentralLayerRepresentation hcover.right.2.restrict 1 g
          (E2.symm q) := by
    intro g q
    apply E2.injective
    rw [E2.apply_symm_apply, hE2, E2.apply_symm_apply]
  let E : Additive (lowerCentralLayer C 0) ≃ₗ[ZMod 2]
      Additive (lowerCentralLayer C 1) :=
    E0.trans (EA.trans E2.symm)
  have hE : ∀ g v,
      E (lowerCentralLayerRepresentation hcover.right.2.restrict 0 g v) =
        lowerCentralLayerRepresentation hcover.right.2.restrict 1 g (E v) := by
    intro g v
    change E2.symm (EA (E0
      (lowerCentralLayerRepresentation hcover.right.2.restrict 0 g v))) =
        lowerCentralLayerRepresentation hcover.right.2.restrict 1 g
          (E2.symm (EA (E0 v)))
    rw [hE0, hEA, hE2symm]
  exact (not_exists_equivariant_linearEquiv_of_higman_bracket_of_transitive
    (lowerCentralLayerRepresentation hcover.right.2.restrict 0)
    (lowerCentralLayerRepresentation hcover.right.2.restrict 1)
    (Module.finrank (ZMod 2) (Additive (lowerCentralLayer C 1)))
    hfinrank rfl (lowerCentralCommutatorBilinear C)
    (fun g a b => by
      simpa only [← lowerCentralLayerRepresentation_apply, ofMul_toMul] using
        lowerCentralCommutatorBilinear_equivariant
          hcover.right.2.restrict g a b)
    (lowerCentralCommutatorBilinear_self C)
    (lowerCentralCommutatorBilinear_span_eq_top C)
    htrans2) ⟨E, hE⟩

/-- **Higman, Suzuki 2-groups, Lemma 7 (p. 86), source-strength form.**

The cyclic actor is assumed only transitive on the involutions, as in
Higman's definition.  Faithfulness of its restriction to `C` is not needed:
the spectral contradiction passes to the effective image of the induced
first-layer representation. -/
theorem higmanLemmaSeven_isMulCommutative_of_transitive
    {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (X : Subgroup (MulAut P))
    (hXcyc : IsCyclic X)
    (htrans : ActsTransitivelyOnInvolutions X)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (A C : Subgroup P)
    (hcover : NormalInvariantCover X.subtype A C)
    (hAcomm : IsMulCommutative A)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    IsMulCommutative C := by
  rcases eq_or_ne A ⊥ with hAbot | hAne
  · have hmap_le : (_root_.commutator C).map C.subtype ≤ A :=
      hderived.trans (Subgroup.map_subtype_le _)
    rw [hAbot] at hmap_le
    have hmap_bot : (_root_.commutator C).map C.subtype = ⊥ :=
      le_bot_iff.mp hmap_le
    have hcomm_bot : _root_.commutator C = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (_root_.commutator C) C.subtype_injective).mp hmap_bot
    exact (commutator_eq_bot_iff C).mp hcomm_bot
  · letI : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := hAcomm.is_comm.comm }
    let E0 : Additive (lowerCentralLayer C 0) ≃ₗ[ZMod 2]
        Additive (AgemoSuccQuotient A 0) :=
      lowerCentralLayerZeroToAgemoZeroLinearEquiv
        hP hcover hAcomm hAne hPhi hderived
    exact higmanLemmaSeven_isMulCommutative_of_overlap
      hP X hXcyc htrans hmulti A C hcover hAcomm hPhi hderived E0
      (lowerCentralLayerZeroToAgemoZeroLinearEquiv_equivariant
        hP hcover hAcomm hAne hPhi hderived)

/-- Higman, Suzuki 2-groups, Lemma 7 (p. 86).

For a normal invariant cover whose lower member is abelian and equals the
Frattini subgroup of the upper member, the hypothesis C' ≤ A² forces C to
be abelian.  The equivariant overlap used in Higman's spectral argument is
constructed internally by the square map above. -/
theorem higmanLemmaSeven_isMulCommutative
    {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (X : Subgroup (MulAut P))
    (hXcyc : IsCyclic X)
    (hreg : ActsRegularlyOnInvolutions X)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (A C : Subgroup P)
    (hcover : NormalInvariantCover X.subtype A C)
    (hAcomm : IsMulCommutative A)
    (hPhi : NormalInvariantCover.ambientFrattini C = A)
    (hderived : (_root_.commutator C).map C.subtype ≤
      (Agemo A 2 1).map A.subtype) :
    IsMulCommutative C :=
  higmanLemmaSeven_isMulCommutative_of_transitive
    hP X hXcyc hreg.transitive hmulti A C hcover hAcomm hPhi hderived

end OddOrder.Higman.Suzuki2Groups
