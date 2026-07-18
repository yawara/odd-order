/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FixedPointCentralizer

/-!
# Peterfalvi Part II, Ch. I §3: Proposition 1(a)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, pp. 105–106.

For a subgroup `1 ≠ X ≤ V`, Proposition 1(a) starts the induction on
centralizers by putting `L = C_G(X)` and letting `L` act on the fixed-point
set `Ω_X`.  Peterfalvi observes that the three points `H`, `H^t`, and
`H^{ts}` lie in `Ω_X`, then invokes Ch. I §1 Proposition 6 to conclude that
this action satisfies hypothesis (A1).

This file formalizes Proposition 1(a).  It constructs the induced action of
`C_G(X)` on `Ω_X`, proves the three-point lower bound, bundles double
transitivity, and packages every part of the source hypothesis (A1): the
point stabilizer, the decomposition `H = Q ⋊ D`, the distinguished
involution `t`, and the parity conditions.  It then identifies `𝒩(L)` both
as the restricted-action kernel and as the intrinsic normal core of
`C_H(X)` in `L = C_G(X)`, proves `𝒩(L) = C_{C_D(X)}(C_Q(X))`, and proves
`𝒩(L) ≤ C_V(X)`.  Faithfulness (A2) and the 2-rank condition (A3) are not
assumed for the restricted action.

Peterfalvi writes actions on the right.  Thus the book's point `H^{ts}` is
represented by `s • (t • basept)` in Lean's left-action convention, where
`s` is the distinguished involution of `Q`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open MulAction
open scoped Pointwise

section /- §3, Proposition 1(a): the induced fixed-point action (pp. 105–106) -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(a)**, induced-action carrier:
the fixed points of `X` are stable under the restricted action of `C_G(X)`. -/
def fixedPointsCentralizerSubMulAction (X : Subgroup G) :
    SubMulAction ↥(Subgroup.centralizer (X : Set G)) Ω where
  carrier := fixedPoints X Ω
  smul_mem' := by
    intro c ω hω
    rw [mem_fixedPoints] at hω ⊢
    intro x
    have hxc : (x : G) * (c : G) = (c : G) * (x : G) :=
      Subgroup.mem_centralizer_iff.mp c.2 x x.2
    calc
      (x : G) • (c : G) • ω = ((x : G) * (c : G)) • ω := (mul_smul _ _ _).symm
      _ = ((c : G) * (x : G)) • ω := by rw [hxc]
      _ = (c : G) • (x : G) • ω := mul_smul _ _ _
      _ = (c : G) • ω := by
        rw [show (x : G) • ω = ω by simpa only [Subgroup.smul_def] using hω x]

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(a)**, induced action of `C_G(X)`
on the fixed-point set `Ω_X`. -/
instance (X : Subgroup G) :
    MulAction ↥(Subgroup.centralizer (X : Set G)) ↥(fixedPoints X Ω) :=
  inferInstanceAs
    (MulAction ↥(Subgroup.centralizer (X : Set G))
      ↥(fixedPointsCentralizerSubMulAction X))

/-- **Peterfalvi Theorem A, hypothesis (A1)**, in the form used by Part II,
Ch. I §3 Prop 1(a).  This carrier deliberately excludes faithfulness (A2)
and the 2-rank assumption (A3). -/
structure HypothesisA1 (L Λ : Type*) [Group L] [MulAction L Λ] [Finite L] where
  /-- The distinguished point whose stabilizer is `H`. -/
  basept : Λ
  /-- The action is doubly transitive. -/
  doubly_transitive : IsMultiplyPretransitive L Λ 2
  /-- The stabilizer of `basept`. -/
  H : Subgroup L
  /-- The regular normal subgroup in the point stabilizer. -/
  Q : Subgroup L
  /-- The two-point stabilizer and complement to `Q` in `H`. -/
  D : Subgroup L
  /-- `H` is the stabilizer of `basept`. -/
  H_def : H = stabilizer L basept
  /-- The distinguished involution outside `H`. -/
  t : L
  /-- `t` is an involution. -/
  t_sq : t ^ 2 = 1
  /-- `t` is nontrivial. -/
  t_ne_one : t ≠ 1
  /-- `t` lies outside the point stabilizer. -/
  t_not_mem_H : t ∉ H
  /-- `D = H ∩ H^t`. -/
  D_def : D = H ⊓ H.map (MulAut.conj t).toMonoidHom
  /-- `Q ≤ H`. -/
  Q_le_H : Q ≤ H
  /-- `Q` is normal in `H`, in ambient conjugation form. -/
  Q_normal_in_H : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q
  /-- The internal factors have trivial intersection. -/
  Q_inf_D_eq_bot : Q ⊓ D = ⊥
  /-- `H = QD`. -/
  Q_mul_D_eq_H : (Q : Set L) * (D : Set L) = (H : Set L)
  /-- `Q` has even order. -/
  Q_even : Even (Nat.card Q)
  /-- `D` has odd order. -/
  D_odd : Odd (Nat.card D)

/-- Kernel/core lemma used in **Peterfalvi Part II, Ch. I §3 Prop 1(a)**:
for a transitive action, the normal core of a point stabilizer is exactly
the kernel of the permutation action. -/
theorem normalCore_stabilizer_eq_ker_of_isPretransitive
    {A Λ : Type*} [Group A] [MulAction A Λ] (b : Λ)
    (htrans : IsPretransitive A Λ) :
    (stabilizer A b).normalCore = (toPermHom A Λ).ker := by
  ext n
  constructor
  · intro hn
    rw [MonoidHom.mem_ker]
    apply Equiv.Perm.ext
    intro ω
    change n • ω = ω
    obtain ⟨g, hg⟩ := (isPretransitive_iff A Λ).mp htrans b ω
    have hconj : g⁻¹ * n * g ∈ stabilizer A b := by
      simpa using hn g⁻¹
    have hconjfix : (g⁻¹ * n * g) • b = b :=
      mem_stabilizer_iff.mp hconj
    calc
      n • ω = n • (g • b) := by rw [hg]
      _ = (n * g) • b := (mul_smul _ _ _).symm
      _ = (g * (g⁻¹ * n * g)) • b := by
        congr 1
        group
      _ = g • ((g⁻¹ * n * g) • b) := mul_smul _ _ _
      _ = g • b := by rw [hconjfix]
      _ = ω := hg
  · intro hn
    rw [MonoidHom.mem_ker] at hn
    intro g
    rw [mem_stabilizer_iff]
    have hfix : n • (g⁻¹ • b) = g⁻¹ • b := by
      have happ := congrArg (fun p : Equiv.Perm Λ => p (g⁻¹ • b)) hn
      simpa using happ
    calc
      (g * n * g⁻¹) • b = g • (n • (g⁻¹ • b)) := by
        rw [mul_smul, mul_smul]
      _ = g • (g⁻¹ • b) := by rw [hfix]
      _ = b := smul_inv_smul _ _

end

namespace Hypothesis

section /- §3, Proposition 1(a): three fixed points and (A1) (pp. 105–106) -/

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {X : Subgroup G}

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(a)** — if `X ≤ V`, then the
three points corresponding to `H`, `H^t`, and `H^{ts}` are fixed by `X`.
Consequently `|Ω_X| ≥ 3`.  The proposition's assumption `X ≠ 1` is not
needed for this fixed-point bound. -/
lemma three_le_ncard_fixedPoints_of_le_V (hXV : X ≤ hyp.V) :
    3 ≤ (fixedPoints X Ω).ncard := by
  classical
  letI : Finite Ω := hyp.finite_Omega
  let s : G := hyp.distinguishedInvolution
  have hsH : s ∈ hyp.H := hyp.distinguishedInvolution_mem_H
  have hs2 : s ^ 2 = 1 := hyp.distinguishedInvolution_sq
  have hs1 : s ≠ 1 := hyp.distinguishedInvolution_ne_one
  have hsQ : s ∈ hyp.Q := hyp.mem_Q_of_sq_eq_one_of_mem_H hsH hs2
  have hXD : X ≤ hyp.D := hXV.trans hyp.V_le_D
  have hb : hyp.basept ∈ fixedPoints X Ω := hyp.basept_mem_fixedPoints hXD
  have ht : hyp.t • hyp.basept ∈ fixedPoints X Ω :=
    hyp.t_smul_basept_mem_fixedPoints hXD
  have hsCX : s ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxs : s * x = x * s :=
      Subgroup.mem_centralizer_iff.mp
        (hyp.V_le_centralizer_distinguishedInvolution (hXV hx)).2 s (Set.mem_singleton s)
    exact hxs.symm
  have hst : s • (hyp.t • hyp.basept) ∈ fixedPoints X Ω :=
    smul_mem_fixedPoints_of_mem_centralizer hsCX ht
  have htb : hyp.t • hyp.basept ≠ hyp.basept :=
    hyp.smul_basept_ne_of_not_mem_H hyp.t_not_mem_H
  have hstb : s • (hyp.t • hyp.basept) ≠ hyp.basept :=
    hyp.Q_smul_t_basept_ne hsQ
  have hstt : s • (hyp.t • hyp.basept) ≠ hyp.t • hyp.basept := by
    intro heq
    have heq' :
        hyp.qRegularEquiv ⟨s, hsQ⟩ = hyp.qRegularEquiv (1 : hyp.Q) := by
      apply Subtype.ext
      change s • (hyp.t • hyp.basept) = (1 : G) • (hyp.t • hyp.basept)
      simpa using heq
    have hsub : (⟨s, hsQ⟩ : hyp.Q) = 1 := hyp.qRegularEquiv.injective heq'
    exact hs1 (congrArg Subtype.val hsub)
  have hsub :
      ({hyp.basept, hyp.t • hyp.basept, s • (hyp.t • hyp.basept)} : Set Ω) ⊆
        fixedPoints X Ω := by
    intro ω hω
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hω
    rcases hω with rfl | rfl | rfl
    · exact hb
    · exact ht
    · exact hst
  calc
    3 = ({hyp.basept, hyp.t • hyp.basept,
        s • (hyp.t • hyp.basept)} : Set Ω).ncard := by
      have hbnot : hyp.basept ∉
          ({hyp.t • hyp.basept, s • (hyp.t • hyp.basept)} : Set Ω) := by
        simp [htb.symm, hstb.symm]
      have htnot : hyp.t • hyp.basept ∉
          ({s • (hyp.t • hyp.basept)} : Set Ω) := by
        simpa using hstt.symm
      rw [Set.ncard_insert_of_notMem hbnot,
        Set.ncard_insert_of_notMem htnot, Set.ncard_singleton]
    _ ≤ (fixedPoints X Ω).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(a)** — the induced action of
`C_G(X)` on `Ω_X` is doubly transitive. -/
theorem centralizer_isMultiplyPretransitive_two (hXV : X ≤ hyp.V) :
    IsMultiplyPretransitive ↥(Subgroup.centralizer (X : Set G))
      ↥(fixedPoints X Ω) 2 := by
  rw [is_two_pretransitive_iff]
  intro a b c d hab hcd
  have hXD : X ≤ hyp.D := hXV.trans hyp.V_le_D
  have h3 : 3 ≤ (fixedPoints X Ω).ncard :=
    three_le_ncard_fixedPoints_of_le_V hyp hXV
  have hab' : (a : Ω) ≠ (b : Ω) := fun h => hab (Subtype.ext h)
  have hcd' : (c : Ω) ≠ (d : Ω) := fun h => hcd (Subtype.ext h)
  obtain ⟨g, hg, hga, hgb⟩ := hyp.exists_mem_centralizer_smul_pair hXD h3
    a.2 b.2 c.2 d.2 hab' hcd'
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · exact Subtype.ext hga
  · exact Subtype.ext hgb

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(a)** — the centralizer
`L = C_G(X)`, acting on `Ω_X`, satisfies the complete source hypothesis
(A1).  Its structural subgroups are `C_H(X)`, `C_Q(X)`, and `C_D(X)`,
represented internally by `subgroupOf`; the same `t` is the distinguished
involution. -/
noncomputable def centralizerHypothesisA1 (hXV : X ≤ hyp.V) :
    HypothesisA1 ↥(Subgroup.centralizer (X : Set G)) ↥(fixedPoints X Ω) := by
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  have hXD : X ≤ hyp.D := hXV.trans hyp.V_le_D
  have hb : hyp.basept ∈ fixedPoints X Ω := hyp.basept_mem_fixedPoints hXD
  have h3 : 3 ≤ (fixedPoints X Ω).ncard :=
    three_le_ncard_fixedPoints_of_le_V hyp hXV
  have htC : hyp.t ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hyp.commute_t_of_mem_V (hXV hx)).eq
  let tC : C := ⟨hyp.t, htC⟩
  let bX : ↥(fixedPoints X Ω) := ⟨hyp.basept, hb⟩
  refine
    { basept := bX
      doubly_transitive := centralizer_isMultiplyPretransitive_two hyp hXV
      H := hyp.H.subgroupOf C
      Q := hyp.Q.subgroupOf C
      D := hyp.D.subgroupOf C
      H_def := ?_
      t := tC
      t_sq := ?_
      t_ne_one := ?_
      t_not_mem_H := ?_
      D_def := ?_
      Q_le_H := ?_
      Q_normal_in_H := ?_
      Q_inf_D_eq_bot := ?_
      Q_mul_D_eq_H := ?_
      Q_even := ?_
      D_odd := ?_ }
  · ext c
    change (c : G) ∈ hyp.H ↔ c • bX = bX
    rw [hyp.H_def, mem_stabilizer_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · exact Subtype.ext hyp.t_sq
  · intro h
    exact hyp.t_ne_one (congrArg Subtype.val h)
  · intro h
    exact hyp.t_not_mem_H h
  · ext c
    rw [Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    change (c : G) ∈ hyp.D ↔
      (c : G) ∈ hyp.H ∧ hyp.t⁻¹ * (c : G) * hyp.t ∈ hyp.H
    exact hyp.mem_D_iff
  · intro q hq
    exact hyp.Q_le_H hq
  · intro h hh q hq
    exact hyp.Q_normal_in_H (h : G) hh (q : G) hq
  · rw [eq_bot_iff]
    intro c hc
    rw [Subgroup.mem_bot]
    have hc' : (c : G) ∈ hyp.Q ⊓ hyp.D := ⟨hc.1, hc.2⟩
    rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hc'
    exact Subtype.ext hc'
  · apply Set.Subset.antisymm
    · rintro y ⟨q, hq, d, hd, rfl⟩
      change (q : G) * (d : G) ∈ hyp.H
      exact hyp.H.mul_mem (hyp.Q_le_H hq) (hyp.D_le_H hd)
    · intro y hy
      have hy' : (y : G) ∈ hyp.H ⊓ C := ⟨hy, y.2⟩
      have hprod : (y : G) ∈
          ((hyp.Q ⊓ C : Subgroup G) : Set G) *
            ((hyp.D ⊓ C : Subgroup G) : Set G) := by
        rw [hyp.cQ_mul_cD_eq_cH hXD]
        exact hy'
      obtain ⟨q, hq, d, hd, hqd⟩ := hprod
      refine ⟨⟨q, hq.2⟩, hq.1, ⟨d, hd.2⟩, hd.1, ?_⟩
      exact Subtype.ext hqd
  · have hcard : Nat.card ↥(hyp.Q.subgroupOf C) =
        Nat.card ↥(hyp.Q ⊓ C) := by
      rw [← Subgroup.inf_subgroupOf_right hyp.Q C]
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (K := C) inf_le_right).toEquiv
    rw [hcard]
    exact hyp.even_card_cQ hXD h3
  · have hcard : Nat.card ↥(hyp.D.subgroupOf C) =
        Nat.card ↥(hyp.D ⊓ C) := by
      rw [← Subgroup.inf_subgroupOf_right hyp.D C]
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (K := C) inf_le_right).toEquiv
    rw [hcard]
    exact hyp.D_odd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(a)** — for `L = C_G(X)` acting
on `Ω_X`, the book's `𝒩(L)` is simultaneously the normal core of
`C_H(X)` in `L` and the kernel of the restricted permutation action.
The source assumption `X ≠ 1` is not needed for this identity. -/
theorem normalCore_cH_eq_restrictedAction_ker (hXV : X ≤ hyp.V) :
    let C : Subgroup G := Subgroup.centralizer (X : Set G)
    (hyp.H.subgroupOf C).normalCore =
      (MulAction.toPermHom C ↥(fixedPoints X Ω)).ker := by
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  have hXD : X ≤ hyp.D := hXV.trans hyp.V_le_D
  have h3 : 3 ≤ (fixedPoints X Ω).ncard :=
    three_le_ncard_fixedPoints_of_le_V hyp hXV
  change (hyp.H.subgroupOf C).normalCore =
    (MulAction.toPermHom C ↥(fixedPoints X Ω)).ker
  letI : IsMultiplyPretransitive C ↥(fixedPoints X Ω) 2 :=
    centralizer_isMultiplyPretransitive_two hyp hXV
  have hpre : IsPretransitive C ↥(fixedPoints X Ω) :=
    isPretransitive_of_is_two_pretransitive
  have hstab :
      MulAction.stabilizer C
          (⟨hyp.basept, hyp.basept_mem_fixedPoints hXD⟩ : fixedPoints X Ω) =
        hyp.H.subgroupOf C := by
    let bX : ↥(fixedPoints X Ω) :=
      ⟨hyp.basept, hyp.basept_mem_fixedPoints hXD⟩
    ext c
    change c • bX = bX ↔ (c : G) ∈ hyp.H
    rw [hyp.H_def, mem_stabilizer_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [← hstab]
  exact normalCore_stabilizer_eq_ker_of_isPretransitive
    (⟨hyp.basept, hyp.basept_mem_fixedPoints hXD⟩ : fixedPoints X Ω) hpre

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(a)** — for `L = C_G(X)`,
`H_L = C_H(X)`, `Q_L = C_Q(X)`, and `D_L = C_D(X)`, the source identity
`𝒩(L) = C_{D_L}(Q_L)`.  The normal core is taken intrinsically in `L`.
The source assumption `X ≠ 1` is not needed for this identity. -/
theorem normalCore_cH_eq_centralizer_cQ (hXV : X ≤ hyp.V) :
    let L : Subgroup G := Subgroup.centralizer (X : Set G)
    let H_L : Subgroup L := hyp.H.subgroupOf L
    let Q_L : Subgroup L := hyp.Q.subgroupOf L
    let D_L : Subgroup L := hyp.D.subgroupOf L
    H_L.normalCore = D_L ⊓ Subgroup.centralizer (Q_L : Set L) := by
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let H_L : Subgroup L := hyp.H.subgroupOf L
  let Q_L : Subgroup L := hyp.Q.subgroupOf L
  let D_L : Subgroup L := hyp.D.subgroupOf L
  change H_L.normalCore = D_L ⊓ Subgroup.centralizer (Q_L : Set L)
  have hXD : X ≤ hyp.D := hXV.trans hyp.V_le_D
  have h3 : 3 ≤ (fixedPoints X Ω).ncard :=
    three_le_ncard_fixedPoints_of_le_V hyp hXV
  have core_fixes : ∀ n : L, n ∈ H_L.normalCore →
      ∀ ω : Ω, ω ∈ fixedPoints X Ω → (n : G) • ω = ω := by
    intro n hn ω hω
    obtain ⟨c, hcL, hcω⟩ := hyp.exists_mem_centralizer_smul_eq hXD h3
      (hyp.basept_mem_fixedPoints hXD) hω
    let cL : L := ⟨c, hcL⟩
    have hconj : cL⁻¹ * n * cL ∈ H_L := by
      simpa using hn cL⁻¹
    have hfix : ((cL⁻¹ * n * cL : L) : G) • hyp.basept = hyp.basept :=
      hyp.smul_basept_eq_of_mem_H hconj
    calc
      (n : G) • ω = (n : G) • ((cL : G) • hyp.basept) := by rw [hcω]
      _ = ((n : G) * (cL : G)) • hyp.basept := (mul_smul _ _ _).symm
      _ = ((cL : G) * ((cL⁻¹ * n * cL : L) : G)) • hyp.basept := by
        apply congrArg (fun g : G => g • hyp.basept)
        change (n : G) * (cL : G) =
          (cL : G) * ((cL : G)⁻¹ * (n : G) * (cL : G))
        group
      _ = (cL : G) • (((cL⁻¹ * n * cL : L) : G) • hyp.basept) :=
        mul_smul _ _ _
      _ = (cL : G) • hyp.basept := by rw [hfix]
      _ = ω := hcω
  apply le_antisymm
  · intro n hn
    have hnH : (n : G) ∈ hyp.H := H_L.normalCore_le hn
    have hnfixb : (n : G) • hyp.basept = hyp.basept :=
      hyp.smul_basept_eq_of_mem_H hnH
    have hnfixt : (n : G) • (hyp.t • hyp.basept) = hyp.t • hyp.basept :=
      core_fixes n hn _ (hyp.t_smul_basept_mem_fixedPoints hXD)
    have hnD : (n : G) ∈ hyp.D := by
      rw [hyp.D_eq_stabilizer_inf]
      exact Subgroup.mem_inf.mpr
        ⟨MulAction.mem_stabilizer_iff.mpr hnfixb,
          MulAction.mem_stabilizer_iff.mpr hnfixt⟩
    refine Subgroup.mem_inf.mpr ⟨hnD, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqQ : (q : G) ∈ hyp.Q := hq
    have hnH' : (n : G) ∈ hyp.H := hyp.D_le_H hnD
    have hconjQ : (n : G) * (q : G) * (n : G)⁻¹ ∈ hyp.Q :=
      hyp.Q_normal_in_H n hnH' q hqQ
    have hninvt : (n : G)⁻¹ • (hyp.t • hyp.basept) =
        hyp.t • hyp.basept := by
      calc
        (n : G)⁻¹ • (hyp.t • hyp.basept) =
            (n : G)⁻¹ • ((n : G) • (hyp.t • hyp.basept)) := by rw [hnfixt]
        _ = hyp.t • hyp.basept := inv_smul_smul _ _
    have hqtfix : (q : G) • (hyp.t • hyp.basept) ∈ fixedPoints X Ω :=
      smul_mem_fixedPoints_of_mem_centralizer q.2
        (hyp.t_smul_basept_mem_fixedPoints hXD)
    have hnqfix : (n : G) • ((q : G) • (hyp.t • hyp.basept)) =
        (q : G) • (hyp.t • hyp.basept) := core_fixes n hn _ hqtfix
    have hsmul : ((n : G) * (q : G) * (n : G)⁻¹) •
        (hyp.t • hyp.basept) = (q : G) • (hyp.t • hyp.basept) := by
      rw [mul_smul, mul_smul, hninvt, hnqfix]
    have himg :
        hyp.qRegularEquiv
            (⟨(n : G) * (q : G) * (n : G)⁻¹, hconjQ⟩ : hyp.Q) =
          hyp.qRegularEquiv (⟨(q : G), hqQ⟩ : hyp.Q) :=
      Subtype.ext hsmul
    have heq : (n : G) * (q : G) * (n : G)⁻¹ = (q : G) :=
      congrArg Subtype.val (hyp.qRegularEquiv.injective himg)
    apply Subtype.ext
    change (q : G) * (n : G) = (n : G) * (q : G)
    calc
      (q : G) * (n : G) =
          ((n : G) * (q : G) * (n : G)⁻¹) * (n : G) := by rw [heq]
      _ = (n : G) * (q : G) := by group
  · intro d hd
    obtain ⟨hdD, hdC⟩ := Subgroup.mem_inf.mp hd
    have hdfix : ∀ ω : Ω, ω ∈ fixedPoints X Ω → (d : G) • ω = ω := by
      intro ω hω
      by_cases hωb : ω = hyp.basept
      · rw [hωb]
        exact hyp.smul_basept_eq_of_mem_H (hyp.D_le_H hdD)
      · obtain ⟨q, hq⟩ := (hyp.cQRegularEquiv hXD).surjective ⟨ω, hω, hωb⟩
        have hqval : (q : G) • (hyp.t • hyp.basept) = ω :=
          congrArg Subtype.val hq
        let qL : L := ⟨(q : G), q.2.2⟩
        have hqQL : qL ∈ Q_L := q.2.1
        have hcommL : (qL : L) * d = d * qL :=
          Subgroup.mem_centralizer_iff.mp hdC qL hqQL
        have hcomm : (q : G) * (d : G) = (d : G) * (q : G) :=
          congrArg Subtype.val hcommL
        calc
          (d : G) • ω = (d : G) • ((q : G) • (hyp.t • hyp.basept)) := by rw [hqval]
          _ = ((d : G) * (q : G)) • (hyp.t • hyp.basept) :=
            (mul_smul _ _ _).symm
          _ = ((q : G) * (d : G)) • (hyp.t • hyp.basept) := by rw [hcomm]
          _ = (q : G) • ((d : G) • (hyp.t • hyp.basept)) := mul_smul _ _ _
          _ = (q : G) • (hyp.t • hyp.basept) := congrArg ((q : G) • ·)
            (hyp.smul_t_basept_eq_of_mem_D hdD)
          _ = ω := hqval
    intro l
    have hlinvfix : ((l : G)⁻¹ • hyp.basept) ∈ fixedPoints X Ω := by
      exact smul_mem_fixedPoints_of_mem_centralizer (inv_mem l.2)
        (hyp.basept_mem_fixedPoints hXD)
    have hfix := hdfix _ hlinvfix
    have hstab : ((l * d * l⁻¹ : L) : G) • hyp.basept = hyp.basept := by
      calc
        ((l * d * l⁻¹ : L) : G) • hyp.basept =
            (l : G) • ((d : G) • ((l : G)⁻¹ • hyp.basept)) := by
              rw [← mul_smul, ← mul_smul]
              rfl
        _ = (l : G) • ((l : G)⁻¹ • hyp.basept) := by rw [hfix]
        _ = hyp.basept := smul_inv_smul _ _
    change ((l * d * l⁻¹ : L) : G) ∈ hyp.H
    rw [hyp.H_def]
    exact MulAction.mem_stabilizer_iff.mpr hstab

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(a)** — with `L = C_G(X)`,
the normal core `𝒩(L)` lies in `C_V(X) = L ∩ V`.  Using Ch. I §1 Prop 5,
`V = C_D(s)` for the distinguished involution `s`; since `s ∈ L ∩ Q`,
the preceding centralizer formula gives the inclusion. -/
theorem normalCore_cH_le_cV (hXV : X ≤ hyp.V) :
    let L : Subgroup G := Subgroup.centralizer (X : Set G)
    let H_L : Subgroup L := hyp.H.subgroupOf L
    let V_L : Subgroup L := hyp.V.subgroupOf L
    H_L.normalCore ≤ V_L := by
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let H_L : Subgroup L := hyp.H.subgroupOf L
  let Q_L : Subgroup L := hyp.Q.subgroupOf L
  let D_L : Subgroup L := hyp.D.subgroupOf L
  let V_L : Subgroup L := hyp.V.subgroupOf L
  change H_L.normalCore ≤ V_L
  have heq : H_L.normalCore = D_L ⊓ Subgroup.centralizer (Q_L : Set L) :=
    hyp.normalCore_cH_eq_centralizer_cQ hXV
  intro n hn
  rw [heq] at hn
  obtain ⟨hnD, hnC⟩ := Subgroup.mem_inf.mp hn
  have hsQ : hyp.distinguishedInvolution ∈ hyp.Q :=
    hyp.mem_Q_of_sq_eq_one_of_mem_H hyp.distinguishedInvolution_mem_H
      hyp.distinguishedInvolution_sq
  have hsL : hyp.distinguishedInvolution ∈ L := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxV := hXV hx
    have hxc : Commute x hyp.distinguishedInvolution :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.mem_inf.mp (hyp.V_eq_centralizer_distinguishedInvolution ▸ hxV)).2
    exact hxc.eq
  let sL : L := ⟨hyp.distinguishedInvolution, hsL⟩
  have hsQL : sL ∈ Q_L := hsQ
  have hscomm : (sL : L) * n = n * sL :=
    Subgroup.mem_centralizer_iff.mp hnC sL hsQL
  change (n : G) ∈ hyp.V
  rw [hyp.V_eq_centralizer_distinguishedInvolution]
  refine Subgroup.mem_inf.mpr ⟨hnD, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val hscomm.symm

end

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
