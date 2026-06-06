/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.Isaacs.Ch02_Subnormality.Main
import OddOrder.BG.Ch1_Preliminary.S03b_Lemma33
import OddOrder.GroupTheory.RepresentationTheory.ElementaryAbelianRepresentation
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusActionTI
import OddOrder.GroupTheory.ChiefFactor
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# BG §3D: toward Theorem 3.7 (Frobenius kernel nilpotency)

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_, Ch. I §3D,
mmd `references/bg/local-analysis.mmd` L1199-1219. plan = `notes/bg/s03_thm37_plan.md`.

Thm 3.7 の chief-factor 解析の **same-prime case** をここで証明する (group-theoretic,
BG の「K̄ ⊆ O_q(Ḡ) acts trivially」を回避): 有限群の正規 `q`-部分群 `K` は、任意の
minimal-normal `q`-部分群 `V` を中心化する。`q`-群 `K ⊔ V` 内で非自明正規部分群 `V` が
中心と交わること (`exists_mem_center_of_normal_ne_bot`) を使う。
-/

namespace OddOrder.BG.Ch1.S03c

open scoped Pointwise

variable {H : Type*} [Group H] [Finite H]

/-- **Same-prime case** of BG Thm 3.7's chief-factor analysis: a normal `q`-subgroup `K` of a
finite group `H` centralizes every minimal-normal `q`-subgroup `V`.

Proof: `K ⊔ V` is a `q`-group in which `V` is a nontrivial normal subgroup, so `V` meets the
center (`exists_mem_center_of_normal_ne_bot`), giving a nonidentity element of `V` that
centralizes `K`. Thus `V ⊓ C_H(K)` is a nonzero normal subgroup `≤ V`, hence `= V` by
minimality, i.e. `V ≤ C_H(K)`, i.e. `⁅K, V⁆ = ⊥`. -/
theorem commutator_eq_bot_of_normal_pgroup_minimalNormal {q : ℕ} [Fact q.Prime]
    {K V : Subgroup H} [K.Normal] (hK : IsPGroup q K) (hV : IsPGroup q V)
    (hVmin : OddOrder.Isaacs.Ch02.IsMinimalNormal V) :
    ⁅K, V⁆ = ⊥ := by
  haveI hVnorm : V.Normal := hVmin.1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← Subgroup.le_centralizer_iff]
  -- goal: `V ≤ centralizer K`
  haveI : (Subgroup.centralizer (K : Set H)).Normal := Subgroup.normal_centralizer
  have hCne : V ⊓ Subgroup.centralizer (K : Set H) ≠ ⊥ := by
    have hKV : IsPGroup q (K ⊔ V : Subgroup H) := hK.to_sup_of_normal_left hV
    haveI : (V.subgroupOf (K ⊔ V)).Normal := Subgroup.normal_subgroupOf
    have hV'ne : V.subgroupOf (K ⊔ V) ≠ ⊥ := by
      rw [Ne, Subgroup.subgroupOf_eq_bot]
      exact fun hdisj => hVmin.2.1 (hdisj.eq_bot_of_le le_sup_right)
    obtain ⟨x, hxV', hxZ, hxne⟩ :=
      OddOrder.GroupTheory.exists_mem_center_of_normal_ne_bot hKV hV'ne
    refine fun hbot => hxne ?_
    have hxV : (x : H) ∈ V := Subgroup.mem_subgroupOf.mp hxV'
    have hxC : (x : H) ∈ Subgroup.centralizer (K : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hc := Subgroup.mem_center_iff.mp hxZ ⟨k, Subgroup.mem_sup_left hk⟩
      have := congrArg (Subgroup.subtype (K ⊔ V)) hc
      simpa using this
    have hxmem : (x : H) ∈ V ⊓ Subgroup.centralizer (K : Set H) := ⟨hxV, hxC⟩
    rw [hbot, Subgroup.mem_bot] at hxmem
    exact Subtype.ext hxmem
  haveI hCnorm : (V ⊓ Subgroup.centralizer (K : Set H)).Normal := inferInstance
  rcases hVmin.2.2 (V ⊓ Subgroup.centralizer (K : Set H)) hCnorm inf_le_left with h | h
  · exact absurd h hCne
  · rw [← h]; exact inf_le_right

/-- **Coprime case** of BG Thm 3.7's chief-factor analysis (via BG Lemma 3.3): let `G = KR` be a
Frobenius group whose kernel order `|K|` is coprime to a prime `s` (`s ∤ |K|`), and let `M` be a
commutative group with a `MulDistribMulAction` of `G` whose additive form `Additive M` is a
`ZMod s`-module (the intended case is an elementary abelian `s`-group via
`IsElementaryAbelian.zmodModule`). If `R` acts fixed-point-freely on `M` (`C_M(R) = 1`), then `K`
acts trivially on `M`.

View `M` additively as the `ZMod s`-representation `Representation.ofDistribMulAction` (the bridge
instances supply `DistribMulAction G (Additive M)` and `SMulCommClass`), and apply the
contrapositive of Lemma 3.3 (`S03b.kernel_acts_trivially_of_centralizer_eq_bot`). -/
theorem kernel_acts_trivially_of_coprime_fixedPointFree {s : ℕ} [Fact s.Prime]
    {G M : Type*} [Finite G] [Group G] [CommGroup M] [MulDistribMulAction G M]
    [Module (ZMod s) (Additive M)]
    {K R : Subgroup G} (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G K R)
    (hchar : ¬ s ∣ Nat.card K)
    (hFPF : ∀ m : M, (∀ r : R, (r : G) • m = m) → m = 1) :
    ∀ (k : K) (m : M), (k : G) • m = m := by
  set ρ : Representation (ZMod s) G (Additive M) :=
    Representation.ofDistribMulAction (ZMod s) G (Additive M) with hρ
  have hρ_apply : ∀ (g : G) (a : Additive M), ρ g a = g • a := by
    intro g a; rw [hρ]; rfl
  have hchar' : (Nat.card K : ZMod s) ≠ 0 :=
    fun h => hchar ((ZMod.natCast_eq_zero_iff _ _).1 h)
  have hCR : ∀ v : Additive M, (∀ r : R, ρ (r : G) v = v) → v = 0 := by
    intro v hv
    have hfix : ∀ r : R, (r : G) • Additive.toMul v = Additive.toMul v := by
      intro r
      have h := hv r
      rw [hρ_apply] at h
      exact congrArg Additive.toMul h
    have h0 : Additive.ofMul (Additive.toMul v) = Additive.ofMul (1 : M) :=
      congrArg Additive.ofMul (hFPF _ hfix)
    simpa using h0
  have hKtriv := OddOrder.BG.Ch1.S03b.kernel_acts_trivially_of_centralizer_eq_bot
    hFrob ρ hchar' hCR
  intro k m
  have happ : ρ (k : G) (Additive.ofMul m) = Additive.ofMul m := by
    rw [hKtriv k]; rfl
  rw [hρ_apply] at happ
  exact congrArg Additive.toMul happ

/-- The conjugation action of `G` on a chief factor `X/Y` (with `X`, `Y` normal in `G`), presented
as `MulDistribMulAction G (↥X ⧸ Y.subgroupOf X)`: `G` conjugates the normal subgroup `↥X`, the
invariant subgroup `Y.subgroupOf X` is preserved (`Y` normal), and the action descends to the
quotient, then is pulled back from `ConjAct G` to `G`. This is the chief-factor action fed (after
descending through `G/L` via `mulDistribMulActionQuotientOfTrivial`) to the coprime case. -/
noncomputable def chiefFactorConjAction {G : Type*} [Group G] (X Y : Subgroup G)
    [X.Normal] [Y.Normal] :
    MulDistribMulAction G (↥X ⧸ Y.subgroupOf X) :=
  letI : MulDistribMulAction (ConjAct G) (↥X ⧸ Y.subgroupOf X) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantQuotientMulDistribMulAction
      (Y.subgroupOf X) (by
        intro a m hm
        rw [Subgroup.mem_subgroupOf] at hm ⊢
        show ConjAct.ofConjAct a * (↑m : G) * (ConjAct.ofConjAct a)⁻¹ ∈ Y
        exact (‹Y.Normal›).conj_mem _ hm _)
  MulDistribMulAction.compHom _ (ConjAct.toConjAct (G := G)).toMonoidHom

/-- Reduction of the chief-factor conjugation smul on a coset: `g` sends the class of `x ∈ X` to
the class of its `G`-conjugate. -/
theorem chiefFactorConjAction_smul_mk {G : Type*} [Group G] {X Y : Subgroup G}
    [X.Normal] [Y.Normal] (g : G) (x : ↥X) :
    letI := chiefFactorConjAction X Y
    (g • (QuotientGroup.mk x : ↥X ⧸ Y.subgroupOf X)) =
      QuotientGroup.mk (ConjAct.toConjAct g • x) :=
  rfl

open OddOrder.GroupTheory in
/-- **Model bridge**: `g` acts trivially on the chief factor `↥X ⧸ Y.subgroupOf X` via
`chiefFactorConjAction` iff `g ∈ chiefFactorCentralizer X Y`. Both sides reduce to
`∀ x ∈ X, g x g⁻¹ x⁻¹ ∈ Y` (the action side via `x ↦ x⁻¹` reindexing). -/
theorem chiefFactorConjAction_smul_eq_self_iff_mem {G : Type*} [Group G] {X Y : Subgroup G}
    [X.Normal] [Y.Normal] (g : G) :
    letI := chiefFactorConjAction X Y
    (∀ v : ↥X ⧸ Y.subgroupOf X, g • v = v) ↔ g ∈ chiefFactorCentralizer X Y := by
  letI := chiefFactorConjAction X Y
  have hcoe : ∀ x : ↥X, (↑(ConjAct.toConjAct g • x) : G) = g * ↑x * g⁻¹ := fun _ => rfl
  have hL : (∀ v : ↥X ⧸ Y.subgroupOf X, g • v = v)
      ↔ ∀ x : ↥X, (g * (↑x)⁻¹ * g⁻¹ * ↑x : G) ∈ Y := by
    constructor
    · intro h x
      have hv := h (QuotientGroup.mk x)
      rw [chiefFactorConjAction_smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf,
        Subgroup.coe_mul, Subgroup.coe_inv, hcoe] at hv
      have heq : ((g * ↑x * g⁻¹)⁻¹ * ↑x : G) = g * (↑x)⁻¹ * g⁻¹ * ↑x := by group
      rwa [heq] at hv
    · intro h v
      induction v using QuotientGroup.induction_on with
      | _ x =>
        rw [chiefFactorConjAction_smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf,
          Subgroup.coe_mul, Subgroup.coe_inv, hcoe]
        have heq : ((g * ↑x * g⁻¹)⁻¹ * ↑x : G) = g * (↑x)⁻¹ * g⁻¹ * ↑x := by group
        rw [heq]; exact h x
  have hR : g ∈ chiefFactorCentralizer X Y
      ↔ ∀ x : ↥X, (g * ↑x * g⁻¹ * (↑x)⁻¹ : G) ∈ Y := by
    rw [chiefFactorCentralizer.mem_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h x
      have hcomm := h ((QuotientGroup.mk' Y) (↑x : G)) ⟨↑x, x.2, rfl⟩
      have hgoal : (QuotientGroup.mk' Y) (g * ↑x * g⁻¹ * (↑x)⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [← hcomm]
        group
      exact (QuotientGroup.eq_one_iff _).mp hgoal
    · intro h q hq
      obtain ⟨x, hx, rfl⟩ := hq
      have hy : (QuotientGroup.mk' Y) (g * ↑x * g⁻¹ * (↑x)⁻¹) = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff _).mpr (h ⟨x, hx⟩)
      simp only [map_mul, map_inv] at hy
      rw [mul_inv_eq_one] at hy
      rw [mul_inv_eq_iff_eq_mul] at hy
      exact hy.symm
  rw [hL, hR]
  constructor
  · intro h x; have := h x⁻¹; simpa using this
  · intro h x; have := h x⁻¹; simpa using this

open OddOrder.GroupTheory in
/-- **Coprime branch of BG Thm 3.7's chief-factor analysis**: for a `G`-chief factor `X/Y` with
`X ⊆ K`, elementary abelian of prime `s` coprime to `|K/L|`, with `L ⊴ G` (the nilpotent layer from
the induction) centralizing `X/Y` and `R` acting fixed-point-freely on `X/Y`, the kernel `K`
centralizes `X/Y` (i.e. `K ≤ chiefFactorCentralizer X Y`). Assembles glue (A) + the model-bridge +
the descent helper + the coprime case (`kernel_acts_trivially_of_coprime_fixedPointFree`). -/
theorem coprime_kernel_le_chiefFactorCentralizer
    {G : Type*} [Group G] [Finite G] {K R X Y : Subgroup G}
    [X.Normal] [Y.Normal] {s : ℕ} [Fact s.Prime]
    (hVelem : IsElementaryAbelian s (↥X ⧸ Y.subgroupOf X))
    {L : Subgroup G} [L.Normal] (hLcent : L ≤ chiefFactorCentralizer X Y)
    (hFrobL : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (G ⧸ L)
      (K.map (QuotientGroup.mk' L)) (R.map (QuotientGroup.mk' L)))
    (hchar : ¬ s ∣ Nat.card (K.map (QuotientGroup.mk' L)))
    (hFPF : letI := chiefFactorConjAction X Y
            ∀ v : ↥X ⧸ Y.subgroupOf X, (∀ r : R, (r : G) • v = v) → v = 1) :
    K ≤ chiefFactorCentralizer X Y := by
  haveI : NeZero s := ⟨(Fact.out : s.Prime).ne_zero⟩
  letI : CommGroup (↥X ⧸ Y.subgroupOf X) :=
    { (inferInstance : Group (↥X ⧸ Y.subgroupOf X)) with mul_comm := hVelem.comm }
  letI := hVelem.zmodModule
  letI := chiefFactorConjAction X Y
  have hL : ∀ l : G, l ∈ L → ∀ v : ↥X ⧸ Y.subgroupOf X, l • v = v := by
    intro l hl v
    exact (chiefFactorConjAction_smul_eq_self_iff_mem l).mpr (hLcent hl) v
  letI := mulDistribMulActionQuotientOfTrivial L hL
  have hFPF' : ∀ v : ↥X ⧸ Y.subgroupOf X,
      (∀ r : R.map (QuotientGroup.mk' L), (r : G ⧸ L) • v = v) → v = 1 := by
    intro v hv
    refine hFPF v (fun r => ?_)
    rw [← mulDistribMulActionQuotientOfTrivial_smul_mk hL (r : G) v]
    exact hv ⟨QuotientGroup.mk' L (r : G), ⟨r, r.2, rfl⟩⟩
  have hKtriv := kernel_acts_trivially_of_coprime_fixedPointFree hFrobL hchar hFPF'
  intro k hk
  refine (chiefFactorConjAction_smul_eq_self_iff_mem k).mp (fun v => ?_)
  rw [← mulDistribMulActionQuotientOfTrivial_smul_mk hL (k : G) v]
  exact hKtriv ⟨QuotientGroup.mk' L (k : G), ⟨k, hk, rfl⟩⟩ v

end OddOrder.BG.Ch1.S03c
