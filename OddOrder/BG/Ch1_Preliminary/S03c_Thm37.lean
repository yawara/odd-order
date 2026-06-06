/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.Isaacs.Ch02_Subnormality.Main
import OddOrder.BG.Ch1_Preliminary.S03b_Lemma33
import OddOrder.BG.Ch1_Preliminary.S03_FrobeniusActions
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
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

/-- **G/L is Frobenius** (BG Lemmas 3.1/3.2 applied in Thm 3.7): if `G = KR` is a Frobenius group
with solvable kernel `K`, and `N ⊴ G` is a proper subgroup of `K`, then `G/N` is a Frobenius group
with kernel `K/N` and complement `RN/N`. The coprimality of `⟨x⟩` with `K` (for `x ∈ R`) comes from
`coprime_card_kernel_complement`. -/
theorem frobenius_quotient_of_normal_lt_kernel
    {G : Type*} [Group G] [Finite G] {K R N : Subgroup G} [N.Normal]
    (h : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G K R) (hNK : N ≤ K) (hKN : ¬ K ≤ N)
    (hSolvK : IsSolvable ↥K) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup (G ⧸ N)
      (K.map (QuotientGroup.mk' N)) (R.map (QuotientGroup.mk' N)) := by
  refine OddOrder.BG.Ch1.S03.quotient_isFrobeniusGroup_of_le_kernel_of_coprime_zpowers
    h hNK hKN ?_ hSolvK
  intro x hxR _
  have hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥R) :=
    h.coprime_card_kernel_complement
  have hdvd : Nat.card ↥(Subgroup.zpowers x) ∣ Nat.card ↥R :=
    Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxR)
  exact (hcop.coprime_dvd_right hdvd).symm

open OddOrder.GroupTheory in
/-- **A chief factor of a finite solvable group is elementary abelian** (in the quotient-type model
`↥X ⧸ Y.subgroupOf X` used by `chiefFactorConjAction`): transports the standard
`X.map(mk' Y)`-form (`isMinimalNormal_le_fitting_and_isElementaryAbelian`) across the first
isomorphism `↥X ⧸ Y.subgroupOf X ≃* ↥(X.map (mk' Y))`. -/
theorem chiefFactor_isElementaryAbelian
    {G : Type*} [Group G] [Finite G] [IsSolvable G] {X Y : Subgroup G} [Y.Normal]
    (hChief : IsChiefFactor X Y) :
    ∃ s : ℕ, s.Prime ∧ IsElementaryAbelian s (↥X ⧸ Y.subgroupOf X) := by
  have hMin := hChief.isMinimalNormal_map_quotient
  obtain ⟨s, hs_prime, hs_ea⟩ :=
    (OddOrder.BG.Ch1.S01.isMinimalNormal_le_fitting_and_isElementaryAbelian hMin).2.2
  refine ⟨s, hs_prime, ?_⟩
  let φ : ↥X →* G ⧸ Y := (QuotientGroup.mk' Y).comp X.subtype
  have hker : φ.ker = Y.subgroupOf X := by
    ext x
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : φ.range = X.map (QuotientGroup.mk' Y) := by
    ext z
    simp only [φ, MonoidHom.mem_range, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩; exact ⟨⟨g, hg⟩, rfl⟩
  let e : ↥X ⧸ Y.subgroupOf X ≃* ↥(X.map (QuotientGroup.mk' Y)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))
  exact IsElementaryAbelian.of_mulEquiv e.symm hs_ea

/-- **Frobenius FPF on the kernel** (conjugation form): in a Frobenius group `G = KR`, the only
element of the kernel `K` fixed by conjugation by *all* of `R` is the identity (`C_K(R) = 1`). Used
to collapse the lifted fixed point in BG Thm 3.7's coprime case. -/
theorem frobenius_kernel_conj_fixed_eq_one
    {G : Type*} [Group G] {K R : Subgroup G} (h : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G K R)
    {c : G} (hcK : c ∈ K) (hfix : ∀ r ∈ R, r * c * r⁻¹ = c) : c = 1 := by
  by_contra hc1
  haveI : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr h.ne_bot_complement
  obtain ⟨r, hr⟩ := exists_ne (1 : ↥R)
  have hrR : (r : G) ∈ R := r.2
  have hr1 : (r : G) ≠ 1 := by simpa using hr
  have hcomm : (r : G) * c = c * (r : G) := by
    have hf : (r : G) * c * (r : G)⁻¹ * (r : G) = c * (r : G) := by rw [hfix (r : G) hrR]
    simpa [mul_assoc] using hf
  have hmem : c ∈ Subgroup.centralizer ({(r : G)} : Set G) ⊓ K :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm, hcK⟩
  rw [OddOrder.BG.Ch1.S03.centralizer_complement_inf_kernel_eq_bot h (r : G) hrR hr1,
    Subgroup.mem_bot] at hmem
  exact hc1 hmem

/-- In a Frobenius group `G = KR`, the complement order `|R|` is coprime to the order of any
subgroup `X ≤ K` (since `|X| ∣ |K|` and `(|K|,|R|)=1`). The coprimality hypothesis for the
coprime fixed-point lift in BG Thm 3.7's FPF derivation. -/
theorem frobenius_coprime_complement_subgroup
    {G : Type*} [Group G] [Finite G] {K R X : Subgroup G}
    (h : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G K R) (hXK : X ≤ K) :
    Nat.Coprime (Nat.card ↥R) (Nat.card ↥X) :=
  h.coprime_card_kernel_complement.symm.coprime_dvd_right (Subgroup.card_dvd_of_le hXK)

open OddOrder.GroupTheory in
/-- **(ii) FPF for the coprime chief-factor case**: in a finite solvable Frobenius group `G = KR`,
for a chief factor `X/Y` with `X ⊆ K`, the complement `R` acts fixed-point-freely on `X/Y` via
`chiefFactorConjAction` (`C_{X/Y}(R) = 1`). Proof: an `R`-fixed coset lifts (coprime action,
`coprime_fixedPoints_quotient_of_coprime_normal`) to an `R`-fixed element of `X ≤ K`, which is `1`
by `frobenius_kernel_conj_fixed_eq_one`. -/
theorem chiefFactor_fixedPointFree
    {G : Type*} [Group G] [Finite G] [IsSolvable G] {K R X Y : Subgroup G}
    [X.Normal] [Y.Normal]
    (h : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G K R) (hXK : X ≤ K) :
    letI := chiefFactorConjAction X Y
    ∀ v : ↥X ⧸ Y.subgroupOf X, (∀ r : R, (r : G) • v = v) → v = 1 := by
  letI := chiefFactorConjAction X Y
  set ψ : ↥R →* MulAut G := MulAut.conj.comp R.subtype with hψ
  have hXinv : OddOrder.Isaacs.Ch03.IsAInvariant ψ X :=
    fun a => Subgroup.Normal.conj_smul_eq_self (a : G) X
  have hYinv : OddOrder.Isaacs.Ch03.IsAInvariant ψ Y :=
    fun a => Subgroup.Normal.conj_smul_eq_self (a : G) Y
  have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant hXinv.restrict (Y.subgroupOf X) :=
    hXinv.subgroupOf hYinv
  have hCop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥(Y.subgroupOf X)) :=
    (frobenius_coprime_complement_subgroup h hXK).coprime_dvd_right
      (Subgroup.card_subgroup_dvd_card (Y.subgroupOf X))
  have hSolv : IsSolvable ↥R ∨ IsSolvable ↥(Y.subgroupOf X) := Or.inr inferInstance
  have hrestrict : ∀ (a : ↥R) (x : ↥X),
      (hXinv.restrict a) x = ConjAct.toConjAct (a : G) • x := fun _ _ => rfl
  intro v hv
  induction v using QuotientGroup.induction_on with
  | _ x =>
    have hgfix : ∀ a : ↥R, ∃ n ∈ Y.subgroupOf X, (hXinv.restrict a) x = x * n := by
      intro a
      have hva := hv a
      rw [chiefFactorConjAction_smul_mk, QuotientGroup.eq] at hva
      refine ⟨x⁻¹ * (hXinv.restrict a) x, ?_, by group⟩
      rw [hrestrict]
      simpa using (Y.subgroupOf X).inv_mem hva
    obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
      OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal hCop hSolv hN_inv hgfix
    have hc_one : (c : G) = 1 := by
      refine frobenius_kernel_conj_fixed_eq_one h (hXK c.2) (fun r hrR => ?_)
      have hcr : ConjAct.toConjAct r • c = c := by
        rw [← hrestrict ⟨r, hrR⟩ c]; exact hc_fix ⟨r, hrR⟩
      exact congrArg Subtype.val hcr
    have hc1 : c = 1 := Subtype.ext (by simpa using hc_one)
    have hx_eq : x = n⁻¹ := by
      rw [hc1] at hcn; rw [eq_comm, mul_eq_one_iff_eq_inv] at hcn; exact hcn
    rw [QuotientGroup.eq_one_iff, hx_eq]
    exact (Y.subgroupOf X).inv_mem hn

/-- **Frobenius restriction to `LR`** (inductive step of BG Thm 3.7): if `G = KR` is a Frobenius
group and `L ⊴ G` is a nontrivial normal subgroup of the kernel `K`, then the subgroup `L ⊔ R = LR`
is a Frobenius group with kernel `L` and complement `R` (as subgroups of `↥(L ⊔ R)` via
`subgroupOf`). The conjugation/complement structure restricts from `G`. -/
theorem isFrobeniusGroup_sup_of_normal_le_kernel
    {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
    (h : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G K R) {L : Subgroup G} [L.Normal]
    (hLK : L ≤ K) (hL_ne : L ≠ ⊥) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(L ⊔ R)
      (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)) := by
  have hdisjLR : Disjoint L R := Disjoint.mono_left hLK h.isComplement.disjoint
  have hLR_bot : L ⊓ R = ⊥ := hdisjLR.eq_bot
  refine
    { isNormal := Subgroup.normal_subgroupOf
      isComplement := ?_
      ne_bot_kernel := ?_
      ne_bot_complement := ?_
      conj_frobenius := ?_ }
  · -- complement: disjoint + the product covers `L ⊔ R`
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · refine disjoint_iff.mpr (eq_bot_iff.mpr (fun x hx => ?_))
      rw [Subgroup.mem_inf] at hx
      simp only [Subgroup.mem_subgroupOf] at hx
      have hmem : (x : G) ∈ L ⊓ R := ⟨hx.1, hx.2⟩
      rw [hLR_bot, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      exact Subtype.ext (by simpa using hmem)
    · ext g
      simp only [Set.mem_mul, Set.mem_univ, iff_true]
      have hgset : (g : G) ∈ (↑L : Set G) * (↑R : Set G) := by
        rw [← Subgroup.normal_mul L R]; exact g.2
      obtain ⟨l, hl, r, hr, hlr⟩ := hgset
      have hlL : l ∈ L := hl
      have hrR : r ∈ R := hr
      exact ⟨⟨l, (le_sup_left : L ≤ L ⊔ R) hlL⟩, Subgroup.mem_subgroupOf.mpr hlL,
        ⟨r, (le_sup_right : R ≤ L ⊔ R) hrR⟩, Subgroup.mem_subgroupOf.mpr hrR,
        Subtype.ext (by simpa using hlr)⟩
  · -- ne_bot_kernel
    rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hL_ne (hd.eq_bot_of_le le_sup_left)
  · -- ne_bot_complement
    rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => h.ne_bot_complement (hd.eq_bot_of_le le_sup_right)
  · -- conj_frobenius inherited from `h` (via `L ≤ K`)
    intro a ha hane n hn hnne
    simp only [Subgroup.mem_subgroupOf] at ha hn
    have hane' : (a : G) ≠ 1 := fun hc => hane (Subtype.ext (by simpa using hc))
    have hnne' : (n : G) ≠ 1 := fun hc => hnne (Subtype.ext (by simpa using hc))
    intro hcontra
    apply h.conj_frobenius (a : G) ha hane' (n : G) (hLK hn) hnne'
    have hval := congrArg (Subtype.val) hcontra
    push_cast at hval
    exact hval

/-- **A normal `s`-subgroup acts trivially on an irreducible `s`-module** (same-prime core of BG
Thm 3.7's chief-factor analysis). If `K̄ ⊴ Ḡ` is an `s`-group acting (`MulDistribMulAction`) on a
finite `s`-group `M` whose only `Ḡ`-invariant subgroups are `⊥` and `⊤`, then `K̄` fixes every point
of `M`. Proof: the `K̄`-fixed points `C_M(K̄)` form a `Ḡ`-invariant subgroup
(`K̄ ⊴ Ḡ`), nonzero by the `p`-group fixed-point theorem
(`fixedPoints_ne_bot_of_pgroup_action_pgroup`), hence `= ⊤` by irreducibility. -/
theorem normal_pgroup_acts_trivially_of_irreducible {s : ℕ} [Fact s.Prime]
    {Gbar M : Type*} [Group Gbar] [Finite Gbar] [Group M] [Finite M]
    [MulDistribMulAction Gbar M] {Kbar : Subgroup Gbar} [Kbar.Normal]
    (hKbar : IsPGroup s Kbar) (hMs : IsPGroup s M)
    (hirr : ∀ N : Subgroup M, (∀ g : Gbar, ∀ n : M, n ∈ N → g • n ∈ N) → N = ⊥ ∨ N = ⊤) :
    ∀ (k : Kbar) (m : M), (k : Gbar) • m = m := by
  rcases subsingleton_or_nontrivial M with _ | _
  · intro k m; exact Subsingleton.elim _ _
  · set φ : Kbar →* MulAut M := (MulDistribMulAction.toMulAut Gbar M).comp Kbar.subtype with hφ
    have hsmul : ∀ (a : Kbar) (m : M), (φ a) m = (a : Gbar) • m := fun _ _ => rfl
    have hCne : Subgroup.fixedPointsOfMulAut φ ≠ ⊥ :=
      OddOrder.Isaacs.Ch04.fixedPoints_ne_bot_of_pgroup_action_pgroup hMs hKbar φ
    have hCinv : ∀ g : Gbar, ∀ n : M, n ∈ Subgroup.fixedPointsOfMulAut φ →
        g • n ∈ Subgroup.fixedPointsOfMulAut φ := by
      intro g n hn
      rw [Subgroup.mem_fixedPointsOfMulAut]
      intro a
      rw [hsmul]
      have hk' : g⁻¹ * (a : Gbar) * g ∈ Kbar := by
        have hc := (inferInstance : Kbar.Normal).conj_mem (a : Gbar) a.2 g⁻¹
        simpa using hc
      have hfix : ((⟨g⁻¹ * (a : Gbar) * g, hk'⟩ : Kbar) : Gbar) • n = n := by
        have hm := (Subgroup.mem_fixedPointsOfMulAut.mp hn) ⟨g⁻¹ * (a : Gbar) * g, hk'⟩
        rw [hsmul] at hm; exact hm
      calc (a : Gbar) • (g • n) = ((a : Gbar) * g) • n := by rw [mul_smul]
        _ = (g * (g⁻¹ * (a : Gbar) * g)) • n := by group
        _ = g • ((g⁻¹ * (a : Gbar) * g) • n) := by rw [mul_smul]
        _ = g • n := by rw [hfix]
    rcases hirr _ hCinv with hbot | htop
    · exact absurd hbot hCne
    · intro k m
      have hmem : m ∈ Subgroup.fixedPointsOfMulAut φ := by rw [htop]; exact Subgroup.mem_top m
      have hm := (Subgroup.mem_fixedPointsOfMulAut.mp hmem) k
      rw [hsmul] at hm; exact hm

open OddOrder.GroupTheory in
/-- **A chief factor is irreducible** (same-prime plumbing for BG Thm 3.7): for a `G`-chief factor
`X/Y`, the only `chiefFactorConjAction`-invariant subgroups of `↥X ⧸ Y.subgroupOf X` are `⊥` and
`⊤`. An invariant subgroup `N` pulls back (correspondence theorem) to a `G`-normal subgroup
`W = (N.comap mk).map X.subtype` with `Y ≤ W ≤ X`, which by `IsChiefFactor` equals `Y` or `X`,
giving `N = ⊥` or `N = ⊤`. -/
theorem chiefFactor_invariant_eq_bot_or_top {G : Type*} [Group G] {X Y : Subgroup G}
    [X.Normal] [Y.Normal] (hChief : IsChiefFactor X Y) :
    letI := chiefFactorConjAction X Y
    ∀ N : Subgroup (↥X ⧸ Y.subgroupOf X),
      (∀ g : G, ∀ n : ↥X ⧸ Y.subgroupOf X, n ∈ N → g • n ∈ N) → N = ⊥ ∨ N = ⊤ := by
  letI := chiefFactorConjAction X Y
  intro N hNinv
  have hYleX : Y ≤ X := hChief.lt.le
  set q : ↥X →* (↥X ⧸ Y.subgroupOf X) := QuotientGroup.mk' (Y.subgroupOf X) with hq
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  set W : Subgroup G := (N.comap q).map X.subtype with hW
  have hWX : W ≤ X := by rw [hW]; exact Subgroup.map_subtype_le _
  have hNcomapW : N.comap q = W.subgroupOf X := by
    rw [hW]
    exact (Subgroup.comap_map_eq_self (by rw [Subgroup.ker_subtype]; exact bot_le)).symm
  have hNeq : (N.comap q).map q = N := Subgroup.map_comap_eq_self_of_surjective hqsurj N
  have hWnorm : W.Normal := by
    refine ⟨fun w hw g => ?_⟩
    rw [hW, Subgroup.mem_map] at hw ⊢
    obtain ⟨x', hx', hx'eq⟩ := hw
    have hgxX : g * w * g⁻¹ ∈ X := by
      rw [← hx'eq]; exact (inferInstance : X.Normal).conj_mem _ x'.2 g
    refine ⟨⟨g * w * g⁻¹, hgxX⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap] at hx' ⊢
    have hmkeq : q ⟨g * w * g⁻¹, hgxX⟩ = g • q x' := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, chiefFactorConjAction_smul_mk]
      congr 1
      apply Subtype.ext
      show g * w * g⁻¹ = (↑(ConjAct.toConjAct g • x') : G)
      rw [← hx'eq]; rfl
    rw [hmkeq]; exact hNinv g (q x') hx'
  have hYW : Y ≤ W := by
    intro y hy
    rw [hW, Subgroup.mem_map]
    have hk : q ⟨y, hYleX hy⟩ = 1 := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hy
    exact ⟨⟨y, hYleX hy⟩, by rw [Subgroup.mem_comap, hk]; exact N.one_mem, rfl⟩
  rcases hChief.eq_bot_or_eq_top_of_normal W hWnorm hYW hWX with hWeq | hWeq
  · left
    rw [← hNeq, hNcomapW, hWeq, eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨a, ha, haz⟩ := hz
    rw [Subgroup.mem_bot, ← haz, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ha
  · right
    rw [← hNeq, hNcomapW, hWeq, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective q hqsurj]

open OddOrder.GroupTheory in
/-- **Same-prime branch of BG Thm 3.7's chief-factor analysis**: for a `G`-chief factor `X/Y`
elementary abelian of prime `s`, with `L ⊴ G` centralizing `X/Y` and the quotient kernel
`K/L` an `s`-group (same prime as `X/Y`), the kernel `K` centralizes `X/Y`
(`K ≤ chiefFactorCentralizer X Y`). Descends the action to `G/L`, then applies
`normal_pgroup_acts_trivially_of_irreducible` with irreducibility from
`chiefFactor_invariant_eq_bot_or_top`. -/
theorem samePrime_kernel_le_chiefFactorCentralizer
    {G : Type*} [Group G] [Finite G] {K X Y : Subgroup G} [K.Normal]
    [X.Normal] [Y.Normal] {s : ℕ} [Fact s.Prime]
    (hChief : IsChiefFactor X Y)
    (hVelem : IsElementaryAbelian s (↥X ⧸ Y.subgroupOf X))
    {L : Subgroup G} [L.Normal] (hLcent : L ≤ chiefFactorCentralizer X Y)
    (hKbar : IsPGroup s (K.map (QuotientGroup.mk' L))) :
    K ≤ chiefFactorCentralizer X Y := by
  letI := chiefFactorConjAction X Y
  have hVs : IsPGroup s (↥X ⧸ Y.subgroupOf X) :=
    fun v => ⟨1, by rw [pow_one]; exact hVelem.pow_eq_one v⟩
  have hL : ∀ l : G, l ∈ L → ∀ v : ↥X ⧸ Y.subgroupOf X, l • v = v := by
    intro l hl v
    exact (chiefFactorConjAction_smul_eq_self_iff_mem l).mpr (hLcent hl) v
  letI := mulDistribMulActionQuotientOfTrivial L hL
  haveI : (K.map (QuotientGroup.mk' L)).Normal :=
    (inferInstance : K.Normal).map (QuotientGroup.mk' L) (QuotientGroup.mk'_surjective L)
  have hirr : ∀ N : Subgroup (↥X ⧸ Y.subgroupOf X),
      (∀ gq : G ⧸ L, ∀ n : ↥X ⧸ Y.subgroupOf X, n ∈ N → gq • n ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hNinv
    refine chiefFactor_invariant_eq_bot_or_top hChief N (fun g n hn => ?_)
    rw [← mulDistribMulActionQuotientOfTrivial_smul_mk hL g n]
    exact hNinv (QuotientGroup.mk g) n hn
  have hKtriv := normal_pgroup_acts_trivially_of_irreducible hKbar hVs hirr
  intro k hk
  refine (chiefFactorConjAction_smul_eq_self_iff_mem k).mp (fun v => ?_)
  rw [← mulDistribMulActionQuotientOfTrivial_smul_mk hL (k : G) v]
  exact hKtriv ⟨QuotientGroup.mk' L (k : G), ⟨k, hk, rfl⟩⟩ v

end OddOrder.BG.Ch1.S03c
