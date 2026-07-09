/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CoherenceCorePart1

/-!
# Peterfalvi §08 Coherence Core — Part 2/3 (first `SibleyDadeHypothesis` block)

Prefix-split from `S08_CoherenceCore.lean` (11,969 行 → 3 ファイル, issue 0066)。
本ファイル = 元 L3451–8088 (最初の `SibleyDadeHypothesis` namespace + inter-block lemmas)。
import chain: Part1 ← **Part2** ← S08_CoherenceCore。下流は従来どおり `S08_CoherenceCore` を import すれば全名前にアクセス可。
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- The coherence map `τ` of the (6.8) setup, realized as the genuine §4 Dade isometry
(`dadeIntegralCharacterMap`) — **not** an opaque global isometry. -/
noncomputable abbrev tau (hyp : SibleyDadeHypothesis G L H) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G :=
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dade
    (hyp.dade.fullDadeIsometryData hyp.hconj)

/-- The (6.8) coherence target: `S` is coherent for the **real Dade map** `tau`.  This is exactly
the conclusion shape produced by the §7 engine, hence honestly dischargeable — unlike the legacy
`SibleySetup.CoherenceTarget`, which required a nonexistent global isometry. -/
abbrev CoherenceTarget (hyp : SibleyDadeHypothesis G L H) :=
  OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.S
    (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)

/-- **(6.8.1) Dade reciprocity for the Sibley carrier.**  Since `H^#` is TI (`dade_H_eq_bot`), the
real Dade map `tau` satisfies `⟨α^τ, ψ⟩_G = ⟨α, Res_L^G ψ⟩_L` for supported `α ∈ CF(L, H^#)` and any
`ψ ∈ CF(G)` (`inner_dadeIntegralCharacterMap_eq_inner_restrict`).  This is the move the (6.8.1)
proof (mmd L176) uses to rewrite `⟨η₁^{τ₁}, (χᵢ − dᵢχ₁)^τ⟩ = ⟨Res_L(η₁^{τ₁}), χᵢ − dᵢχ₁⟩`, feeding
the `Res_L(η₁^{τ₁}) = c∑dᵢχᵢ + χ′` decomposition. -/
theorem inner_tau_eq_inner_restrict (hyp : SibleyDadeHypothesis G L H)
    {α : ClassFunction ↥L ℂ}
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (ψ : ClassFunction G ℂ) :
    ClassFunction.inner (hyp.tau α) ψ = ClassFunction.inner α (ClassFunction.restrict L ψ) :=
  inner_dadeIntegralCharacterMap_eq_inner_restrict hyp.dade hyp.hconj hyp.dade_H_eq_bot hαsupp ψ

/-- (6.8)(a) consequence: `[L : H] = |W₁|`.  From the complement `L = H ⋊ W₁` (`hyp.split`).
This is the common degree of the members of `Y = S(H')`: by [Is] Thm 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`), `(Ind_H^L θ)(1) = [L:H]·θ(1) = |W₁|` for the
degree-`1` characters `θ ∈ Irr(H/H')`. -/
theorem index_H_eq_card_W1 (hyp : SibleyDadeHypothesis G L H) :
    H.index = Nat.card hyp.W1 :=
  (Subgroup.IsComplement.card_right (Subgroup.isComplement'_def.mp hyp.split)).symm

/-- Degree-one source characters induce to class functions of degree |W1| in the (6.8)
setup. This is the degree side of the Y = S(Hprime) family used in the final coherence assembly. -/
theorem induce_apply_one_eq_card_W1_of_degree_one
    (hyp : SibleyDadeHypothesis G L H) (θ : IrreducibleCharacter ↥H)
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L) =
      (Nat.card hyp.W1 : ℂ) := by
  rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ_one, mul_one,
    hyp.index_H_eq_card_W1]

/-- If two source class functions induce to the same value at 1, their induced difference is
supported on H-sharp in the (6.8) Dade support. -/
theorem support_sub_induce_subset_sharpImage_of_apply_one_eq
    (hyp : SibleyDadeHypothesis G L H) (θ ψ : ClassFunction ↥H ℂ)
    (hone : OddOrder.RepresentationTheory.ClassFunction.induce H θ (1 : ↥L) =
      OddOrder.RepresentationTheory.ClassFunction.induce H ψ (1 : ↥L)) :
    (OddOrder.RepresentationTheory.ClassFunction.induce H θ -
        OddOrder.RepresentationTheory.ClassFunction.induce H ψ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  letI : H.Normal := hyp.H_normal
  intro x hx
  have hθsupp :
      (OddOrder.RepresentationTheory.ClassFunction.induce H θ).support ⊆ H :=
    OddOrder.RepresentationTheory.ClassFunction.support_induce_subset_of_normal
      (G := ↥L) (k := ℂ) H θ
  have hψsupp :
      (OddOrder.RepresentationTheory.ClassFunction.induce H ψ).support ⊆ H :=
    OddOrder.RepresentationTheory.ClassFunction.support_induce_subset_of_normal
      (G := ↥L) (k := ℂ) H ψ
  have hxH : x ∈ H := by
    rcases OddOrder.RepresentationTheory.ClassFunction.support_sub_subset
        (OddOrder.RepresentationTheory.ClassFunction.induce H θ)
        (OddOrder.RepresentationTheory.ClassFunction.induce H ψ) hx with hxθ | hxψ
    · exact hθsupp hxθ
    · exact hψsupp hxψ
  have hxne : x ≠ 1 := by
    intro hx1
    apply hx
    rw [hx1, OddOrder.RepresentationTheory.ClassFunction.sub_apply, hone, sub_self]
  change (x : G) ∈ sharpImage H
  refine ⟨?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩
  · intro hx1G
    exact hxne (Subtype.ext hx1G)

/-- Degree-one source characters give induced differences supported on H-sharp. -/
theorem support_sub_induce_subset_sharpImage_of_degree_one
    (hyp : SibleyDadeHypothesis G L H) (θ ψ : IrreducibleCharacter ↥H)
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hψ_one : (ψ : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    (OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) -
        OddOrder.RepresentationTheory.ClassFunction.induce H (ψ : ClassFunction ↥H ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
  hyp.support_sub_induce_subset_sharpImage_of_apply_one_eq
    (θ : ClassFunction ↥H ℂ) (ψ : ClassFunction ↥H ℂ) (by
      rw [hyp.induce_apply_one_eq_card_W1_of_degree_one θ hθ_one,
        hyp.induce_apply_one_eq_card_W1_of_degree_one ψ hψ_one])

/-- Equal-degree induced irreducible families from degree-one source characters are coherent for
Sibley's Dade map. This is the engine-call form of the (6.8) Y = S(Hprime) step: once the
eta-family of irreducible induced characters is constructed and shown injective, the remaining
(1.1)+(1.4) equal-degree coherence hypotheses are discharged by the Sibley carrier. -/
noncomputable def coherentInducedDegreeOneFamily
    (hyp : SibleyDadeHypothesis G L H) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (θ : Fin n → IrreducibleCharacter ↥H) (η : Fin n → IrreducibleCharacter ↥L)
    (hη_ind : ∀ j,
      (η j : ClassFunction ↥L ℂ) =
        OddOrder.RepresentationTheory.ClassFunction.induce H (θ j : ClassFunction ↥H ℂ))
    (hηinj : Function.Injective η)
    (hθ_one : ∀ j, (θ j : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (Set.range (fun j => (η j : ClassFunction ↥L ℂ)))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hdeg : ∀ j, ((η j : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 =
      ((η 0 : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    intro j
    rw [hη_ind j, hη_ind 0,
      hyp.induce_apply_one_eq_card_W1_of_degree_one (θ j) (hθ_one j),
      hyp.induce_apply_one_eq_card_W1_of_degree_one (θ 0) (hθ_one 0)]
  have hsuppdiff : ∀ j,
      (OddOrder.RepresentationTheory.irreducibleCharacterDifference η j).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    intro j
    simpa [OddOrder.RepresentationTheory.irreducibleCharacterDifference, hη_ind j, hη_ind 0] using
      hyp.support_sub_induce_subset_sharpImage_of_degree_one (θ j) (θ 0)
        (hθ_one j) (hθ_one 0)
  have h1notA : (1 : G) ∉ sharpImage H := by
    intro h
    exact h.2 rfl
  exact OddOrder.Peterfalvi.S07.coherentEqualDegree_fromDade hyp.dade hyp.hconj hn η hηinj
    hdeg hsuppdiff h1notA

/-- **(6.8)(c2) inertia equality** for a nontrivial linear `θ`.

Under the (4.6)/(c2) data — `H ⋊ W₁`, `C_H(w) = W₂ ⊆ ⁅H,H⁆` for `w ∈ W₁∖1`, and the Hall
coprimality `gcd(|H|,|W₁|) = 1` — the inertia group of a nontrivial degree-one `θ` is exactly `H`.

Proof.  Pass to `Ḡ = L/⁅H,H⁆`, `H̄ = H/⁅H,H⁆` (abelian).  `θ` is linear, so inflates from a
nontrivial `θ̄ ∈ Irr H̄`.  The coprimality + Isaacs (3.28) lift gives `C_{H̄}(w̄) = 1` for
`w̄ ∈ W̄₁∖1`; since `H̄` is abelian, Brauer's permutation lemma turns this into "`w̄` fixes only the
trivial irreducible", so `w̄ ∉ I_{Ḡ}(θ̄)`.  The inertia-transfer bridge then gives `w ∉ I_L(θ)` for
`w ∈ W₁∖1`, and the complement `L = H ⋊ W₁` reduces a general `g ∉ H` to this case (`I_L(θ) ⊇ H`, so
the `H`-part is absorbed). -/
theorem inertia_eq_H_of_c2 (hyp : SibleyDadeHypothesis G L H)
    (cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L)
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1) (hW2 : cert.W2 ≤ ⁅H, H⁆)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {θ : IrreducibleCharacter ↥H}
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hθ_ne : θ ≠ trivialIrreducibleCharacter ↥H) :
    letI : H.Normal := hyp.H_normal
    ClassFunction.inertia (θ : ClassFunction ↥H ℂ) = H := by
  classical
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Finite ↥L := Fintype.finite (Fintype.ofFinite _)
  -- The quotient `Ḡ = L/⁅H,H⁆` and the image `H̄ = H/⁅H,H⁆`.
  set M : Subgroup ↥L := ⁅H, H⁆ with hM_def
  haveI hMnormal : M.Normal := by rw [hM_def]; infer_instance
  set mkM : ↥L →* (↥L ⧸ M) := QuotientGroup.mk' M with hmkM_def
  set Hbar : Subgroup (↥L ⧸ M) := H.map mkM with hHbar_def
  haveI hHbar_normal : Hbar.Normal := by rw [hHbar_def, hmkM_def]; infer_instance
  -- `H̄` is abelian: images of `H` commute since their commutators land in `⁅H,H⁆ = ker mkM`.
  have hHbar_comm : ∀ a b : ↥Hbar, Commute a b := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [hHbar_def, Subgroup.mem_map] at ha hb
    obtain ⟨x, hxH, rfl⟩ := ha
    obtain ⟨y, hyH, rfl⟩ := hb
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    -- `mkM x` and `mkM y` commute because `⁅x,y⁆ ∈ ⁅H,H⁆ = ker mkM`.
    have hcomm_elt : ⁅(x : ↥L), (y : ↥L)⁆ ∈ M := by
      rw [hM_def]; exact Subgroup.commutator_mem_commutator hxH hyH
    have hmk_one : mkM ⁅(x : ↥L), (y : ↥L)⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm_elt
    rw [map_commutatorElement] at hmk_one
    exact commutatorElement_eq_one_iff_mul_comm.mp hmk_one
  -- The corestriction `q : ↥H →* ↥H̄` with `(q x : Ḡ) = mkM x`.
  set q : ↥H →* ↥Hbar :=
    (mkM.comp H.subtype).codRestrict Hbar (fun x => by
      rw [hHbar_def]; exact Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩) with hq_def
  have hq : ∀ x : ↥H, ((q x : ↥Hbar) : ↥L ⧸ M) = mkM (x : ↥L) := fun x => rfl
  have hq_surj : Function.Surjective q := by
    rintro ⟨z, hz⟩
    rw [hHbar_def, Subgroup.mem_map] at hz
    obtain ⟨x, hxH, hxz⟩ := hz
    exact ⟨⟨x, hxH⟩, Subtype.ext hxz⟩
  have hqinj : Function.Injective
      (ClassFunction.compHom q : ClassFunction ↥Hbar ℂ → ClassFunction ↥H ℂ) :=
    ClassFunction.compHom_injective_of_surjective hq_surj
  -- `θ` is linear, hence kills `⁅H,H⁆.subgroupOf H = commutator ↥H`, so inflates from `H̄`.
  set N : Subgroup ↥H := M.subgroupOf H with hN_def
  haveI hN_normal : N.Normal := by rw [hN_def, hM_def]; exact hMnormal.subgroupOf H
  have hN_eq : N = _root_.commutator ↥H := by
    rw [hN_def, hM_def, ← Subgroup.map_subtype_commutator H, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hker : (N : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro n hn
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def, hθ_one]
    -- `θ` is multiplicative with `θ(1)=1`, so `{x | θ x = 1}` is a subgroup containing commutators.
    have hθ1 : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1 := hθ_one
    have hn' : n ∈ Subgroup.closure (commutatorSet ↥H) := by
      have : n ∈ N := hn
      rwa [hN_eq, _root_.commutator_eq_closure] at this
    refine Subgroup.closure_induction
      (p := fun g _ => (θ : ClassFunction ↥H ℂ) g = 1) ?_ ?_ ?_ ?_ hn'
    · rintro _ ⟨a, b, rfl⟩
      exact θ.isIrreducible.apply_commutatorElement_eq_one_of_apply_one_eq_one hθ1 a b
    · exact hθ1
    · intro a b _ _ ha hb
      rw [θ.isIrreducible.map_mul_of_apply_one_eq_one hθ1, ha, hb, one_mul]
    · intro a _ ha
      have hai := θ.isIrreducible.map_mul_of_apply_one_eq_one hθ1 a a⁻¹
      rw [mul_inv_cancel, hθ1, ha, one_mul] at hai
      exact hai.symm
  have hkerq : q.ker = N := by
    ext x
    rw [MonoidHom.mem_ker]
    change q x = 1 ↔ (x : ↥L) ∈ M
    constructor
    · intro hx
      have hx1 : mkM (x : ↥L) = 1 := by rw [← hq x, hx]; rfl
      rw [hmkM_def] at hx1
      exact (QuotientGroup.eq_one_iff _).mp hx1
    · intro hx
      apply Subtype.ext
      rw [hq x, hmkM_def]
      exact (QuotientGroup.eq_one_iff _).mpr hx
  -- `θ` inflates from a `θ̄ : Irr ↥H̄` along the surjection `q` (linear ⟹ `ker q = N ⊆ ker θ`).
  obtain ⟨θbar, hcompq⟩ :=
    exists_compHom_eq_of_subset_characterKernel hq_surj θ (by rw [hkerq]; exact hker)
  -- `θ̄` is nontrivial, else `θ = compHom q (triv) = triv`.
  have hθbar_ne : θbar ≠ trivialIrreducibleCharacter ↥Hbar := by
    intro hbar
    apply hθ_ne
    apply IrreducibleCharacter.ext
    rw [← hcompq, hbar]
    ext x
    simp [ClassFunction.compHom_apply, trivialIrreducibleCharacter,
      trivialClassFunction_apply]
  -- **B1′** (fixed-point-free action of `W̄₁` on `H̄`): `C_{H̄}(w̄) = 1` for `w̄ ∈ W̄₁∖1`.
  -- We only need the specific `w̄ = mkM w`; the S03 `≤ N` quotient lemma supplies it.
  have hNK : (⁅H, H⁆ : Subgroup ↥L) ≤ H := Subgroup.commutator_le_left H H
  have hcentral : ∀ x ∈ hyp.W1, x ≠ 1 →
      Subgroup.centralizer ({x} : Set ↥L) ⊓ H ≤ M := by
    intro x hxW1 hxne
    have hcw2 : Subgroup.centralizer ({x} : Set ↥L) ⊓ cert.K = cert.W2 :=
      cert.centralizer_W2 x (hW1 ▸ hxW1) hxne
    rw [hK] at hcw2
    rw [hcw2, hM_def]; exact hW2
  have hlift : ∀ x ∈ hyp.W1, x ≠ 1 → ∀ y ∈ H,
      mkM (x * y * x⁻¹) = mkM y →
        ∃ c : ↥L, c ∈ H ∧ mkM c = mkM y ∧ x * c * x⁻¹ = c := by
    intro x hxW1 hxne y hyH hfix
    have hcop_x : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥H) := by
      rw [Nat.card_zpowers]
      have hdvd : orderOf x ∣ Nat.card hyp.W1 := hyp.W1.orderOf_dvd_natCard hxW1
      exact (hcop.coprime_dvd_right hdvd).symm
    exact OddOrder.BG.Ch1.S03.fixedPoint_lift_of_generator_quotient_fixed
      hNK hcop_x (Or.inl (by infer_instance)) hyH hfix
  have hB1 : ∀ qx ∈ hyp.W1.map mkM, qx ≠ 1 →
      Subgroup.centralizer ({qx} : Set (↥L ⧸ M)) ⊓ Hbar = ⊥ := by
    rw [hHbar_def, hmkM_def]
    exact OddOrder.BG.Ch1.S03.quotient_centralizer_inf_kernel_eq_bot_of_fixedPoint_lift_of_le
      hcentral hlift
  -- Assemble: `I_L(θ) = H` by `le_antisymm`.
  apply le_antisymm
  · -- `I_L(θ) ≤ H`: a `g ∉ H` is `h·w` with `w ∈ W₁∖1`, and `w ∉ I_L(θ)`.
    intro g hg
    by_contra hgH
    -- Write `g = h * w` via the complement `L = H ⋊ W₁`.
    obtain ⟨⟨h, w⟩, hgw⟩ := (hyp.split.existsUnique g).exists
    rw [ClassFunction.mem_inertia] at hg
    -- `w ≠ 1`, else `g = h ∈ H`.
    have hwne : (w : ↥L) ≠ 1 := by
      rintro hw1
      apply hgH
      have : g = (h : ↥L) := by rw [← hgw, hw1, mul_one]
      rw [this]; exact h.property
    -- `h ∈ H ⊆ I_L(θ)`, so `w = h⁻¹·g ∈ I_L(θ)`.
    have hhinertia : (h : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) :=
      ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ) h.property
    have hwinertia : (w : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) := by
      have hwval : (w : ↥L) = (h : ↥L)⁻¹ * g := by rw [← hgw]; group
      rw [hwval]
      exact (ClassFunction.inertia (θ : ClassFunction ↥H ℂ)).mul_mem
        ((ClassFunction.inertia (θ : ClassFunction ↥H ℂ)).inv_mem hhinertia)
        (ClassFunction.mem_inertia.mpr hg)
    -- Transfer `w ∈ I_L(θ)` to `w̄ ∈ I_{Ḡ}(θ̄)`.
    rw [← hcompq] at hwinertia
    have hwbar : mkM (w : ↥L) ∈ ClassFunction.inertia (θbar : ClassFunction ↥Hbar ℂ) :=
      (mem_inertia_compHom_iff q hq hqinj (θbar : ClassFunction ↥Hbar ℂ) (w : ↥L)).mp hwinertia
    -- But `w̄ ∉ I_{Ḡ}(θ̄)`: `C_{H̄}(w̄) = 1`, abelian Brauer, `θ̄ ≠ triv`.
    have hwbar_mem : mkM (w : ↥L) ∈ hyp.W1.map mkM :=
      Subgroup.mem_map.mpr ⟨w, w.property, rfl⟩
    have hwbar_ne : mkM (w : ↥L) ≠ 1 := by
      intro hw1
      have hwM : (w : ↥L) ∈ M := by
        rw [hmkM_def, QuotientGroup.mk'_apply] at hw1
        exact (QuotientGroup.eq_one_iff _).mp hw1
      exact hwne (Subgroup.disjoint_def.mp hyp.split.disjoint (hNK (hM_def ▸ hwM)) w.property)
    have hfree : Subgroup.centralizer ({mkM (w : ↥L)} : Set (↥L ⧸ M)) ⊓ Hbar = ⊥ :=
      hB1 (mkM (w : ↥L)) hwbar_mem hwbar_ne
    have hclass : Nat.card (Function.fixedPoints
        (ConjClasses.conjByPerm (G := ↥L ⧸ M) (H := Hbar) (mkM (w : ↥L)))) = 1 :=
      card_fixedPoints_conjClassPerm_eq_one_of_commute_of_centralizer_inf_eq_bot
        (mkM (w : ↥L)) hHbar_comm hfree
    exact not_mem_inertia_of_ne_trivial_of_card_fixedClasses_eq_one
      (G := ↥L ⧸ M) (H := Hbar) (mkM (w : ↥L)) hclass hθbar_ne hwbar
  · exact ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ)

/-- **(T7-c2 case A) Inertia `I_L(θ) = H`** via the **fixed-point-free action on `Z`**.  Here
`Z ≤ H` is central in `H` (`Z.subgroupOf H ≤ Z(H)`), normalized by `W₁`, with `W₁∖1` acting
fixed-point-freely (`C_Z(w) = Z ∩ W₂ = 1` in case A).  If `w ∈ W₁∖1` fixed `θ`, the central linear
character `φ` of `Res_Z θ` ([Is] 2.27) would be `σ = (·)^w`-invariant, hence `≡ 1`
(`eq_one_of_fixedPointFree_invariant`), forcing `Z.subgroupOf H ⊆ Ker θ`, contradicting `hZker`.
So `I_L(θ) ∩ W₁ = 1` and the complement split `L = H ⋊ W₁` gives `I_L(θ) = H`.  Needs no Hall
coprimality and works for an arbitrary (not necessarily linear) `θ`. -/
theorem inertia_eq_H_of_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    (hZnorm : ∀ w ∈ hyp.W1, w ∈ Subgroup.normalizer Z)
    (hZfpf : ∀ w ∈ hyp.W1, w ≠ 1 → Subgroup.centralizer ({w} : Set ↥L) ⊓ Z = ⊥)
    {θ : IrreducibleCharacter ↥H}
    (hZker : ¬ ((Z.subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ))) :
    letI : H.Normal := hyp.H_normal
    ClassFunction.inertia (θ : ClassFunction ↥H ℂ) = H := by
  classical
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Finite ↥L := Fintype.finite (Fintype.ofFinite _)
  obtain ⟨φ, hφirr, hφ1, -, hφpt⟩ :=
    θ.isIrreducible.exists_central_linear_restriction (Z.subgroupOf H) hZcentral
  have hφmul : ∀ a b : ↥(Z.subgroupOf H), φ (a * b) = φ a * φ b :=
    hφirr.map_mul_of_apply_one_eq_one hφ1
  have hθ1_ne : (θ : ClassFunction ↥H ℂ) 1 ≠ 0 := by
    obtain ⟨n, hpos, hn1, -⟩ := θ.isIrreducible.exists_natDegree_charValue_one_dvd_card
    rw [hn1]; exact_mod_cast hpos.ne'
  apply le_antisymm
  · intro g hg
    by_contra hgH
    obtain ⟨⟨h, w⟩, hgw⟩ := (hyp.split.existsUnique g).exists
    rw [ClassFunction.mem_inertia] at hg
    have hwne : (w : ↥L) ≠ 1 := by
      rintro hw1; apply hgH
      have : g = (h : ↥L) := by rw [← hgw, hw1, mul_one]
      rw [this]; exact h.property
    have hhinertia : (h : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) :=
      ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ) h.property
    have hwinertia : (w : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) := by
      have hwval : (w : ↥L) = (h : ↥L)⁻¹ * g := by rw [← hgw]; group
      rw [hwval]
      exact (ClassFunction.inertia _).mul_mem
        ((ClassFunction.inertia _).inv_mem hhinertia) (ClassFunction.mem_inertia.mpr hg)
    have hwW1 : (w : ↥L) ∈ hyp.W1 := w.property
    -- Conjugation `σ` by `w` on `Z`, fixed-point-free (`C_Z(w) = Z ∩ W₂ = 1`).
    set σ : MulAut ↥Z := Z.normalizerMonoidHom ⟨(w : ↥L), hZnorm (w : ↥L) hwW1⟩ with hσ_def
    have hσval : ∀ z : ↥Z, ((σ z : ↥Z) : ↥L) = (w : ↥L) * (z : ↥L) * (w : ↥L)⁻¹ := fun _ => rfl
    have hσfpf : MonoidHom.FixedPointFree σ := by
      intro z hz
      have hzmem : ((z : ↥Z) : ↥L) ∈ Subgroup.centralizer ({(w : ↥L)} : Set ↥L) ⊓ Z := by
        refine Subgroup.mem_inf.mpr ⟨?_, z.property⟩
        rw [Subgroup.mem_centralizer_iff]
        rintro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
        have hzL := congrArg (Subtype.val : ↥Z → ↥L) hz
        rw [hσval] at hzL
        rw [mul_inv_eq_iff_eq_mul] at hzL
        exact hzL
      rw [hZfpf (w : ↥L) hwW1 hwne, Subgroup.mem_bot] at hzmem
      exact Subtype.ext hzmem
    -- `f = φ ∘ iso` is multiplicative and `σ`-invariant; brick ① gives `φ ≡ 1`.
    set iso : ↥Z ≃* ↥(Z.subgroupOf H) := (Subgroup.subgroupOfEquivOfLe hZH).symm with hiso_def
    have hisoL : ∀ z : ↥Z, (((iso z : ↥(Z.subgroupOf H)) : ↥H) : ↥L) = (z : ↥L) := fun _ => rfl
    set f : ↥Z → ℂ := fun z => φ (iso z) with hf_def
    have hfmul : ∀ a b : ↥Z, f (a * b) = f a * f b := fun a b => by
      simp only [hf_def, map_mul, hφmul]
    have hfone : f 1 = 1 := by simp only [hf_def, map_one, hφ1]
    have hfinv : ∀ z : ↥Z, f (σ z) = f z := by
      intro z
      have hconj : ClassFunction.conjBy (w : ↥L) (θ : ClassFunction ↥H ℂ)
          = (θ : ClassFunction ↥H ℂ) := ClassFunction.mem_inertia.mp hwinertia
      have hval : (θ : ClassFunction ↥H ℂ) ((iso (σ z) : ↥(Z.subgroupOf H)) : ↥H)
          = (θ : ClassFunction ↥H ℂ) ((iso z : ↥(Z.subgroupOf H)) : ↥H) := by
        have hc := congrArg (fun ψ : ClassFunction ↥H ℂ => ψ ((iso z : ↥(Z.subgroupOf H)) : ↥H))
          hconj
        simp only [ClassFunction.conjBy_apply] at hc
        rw [← hc]
        congr 1
      have e1 := hφpt (iso (σ z))
      have e2 := hφpt (iso z)
      have hmul : φ (iso (σ z)) * (θ : ClassFunction ↥H ℂ) 1
          = φ (iso z) * (θ : ClassFunction ↥H ℂ) 1 := by rw [← e1, hval]; exact e2
      simp only [hf_def]
      exact mul_right_cancel₀ hθ1_ne hmul
    -- `φ ≡ 1` forces `Z.subgroupOf H ⊆ Ker θ`, contradicting `hZker`.
    apply hZker
    intro x hx
    rw [SetLike.mem_coe] at hx
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
    have hφx : φ (⟨x, hx⟩ : ↥(Z.subgroupOf H)) = 1 := by
      have hfx := eq_one_of_fixedPointFree_invariant hσfpf hfmul hfone hfinv
        (iso.symm ⟨x, hx⟩)
      simpa only [hf_def, MulEquiv.apply_symm_apply] using hfx
    have hpt := hφpt (⟨x, hx⟩ : ↥(Z.subgroupOf H))
    rw [hφx, one_mul] at hpt
    exact hpt
  · exact ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ)

/-- **Peterfalvi (6.8) Y-family irreducibility.**  For a nontrivial degree-one (linear) source
character `θ` of `H`, the induced character `Ind_H^L θ` is irreducible.  Inertia `I_L(θ) = H`
(free action of `W₁`) is discharged via the (6.8)(c) disjunction and fed to [Is] Thm 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`):

* **(c1)** `L` Frobenius with kernel `H`: `isIrreducibleCharacter_induce_of_frobeniusGroup`
  (needs only `θ ≠ 1`; degree-one not used).
* **(c2)** Hyp (4.6): the inertia bridge `inertia_eq_H_of_c2` from
  `CertainTypeHypothesis.centralizer_W2` + Hall coprimality + Isaacs 3.28 on `H/H'` (T6 §5). -/
theorem isIrreducibleCharacter_induce_of_degree_one (hyp : SibleyDadeHypothesis G L H)
    {θ : IrreducibleCharacter ↥H}
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hθ_ne : θ ≠ trivialIrreducibleCharacter ↥H) :
    IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rcases hyp.cases with hF | ⟨h46, _hdade, hK, hW1, _hprime, hW2, hcop⟩
  · exact isIrreducibleCharacter_induce_of_frobeniusGroup hF θ hθ_ne
  · -- (c2) inertia bridge: `I_L(θ) = H` via the abelian quotient `H/⁅H,H⁆` (Brauer + Isaacs 3.28).
    -- `cases` now carries the full `Hypothesis46`; project to the underlying `CertainTypeHypothesis`.
    exact isIrreducibleCharacter_induce_of_inertia_eq θ
      (hyp.inertia_eq_H_of_c2 h46.toCertainTypeHypothesis hK hW1 hW2 hcop hθ_one hθ_ne)

/-- **(6.8) `Y = S(H')` coherence (engine call from a constructed family).**  Given a family of
nontrivial linear source characters `χ_j : H →* ℂˣ` indexed by `Fin n` (`n ≥ 2`), pairwise
non-`L`-conjugate, with each `Ind_H^L (linear χ_j)` irreducible (`hirr`), the induced family
`Y = {Ind_H^L (linear χ_j)}` is coherent for Sibley's Dade map `tau`.

This is the (6.8) `Y`-step: the `χ_j` are the `Irr(H/H') ∖ {1}` orbit representatives (degree one,
so each `Ind` has the common degree `|W₁|`).  `hirr` and the pairwise non-conjugacy come from the
free `W₁`-action (`isIrreducibleCharacter_induce_of_degree_one`).  Injectivity of
`j ↦ Ind_H^L (linear χ_j)` is the cross-Mackey orthogonality `inner_induce_eq_zero_of_not_conj`;
the equal-degree coherence is then `coherentInducedDegreeOneFamily`. -/
noncomputable def coherentYFamily (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (χ : Fin n → (↥H →* ℂˣ))
    (hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j))
    (hirr : ∀ j, IsIrreducibleCharacter
      (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ))) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (Set.range (fun j => ClassFunction.induce H
        (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hηinj : Function.Injective
      (fun j => (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
        hirr j⟩ : IrreducibleCharacter ↥L)) := by
    intro i j hij
    by_contra hne
    have h0 := inner_induce_eq_zero_of_not_conj
      (linearIrreducibleCharacter (χ i)) (linearIrreducibleCharacter (χ j))
      (fun g => hpairwise i j hne g)
    have hcoe : ClassFunction.induce H (linearIrreducibleCharacter (χ i) : ClassFunction ↥H ℂ) =
        ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ) :=
      congrArg Subtype.val hij
    rw [hcoe] at h0
    have h1 : ClassFunction.inner
        (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ))
        (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)) = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite
        (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
          hirr j⟩ : IrreducibleCharacter ↥L)
        (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ), hirr j⟩)
    rw [h1] at h0
    exact one_ne_zero h0
  exact coherentInducedDegreeOneFamily hyp hn
    (fun j => linearIrreducibleCharacter (χ j))
    (fun j => ⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
      hirr j⟩)
    (fun _ => rfl) hηinj (fun j => linearIrreducibleCharacter_apply_one (χ j))

/-- **(6.8) `Y = S(H')` coherence, with induced irreducibility discharged internally.**
Compared with `coherentYFamily`, the caller supplies only nontrivial linear source characters and
pairwise non-`L`-conjugacy.  The irreducibility of each induced member is the genuine T6/c1-c2
brick `isIrreducibleCharacter_induce_of_degree_one`, not an extra hypothesis. -/
noncomputable def coherentYFamily_of_pairwiseNonconj
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (χ : Fin n → (↥H →* ℂˣ))
    (hχ_ne : ∀ j, χ j ≠ 1)
    (hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j)) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (Set.range (fun j => ClassFunction.induce H
        (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  refine hyp.coherentYFamily hn χ hpairwise ?_
  intro j
  exact hyp.isIrreducibleCharacter_induce_of_degree_one
    (linearIrreducibleCharacter_apply_one (χ j)) (by
      rw [Ne, linearIrreducibleCharacter_eq_trivial_iff]
      exact hχ_ne j)

/-! ### Peterfalvi (6.8) `X`-characterization (T7): the sets `S(A)`, `X = S − S(Z)`, `Y = S(H')`

mmd 04.8 L150-164.  The (6.8) proof denotes `H' = [H,H]`, sets `Z = Z(H) ∩ H'` in case (A) and
`Z = W₂` in case (B), and forms `X = S − S(Z)`, `Y = S(H')` (`Z ⊆ H'` makes `X ∩ Y = ∅`).
`S(A)` is the (6.1) filtration: the members of `S` whose source `θ` has `A` in its kernel. -/

/-- **Peterfalvi (6.1) filtration `S(A)`** in the (6.8) setup: the members `Ind_H^L θ` of `S`
(`θ ∈ Irr H`, `θ ≠ 1_H`) whose source `θ` has `A` (as a subgroup of `H`) inside its kernel.
`S(1) = S`, and the (6.8) sets are `X = S − S(Z)` and `Y = S(H')`. -/
def SsubFiltration (_hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  {φ : ClassFunction ↥L ℂ | ∃ θ : IrreducibleCharacter ↥H,
    θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
    (A.subgroupOf H : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) ∧
    φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ)}

/-- The (6.8) set `X = S − S(Z)` (the (6.6) `X`-set) for a normal `Z ⊆ Z(H)`. -/
def Xset (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  hyp.S \ hyp.SsubFiltration Z

/-- The (6.8) set `Y = S(H')` (`H' = [H,H]`), the equal-degree family handled by T6. -/
def Yset (hyp : SibleyDadeHypothesis G L H) : Set (ClassFunction ↥L ℂ) :=
  hyp.SsubFiltration ⁅H, H⁆

/-- **(6.8) case (A) central subgroup `Z = Z(H) ∩ H′`** (Peterfalvi (6.8), p.34: *"Set
`Z = Z(H) ∩ H′` in case (A)"*).  This is the **correct** `(6.6)` `Z` for the `X = S − S(Z)`
coherence step: it is **central in `H`** (so [Is] Cor 2.30 `exists_degree_sq_le_index` bounds
`θ(1)² ≤ |H:Z|`, making the per-step degree field fillable) and contained in `H′ = ⁅H,H⁆`.

The earlier capstone route mis-instantiated the `(6.6)` producer at `Z = ⁅H,H⁆`, which is **not**
central for class `≥ 3` `p`-groups (e.g. `UT(4,p)`), so its degree field `θχ² ≤ qtot ≤ |H:⁅H,H⁆|`
was unsatisfiable.  See `notes/peterfalvi/s08_6_8_blocker_central_Z.md`. -/
def centralCommutator (hyp : SibleyDadeHypothesis G L H) : Subgroup ↥L :=
  (Subgroup.center ↥H).map H.subtype ⊓ ⁅H, H⁆

theorem centralCommutator_le_commutator (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator ≤ ⁅H, H⁆ := by
  simp only [centralCommutator]; exact inf_le_right

theorem centralCommutator_le (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator ≤ H := by
  haveI := hyp.H_normal
  exact le_trans hyp.centralCommutator_le_commutator (Subgroup.commutator_le_left H H)

/-- `Z = Z(H) ∩ H′` is central in `H`: its trace `Z.subgroupOf H` lies in `Z(↥H)`.  This is the
hypothesis [Is] Cor 2.30 / `IsIrreducibleCharacter.exists_degree_sq_le_index` needs to bound
`θ(1)² ≤ |H : Z|` for the `(6.6)` per-step degree field. -/
theorem centralCommutator_subgroupOf_le_center (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator.subgroupOf H ≤ Subgroup.center ↥H := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  simp only [centralCommutator] at hx
  have hx2 : (x : ↥L) ∈ (Subgroup.center ↥H).map H.subtype := (Subgroup.mem_inf.mp hx).1
  rw [Subgroup.mem_map] at hx2
  obtain ⟨z, hz, hzx⟩ := hx2
  have hzx' : z = x := Subtype.ext (by simpa using hzx)
  rwa [← hzx']

/-- `Z = Z(H) ∩ H′` is normal in `L`: `(center ↥H).map H.subtype` is normal (characteristic in the
normal `H`, via `normal_of_characteristic_of_normal`) and `⁅H,H⁆` is normal, so their inf is. -/
instance centralCommutator_normal (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator.Normal := by
  haveI := hyp.H_normal
  haveI : (⁅H, H⁆ : Subgroup ↥L).Normal := Subgroup.commutator_normal H H
  simp only [centralCommutator]
  infer_instance

/-- `Z = Z(H) ∩ H′` traced into `H` is `Z(↥H) ⊓ commutator ↥H`. -/
theorem centralCommutator_subgroupOf_eq (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator.subgroupOf H
      = Subgroup.center ↥H ⊓ _root_.commutator ↥H := by
  have h1 : hyp.centralCommutator.subgroupOf H
      = ((Subgroup.center ↥H).map H.subtype).subgroupOf H
        ⊓ (⁅H, H⁆ : Subgroup ↥L).subgroupOf H := by
    rw [centralCommutator]; exact Subgroup.comap_inf _ _ _
  rw [h1, commutator_subgroupOf_self]
  congr 1
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

/-- `Z = Z(H) ∩ H′ ≠ 1` when `H` is non-abelian: a non-trivial nilpotent group has
`Z(H) ∩ H′ ≠ 1` (`isNilpotent_normal_inf_center_ne_bot` with `N = H′`). -/
theorem centralCommutator_ne_bot (hyp : SibleyDadeHypothesis G L H)
    (hHnonab : _root_.commutator ↥H ≠ ⊥) : hyp.centralCommutator ≠ ⊥ := by
  haveI := hyp.H_normal
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have hkey : Subgroup.center ↥H ⊓ _root_.commutator ↥H ≠ ⊥ := by
    rw [inf_comm]
    exact isNilpotent_normal_inf_center_ne_bot (Subgroup.commutator_normal ⊤ ⊤) hHnonab
  intro hbot
  apply hkey
  rw [← hyp.centralCommutator_subgroupOf_eq, hbot, Subgroup.bot_subgroupOf]

/-- **(6.8) case (B) centrality** (Peterfalvi (6.8), case (B): *"`1 ≠ W₂ ⊆ Z(H)`"*, mmd 04.8 L154).

In the CertainType branch `cert.W2 ≤ K = H` has prime order (`cert.W2` is cyclic of prime order
`w₂`), so the math-case split on `Z(H) ⊓ W₂` is a dichotomy (`eq_bot_or_eq_of_le_of_card_prime`):
either `Z(H) ⊓ W₂ = 1` (case A, handled at the central `Z = Z(H) ∩ H'`) or `W₂ ⊆ Z(H)` (case B).
This lemma extracts the case-(B) hypothesis `hB : Z(H) ⊓ W₂ ≠ 1` into the centrality
`W₂.subgroupOf H ≤ Z(↥H)` — the (6.6) / [Is] Cor 2.30 bound enabler at `Z = W₂`, the analogue of
`centralCommutator_subgroupOf_le_center`. -/
theorem W2_subgroupOf_le_center_of_caseB (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hprime : (Nat.card cert.W2).Prime)
    (hB : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H ≠ ⊥) :
    cert.W2.subgroupOf H ≤ Subgroup.center ↥H := by
  have hle : cert.W2 ≤ H := cert.W2_le_K.trans_eq hK
  haveI : Finite ↥H := Subtype.finite
  haveI : Finite (cert.W2.subgroupOf H) := Subtype.finite
  have hcard : Nat.card (cert.W2.subgroupOf H) = Nat.card cert.W2 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hpsub : (Nat.card (cert.W2.subgroupOf H)).Prime := by rw [hcard]; exact hprime
  rcases eq_bot_or_eq_of_le_of_card_prime inf_le_right hpsub with h | h
  · exact absurd h hB
  · exact le_of_eq_of_le h.symm inf_le_left

/-- **(c2)+math-(A) fixed-point-freeness on `Zc = Z(H) ∩ H'`** (Peterfalvi (6.8), case (A) in the
CertainType branch, i.e. `Z(H) ⊓ W₂ = 1`).  `W₁` acts fixed-point-freely on `Zc`: for `w ∈ W₁^#`,
`C_L(w) ⊓ Zc = 1`.  Indeed `C_L(w) ⊓ H = W₂` (`cert.centralizer_W2`) and `Zc ≤ H ⊓ Z(H).map`, so
`C_L(w) ⊓ Zc ≤ W₂ ⊓ (Z(H)).map = 1` (the lifted math-(A) hypothesis).  This is the `hZfpf` input
that `isIrreducibleCharacter_of_mem_Xset_caseA` (and the CB3 FPF generalization) needs at `Z = Zc`,
the (c2) analogue of the Frobenius fixed-point-free property. -/
theorem centralizer_inf_centralCommutator_eq_bot_of_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {w : ↥L} (hw : w ∈ hyp.W1) (hw1 : w ≠ 1) :
    Subgroup.centralizer ({w} : Set ↥L) ⊓ hyp.centralCommutator = ⊥ := by
  haveI := hyp.H_normal
  have hle : cert.W2 ≤ H := cert.W2_le_K.trans_eq hK
  -- `C_L(w) ⊓ H = W₂`
  have hCW2 : Subgroup.centralizer ({w} : Set ↥L) ⊓ H = cert.W2 := by
    have h := cert.centralizer_W2 w (hW1.symm ▸ hw) hw1
    rwa [hK] at h
  -- lift the math-(A) hypothesis from `↥H` to `↥L`: `(Z(H)).map ⊓ W₂ = ⊥`
  have hAmap : (Subgroup.center ↥H).map H.subtype ⊓ cert.W2 = ⊥ := by
    have h1 := congrArg (Subgroup.map H.subtype) hA
    rwa [Subgroup.map_inf _ _ H.subtype H.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at h1
  have hccZ : hyp.centralCommutator ≤ (Subgroup.center ↥H).map H.subtype := by
    simp only [centralCommutator]; exact inf_le_left
  rw [← le_bot_iff]
  calc Subgroup.centralizer ({w} : Set ↥L) ⊓ hyp.centralCommutator
      ≤ (Subgroup.centralizer ({w} : Set ↥L) ⊓ H) ⊓ (Subgroup.center ↥H).map H.subtype :=
        le_inf (le_inf inf_le_left (inf_le_right.trans hyp.centralCommutator_le))
          (inf_le_right.trans hccZ)
    _ = cert.W2 ⊓ (Subgroup.center ↥H).map H.subtype := by rw [hCW2]
    _ = ⊥ := by rw [inf_comm]; exact hAmap

/-- **(6.7)-wiring step (c): the centralizer in `↥L` of a nontrivial `z ∈ Z = Z(H) ∩ H′` is `H`.**
`z ∈ Z(H)` gives `H ≤ C_L(z)`; `z ∈ H^#` with `L` Frobenius (kernel `H`) gives `C_L(z) ≤ H`
(`centralizer_kernel_le`).  Hence `|C_L(z)| = |H|` is **constant on `Z^#`** — the `|C_L(·)|`-constancy
input of Peterfalvi (6.7). -/
theorem centralizer_centralCommutator_eq (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set ↥L) = H := by
  apply le_antisymm
  · exact hF.centralizer_kernel_le z (hyp.centralCommutator_le hz) hz1
  · intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzH : (z : ↥L) ∈ H := hyp.centralCommutator_le hz
    have hzc : (⟨z, hzH⟩ : ↥H) ∈ Subgroup.center ↥H :=
      hyp.centralCommutator_subgroupOf_le_center (Subgroup.mem_subgroupOf.mpr hz)
    have hcomm := (Subgroup.mem_center_iff.mp hzc) ⟨h, hh⟩
    have hcoe := congrArg (H.subtype) hcomm
    simpa using hcoe

/-- **(6.7)-wiring step (c), case (A) / c2 form: `C_↥L(z) = H` for `z ∈ Zc^#`.**  The (c2) analogue
of `centralizer_centralCommutator_eq` (which used `hF.centralizer_kernel_le`).  `H ≤ C_L(z)` since
`z ∈ Z(H)`; for `C_L(z) ≤ H`, decompose `g ∈ C_L(z)` via the complement `L = H ⋊ W₁`
(`cert.isComplement`, `cert.K = H`) as `g = k·w` (`k ∈ H`, `w ∈ W₁`): `k` centralizes `z` (central),
so `w = k⁻¹g` centralizes `z`; if `w ≠ 1` then `z ∈ C_L(w) ⊓ Zc = ⊥`
(`centralizer_inf_centralCommutator_eq_bot_of_c2_caseA`, the math-(A) FPF), contradicting `z ≠ 1`, so
`w = 1` and `g = k ∈ H`.  Gives the `|C_L(·)|`-constancy on `Zc^#` of Peterfalvi (6.7) without
Frobenius. -/
theorem centralizer_centralCommutator_eq_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set ↥L) = H := by
  haveI := hyp.H_normal
  have hzH : (z : ↥L) ∈ H := hyp.centralCommutator_le hz
  have hzc : (⟨z, hzH⟩ : ↥H) ∈ Subgroup.center ↥H :=
    hyp.centralCommutator_subgroupOf_le_center (Subgroup.mem_subgroupOf.mpr hz)
  apply le_antisymm
  · -- `C_L(z) ≤ H`
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg  -- `hg : g * z = z * g`
    -- `g = k·w` via the complement `L = H ⋊ W₁`
    obtain ⟨⟨⟨k, hk⟩, ⟨w, hw⟩⟩, hkw, -⟩ := Subgroup.IsComplement.existsUnique cert.isComplement g
    simp only at hkw  -- `hkw : k * w = g`
    rw [hK] at hk
    rw [hW1] at hw
    -- `k` centralizes `z` (central in `H`)
    have hkz : k * z = z * k := by
      have h := (Subgroup.mem_center_iff.mp hzc) ⟨k, hk⟩
      have hcoe := congrArg (H.subtype) h
      simpa using hcoe
    -- `w` centralizes `z`
    have hwz : w * z = z * w := by
      have h1 : k * (w * z) = k * (z * w) := by
        calc k * (w * z) = (k * w) * z := by rw [mul_assoc]
          _ = g * z := by rw [hkw]
          _ = z * g := hg
          _ = z * (k * w) := by rw [← hkw]
          _ = (z * k) * w := by rw [mul_assoc]
          _ = (k * z) * w := by rw [← hkz]
          _ = k * (z * w) := by rw [mul_assoc]
      exact mul_left_cancel h1
    by_cases hw1 : w = 1
    · rw [hw1, mul_one] at hkw
      rw [← hkw]; exact hk
    · exfalso
      have hzC : z ∈ Subgroup.centralizer ({w} : Set ↥L) := by
        rw [Subgroup.mem_centralizer_singleton_iff]; exact hwz.symm
      have hmem : z ∈ Subgroup.centralizer ({w} : Set ↥L) ⊓ hyp.centralCommutator := ⟨hzC, hz⟩
      rw [hyp.centralizer_inf_centralCommutator_eq_bot_of_c2_caseA hK hW1 hA hw hw1,
        Subgroup.mem_bot] at hmem
      exact hz1 hmem
  · -- `H ≤ C_L(z)` (`z ∈ Z(H)`)
    intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := (Subgroup.mem_center_iff.mp hzc) ⟨h, hh⟩
    have hcoe := congrArg (H.subtype) hcomm
    simpa using hcoe

/-- **(6.7)-wiring step (c′): the ambient-`G` form `(L:Subgroup G) ⊓ C_G(↑w) = H.map L.subtype`.**
Realizes `centralizer_centralCommutator_eq` (`C_↥L(w) = H`) in `G`: an element `g ∈ L` centralizes
`↑w` iff (as an element of `↥L`) it centralizes `w`, iff it lies in `H = C_↥L(w)`.  Hence
`|N_G(Ĥ) ⊓ C_G(w)| = |C_L(w)| = |Ĥ|` is **constant on `Z^#`** (`N_G(Ĥ) = L`), the centralizer-card
clause of Peterfalvi (6.7)'s `hconst`. -/
theorem inf_centralizer_centralCommutator_map (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {w : ↥L} (hw : w ∈ hyp.centralCommutator) (hw1 : w ≠ 1) :
    (L : Subgroup G) ⊓ Subgroup.centralizer ({(w : G)} : Set G) = H.map L.subtype := by
  have hCH := hyp.centralizer_centralCommutator_eq hF hw hw1
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hgL, hgc⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    refine Subgroup.mem_map.mpr ⟨⟨g, hgL⟩, ?_, rfl⟩
    rw [← hCH, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (by simpa using hgc)
  · intro hg
    obtain ⟨c, hcH, rfl⟩ := Subgroup.mem_map.mp hg
    rw [← hCH, Subgroup.mem_centralizer_singleton_iff] at hcH
    refine ⟨c.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg (L.subtype) hcH
    simpa using this

/-- **(6.7)-wiring step (c′), case (A) / c2 form: `(L:Subgroup G) ⊓ C_G(↑w) = H.map L.subtype`.**  The
(c2) analogue of `inf_centralizer_centralCommutator_map`, supplying the centralizer-card constancy
clause of Peterfalvi (6.7)'s `hconst` from the case-(A) `C_↥L(w) = H`
(`centralizer_centralCommutator_eq_c2_caseA`).  The subgroup manipulation is identical to the
Frobenius form. -/
theorem inf_centralizer_centralCommutator_map_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {w : ↥L} (hw : w ∈ hyp.centralCommutator) (hw1 : w ≠ 1) :
    (L : Subgroup G) ⊓ Subgroup.centralizer ({(w : G)} : Set G) = H.map L.subtype := by
  haveI := hyp.H_normal
  have hCH := hyp.centralizer_centralCommutator_eq_c2_caseA hK hW1 hA hw hw1
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hgL, hgc⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    refine Subgroup.mem_map.mpr ⟨⟨g, hgL⟩, ?_, rfl⟩
    rw [← hCH, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (by simpa using hgc)
  · intro hg
    obtain ⟨c, hcH, rfl⟩ := Subgroup.mem_map.mp hg
    rw [← hCH, Subgroup.mem_centralizer_singleton_iff] at hcH
    refine ⟨c.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg (L.subtype) hcH
    simpa using this

/-- **(6.8.3) case-(A) fixed-point-free bound** `|Z| ≥ 2|W₁| + 1` (hence `|Z| − 1 ≥ 2|W₁|`).
`W₁` acts fixed-point-freely on `H` (`hF.toFrobeniusAction`), and `Z.subgroupOf H = Z(↥H) ⊓ H′` is
characteristic, so the action restricts fixed-point-freely to it (`IsFrobeniusAction.subgroup`);
`card_modEq_one` gives `|Z| ≡ 1 (mod |W₁|)`, and as `|Z|, |W₁|` are odd and `|Z| > 1`
(`H` non-abelian), `two_mul_add_one_le_of_odd_dvd` yields `2|W₁| + 1 ≤ |Z|`. -/
theorem centralCommutator_card_subgroupOf_lower (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥) :
    2 * Nat.card hyp.W1 + 1 ≤ Nat.card ↥(hyp.centralCommutator.subgroupOf H) := by
  classical
  letI : H.Normal := hyp.H_normal
  letI actH : MulDistribMulAction ↥hyp.W1 ↥H :=
    MulDistribMulAction.compHom H ((MulAut.conjNormal (H := H)).comp hyp.W1.subtype)
  have hFrobH : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥hyp.W1 ↥H := hF.toFrobeniusAction
  have hMeq : hyp.centralCommutator.subgroupOf H = Subgroup.center ↥H ⊓ _root_.commutator ↥H :=
    hyp.centralCommutator_subgroupOf_eq
  have hcprod : ∀ (K : Subgroup ↥H) [K.Characteristic] (a : ↥hyp.W1) (m : ↥H),
      m ∈ K → a • m ∈ K := by
    intro K _ a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp ‹K.Characteristic›
      (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a)
    have hmem : (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a).toMonoidHom m ∈ K := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  have hinv : ∀ a : ↥hyp.W1, ∀ m ∈ hyp.centralCommutator.subgroupOf H,
      a • m ∈ hyp.centralCommutator.subgroupOf H := by
    intro a m hm
    rw [hMeq, Subgroup.mem_inf] at hm ⊢
    exact ⟨hcprod (Subgroup.center ↥H) a m hm.1, hcprod (_root_.commutator ↥H) a m hm.2⟩
  letI instM : MulDistribMulAction ↥hyp.W1 ↥(hyp.centralCommutator.subgroupOf H) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantSubgroupMulDistribMulAction _ hinv
  have hFrobM : @OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥hyp.W1
      ↥(hyp.centralCommutator.subgroupOf H) _ _ instM := hFrobH.subgroup _ hinv
  haveI : Fintype ↥hyp.W1 := Fintype.ofFinite _
  haveI : Fintype ↥(hyp.centralCommutator.subgroupOf H) := Fintype.ofFinite _
  have hMmod : Nat.card ↥(hyp.centralCommutator.subgroupOf H) ≡ 1 [MOD Nat.card hyp.W1] := by
    simpa only [Fintype.card_eq_nat_card] using hFrobM.card_modEq_one
  have hMne : hyp.centralCommutator.subgroupOf H ≠ ⊥ := by
    rw [hMeq, inf_comm]
    letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
    exact isNilpotent_normal_inf_center_ne_bot (Subgroup.commutator_normal ⊤ ⊤) hHnonab
  have hMgt1 : 1 < Nat.card ↥(hyp.centralCommutator.subgroupOf H) := by
    haveI : Nontrivial ↥(hyp.centralCommutator.subgroupOf H) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hMne
    exact Finite.one_lt_card
  have hRdvd : Nat.card hyp.W1 ∣ Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1 :=
    (Nat.modEq_iff_dvd' (by omega)).mp hMmod.symm
  have hW1odd : Odd (Nat.card hyp.W1) :=
    Odd.of_dvd_nat hyp.card_L_odd (Subgroup.card_subgroup_dvd_card hyp.W1)
  have hModd : Odd (Nat.card ↥(hyp.centralCommutator.subgroupOf H)) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hyp.card_L_odd (Subgroup.card_subgroup_dvd_card H))
      (Subgroup.card_subgroup_dvd_card (hyp.centralCommutator.subgroupOf H))
  exact two_mul_add_one_le_of_odd_dvd hW1odd hModd hRdvd hMgt1

/-- **(6.8.3) case-(A) fixed-point-free bound, c2 form** `|Zc| ≥ 2|W₁| + 1`.  The (c2) analogue of
`centralCommutator_card_subgroupOf_lower` (which used `hF.toFrobeniusAction`).  `W₁` acts on `H` by
conjugation, restricting (characteristic `Z(H) ⊓ H′`) to `Zc.subgroupOf H`; the restricted action is
fixed-point-free *not* from a global Frobenius action but from the math-(A) FPF on `Zc`
(`centralizer_inf_centralCommutator_eq_bot_of_c2_caseA`: `C_L(w) ⊓ Zc = ⊥` for `w ∈ W₁^#`), giving
`|Zc| ≡ 1 (mod |W₁|)` and then `2|W₁| + 1 ≤ |Zc|`. -/
theorem centralCommutator_card_subgroupOf_lower_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥) :
    2 * Nat.card hyp.W1 + 1 ≤ Nat.card ↥(hyp.centralCommutator.subgroupOf H) := by
  classical
  letI : H.Normal := hyp.H_normal
  letI actH : MulDistribMulAction ↥hyp.W1 ↥H :=
    MulDistribMulAction.compHom H ((MulAut.conjNormal (H := H)).comp hyp.W1.subtype)
  have hMeq : hyp.centralCommutator.subgroupOf H = Subgroup.center ↥H ⊓ _root_.commutator ↥H :=
    hyp.centralCommutator_subgroupOf_eq
  have hcprod : ∀ (K : Subgroup ↥H) [K.Characteristic] (a : ↥hyp.W1) (m : ↥H),
      m ∈ K → a • m ∈ K := by
    intro K _ a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp ‹K.Characteristic›
      (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a)
    have hmem : (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a).toMonoidHom m ∈ K := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  have hinv : ∀ a : ↥hyp.W1, ∀ m ∈ hyp.centralCommutator.subgroupOf H,
      a • m ∈ hyp.centralCommutator.subgroupOf H := by
    intro a m hm
    rw [hMeq, Subgroup.mem_inf] at hm ⊢
    exact ⟨hcprod (Subgroup.center ↥H) a m hm.1, hcprod (_root_.commutator ↥H) a m hm.2⟩
  letI instM : MulDistribMulAction ↥hyp.W1 ↥(hyp.centralCommutator.subgroupOf H) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantSubgroupMulDistribMulAction _ hinv
  -- FPF on `Zc.subgroupOf H` directly from the math-(A) FPF `C_L(w) ⊓ Zc = ⊥` (no global action).
  have hFrobM : @OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥hyp.W1
      ↥(hyp.centralCommutator.subgroupOf H) _ _ instM := by
    intro a ha m hm hfix
    apply hm
    -- `↑↑m ∈ Zc`
    have hmZc : ((m : ↥H) : ↥L) ∈ hyp.centralCommutator :=
      (Subgroup.mem_subgroupOf).mp m.2
    have ha1 : (hyp.W1.subtype a : ↥L) ≠ 1 := fun h => ha (Subtype.ext h)
    -- actH-fixedness of `↑m` (definitional from the invariant-subgroup action)
    have hfixH : a • (m : ↥H) = (m : ↥H) := Subtype.ext_iff.mp hfix
    have hc : MulAut.conjNormal (hyp.W1.subtype a) (m : ↥H) = (m : ↥H) := hfixH
    -- `↑a` centralizes `↑↑m`
    have hcomm : ((m : ↥H) : ↥L) ∈
        Subgroup.centralizer ({(hyp.W1.subtype a : ↥L)} : Set ↥L) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hL := congrArg (fun x : ↥H => (x : ↥L)) hc
      simp only [MulAut.conjNormal_apply] at hL
      rw [mul_inv_eq_iff_eq_mul] at hL
      exact hL.symm
    have hbot := hyp.centralizer_inf_centralCommutator_eq_bot_of_c2_caseA hK hW1 hA
      (w := (hyp.W1.subtype a : ↥L)) a.2 ha1
    have hmem : ((m : ↥H) : ↥L) ∈
        Subgroup.centralizer ({(hyp.W1.subtype a : ↥L)} : Set ↥L) ⊓ hyp.centralCommutator :=
      ⟨hcomm, hmZc⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext (Subtype.ext hmem)
  haveI : Fintype ↥hyp.W1 := Fintype.ofFinite _
  haveI : Fintype ↥(hyp.centralCommutator.subgroupOf H) := Fintype.ofFinite _
  have hMmod : Nat.card ↥(hyp.centralCommutator.subgroupOf H) ≡ 1 [MOD Nat.card hyp.W1] := by
    simpa only [Fintype.card_eq_nat_card] using hFrobM.card_modEq_one
  have hMne : hyp.centralCommutator.subgroupOf H ≠ ⊥ := by
    rw [hMeq, inf_comm]
    letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
    exact isNilpotent_normal_inf_center_ne_bot (Subgroup.commutator_normal ⊤ ⊤) hHnonab
  have hMgt1 : 1 < Nat.card ↥(hyp.centralCommutator.subgroupOf H) := by
    haveI : Nontrivial ↥(hyp.centralCommutator.subgroupOf H) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hMne
    exact Finite.one_lt_card
  have hRdvd : Nat.card hyp.W1 ∣ Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1 :=
    (Nat.modEq_iff_dvd' (by omega)).mp hMmod.symm
  have hW1odd : Odd (Nat.card hyp.W1) :=
    Odd.of_dvd_nat hyp.card_L_odd (Subgroup.card_subgroup_dvd_card hyp.W1)
  have hModd : Odd (Nat.card ↥(hyp.centralCommutator.subgroupOf H)) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hyp.card_L_odd (Subgroup.card_subgroup_dvd_card H))
      (Subgroup.card_subgroup_dvd_card (hyp.centralCommutator.subgroupOf H))
  exact two_mul_add_one_le_of_odd_dvd hW1odd hModd hRdvd hMgt1

/-- Membership in `S(A)`, unfolded. -/
theorem mem_SsubFiltration (hyp : SibleyDadeHypothesis G L H) {A : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} :
    φ ∈ hyp.SsubFiltration A ↔ ∃ θ : IrreducibleCharacter ↥H,
      θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
      (A.subgroupOf H : Set ↥H) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) ∧
      φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) :=
  Iff.rfl

/-- `S(⊥) = S`: the kernel condition `⊥ ⊆ Ker θ` is vacuous, so the bottom filtration is all of
`S`.  (Peterfalvi writes `S(1) = S`.) -/
theorem SsubFiltration_bot (hyp : SibleyDadeHypothesis G L H) :
    hyp.SsubFiltration ⊥ = hyp.S := by
  ext φ
  rw [hyp.mem_SsubFiltration, hyp.S_eq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨θ, hθ, -, hφ⟩
    exact ⟨θ, hθ, hφ⟩
  · rintro ⟨θ, hθ, hφ⟩
    refine ⟨θ, hθ, ?_, hφ⟩
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _

/-- Membership in `X = S − S(Z)`, unfolded. -/
theorem mem_Xset (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} :
    φ ∈ hyp.Xset Z ↔ φ ∈ hyp.S ∧ φ ∉ hyp.SsubFiltration Z :=
  Iff.rfl

/-- Every member of the filtration `S(A)` is a member of the ambient set `S`. -/
theorem SsubFiltration_subset_S (hyp : SibleyDadeHypothesis G L H) {A : Subgroup ↥L} :
    hyp.SsubFiltration A ⊆ hyp.S := by
  intro φ hφ
  rw [hyp.mem_SsubFiltration] at hφ
  obtain ⟨θ, hθ_ne, _hker, hφeq⟩ := hφ
  rw [hyp.S_eq]
  exact ⟨θ, hθ_ne, hφeq⟩

/-- `X(Z) = S - S(Z)` is contained in `S`. -/
theorem Xset_subset_S (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L} :
    hyp.Xset Z ⊆ hyp.S := by
  intro φ hφ
  exact (hyp.mem_Xset.mp hφ).1

/-- `Y = S(H')` is contained in `S`. -/
theorem Yset_subset_S (hyp : SibleyDadeHypothesis G L H) :
    hyp.Yset ⊆ hyp.S := by
  intro φ hφ
  rw [Yset] at hφ
  exact hyp.SsubFiltration_subset_S hφ

/-- `X(Z) = S - S(Z)` is disjoint from `S(Z)`. -/
theorem disjoint_Xset_SsubFiltration
    (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    Disjoint (hyp.Xset Z) (hyp.SsubFiltration Z) := by
  rw [Set.disjoint_left]
  intro φ hφX hφZ
  exact (hyp.mem_Xset.mp hφX).2 hφZ

/-- `X(Z)` and `S(Z)` partition `S`. -/
theorem Xset_union_SsubFiltration_eq_S
    (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    hyp.Xset Z ∪ hyp.SsubFiltration Z = hyp.S := by
  ext φ
  constructor
  · intro hφ
    rcases hφ with hφX | hφZ
    · exact hyp.Xset_subset_S hφX
    · exact hyp.SsubFiltration_subset_S hφZ
  · intro hφS
    by_cases hφZ : φ ∈ hyp.SsubFiltration Z
    · exact Or.inr hφZ
    · exact Or.inl (hyp.mem_Xset.mpr ⟨hφS, hφZ⟩)

/-- The Peterfalvi filtration is antitone: a larger subgroup imposes a stronger kernel
condition. -/
theorem SsubFiltration_antitone
    (hyp : SibleyDadeHypothesis G L H) {A B : Subgroup ↥L} (hAB : A ≤ B) :
    hyp.SsubFiltration B ⊆ hyp.SsubFiltration A := by
  intro φ hφ
  rw [hyp.mem_SsubFiltration] at hφ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hφ
  refine ⟨θ, hθ_ne, ?_, hφeq⟩
  intro x hxA
  exact hker (Subgroup.mem_subgroupOf.mpr (hAB (Subgroup.mem_subgroupOf.mp hxA)))

/-- `X(A) = S - S(A)` grows with the subgroup parameter. -/
theorem Xset_mono
    (hyp : SibleyDadeHypothesis G L H) {A B : Subgroup ↥L} (hAB : A ≤ B) :
    hyp.Xset A ⊆ hyp.Xset B := by
  intro φ hφ
  obtain ⟨hφS, hφnotA⟩ := hyp.mem_Xset.mp hφ
  exact hyp.mem_Xset.mpr ⟨hφS, fun hφB => hφnotA (hyp.SsubFiltration_antitone hAB hφB)⟩

/-- If `Z ≤ H'`, then the larger capstone set `S - S(H')` splits into the smaller
`X(Z) = S - S(Z)` plus the filtration layer between `Z` and `H'`.  This is the set-theoretic
bridge needed by the case-A/case-B route, where the textbook first proves coherence for a smaller
central/fixed-point-free subgroup `Z`. -/
theorem Xset_commutator_eq_Xset_union_filtrationDiff
    (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L} (hZH' : Z ≤ ⁅H, H⁆) :
    hyp.Xset ⁅H, H⁆ =
      hyp.Xset Z ∪ (hyp.SsubFiltration Z \ hyp.SsubFiltration ⁅H, H⁆) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨hφS, hφnotH'⟩ := hyp.mem_Xset.mp hφ
    by_cases hφZ : φ ∈ hyp.SsubFiltration Z
    · exact Or.inr ⟨hφZ, hφnotH'⟩
    · exact Or.inl (hyp.mem_Xset.mpr ⟨hφS, hφZ⟩)
  · rintro (hφZ | ⟨hφFilZ, hφnotH'⟩)
    · exact hyp.Xset_mono hZH' hφZ
    · exact hyp.mem_Xset.mpr ⟨hyp.SsubFiltration_subset_S hφFilZ, hφnotH'⟩

/-- The (6.8) sets `X = S - S(H')` and `Y = S(H')` are disjoint. -/
theorem disjoint_Xset_Yset (hyp : SibleyDadeHypothesis G L H) :
    Disjoint (hyp.Xset ⁅H, H⁆) hyp.Yset := by
  simpa [Yset] using hyp.disjoint_Xset_SsubFiltration (Z := ⁅H, H⁆)

/-- The (6.8) sets `X = S - S(H')` and `Y = S(H')` partition `S`. -/
theorem Xset_union_Yset_eq_S (hyp : SibleyDadeHypothesis G L H) :
    hyp.Xset ⁅H, H⁆ ∪ hyp.Yset = hyp.S := by
  simpa [Yset] using hyp.Xset_union_SsubFiltration_eq_S (Z := ⁅H, H⁆)

/-- A nontrivial irreducible character remains nontrivial after complex conjugation. -/
theorem irreducibleCharacter_conj_ne_trivial {Γ : Type*} [Group Γ] [Finite Γ]
    {θ : IrreducibleCharacter Γ}
    (hθ_ne : θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ) :
    (⟨(θ : ClassFunction Γ ℂ).conj, θ.isIrreducible.conj⟩ :
      IrreducibleCharacter Γ) ≠
        OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ := by
  intro hθc
  apply hθ_ne
  apply IrreducibleCharacter.ext
  have hval : (θ : ClassFunction Γ ℂ).conj =
      (OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ :
        ClassFunction Γ ℂ) := by
    simpa using congrArg
      (fun η : IrreducibleCharacter Γ => (η : ClassFunction Γ ℂ)) hθc
  calc
    (θ : ClassFunction Γ ℂ) = ((θ : ClassFunction Γ ℂ).conj).conj := by
      rw [ClassFunction.conj_conj]
    _ = (OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ :
        ClassFunction Γ ℂ).conj := by
      rw [hval]
    _ = (OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ :
        ClassFunction Γ ℂ) := by
      ext x
      simp

/-- `S = {Ind_H^L θ | θ ∈ Irr(H), θ ≠ 1}` is finite, directly from the finite source
irreducible-character set. -/
theorem S_finite (hyp : SibleyDadeHypothesis G L H) :
    hyp.S.Finite := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Finite (IrreducibleCharacter ↥H) :=
    OddOrder.RepresentationTheory.finite_irreducibleCharacter (G := ↥H)
  refine (Set.finite_range
    (fun θ : {θ : IrreducibleCharacter ↥H //
      θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H} =>
      ClassFunction.induce H (θ.1 : ClassFunction ↥H ℂ))).subset ?_
  intro φ hφ
  rw [hyp.S_eq] at hφ
  obtain ⟨θ, hθ_ne, hφeq⟩ := hφ
  exact ⟨⟨θ, hθ_ne⟩, hφeq.symm⟩

/-- Every filtration layer `S(A)` is finite, because it is a subset of `S`. -/
theorem SsubFiltration_finite (hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L) :
    (hyp.SsubFiltration A).Finite :=
  hyp.S_finite.subset hyp.SsubFiltration_subset_S

/-- `X(Z) = S - S(Z)` is finite, because it is a subset of `S`. -/
theorem Xset_finite (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    (hyp.Xset Z).Finite :=
  hyp.S_finite.subset hyp.Xset_subset_S

/-- `S` is closed under complex conjugation.  This is a source-side fact:
`conj (Ind_H^L θ) = Ind_H^L (conj θ)`. -/
theorem S_closedUnderConjugate (hyp : SibleyDadeHypothesis G L H) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate hyp.S := by
  intro φ hφ
  rw [hyp.S_eq] at hφ ⊢
  obtain ⟨θ, hθ_ne, hφeq⟩ := hφ
  let θc : IrreducibleCharacter ↥H :=
    ⟨(θ : ClassFunction ↥H ℂ).conj, θ.isIrreducible.conj⟩
  refine ⟨θc, irreducibleCharacter_conj_ne_trivial hθ_ne, ?_⟩
  rw [hφeq]
  simpa [θc] using ClassFunction.induce_conj H (θ : ClassFunction ↥H ℂ)

/-- Each Peterfalvi filtration layer `S(A)` is closed under complex conjugation.  The
kernel condition is preserved by conjugating the source character. -/
theorem SsubFiltration_closedUnderConjugate
    (hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.SsubFiltration A) := by
  intro φ hφ
  rw [hyp.mem_SsubFiltration] at hφ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hφ
  let θc : IrreducibleCharacter ↥H :=
    ⟨(θ : ClassFunction ↥H ℂ).conj, θ.isIrreducible.conj⟩
  refine ⟨θc, irreducibleCharacter_conj_ne_trivial hθ_ne, ?_, ?_⟩
  · simpa [θc, OddOrder.Peterfalvi.S03.characterKernel_conj] using hker
  · rw [hφeq]
    simpa [θc] using ClassFunction.induce_conj H (θ : ClassFunction ↥H ℂ)

/-- `X(Z) = S - S(Z)` is closed under complex conjugation, without first proving
`X(Z) ⊆ Irr(L)`. -/
theorem Xset_closedUnderConjugate_unconditional
    (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) := by
  intro φ hφ
  obtain ⟨hφS, hφnotZ⟩ := hyp.mem_Xset.mp hφ
  refine hyp.mem_Xset.mpr ⟨hyp.S_closedUnderConjugate hφS, ?_⟩
  intro hφcZ
  have hφccZ := hyp.SsubFiltration_closedUnderConjugate Z hφcZ
  exact hφnotZ (by simpa [ClassFunction.conj_conj] using hφccZ)

/-- **Peterfalvi (6.2), filtration form.**  If the quotient `H/A` has nontrivial
abelianization, then the filtration layer `S(A)` is nonempty.

The source character is the degree-one irreducible obtained on `H/A`, inflated to `H`; inducing it
to `L` gives an element of the Peterfalvi filtration by construction. -/
theorem SsubFiltration_nonempty_of_commutator_quotient_ne_top
    (hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L)
    [(A.subgroupOf H).Normal]
    (hcomm : commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤) :
    (hyp.SsubFiltration A).Nonempty := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  obtain ⟨θ, hθ_ne, hker, _hdeg⟩ :=
    exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top
      (K := ↥H) (A.subgroupOf H) hcomm
  refine ⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), ?_⟩
  rw [hyp.mem_SsubFiltration]
  exact ⟨θ, hθ_ne, hker, rfl⟩

/-- **Peterfalvi (6.2), solvable quotient form.**  A nontrivial finite solvable quotient `H/A`
has proper commutator subgroup, hence supplies a nontrivial degree-one source character and a
member of `S(A)`. -/
theorem SsubFiltration_nonempty_of_nontrivial_solvable_quotient
    (hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L)
    [(A.subgroupOf H).Normal] [IsSolvable (↥H ⧸ A.subgroupOf H)]
    [Nontrivial (↥H ⧸ A.subgroupOf H)] :
    (hyp.SsubFiltration A).Nonempty :=
  hyp.SsubFiltration_nonempty_of_commutator_quotient_ne_top A
    (IsSolvable.commutator_lt_top_of_nontrivial
      (G := ↥H ⧸ A.subgroupOf H)).ne

/-- **Peterfalvi (6.2), proper nilpotent quotient form.**  If `A` is a proper
normal subgroup of the nilpotent kernel `H`, then the filtration layer `S(A)` is nonempty.

The quotient `H/A` is nontrivial and nilpotent, hence solvable, so the solvable-quotient
filtration form supplies a nontrivial degree-one source character. -/
theorem SsubFiltration_nonempty_of_subgroupOf_ne_top
    (hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L)
    [(A.subgroupOf H).Normal] (hA : A.subgroupOf H ≠ ⊤) :
    (hyp.SsubFiltration A).Nonempty := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  haveI : Group.IsNilpotent (↥H ⧸ A.subgroupOf H) :=
    nilpotent_of_surjective (QuotientGroup.mk' (A.subgroupOf H))
      (QuotientGroup.mk'_surjective (A.subgroupOf H))
  haveI : IsSolvable (↥H ⧸ A.subgroupOf H) := IsNilpotent.to_isSolvable
  haveI : Nontrivial (↥H ⧸ A.subgroupOf H) :=
    Subgroup.nontrivial_quotient_of_ne_top hA
  exact hyp.SsubFiltration_nonempty_of_nontrivial_solvable_quotient A

/-- A nontrivial linear source character induces to a member of `Y = S(H')`.

The witness in `S(H')` is `linearIrreducibleCharacter χ`.  Its kernel contains
`H' = [H,H]` because a degree-one character kills commutators. -/
theorem induce_linearIrreducibleCharacter_mem_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {χ : ↥H →* ℂˣ}
    (hχ_ne : χ ≠ 1) :
    ClassFunction.induce H (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) ∈
      hyp.Yset := by
  rw [Yset]
  refine ⟨linearIrreducibleCharacter χ, ?_, ?_, rfl⟩
  · rw [Ne, linearIrreducibleCharacter_eq_trivial_iff]
    exact hχ_ne
  · intro x hx
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def, linearIrreducibleCharacter_apply_one]
    have hsubgroupOf_eq :
        ((⁅H, H⁆ : Subgroup ↥L).subgroupOf H) = _root_.commutator ↥H := by
      rw [← Subgroup.map_subtype_commutator H, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    have hxcomm : x ∈ _root_.commutator ↥H := by
      rwa [hsubgroupOf_eq] at hx
    have hxclosure : x ∈ Subgroup.closure (commutatorSet ↥H) := by
      rwa [_root_.commutator_eq_closure] at hxcomm
    refine Subgroup.closure_induction
      (p := fun y _ => (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) y = 1)
      ?_ ?_ ?_ ?_ hxclosure
    · rintro _ ⟨a, b, rfl⟩
      have hlin := (linearIrreducibleCharacter χ).isIrreducible
      exact hlin.apply_commutatorElement_eq_one_of_apply_one_eq_one
        (linearIrreducibleCharacter_apply_one χ) a b
    · exact linearIrreducibleCharacter_apply_one χ
    · intro a b _ _ ha hb
      rw [(linearIrreducibleCharacter χ).isIrreducible.map_mul_of_apply_one_eq_one
        (linearIrreducibleCharacter_apply_one χ), ha, hb, one_mul]
    · intro a _ ha
      have hai := (linearIrreducibleCharacter χ).isIrreducible.map_mul_of_apply_one_eq_one
        (linearIrreducibleCharacter_apply_one χ) a a⁻¹
      rw [mul_inv_cancel, linearIrreducibleCharacter_apply_one χ, ha, one_mul] at hai
      exact hai.symm


/-- A source character whose kernel contains `H'` comes from a linear character of `H`.

The proof factors the source through the abelianization `H/H'`; irreducible characters of a finite
commutative group are degree one, hence are `linearIrreducibleCharacter`s, and pulling that linear
character back along `Abelianization.of` recovers the original source. -/
theorem exists_linearIrreducibleCharacter_eq_of_YsetSource
    (_hyp : SibleyDadeHypothesis G L H) {θ : IrreducibleCharacter ↥H}
    (hker : (((⁅H, H⁆ : Subgroup ↥L).subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ))) :
    ∃ χ : ↥H →* ℂˣ,
      (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) = (θ : ClassFunction ↥H ℂ) := by
  classical
  have hsubgroupOf_eq :
      ((⁅H, H⁆ : Subgroup ↥L).subgroupOf H) = _root_.commutator ↥H := by
    rw [← Subgroup.map_subtype_commutator H, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  let q : ↥H →* Abelianization ↥H := Abelianization.of
  have hq_surj : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (_root_.commutator ↥H) y
    exact ⟨x, rfl⟩
  have hker_q :
      ((q.ker : Subgroup ↥H) : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro x hx
    apply hker
    have hxcomm : x ∈ _root_.commutator ↥H := by
      rwa [show q.ker = _root_.commutator ↥H by
        change Abelianization.of.ker = _root_.commutator ↥H
        exact Abelianization.ker_of ↥H] at hx
    rwa [hsubgroupOf_eq]
  obtain ⟨θbar, hθbar⟩ := exists_compHom_eq_of_subset_characterKernel hq_surj θ hker_q
  haveI : Finite (Abelianization ↥H) := Finite.of_surjective q hq_surj
  obtain ⟨χbar, hχbar⟩ :=
    θbar.isIrreducible.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  refine ⟨χbar.comp q, ?_⟩
  rw [← ClassFunction.compHom_linearIrreducibleCharacter, hχbar, hθbar]

/-- Every member of `Y = S(H')` is induced from a nontrivial linear character of `H`. -/
theorem exists_linear_source_of_mem_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Yset) :
    ∃ χ : ↥H →* ℂˣ, χ ≠ 1 ∧
      φ = ClassFunction.induce H
        (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) := by
  rw [Yset, SsubFiltration] at hφ
  obtain ⟨θ, hθ_ne, hker, hφ⟩ := hφ
  obtain ⟨χ, hχθ⟩ := hyp.exists_linearIrreducibleCharacter_eq_of_YsetSource hker
  refine ⟨χ, ?_, ?_⟩
  · intro hχ
    apply hθ_ne
    apply IrreducibleCharacter.ext
    rw [← hχθ]
    exact congrArg (fun η : IrreducibleCharacter ↥H => (η : ClassFunction ↥H ℂ))
      ((linearIrreducibleCharacter_eq_trivial_iff (χ := χ)).mpr hχ)
  · rw [hφ, ← hχθ]

/-- `Y = S(H')` is exactly the image of the nontrivial linear characters of `H` under induction. -/
theorem mem_Yset_iff_exists_linear_source
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {φ : ClassFunction ↥L ℂ} :
    φ ∈ hyp.Yset ↔ ∃ χ : ↥H →* ℂˣ, χ ≠ 1 ∧
      φ = ClassFunction.induce H
        (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) := by
  constructor
  · exact hyp.exists_linear_source_of_mem_Yset
  · rintro ⟨χ, hχ_ne, rfl⟩
    exact hyp.induce_linearIrreducibleCharacter_mem_Yset hχ_ne

/-- Every `Y = S(H')` member has degree `|W₁|` (`Ind_H^L` of a degree-`1` source of `H`).  The
common degree of the equal-degree `Y`-family; used for the equal-degree difference support
(`sMember_diffSupport_of_charValue_eq`) in the (6.8.1) `himg_ortho`. -/
theorem Yset_apply_one (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Yset) :
    φ (1 : ↥L) = (Nat.card hyp.W1 : ℂ) := by
  obtain ⟨χ, _hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
  rw [hφeq]
  simpa [linearIrreducibleCharacter_coe] using
    hyp.induce_apply_one_eq_card_W1_of_degree_one
      (linearIrreducibleCharacter χ) (linearIrreducibleCharacter_apply_one χ)

/-- Family form of `induce_linearIrreducibleCharacter_mem_Yset`. -/
theorem range_induce_linearIrreducibleCharacter_subset_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ}
    (χ : Fin n → (↥H →* ℂˣ)) (hχ_ne : ∀ j, χ j ≠ 1) :
    Set.range (fun j => ClassFunction.induce H
      (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)) ⊆ hyp.Yset := by
  rintro φ ⟨j, rfl⟩
  exact hyp.induce_linearIrreducibleCharacter_mem_Yset (hχ_ne j)

/-- If an index family covers all nontrivial linear sources after induction, its induced range is
exactly `Y = S(H')`.

This is the orbit-representative form needed for (6.8): the family need only hit each induced
character in `Y`, not each nontrivial linear source before quotienting by `L`-conjugacy. -/
theorem range_induce_linearIrreducibleCharacter_eq_Yset_of_induce_surjective
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {ι : Type*}
    (χ : ι → (↥H →* ℂˣ)) (hχ_ne : ∀ j, χ j ≠ 1)
    (hχ_cover : ∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
      ClassFunction.induce H (linearClassFunction (χ j)) =
        ClassFunction.induce H (linearClassFunction η)) :
    Set.range (fun j => ClassFunction.induce H (linearClassFunction (χ j))) = hyp.Yset := by
  ext φ
  constructor
  · rintro ⟨j, rfl⟩
    simpa [linearIrreducibleCharacter_coe] using
      hyp.induce_linearIrreducibleCharacter_mem_Yset (hχ_ne j)
  · intro hφ
    obtain ⟨η, hη_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
    obtain ⟨j, hηj⟩ := hχ_cover η hη_ne
    refine ⟨j, ?_⟩
    rw [hφeq, linearIrreducibleCharacter_coe]
    exact hηj

/-- There are finitely many linear characters `Γ →* ℂˣ` for a finite group `Γ`.

Local to §8 because the immediate consumer is the finiteness of `Y = S(H')`; a more global API can
move this later if it gets reused outside the Peterfalvi assembly. -/
theorem finite_linearCharacters_of_finite {Γ : Type*} [Group Γ] [Finite Γ] :
    Finite (Γ →* ℂˣ) := by
  haveI : Finite (IrreducibleCharacter Γ) := finite_irreducibleCharacter (G := Γ)
  exact Finite.of_injective (linearIrreducibleCharacter (H := Γ))
    linearIrreducibleCharacter_injective

/-- `Y = S(H')` is finite: it is covered by inducing the finite set of nontrivial
linear source characters of `H`. -/
theorem Yset_finite (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    hyp.Yset.Finite := by
  classical
  haveI : Finite (↥H →* ℂˣ) := finite_linearCharacters_of_finite (Γ := ↥H)
  let T : Set (↥H →* ℂˣ) := {χ | χ ≠ 1}
  refine ((Set.toFinite T).image
    (fun χ => ClassFunction.induce H (linearClassFunction χ))).subset ?_
  intro φ hφ
  obtain ⟨χ, hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
  refine ⟨χ, hχ_ne, ?_⟩
  rw [hφeq, linearIrreducibleCharacter_coe]

/-- Every member of `Y = S(H')` is irreducible. -/
theorem isIrreducibleCharacter_of_mem_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Yset) :
    IsIrreducibleCharacter φ := by
  obtain ⟨χ, hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
  rw [hφeq]
  exact hyp.isIrreducibleCharacter_induce_of_degree_one
    (linearIrreducibleCharacter_apply_one χ) (by
      rw [Ne, linearIrreducibleCharacter_eq_trivial_iff]
      exact hχ_ne)

/-- Disjoint families of irreducible characters are orthogonal after passing to their
integer spans. -/
theorem inner_eq_zero_of_mem_span_of_disjoint_irreducible
    {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]
    {X Y : Set (ClassFunction Γ ℂ)}
    (hXirr : ∀ χ ∈ X, IsIrreducibleCharacter χ)
    (hYirr : ∀ η ∈ Y, IsIrreducibleCharacter η)
    (hdisj : Disjoint X Y) :
    ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner u v = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem χ hχ =>
      intro v hv
      refine OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan ?_ hv
      intro η hη
      have hχη : χ ≠ η := by
        intro h
        exact (Set.disjoint_left.mp hdisj) hχ (by simpa [← h] using hη)
      have hχirr : IsIrreducibleCharacter χ := hXirr χ hχ
      have hηirr : IsIrreducibleCharacter η := hYirr η hη
      have hneq :
          (⟨χ, hχirr⟩ : IrreducibleCharacter Γ) ≠ ⟨η, hηirr⟩ := by
        intro h
        exact hχη (congrArg Subtype.val h)
      simpa [hneq] using
        irreducibleCharacter_inner_eq_ite
          (⟨χ, hχirr⟩ : IrreducibleCharacter Γ) ⟨η, hηirr⟩
  | zero =>
      intro v _hv
      exact ClassFunction.inner_zero_left v
  | add x y _hx _hy ihx ihy =>
      intro v hv
      rw [ClassFunction.inner_add_left, ihx v hv, ihy v hv, zero_add]
  | smul a x _hx ih =>
      intro v hv
      rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, ih v hv, mul_zero]

/-- Source-side orthogonality of the (6.8) partition `X = S - S(H')` and `Y = S(H')`,
assuming the `X` side has already been shown irreducible. -/
theorem inner_span_Xset_Yset_eq_zero_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    (hXirr : ∀ φ ∈ hyp.Xset ⁅H, H⁆, IsIrreducibleCharacter φ) :
    ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner u v = 0 := by
  letI : H.Normal := hyp.H_normal
  exact inner_eq_zero_of_mem_span_of_disjoint_irreducible hXirr
    (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hyp.disjoint_Xset_Yset

/-- Enumerating `Yset` gives nontrivial linear source representatives for its induced members.

The returned family is indexed by `Fin n`, covers `Yset` after induction, and is pairwise
non-`L`-conjugate.  The cardinal lower bound is kept as an explicit input because the later
coherence engine requires `2 ≤ n`. -/
theorem exists_Yset_linearRepresentativeFamily
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] (hYtwo : 2 ≤ hyp.Yset.ncard) :
    ∃ (n : ℕ) (_ : NeZero n) (χ : Fin n → ↥H →* ℂˣ),
      2 ≤ n ∧
      (∀ j, χ j ≠ 1) ∧
      (∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
        ClassFunction.induce H (linearClassFunction (χ j)) =
          ClassFunction.induce H (linearClassFunction η)) ∧
      (∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
        IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
          linearIrreducibleCharacter (χ j)) ∧
      Set.range (fun j => ClassFunction.induce H (linearClassFunction (χ j))) = hyp.Yset := by
  classical
  obtain ⟨n, ζ, hζinj, hζrange⟩ :=
    exists_finEnum_irreducible (hyp.Yset_finite)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ)
  have hζmem : ∀ j, (ζ j : ClassFunction ↥L ℂ) ∈ hyp.Yset := by
    intro j
    rw [← hζrange]
    exact Set.mem_range_self j
  choose χ hχ_ne hχeq using fun j => hyp.exists_linear_source_of_mem_Yset (hζmem j)
  have hindRange : Set.range (fun j => ClassFunction.induce H (linearClassFunction (χ j))) =
      hyp.Yset := by
    ext φ
    constructor
    · rintro ⟨j, rfl⟩
      have hζeq :
          (ζ j : ClassFunction ↥L ℂ) =
            ClassFunction.induce H (linearClassFunction (χ j)) := by
        simpa [linearIrreducibleCharacter_coe] using hχeq j
      change ClassFunction.induce H (linearClassFunction (χ j)) ∈ hyp.Yset
      rw [← hζeq]
      exact hζmem j
    · intro hφ
      rw [← hζrange] at hφ
      obtain ⟨j, hj⟩ := hφ
      refine ⟨j, ?_⟩
      rw [← hj]
      simpa [linearIrreducibleCharacter_coe] using (hχeq j).symm
  have hcover : ∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
      ClassFunction.induce H (linearClassFunction (χ j)) =
        ClassFunction.induce H (linearClassFunction η) := by
    intro η hη_ne
    have hmem : ClassFunction.induce H (linearClassFunction η) ∈ hyp.Yset := by
      simpa [linearIrreducibleCharacter_coe] using
        hyp.induce_linearIrreducibleCharacter_mem_Yset hη_ne
    rw [← hindRange] at hmem
    exact hmem
  have hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j) := by
    intro i j hij g hconj
    apply hij
    apply hζinj
    apply IrreducibleCharacter.ext
    have hind :
        ClassFunction.induce H
            (linearIrreducibleCharacter (χ i) : ClassFunction ↥H ℂ) =
          ClassFunction.induce H
            (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ) :=
      (induce_eq_induce_iff_conj
        (G := ↥L) (H := H)
        (linearIrreducibleCharacter (χ i))
        (linearIrreducibleCharacter (χ j))).mpr ⟨g, hconj⟩
    rw [hχeq i, hχeq j]
    exact hind
  have hcoeinj : Function.Injective (fun j => (ζ j : ClassFunction ↥L ℂ)) := by
    intro i j hij
    exact hζinj (IrreducibleCharacter.ext hij)
  have hncard : hyp.Yset.ncard = n := by
    rw [← hζrange, Set.ncard_range_of_injective hcoeinj, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hn2 : 2 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  exact ⟨n, inferInstance, χ, hn2, hχ_ne, hcover, hpairwise, hindRange⟩

/-- `Y = S(H')` coherence from finite orbit representatives of nontrivial linear characters.

The caller supplies representatives whose induced characters cover `Y`, together with the usual
pairwise non-`L`-conjugacy input that makes the constructed family orthonormal.  The exact range
equality rewrites `coherentYFamily` from the constructed range to `hyp.Yset`. -/
noncomputable def coherentYset_of_pairwiseNonconj
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (χ : Fin n → (↥H →* ℂˣ))
    (hχ_ne : ∀ j, χ j ≠ 1)
    (hχ_cover : ∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
      ClassFunction.induce H (linearClassFunction (χ j)) =
        ClassFunction.induce H (linearClassFunction η))
    (hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j)) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  have hcoh := hyp.coherentYFamily_of_pairwiseNonconj hn χ hχ_ne hpairwise
  have hrange :=
    hyp.range_induce_linearIrreducibleCharacter_eq_Yset_of_induce_surjective χ hχ_ne hχ_cover
  simpa [hrange] using hcoh

/-- `Y = S(H')` coherence from the finite `Yset` representative construction.

This packages `exists_Yset_linearRepresentativeFamily` with the concrete coherence engine; the
remaining downstream input is the cardinal lower bound `2 ≤ |Y|`. -/
noncomputable def coherentYset_of_two_le_ncard
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] (hYtwo : 2 ≤ hyp.Yset.ncard) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  choose n hnzero χ hn2 hχ_ne hχ_cover hpairwise _hrange using
    hyp.exists_Yset_linearRepresentativeFamily hYtwo
  letI : NeZero n := hnzero
  exact hyp.coherentYset_of_pairwiseNonconj hn2 χ hχ_ne hχ_cover hpairwise

/-- `Y = S(H')` is nonempty.

The nontrivial nilpotent group `H` is solvable, hence has proper commutator subgroup.  The
abelianization therefore has a nontrivial linear character, whose induced character lies in
`Yset`. -/
theorem Yset_nonempty (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    hyp.Yset.Nonempty := by
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have hcomm : _root_.commutator ↥H ≠ ⊤ :=
    (IsSolvable.commutator_lt_top_of_nontrivial (G := ↥H)).ne
  obtain ⟨χ, hχ_ne⟩ := exists_monoidHom_units_ne_one_of_commutator_ne_top hcomm
  exact ⟨ClassFunction.induce H (linearClassFunction χ),
    by simpa [linearIrreducibleCharacter_coe] using
      hyp.induce_linearIrreducibleCharacter_mem_Yset hχ_ne⟩

/-- `Y = S(H')` contains no real characters.

Each member of `Yset` is an irreducible induced character of degree `|W₁|`; since `W₁` is
nontrivial this degree is not `1`, so the member is not the trivial irreducible character.  Odd
order of `L` then gives non-realness by Peterfalvi (1.1). -/
theorem Yset_hasNoRealCharacters (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters hyp.Yset := by
  intro φ hφ hreal
  let η : IrreducibleCharacter ↥L := ⟨φ, hyp.isIrreducibleCharacter_of_mem_Yset hφ⟩
  have hη_ne : η ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥L := by
    intro hη
    have hφ_one_triv : φ (1 : ↥L) = 1 := by
      have h := congrArg (fun ψ : IrreducibleCharacter ↥L =>
        (ψ : ClassFunction ↥L ℂ) (1 : ↥L)) hη
      simpa [η, trivialClassFunction_apply] using h
    obtain ⟨χ, _hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
    have hφ_one : φ (1 : ↥L) = (Nat.card hyp.W1 : ℂ) := by
      rw [hφeq]
      simpa [linearIrreducibleCharacter_coe] using
        hyp.induce_apply_one_eq_card_W1_of_degree_one
          (linearIrreducibleCharacter χ) (linearIrreducibleCharacter_apply_one χ)
    have hcard_ne : (Nat.card hyp.W1 : ℂ) ≠ 1 := by
      have hcard_nat : Nat.card hyp.W1 ≠ 1 := by
        intro hcard
        exact hyp.W1_nontrivial (Subgroup.card_eq_one.mp hcard)
      exact_mod_cast hcard_nat
    exact hcard_ne (hφ_one.symm.trans hφ_one_triv)
  exact (OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'
    hyp.card_L_odd hη_ne) hreal

/-- `Y = S(H')` is closed under complex conjugation. -/
theorem Yset_closedUnderConjugate (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate hyp.Yset := by
  intro φ hφ
  rw [Yset, SsubFiltration] at hφ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hφ
  let θc : IrreducibleCharacter ↥H :=
    ⟨(θ : ClassFunction ↥H ℂ).conj, θ.isIrreducible.conj⟩
  refine ⟨θc, ?_, ?_, ?_⟩
  · intro hθc
    apply hθ_ne
    apply IrreducibleCharacter.ext
    have hval : (θ : ClassFunction ↥H ℂ).conj =
        (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H :
          ClassFunction ↥H ℂ) := by
      simpa [θc] using congrArg
        (fun η : IrreducibleCharacter ↥H => (η : ClassFunction ↥H ℂ)) hθc
    calc
      (θ : ClassFunction ↥H ℂ) = ((θ : ClassFunction ↥H ℂ).conj).conj := by
        rw [ClassFunction.conj_conj]
      _ = (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H :
          ClassFunction ↥H ℂ).conj := by
        rw [hval]
      _ = (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H :
          ClassFunction ↥H ℂ) := by
        ext x
        simp
  · simpa [θc, OddOrder.Peterfalvi.S03.characterKernel_conj] using hker
  · rw [hφeq]
    simpa [θc] using ClassFunction.induce_conj H (θ : ClassFunction ↥H ℂ)

/-- `Y = S(H')` has at least two members. -/
theorem two_le_Yset_ncard (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    2 ≤ hyp.Yset.ncard :=
  OddOrder.Peterfalvi.S07.two_le_ncard_of_conjugate_closed_of_noReal
    hyp.Yset_finite
    hyp.Yset_nonempty
    hyp.Yset_closedUnderConjugate
    hyp.Yset_hasNoRealCharacters

/-- `Y = S(H')` coherence, with the cardinal lower bound discharged internally. -/
noncomputable def coherentYset (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.coherentYset_of_two_le_ncard hyp.two_le_Yset_ncard

/-- Convert the `X(Z) ≠ ∅` branch condition used in the (6.8) capstone into
the `Set.Nonempty` input consumed by the X-chain coherence constructors. -/
theorem Xset_nonempty_of_ne_empty (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    (hX : hyp.Xset Z ≠ ∅) : (hyp.Xset Z).Nonempty :=
  Set.nonempty_iff_ne_empty.mpr hX

/-- **(6.8) coherence, `X`-empty case** (`H` abelian / no non-linear constituents).  When
`X = S − S([H,H])` is empty, the partition `S = X ∪ Y` (`Xset_union_Yset_eq_S`) collapses to
`S = Y = S([H,H])`, so the full target `IsCoherent τ S H^#` is exactly the already-built
`Y`-coherence `coherentYset` (T6: equal-degree `|W₁|` family).  This discharges the abelian branch
of the (6.8) capstone with no gluing required. -/
noncomputable def coherenceTarget_of_Xset_empty (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hXe : hyp.Xset ⁅H, H⁆ = ∅) : hyp.CoherenceTarget := by
  have hSY : hyp.Yset = hyp.S := by
    rw [← hyp.Xset_union_Yset_eq_S, hXe, Set.empty_union]
  have h : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := hSY ▸ hyp.coherentYset
  exact h

/-- Glue `X = S - S(H')` coherence with the internally constructed `Y = S(H')` coherence.

This is the final algebraic assembly shape needed by Peterfalvi (6.8): callers still provide the
case-dependent `X` coherence and the two orthogonality/agreement inputs, but the `Y` side and the
set-theoretic rewrite from `X ∪ Y` to `S` are discharged here. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (hsrc_ortho : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner u v = 0)
    (himg_ortho : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset,
        ClassFunction.inner (hX.extension u) (hyp.coherentYset.extension v) = 0)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget := by
  let hY := hyp.coherentYset
  have hU : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
    OddOrder.Peterfalvi.S07.coherentUnion_of_glued
      (hX := hX) (hY := hY) ν hagreeX hagreeY hsrc_ortho himg_ortho hgen
  simpa [hyp.Xset_union_Yset_eq_S] using hU

/-- Variant of the (6.8) glue step where source-side orthogonality is discharged from
irreducibility of the `X` side and disjointness of the `X/Y` partition. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hXirr : ∀ φ ∈ hyp.Xset ⁅H, H⁆, IsIrreducibleCharacter φ)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (himg_ortho : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset,
        ClassFunction.inner (hX.extension u) (hyp.coherentYset.extension v) = 0)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget := by
  letI : H.Normal := hyp.H_normal
  exact hyp.coherentS_of_Xset_commutator_Yset_glued hX ν hagreeX hagreeY
    (hyp.inner_span_Xset_Yset_eq_zero_of_irreducible_X hXirr) himg_ortho hgen

/-- Variant of the (6.8) glue step where source-side orthogonality is discharged from
irreducibility of `X`, and image-side orthogonality is discharged from mixed inner preservation
of the glued map `ν`. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hXirr : ∀ φ ∈ hyp.Xset ⁅H, H⁆, IsIrreducibleCharacter φ)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (hmixed : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner (ν u) (ν v) =
        ClassFunction.inner u v)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget := by
  let hsrc := hyp.inner_span_Xset_Yset_eq_zero_of_irreducible_X hXirr
  exact hyp.coherentS_of_Xset_commutator_Yset_glued hX ν hagreeX hagreeY hsrc
    (OddOrder.Peterfalvi.S07.image_orthogonal_of_mixed_inner_eq
      hagreeX hagreeY hmixed hsrc)
    hgen

/-- Generator-level variant of
`coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_mixed_inner`.

The `τ₃` candidate only has to be checked on the characters in `Xset H'` and `Yset`; agreement and
mixed-inner preservation on the integral spans are derived internally. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_generator_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hXirr : ∀ φ ∈ hyp.Xset ⁅H, H⁆, IsIrreducibleCharacter φ)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆, ν x = hX.extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset ⁅H, H⁆, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_mixed_inner hXirr hX ν
    (fun _ hu => OddOrder.Peterfalvi.S07.IntegralCharacterMap.eq_on_zSpan_of_eq_on hagreeX hu)
    (fun _ hv => OddOrder.Peterfalvi.S07.IntegralCharacterMap.eq_on_zSpan_of_eq_on hagreeY hv)
    (OddOrder.Peterfalvi.S07.mixed_inner_eq_on_zSpan_of_eq_on hmixed)
    hgen

/-- **(6.8.1), case (c1):** in the Frobenius case every member of `S` is irreducible (hence
`X ⊆ Irr L`).  By [Is] Thm 6.34 (`isIrreducibleCharacter_induce_of_frobeniusGroup`), inducing any
nontrivial irreducible of the kernel `H` to the Frobenius group `L` gives an irreducible. -/
theorem isIrreducibleCharacter_of_mem_S_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.S) : IsIrreducibleCharacter φ := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hφ
  obtain ⟨θ, hθ_ne, rfl⟩ := hφ
  exact isIrreducibleCharacter_induce_of_frobeniusGroup hF θ hθ_ne

/-- **(6.8.1), case (c1):** `X ⊆ Irr L` in the Frobenius case, since `X ⊆ S` and `S ⊆ Irr L`.
This is the irreducibility input the §6 coherence engine (T8) consumes for the `X`-family (and the
`hX` hypothesis of the (6.6) characterization). -/
theorem isIrreducibleCharacter_of_mem_Xset_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Xset Z) :
    IsIrreducibleCharacter φ :=
  hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF (hyp.mem_Xset.mp hφ).1

/-- **`S` contains no real characters** (Frobenius case).

Each member of `S` is an irreducible induced character `Ind_H^L θ` (`θ ≠ 1_H`,
`isIrreducibleCharacter_of_mem_S_of_frobenius`) of degree `|L:H|·θ(1) = |W₁|·θ(1) ≥ |W₁| > 1`, so
it is not the trivial irreducible character; odd order of `L` then gives non-realness by Peterfalvi
(1.1) (`not_isReal_of_ne_trivial_of_odd_card'`).  This `HasNoRealCharacters` fact and its
`SsubFiltration` corollary supply the no-real input to the conjugate-pair enumeration of any
`S(A) ⊆ S` consumed on the way to the (6.2)/(6.3) degree bound. -/
theorem S_hasNoRealCharacters (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters hyp.S := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  intro φ hφ hreal
  have hirr : IsIrreducibleCharacter φ := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hφ
  let η : IrreducibleCharacter ↥L := ⟨φ, hirr⟩
  have hη_ne : η ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥L := by
    intro hη
    have hφ_one_triv : φ (1 : ↥L) = 1 := by
      have h := congrArg (fun ψ : IrreducibleCharacter ↥L =>
        (ψ : ClassFunction ↥L ℂ) (1 : ↥L)) hη
      simpa [η, trivialClassFunction_apply] using h
    rw [hyp.S_eq] at hφ
    obtain ⟨θ, -, hφeq⟩ := hφ
    obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hφ_one : φ (1 : ↥L) = (Nat.card hyp.W1 : ℂ) * (d : ℂ) := by
      rw [hφeq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hd,
        hyp.index_H_eq_card_W1]
    refine absurd (hφ_one.symm.trans hφ_one_triv) ?_
    rw [← Nat.cast_mul]
    intro hcast
    have hnat : Nat.card hyp.W1 * d = 1 := by exact_mod_cast hcast
    exact hyp.W1_nontrivial (Subgroup.card_eq_one.mp (Nat.dvd_one.mp ⟨d, hnat.symm⟩))
  exact (OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'
    hyp.card_L_odd hη_ne) hreal

/-- **`S(A)` contains no real characters** (Frobenius case), as `S(A) ⊆ S`. -/
theorem SsubFiltration_hasNoRealCharacters (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) (A : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.SsubFiltration A) :=
  (hyp.S_hasNoRealCharacters hF).mono hyp.SsubFiltration_subset_S

/-- **`S`-member character facts** (Frobenius case): for `χ ∈ S` (irreducible by
`isIrreducibleCharacter_of_mem_S_of_frobenius`, non-real by `S_hasNoRealCharacters`) the conjugate
pair `{χ, χ̄}` is orthonormal (`‖χ‖² = ‖χ̄‖² = 1`, `⟨χ̄, χ⟩ = ⟨χ, χ̄⟩ = 0`).  These are the
per-member `hreal`/`hχχ`/`hχbarχbar`/`hχbarχ`/`hχχbar` facts that the (6.2) member-family
enumeration feeds to B1 (`coherentDegreeSumBound_of_not_coherent`) for each member of `S₁ ⊆ S`. -/
theorem sMember_characterFacts (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {χ : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) :
    ¬ ClassFunction.IsReal χ ∧
      ClassFunction.inner χ χ = 1 ∧
      ClassFunction.inner χ.conj χ.conj = 1 ∧
      ClassFunction.inner χ.conj χ = 0 ∧
      ClassFunction.inner χ χ.conj = 0 := by
  have hirr : IsIrreducibleCharacter χ := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hχS
  have hconjirr : IsIrreducibleCharacter χ.conj := hirr.conj
  have hreal : ¬ ClassFunction.IsReal χ := hyp.S_hasNoRealCharacters hF hχS
  have hbi_ne : (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ≠ ⟨χ, hirr⟩ :=
    fun h => hreal (congrArg Subtype.val h)
  refine ⟨hreal, ?_, ?_, ?_, ?_⟩
  · simpa using irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) ⟨χ, hirr⟩
  · simpa using
      irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L)
        ⟨χ.conj, hconjirr⟩
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L)
      ⟨χ, hirr⟩
    rwa [if_neg hbi_ne] at h
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L)
      ⟨χ.conj, hconjirr⟩
    rwa [if_neg (fun h => hbi_ne h.symm)] at h

/-- **`S`-member conjugate-difference support** (any irreducible `χ ∈ S`): `χ̄ − χ` is supported on
`H^# = sharpImage H`.  Since `χ = Ind_H^L θ` with `H ⊴ L`, `support χ ⊆ H`, and `χ̄ − χ` vanishes at
`1` (the degree `χ(1)` is a real natural number), so it omits `1`.  This is the per-member
`hdiffsupp` fact for the (6.2)/B1 member-family over `S₁ ⊆ S`. -/
theorem sMember_diffSupport (hyp : SibleyDadeHypothesis G L H)
    {χ : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) (hirr : IsIrreducibleCharacter χ) :
    (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, -, hχeq⟩ := hχS
  obtain ⟨n, -, hn1, -⟩ := hirr.exists_natDegree_charValue_one_dvd_card
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hn1, star_natCast, sub_self])
  have hχg : χ g ≠ 0 := fun h0 =>
    hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, h0, star_zero, sub_zero])
  have hgH : g ∈ H := by
    have hsupp : χ.support ⊆ (H : Set ↥L) := by
      rw [hχeq]
      exact ClassFunction.support_induce_subset_of_normal H (θ : ClassFunction ↥H ℂ)
    exact hsupp (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **(6.8.1), Frobenius case:** source-side orthogonality for the final
`X = S - S(H')`, `Y = S(H')` partition. -/
theorem inner_span_Xset_Yset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) :
    ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner u v = 0 :=
  hyp.inner_span_Xset_Yset_eq_zero_of_irreducible_X
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)

/-- **(6.8.1), Frobenius case:** glue the Frobenius `X` coherence with the internally
constructed `Y` coherence, with source-side orthogonality discharged from Frobenius
irreducibility. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (himg_ortho : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset,
        ClassFunction.inner (hX.extension u) (hyp.coherentYset.extension v) = 0)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hX ν hagreeX hagreeY himg_ortho hgen

/-- **(6.8.1), Frobenius case:** glue the Frobenius `X` coherence with the internally
constructed `Y` coherence, using mixed inner preservation of `ν` to discharge image-side
orthogonality. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_frobenius_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (hmixed : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner (ν u) (ν v) =
        ClassFunction.inner u v)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_mixed_inner
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hX ν hagreeX hagreeY hmixed hgen

/-- **(6.8.1), Frobenius case:** generator-level mixed-inner glue adapter.

This is the Frobenius specialization of the generator-level `τ₃` interface: the `X`-side
irreducibility is discharged from `hF`, while agreement and mixed-inner preservation are required
only on members of `Xset H'` and `Yset`. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_frobenius_generator_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆, ν x = hX.extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset ⁅H, H⁆, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_generator_mixed_inner
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hX ν hagreeX hagreeY hmixed hgen

/-- **(T7-c2 case A) `X ⊆ Irr L`.**  In case A every `χ ∈ X = S − S(Z)` is irreducible.  Writing
`χ = Ind_H^L θ` (`θ ≠ 1`, from `χ ∈ S`), membership `χ ∉ S(Z)` forces `Z.subgroupOf H ⊄ Ker θ`, so
`inertia_eq_H_of_c2_caseA` gives `I_L(θ) = H`, and [Is] Thm 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`) makes `Ind_H^L θ = χ` irreducible.  This is the
case-A analogue of `isIrreducibleCharacter_of_mem_Xset_of_frobenius` (the Frobenius case). -/
theorem isIrreducibleCharacter_of_mem_Xset_caseA (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    (hZnorm : ∀ w ∈ hyp.W1, w ∈ Subgroup.normalizer Z)
    (hZfpf : ∀ w ∈ hyp.W1, w ≠ 1 → Subgroup.centralizer ({w} : Set ↥L) ⊓ Z = ⊥)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    letI : H.Normal := hyp.H_normal
    IsIrreducibleCharacter χ := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  obtain ⟨hχS, hχnotZ⟩ := hχX
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, hθne, hχeq⟩ := hχS
  have hZker : ¬ ((Z.subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ)) :=
    fun hsub => hχnotZ ⟨θ, hθne, hsub, hχeq⟩
  have hinertia := hyp.inertia_eq_H_of_c2_caseA hZH hZcentral hZnorm hZfpf hZker
  rw [hχeq]
  exact isIrreducibleCharacter_induce_of_inertia_eq θ hinertia

/-- **(c2)+math-(A) `X ⊆ Irr L`** (Peterfalvi (6.8.1) in the CertainType branch, math-case A).
Every `χ ∈ X = S − S(Zc)` is irreducible at the central `Zc = Z(H) ∩ H'`.  This is the (c2)
analogue of `isIrreducibleCharacter_of_mem_Xset_of_frobenius`: it discharges the four hypotheses of
the FPF-generic `isIrreducibleCharacter_of_mem_Xset_caseA` at `Z = Zc` — centrality
(`centralCommutator_subgroupOf_le_center`), normality (`Zc ◁ L`, so every `w` normalizes it), and
fixed-point-freeness (`centralizer_inf_centralCommutator_eq_bot_of_c2_caseA`, from the math-(A)
hypothesis `hA : Z(H) ⊓ W₂ = 1`). -/
theorem isIrreducibleCharacter_of_mem_Xset_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset hyp.centralCommutator) :
    letI : H.Normal := hyp.H_normal
    IsIrreducibleCharacter χ := by
  haveI := hyp.H_normal
  exact hyp.isIrreducibleCharacter_of_mem_Xset_caseA hyp.centralCommutator_le
    hyp.centralCommutator_subgroupOf_le_center
    (fun w _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hyp.centralCommutator_normal]; exact Subgroup.mem_top w)
    (fun w hw hw1 => hyp.centralizer_inf_centralCommutator_eq_bot_of_c2_caseA hK hW1 hA hw hw1)
    hχX

/-- **Peterfalvi (6.6) `X`-characterization** (mmd 04.8 L74-76).  For a normal `Z ≤ H` such that
every member of `X = S − S(Z)` is irreducible (the (6.8) Frobenius/case-A input `hX`), `X` is
exactly the set of irreducible characters of `L` whose kernel does not contain `Z`:
`X = {χ ∈ Irr L | Z ⊄ Ker χ}`.

Both inclusions route the kernel comparison through a *genuine* character — `Res_H φ` for `⊆`
(via `characterKernel_subset_of_isCharacter_of_inner_ne_zero`) and `Ind_H^L θ` for `⊇` (via
`characterKernel_subset_of_inner_induce_ne_zero`) — together with the (1.6.a) forward bridge
`subsetCharacterKernel_induce_of_subgroupOf`; no use of [Is] Lemma 2.21 is needed. -/
theorem Xset_eq_irreducible_not_subset_characterKernel (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    hyp.Xset Z = {χ : ClassFunction ↥L ℂ | IsIrreducibleCharacter χ ∧
      ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ)} := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  ext φ
  constructor
  · -- (⊆): φ ∈ X is irreducible (hX); if `Z ⊆ Ker φ` then `φ = Ind θ ∈ S(Z)`, contradiction.
    intro hφX
    have hφirr : IsIrreducibleCharacter φ := hX φ hφX
    refine ⟨hφirr, ?_⟩
    obtain ⟨hφS, hφnotSZ⟩ := hyp.mem_Xset.mp hφX
    rw [hyp.S_eq] at hφS
    obtain ⟨θ, hθ_ne, hφeq⟩ := hφS
    intro hZker
    apply hφnotSZ
    rw [hyp.mem_SsubFiltration]
    refine ⟨θ, hθ_ne, ?_, hφeq⟩
    -- `Z.subgroupOf H ⊆ Ker θ`: read off from `Res_H φ` (a genuine constituent of `θ`).
    have hRes : IsCharacter (ClassFunction.restrict H φ) := isCharacter_restrict hφirr.isCharacter H
    have hθirr : IsIrreducibleCharacter (θ : ClassFunction ↥H ℂ) := θ.property
    have hnorm : ClassFunction.inner φ φ = 1 := by
      have h := irreducibleCharacter_inner_eq_ite (⟨φ, hφirr⟩ : IrreducibleCharacter ↥L)
        (⟨φ, hφirr⟩ : IrreducibleCharacter ↥L)
      simpa using h
    have hinner_ne : ClassFunction.inner (ClassFunction.restrict H φ)
        (θ : ClassFunction ↥H ℂ) ≠ 0 := by
      have hfrob := ClassFunction.inner_induce_eq_inner_restrict H (θ : ClassFunction ↥H ℂ) φ
      rw [← hφeq, hnorm] at hfrob
      rw [inner_conj_symm θ (ClassFunction.restrict H φ), ← hfrob]
      simp
    intro n hn
    refine characterKernel_subset_of_isCharacter_of_inner_ne_zero hRes hθirr hinner_ne ?_
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
    simp only [ClassFunction.restrict_apply]
    have hnZ : ((n : ↥L)) ∈ Z := Subgroup.mem_subgroupOf.mp hn
    have hker := hZker hnZ
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hker
    rw [hker, OneMemClass.coe_one]
  · -- (⊇): χ irreducible with `Z ⊄ Ker χ`.  Take a source `θ` of `χ`; show `Ind θ ∈ X`, hence
    -- irreducible (hX), hence `= χ` by orthonormality.
    rintro ⟨hχirr, hχZ⟩
    obtain ⟨θ, hθinner⟩ := OddOrder.Peterfalvi.S03.exists_inner_induce_ne_zero (H := H)
      (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
    -- A source `θ'` of `χ` with `Z.subgroupOf H ⊆ Ker θ'` would force `Z ⊆ Ker χ` (contradiction).
    have hkey : ∀ θ' : IrreducibleCharacter ↥H,
        ClassFunction.inner (ClassFunction.induce H (θ' : ClassFunction ↥H ℂ)) φ ≠ 0 →
        ((Z.subgroupOf H : Set ↥H) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ' : ClassFunction ↥H ℂ)) → False := by
      intro θ' hθ'inner hθ'ker
      apply hχZ
      have hZind := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
        (G := ↥L) hZH (θ' : ClassFunction ↥H ℂ) hθ'ker
      intro z hz
      exact characterKernel_subset_of_inner_induce_ne_zero θ'.property.isCharacter hχirr
        hθ'inner (hZind hz)
    have hθ_ne : θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H := by
      intro hθtriv
      refine hkey θ hθinner (fun n _ => ?_)
      rw [hθtriv]
      simp [OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    have hIndnotSZ : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ∉ hyp.SsubFiltration Z := by
      intro hmem
      rw [hyp.mem_SsubFiltration] at hmem
      obtain ⟨θ', _, hθ'ker, hθ'eq⟩ := hmem
      exact hkey θ' (by rw [← hθ'eq]; exact hθinner) hθ'ker
    have hIndX : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ∈ hyp.Xset Z :=
      hyp.mem_Xset.mpr ⟨by rw [hyp.S_eq]; exact ⟨θ, hθ_ne, rfl⟩, hIndnotSZ⟩
    have hIndirr : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) :=
      hX _ hIndX
    have heq : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) = φ := by
      have hite := irreducibleCharacter_inner_eq_ite
        (⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hIndirr⟩ : IrreducibleCharacter ↥L)
        (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
      by_cases hAB : (⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hIndirr⟩ :
          IrreducibleCharacter ↥L) = (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
      · exact congrArg Subtype.val hAB
      · rw [if_neg hAB] at hite
        exact absurd hite hθinner
    rw [← heq]; exact hIndX

/-- **(T8 leaf 1) `X`-member character facts**, from the abstract input `X ⊆ Irr L`.

Every `χ ∈ X = S − S(Z)` is non-real (Peterfalvi (1.1), `L` odd) with
`‖χ‖² = ‖χ̄‖² = 1` and `⟨χ̄, χ⟩ = ⟨χ, χ̄⟩ = 0`.  These are the
`hreal`/`hχχ`/`hχbarχbar`/`hχbarχ`/`hχχbar'` fields of `S07.DadeChainStep`.
Non-triviality is read off the (6.6) characterization
(`Z ⊄ Ker χ` via `Xset_eq_irreducible_not_subset_characterKernel`, so `χ ≠ 1`),
then (1.1) (`not_isReal_of_ne_trivial_of_odd_card'`) gives non-realness and
`irreducibleCharacter_inner_eq_ite` gives the orthonormality.

This form is shared by the Frobenius case and the case-A `X ⊆ Irr L` bridge. -/
theorem xMember_characterFacts_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    ¬ ClassFunction.IsReal χ ∧
      ClassFunction.inner χ χ = 1 ∧
      ClassFunction.inner χ.conj χ.conj = 1 ∧
      ClassFunction.inner χ.conj χ = 0 ∧
      ClassFunction.inner χ χ.conj = 0 := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hirr : IsIrreducibleCharacter χ := hX χ hχX
  have hconjirr : IsIrreducibleCharacter χ.conj := hirr.conj
  -- `Z ⊄ Ker χ` from the (6.6) characterization, hence `χ ≠ 1`.
  have hZker : ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ) := by
    have hXeq := hyp.Xset_eq_irreducible_not_subset_characterKernel hZH hX
    rw [hXeq] at hχX
    exact hχX.2
  have hne_triv : (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) ≠
      OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥L := by
    intro htriv
    apply hZker
    have hχtriv : χ = OddOrder.RepresentationTheory.trivialClassFunction ↥L :=
      congrArg Subtype.val htriv
    rw [hχtriv, OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    exact Set.subset_univ _
  have hreal : ¬ ClassFunction.IsReal χ :=
    OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card' hyp.card_L_odd hne_triv
  have hbi_ne : (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ≠ ⟨χ, hirr⟩ :=
    fun h => hreal (congrArg Subtype.val h)
  refine ⟨hreal, ?_, ?_, ?_, ?_⟩
  · simpa using irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) ⟨χ, hirr⟩
  · simpa using
      irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ⟨χ.conj, hconjirr⟩
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ⟨χ, hirr⟩
    rwa [if_neg hbi_ne] at h
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) ⟨χ.conj, hconjirr⟩
    rwa [if_neg (fun h => hbi_ne h.symm)] at h

/-- **(T8 leaf 1) `X`-member character facts** (Frobenius case). -/
theorem xMember_characterFacts (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    ¬ ClassFunction.IsReal χ ∧
      ClassFunction.inner χ χ = 1 ∧
      ClassFunction.inner χ.conj χ.conj = 1 ∧
      ClassFunction.inner χ.conj χ = 0 ∧
      ClassFunction.inner χ χ.conj = 0 :=
  hyp.xMember_characterFacts_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hχX

/-- **(T8 leaf 2) `X`-member difference support**, from the abstract input `X ⊆ Irr L`.

For `χ ∈ X = S − S(Z)` the conjugate difference `χ̄ − χ` is supported on
`H^# = sharpImage H` (the `hdiffsupp` field of `S07.DadeChainStep`).  Since
`χ = Ind_H^L θ` with `H ⊴ L`, `support χ ⊆ H` (`support_induce_subset_of_normal`);
`χ̄ − χ` vanishes at `1` (the degree `χ(1)` is the real `(n : ℂ)`), so it omits `1`
and lands in `H ∖ {1}`. -/
theorem xMember_diffSupport_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hirr : IsIrreducibleCharacter χ := hX χ hχX
  have hχS : χ ∈ hyp.S := (hyp.mem_Xset.mp hχX).1
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, -, hχeq⟩ := hχS
  obtain ⟨n, -, hn1, -⟩ := hirr.exists_natDegree_charValue_one_dvd_card
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hn1, star_natCast, sub_self])
  have hχg : χ g ≠ 0 := fun h0 =>
    hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, h0, star_zero, sub_zero])
  have hgH : g ∈ H := by
    have hsupp : χ.support ⊆ (H : Set ↥L) := by
      rw [hχeq]
      exact ClassFunction.support_induce_subset_of_normal H (θ : ClassFunction ↥H ℂ)
    exact hsupp (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **(T8 leaf 2) `X`-member difference support** (Frobenius case). -/
theorem xMember_diffSupport (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
  hyp.xMember_diffSupport_of_irreducible_X
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hχX

/-- **(T8 leaf 3a) `X` is closed under conjugation**, from the abstract input `X ⊆ Irr L`.

`Z ⊴ L` gives `Ker χ̄ = Ker χ` (`characterKernel_conj`), so the (6.6) characterization
`X = {χ ∈ Irr L | Z ⊄ Ker χ}` is conjugation-invariant.  This is the
`ClosedUnderConjugate` input to the degree-monotone enumeration of `X` into conjugate pairs
(`S07.two_le_ncard_of_conjugate_closed_of_noReal`, `S07.exists_monotoneDegreeEnum`). -/
theorem Xset_closedUnderConjugate_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (_hZH : Z ≤ H) [Z.Normal]
    (_hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) :=
  hyp.Xset_closedUnderConjugate_unconditional Z

/-- **(T8 leaf 3a) `X` is closed under conjugation** (Frobenius case). -/
theorem Xset_closedUnderConjugate (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) :=
  hyp.Xset_closedUnderConjugate_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)

/-- **(T8 leaf 3b) `X` has no real characters**, from the abstract input `X ⊆ Irr L`. -/
theorem Xset_hasNoRealCharacters_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset Z) :=
  fun _ hχX => (hyp.xMember_characterFacts_of_irreducible_X hZH hX hχX).1

/-- **(T8 leaf 3b) `X` has no real characters** (Frobenius case). -/
theorem Xset_hasNoRealCharacters (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset Z) :=
  hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)

/-- **(T8 leaf 4) `X` is finite**, from the abstract input `X ⊆ Irr L`.

This is the `hXfin` input to the degree-monotone enumeration
`S07.exists_monotoneDegreeEnum` and the chain assembly. -/
theorem xSet_finite_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (_hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    (hyp.Xset Z).Finite :=
  hyp.Xset_finite Z

/-- **(T8 leaf 4) `X` is finite** (Frobenius case). -/
theorem xSet_finite (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {Z : Subgroup ↥L} :
    (hyp.Xset Z).Finite :=
  hyp.xSet_finite_of_irreducible_X
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)

/-- **(T8 leaf 5) the base block `S₀`**: the minimal-(real-)degree members of `X`.  This is the
equal-minimal-degree prefix `{χ₁,…,χₖ}` of (6.6), on which (1.1)+(1.4) supplies the base coherence
`coherentEqualDegree_fromDade` before the (5.6) adjoining of the strictly-higher-degree conjugate
pairs.  `S₀` must contain **all** minimal-degree members (not just one pair): the first (5.6)
adjoining of a pair of degree ratio `a` needs `2a < ∑_{S₀} aⱼ²`, which fails at equal degree. -/
def xBaseBlock (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  {χ ∈ hyp.Xset Z | ∀ ψ ∈ hyp.Xset Z,
    (OddOrder.Peterfalvi.S03.characterDegree χ).re ≤
      (OddOrder.Peterfalvi.S03.characterDegree ψ).re}

theorem xBaseBlock_subset (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    hyp.xBaseBlock Z ⊆ hyp.Xset Z :=
  fun _ hχ => hχ.1

/-- The minimal-degree base block of `X(Z)` is closed under conjugation.  This uses only the
direct conjugation-invariance of `X(Z)` and degree preservation under conjugation. -/
theorem xBaseBlock_closedUnderConjugate_unconditional
    (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) := by
  intro χ hχ
  refine ⟨hyp.Xset_closedUnderConjugate_unconditional Z hχ.1, fun ψ hψ => ?_⟩
  have hre : (OddOrder.Peterfalvi.S03.characterDegree χ.conj).re =
      (OddOrder.Peterfalvi.S03.characterDegree χ).re := by
    simp
  rw [hre]
  exact hχ.2 ψ hψ

/-- Any two members of the base block have the same degree (the base is an *equal*-degree family,
the input shape of `coherentEqualDegree_fromDade`). -/
theorem xBaseBlock_degree_re_eq (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.xBaseBlock Z) (hχ' : χ' ∈ hyp.xBaseBlock Z) :
    (OddOrder.Peterfalvi.S03.characterDegree χ).re =
      (OddOrder.Peterfalvi.S03.characterDegree χ').re :=
  le_antisymm (hχ.2 χ' hχ'.1) (hχ'.2 χ hχ.1)

/-- If `χ₁` is a base-block anchor and `χ ∈ X`, then the natural degree of `χ₁` is no larger
than the natural degree of `χ`. -/
theorem natDegree_le_of_xBaseBlock_anchor (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {χ₁ χ : IrreducibleCharacter ↥L} {d₁ d : ℕ}
    (hχ₁base : (χ₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z)
    (hχX : (χ : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hχ₁one : (χ₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hχone : (χ : ClassFunction ↥L ℂ) 1 = (d : ℂ)) :
    d₁ ≤ d := by
  have hre := hχ₁base.2 (χ : ClassFunction ↥L ℂ) hχX
  rw [OddOrder.Peterfalvi.S03.characterDegree_def,
    OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one, hχone] at hre
  exact_mod_cast hre

/-- If `χ₁` is a base-block anchor and `χ ∈ X` is not itself in the base block, then the
natural degree of `χ` is strictly larger. -/
theorem natDegree_lt_of_xBaseBlock_anchor_of_not_mem
    (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {χ₁ χ : IrreducibleCharacter ↥L} {d₁ d : ℕ}
    (hχ₁base : (χ₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z)
    (hχX : (χ : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hχnotbase : (χ : ClassFunction ↥L ℂ) ∉ hyp.xBaseBlock Z)
    (hχ₁one : (χ₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hχone : (χ : ClassFunction ↥L ℂ) 1 = (d : ℂ)) :
    d₁ < d := by
  have hle : d₁ ≤ d :=
    hyp.natDegree_le_of_xBaseBlock_anchor hχ₁base hχX hχ₁one hχone
  have hne : d₁ ≠ d := by
    intro hEq
    apply hχnotbase
    refine ⟨hχX, ?_⟩
    intro ψ hψX
    have hbase_le := hχ₁base.2 ψ hψX
    have hχre :
        (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction ↥L ℂ)).re =
          (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction ↥L ℂ)).re := by
      rw [OddOrder.Peterfalvi.S03.characterDegree_def,
        OddOrder.Peterfalvi.S03.characterDegree_def, hχone, hχ₁one]
      exact_mod_cast hEq.symm
    rw [hχre]
    exact hbase_le
  omega

/-- The base block is closed under conjugation, from the abstract input `X ⊆ Irr L`:
conjugation preserves the degree (`characterDegree_conj`) and `X`
(`Xset_closedUnderConjugate_of_irreducible_X`).  With the no-real property this makes `S₀`
contain a conjugate pair, so `2 ≤ |S₀|`. -/
theorem xBaseBlock_closedUnderConjugate_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (_hZH : Z ≤ H) [Z.Normal]
    (_hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
  hyp.xBaseBlock_closedUnderConjugate_unconditional Z

/-- The base block is closed under conjugation (Frobenius case). -/
theorem xBaseBlock_closedUnderConjugate (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
  hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)

/-- A member `χ = Ind_H^L θ` of `S` is supported on `H` (its induced character vanishes off the
normal subgroup `H`). -/
theorem sMember_support_subset_H (hyp : SibleyDadeHypothesis G L H)
    {χ : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) :
    χ.support ⊆ (H : Set ↥L) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, -, hχeq⟩ := hχS
  rw [hχeq]
  exact ClassFunction.support_induce_subset_of_normal H (θ : ClassFunction ↥H ℂ)

/-- **(T8 leaf 6) equal-degree difference support.**  For two members `χ, χ'` of `S` of equal
degree (`χ(1) = χ'(1)`) the difference `χ − χ'` is supported on `H^# = sharpImage H`: both are
supported on `H` (`sMember_support_subset_H`) and the difference vanishes at `1` (equal degree).
This is the `hsuppdiff` input of `coherentEqualDegree_fromDade` for the equal-minimal-degree base
block `S₀` (`irreducibleCharacterDifference χ j = χⱼ − χ₀`), and the (5.6) `χ − a·χ₁` support shape. -/
theorem sMember_diffSupport_of_charValue_eq (hyp : SibleyDadeHypothesis G L H)
    {χ χ' : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) (hχ'S : χ' ∈ hyp.S) (hdeg : χ 1 = χ' 1) :
    (χ - χ').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  have hgH : g ∈ H := by
    rcases eq_or_ne (χ g) 0 with hχg | hχg
    · have hχ'g : χ' g ≠ 0 := fun h0 =>
        hg (by rw [ClassFunction.sub_apply, hχg, h0, sub_self])
      exact hyp.sMember_support_subset_H hχ'S (ClassFunction.mem_support.mpr hχ'g)
    · exact hyp.sMember_support_subset_H hχS (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **(T8.11d) scaled degree-matched support.**

For two `S`-members whose degrees satisfy `χ(1) = a χ₁(1)`, the scaled difference
`χ - aχ₁` is supported on `H^# = sharpImage H`.  This is the support bridge used for the
`hmemdegdiffsupp` and `hdiffasuppχ` fields once the integer degree ratios are available. -/
theorem sMember_scaledDiffSupport_of_charValue_eq (hyp : SibleyDadeHypothesis G L H)
    {χ χ' : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) (hχ'S : χ' ∈ hyp.S) {a : ℕ}
    (hdeg : χ 1 = (a : ℂ) * χ' 1) :
    (χ - a • χ').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by
      rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ a χ', ClassFunction.smul_apply,
        hdeg, sub_self])
  have hgH : g ∈ H := by
    rcases eq_or_ne (χ g) 0 with hχg | hχg
    · have hχ'g : χ' g ≠ 0 := fun h0 =>
        hg (by
          rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ a χ',
            ClassFunction.smul_apply, hχg, h0, mul_zero, sub_self])
      exact hyp.sMember_support_subset_H hχ'S (ClassFunction.mem_support.mpr hχ'g)
    · exact hyp.sMember_support_subset_H hχS (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **Two-coefficient degree-matched difference support.**  For two `S`-members `χ, χ'` and naturals
`m, n` with `m·χ(1) = n·χ'(1)`, the combination `m·χ − n·χ'` is supported on `H^# = sharpImage H`.
Both are supported on `H` (`sMember_support_subset_H`) and the combination vanishes at `1`.  Unlike
`sMember_scaledDiffSupport_of_charValue_eq` (`χ − a·χ'`, requiring `χ'(1) ∣ χ(1)`), the symmetric
coefficients `m = χ'(1)`, `n = χ(1)` make `m·χ − n·χ'` supported **without** any divisibility — the
(4.1) supported-difference input `χ'(1)·χ − χ(1)·χ'` used in the (6.8.1) `himg_ortho`. -/
theorem sMember_smulDiffSupport_of_charValue_eq (hyp : SibleyDadeHypothesis G L H)
    {χ χ' : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) (hχ'S : χ' ∈ hyp.S) {m n : ℕ}
    (hdeg : (m : ℂ) * χ 1 = (n : ℂ) * χ' 1) :
    (m • χ - n • χ').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  have hval : ∀ x : ↥L, (m • χ - n • χ') x = (m : ℂ) * χ x - (n : ℂ) * χ' x := by
    intro x
    rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ m χ, ← Nat.cast_smul_eq_nsmul ℂ n χ',
      ClassFunction.smul_apply, ClassFunction.smul_apply]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by rw [hval, hdeg, sub_self])
  have hgH : g ∈ H := by
    by_contra hgnH
    have hχg : χ g = 0 := by
      by_contra h
      exact hgnH (hyp.sMember_support_subset_H hχS (ClassFunction.mem_support.mpr h))
    have hχ'g : χ' g = 0 := by
      by_contra h
      exact hgnH (hyp.sMember_support_subset_H hχ'S (ClassFunction.mem_support.mpr h))
    exact hg (by rw [hval, hχg, hχ'g, mul_zero, mul_zero, sub_zero])
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **General `S`-combination support from degree 0.**  Any integer combination of `S`-members
(`φ ∈ ℤ[S]`) that vanishes at `1` is supported on `H^# = sharpImage H`.  Each `S`-member is
supported on `H` (`sMember_support_subset_H`), so `φ.support ⊆ H` (span induction); and `φ(1) = 0`
removes `1`.  This is the multi-term generalisation of `sMember_diffSupport_of_charValue_eq` /
`sMember_scaledDiffSupport_of_charValue_eq` — the supported↔degree-0 direction for the `S`-lattice,
the support side of the (6.8.1) `hgen'` decomposition. -/
theorem zSpan_S_support_subset_of_apply_one_eq_zero (hyp : SibleyDadeHypothesis G L H)
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.S) (h1 : φ 1 = 0) :
    φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  -- `ℤ[S] ⊆ {ψ | ψ.support ⊆ H}` by span induction (decoupled from `h1`).
  have hsuppH : ∀ ψ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.S, ψ.support ⊆ (H : Set ↥L) := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx => exact hyp.sMember_support_subset_H hx
    | zero => intro g hg; rw [ClassFunction.mem_support] at hg; exact absurd rfl hg
    | add x y _ _ hx hy =>
        intro g hg
        rcases ClassFunction.support_add_subset x y hg with h | h
        · exact hx h
        · exact hy h
    | smul c x _ hx =>
        intro g hg
        refine hx ?_
        rw [ClassFunction.mem_support] at hg ⊢
        intro hxg
        apply hg
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hxg, mul_zero]
  intro g hg
  have hgH : g ∈ H := hsuppH φ hφ hg
  have hg1 : g ≠ 1 := by
    rintro rfl; exact (ClassFunction.mem_support.mp hg) h1
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h => hg1 (OneMemClass.coe_eq_one.mp h)⟩

/-- **`S`-member degree ratio against a degree-`|W₁|` anchor.**

For `χ = Ind_H^L θ ∈ S` and an anchor `χ₁` of the minimal degree `χ₁(1) = |W₁|` (induced from a
degree-`1` source of `H`), the degree ratio `χ(1)/χ₁(1)` is the source degree `θ(1)`, a positive
natural number: `χ(1) = θ(1)·χ₁(1)` (`χ(1) = |L:H|·θ(1) = |W₁|·θ(1)`, `induce_apply_one`).  This
produces the integer degree `a = deg i` and the equation `χ(1) = a·χ₁(1)` that
`sMember_scaledDiffSupport_of_charValue_eq` (and `scaledDiff_dadeImage_mem_ZIrr`) consume for the
`hmemdegdiffsupp`/`hdiffasuppχ`/`htau1_memaχ` fields of the (6.2)/B1 member-family.  Applied with
`χ = χ₁` it gives the anchor ratio `a = 1` (`ha1`). -/
theorem sMember_charValue_one_eq_mul_anchor (hyp : SibleyDadeHypothesis G L H)
    {χ χ₁ : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ)) :
    ∃ a : ℕ, 0 < a ∧ χ 1 = (a : ℂ) * χ₁ 1 := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, -, hχeq⟩ := hχS
  obtain ⟨a, ha_pos, ha⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  refine ⟨a, ha_pos, ?_⟩
  rw [hχeq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, ha,
    hyp.index_H_eq_card_W1, hχ₁deg]
  ring

open scoped Classical in
/-- **Degree-ratio integrality against a base-block anchor.**  For `χ ∈ X(Z)` and a minimal-degree
anchor `χ₁ ∈ xBaseBlock Z`, the degree ratio `χ(1)/χ₁(1)` is a positive natural number:
`∃ d : ℕ, 0 < d ∧ χ(1) = d·χ₁(1)`.  Both source degrees are powers of `p` (`H` a `p`-group,
`IsIrreducibleCharacter.exists_charValue_one_eq_prime_pow_of_isPGroup`); minimality
(`natDegree_le_of_xBaseBlock_anchor`) gives `χ₁(1) ≤ χ(1)`, so the smaller `p`-power divides the
larger and the ratio `p^{k−k₁}` is a positive integer.  This is the `dᵢ ∈ ℤ` datum of the (6.8.1)
`hgen'` decomposition (the degree side; `zSpan_S_support_subset_of_apply_one_eq_zero` is the support
side).

Only `X`-irreducibility (`hX`) is used from the ambient hypothesis, so this form serves both the
Frobenius case (`exists_charValue_one_eq_mul_xBaseBlock_anchor`) and case (A) / c2 (where `hX` is
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`). -/
theorem exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) {Z : Subgroup ↥L}
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {χ χ₁ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) (hχ₁base : χ₁ ∈ hyp.xBaseBlock Z) :
    ∃ d : ℕ, 0 < d ∧ χ 1 = (d : ℂ) * χ₁ 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  -- sources of `χ` and `χ₁`.
  have hχS : χ ∈ hyp.S := hyp.Xset_subset_S hχX
  have hχ₁S : χ₁ ∈ hyp.S := hyp.Xset_subset_S (hyp.xBaseBlock_subset Z hχ₁base)
  rw [hyp.S_eq] at hχS hχ₁S
  obtain ⟨θ, -, hχeq⟩ := hχS
  obtain ⟨θ₁, -, hχ₁eq⟩ := hχ₁S
  obtain ⟨a, ha_pos, ha⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  obtain ⟨a₁, ha₁_pos, ha₁⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ₁
  -- source degrees are `p`-powers.
  obtain ⟨k, hk⟩ := θ.2.exists_charValue_one_eq_prime_pow_of_isPGroup hHp
  obtain ⟨k₁, hk₁⟩ := θ₁.2.exists_charValue_one_eq_prime_pow_of_isPGroup hHp
  have hak : a = p ^ k := by exact_mod_cast ha.symm.trans hk
  have ha₁k₁ : a₁ = p ^ k₁ := by exact_mod_cast ha₁.symm.trans hk₁
  -- `χ(1) = |W₁|·a`, `χ₁(1) = |W₁|·a₁` (nat degrees).
  have hχ1 : χ 1 = ((Nat.card hyp.W1 * a : ℕ) : ℂ) := by
    rw [hχeq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, ha,
      hyp.index_H_eq_card_W1]; push_cast; ring
  have hχ₁1 : χ₁ 1 = ((Nat.card hyp.W1 * a₁ : ℕ) : ℂ) := by
    rw [hχ₁eq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, ha₁,
      hyp.index_H_eq_card_W1]; push_cast; ring
  -- minimality of `χ₁`: `|W₁|·a₁ ≤ |W₁|·a`, hence `a₁ ≤ a`, hence `k₁ ≤ k`.
  have hirr : IsIrreducibleCharacter χ := hX χ hχX
  have hirr₁ : IsIrreducibleCharacter χ₁ := hX χ₁ (hyp.xBaseBlock_subset Z hχ₁base)
  have hle : Nat.card hyp.W1 * a₁ ≤ Nat.card hyp.W1 * a :=
    hyp.natDegree_le_of_xBaseBlock_anchor (χ₁ := ⟨χ₁, hirr₁⟩) (χ := ⟨χ, hirr⟩) hχ₁base hχX hχ₁1 hχ1
  have hW1pos : 0 < Nat.card hyp.W1 := Nat.card_pos
  have ha₁a : a₁ ≤ a := Nat.le_of_mul_le_mul_left hle hW1pos
  have hkk₁ : k₁ ≤ k := by
    rw [hak, ha₁k₁] at ha₁a; exact (Nat.pow_le_pow_iff_right hp.one_lt).mp ha₁a
  -- the ratio is `p^{k−k₁}`.
  refine ⟨p ^ (k - k₁), pow_pos hp.pos _, ?_⟩
  have hap : a = p ^ (k - k₁) * a₁ := by rw [hak, ha₁k₁, ← pow_add]; congr 1; omega
  rw [hχ1, hχ₁1]
  have : Nat.card hyp.W1 * a = p ^ (k - k₁) * (Nat.card hyp.W1 * a₁) := by rw [hap]; ring
  rw [this]; push_cast; ring

/-- **(6.2) member-family core for `S₁ ⊆ S`** (Frobenius case): the flat enumeration of `S₁` with
its per-member orthonormality, non-realness, conjugate-difference support, and `S₁`-membership
facts.

For a finite conjugation-closed `S₁ ⊆ S`, `exists_finEnum_irreducible` gives an injective family
`χmem : Fin k → Irr L` with range `S₁`; the per-member helpers (`sMember_characterFacts`,
`sMember_diffSupport`) and conjugation-closure of `S₁` discharge the `hmemreal`/`hmemconjortho`/
`hmemortho`/`hmemdiffsupp`/`hmemS1`/`hmembarS1` fields that B1
(`coherentDegreeSumBound_of_not_coherent`) consumes.  The degree data
(`deg`/`hmemdegdiffsupp`, from `sMember_charValue_one_eq_mul_anchor`) is layered on separately. -/
theorem exists_sMemberOrthonormalFamily (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ)) ∧
      (∀ j, ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ).conj ∈ S₁) ∧
      (∀ j, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ).conj = 0) ∧
      (∀ i j, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ) = if i = j then (1 : ℂ) else 0) := by
  have hS₁irr : ∀ φ ∈ S₁, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF (hS₁sub hφ)
  obtain ⟨k, χmem, hχinj, hrange⟩ := exists_finEnum_irreducible hS₁fin hS₁irr
  have hmemS1 : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j; rw [← hrange]; exact Set.mem_range_self j
  refine ⟨k, χmem, hχinj, hrange, ?_, ?_, hmemS1, ?_, ?_, ?_⟩
  · intro j
    exact (hyp.sMember_characterFacts hF (hS₁sub (hmemS1 j))).1
  · intro j
    exact hyp.sMember_diffSupport (hS₁sub (hmemS1 j)) (χmem j).2
  · intro j
    exact hS₁conj (hmemS1 j)
  · intro j
    exact (hyp.sMember_characterFacts hF (hS₁sub (hmemS1 j))).2.2.2.2
  · intro i j
    rw [irreducibleCharacter_inner_eq_ite (χmem i) (χmem j)]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · rw [if_neg (fun he => h (hχinj he)), if_neg h]

/-- **(6.2) member-family degree data** (Frobenius case): integer degree ratios against a
degree-`|W₁|` anchor.

Given a family `χmem` of `S`-members and a distinguished index `i₁` whose member has the minimal
degree `χmem i₁ (1) = |W₁|`, every member has a positive integer degree ratio
`χmem j (1) = (deg j)·χmem i₁ (1)` (the source degree, `sMember_charValue_one_eq_mul_anchor`), the
anchor ratio is `deg i₁ = 1` (cancel the nonzero `|W₁|`), and each scaled difference
`χmem j − deg j·χmem i₁` is supported on `H^#` (`sMember_scaledDiffSupport_of_charValue_eq`).  This
is the `deg`/`ha1`/`hmemdegdiffsupp` data that layers on `exists_sMemberOrthonormalFamily` to
complete the (6.2)/B1 member-family. -/
theorem exists_sMemberDegreeData (hyp : SibleyDadeHypothesis G L H)
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L} {i₁ : Fin k}
    (hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.S)
    (hanchordeg : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (Nat.card hyp.W1 : ℂ)) :
    ∃ deg : Fin k → ℕ, deg i₁ = 1 ∧ (∀ j, 0 < deg j) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) 1 =
        (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1) ∧
      (∀ j, ((χmem j : ClassFunction ↥L ℂ) - deg j • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  choose deg hdeg_pos hdeg_eq using fun j =>
    hyp.sMember_charValue_one_eq_mul_anchor (hmemS j) hanchordeg
  have hW1ne : (Nat.card hyp.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨deg, ?_, hdeg_pos, hdeg_eq, fun j =>
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hmemS j) (hmemS i₁) (hdeg_eq j)⟩
  have h := hdeg_eq i₁
  rw [hanchordeg] at h
  have hdeg1 : (deg i₁ : ℂ) = 1 :=
    mul_right_cancel₀ hW1ne (by rw [one_mul]; exact h.symm)
  exact_mod_cast hdeg1

/-- **(6.2) anchor existence: `S(A)` contains a member of the minimal degree `|W₁|`.**

When the section `H/(A.subgroupOf H)` has a proper commutator subgroup (e.g. `A ⊊ H` with `H`
solvable, so `H/A` is a nontrivial solvable group), it carries a nontrivial degree-`1` character
trivial on `A` (`exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top`); its
induction `Ind_H^L θ ∈ S(A)` has degree `|L:H|·1 = |W₁|`
(`induce_apply_one_eq_card_W1_of_degree_one`).  This furnishes the degree-`|W₁|` anchor `χ₁`
consumed by `exists_sMemberDegreeData` (its `hanchordeg`). -/
theorem exists_mem_SsubFiltration_degree_W1 (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {A : Subgroup ↥L} [A.Normal]
    (h : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤) :
    ∃ φ, φ ∈ hyp.SsubFiltration A ∧ (φ : ClassFunction ↥L ℂ) 1 = (Nat.card hyp.W1 : ℂ) := by
  obtain ⟨θ, hθne, hθker, hθdeg⟩ :=
    exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top (A.subgroupOf H) h
  refine ⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), ?_, ?_⟩
  · rw [hyp.mem_SsubFiltration]; exact ⟨θ, hθne, hθker, rfl⟩
  · exact hyp.induce_apply_one_eq_card_W1_of_degree_one θ hθdeg

/-- **(6.2) adjoined-pair fields for the breaking pair `{ψ, ψ̄}`** (Frobenius case).

For `ψ ∈ S` whose conjugate pair `{ψ, ψ̄}` is disjoint from `S₁ ⊆ S`, this packages the per-`ψ`
fields B1 (`coherentDegreeSumBound_of_not_coherent`) consumes: non-realness and orthonormality of
`{ψ, ψ̄}` (`sMember_characterFacts`), the conjugate-difference support on `H^#`
(`sMember_diffSupport`), and the orthogonality of `ψ` and `ψ̄` to every member of `S₁` (distinct
irreducibles, since `ψ, ψ̄ ∉ S₁` but the members lie in `S₁`).  Together with
`exists_coherentBreakPair` (which supplies `ψ ∉ S₁`, `ψ̄ ∉ S₁`) this is the adjoined-pair side of
the (6.2) member-family. -/
theorem sBreakPair_fields (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {ψ : ClassFunction ↥L ℂ} {S₁ : Set (ClassFunction ↥L ℂ)}
    (hψS : ψ ∈ hyp.S) (hS₁sub : S₁ ⊆ hyp.S) (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁) :
    ¬ ClassFunction.IsReal ψ ∧
      ClassFunction.inner ψ ψ = 1 ∧ ClassFunction.inner ψ.conj ψ.conj = 1 ∧
      ClassFunction.inner ψ.conj ψ = 0 ∧ ClassFunction.inner ψ ψ.conj = 0 ∧
      ((ψ.conj - ψ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      (∀ χ ∈ S₁, ClassFunction.inner ψ χ = 0) ∧
      (∀ χ ∈ S₁, ClassFunction.inner ψ.conj χ = 0) := by
  have hψirr : IsIrreducibleCharacter ψ := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hψS
  obtain ⟨hreal, hψψ, hψbarψbar, hψbarψ, hψψbar⟩ := hyp.sMember_characterFacts hF hψS
  refine ⟨hreal, hψψ, hψbarψbar, hψbarψ, hψψbar,
    hyp.sMember_diffSupport hψS hψirr, ?_, ?_⟩
  · intro χ hχS1
    have hχirr : IsIrreducibleCharacter χ :=
      hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF (hS₁sub hχS1)
    have hne : ψ ≠ χ := fun h => hψnotS1 (by rw [h]; exact hχS1)
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hψirr⟩ : IrreducibleCharacter ↥L) ⟨χ, hχirr⟩
    rwa [if_neg (fun he => hne (congrArg Subtype.val he))] at h
  · intro χ hχS1
    have hχirr : IsIrreducibleCharacter χ :=
      hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF (hS₁sub hχS1)
    have hne : ψ.conj ≠ χ := fun h => hψcnotS1 (by rw [h]; exact hχS1)
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ.conj, hψirr.conj⟩ : IrreducibleCharacter ↥L)
      ⟨χ, hχirr⟩
    rwa [if_neg (fun he => hne (congrArg Subtype.val he))] at h

/-- **(T8.11e) scaled supported differences map to virtual characters.**

Once the degree-ratio support field for `χ - aχ₁` is known, the real Dade map sends that
scaled difference to `ℤ[Irr G]`.  This is exactly the `htau1_memaχ` field of
`XAdjoinStepInput`, separated from the arithmetic that produces the ratio and support. -/
theorem scaledDiff_dadeImage_mem_ZIrr (hyp : SibleyDadeHypothesis G L H)
    {χ χ₁ : IrreducibleCharacter ↥L} {a : ℕ}
    (hdiffasupp : ((χ : ClassFunction ↥L ℂ) - a • (χ₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    hyp.tau ((χ : ClassFunction ↥L ℂ) - a • (χ₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G := by
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dade hyp.hconj hdiffasupp
    (Submodule.sub_mem _ χ.mem_ZIrr (nsmul_mem χ₁.mem_ZIrr a))

/-- **(T8.11f) X-members with a degree ratio have supported scaled difference.**

This is the `X = S - S(Z)` adapter for `sMember_scaledDiffSupport_of_charValue_eq`: once
the degree-ratio equation `χ(1)=aχ₁(1)` is available, the scaled difference
`χ-aχ₁` is supported on `H^#`. -/
theorem xMember_scaledDiffSupport_of_degreeData (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} {χ χ₁ : IrreducibleCharacter ↥L} {a : ℕ}
    (hχX : (χ : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hχ₁X : (χ₁ : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hdeg : (χ : ClassFunction ↥L ℂ) 1 = (a : ℂ) * (χ₁ : ClassFunction ↥L ℂ) 1) :
    ((χ : ClassFunction ↥L ℂ) - a • (χ₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  exact hyp.sMember_scaledDiffSupport_of_charValue_eq
    (hyp.mem_Xset.mp hχX).1 (hyp.mem_Xset.mp hχ₁X).1 hdeg

/-- **(T8.11g) member-family scaled supports from degree data.**

Given a finite accumulator family inside `X` and degree ratios against the distinguished member
`χ₁`, all scaled member differences `χᵢ-degᵢχ₁` are supported on `H^#`.  This is the
`hmemdegdiffsupp` half of `XAdjoinStepInput`, separated from the arithmetic that constructs the
ratios. -/
theorem xMember_scaledDiffSupports_of_degreeData (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} {ι : Type*} {s : Finset ι}
    {χmem : ι → IrreducibleCharacter ↥L} {deg : ι → ℕ} {i₁ : ι}
    (hmemX : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hi₁ : i₁ ∈ s)
    (hdeg : ∀ i ∈ s,
      (χmem i : ClassFunction ↥L ℂ) 1 =
        (deg i : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1) :
    ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  intro i hi
  exact hyp.xMember_scaledDiffSupport_of_degreeData (hmemX i hi) (hmemX i₁ hi₁) (hdeg i hi)

open scoped Classical in
/-- **(6.2) member-family → B1 degree-sum bound.**

Assembles the (6.2) member-family for a coherent `S₁` and the breaking pair `{ψ, ψ̄}`, feeding it to
B1 (`coherentDegreeSumBound_of_not_coherent`).  When `S₁` (conjugation-closed, coherent, `⊆ S`)
contains the degree-`|W₁|` anchor `χ₁`, `ψ ∈ S` with `{ψ, ψ̄}` disjoint from `S₁`, and `S₁ ∪ {ψ, ψ̄}`
is not coherent, the degree-ratio sum is bounded by `∑ⱼ (degⱼ)² ≤ 2·a`, where `degⱼ = χⱼ(1)/χ₁(1)`
and `a = ψ(1)/χ₁(1)`.

All member-family fields are discharged from the landed pieces: the per-member core
(`exists_sMemberOrthonormalFamily`), the degree data (`exists_sMemberDegreeData`), the adjoined-pair
fields (`sBreakPair_fields`), the scaled-difference support + Dade image
(`sMember_scaledDiffSupport_of_charValue_eq`, `scaledDiff_dadeImage_mem_ZIrr`), and the abstract
S07 generation bridges (`…_scaledDiffs`, `…_anchorGeneration`).  This is the (6.2) step
"`2ψ(1)|L:K| ≥ ∑_{χ∈S₁} χ(1)²/‖χ‖²`" in normalized integer form. -/
theorem sMember_degreeSumBound_of_not_coherent (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁sub : S₁ ⊆ hyp.S) (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L) (deg : Fin k → ℕ) (a : ℕ),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (deg j : ℂ) * χ₁ 1) ∧
      ψ 1 = (a : ℂ) * χ₁ 1 ∧
      ∑ j : Fin k, ((deg j : ℝ)) ^ 2 ≤ 2 * (a : ℝ) := by
  classical
  -- (1) enumerate `S₁` with the per-member fields
  obtain ⟨k, χmem, hχinj, hrange, hmemreal, hmemdiffsupp, hmemS1, hmembarS1,
    hmemconjortho, hmemortho⟩ := hyp.exists_sMemberOrthonormalFamily hF hS₁sub hS₁conj hS₁fin
  -- (2) locate the anchor index `i₁` (the anchor lies in `S₁ = range χmem`)
  have hχ₁range : χ₁ ∈ Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) := by
    rw [hrange]; exact hχ₁S₁
  obtain ⟨i₁, hi₁eq0⟩ := hχ₁range
  have hi₁eq : (χmem i₁ : ClassFunction ↥L ℂ) = χ₁ := hi₁eq0
  have hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.S := fun j => hS₁sub (hmemS1 j)
  have hanchordeg : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (Nat.card hyp.W1 : ℂ) := by
    rw [hi₁eq]; exact hχ₁deg
  -- (3) degree data
  obtain ⟨deg, hdeg_i₁, _hdeg_pos, hdeg_eq, hmemdegdiffsupp⟩ :=
    hyp.exists_sMemberDegreeData hmemS hanchordeg
  -- (4) breaking-pair fields
  obtain ⟨hrealψ, hψψ, hψbarψbar, hψbarψ, hψψbar, hdiffsuppψ, hψ_S1, hψbar_S1⟩ :=
    hyp.sBreakPair_fields hF hψS hS₁sub hψnotS1 hψcnotS1
  -- (5) the `ψ` degree ratio `a`
  obtain ⟨a, _ha_pos, hψratio⟩ := hyp.sMember_charValue_one_eq_mul_anchor hψS hanchordeg
  -- (6) `ψ` scaled-difference support + Dade image (the `ψ`-side `hdiffasuppχ`/`htau1_memaχ`)
  have hdiffasuppψ : (ψ - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq hψS (hmemS i₁) hψratio
  have htau1ψ : hyp.tau (ψ - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G :=
    hyp.scaledDiff_dadeImage_mem_ZIrr (χ := ⟨ψ, hψirr⟩) (χ₁ := χmem i₁) hdiffasuppψ
  -- (7) generation fields via the abstract S07 bridges (`hSgen`, `hgen`)
  have hcover : ∀ x ∈ S₁, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧
      (χmem j : ClassFunction ↥L ℂ) = x := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, Finset.mem_univ j, hj⟩
  have hSgen := OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
    (s := (Finset.univ : Finset (Fin k))) (χmem := fun j => (χmem j : ClassFunction ↥L ℂ))
    (deg := deg) (i₁ := i₁) hcover (Finset.mem_univ i₁) (fun j _ => hmemS1 j)
    (fun j _ => hmemdegdiffsupp j)
  have hbar1 : ψ.conj 1 = ψ 1 := by
    rw [ClassFunction.conj_apply]
    obtain ⟨n, -, hn1, -⟩ := hψirr.exists_natDegree_charValue_one_dvd_card
    rw [hn1, star_natCast]
  have hchi1_ne : (χmem i₁ : ClassFunction ↥L ℂ) 1 ≠ 0 := by
    rw [hanchordeg]; exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    intro hmem
    exact hmem.2 (by simp)
  have hgen := OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
    (χ := ψ) (chibar := ψ.conj) (chi1 := (χmem i₁ : ClassFunction ↥L ℂ)) (a := a)
    hSgen hψratio hbar1 hchi1_ne h1A
  -- (8) feed everything to B1
  refine ⟨k, χmem, deg, a, hχinj, hrange, fun j => by rw [hdeg_eq j, hi₁eq],
    by rw [hψratio, hi₁eq], ?_⟩
  have hbound := coherentDegreeSumBound_of_not_coherent hyp.dade hyp.hconj hS₁coh
    ⟨ψ, hψirr⟩ hrealψ hdiffsuppψ hψψ hψbarψbar hψψbar hψbarψ hψ_S1 hψbar_S1
    (Finset.univ : Finset (Fin k)) χmem deg i₁ (Finset.mem_univ i₁)
    (fun j _ => hmemreal j) (fun j _ => hmemdiffsupp j) (fun j _ => hmemdegdiffsupp j)
    (fun j _ => hmemS1 j) (fun j _ => hmembarS1 j) (fun j _ => hmemconjortho j)
    (fun i _ j _ => by rw [hmemortho i j]; rcases eq_or_ne i j with h | h <;> simp [h])
    hdiffasuppψ htau1ψ hdeg_i₁ hSgen hgen hnc
  simpa using hbound

/-- **(6.2) member-family degree-square bound** (real form).

The degree-sum bound `sMember_degreeSumBound_of_not_coherent` (`∑ⱼ (degⱼ)² ≤ 2a`), rescaled by the
anchor degree `χ₁(1) = |W₁|`, gives the character-degree-square sum over the enumerated `S₁`-family:
`∑ⱼ (χⱼ(1))² ≤ 2·ψ(1)·χ₁(1)` (real parts), since `χⱼ(1) = degⱼ·χ₁(1)` and `ψ(1) = a·χ₁(1)`.  This is
the (6.2) bound `∑_{χ∈S₁} χ(1)² ≤ 2ψ(1)χ₁(1)` in the form ready to be compared, via `S(A) ⊆ S₁`,
with the `S(A)` degree-sum identity B2. -/
theorem sMember_degreeSqReBound_of_not_coherent (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁sub : S₁ ⊆ hyp.S) (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁) ∧
      ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 ≤
        2 * (ψ 1).re * (χ₁ 1).re := by
  obtain ⟨k, χmem, deg, a, hχinj, hrange, hdeg_eq, hψ_eq, hbound⟩ :=
    hyp.sMember_degreeSumBound_of_not_coherent hF hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁ hχ₁deg
      hψS hψirr hψnotS1 hψcnotS1 hnc
  have hmemS1 : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j; rw [← hrange]; exact ⟨j, rfl⟩
  refine ⟨k, χmem, hχinj, hrange, hmemS1, ?_⟩
  -- real parts of the degree relations
  have hdegre : ∀ j, ((χmem j : ClassFunction ↥L ℂ) 1).re = (deg j : ℝ) * (χ₁ 1).re := by
    intro j
    rw [hdeg_eq j, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  have hψre : (ψ 1).re = (a : ℝ) * (χ₁ 1).re := by
    rw [hψ_eq, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  have hre_nonneg : (0 : ℝ) ≤ (χ₁ 1).re ^ 2 := sq_nonneg _
  calc ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2
      = ∑ j : Fin k, ((deg j : ℝ) * (χ₁ 1).re) ^ 2 := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hdegre j]
    _ = (χ₁ 1).re ^ 2 * ∑ j : Fin k, (deg j : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
    _ ≤ (χ₁ 1).re ^ 2 * (2 * (a : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hbound hre_nonneg
    _ = 2 * ((a : ℝ) * (χ₁ 1).re) * (χ₁ 1).re := by ring
    _ = 2 * (ψ 1).re * (χ₁ 1).re := by rw [hψre]

open scoped Classical in
/-- **(6.2) B2 in real / Frobenius form.**

In the Frobenius case every member of `S(A)` is an irreducible induced character
(`isIrreducibleCharacter_of_mem_S_of_frobenius`), so `χ(1)²/‖χ‖² = (χ(1).re)²` (`‖χ‖² = 1`, `χ(1)`
a real natural number), and B2 (`sum_div_normSq_induce_kernelFilter_eq`) becomes the real
degree-square identity `∑_{χ∈S(A)} (χ(1).re)² = |L:H|·(|H:A| − 1)`. -/
theorem sum_re_sq_induce_kernelFilter_eq (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {A : Subgroup ↥L} [A.Normal] :
    ∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction),
        ((χ 1).re) ^ 2
      = (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hB2 := sum_div_normSq_induce_kernelFilter_eq (G := ↥L) (H := H) (A := A)
  have hsummand : ∀ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
      (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥H ℂ) ∧
        θ ≠ trivialIrreducibleCharacter ↥H)).image
      (fun θ => ClassFunction.induce H θ.toClassFunction),
      χ 1 ^ 2 / ClassFunction.inner χ χ = ((((χ 1).re) ^ 2 : ℝ) : ℂ) := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    have hθne : θ ≠ trivialIrreducibleCharacter ↥H := (Finset.mem_filter.mp hθ).2.2
    have hχS : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ∈ hyp.S := by
      rw [hyp.S_eq]; exact ⟨θ, hθne, rfl⟩
    have hirr := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hχS
    have hinner : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
        (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite (⟨_, hirr⟩ : IrreducibleCharacter ↥L) ⟨_, hirr⟩
    obtain ⟨n, -, hn1, -⟩ := hirr.exists_natDegree_charValue_one_dvd_card
    rw [hinner, div_one, hn1, Complex.natCast_re]; push_cast; ring
  have key : ((∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction),
        ((χ 1).re) ^ 2 : ℝ) : ℂ)
      = (((H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1)) : ℝ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun χ hχ => (hsummand χ hχ).symm), hB2]
    push_cast; ring
  exact Complex.ofReal_inj.mp key

open scoped Classical in
/-- **(6.6) X degree-sum identity (Frobenius case).**

The degree-square sum over `X = S − S(Z)` is `|L:H| · (|H| − |H:Z|)`.  Since `S = S(⊥)` and
`S(Z) ⊆ S`, this is the difference of two instances of the `S(A)` degree-sum identity
`sum_re_sq_induce_kernelFilter_eq` (at `A = ⊥`, using `|H ⧸ ⊥| = |H|`, and at `A = Z`).  This is
the `total` of the X-chain step data: the (6.6) divisibility argument shows the source degree
`θχ(1)²` divides it. -/
theorem sum_re_sq_Xset_eq (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {Z : Subgroup ↥L} [Z.Normal] :
    ∑ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
        ((χ 1).re) ^ 2
      = (H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ)) := by
  letI : H.Normal := hyp.H_normal
  have hbotker : ∀ θ : IrreducibleCharacter ↥H,
      (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro θ x hx
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
    subst hx
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  have hsub : (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) ⊆
      (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) := by
    apply Finset.image_subset_image
    intro θ hθ
    rw [Finset.mem_filter] at hθ ⊢
    exact ⟨hθ.1, hbotker θ, hθ.2.2⟩
  have hsd := Finset.sum_sdiff (f := fun χ : ClassFunction ↥L ℂ => ((χ 1).re) ^ 2) hsub
  have h0 := hyp.sum_re_sq_induce_kernelFilter_eq hF (A := (⊥ : Subgroup ↥L))
  have hZ := hyp.sum_re_sq_induce_kernelFilter_eq hF (A := Z)
  have hbotcard : Nat.card (↥H ⧸ (⊥ : Subgroup ↥L).subgroupOf H) = Nat.card ↥H := by
    rw [Subgroup.bot_subgroupOf]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := ↥H)).toEquiv
  rw [hbotcard] at h0
  rw [eq_sub_of_add_eq hsd, h0, hZ]
  ring

open scoped Classical in
/-- **(6.6) X degree-sum identity, CertainType (case B) form.**  The Frobenius proof
(`sum_re_sq_Xset_eq`) routes the degree-square sum over `X = S − S(Z)` through
`sum_re_sq_induce_kernelFilter_eq`, which converts each summand `χ(1)²/‖χ‖² = (χ(1).re)²`
using that **every** member of `S` is irreducible (Frobenius).  In case B `S` carries `w₂−1`
reducible members, so that conversion fails on `S`.  But `X` itself is irreducible
(Peterfalvi (6.8.1) for (c2): the reducibles all lie in `S(Z)`, and `X = S ∖ S(Z)`), so the
conversion holds **on `X`** alone.  The orbit-counting identity `sum_div_normSq_induce_kernelFilter_eq`
(in the `χ(1)²/‖χ‖²` form — valid for reducibles) supplies the two filter sums, and
`Finset.sum_sdiff` extracts `∑_X = ∑_{S} − ∑_{S(Z)}`; the `X`-irreducibility hypothesis converts
only the `X`-side terms.  This unblocks the case-B (CB3 math-A / CB4 math-B) `hstepData` `total`. -/
theorem sum_re_sq_Xset_eq_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} [Z.Normal]
    (hX : ∀ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
        IsIrreducibleCharacter χ) :
    ∑ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
        ((χ 1).re) ^ 2
      = (H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ)) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hbotker : ∀ θ : IrreducibleCharacter ↥H,
      (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro θ x hx
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
    subst hx
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  have hsub : (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) ⊆
      (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) := by
    apply Finset.image_subset_image
    intro θ hθ
    rw [Finset.mem_filter] at hθ ⊢
    exact ⟨hθ.1, hbotker θ, hθ.2.2⟩
  have hsd := Finset.sum_sdiff
    (f := fun χ : ClassFunction ↥L ℂ => χ 1 ^ 2 / ClassFunction.inner χ χ) hsub
  have hB2bot := sum_div_normSq_induce_kernelFilter_eq (G := ↥L) (H := H) (A := (⊥ : Subgroup ↥L))
  have hB2Z := sum_div_normSq_induce_kernelFilter_eq (G := ↥L) (H := H) (A := Z)
  have hbotcard : Nat.card (↥H ⧸ (⊥ : Subgroup ↥L).subgroupOf H) = Nat.card ↥H := by
    rw [Subgroup.bot_subgroupOf]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := ↥H)).toEquiv
  rw [hbotcard] at hB2bot
  have hconv : ∀ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) \
      (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction)),
      χ 1 ^ 2 / ClassFunction.inner χ χ = ((((χ 1).re) ^ 2 : ℝ) : ℂ) := by
    intro χ hχ
    have hirr := hX χ hχ
    have hinner : ClassFunction.inner χ χ = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L)
        ⟨χ, hirr⟩
    obtain ⟨n, -, hn1, -⟩ := hirr.exists_natDegree_charValue_one_dvd_card
    rw [hinner, div_one, hn1, Complex.natCast_re]
    push_cast; ring
  have key : ((∑ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
        ((χ 1).re) ^ 2 : ℝ) : ℂ)
      = (((H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ))) : ℝ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun χ hχ => (hconv χ hχ).symm),
      eq_sub_of_add_eq hsd, hB2bot, hB2Z]
    push_cast; ring
  exact Complex.ofReal_inj.mp key

open scoped Classical in
/-- **Reindexing `X(Z)` to the `Irr L`-filter** (Frobenius case).  Any Finset `T` member-wise equal
to the central `(6.6)` set `X(Z) = {χ ∈ Irr L | Z ⊄ ker χ}`
(`Xset_eq_irreducible_not_subset_characterKernel`) sums the same as the `IrreducibleCharacter ↥L`
filter `{ψ | Z ⊄ ker ψ}` for any `ℂ`-valued function: the injective coercion
`IrreducibleCharacter ↥L ↪ ClassFunction ↥L ℂ` (`IrreducibleCharacter.ext`) is a bijection between
them.  This bridges the regular-character sums (`sumNonInflatedDegreeMulChar_of_mem`,
`sumNonInflatedDegreeSq`), stated over the `Irr`-filter, to the Sibley `X(Z)` index set. -/
theorem sum_Xset_eq_sum_filter_irreducible_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    {T : Finset (ClassFunction ↥L ℂ)} (hT : ∀ φ, φ ∈ T ↔ φ ∈ hyp.Xset Z)
    (f : ClassFunction ↥L ℂ → ℂ) :
    ∑ φ ∈ T, f φ = ∑ ψ ∈ Finset.univ.filter (fun ψ : IrreducibleCharacter ↥L =>
        ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction ↥L ℂ))),
        f (ψ : ClassFunction ↥L ℂ) := by
  classical
  have hXc : hyp.Xset Z = {χ : ClassFunction ↥L ℂ | IsIrreducibleCharacter χ ∧
      ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ)} :=
    hyp.Xset_eq_irreducible_not_subset_characterKernel hZH
      (fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)
  have hirrT : ∀ φ, φ ∈ T → IsIrreducibleCharacter φ := by
    intro φ hφ; have := (hT φ).mp hφ; rw [hXc] at this; exact this.1
  have hkerT : ∀ φ, φ ∈ T →
      ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel φ) := by
    intro φ hφ; have := (hT φ).mp hφ; rw [hXc] at this; exact this.2
  have hmemT : ∀ ψ : IrreducibleCharacter ↥L,
      ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction ↥L ℂ)) →
      (ψ : ClassFunction ↥L ℂ) ∈ T := by
    intro ψ hψ; rw [hT, hXc]; exact ⟨ψ.2, hψ⟩
  refine Finset.sum_bij'
    (fun φ hφ => (⟨φ, hirrT φ hφ⟩ : IrreducibleCharacter ↥L))
    (fun ψ _ => (ψ : ClassFunction ↥L ℂ))
    (fun φ hφ => ?_) (fun ψ hψ => ?_) (fun φ hφ => rfl) (fun ψ hψ => ?_) (fun φ hφ => rfl)
  · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hkerT φ hφ⟩
  · rw [Finset.mem_filter] at hψ; exact hmemT ψ hψ.2
  · apply IrreducibleCharacter.ext; rfl

open scoped Classical in
/-- **(6.8.1) regular-character value over `X(Z)`** (mmd 04.8 L168).  For the central `(6.6)` set
`X(Z)` and `z ∈ Z^#`, `∑_{χ ∈ X(Z)} χ(1)·χ(z) = -|L ⧸ Z|` — the off-identity value of
`∑ χ(1)·χ = ρ_L − ρ_{L/Z}` (the step showing `η₁^{τ₁}` is constant on `Z^#`).  Reindex
(`sum_Xset_eq_sum_filter_irreducible_of_frobenius`) + `sumNonInflatedDegreeMulChar_of_mem`. -/
theorem sum_degree_mul_charValue_Xset_eq_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    {T : Finset (ClassFunction ↥L ℂ)} (hT : ∀ φ, φ ∈ T ↔ φ ∈ hyp.Xset Z)
    {z : ↥L} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    ∑ φ ∈ T, (φ 1) * (φ z) = -(Nat.card (↥L ⧸ Z) : ℂ) := by
  rw [hyp.sum_Xset_eq_sum_filter_irreducible_of_frobenius hF hZH hT (fun φ => φ 1 * φ z)]
  exact OddOrder.RepresentationTheory.sumNonInflatedDegreeMulChar_of_mem (N := Z) hz hz1

open scoped Classical in
/-- **(6.8.1) degree-square value over `X(Z)`** (mmd 04.8, the `z = 1` companion).  For the central
`(6.6)` set `X(Z)`, `∑_{χ ∈ X(Z)} χ(1)·χ(1) = |L| − |L ⧸ Z|`.  Reindex
(`sum_Xset_eq_sum_filter_irreducible_of_frobenius`) + `sumNonInflatedDegreeSq`. -/
theorem sum_degree_sq_Xset_eq_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    {T : Finset (ClassFunction ↥L ℂ)} (hT : ∀ φ, φ ∈ T ↔ φ ∈ hyp.Xset Z) :
    ∑ φ ∈ T, (φ 1) * (φ 1) = (Nat.card ↥L : ℂ) - (Nat.card (↥L ⧸ Z) : ℂ) := by
  rw [hyp.sum_Xset_eq_sum_filter_irreducible_of_frobenius hF hZH hT (fun φ => φ 1 * φ 1)]
  rw [← OddOrder.RepresentationTheory.sumNonInflatedDegreeSq (N := Z)]
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  rw [pow_two]

open scoped Classical in
/-- **(6.8.1) regular-character difference value over `X(Z)`** (mmd 04.8 L168, combined form).  For
the central `(6.6)` set `X(Z)` and `z ∈ Z^#`, `∑_{χ ∈ X(Z)} χ(1)·(χ(z) − χ(1)) = -|L|`.  This is
`(ρ_L − ρ_{L/Z})(z) − (ρ_L − ρ_{L/Z})(1) = -|L:Z| − (|L| − |L:Z|) = -|L|` (the off-identity minus the
degree value), which divided by `a|W₁| = χ₁(1)` gives `∑dᵢχᵢ(z) − ∑dᵢχᵢ(1) = -|H|/a` — the key
constant in showing `η₁^{τ₁}` is constant on `Z^#`. -/
theorem sum_degree_mul_charValue_sub_Xset_eq_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    {T : Finset (ClassFunction ↥L ℂ)} (hT : ∀ φ, φ ∈ T ↔ φ ∈ hyp.Xset Z)
    {z : ↥L} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    ∑ φ ∈ T, (φ 1) * (φ z - φ 1) = -(Nat.card ↥L : ℂ) := by
  have hexpand : ∑ φ ∈ T, (φ 1) * (φ z - φ 1)
      = (∑ φ ∈ T, (φ 1) * φ z) - (∑ φ ∈ T, (φ 1) * φ 1) := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun φ _ => ?_); ring
  rw [hexpand, hyp.sum_degree_mul_charValue_Xset_eq_of_frobenius hF hZH hT hz hz1,
    hyp.sum_degree_sq_Xset_eq_of_frobenius hF hZH hT]
  ring

/-- **(6.6) `htotal` factorization.**  `|L:H|·(|H| − |H:Z|) = |H:Z| · (|L:H|·(|Z| − 1))` (Lagrange
`|H| = |H:Z|·|Z|`).  With the X degree-sum `total = |L:H|·(|H| − |H:Z|)` (`sum_re_sq_Xset_eq`), this
is the `total = qtot · c` of the X-chain step data with `qtot = |H:Z|`, `c = |L:H|·(|Z| − 1)`. -/
theorem index_mul_card_sub_factor (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L} [Z.Normal] :
    H.index * (Nat.card ↥H - Nat.card (↥H ⧸ Z.subgroupOf H))
      = Nat.card (↥H ⧸ Z.subgroupOf H) * (H.index * (Nat.card ↥(Z.subgroupOf H) - 1)) := by
  have hlag : Nat.card ↥H
      = Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf H)
  have hz : 1 ≤ Nat.card ↥(Z.subgroupOf H) := Nat.card_pos
  obtain ⟨w, hw⟩ : ∃ w, Nat.card ↥(Z.subgroupOf H) = w + 1 := ⟨_, (Nat.sub_add_cancel hz).symm⟩
  rw [hlag, hw]
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
  ring

/-- **(6.8.3) arithmetic core.**  The numeric contradiction closing the (6.8.3) extension in case
(A).  From the break-pair (5.6) bound `∑_{χ∈X} χ(1)² < 2ψ(1)η₁(1)` — i.e.
`|W₁|·|H:Z|·(|Z|−1) < 2·|W₁|²·d` with `ψ(1) = |W₁|d`, `η₁(1) = |W₁|` — together with [Is] Cor 2.30
`d² ≤ |H:Z|` (valid since `Z` is central) and the fixed-point-free bound `|Z|−1 ≥ 2|W₁|`
(`W₁` acts FPF on the odd-order `Z`), one derives `|H:Z| < d ≤ d² ≤ |H:Z|`, a contradiction.

Here `w1 = |W₁|`, `d = θ(1)` (the degree of the `H`-source of `ψ`), `hZ = |H:Z|`, `cZ = |Z|`.
The hypothesis `2 ≤ hZ` holds because `Z ⊆ H′ ⊊ H` (`H` non-abelian), so `|H:Z| ≥ |H:H′| ≥ 2`. -/
theorem false_of_centralCommutator_break_arith {w1 d hZ cZ : ℕ}
    (hw1 : 1 ≤ w1) (hd : 1 ≤ d) (hdsq : d ^ 2 ≤ hZ) (hZ2 : 2 ≤ hZ)
    (hfpf : 2 * w1 ≤ cZ - 1)
    (hbreak : w1 * hZ * (cZ - 1) ≤ 2 * w1 ^ 2 * d) : False := by
  set m := cZ - 1 with hm
  have hge : 2 * w1 ^ 2 * hZ ≤ w1 * hZ * m := by
    calc 2 * w1 ^ 2 * hZ = w1 * hZ * (2 * w1) := by ring
      _ ≤ w1 * hZ * m := mul_le_mul_left' hfpf (w1 * hZ)
  have hle : 2 * w1 ^ 2 * hZ ≤ 2 * w1 ^ 2 * d := le_trans hge hbreak
  have hZd : hZ ≤ d := Nat.le_of_mul_le_mul_left hle (by positivity)
  have h2d : 2 ≤ d := le_trans hZ2 hZd
  have hdd : 2 * d ≤ d ^ 2 := by nlinarith [h2d]
  omega

/-- **(6.6) per-member degree shape.**  Every member `χ = Ind_H^L θ` of `S` (`θ ∈ Irr H`) has degree
`χ(1) = |L:H| · θ(1)`; when `H` is a `p`-group `θ(1) = p^k`, so `χ(1) = |L:H| · p^k`.  This is the
common-index `p`-power degree shape (`idx = |L:H|`) of every X-chain member. -/
theorem exists_index_primePow_degree_of_mem_S (hyp : SibleyDadeHypothesis G L H)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.S) :
    ∃ k : ℕ, χ 1 = ((H.index * p ^ k : ℕ) : ℂ) := by
  rw [hyp.S_eq, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, _hθ, rfl⟩ := hχ
  obtain ⟨k, hk⟩ := exists_primePow_natDegree_of_isPGroup hp hHp θ
  refine ⟨k, ?_⟩
  rw [ClassFunction.induce_apply_one, hk]
  push_cast; ring

/-- **(6.6) per-member degree data for an X-member family.**  Vectorizes
`exists_index_primePow_degree_of_mem_S` over a finite family `χmem : Fin k → Irr L` of `S`-members:
there are exponents `mmem j` with `χmem j (1) = |L:H| · p^(mmem j)`.  Supplies the `dmem`/`θmem`/`mmem`
fields of the X-chain step data (`dmem j = |L:H|·θmem j`, `θmem j = p^(mmem j)`). -/
theorem exists_memberDegreeData (hyp : SibleyDadeHypothesis G L H)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L}
    (hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.S) :
    ∃ mmem : Fin k → ℕ,
      ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = ((H.index * p ^ mmem j : ℕ) : ℂ) := by
  choose mmem hmmem using fun j => hyp.exists_index_primePow_degree_of_mem_S hp hHp (hmemS j)
  exact ⟨mmem, hmmem⟩

/-- **(6.6)/(6.8) central degree bound for an X-member (the redesign linchpin).**  For
`χ = Ind_H^L θ ∈ X(Z) = S − S(Z)` with `H` a `p`-group and `Z` **central in `H`**
(`Z.subgroupOf H ≤ Z(↥H)`), the source `θ` has `θ(1) = p^k` and — crucially — by [Is] Cor 2.30
(`exists_degree_sq_le_index`, which needs `Z` central) `θ(1)² = (p^k)² ≤ |H:Z|`, while
`χ(1) = |L:H|·p^k`.  This is exactly the `θχ`/`hθχ`/`hθsq_le_qtot` data the per-step X-chain producer
needs (with `qtot = |H:Z|`); it is fillable at the central `Z = Z(H)∩H′` but **not** at `Z = ⁅H,H⁆`
(see `notes/peterfalvi/s08_6_8_blocker_central_Z.md`). -/
theorem exists_source_primePow_centralBound_of_mem_Xset (hyp : SibleyDadeHypothesis G L H)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {Z : Subgroup ↥L} (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset Z) :
    ∃ k : ℕ, χ 1 = ((H.index * p ^ k : ℕ) : ℂ)
      ∧ (p ^ k) ^ 2 ≤ Nat.card (↥H ⧸ Z.subgroupOf H) := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hχS : χ ∈ hyp.S := hyp.Xset_subset_S hχ
  rw [hyp.S_eq, Set.mem_setOf_eq] at hχS
  obtain ⟨θ, _hθne, rfl⟩ := hχS
  obtain ⟨k, hk⟩ := exists_primePow_natDegree_of_isPGroup hp hHp θ
  refine ⟨k, ?_, ?_⟩
  · rw [ClassFunction.induce_apply_one, hk]; push_cast; ring
  · obtain ⟨d, hd, hdsq⟩ := θ.isIrreducible.exists_degree_sq_le_index (Z.subgroupOf H) hZcentral
    have hdpk : d = p ^ k := by
      have hcast : (d : ℂ) = ((p ^ k : ℕ) : ℂ) := by rw [← hd, hk]
      exact_mod_cast hcast
    rw [← hdpk, ← Subgroup.index_eq_card]; exact hdsq

open scoped Classical in
/-- **(6.2) core inequality** `|K:A| − 1 ≤ 2ψ(1)` (Frobenius case).

Combines the member-family degree-square bound `sMember_degreeSqReBound_of_not_coherent`
(`∑_{χ∈S₁} χ(1).re² ≤ 2ψ(1).re·χ₁(1).re`) with the real B2 identity `sum_re_sq_induce_kernelFilter_eq`
(`∑_{χ∈S(A)} χ(1).re² = |L:H|·(|H:A| − 1)`).  Since `S(A) ⊆ S₁`, the `S(A)`-sum is bounded by the
`S₁`-sum, and with `χ₁(1) = |W₁| = |L:H|` (cancelling the positive index `|L:H|`) this gives
`|H:A| − 1 ≤ 2ψ(1)`.  This is the (6.2) bound `2ψ(1) ≥ |K:A| − 1` (with `K = H`); composing with the
θ-bound `ψ(1) ≤ |L:C|√|C:D|` yields the full (6.2) `2|L:C|√|C:D| ≥ |K:A| − 1`. -/
theorem sMember_index_le_two_psi (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {A : Subgroup ↥L} [A.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁sub : S₁ ⊆ hyp.S) (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁fin : S₁.Finite) (hSA_S1 : hyp.SsubFiltration A ⊆ S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤ 2 * (ψ 1).re := by
  obtain ⟨k, χmem, hχinj, hrange, hmemS1, hfambound⟩ :=
    hyp.sMember_degreeSqReBound_of_not_coherent hF hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁ hχ₁deg
      hψS hψirr hψnotS1 hψcnotS1 hnc
  have hcfinj : Function.Injective (fun j => (χmem j : ClassFunction ↥L ℂ)) :=
    fun a b h => hχinj (Subtype.ext h)
  have hB2 := hyp.sum_re_sq_induce_kernelFilter_eq hF (A := A)
  set SA := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) with hSAdef
  -- the `S(A)` Finset is contained in the enumerated `S₁`-range Finset
  have hsub : SA ⊆ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hSAdef] at hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨-, hker, hne⟩ := Finset.mem_filter.mp hθ
    exact hSA_S1 (by rw [hyp.mem_SsubFiltration]; exact ⟨θ, hne, hker, rfl⟩)
  have hchain : (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1) ≤
      2 * (ψ 1).re * (χ₁ 1).re := by
    rw [← hB2]
    calc ∑ χ ∈ SA, ((χ 1).re) ^ 2
        ≤ ∑ χ ∈ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset, ((χ 1).re) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ = ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 :=
          sum_toFinset_range_eq hcfinj (fun χ => (χ 1).re ^ 2)
      _ ≤ 2 * (ψ 1).re * (χ₁ 1).re := hfambound
  have hχ₁re : (χ₁ 1).re = (H.index : ℝ) := by
    rw [hχ₁deg, Complex.natCast_re, hyp.index_H_eq_card_W1]
  rw [hχ₁re] at hchain
  have hidx_pos : (0 : ℝ) < (H.index : ℝ) := by
    rw [hyp.index_H_eq_card_W1]; exact_mod_cast Nat.card_pos
  have key : (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1) ≤
      (H.index : ℝ) * (2 * (ψ 1).re) := by
    calc (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1)
        ≤ 2 * (ψ 1).re * (H.index : ℝ) := hchain
      _ = (H.index : ℝ) * (2 * (ψ 1).re) := by ring
  exact le_of_mul_le_mul_left key hidx_pos

open scoped Classical in
/-- **(6.8.3) X-sum break bound.**  The (5.6)/B1 bound applied to the breaking coherent set `S₁ ⊇ X`:
`∑_{χ∈X} χ(1)² ≤ 2ψ(1)·χ₁(1)`.  Since `X ⊆ S₁` and `S₁` enumerates as a member family bounded by
`sMember_degreeSqReBound_of_not_coherent`, the `X`-sum `(H.index)·(|H| − |H:Z|)`
(`sum_re_sq_Xset_eq`) is dominated by the full family sum, which the (5.6) break bounds by
`2ψ(1)χ₁(1)`.  This is the `(6.8.3)` inequality with `χ₁ = η₁ ∈ Y` of degree `|W₁|`. -/
theorem xSum_le_two_psi (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {Z : Subgroup ↥L} [Z.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁sub : S₁ ⊆ hyp.S) (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁fin : S₁.Finite) (hXS1 : hyp.Xset Z ⊆ S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ))
      ≤ 2 * (ψ 1).re * (χ₁ 1).re := by
  obtain ⟨k, χmem, hχinj, hrange, hmemS1, hfambound⟩ :=
    hyp.sMember_degreeSqReBound_of_not_coherent hF hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁ hχ₁deg
      hψS hψirr hψnotS1 hψcnotS1 hnc
  have hcfinj : Function.Injective (fun j => (χmem j : ClassFunction ↥L ℂ)) :=
    fun a b h => hχinj (Subtype.ext h)
  have hXsum := hyp.sum_re_sq_Xset_eq hF (Z := Z)
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXdiffdef
  have hsub : Xdiff ⊆ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hXdiffdef, Finset.mem_sdiff] at hχ
    obtain ⟨hχbot, hχnotZ⟩ := hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχbot
    obtain ⟨-, -, hne⟩ := Finset.mem_filter.mp hθ
    have hχS : ClassFunction.induce H θ.toClassFunction ∈ hyp.S := by
      rw [hyp.S_eq]; exact ⟨θ, hne, rfl⟩
    have hχnotSZ : ClassFunction.induce H θ.toClassFunction ∉ hyp.SsubFiltration Z := by
      intro hmem
      rw [hyp.mem_SsubFiltration] at hmem
      obtain ⟨θ', hne', hker', heq'⟩ := hmem
      exact hχnotZ (Finset.mem_image.mpr
        ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
    exact hXS1 ⟨hχS, hχnotSZ⟩
  rw [← hXsum]
  calc ∑ χ ∈ Xdiff, ((χ 1).re) ^ 2
      ≤ ∑ χ ∈ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset, ((χ 1).re) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 :=
        sum_toFinset_range_eq hcfinj (fun χ => (χ 1).re ^ 2)
    _ ≤ 2 * (ψ 1).re * (χ₁ 1).re := hfambound

open scoped Classical in
/-- **(6.6) X-set nonemptiness from a nontrivial trace.**  If `Z ⊴ L` and `Z.subgroupOf H ≠ ⊥`,
then `X(Z) = S − S(Z)` is nonempty.  The (6.6) degree-square sum
`∑_{χ∈X(Z)} χ(1).re² = |L:H|·(|H| − |H:Z|)` (`sum_re_sq_Xset_eq`) is strictly positive because
`|H:Z| < |H|` whenever `Z.subgroupOf H` is nontrivial, and a positive sum of squares forces its
index Finset — hence `X(Z)` — to be nonempty.  (Note `Xset` is *antitone* in `Z` (`Xset_mono`), so
`X(Zc)` nonemptiness does **not** follow from `X(⁅H,H⁆)` nonemptiness; this degree-sum route is the
honest argument, and it avoids any Clifford-conjugacy reasoning about `Ind`.) -/
theorem Xset_nonempty_of_subgroupOf_ne_bot (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} [Z.Normal] (hZbot : Z.subgroupOf H ≠ ⊥) :
    (hyp.Xset Z).Nonempty := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hXsum := hyp.sum_re_sq_Xset_eq hF (Z := Z)
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXdiffdef
  -- `|H:Z| < |H|`, since `Z.subgroupOf H` is nontrivial
  have hlt : Nat.card (↥H ⧸ Z.subgroupOf H) < Nat.card ↥H := by
    have h2 : 1 < Nat.card ↥(Z.subgroupOf H) := (Z.subgroupOf H).one_lt_card_iff_ne_bot.mpr hZbot
    have hcard : Nat.card ↥H
        = Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf H)
    calc Nat.card (↥H ⧸ Z.subgroupOf H)
        < Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
          lt_mul_of_one_lt_right Nat.card_pos h2
      _ = Nat.card ↥H := hcard.symm
  -- the degree-square sum is strictly positive
  have hidxpos : 0 < H.index := by rw [hyp.index_H_eq_card_W1]; exact Nat.card_pos
  have hpos : (0 : ℝ) < (H.index : ℝ) *
      ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ)) := by
    refine mul_pos (by exact_mod_cast hidxpos) ?_
    have : (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ) < (Nat.card ↥H : ℝ) := by exact_mod_cast hlt
    linarith
  rw [← hXsum] at hpos
  have hne : Xdiff.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨χ, hχ⟩ := hne
  refine ⟨χ, ?_⟩
  rw [hXdiffdef, Finset.mem_sdiff] at hχ
  obtain ⟨hχbot, hχnotZ⟩ := hχ
  obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχbot
  obtain ⟨-, -, hθne⟩ := Finset.mem_filter.mp hθ
  have hχS : ClassFunction.induce H θ.toClassFunction ∈ hyp.S := by
    rw [hyp.S_eq]; exact ⟨θ, hθne, rfl⟩
  have hχnotSZ : ClassFunction.induce H θ.toClassFunction ∉ hyp.SsubFiltration Z := by
    intro hmem
    rw [hyp.mem_SsubFiltration] at hmem
    obtain ⟨θ', hne', hker', heq'⟩ := hmem
    exact hχnotZ (Finset.mem_image.mpr
      ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
  exact hyp.mem_Xset.mpr ⟨hχS, hχnotSZ⟩

open scoped Classical in
/-- **(6.6)/(6.8) X-set nonemptiness, CertainType (case B) form.**  As
`Xset_nonempty_of_subgroupOf_ne_bot` but the strictly-positive degree-square sum is supplied by the
case-B identity `sum_re_sq_Xset_eq_of_irreducible_X` (which needs only `X`-irreducibility, valid in
case B) instead of the Frobenius `sum_re_sq_Xset_eq`.  The `hX` hypothesis is the `X = S − S(Z) ⊆ Irr L`
fact (Peterfalvi (6.8.1) for (c2), discharged by `isIrreducibleCharacter_of_mem_Xset_c2_caseA`). -/
theorem Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} [Z.Normal] (hZbot : Z.subgroupOf H ≠ ⊥)
    (hX : ∀ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
        IsIrreducibleCharacter χ) :
    (hyp.Xset Z).Nonempty := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hXsum := hyp.sum_re_sq_Xset_eq_of_irreducible_X (Z := Z) hX
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXdiffdef
  have hlt : Nat.card (↥H ⧸ Z.subgroupOf H) < Nat.card ↥H := by
    have h2 : 1 < Nat.card ↥(Z.subgroupOf H) := (Z.subgroupOf H).one_lt_card_iff_ne_bot.mpr hZbot
    have hcard : Nat.card ↥H
        = Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf H)
    calc Nat.card (↥H ⧸ Z.subgroupOf H)
        < Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
          lt_mul_of_one_lt_right Nat.card_pos h2
      _ = Nat.card ↥H := hcard.symm
  have hidxpos : 0 < H.index := by rw [hyp.index_H_eq_card_W1]; exact Nat.card_pos
  have hpos : (0 : ℝ) < (H.index : ℝ) *
      ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ)) := by
    refine mul_pos (by exact_mod_cast hidxpos) ?_
    have : (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ) < (Nat.card ↥H : ℝ) := by exact_mod_cast hlt
    linarith
  rw [← hXsum] at hpos
  have hne : Xdiff.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨χ, hχ⟩ := hne
  refine ⟨χ, ?_⟩
  rw [hXdiffdef, Finset.mem_sdiff] at hχ
  obtain ⟨hχbot, hχnotZ⟩ := hχ
  obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχbot
  obtain ⟨-, -, hθne⟩ := Finset.mem_filter.mp hθ
  have hχS : ClassFunction.induce H θ.toClassFunction ∈ hyp.S := by
    rw [hyp.S_eq]; exact ⟨θ, hθne, rfl⟩
  have hχnotSZ : ClassFunction.induce H θ.toClassFunction ∉ hyp.SsubFiltration Z := by
    intro hmem
    rw [hyp.mem_SsubFiltration] at hmem
    obtain ⟨θ', hne', hker', heq'⟩ := hmem
    exact hχnotZ (Finset.mem_image.mpr
      ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
  exact hyp.mem_Xset.mpr ⟨hχS, hχnotSZ⟩

/-- **(6.6)/(6.8) X-set nonemptiness at the central commutator** (the redesign's `hXne`).
`X(Zc)` with `Zc = Z(H) ∩ H′` is nonempty whenever `H` is non-abelian (`commutator ↥H ≠ ⊥`),
since then `Zc ≠ ⊥` (`centralCommutator_ne_bot`), hence `Zc.subgroupOf H ≠ ⊥` (`Zc ≤ H`). -/
theorem Xset_centralCommutator_nonempty (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥) :
    (hyp.Xset hyp.centralCommutator).Nonempty := by
  haveI := hyp.centralCommutator_normal
  refine hyp.Xset_nonempty_of_subgroupOf_ne_bot hF ?_
  intro hbot
  apply hyp.centralCommutator_ne_bot hHnonab
  rw [eq_bot_iff]
  intro z hz
  have hzH : z ∈ H := hyp.centralCommutator_le hz
  have hmem : (⟨z, hzH⟩ : ↥H) ∈ hyp.centralCommutator.subgroupOf H :=
    (Subgroup.mem_subgroupOf).mpr hz
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hmem

/-- **(6.8.3) extension, case (A): non-coherence of `S` is impossible.**
If `X ∪ Y` (with `X = S − S(Z)`, `Z = Z(H)∩H′` central) is coherent but `S` is not, the
break-pair `{ψ, ψ̄}` (`exists_coherentBreakPair`) gives a coherent `S₁ ⊇ X∪Y` whose extension by
`{ψ,ψ̄}` fails; the (5.6)/B1 bound (`xSum_le_two_psi`) then forces
`|W₁|·|H:Z|·(|Z|−1) = ∑_X χ(1)² ≤ 2ψ(1)·η₁(1) = 2|W₁|²d` with `d = θ(1)`, `ψ = Ind θ`.  Combined
with Cor 2.30 `d² ≤ |H:Z|` (central `Z`) and the FPF bound `|Z|−1 ≥ 2|W₁|`
(`centralCommutator_card_subgroupOf_lower`), the arithmetic core
`false_of_centralCommutator_break_arith` yields a contradiction.  This is the heart of
Peterfalvi (6.8.3) — the step the old `Xset ⁅H,H⁆ ∪ Yset = S` shortcut elided. -/
theorem false_of_coherentXunionYset_of_not_coherentS (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    (hXYcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) : False := by
  classical
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have hcommlt : (⁅H, H⁆ : Subgroup ↥L) < H := by
    have h1 : _root_.commutator ↥H < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial ↥H
    rw [← commutator_subgroupOf_self] at h1
    refine lt_of_le_of_ne (Subgroup.commutator_le_left H H) (fun heq => ?_)
    rw [heq, Subgroup.subgroupOf_self] at h1
    exact lt_irrefl _ h1
  -- break pair on `Sa = X ∪ Y`, `Sb = S`
  have hSaSb : hyp.Xset hyp.centralCommutator ∪ hyp.Yset ⊆ hyp.S := by
    rintro φ (hX | hY)
    · exact hyp.Xset_subset_S hX
    · exact hyp.Yset_subset_S hY
  have hSaconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset) := by
    intro φ hφ
    rcases hφ with hX | hY
    · exact Or.inl (hyp.Xset_closedUnderConjugate_unconditional hyp.centralCommutator hX)
    · exact Or.inr (hyp.SsubFiltration_closedUnderConjugate ⁅H, H⁆ hY)
  obtain ⟨S₁, ψ, hS₁conj, hSaS₁, hS₁Sb, hψSb, hψnS₁, hψcnS₁, hS₁cohN, hncN⟩ :=
    exists_coherentBreakPair hyp.tau hSaSb hyp.S_finite hyp.S_closedUnderConjugate
      (hyp.S_hasNoRealCharacters hF)
      (fun χ hχ => hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hχ)
      hSaconj hXYcoh hncoh
  -- anchor `η ∈ Y` of degree `|W₁|`
  obtain ⟨η, hηY⟩ := hyp.Yset_nonempty
  have hηS₁ : η ∈ S₁ := hSaS₁ (Or.inr hηY)
  have hηdeg : η 1 = (Nat.card hyp.W1 : ℂ) := by
    obtain ⟨χ, -, rfl⟩ := hyp.exists_linear_source_of_mem_Yset hηY
    exact hyp.induce_apply_one_eq_card_W1_of_degree_one _
      (OddOrder.RepresentationTheory.linearIrreducibleCharacter_apply_one χ)
  -- `ψ ∈ S` irreducible, `ψ = Ind θ`
  have hψS : ψ ∈ hyp.S := hψSb
  have hψirr : IsIrreducibleCharacter ψ := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hψS
  rw [hyp.S_eq, Set.mem_setOf_eq] at hψS
  obtain ⟨θ, hθne, hψeq⟩ := hψS
  obtain ⟨d, hdpos, hθd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  have hdsq : d ^ 2 ≤ Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) := by
    obtain ⟨d', hθd', hd'sq⟩ := θ.isIrreducible.exists_degree_sq_le_index
      (hyp.centralCommutator.subgroupOf H) hyp.centralCommutator_subgroupOf_le_center
    have hdd' : d = d' := by
      have hcast : (d : ℂ) = (d' : ℂ) := by rw [← hθd, hθd']
      exact_mod_cast hcast
    rw [hdd', ← Subgroup.index_eq_card]; exact hd'sq
  -- the (5.6) X-sum bound
  have hxb := hyp.xSum_le_two_psi hF (Z := hyp.centralCommutator) hS₁Sb hS₁conj
    (hyp.S_finite.subset hS₁Sb) (fun φ hφ => hSaS₁ (Or.inl hφ)) hS₁cohN.some
    hηS₁ hηdeg hψSb hψirr hψnS₁ hψcnS₁ hncN
  have hψre : (ψ 1).re = (H.index : ℝ) * (d : ℝ) := by
    rw [hψeq, ClassFunction.induce_apply_one, hθd]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
  have hηre : (η 1).re = (Nat.card hyp.W1 : ℝ) := by rw [hηdeg, Complex.natCast_re]
  rw [hψre, hηre] at hxb
  -- cast the real inequality to ℕ
  have hZle : Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) ≤ Nat.card ↥H :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hxbN : H.index * (Nat.card ↥H - Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
      ≤ 2 * (H.index * d) * Nat.card hyp.W1 := by
    rw [← Nat.cast_le (α := ℝ)]
    push_cast [Nat.cast_sub hZle]
    nlinarith [hxb]
  rw [hyp.index_mul_card_sub_factor (Z := hyp.centralCommutator), hyp.index_H_eq_card_W1] at hxbN
  -- discharge the arithmetic core
  refine false_of_centralCommutator_break_arith (w1 := Nat.card hyp.W1) (d := d)
    (hZ := Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
    (cZ := Nat.card ↥(hyp.centralCommutator.subgroupOf H))
    Nat.card_pos hdpos hdsq ?_ ?_ ?_
  · -- `2 ≤ |H:Z|`
    have hZcnotle : ¬ H ≤ hyp.centralCommutator := by
      intro h
      exact (ne_of_lt hcommlt)
        (le_antisymm (Subgroup.commutator_le_left H H)
          (le_trans h hyp.centralCommutator_le_commutator))
    have hne : hyp.centralCommutator.subgroupOf H ≠ ⊤ := fun heq =>
      hZcnotle (Subgroup.subgroupOf_eq_top.mp heq)
    have hcard1 : Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) ≠ 1 := by
      rw [← Subgroup.index_eq_card]; exact mt Subgroup.index_eq_one.mp hne
    have hcardpos : 0 < Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) := Nat.card_pos
    omega
  · -- `2|W₁| ≤ |Z| − 1`
    have he := hyp.centralCommutator_card_subgroupOf_lower hF hHnonab
    omega
  · -- the break inequality, reassociated
    calc Nat.card hyp.W1 * Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H)
            * (Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1)
        = Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H)
            * (Nat.card hyp.W1 * (Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1)) := by ring
      _ ≤ 2 * (Nat.card hyp.W1 * d) * Nat.card hyp.W1 := hxbN
      _ = 2 * Nat.card hyp.W1 ^ 2 * d := by ring

/-- **(6.2) θ-bound for an induced member `ψ = Ind_H^L θ`.**

For `θ ∈ Irr H` and a section `N ◁ C` with `N ≤ D ≤ C ≤ H`, `θ` trivial on `N` (after restriction
to `C`) and `D ⧸ N` central in `C ⧸ N`, the degree of the induced character `ψ = Ind_H^L θ` is
bounded by `ψ(1) = |L:H|·θ(1) ≤ |L:H|·|H:C|·√|C:D|`, combining `induce_apply_one`
(`ψ(1) = |L:H|·θ(1)`) with the §6 `θ`-bound `theta_degree_le_index_mul_sqrt_index`
(`θ(1) ≤ |H:C|·√|C:D|`).  This is the (6.2) step `ψ(1) ≤ |L:C|·√|C:D|`. -/
theorem psi_degree_le_of_source (hyp : SibleyDadeHypothesis G L H)
    (θ : IrreducibleCharacter ↥H) (C : Subgroup ↥H) [Fintype ↥C]
    [Invertible (Nat.card ↥C : ℂ)] {N : Subgroup ↥C} [N.Normal] (D : Subgroup ↥C) (hND : N ≤ D)
    (hθN : (↑N : Set ↥C) ⊆ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.restrict C (θ : ClassFunction ↥H ℂ)))
    (hcentral : D.map (QuotientGroup.mk' N) ≤ Subgroup.center (↥C ⧸ N)) :
    (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re ≤
      (H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hind : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re
      = (H.index : ℝ) * ((θ : ClassFunction ↥H ℂ) 1).re := by
    rw [ClassFunction.induce_apply_one, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  rw [hind]
  have hθbound := theta_degree_le_index_mul_sqrt_index (K := ↥H) θ C D hND hθN hcentral
  calc (H.index : ℝ) * ((θ : ClassFunction ↥H ℂ) 1).re
      ≤ (H.index : ℝ) * ((C.index : ℝ) * Real.sqrt (D.index : ℝ)) :=
        mul_le_mul_of_nonneg_left hθbound (Nat.cast_nonneg _)
    _ = (H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by ring

open scoped Classical in
/-- **(6.2) first-obstruction + core wiring** `|K:A| − 1 ≤ 2ψ(1)`.

From `S(A)` coherent and `S(B)` not coherent (with `S(A) ⊆ S(B)`), the first-obstruction
`exists_coherentBreakPair` produces a breaking pair `{ψ, ψ̄}` with `ψ ∈ S(B)` (`ψ, ψ̄ ∉ S₁`), and the
(6.2) core `sMember_index_le_two_psi` — with the degree-`|W₁|` anchor `χ₁ ∈ S(A) ⊆ S₁`
(`exists_mem_SsubFiltration_degree_W1`, valid since `H/(A.subgroupOf H)` has a proper commutator
subgroup) — gives `|H:A| − 1 ≤ 2ψ(1)`.  The structural inputs (`S(B)` finite / conjugation-closed /
real-free / irreducible, `S(A)` conjugation-closed) come from the landed `SsubFiltration_*`
helpers. -/
theorem six_two_index_bound (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B : Subgroup ↥L} [A.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ ψ, ψ ∈ hyp.SsubFiltration B ∧
      (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤ 2 * (ψ 1).re := by
  letI : H.Normal := hyp.H_normal
  obtain ⟨S₁, ψ, hS₁conj, hAS₁, hS₁B, hψB, hψnotS1, hψcnotS1, hS₁coh, hncoh⟩ :=
    exists_coherentBreakPair hyp.tau hAB (hyp.SsubFiltration_finite B)
      (hyp.SsubFiltration_closedUnderConjugate B) (hyp.SsubFiltration_hasNoRealCharacters hF B)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF
        (hyp.SsubFiltration_subset_S hφ))
      (hyp.SsubFiltration_closedUnderConjugate A) hSAcoh hSBncoh
  obtain ⟨χ₁, hχ₁SA, hχ₁deg⟩ := hyp.exists_mem_SsubFiltration_degree_W1 hAcomm
  have hψS : ψ ∈ hyp.S := hyp.SsubFiltration_subset_S hψB
  exact ⟨ψ, hψB, hyp.sMember_index_le_two_psi hF
    (hS₁B.trans hyp.SsubFiltration_subset_S) hS₁conj
    ((hyp.SsubFiltration_finite B).subset hS₁B) hAS₁ hS₁coh.some
    (hAS₁ hχ₁SA) hχ₁deg hψS (hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hψS)
    hψnotS1 hψcnotS1 hncoh⟩

/-- **Peterfalvi (6.2)** (Frobenius case, `K = H`).

Under the (6.2) section hypotheses — `B ⊆ D ⊆ C ⊆ H` with `D ⧸ B` central in `C ⧸ B` (here `B`
appears as `N = (B.subgroupOf H).subgroupOf C`), `S(A)` coherent, `S(B)` not — the index bound
`2|L:C|·√|C:D| ≥ |K:A| − 1` holds (with `K = H`, so `|L:C| = |L:H|·|H:C|` and `|C:D| = D.index`).

Proof: `six_two_index_bound` gives a breaking pair `ψ ∈ S(B)` with `|H:A| − 1 ≤ 2ψ(1)`; writing
`ψ = Ind_H^L θ` with `θ` trivial on `B` (`ψ ∈ S(B)`), `characterKernel_restrict_subgroupOf`
discharges the θ-bound's kernel hypothesis, and `psi_degree_le_of_source` gives
`ψ(1) ≤ |L:H|·|H:C|·√|C:D|`. -/
theorem six_two (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B : Subgroup ↥L} [A.Normal] [B.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (C : Subgroup ↥H) [Fintype ↥C] [Invertible (Nat.card ↥C : ℂ)] (D : Subgroup ↥C)
    (hND : ((B.subgroupOf H).subgroupOf C) ≤ D)
    (hcentral : D.map (QuotientGroup.mk' ((B.subgroupOf H).subgroupOf C)) ≤
      Subgroup.center (↥C ⧸ (B.subgroupOf H).subgroupOf C))
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤
      2 * (H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  letI : H.Normal := hyp.H_normal
  obtain ⟨ψ, hψB, hψbound⟩ := hyp.six_two_index_bound hF hAB hAcomm hSAcoh hSBncoh
  rw [hyp.mem_SsubFiltration] at hψB
  obtain ⟨θ, _hθne, hθkerB, hψeq⟩ := hψB
  have hθN := characterKernel_restrict_subgroupOf C hθkerB
  have hψdeg := hyp.psi_degree_le_of_source θ C D hND hθN hcentral
  rw [hψeq] at hψbound
  calc (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1
      ≤ 2 * (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re := hψbound
    _ ≤ 2 * ((H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ)) := by linarith [hψdeg]
    _ = 2 * (H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by ring

/-- **(6.2) θ-bound for an induced member, central (`C = H`) case.**

When the section is `N ◁ D ≤ H` with `θ` trivial on `N` and `D ⧸ N` central in `H ⧸ N`, the b-half
`degree_sq_le_index_of_central_quotient` gives `θ(1)² ≤ |H:D|` directly (no Clifford restriction),
so `ψ = Ind_H^L θ` has `ψ(1) = |L:H|·θ(1) ≤ |L:H|·√|H:D|`.  This is the form (6.3) consumes (it
applies (6.2) with `C = H`). -/
theorem psi_degree_le_of_source_central (hyp : SibleyDadeHypothesis G L H)
    (θ : IrreducibleCharacter ↥H) {N : Subgroup ↥H} [N.Normal] (D : Subgroup ↥H) (hND : N ≤ D)
    (hθN : (↑N : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ))
    (hcentral : D.map (QuotientGroup.mk' N) ≤ Subgroup.center (↥H ⧸ N)) :
    (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re ≤
      (H.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  obtain ⟨d, hd1, hd2⟩ :=
    degree_sq_le_index_of_central_quotient N θ D hND hθN hcentral
  have hind : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re
      = (H.index : ℝ) * ((θ : ClassFunction ↥H ℂ) 1).re := by
    rw [ClassFunction.induce_apply_one, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  rw [hind, hd1, Complex.natCast_re]
  exact mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (by exact_mod_cast hd2))
    (Nat.cast_nonneg _)

/-- **Peterfalvi (6.2), central case `C = H`** (the form consumed by (6.3)).

With the section `B ⊆ D ≤ H` (`B` as `N = B.subgroupOf H`), `D/B` central in `H/B`, `S(A)`
coherent, `S(B)` not: `|K:A| − 1 ≤ 2|L:H|·√|H:D|`.  Specializes `six_two` to `C = H`, where the
θ-bound is the direct b-half (`psi_degree_le_of_source_central`), so the source `θ` of the breaking
pair `ψ ∈ S(B)` is trivial on `N = B.subgroupOf H` (no restriction step needed). -/
theorem six_two_central (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B : Subgroup ↥L} [A.Normal] [B.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (D : Subgroup ↥H) (hND : B.subgroupOf H ≤ D)
    (hcentral : D.map (QuotientGroup.mk' (B.subgroupOf H)) ≤
      Subgroup.center (↥H ⧸ B.subgroupOf H))
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤ 2 * (H.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  letI : H.Normal := hyp.H_normal
  obtain ⟨ψ, hψB, hψbound⟩ := hyp.six_two_index_bound hF hAB hAcomm hSAcoh hSBncoh
  rw [hyp.mem_SsubFiltration] at hψB
  obtain ⟨θ, _hθne, hθkerB, hψeq⟩ := hψB
  have hψdeg := hyp.psi_degree_le_of_source_central θ D hND hθkerB hcentral
  rw [hψeq] at hψbound
  calc (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1
      ≤ 2 * (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re := hψbound
    _ ≤ 2 * ((H.index : ℝ) * Real.sqrt (D.index : ℝ)) := by linarith [hψdeg]
    _ = 2 * (H.index : ℝ) * Real.sqrt (D.index : ℝ) := by ring

/-- **(6.3) per-step index bound.**

The per-step of Peterfalvi (6.3): for a section `B ⊆ A ⊆ H₁` with `A/B` central in `H/B`, `S(A)`
coherent and `S(B)` not, the (6.2) central bound `six_two_central` (`|H:A| − 1 ≤ 2|L:H|√|H:A|`)
combines with the arithmetic core `six_three_HH1_le` to give `|H:H₁| ≤ 4|L:K|² + 1` (`K = H`).
The minimal-`A` / maximal-`B` induction of (6.3) repeatedly applies this step. -/
theorem six_three_index_bound (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B H₁ : Subgroup ↥L} [A.Normal] [B.Normal] (hBA : B ≤ A) (hAH₁ : A ≤ H₁)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (hcentral : (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≤
      Subgroup.center (↥H ⧸ B.subgroupOf H))
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    Nat.card (↥H ⧸ H₁.subgroupOf H) ≤ 4 * H.index ^ 2 + 1 := by
  letI : H.Normal := hyp.H_normal
  have hsixtwo := hyp.six_two_central hF (hyp.SsubFiltration_antitone hBA) hAcomm
    (A.subgroupOf H) (Subgroup.subgroupOf_mono H hBA) hcentral hSAcoh hSBncoh
  have hHH1le : Nat.card (↥H ⧸ H₁.subgroupOf H) ≤ Nat.card (↥H ⧸ A.subgroupOf H) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono H hAH₁))
  refine six_three_HH1_le (LK := H.index) (KH := 1) (HA := Nat.card (↥H ⧸ A.subgroupOf H))
    (HH1 := Nat.card (↥H ⧸ H₁.subgroupOf H)) (by norm_num) hHH1le ?_
  simpa [Subgroup.index_eq_card] using hsixtwo

/-- **`hAcomm` from nilpotency of `H`.**

In the Sibley setup `H` is nilpotent, so for a normal `A ⊊ H` the quotient `H/A` is a nontrivial
nilpotent (hence solvable) group, whence its commutator subgroup is proper: `[H/A, H/A] ≠ ⊤`.  This
supplies the `hAcomm` hypothesis of `six_two_index_bound` / `six_three_index_bound` (which need a
degree-`|W₁|` anchor in `S(A)`). -/
theorem commutator_subgroupOf_quotient_ne_top (hyp : SibleyDadeHypothesis G L H)
    {A : Subgroup ↥L} [A.Normal] (hAH : A < H) :
    _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤ := by
  letI : H.Normal := hyp.H_normal
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  haveI : (A.subgroupOf H).Normal := (‹A.Normal›).subgroupOf H
  haveI : Nontrivial (↥H ⧸ A.subgroupOf H) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hAH.ne (le_antisymm hAH.le htop)
  exact (IsSolvable.commutator_lt_top_of_nontrivial (G := ↥H ⧸ A.subgroupOf H)).ne

/-- **Peterfalvi (6.3)** (Frobenius case `K = H`).

With `M ≤ H₁ ⊊ H` normal subgroups of `L`, `S(H₁)` coherent and `|H:H₁| > 4|L:H|² + 1`, the set
`S(M)` is coherent.

Minimal-`A` induction (Peterfalvi's argument): pick a normal `A ∈ [M, H₁]` with `S(A)` coherent that
is minimal for `⊆` (exists since `H₁` qualifies).  If `A ≠ M` then `M < A`; take a maximal normal
`B` with `M ≤ B ⊊ A` (`exists_maximal_normal_between`).  Then `A/B ⊆ Z(H/B)`
(`normal_central_of_maximal_normal_below`, using `H` nilpotent), and `S(B)` is *not* coherent (else
`B ∈ [M, H₁]` would beat the minimality of `A`).  So `six_three_index_bound` gives
`|H:H₁| ≤ 4|L:H|² + 1`, contradicting the hypothesis.  Hence `A = M` and `S(M) = S(A)` is
coherent. -/
theorem six_three (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {M H₁ : Subgroup ↥L} [M.Normal] [H₁.Normal] (hMH₁ : M ≤ H₁) (hH₁H : H₁ < H)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration H₁)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hbound : 4 * H.index ^ 2 + 1 < Nat.card (↥H ⧸ H₁.subgroupOf H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration M)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  classical
  letI : H.Normal := hyp.H_normal
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  haveI : Finite (Subgroup ↥L) := Finite.of_injective (fun K : Subgroup ↥L => (K : Set ↥L))
    (fun _ _ h => SetLike.coe_injective h)
  set s : Set (Subgroup ↥L) := {A | A.Normal ∧ M ≤ A ∧ A ≤ H₁ ∧
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))} with hs_def
  have hH₁s : H₁ ∈ s := by
    simp only [hs_def, Set.mem_setOf_eq]; exact ⟨‹H₁.Normal›, hMH₁, le_refl _, hcoh⟩
  obtain ⟨A, hAmem, hAmin⟩ :=
    Set.Finite.exists_minimalFor (id : Subgroup ↥L → Subgroup ↥L) s (Set.toFinite _) ⟨H₁, hH₁s⟩
  simp only [hs_def, Set.mem_setOf_eq] at hAmem
  obtain ⟨hAnorm, hMA, hAH₁, hAcoh⟩ := hAmem
  haveI : A.Normal := hAnorm
  have hAeqM : A = M := by
    by_contra hne
    have hMltA : M < A := lt_of_le_of_ne hMA (Ne.symm hne)
    obtain ⟨B, hBnorm, hMB, hBltA, hBmaxl⟩ := exists_maximal_normal_between hMltA
    haveI : B.Normal := hBnorm
    have hAltH : A < H := lt_of_le_of_lt hAH₁ hH₁H
    have hAcomm := hyp.commutator_subgroupOf_quotient_ne_top hAltH
    have hcentral := normal_central_of_maximal_normal_below (H := H) (A := A) (B := B)
      ‹H.Normal› hAltH.le hBltA hBmaxl
    have hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
      intro hBcoh
      have hBs : B ∈ s := by
        simp only [hs_def, Set.mem_setOf_eq]
        exact ⟨hBnorm, hMB, hBltA.le.trans hAH₁, hBcoh⟩
      exact lt_irrefl _ (hBltA.trans_le (hAmin hBs hBltA.le))
    have hbnd := hyp.six_three_index_bound hF hBltA.le hAH₁ hAcomm hcentral hAcoh hSBncoh
    omega
  rw [← hAeqM]
  exact hAcoh

/-- **Peterfalvi (6.5) consequence (Frobenius case): `H` is a `p`-group.**

If the full set `S` is *not* coherent, then `H` is a `p`-group for some prime `p`.  Apply `six_three`
with `M = ⊥`, `H₁ = ⁅H,H⁆`: `S(⁅H,H⁆) = Y` is coherent (`coherentYset`), `⊥ ≤ ⁅H,H⁆` and `⁅H,H⁆ ⊊ H`
(`H` nilpotent nontrivial ⟹ not perfect), so if `|H:⁅H,H⁆| > 4|L:H|²+1` then `S(⊥) = S` would be
coherent — contradiction.  Hence `|Abelianization H| = |H:⁅H,H⁆| ≤ 4|W₁|²+1`
(`commutator_subgroupOf_self`, `index_H_eq_card_W1`), and as everything has odd order
`isPGroup_of_isFrobeniusGroup_of_card_le` produces the prime.  This is the (6.5)/(6.6) reduction
"`H` is a `p`-group" that feeds the (6.8) capstone. -/
theorem isPGroup_of_not_coherent (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hSncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p ↥H := by
  letI : H.Normal := hyp.H_normal
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  -- `⁅H,H⁆ ⊊ H` from nilpotency (nontrivial nilpotent is not perfect)
  have hcommlt : (⁅H, H⁆ : Subgroup ↥L) < H := by
    have h1 : _root_.commutator ↥H < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial ↥H
    rw [← commutator_subgroupOf_self] at h1
    refine lt_of_le_of_ne (Subgroup.commutator_le_left H H) (fun heq => ?_)
    rw [heq, Subgroup.subgroupOf_self] at h1
    exact lt_irrefl _ h1
  -- the index bound, by the contrapositive of `six_three`
  have hidx : Nat.card (↥H ⧸ (⁅H, H⁆ : Subgroup ↥L).subgroupOf H) ≤ 4 * H.index ^ 2 + 1 := by
    by_contra hgt
    rw [not_le] at hgt
    have hYcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration ⁅H, H⁆)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := ⟨hyp.coherentYset⟩
    have hMcoh := hyp.six_three hF (M := ⊥) (H₁ := ⁅H, H⁆) bot_le hcommlt hYcoh hgt
    rw [hyp.SsubFiltration_bot] at hMcoh
    exact hSncoh hMcoh
  -- convert the index bound to the abelianization-card bound
  have hbound : Nat.card (Abelianization ↥H) ≤ 4 * Nat.card hyp.W1 ^ 2 + 1 := by
    rw [commutator_subgroupOf_self, hyp.index_H_eq_card_W1] at hidx
    exact hidx
  -- odd orders
  have hLodd : Odd (Nat.card ↥L) := hyp.card_L_odd
  have hHodd : Odd (Nat.card (Abelianization ↥H)) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hLodd H.card_subgroup_dvd_card)
      (Subgroup.card_quotient_dvd_card (_root_.commutator ↥H))
  have hW1odd : Odd (Nat.card hyp.W1) := Odd.of_dvd_nat hLodd hyp.W1.card_subgroup_dvd_card
  exact isPGroup_of_isFrobeniusGroup_of_card_le hF hHodd hW1odd hbound

/-- **(T8 leaf 8) `2 ≤ |S₀|`**, from the abstract input `X ⊆ Irr L`.

If `X` is nonempty, its base block `S₀` (minimal-degree members) contains a minimal-degree `χ`
together with its conjugate `χ̄ ≠ χ` (`Xset_hasNoRealCharacters_of_irreducible_X`,
`xBaseBlock_closedUnderConjugate_of_irreducible_X`), so `2 ≤ |S₀|`. -/
theorem two_le_xBaseBlock_ncard_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty) :
    2 ≤ (hyp.xBaseBlock Z).ncard := by
  have hXfin := hyp.xSet_finite_of_irreducible_X hX
  obtain ⟨χ, hχX, hχmin⟩ := Set.exists_min_image (hyp.Xset Z)
    (fun ψ => (OddOrder.Peterfalvi.S03.characterDegree ψ).re) hXfin hXne
  have hχS₀ : χ ∈ hyp.xBaseBlock Z := ⟨hχX, hχmin⟩
  have hconjS₀ : χ.conj ∈ hyp.xBaseBlock Z :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX hχS₀
  have hne : χ.conj ≠ χ := hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH hX hχX
  have hS₀fin : (hyp.xBaseBlock Z).Finite := hXfin.subset (hyp.xBaseBlock_subset Z)
  have h1 : 1 < (hyp.xBaseBlock Z).ncard :=
    (Set.one_lt_ncard hS₀fin).mpr ⟨χ.conj, hconjS₀, χ, hχS₀, hne⟩
  omega

/-- **(T8 leaf 8) `2 ≤ |S₀|`** (Frobenius case). -/
theorem two_le_xBaseBlock_ncard (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] (hXne : (hyp.Xset Z).Nonempty) :
    2 ≤ (hyp.xBaseBlock Z).ncard :=
  hyp.two_le_xBaseBlock_ncard_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hXne

/-- **(T8 leaf 9) base coherence `IsCoherent τ S₀`**, from the abstract input
`X ⊆ Irr L`.

The minimal-degree base block `S₀ = xBaseBlock Z` is coherent for the real Dade map `tau`.  It is a
finite, equal-degree family of `≥ 2` irreducible characters of `L`
(`exists_finEnum_irreducible`, `xBaseBlock_degree_re_eq` with the integer degrees
`irreducibleCharacter_apply_one_eq_pos_natCast`, `two_le_xBaseBlock_ncard_of_irreducible_X`) whose
pairwise differences `χⱼ − χ₀` vanish off `H^# = sharpImage H`
(`sMember_diffSupport_of_charValue_eq`), so the §7 base engine `coherentEqualDegree_fromDade`
((6.6) base case, via (1.1)+(1.4)) applies with `A = H^#` — matching
`tau = dadeIntegralCharacterMap hyp.dade …`.

`noncomputable def` (not `theorem`): `IsCoherent` carries the isometric extension map as data
(it lives in `Type`, not `Prop`), exactly like `sibleySetup_is_coherent`/`CoherenceTarget`. -/
noncomputable def xBaseBlock_isCoherent_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.xBaseBlock Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  -- Enumerate the finite irreducible base block `S₀` as `χ : Fin k → Irr L`.  The conclusion
  -- `IsCoherent` is `Type`-valued (carries the extension map), so the enumeration data must be
  -- extracted with `choose` (via choice), not `obtain` (which would large-eliminate a `Prop ∃`).
  have hS₀fin : (hyp.xBaseBlock Z).Finite :=
    (hyp.xSet_finite_of_irreducible_X hX).subset (hyp.xBaseBlock_subset Z)
  have hS₀irr : ∀ φ ∈ hyp.xBaseBlock Z, IsIrreducibleCharacter φ :=
    fun φ hφ => hX φ (hyp.xBaseBlock_subset Z hφ)
  choose k χ hχinj hrange using exists_finEnum_irreducible hS₀fin hS₀irr
  have hmemS₀ : ∀ j, (χ j : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z :=
    fun j => hrange ▸ Set.mem_range_self j
  -- `2 ≤ k`: the coerced enumeration is injective, so `|S₀| = k`.
  have hcoeinj : Function.Injective (fun j => (χ j : ClassFunction ↥L ℂ)) := by
    intro i j hij
    exact hχinj (IrreducibleCharacter.ext hij)
  have hk2 : 2 ≤ k := by
    have hcard : (hyp.xBaseBlock Z).ncard = k := by
      rw [← hrange, Set.ncard_range_of_injective hcoeinj, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have h2 := hyp.two_le_xBaseBlock_ncard_of_irreducible_X hZH hX hXne
    omega
  haveI : NeZero k := ⟨by omega⟩
  -- `S₀ ⊆ S`.
  have hmemS : ∀ j, (χ j : ClassFunction ↥L ℂ) ∈ hyp.S :=
    fun j => (hyp.mem_Xset.mp (hyp.xBaseBlock_subset Z (hmemS₀ j))).1
  -- Equal degree: real parts equal (base block) and the degrees are positive integers.
  have hdeg : ∀ j, ((χ j : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
      = ((χ 0 : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    intro j
    obtain ⟨dj, _, hdj⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (χ j)
    obtain ⟨d0, _, hd0⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (χ 0)
    have hre := hyp.xBaseBlock_degree_re_eq (hmemS₀ j) (hmemS₀ 0)
    rw [OddOrder.Peterfalvi.S03.characterDegree_def,
      OddOrder.Peterfalvi.S03.characterDegree_def, hdj, hd0] at hre
    rw [hdj, hd0]
    have hdd : dj = d0 := by exact_mod_cast hre
    rw [hdd]
  -- Difference support: `χⱼ − χ₀` vanishes off `H^#` (equal degree, both supported on `H`).
  have hsuppdiff : ∀ j, (irreducibleCharacterDifference χ j).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    fun j => hyp.sMember_diffSupport_of_charValue_eq (hmemS j) (hmemS 0) (hdeg j)
  -- `1 ∉ A = H^#`.
  have h1notA : (1 : G) ∉ sharpImage H := by simp [sharpImage]
  -- Apply the §7 base engine; its `range χ = S₀` and Dade map `= hyp.tau`.
  have hcoh := OddOrder.Peterfalvi.S07.coherentEqualDegree_fromDade hyp.dade hyp.hconj
    hk2 χ hχinj hdeg hsuppdiff h1notA
  rw [hrange] at hcoh
  exact hcoh

/-- **(T8 leaf 9) base coherence `IsCoherent τ S₀`** (Frobenius case). -/
noncomputable def xBaseBlock_isCoherent (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] (hXne : (hyp.Xset Z).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.xBaseBlock Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.xBaseBlock_isCoherent_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hXne

/-- **(T8 leaf 9, case A) base coherence `IsCoherent τ S₀`.**

This specializes the abstract `X ⊆ Irr L` base-block engine using the case-A irreducibility bridge
`isIrreducibleCharacter_of_mem_Xset_caseA`. -/
noncomputable def xBaseBlock_isCoherent_caseA (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    (hZnorm : ∀ w ∈ hyp.W1, w ∈ Subgroup.normalizer Z)
    (hZfpf : ∀ w ∈ hyp.W1, w ≠ 1 → Subgroup.centralizer ({w} : Set ↥L) ⊓ Z = ⊥)
    (hXne : (hyp.Xset Z).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.xBaseBlock Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.xBaseBlock_isCoherent_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_caseA hZH hZcentral hZnorm hZfpf h)
    hXne


/-- **(T8.11b) X-pair step core facts.**

For a pair supplied by `exists_conjugatePairCover`, the first eight fields of
`XAdjoinStepInput` are forced by membership in `X` and the disjoint-prefix property: the new
character is non-real, has the required difference support, is orthonormal to its conjugate, and is
orthogonal to the accumulated prefix. -/
theorem xPair_stepCoreFacts_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N) :
    ¬ ClassFunction.IsReal (χs i : ClassFunction ↥L ℂ) ∧
      (((χs i : ClassFunction ↥L ℂ).conj - (χs i : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ) (χs i : ClassFunction ↥L ℂ) = 1 ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ).conj
        (χs i : ClassFunction ↥L ℂ).conj = 1 ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ)
        (χs i : ClassFunction ↥L ℂ).conj = 0 ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ).conj
        (χs i : ClassFunction ↥L ℂ) = 0 ∧
      (∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
        ClassFunction.inner (χs i : ClassFunction ↥L ℂ) x = 0) ∧
      (∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
        ClassFunction.inner (χs i : ClassFunction ↥L ℂ).conj x = 0) := by
  classical
  have hχpair : (χs i : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  have hχX : (χs i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := hpairs i hi hχpair
  rcases hyp.xMember_characterFacts_of_irreducible_X hZH hX hχX with
    ⟨hrealχ, hχχ, hχbarχbar, hχbarχ, hχχbar⟩
  have hdiffsuppχ := hyp.xMember_diffSupport_of_irreducible_X hX hχX
  have hortho := pairCover_orthogonal_to_prefix
    (X := hyp.Xset Z) (S₀ := hyp.xBaseBlock Z) (pair := pair) (N := N)
    (i := i) (χ := χs i) hX (hyp.xBaseBlock_subset Z) hpairs
    (hpair0 i hi) (hpair1 i hi) (hdisj i hi) hi
  exact ⟨hrealχ, hdiffsuppχ, hχχ, hχbarχbar, hχχbar, hχbarχ, hortho.1, hortho.2⟩

/-- **(T8.11c) Accumulator member-family enumeration.**

Every prefix accumulator `pairUnion (xBaseBlock Z) pair i` in the X-chain is a finite family of
irreducible characters, closed under conjugation.  This packages the `Fin k` enumeration and the
member facts needed by the member-family half of `XAdjoinStepInput`.  The remaining
degree-ratio and lattice-generation fields stay separate. -/
theorem exists_pairUnion_memberFamily_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hi : i < N) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) =
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i ∧
      (∀ j : Fin k, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ)) ∧
      (∀ j : Fin k,
        ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      (∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i) ∧
      (∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ).conj ∈
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i) ∧
      (∀ j : Fin k, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ).conj = 0) ∧
      (∀ j l : Fin k,
        ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
          (χmem l : ClassFunction ↥L ℂ) = if j = l then (1 : ℂ) else 0) := by
  classical
  let S₁ : Set (ClassFunction ↥L ℂ) :=
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  have hS₁X : S₁ ⊆ hyp.Xset Z := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact hyp.xBaseBlock_subset Z hbase
    · exact hpairs j (hji.trans hi) hjpair
  have hS₁irr : ∀ φ ∈ S₁, IsIrreducibleCharacter φ := fun φ hφ => hX φ (hS₁X hφ)
  have hS₁fin : S₁.Finite := (hyp.xSet_finite_of_irreducible_X hX).subset hS₁X
  have hS₀conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX
  have hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (hS₀conj hbase))
    · have hjN : j < N := hji.trans hi
      have hpair_conj : φ.conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hjpair ⊢
        rcases hjpair with hφ | hφ
        · right
          rw [hφ, hpair0 j hjN, hpair1 j hjN]
        · left
          rw [hφ, hpair1 j hjN, hpair0 j hjN]
          simp
      exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, hpair_conj⟩)
  obtain ⟨k, χmem, hχinj, hrange⟩ := exists_finEnum_irreducible hS₁fin hS₁irr
  have hmemS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j
    rw [← hrange]
    exact Set.mem_range_self j
  have hmembarS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ).conj ∈ S₁ :=
    fun j => hS₁conj (hmemS1 j)
  have hmemreal : ∀ j : Fin k, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ) := by
    intro j
    exact (hyp.xMember_characterFacts_of_irreducible_X hZH hX (hS₁X (hmemS1 j))).1
  have hmemdiffsupp : ∀ j : Fin k,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    intro j
    exact hyp.xMember_diffSupport_of_irreducible_X hX (hS₁X (hmemS1 j))
  have hmemconjortho : ∀ j : Fin k, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0 := by
    intro j
    rcases hyp.xMember_characterFacts_of_irreducible_X hZH hX (hS₁X (hmemS1 j)) with
      ⟨_, _, _, _, hχχbar⟩
    exact hχχbar
  have hmemortho : ∀ j l : Fin k,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem l : ClassFunction ↥L ℂ) = if j = l then (1 : ℂ) else 0 := by
    intro j l
    by_cases hjl : j = l
    · subst j
      simpa using irreducibleCharacter_inner_eq_ite (χmem l) (χmem l)
    · have hχne : χmem j ≠ χmem l := fun h => hjl (hχinj h)
      simpa [hjl, hχne] using irreducibleCharacter_inner_eq_ite (χmem j) (χmem l)
  exact ⟨k, χmem, hχinj, hrange, hmemreal, hmemdiffsupp, hmemS1, hmembarS1,
    hmemconjortho, hmemortho⟩

open scoped Classical in
/-- **(T8.11l) X-adjoin input from member-family degree ratios.**

Given a conjugate-pair cover step, an explicit finite member-family cover of the current prefix
`S₁ = pairUnion (xBaseBlock Z) pair i`, and degree-ratio data against a chosen anchor `χ₁`, this
assembles the full `XAdjoinStepInput` for adjoining `χᵢ`.  The theorem deliberately leaves the
arithmetical (6.6) payload as inputs: the member and new-character degree ratios, `deg i₁ = 1`, and
the strict inequality `2a < ∑ deg²`.  All non-arithmetical fields are discharged from the X-pair
cover, support bridges, virtual-character bridge, and the §7 anchor-generation lemma. -/
noncomputable def xAdjoinStepInput_of_memberFamily_degreeRatios
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι : Type} {s : Finset ι} {χmem : ι → IrreducibleCharacter ↥L}
    {deg : ι → ℕ} {i₁ : ι} {a : ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (ha1 : deg i₁ = 1)
    (hdeg_mem : ∀ j ∈ s,
      (χmem j : ClassFunction ↥L ℂ) 1 =
        (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1)
    (hdegχ : (χs i : ClassFunction ↥L ℂ) 1 =
      (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1)
    (hDeg : 2 * (a : ℝ) < ∑ j ∈ s, ((deg j : ℝ)) ^ 2) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  classical
  let S₁ : Set (ClassFunction ↥L ℂ) :=
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  have hχpair : (χs i : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  have hχX : (χs i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := hpairs i hi hχpair
  have hmemX : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := by
    intro j hj
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp (hmemS1 j hj) with hbase | ⟨k, hki, hkpair⟩
    · exact hyp.xBaseBlock_subset Z hbase
    · exact hpairs k (hki.trans hi) hkpair
  rcases hyp.xPair_stepCoreFacts_of_irreducible_X hZH hX hpair0 hpair1 hpairs hdisj hi with
    ⟨hrealχ, hdiffsuppχ, hχχ, hχbarχbar, hχχbar, hχbarχ, hχ_S1, hχbar_S1⟩
  have hmemdegdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ) - deg j •
          (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.xMember_scaledDiffSupports_of_degreeData hmemX hi₁ hdeg_mem
  have hdiffasuppχ : ((χs i : ClassFunction ↥L ℂ) - a •
        (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.xMember_scaledDiffSupport_of_degreeData hχX (hmemX i₁ hi₁) hdegχ
  have htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dade
      (hyp.dade.fullDadeIsometryData hyp.hconj)
      ((χs i : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G := by
    simpa [SibleyDadeHypothesis.tau] using hyp.scaledDiff_dadeImage_mem_ZIrr hdiffasuppχ
  have hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          {(χmem i₁ : ClassFunction ↥L ℂ)}) :=
    OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
      (L := ↥L) (S₁ := S₁)
      (A := OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      (χmem := fun j => (χmem j : ClassFunction ↥L ℂ)) (deg := deg) (i₁ := i₁)
      (by simpa [S₁] using hcover) hi₁ (by simpa [S₁] using hmemS1)
      (by simpa using hmemdegdiffsupp)
  exact
    { hrealχ := hrealχ
      hdiffsuppχ := hdiffsuppχ
      hχχ := hχχ
      hχbarχbar := hχbarχbar
      hχχbar := hχχbar
      hχbarχ := hχbarχ
      hχ_S1 := hχ_S1
      hχbar_S1 := hχbar_S1
      ι := ι
      s := s
      χmem := χmem
      deg := deg
      i₁ := i₁
      hi₁ := hi₁
      hmemreal := hmemreal
      hmemdiffsupp := hmemdiffsupp
      hmemdegdiffsupp := hmemdegdiffsupp
      hmemS1 := hmemS1
      hmembarS1 := hmembarS1
      hmemconjortho := hmemconjortho
      hmemortho := hmemortho
      a := a
      hdiffasuppχ := hdiffasuppχ
      htau1_memaχ := htau1_memaχ
      ha1 := ha1
      hDeg := hDeg
      hSgen := hSgen }

/-- **(T8 leaf 10 / T-A4) X-chain assembly from per-pair adjoining data.**

This is the Sibley/Xset wrapper around the abstract `xChainCoherent` fold.  It builds the
conjugate-pair cover of `X = hyp.Xset Z` over the minimal-degree base block
`S0 = hyp.xBaseBlock Z` (`exists_conjugatePairCover`), supplies the base coherence
`xBaseBlock_isCoherent_of_irreducible_X`, and leaves exactly the per-step (5.6)/(6.6) adjoining
payload as `hstep`.

The extra disjoint-prefix and degree-monotonicity facts exposed to `hstep` are produced by the pair
cover but are not consumed by `xChainCoherent` itself; they are the data needed to construct each
`XAdjoinStepInput` without re-enumerating `X`. -/
noncomputable def Xset_isCoherent_from_adjoinSteps_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstep : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N → ∀ (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
          (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)),
        XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hXfin : (hyp.Xset Z).Finite := hyp.xSet_finite_of_irreducible_X hX
  have hXconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) :=
    hyp.Xset_closedUnderConjugate_of_irreducible_X hZH hX
  have hXreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset Z) :=
    hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH hX
  have hS0conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX
  choose e pair N hpairχ hsurj hpairs hcoverIdx hpair0Raw hpair1Raw hdisj hmono using
    exists_conjugatePairCover (X := hyp.Xset Z) (S₀ := hyp.xBaseBlock Z)
      hXfin hXconj hXreal hX hS0conj
  let χ0 : IrreducibleCharacter ↥L := ⟨Classical.choose hXne, hX _ (Classical.choose_spec hXne)⟩
  let χs : ℕ → IrreducibleCharacter ↥L := fun i => if hi : i < N then hpairχ i hi else χ0
  have hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ) := by
    intro i hi
    rw [hpair0Raw i hi]
    simp [χs, hi]
  have hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj := by
    intro i hi
    rw [hpair1Raw i hi]
    simp [χs, hi]
  have hcover : ∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨
      ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
    intro φ hφ
    obtain ⟨i, hi⟩ := hsurj φ hφ
    have hci := hcoverIdx i
    rw [hi] at hci
    exact hci
  exact xChainCoherent hyp.dade hyp.hconj pair N χs hpair0 hpair1
    (hyp.xBaseBlock_subset Z) hpairs hcover
    (hyp.xBaseBlock_isCoherent_of_irreducible_X hZH hX hXne)
    (fun i hi hcoh => hstep pair N χs hpair0 hpair1 hpairs hdisj hmono i hi hcoh)

/-- **(T8.10w) X-chain coherence engine, completeness-exposing variant.**  Identical to
`Xset_isCoherent_from_adjoinSteps_of_irreducible_X` but the per-step callback `hstep` additionally
receives the **Xset-cover completeness** witness
`hcover : ∀ φ ∈ X, φ ∈ xBaseBlock Z ∨ ∃ j < N, φ ∈ pairSet pair j`.  The base engine derives this
internally (from `exists_conjugatePairCover`) but does not expose it; the StepData producer needs it
to build the per-step `tailSet = X ∖ accumulator` and discharge `htail_le`/`hsum` (only well-behaved
when the conjugate-pair cover is complete — see `notes/peterfalvi/s08_6_8_blocker_central_Z.md`
finding #6).  Additive: no existing signature changes. -/
noncomputable def Xset_isCoherent_from_adjoinSteps_withCover_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstep : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      (∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨
        ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j) →
      ∀ i, i < N → ∀ (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
          (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)),
        XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hXfin : (hyp.Xset Z).Finite := hyp.xSet_finite_of_irreducible_X hX
  have hXconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) :=
    hyp.Xset_closedUnderConjugate_of_irreducible_X hZH hX
  have hXreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset Z) :=
    hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH hX
  have hS0conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX
  choose e pair N hpairχ hsurj hpairs hcoverIdx hpair0Raw hpair1Raw hdisj hmono using
    exists_conjugatePairCover (X := hyp.Xset Z) (S₀ := hyp.xBaseBlock Z)
      hXfin hXconj hXreal hX hS0conj
  let χ0 : IrreducibleCharacter ↥L := ⟨Classical.choose hXne, hX _ (Classical.choose_spec hXne)⟩
  let χs : ℕ → IrreducibleCharacter ↥L := fun i => if hi : i < N then hpairχ i hi else χ0
  have hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ) := by
    intro i hi
    rw [hpair0Raw i hi]
    simp [χs, hi]
  have hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj := by
    intro i hi
    rw [hpair1Raw i hi]
    simp [χs, hi]
  have hcover : ∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨
      ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
    intro φ hφ
    obtain ⟨i, hi⟩ := hsurj φ hφ
    have hci := hcoverIdx i
    rw [hi] at hci
    exact hci
  exact xChainCoherent hyp.dade hyp.hconj pair N χs hpair0 hpair1
    (hyp.xBaseBlock_subset Z) hpairs hcover
    (hyp.xBaseBlock_isCoherent_of_irreducible_X hZH hX hXne)
    (fun i hi hcoh => hstep pair N χs hpair0 hpair1 hpairs hdisj hmono hcover i hi hcoh)

end SibleyDadeHypothesis

/-- **(T8.11m) normalized degree gap from an absolute degree bound.**

If the new character and the prefix member family have natural degree ratios against the same
anchor `χ₁`, then the absolute §6.6 inequality
`2 * χ(1) * χ₁(1) < ∑ χmem(j)(1)^2` is equivalent, after dividing by the positive square
`χ₁(1)^2`, to the normalized `XAdjoinStepInput.hDeg` inequality
`2 * a < ∑ deg(j)^2`. -/
theorem normalizedDegreeGap_of_realDegreeBound
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {deg : ι → ℕ} {a : ℕ}
    (hχdeg : (χ : ClassFunction G ℂ) 1 =
      (a : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hmemdeg : ∀ i ∈ s,
      (χmem i : ClassFunction G ℂ) 1 =
        (deg i : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hAbs : 2 *
        ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
          (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) <
      ∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) :
    2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 := by
  classical
  obtain ⟨d₁, hd₁pos, hχ₁one⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ₁
  have hd₁real_pos : 0 < (d₁ : ℝ) := by exact_mod_cast hd₁pos
  have hχ₁re :
      (OddOrder.Peterfalvi.S03.characterDegree
          (χ₁ : ClassFunction G ℂ)).re = (d₁ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one]
    norm_num
  have hχre :
      (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re =
        (a : ℝ) * (d₁ : ℝ) := by
    have h := congrArg Complex.re hχdeg
    rw [hχ₁one] at h
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def, Complex.ofReal_mul] using h
  have hmemre : ∀ i ∈ s,
      (OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re =
        (deg i : ℝ) * (d₁ : ℝ) := by
    intro i hi
    have h := congrArg Complex.re (hmemdeg i hi)
    rw [hχ₁one] at h
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def, Complex.ofReal_mul] using h
  have hleft :
      2 * ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
          (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) =
        (2 * (a : ℝ)) * (d₁ : ℝ) ^ 2 := by
    rw [hχre, hχ₁re]
    ring
  have hright :
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
        (∑ i ∈ s, ((deg i : ℝ)) ^ 2) * (d₁ : ℝ) ^ 2 := by
    calc
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
          ∑ i ∈ s, (((deg i : ℝ) * (d₁ : ℝ)) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hmemre i hi]
      _ = ∑ i ∈ s, ((deg i : ℝ) ^ 2 * (d₁ : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = (∑ i ∈ s, ((deg i : ℝ)) ^ 2) * (d₁ : ℝ) ^ 2 := by
            rw [← Finset.sum_mul]
  rw [hleft, hright] at hAbs
  have hd₁sq_pos : 0 < (d₁ : ℝ) ^ 2 := sq_pos_of_pos hd₁real_pos
  nlinarith

/-- **(T8.11n) real absolute degree bound from natural prime-power data.**

This is the adapter from the pure §6.6 number-theoretic leaf in §7 to the real-valued
bound used by
`normalizedDegreeGap_of_realDegreeBound`: if natural degree values identify `χ(1)=dχ`,
`χ₁(1)=d₁`, and the member-family square sum is `D`, then the prime-power gap plus
square-divisibility `dχ^2 ∣ D` gives
`2 * χ(1).re * χ₁(1).re < ∑ χmem(j)(1).re^2`. -/
theorem realDegreeBound_of_natDegreeSumPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {p d₁ dχ q m D : ℕ} {dmem : ι → ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
        (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) <
      ∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2 := by
  classical
  have hNat : 2 * (dχ * d₁) < D :=
    OddOrder.Peterfalvi.S07.two_mul_lt_of_sq_dvd_of_gap
      (OddOrder.Peterfalvi.S07.two_mul_lt_sq_of_primePow_gap hp hpos₁ hq hdiv hlt)
      hdvd hDpos
  have hNatReal : 2 * ((dχ : ℝ) * (d₁ : ℝ)) < (D : ℝ) := by
    exact_mod_cast hNat
  have hχre :
      (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re = (dχ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχone]
    norm_num
  have hχ₁re :
      (OddOrder.Peterfalvi.S03.characterDegree
          (χ₁ : ClassFunction G ℂ)).re = (d₁ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one]
    norm_num
  have hsumCast : (∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ)) = (D : ℝ) := by
    exact_mod_cast hDsum
  have hright :
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
        (D : ℝ) := by
    calc
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
          ∑ i ∈ s, ((dmem i : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [OddOrder.Peterfalvi.S03.characterDegree_def, hmemone i hi]
            norm_num
      _ = ∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            norm_num [pow_two]
      _ = (D : ℝ) := hsumCast
  rw [hχre, hχ₁re, hright]
  exact hNatReal

/-- **(T8.11n1) real absolute degree bound from common-index p-power data.**

This variant of `realDegreeBound_of_natDegreeSumPrimePowerGap` uses the actual §6.6
common-index data instead of asking the caller to name a quotient `q` with
`dχ = q * d₁`.  The strict gap comes from
`two_mul_lt_sq_of_commonIndex_primePower_gap`; square-divisibility then pushes it to
the prefix degree sum. -/
theorem realDegreeBound_of_natDegreeSumCommonIndexPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {p idx d₁ dχ θ₁ θχ m₁ mχ D : ℕ} {dmem : ι → ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
        (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) <
      ∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2 := by
  classical
  have hidxpos : 0 < idx := commonIndex_pos_of_natDegree_factor hχone hdχ
  have hNat : 2 * (dχ * d₁) < D :=
    OddOrder.Peterfalvi.S07.two_mul_lt_of_sq_dvd_of_gap
      (OddOrder.Peterfalvi.S07.two_mul_lt_sq_of_commonIndex_primePower_gap
        hp hidxpos hd₁ hdχ hθ₁ hθχ hlt)
      hdvd hDpos
  have hNatReal : 2 * ((dχ : ℝ) * (d₁ : ℝ)) < (D : ℝ) := by
    exact_mod_cast hNat
  have hχre :
      (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re = (dχ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχone]
    norm_num
  have hχ₁re :
      (OddOrder.Peterfalvi.S03.characterDegree
          (χ₁ : ClassFunction G ℂ)).re = (d₁ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one]
    norm_num
  have hsumCast : (∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ)) = (D : ℝ) := by
    exact_mod_cast hDsum
  have hright :
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
        (D : ℝ) := by
    calc
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
          ∑ i ∈ s, ((dmem i : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [OddOrder.Peterfalvi.S03.characterDegree_def, hmemone i hi]
            norm_num
      _ = ∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            norm_num [pow_two]
      _ = (D : ℝ) := hsumCast
  rw [hχre, hχ₁re, hright]
  exact hNatReal

/-- **(T8.11o) normalized degree gap from natural prime-power data.**

Combines `realDegreeBound_of_natDegreeSumPrimePowerGap` with
`normalizedDegreeGap_of_realDegreeBound`, so a §6.6 caller with natural degree data and ratio data
can produce the `XAdjoinStepInput.hDeg` field directly. -/
theorem normalizedDegreeGap_of_natDegreeSumPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {deg : ι → ℕ} {a p d₁ dχ q m D : ℕ} {dmem : ι → ℕ}
    (hχdeg : (χ : ClassFunction G ℂ) 1 =
      (a : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hmemdeg : ∀ i ∈ s,
      (χmem i : ClassFunction G ℂ) 1 =
        (deg i : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 :=
  normalizedDegreeGap_of_realDegreeBound hχdeg hmemdeg
    (realDegreeBound_of_natDegreeSumPrimePowerGap hχone hχ₁one hmemone hDsum
      hp hpos₁ hq hdiv hlt hdvd hDpos)

/-- **(T8.11r0) intrinsic degree-divisibility from common-index p-power data.**

`exists_pos_natDegreeRatio_of_dvd` consumes an intrinsic predicate over any natural witnesses for
`χ(1)` and `χ₁(1)`.  This lemma produces that predicate from the (6.6) degree-sort data: both
degrees have the same positive induced index `idx`, their residual factors are powers of the same
base `p`, and the sorted degrees satisfy `d₁ ≤ d`. -/
theorem natDegreeDvd_of_commonIndex_primePowerData
    {G : Type*} [Group G] {χ χ₁ : IrreducibleCharacter G}
    {p idx d d₁ θ θ₁ m n : ℕ} (hp : 2 ≤ p) (hidx : 0 < idx)
    (hχone : (χ : ClassFunction G ℂ) 1 = (d : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hd : d = idx * θ) (hd₁ : d₁ = idx * θ₁)
    (hθ : θ = p ^ m) (hθ₁ : θ₁ = p ^ n) (hle : d₁ ≤ d) :
    ∀ e e₁ : ℕ, (χ : ClassFunction G ℂ) 1 = (e : ℂ) →
      (χ₁ : ClassFunction G ℂ) 1 = (e₁ : ℂ) → e₁ ∣ e := by
  intro e e₁ he he₁
  have hed : e = d := Nat.cast_injective (he.symm.trans hχone)
  have he₁d₁ : e₁ = d₁ := Nat.cast_injective (he₁.symm.trans hχ₁one)
  subst e
  subst e₁
  exact OddOrder.Peterfalvi.S07.mul_primePow_dvd_mul_primePow_of_le
    hp hidx hd₁ hd hθ₁ hθ hle

/-- **(T8.11o1) normalized degree gap from common-index p-power data.**

Combines `realDegreeBound_of_natDegreeSumCommonIndexPrimePowerGap` with
`normalizedDegreeGap_of_realDegreeBound`.  This is the consumer form used by the
common-index step constructors after the quotient `q` has been removed from their input data. -/
theorem normalizedDegreeGap_of_natDegreeSumCommonIndexPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {deg : ι → ℕ} {a p idx d₁ dχ θ₁ θχ m₁ mχ D : ℕ} {dmem : ι → ℕ}
    (hχdeg : (χ : ClassFunction G ℂ) 1 =
      (a : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hmemdeg : ∀ i ∈ s,
      (χmem i : ClassFunction G ℂ) 1 =
        (deg i : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 :=
  normalizedDegreeGap_of_realDegreeBound hχdeg hmemdeg
    (realDegreeBound_of_natDegreeSumCommonIndexPrimePowerGap hχone hχ₁one hmemone hDsum
      hp hlt hdχ hd₁ hθχ hθ₁ hdvd hDpos)

/-- **(T8.11r) degree-divisibility inputs from common-index p-power sorted degrees.**

This packages both divisibility predicates required by
`xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap`: the anchor degree divides every
prefix member degree and the new character degree.  The hypotheses are the honest (6.6) data
behind those predicates — common induced index, p-power residual degrees, and sorted natural
degrees — rather than abstract divisibility assumptions. -/
theorem degreeDivisibilityInputs_of_commonIndex_primePowerData
    {G : Type*} [Group G] {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {p idx d₁ dχ θ₁ θχ m₁ mχ : ℕ}
    {dmem θmem mmem : ι → ℕ} (hp : 2 ≤ p) (hidx : 0 < idx)
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction G ℂ) 1 = (dmem j : ℂ))
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hdmem : ∀ j ∈ s, dmem j = idx * θmem j)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hθmem : ∀ j ∈ s, θmem j = p ^ mmem j)
    (hleχ : d₁ ≤ dχ) (hlemem : ∀ j ∈ s, d₁ ≤ dmem j) :
    (∀ j ∈ s, ∀ d dAnchor : ℕ,
      (χmem j : ClassFunction G ℂ) 1 = (d : ℂ) →
      (χ₁ : ClassFunction G ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d) ∧
    (∀ d dAnchor : ℕ,
      (χ : ClassFunction G ℂ) 1 = (d : ℂ) →
      (χ₁ : ClassFunction G ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d) := by
  refine ⟨?_, ?_⟩
  · intro j hj
    exact natDegreeDvd_of_commonIndex_primePowerData hp hidx
      (hmemone j hj) hχ₁one (hdmem j hj) hd₁ (hθmem j hj) hθ₁ (hlemem j hj)
  · exact natDegreeDvd_of_commonIndex_primePowerData hp hidx
      hχone hχ₁one hdχ hd₁ hθχ hθ₁ hleχ



end OddOrder.Peterfalvi.S08
