/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_SAndT_Setup.PairStructure

/-!
# Peterfalvi (13.5)-(13.10) — counting layer

Split from the former monolithic `OddOrder.Peterfalvi.S15_SAndT_Setup` (directory split, issue 0103).
Structural `(S, T)`-pair facts live upstream in `PairStructure.lean` (prefix-split).
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


section CountingLayer

open OddOrder.GroupTheory

open scoped Classical in
/-- **The §9 setup on `T`** (the (13.4) gate-3 router, issue 9013): the `TypesIIIIIIVSetup T`
carrier assembled from the **reconciled** type-`P` datum (`reconciled_typePData_T`), so its
`U`/`W1`/`W2` are the hypothesis's `V`/`W₂`/`W₁` (companions `toTypesIIIIIIVSetupT_U_eq` etc.)
and its kernel is `H = T_F = Q` (`toTypesIIIIIIVSetupT_H_eq`).  Nontriviality: `U = V ≠ ⊥` from
`|V| = v·d ≠ 1`; `|W1| = |W₂| = p` prime; the `M_F`-TI component of `TypePNontrivialCore` is
datum-independent, read off any non-V type witness (`T_typeII_or_III_or_IV`).  Opens the §9
machinery ((9.7)–(9.9), `typeII_III_IV_order_relations`, the `hcPsi` degree analysis) on `T` —
the (13.3.b)-on-`T` route of the (13.4) θ-package.  Mirrors `toTypesIIIIIIVSetupS`; extracts the
inline construction of `Q_elementaryAbelian_T` (`S15_SAndT`) without its `IsTypeII` hypothesis. -/
noncomputable def Hypothesis.toTypesIIIIIIVSetupT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup hyp.T where
  maximal := hyp.T_maximal
  typeP := (reconciled_typePData_T hG hyp).choose
  nontrivial := by
    obtain ⟨hU, hW1, -⟩ := (reconciled_typePData_T hG hyp).choose_spec
    refine ⟨?_, ?_, ?_⟩
    · rw [hU]
      intro hbot
      apply hvd
      rw [← hyp.card_V_eq_vd, hbot, Subgroup.card_bot]
    · rw [hW1, ← hyp.p_eq_card_W2]
      exact hyp.p_prime
    · rcases hyp.T_typeII_or_III_or_IV hG hvd with h | h | h
      · exact h.some.common.2.2
      · exact h.some.common.2.2
      · exact h.some.common.2.2
  type_alt := hyp.T_typeII_or_III_or_IV hG hvd

theorem Hypothesis.toTypesIIIIIIVSetupT_U_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    (hyp.toTypesIIIIIIVSetupT hG hvd).U = hyp.V :=
  (reconciled_typePData_T hG hyp).choose_spec.1

theorem Hypothesis.toTypesIIIIIIVSetupT_W1_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    (hyp.toTypesIIIIIIVSetupT hG hvd).W1 = hyp.W2 :=
  (reconciled_typePData_T hG hyp).choose_spec.2.1

theorem Hypothesis.toTypesIIIIIIVSetupT_W2_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    (hyp.toTypesIIIIIIVSetupT hG hvd).W2 = hyp.W1 :=
  (reconciled_typePData_T hG hyp).choose_spec.2.2

theorem Hypothesis.toTypesIIIIIIVSetupT_H_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    ((hyp.toTypesIIIIIIVSetupT hG hvd).H : Subgroup G) = hyp.Q := by
  show (reconciled_typePData_T hG hyp).choose.H = hyp.Q
  rw [(reconciled_typePData_T hG hyp).choose.H_eq, hyp.Q_eq_TF]

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **§9 character data on `T`** (the T-mirror of `mkSection11CharacterDataS`, over the
`toTypesIIIIIIVSetupT` router; issue 9013 gate 3): `u = |V̄|` is rfl-pinned to the `V`-action
image on the chief factor of `Q`; `tau := hyp.tauT`; `H0CprimeSupport := ∅` and
`quotientSemidirectFrobenius := True` are the same documented count/degree-only placeholders as
the `S`-instance (NOT for coherence consumption).  Opens the §9 (9.8)/(9.9) counts — in
particular the (13.3.b) dichotomy glue `caseB_of_no_irreducible_sOf_H0Cprime` — on `T`. -/
noncomputable def Hypothesis.mkSection11CharacterDataT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    OddOrder.Peterfalvi.S11.Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief where
  u := Nat.card ↥(((quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
      (((hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U.subgroupOf
        ((hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U
          ⊔ (hyp.toTypesIIIIIIVSetupT hG hvd).typeP.W1)).subtype)).range)
  u_eq_card_quotient := rfl
  H0CprimeSupport := ∅
  tau := hyp.tauT
  quotientSemidirectFrobenius := True

/-- **Peterfalvi (13.3.b), dichotomy glue** (§9-generic, issue 9013 gate 3): if the §9 family
`𝒮(H₀C')` contains **no** irreducible character, then case (9.7.b) holds
(a `CliffordCaseBData` — carrying the Singer facts `Ū` cyclic, `u ∣ (p^q−1)/(p−1)`, irreducible
action), with `C = ⊥` and the full value `u = (p^q − 1)/(p − 1)`.

Assembly of the sorry-free §9 endpoints: `clifford_dichotomy` splits into the two Clifford cases;
in case (a) the (9.8.c) witness (`caseA_character_counts` conjunct (c)) is an irreducible member
of `𝒮(H₀C) ⊆ 𝒮(H₀C')` (`sOf_antitone`, `C' ≤ C`) — contradicting the hypothesis; in case (b) the
(9.9.c) conjunct (d) of `caseB_character_counts` delivers both values.  This is the C=1/u-full
half of (13.3.b); the "case (9.7.b) holds"半 is the returned `CliffordCaseBData` itself.  Stated
generically over `M` so both the `S`- and `T`-instances (via `toTypesIIIIIIVSetupS` /
`toTypesIIIIIIVSetupT`) can cite it — the T-instance is the (13.4) θ-package's (13.3.b)-on-`T`
input (contrapositive form). -/
theorem caseB_of_no_irreducible_sOf_H0Cprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M}
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData data}
    (chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief)
    (hno : ¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ) :
    ∃ _caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData chars,
      chars.C = ⊥ ∧ chars.u = (chief.p ^ data.q - 1) / (chief.p - 1) := by
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG chars with hA | hB
  · exfalso
    obtain ⟨caseA⟩ := hA
    obtain ⟨-, -, ⟨χ, hχmem, hχirr, -⟩, -⟩ :=
      OddOrder.Peterfalvi.S11.caseA_character_counts hG chars caseA
    exact hno ⟨χ,
      OddOrder.Peterfalvi.S11.sOf_antitone data
        (sup_le_sup_left chars.Cprime_le_C chief.H0) hχmem, hχirr⟩
  · obtain ⟨caseB⟩ := hB
    exact ⟨caseB,
      (OddOrder.Peterfalvi.S11.caseB_character_counts hG chars caseB).2.2.2 hno⟩

/-- **`q ∤ |H|`** — the order-theoretic core of the `(H^#)^G ∩ (Q^#)^G = ∅` disjointness:
`H = PC ≤ S' = PU` has order dividing `|P|·|U|` (`derived_complement`), `q ∤ |P| = p^q`
(`p ≠ q`), and `q ∤ |U|` (the `U W₁` Frobenius structure has coprime kernel and complement,
`|W₁| = q`). -/
theorem Hypothesis.q_not_dvd_card_H [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : ¬ hyp.q ∣ Nat.card ↥hyp.H := by
  intro hdvd
  -- `|H| ∣ |S'| = |P|·|U|`.
  have hHle : hyp.H ≤ derivedInG hyp.S := by
    show hyp.P ⊔ hyp.C ≤ derivedInG hyp.S
    rw [hyp.S_deriv_eq_PU]
    exact sup_le le_sup_left (le_trans (hyp.C_eq ▸ inf_le_left) le_sup_right)
  have hcard_deriv : Nat.card ↥hyp.P * Nat.card ↥hyp.U = Nat.card ↥(derivedInG hyp.S) := by
    have h := hyp.Sdata.derived_complement.card_mul
    have hPeq : hyp.Sdata.H = hyp.P := by rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPeq ▸ hyp.Sdata.H_le)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.U_le).toEquiv, hPeq,
      hyp.Sdata_U_eq] at h
  have hdvd' : hyp.q ∣ Nat.card ↥hyp.P * Nat.card ↥hyp.U := by
    rw [hcard_deriv]
    exact hdvd.trans (Subgroup.card_dvd_of_le hHle)
  rcases (Nat.Prime.dvd_mul hyp.q_prime).mp hdvd' with hq | hq
  · -- `q ∤ |P| = p^q` since `p ≠ q`.
    rw [hyp.card_P_eq hG hyp.Sdata_W2_eq] at hq
    have hqp : hyp.q ∣ hyp.p := Nat.Prime.dvd_of_dvd_pow hyp.q_prime hq
    exact hyp.p_ne_q ((Nat.prime_dvd_prime_iff_eq hyp.q_prime hyp.p_prime).mp hqp).symm
  · -- `q ∤ |U|`: `U W₁` Frobenius has coprime kernel/complement.
    -- `U ≠ ⊥` via the type-II witness on `S` (as in `basic_structure`).
    have hSII : IsTypeII hyp.S :=
      OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2
    have tdata : TypeIIData hyp.S := hSII.some
    have hSdataUne : hyp.Sdata.U ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ↥hyp.Sdata.U = Nat.card ↥tdata.typeP.U := by
        rw [hyp.Sdata.card_U_eq_index, tdata.typeP.card_U_eq_index]
      rw [hbot, Subgroup.card_bot] at h1
      exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
    have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
    have hcop := hfrob.coprime_card_kernel_complement
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
        hyp.Sdata.U ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
        hyp.Sdata.W1 ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv,
      hyp.Sdata_U_eq, hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1] at hcop
    exact hyp.q_prime.ne_one (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hq dvd_rfl))

/-- **`(H^#)^G` and `(Q^#)^G` are disjoint**: a common element would be conjugate both to a
nonidentity element of `H` (order dividing `|H|`, so prime to `q` by `q_not_dvd_card_H`) and to
a nonidentity element of `Q` (order a positive power of `q`, `|Q| = q^p`). -/
theorem disjoint_conjClassSet_sharp_H_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) :
    ∀ x : G, x ∈ conjClassSet (sharpSubgroup hyp.H) →
      x ∈ conjClassSet (sharpSubgroup hyp.Q) → False := by
  intro x hxH hxQ
  obtain ⟨a, ⟨haH, ha1⟩, g, rfl⟩ := mem_conjClassSet.mp hxH
  obtain ⟨b, ⟨hbQ, hb1⟩, h, hab⟩ := mem_conjClassSet.mp hxQ
  -- Conjugation preserves orders: `orderOf a = orderOf b`.
  have horder : orderOf a = orderOf b := by
    have h1 : orderOf (g * a * g⁻¹) = orderOf a := by
      rw [show g * a * g⁻¹ = (MulAut.conj g) a from rfl]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
    have h2 : orderOf (h * b * h⁻¹) = orderOf b := by
      rw [show h * b * h⁻¹ = (MulAut.conj h) b from rfl]
      exact orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective b
    rw [← h1, ← hab, h2]
  -- `orderOf b` is a positive power of `q`, so `q ∣ orderOf a ∣ |H|`.
  have hbdvd : orderOf b ∣ hyp.q ^ hyp.p := by
    have h1 : orderOf (⟨b, hbQ⟩ : ↥hyp.Q) ∣ Nat.card ↥hyp.Q := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk b hbQ, hcardQ] at h1
  obtain ⟨i, hip, hbord⟩ := (Nat.dvd_prime_pow hyp.q_prime).mp hbdvd
  have hi0 : i ≠ 0 := by
    intro hi0
    rw [hi0, pow_zero] at hbord
    exact hb1 (orderOf_eq_one_iff.mp hbord)
  have hqdvd_a : hyp.q ∣ orderOf a := by
    rw [horder, hbord]
    exact dvd_pow_self hyp.q hi0
  have hadvd : orderOf a ∣ Nat.card ↥hyp.H := by
    have h1 : orderOf (⟨a, SetLike.mem_coe.mp haH⟩ : ↥hyp.H) ∣ Nat.card ↥hyp.H :=
      orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk a (SetLike.mem_coe.mp haH)] at h1
  exact hyp.q_not_dvd_card_H hG (hqdvd_a.trans hadvd)

/-- Membership in the generic set `G₀`, unfolded: nonidentity and in neither saturation. -/
theorem Hypothesis.mem_G0_iff (hyp : Hypothesis (G := G)) (x : G) :
    x ∈ hyp.G0 ↔ x ≠ 1 ∧ x ∉ conjClassSet (sharpSubgroup hyp.H)
      ∧ x ∉ conjClassSet (sharpSubgroup hyp.Q) := by
  show x ∈ sharpSubgroup (⊤ : Subgroup G) \ _ ↔ _
  simp only [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_top, true_and, Set.mem_union, not_or]

open scoped Classical in
/-- **The four-piece split of a conjugation-invariant sum** (the (13.10) counting skeleton):
for a conjugation-invariant `f`,

  `∑_G f = f(1) + ∑_{G₀} f + [G:S]·∑_{H^#} f + [G:T]·∑_{Q^#} f`.

`G` is the disjoint union of `{1}`, `G₀`, `(H^#)^G`, and `(Q^#)^G` (the saturations are disjoint
by `disjoint_conjClassSet_sharp_H_Q` and miss `1`; `G₀` is *defined* as the complement), and each
saturation sum collapses by `IsTISubset.sum_conjClassSet` (issue 9011) via the proven TI
structure (`H_sharp_isTISubset` / `Q_sharp_isTISubset`).  Instantiations: `f = ‖χ(·)‖²` gives the
Parseval splits (13.10.1)/(13.10.2); `f = 1` the cover count (13.10.3). -/
theorem Hypothesis.sum_univ_split [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {M : Type*} [AddCommMonoid M] (f : G → M)
    (hf : ∀ g x : G, f (g * x * g⁻¹) = f x)
    (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) (hvd : hyp.v * hyp.d ≠ 1) :
    ∑ x : G, f x
      = f 1 + (∑ x ∈ hyp.G0Finset, f x)
        + hyp.S.index • ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, f x
        + hyp.T.index • ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, f x := by
  classical
  -- TI structure and stabilization on both sides.
  have hTIH : OddOrder.GroupTheory.IsTISubset (sharpSubgroup hyp.H) hyp.S :=
    H_sharp_isTISubset hG hyp
  have hTIQ : OddOrder.GroupTheory.IsTISubset (sharpSubgroup hyp.Q) hyp.T :=
    Q_sharp_isTISubset hG hyp hvd
  have hstabH : ∀ l ∈ hyp.S, MulAut.conj l • sharpSubgroup hyp.H = sharpSubgroup hyp.H :=
    fun l hl => conj_smul_sharpSubgroup_eq (normalizer_H_eq_S hG hyp) hl
  have hstabQ : ∀ l ∈ hyp.T, MulAut.conj l • sharpSubgroup hyp.Q = sharpSubgroup hyp.Q :=
    fun l hl => conj_smul_sharpSubgroup_eq (normalizer_Q_eq_T hG hyp) hl
  -- The four Finset pieces.
  set CH : Finset G := (Set.toFinite (conjClassSet (sharpSubgroup hyp.H))).toFinset with hCHdef
  set CQ : Finset G := (Set.toFinite (conjClassSet (sharpSubgroup hyp.Q))).toFinset with hCQdef
  have hmemCH : ∀ x : G, x ∈ CH ↔ x ∈ conjClassSet (sharpSubgroup hyp.H) := fun x =>
    (Set.toFinite _).mem_toFinset
  have hmemCQ : ∀ x : G, x ∈ CQ ↔ x ∈ conjClassSet (sharpSubgroup hyp.Q) := fun x =>
    (Set.toFinite _).mem_toFinset
  have hmemG0 : ∀ x : G, x ∈ hyp.G0Finset ↔ x ∈ hyp.G0 := fun x =>
    (Set.toFinite _).mem_toFinset
  -- Nonidentity: conjugates of nonidentity elements are nonidentity.
  have hne1 : ∀ (K : Subgroup G) (x : G), x ∈ conjClassSet (sharpSubgroup K) → x ≠ 1 := by
    rintro K x hx rfl
    obtain ⟨a, ⟨-, ha1⟩, g, hg⟩ := mem_conjClassSet.mp hx
    refine ha1 ?_
    show a = 1
    have ha : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [ha, hg]
    group
  have hne1H : ∀ x ∈ CH, x ≠ 1 := fun x hx => hne1 hyp.H x ((hmemCH x).mp hx)
  have hne1Q : ∀ x ∈ CQ, x ≠ 1 := fun x hx => hne1 hyp.Q x ((hmemCQ x).mp hx)
  -- `G₀` misses `1` and both saturations (definitional).
  have hG0iff := hyp.mem_G0_iff
  -- The partition: `univ = {1} ∪ G₀ ∪ CH ∪ CQ`, pairwise disjoint.
  have hcover : (Finset.univ : Finset G) = insert 1 (hyp.G0Finset ∪ CH ∪ CQ) := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, true_iff]
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · refine Or.inr ?_
      by_cases hxH : x ∈ conjClassSet (sharpSubgroup hyp.H)
      · exact Or.inl (Or.inr ((hmemCH x).mpr hxH))
      · by_cases hxQ : x ∈ conjClassSet (sharpSubgroup hyp.Q)
        · exact Or.inr ((hmemCQ x).mpr hxQ)
        · exact Or.inl (Or.inl ((hmemG0 x).mpr ((hG0iff x).mpr ⟨hx1, hxH, hxQ⟩)))
  have hdisjHQ : Disjoint CH CQ := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact disjoint_conjClassSet_sharp_H_Q hG hyp hcardQ x ((hmemCH x).mp hx) ((hmemCQ x).mp hx')
  have hdisjG0 : Disjoint hyp.G0Finset (CH ∪ CQ) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨-, hxH, hxQ⟩ := (hG0iff x).mp ((hmemG0 x).mp hx)
    rcases Finset.mem_union.mp hx' with h | h
    · exact hxH ((hmemCH x).mp h)
    · exact hxQ ((hmemCQ x).mp h)
  have hone_notin : (1 : G) ∉ hyp.G0Finset ∪ CH ∪ CQ := by
    intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact ((hG0iff 1).mp ((hmemG0 1).mp h')).1 rfl
      · exact hne1H 1 h' rfl
    · exact hne1Q 1 h rfl
  -- Assemble the split.
  rw [hcover, Finset.sum_insert hone_notin, Finset.union_assoc, Finset.sum_union hdisjG0,
    Finset.sum_union hdisjHQ, hCHdef, hCQdef,
    OddOrder.GroupTheory.IsTISubset.sum_conjClassSet f hTIH hstabH hf,
    OddOrder.GroupTheory.IsTISubset.sum_conjClassSet f hTIQ hstabQ hf]
  abel

/-- `|S'| = |P|·|U|` — the (13.1.b) `S' = P ⋊ U` order decomposition
(`Sdata.derived_complement`). -/
theorem Hypothesis.card_deriv_S_eq [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥(derivedInG hyp.S) = Nat.card ↥hyp.P * Nat.card ↥hyp.U := by
  have h := hyp.Sdata.derived_complement.card_mul
  have hPeq : hyp.Sdata.H = hyp.P := by rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.H_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.U_le).toEquiv, hPeq,
    hyp.Sdata_U_eq] at h
  exact h.symm

/-- `|S| = |S'|·q` — the (13.1.b) `S = S' ⋊ W₁` order decomposition (`Sdata.M_complement`). -/
theorem Hypothesis.card_S_eq_deriv_mul_q [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.S = Nat.card ↥(derivedInG hyp.S) * hyp.q := by
  have hle : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have h := hyp.Sdata.M_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.W1_le).toEquiv,
    hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1] at h
  exact h.symm

/-- **`|S| = p^q·(uc)·q`** — the (13.2)-level order value of `S`, assembling
`card_S_eq_deriv_mul_q`, `card_deriv_S_eq`, `card_P_eq` (`|P| = p^q`), and `|U| = uc`. -/
theorem Hypothesis.card_S_val [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.S = hyp.p ^ hyp.q * (hyp.u * hyp.c) * hyp.q := by
  rw [hyp.card_S_eq_deriv_mul_q, hyp.card_deriv_S_eq, hyp.card_P_eq hG hyp.Sdata_W2_eq,
    hyp.card_U_eq_uc]

/-- **`|H| = p^q · c`** (Peterfalvi (13.2)): `H = PC` with `P = S_F` elementary abelian of order
`p^q` and `C = C_U(P)` of order `c`, and `P ⊓ C = ⊥` (`P` a `p`-group, `C ≤ U` with `|U| = uc`
coprime to `p` by the Hall property of `P` in `S`).  So `|PC| = |P|·|C| = p^q·c` (the complement
`card_mul_card_of_complement_normal`, `P ◁ H`).  Feeds `[S:H] = uq` (`mu_j_isIndPC` degree) and the
(13.5) counting value `|H^#|/|S| = uq/(cp^q)`. -/
theorem Hypothesis.card_H_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.H = hyp.p ^ hyp.q * hyp.c := by
  have hP_le_S : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hC_le_S : hyp.C ≤ hyp.S := by
    have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    exact le_trans (hyp.C_eq ▸ inf_le_left) hUS
  have hPH : hyp.P ≤ hyp.H := le_sup_left
  have hCH : hyp.C ≤ hyp.H := le_sup_right
  have hPcard : Nat.card ↥hyp.P = hyp.p ^ hyp.q := hyp.card_P_eq hG hyp.Sdata_W2_eq
  -- `p ∤ c`: `P` Hall in `S`, `[S:P] = ucq`
  have hPScard : Nat.card ↥(hyp.P.subgroupOf hyp.S) = Nat.card ↥hyp.P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_S).toEquiv
  have hcop : Nat.Coprime (hyp.p ^ hyp.q) ((hyp.P.subgroupOf hyp.S).index) := by
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.S
    rw [← hyp.P_eq_SF] at hHall
    have h0 := Ch03.IsHallSubgroup.coprime_index hHall
    rw [hPScard, hPcard] at h0
    exact h0
  have hSPidx : (hyp.P.subgroupOf hyp.S).index = hyp.u * hyp.c * hyp.q := by
    have hm := Subgroup.card_mul_index (hyp.P.subgroupOf hyp.S)
    rw [hPScard, hPcard, hyp.card_S_val hG] at hm
    have hpq : (0 : ℕ) < hyp.p ^ hyp.q := pow_pos hyp.p_prime.pos hyp.q
    have hmm : hyp.p ^ hyp.q * (hyp.P.subgroupOf hyp.S).index
        = hyp.p ^ hyp.q * (hyp.u * hyp.c * hyp.q) := by rw [hm]; ring
    exact Nat.eq_of_mul_eq_mul_left hpq hmm
  have hpc : Nat.Coprime (hyp.p ^ hyp.q) hyp.c := by
    have hcdvd : hyp.c ∣ (hyp.P.subgroupOf hyp.S).index := by
      rw [hSPidx]; exact ⟨hyp.u * hyp.q, by ring⟩
    exact Nat.Coprime.coprime_dvd_right hcdvd hcop
  have hpc' : Nat.gcd (hyp.p ^ hyp.q) hyp.c = 1 := hpc
  -- `P ⊓ C = ⊥` from coprime orders
  have hdisj : hyp.P ⊓ hyp.C = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have hd1 : Nat.card ↥(hyp.P ⊓ hyp.C) ∣ hyp.p ^ hyp.q :=
      hPcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(hyp.P ⊓ hyp.C) ∣ hyp.c :=
      hyp.c_eq_card_C ▸ Subgroup.card_dvd_of_le inf_le_right
    exact Nat.dvd_one.mp (hpc' ▸ Nat.dvd_gcd hd1 hd2)
  -- `|H| = |P|·|C|` (complement `P ◁ H`)
  haveI hPnormalH : (hyp.P.subgroupOf hyp.H).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr ?_
    have hSnorm : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
      rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
    exact le_trans (hyp.H_le_S) hSnorm
  have hinf : hyp.P.subgroupOf hyp.H ⊓ hyp.C.subgroupOf hyp.H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
    have hmem : ((x : ↥hyp.H) : G) ∈ hyp.P ⊓ hyp.C :=
      ⟨Subgroup.mem_subgroupOf.mp hxP, Subgroup.mem_subgroupOf.mp hxC⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; exact Subtype.ext hmem
  have hsup : hyp.P.subgroupOf hyp.H ⊔ hyp.C.subgroupOf hyp.H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPH hCH]
    exact Subgroup.subgroupOf_self hyp.H
  have hcompl : Subgroup.IsComplement' (hyp.P.subgroupOf hyp.H) (hyp.C.subgroupOf hyp.H) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf)
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
  have hmul := hcompl.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv, hPcard,
    ← hyp.c_eq_card_C] at hmul
  exact hmul.symm

/-- **`[S : H] = uq`** (Peterfalvi (13.2)): the index of `H = PC` in `S`.  From
`|S| = p^q·(uc)·q` (`card_S_val`) and `|H| = p^q·c` (`card_H_eq`), `[S:H] = |S|/|H| = uq`.  The
degree index of `mu_j_isIndPC` (`μ_j(1) = [S:H]·θ(1) = uq`). -/
theorem Hypothesis.H_index_eq_uq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (hyp.H.subgroupOf hyp.S).index = hyp.u * hyp.q := by
  have hm := Subgroup.card_mul_index (hyp.H.subgroupOf hyp.S)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hyp.H_le_S)).toEquiv, hyp.card_H_eq hG,
    hyp.card_S_val hG] at hm
  have hpos : (0 : ℕ) < hyp.p ^ hyp.q * hyp.c :=
    Nat.mul_pos (pow_pos hyp.p_prime.pos hyp.q) (hyp.c_eq_card_C ▸ Nat.card_pos)
  have hmm : hyp.p ^ hyp.q * hyp.c * (hyp.H.subgroupOf hyp.S).index
      = hyp.p ^ hyp.q * hyp.c * (hyp.u * hyp.q) := by rw [hm]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos hmm

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a), degree**: each nonzero `μ`-column sum has degree `uq`.  Immediate from
`mu_j_isIndPC` (`μ_j = Ind_{PC} θ`, `θ` linear) and `H_index_eq_uq` (`[S:H] = uq`):
`μ_j(1) = [S:H]·θ(1) = uq·1 = uq`. -/
theorem Hypothesis.mu_j_degree [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    (∑ i : Fin hyp.q, hyp.mu i j) (1 : ↥hyp.S) = ((hyp.u * hyp.q : ℕ) : ℂ) := by
  haveI := hyp.finiteG
  obtain ⟨θ, hθirr, hθ1, hθeq⟩ := hyp.mu_j_isIndPC hG j hj
  rw [hθeq, ClassFunction.induce_apply_one, hθ1, mul_one, hyp.H_index_eq_uq hG]

open scoped FiniteInduce in
/-- **Column-constant degree** (Peterfalvi (13.1.e)/(4.3.c)): within a column `j`, all
`μ_{ij}(1)` are equal.  From `mu_definition` at `1`: the LHS `Ind_W^S(ω_{ij} − ω_{0j})(1)` is
`[S:W]·(ω_{ij}(1) − ω_{0j}(1)) = 0` (`omega_apply_one`: `ω`-grid linear), so the RHS
`δ_j·(μ_{ij}(1) − μ_{0j}(1)) = 0`, and `δ_j = ±1 ≠ 0` (`delta_pm_one`) gives the equality. -/
theorem Hypothesis.mu_apply_one_column_const [Finite G] (hyp : Hypothesis (G := G))
    (i : Fin hyp.q) (j : Fin hyp.p) :
    hyp.mu i j (1 : ↥hyp.S) = hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) := by
  haveI := hyp.finiteG
  have hdef := hyp.mu_definition i j
  have h1 := congrArg (fun f : ClassFunction ↥hyp.S ℂ => f (1 : ↥hyp.S)) hdef
  -- LHS(1) = 0
  rw [ClassFunction.induce_apply_one] at h1
  have homega0 : (ClassFunction.compHom
      (Subgroup.subgroupOfEquivOfLe ((le_of_eq hyp.W_eq_inter).trans inf_le_left)).toMonoidHom
        (hyp.omega i j - hyp.omega ⟨0, hyp.q_prime.pos⟩ j))
      (1 : ↥(hyp.W.subgroupOf hyp.S)) = 0 := by
    rw [ClassFunction.compHom_apply, map_one, ClassFunction.sub_apply,
      hyp.omega_apply_one, hyp.omega_apply_one, sub_self]
  rw [homega0, mul_zero] at h1
  -- RHS(1) = δ_j·(μ_{ij}(1) − μ_{0j}(1)) = 0, with δ_j ≠ 0
  have hδ : (hyp.delta j : ℂ) ≠ 0 := by
    rcases (hyp.delta_pm_one.1 j) with h | h <;> rw [h] <;> norm_num
  have hsub : hyp.mu i j (1 : ↥hyp.S) - hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) = 0 :=
    (mul_eq_zero.mp h1.symm).resolve_left hδ
  exact sub_eq_zero.mp hsub

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a), per-entry degree**: `μ_{ij}(1) = u` for `j ≥ 1`.  The column is
degree-constant (`mu_apply_one_column_const`), so the column sum `μ_j(1) = q·μ_{0j}(1)`; with
`μ_j(1) = uq` (`mu_j_degree`) and `q ≠ 0`, `μ_{0j}(1) = u`.  The `μ_{ij}(1) = u` that Peterfalvi
(13.3.c) feeds into the `(4.3.d)` congruence `u ≡ δ_j (mod q)` for `δ_j = 1`. -/
theorem Hypothesis.mu_apply_one_eq_u [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (i : Fin hyp.q) (j : Fin hyp.p)
    (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    hyp.mu i j (1 : ↥hyp.S) = ((hyp.u : ℕ) : ℂ) := by
  haveI := hyp.finiteG
  -- `∑ᵢ μ_{ij}(1) = q·μ_{0j}(1)` and `= uq`
  have hsum := hyp.mu_j_degree hG j hj
  rw [ClassFunction.finset_sum_apply] at hsum
  have hconst : ∑ k : Fin hyp.q, hyp.mu k j (1 : ↥hyp.S)
      = (hyp.q : ℂ) * hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) := by
    rw [Finset.sum_congr rfl (fun k _ => hyp.mu_apply_one_column_const k j),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hconst] at hsum
  have hq0 : (hyp.q : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact hyp.q_prime.pos.ne'
  have h0j : hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) = ((hyp.u : ℕ) : ℂ) := by
    have : (hyp.q : ℂ) * hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S)
        = (hyp.q : ℂ) * ((hyp.u : ℕ) : ℂ) := by rw [hsum]; push_cast; ring
    exact mul_left_cancel₀ hq0 this
  rw [hyp.mu_apply_one_column_const i j, h0j]

/-- **Peterfalvi `u ≡ 1 (mod q)`** (the (13.3.c) crux, (11.8.1) `|Ū| ≡ 1 mod q`).  The `S`-side
`U W₁` is a Frobenius group (`typeP_uW1_frobenius`), so for the conjugation homomorphism
`φ : U W₁ →* Aut(P)` the kernel-image `φ(U) = U/C_U(P) = Ū` satisfies `|Ū| ≡ 1 (mod |W₁|)`
(`IsFrobeniusGroup.card_range_comp_subtype_modEq_one`, Isaacs Lemma 6.1); with `|Ū| = u`
(`card_U_eq_uc`, `C = U ⊓ C_G(P)`) and `|W₁| = q` this is `u ≡ 1 (mod q)`.  Crucially **ungated**:
uses only the (proven) `U W₁` Frobenius structure, not the case-(b) Singer field model. -/
theorem Hypothesis.u_modEq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.u ≡ 1 [MOD hyp.q] := by
  haveI := hyp.finiteG
  have hSII : IsTypeII hyp.S :=
    OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2
  have tdata : TypeIIData hyp.S := hSII.some
  have hSdataUne : hyp.Sdata.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥hyp.Sdata.U = Nat.card ↥tdata.typeP.U := by
      rw [hyp.Sdata.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
  have hUW1leS : hyp.Sdata.U ⊔ hyp.Sdata.W1 ≤ hyp.S :=
    sup_le (hyp.Sdata.U_le.trans (Subgroup.map_subtype_le _)) hyp.Sdata.W1_le
  have hSnormP : hyp.S ≤ Subgroup.normalizer hyp.P := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hUW1normP : hyp.Sdata.U ⊔ hyp.Sdata.W1 ≤ Subgroup.normalizer hyp.P :=
    le_trans hUW1leS hSnormP
  letI : MulDistribMulAction ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1) ↥hyp.P :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer hyp.P)) ↥hyp.P
      (Subgroup.inclusion hUW1normP)
  set φ : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1) →* MulAut ↥hyp.P :=
    MulDistribMulAction.toMulAut ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1) ↥hyp.P with hφ
  have hmod := hfrob.card_range_comp_subtype_modEq_one φ
  have hAcard : Nat.card ↥(hyp.Sdata.W1.subgroupOf (hyp.Sdata.U ⊔ hyp.Sdata.W1)) = hyp.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
      hyp.Sdata.W1 ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv, hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
  have hφapply : ∀ (a : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1)) (p : ↥hyp.P),
      ((φ a p : ↥hyp.P) : G) = (a : G) * (p : G) * (a : G)⁻¹ := fun a p => rfl
  have hker_iff : ∀ a : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1),
      φ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (hyp.P : Set G) := by
    intro a
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h1 p hp
      have hcg := congrArg (fun e : MulAut ↥hyp.P => ((e ⟨p, hp⟩ : ↥hyp.P) : G)) h1
      simp only [hφapply, MulAut.one_apply] at hcg
      exact (mul_inv_eq_iff_eq_mul.mp hcg).symm
    · intro hc
      ext p
      simp only [hφapply, MulAut.one_apply]
      have hpc := hc (p : G) p.2
      rw [← hpc]; group
  set N := hyp.Sdata.U.subgroupOf (hyp.Sdata.U ⊔ hyp.Sdata.W1) with hN
  set ψ : ↥N →* MulAut ↥hyp.P := φ.comp N.subtype with hψ
  set ρ : ↥N →* G := (hyp.Sdata.U ⊔ hyp.Sdata.W1).subtype.comp N.subtype with hρ
  have hρinj : Function.Injective ρ :=
    (hyp.Sdata.U ⊔ hyp.Sdata.W1).subtype_injective.comp N.subtype_injective
  have hkermap : (ψ.ker).map ρ = hyp.C := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply] at hn
      have hgC : (ρ n : G) ∈ Subgroup.centralizer (hyp.P : Set G) := (hker_iff _).mp hn
      have hgU : (ρ n : G) ∈ hyp.Sdata.U := Subgroup.mem_subgroupOf.mp n.2
      have hgU' : (ρ n : G) ∈ hyp.U := by rw [← hyp.Sdata_U_eq]; exact hgU
      rw [hyp.C_eq]
      exact ⟨hgU', hgC⟩
    · intro hgC
      rw [hyp.C_eq, Subgroup.mem_inf] at hgC
      obtain ⟨hgU, hgc⟩ := hgC
      have hgUS : g ∈ hyp.Sdata.U := by rw [hyp.Sdata_U_eq]; exact hgU
      have hgUW1 : g ∈ hyp.Sdata.U ⊔ hyp.Sdata.W1 :=
        (le_sup_left : hyp.Sdata.U ≤ _) hgUS
      have hgN : (⟨g, hgUW1⟩ : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1)) ∈ N :=
        Subgroup.mem_subgroupOf.mpr hgUS
      refine ⟨⟨⟨g, hgUW1⟩, hgN⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply]
      exact (hker_iff _).mpr hgc
  have hkercard : Nat.card ↥(ψ.ker) = hyp.c := by
    rw [hyp.c_eq_card_C, ← hkermap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ ρ hρinj).toEquiv
  have hNcard : Nat.card ↥N = hyp.u * hyp.c := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
      hyp.Sdata.U ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv, hyp.Sdata_U_eq, hyp.card_U_eq_uc]
  have hrangecard : Nat.card ↥(ψ.range) = hyp.u := by
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hkercard, hNcard] at hsplit
    have hc0 : 0 < hyp.c := hyp.c_eq_card_C ▸ Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hc0 hsplit).symm
  have hru : Nat.card ↥((φ.comp N.subtype).range) = hyp.u := hrangecard
  rw [hru, hAcard] at hmod
  exact hmod

/-- **Peterfalvi (13.3.c), the `S`-side signs are `1`**: `δ_j = 1` for `j ≥ 1`.  The (4.3.d)
congruence `μ_{0j}(1) = δ_j + q·a` (`mu_degree_modEq_delta`) with `μ_{0j}(1) = u`
(`mu_apply_one_eq_u`) and `u ≡ 1 (mod q)` (`u_modEq_one`) gives `q ∣ δ_j − 1`; since `δ_j = ±1`
(`delta_pm_one`) and `q ≥ 3`, `δ_j = -1` would force `q ∣ 2`, so `δ_j = 1`. -/
theorem Hypothesis.delta_eq_one_of_ne_zero [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    hyp.delta j = 1 := by
  obtain ⟨a, ha⟩ := hyp.mu_degree_modEq_delta ⟨0, hyp.q_prime.pos⟩ j
  rw [hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩ j hj] at ha
  have haZ : (hyp.u : ℤ) = hyp.delta j + (hyp.q : ℤ) * a := by exact_mod_cast ha
  have hqu : (hyp.q : ℤ) ∣ (hyp.u : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd.mp (hyp.u_modEq_one hG))
    simpa using (dvd_neg.mpr h)
  have hqδ : (hyp.q : ℤ) ∣ hyp.delta j - 1 := by
    have hsub : hyp.delta j - 1 = ((hyp.u : ℤ) - 1) - (hyp.q : ℤ) * a := by
      rw [haZ]; ring
    rw [hsub]
    exact dvd_sub hqu (Dvd.intro a rfl)
  rcases hyp.delta_pm_one.1 j with h1 | hm1
  · exact h1
  · exfalso
    rw [hm1] at hqδ
    have hq2 : (hyp.q : ℤ) ∣ 2 := dvd_neg.mp (by simpa using hqδ)
    have hqle : hyp.q ≤ 2 := Nat.le_of_dvd (by norm_num) (by exact_mod_cast hq2)
    have h2le := hyp.q_prime.two_le
    have hodd := Nat.odd_iff.mp hyp.q_odd
    omega

/-- **Peterfalvi (13.3.c), the `S`-side signs are all `1`**: `δ_j = 1` for every `j`.  The
base `δ_0 = 1` is the (4.4) trivial-column anchor (`delta_zero_eq_one`); for `j ≥ 1` it is
`delta_eq_one_of_ne_zero` (the `u ≡ 1 (mod q)` route).  This is the `S`-half of the
`CharacterDegreeData.delta_eq_one` field. -/
theorem Hypothesis.delta_eq_one_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) : hyp.delta j = 1 := by
  by_cases hj : j = ⟨0, hyp.p_prime.pos⟩
  · rw [hj]; exact hyp.delta_zero_eq_one
  · exact hyp.delta_eq_one_of_ne_zero hG j hj

/-- **Peterfalvi (4.3.c)+(13.3.c), the `W₁#` `μ`-value**: `μ_{0j}(x) = 1` for `x ∈ W₁`,
`x ≠ 1`.  The (4.3.c) value identity `mu_apply_of_not_mem_W2` applies (`x ∉ W₂` since
`W₁ ⊓ W₂ = ⊥` and `x ≠ 1`), giving `μ_{0j}(x) = δ_j·ω_{0j}(x)`; then `δ_j = 1`
(`delta_eq_one_S`, Pf (13.3.c)) and the row-`0` `ω`-value `ω_{0j}|_{W₁} = 1`
(`omega_row_zero_apply_of_mem_W1`).  This is the `hmuW1` input of the (13.18.a) exact
`β`-support `betaGrid_support_sharpP_union_typePV_of_values` (`S16_NonExistenceG/TGapCross`)
and of the original support argument (Pf p.83 "`μ_{0j}(x) = ω_{0j}(x) = 1`"). -/
theorem Hypothesis.mu_row0_apply_eq_one_of_mem_W1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (x : ↥hyp.S) (hxW1 : (x : G) ∈ hyp.W1) (hx1 : x ≠ 1) :
    hyp.mu ⟨0, hyp.q_prime.pos⟩ j x = 1 := by
  have hxW : (x : G) ∈ hyp.W := by
    rw [hyp.W_eq_join]; exact Subgroup.mem_sup_left hxW1
  have hxW2 : (x : G) ∉ (hyp.W2 : Set G) := by
    intro hmem
    apply hx1
    have hinf : (x : G) ∈ hyp.W1 ⊓ hyp.W2 := ⟨hxW1, hmem⟩
    rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hinf
    exact Subtype.ext hinf
  have hval := hyp.mu_apply_of_not_mem_W2 ⟨0, hyp.q_prime.pos⟩ j (x : G) hxW x.2 hxW2
  rw [show (⟨(x : G), x.2⟩ : ↥hyp.S) = x from rfl] at hval
  rw [hval, hyp.delta_eq_one_S hG j,
    hyp.omega_row_zero_apply_of_mem_W1 j ⟨(x : G), hxW⟩ hxW1]
  norm_num

/-- `|T| = |Q|·(vd)·p` — the `T`-side order decomposition, read off the reconciled type-`P`
datum (`M_complement`/`derived_complement` of `reconciled_typePData_T`) with `|V| = vd` and
`|W₂| = p`. -/
theorem Hypothesis.card_T_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.T = Nat.card ↥hyp.Q * (hyp.v * hyp.d) * hyp.p := by
  obtain ⟨tpd, hU, hW1, -⟩ := reconciled_typePData_T hG hyp
  -- `|T| = |T'|·p`.
  have hle : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have h1 := tpd.M_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.W1_le).toEquiv,
    hW1, ← hyp.p_eq_card_W2] at h1
  -- `|T'| = |Q|·|V| = |Q|·(vd)`.
  have h2 := tpd.derived_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.H_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.U_le).toEquiv, tpd.H_eq, ← hyp.Q_eq_TF,
    hU, hyp.card_V_eq_vd] at h2
  rw [← h1, ← h2]

/-- `|T| = |T'|·p` — the `T`-side mirror of `card_S_eq_deriv_mul_q`
(`M_complement` of the reconciled type-`P` datum + `|W₂| = p`). -/
theorem Hypothesis.card_T_eq_deriv_mul_p [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.T = Nat.card ↥(derivedInG hyp.T) * hyp.p := by
  obtain ⟨tpd, -, hW1, -⟩ := reconciled_typePData_T hG hyp
  have hle : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have h := tpd.M_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.W1_le).toEquiv,
    hW1, ← hyp.p_eq_card_W2] at h
  exact h.symm

/-- **`(QD)^# ⊆ A(T)` membership** ((13.2.e) structural input, issue 0116 step 4): every
nonidentity element of `K = QD` lies in the honest type-`P` support `A(T)`.  Split `z = q·d`
along the `T`-normalized `Q` (`exists_mul_of_mem_sup_of_normalized`); `d ∈ D = C_V(Q)`
centralizes `Q` (`D_eq`), so for `q ≠ 1` the pair `(q, z)` witnesses `z ∈ C_{T'}(q)^#` with
`q ∈ Q^# ⊆ T_σ^#` (`maxNilpotentNormalHall_le_Msigma`), while for `q = 1` (so `z = d ∈ D^#`)
any `x ∈ Q^#` (`Q_ne_bot`) serves as the `T_σ^#`-witness. -/
theorem Hypothesis.mem_honestTypeP2ASet_of_mem_Q_sup_D [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {z : G} (hz : z ∈ hyp.Q ⊔ hyp.D) (hz1 : z ≠ 1) :
    z ∈ honestTypeP2ASet hyp.T := by
  have hQT' : hyp.Q ≤ derivedInG hyp.T := hyp.T_deriv_eq_QV ▸ le_sup_left
  have hDV : hyp.D ≤ hyp.V := hyp.D_eq ▸ inf_le_left
  have hVT' : hyp.V ≤ derivedInG hyp.T := hyp.T_deriv_eq_QV ▸ le_sup_right
  have hQT : hyp.Q ≤ hyp.T := hQT'.trans (Subgroup.map_subtype_le _)
  have hDT : hyp.D ≤ hyp.T := (hDV.trans hVT').trans (Subgroup.map_subtype_le _)
  have hTnorm : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  have hzT' : z ∈ derivedInG hyp.T := (sup_le hQT' (hDV.trans hVT')) hz
  have hQMs : hyp.Q ≤ OddOrder.BG.Ch3.S10.Msigma hyp.T := by
    rw [hyp.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.T_maximal
  obtain ⟨q, hq, d, hd, rfl⟩ :=
    OddOrder.Peterfalvi.S13.exists_mul_of_mem_sup_of_normalized hQT hDT hTnorm hz
  have hdC : d ∈ Subgroup.centralizer (hyp.Q : Set G) :=
    (Subgroup.mem_inf.mp (hyp.D_eq ▸ hd)).2
  by_cases hq1 : q = 1
  · -- `z = d ∈ D^#`: any `x ∈ Q^#` is the `T_σ^#`-witness (`D` centralizes all of `Q`)
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hyp.Q_ne_bot
    refine mem_honestTypeP2ASet.mpr ⟨hzT', hz1, (x : G),
      ⟨hQMs x.2, fun h => hx1 (Subtype.ext h)⟩, ?_⟩
    rw [hq1, one_mul]
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr x.2) hdC
  · -- `q ≠ 1`: `q` itself is the witness — `q` and `d` both centralize `q`
    refine mem_honestTypeP2ASet.mpr ⟨hzT', hz1, q, ⟨hQMs hq, hq1⟩, ?_⟩
    exact Subgroup.mul_mem _
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hq) hdC)

/-- **(13.2.e)-for-`T`, `K^# = (QD)^#` TI-centralizer gate** ((13.4) structural gate, issue 9013
追記⁶ (c)): every nonidentity element of `K = QD` has its `G`-centralizer inside `T`.
Discharged through the honest `A(T)`-support (issue 0116 step 4): `(QD)^# ⊆ A(T)`
(`mem_honestTypeP2ASet_of_mem_Q_sup_D`), and no `A(T)`-point escapes a type-`P` maximal
(`escaping_honestTypeP2ASet_eq_empty`, the proven (13.2.e) core via BG Theorem D(4)); the
type-V exclusion feeding the latter is Peterfalvi (10.10)
(`no_typeV_maximal_unconditional`, whose remaining upstream gap is the (6.5) gate, issue
2022), and `T` is type `P` from `T_nonI` (`isTypeP_of_isTypeNonI`). -/
theorem QD_sharp_centralizer_le_T [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∀ z : ↥hyp.T, (z : G) ∈ hyp.Q ⊔ hyp.D → z ≠ 1 →
      Subgroup.centralizer ({(z : G)} : Set G) ≤ hyp.T := by
  intro z hzQD hz1
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hmemA : (z : G) ∈ honestTypeP2ASet hyp.T :=
    hyp.mem_honestTypeP2ASet_of_mem_Q_sup_D _hG hzQD hz1'
  have hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI _hG hyp.T_maximal hyp.T_nonI
  by_contra hesc
  have hz_esc : (z : G) ∈
      OddOrder.GroupTheory.escapingCentralizerSet hyp.T (honestTypeP2ASet hyp.T) :=
    ⟨hmemA, hesc⟩
  rw [escaping_honestTypeP2ASet_eq_empty _hG
    (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional _hG) hyp.T_maximal hTP] at hz_esc
  exact Set.notMem_empty _ hz_esc

/-- **No conjugate of `P` fits inside `T`** ((13.4) structural gate, issue 9013 追記⁶ (c),
discharged type-free post-9073): `|P| = p^q` (13.2.b) exceeds the `p`-part `p = |W₂|` of
`|T| = |Q|·(v·d)·p` (`card_T_eq`): `p ∤ |Q|` because `Q = T_F` is a Hall subgroup of `T` whose
index `(v·d)·p` is divisible by `p`, and `p ∤ v·d = |V|` because `V ⋊ W₂` is a Frobenius group
(`|V| ≡ 1 (mod p)`; trivially if `V = ⊥`).  So `v_p(|T|) = 1 < q`, and a conjugate `P^w ≤ T`
would give `p^q ∣ |T|` by Lagrange — impossible. -/
theorem P_conj_forall_not_le_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∀ w : G, ¬ ∀ r ∈ hyp.P, w⁻¹ * r * w ∈ hyp.T := by
  intro w hall
  haveI := hyp.finiteG
  -- `|P| = p^q` (13.2.b).
  obtain ⟨-, -, -, hPcard, -, -⟩ := basic_structure hG hyp
  -- The conjugate `P^w = (conj w⁻¹)(P)` lies in `T` and has order `p^q`; Lagrange.
  set f : G →* G := (MulAut.conj w⁻¹).toMonoidHom with hf
  have hle : hyp.P.map f ≤ hyp.T := by
    rintro - ⟨r, hr, rfl⟩
    simpa [hf, MulAut.conj_apply] using hall r hr
  have hcardmap : Nat.card ↥(hyp.P.map f) = hyp.p ^ hyp.q := by
    rw [← hPcard]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective hyp.P f (MulAut.conj w⁻¹).injective).toEquiv).symm
  have hdvd : hyp.p ^ hyp.q ∣ Nat.card ↥hyp.T := by
    rw [← hcardmap]
    exact Subgroup.card_dvd_of_le hle
  rw [hyp.card_T_eq hG] at hdvd
  -- `p ∤ v·d = |V|`: Frobenius `V ⋊ W₂` gives `|V| ≡ 1 (mod p)` (trivial if `V = ⊥`).
  have hpV : ¬ hyp.p ∣ hyp.v * hyp.d := by
    rw [← hyp.card_V_eq_vd]
    by_cases hVbot : hyp.V = ⊥
    · rw [hVbot, Subgroup.card_bot]
      intro h
      exact hyp.p_prime.one_lt.ne' (Nat.dvd_one.mp h)
    · obtain ⟨tpd, htpdU, htpdW1, -⟩ := reconciled_typePData_T hG hyp
      have hUne : tpd.U ≠ ⊥ := by rw [htpdU]; exact hVbot
      have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd hUne
      rw [htpdU, htpdW1] at hfrob
      have hmod := hfrob.card_kernel_modEq_one
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (le_sup_left : hyp.V ≤ hyp.V ⊔ hyp.W2)).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (le_sup_right : hyp.W2 ≤ hyp.V ⊔ hyp.W2)).toEquiv,
          ← hyp.p_eq_card_W2] at hmod
      intro hpdvd
      have hV1 : 1 ≤ Nat.card ↥hyp.V := Nat.card_pos
      have hsub : hyp.p ∣ Nat.card ↥hyp.V - 1 := (Nat.modEq_iff_dvd' hV1).mp hmod.symm
      have hone : hyp.p ∣ 1 := by
        have := Nat.dvd_sub hpdvd hsub
        rwa [Nat.sub_sub_self hV1] at this
      exact hyp.p_prime.one_lt.ne' (Nat.dvd_one.mp hone)
  -- `p ∤ |Q|`: `Q = T_F` is Hall in `T` and `p` divides its index `(v·d)·p`.
  have hpQ : ¬ hyp.p ∣ Nat.card ↥hyp.Q := by
    have hQ_le_T : hyp.Q ≤ hyp.T := hyp.Q_eq_TF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.T
    rw [← hyp.Q_eq_TF] at hHall
    have hcard_eq : Nat.card ↥(hyp.Q.subgroupOf hyp.T) = Nat.card ↥hyp.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_T).toEquiv
    have hcopIdx : Nat.Coprime (Nat.card ↥hyp.Q) (hyp.Q.subgroupOf hyp.T).index :=
      hcard_eq ▸ OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
    -- `index · |Q| = |T| = |Q|·(v·d)·p ⟹ index = (v·d)·p`, so `p ∣ index`.
    have hidx : (hyp.Q.subgroupOf hyp.T).index * Nat.card ↥hyp.Q
        = Nat.card ↥hyp.Q * (hyp.v * hyp.d) * hyp.p := by
      rw [← hyp.card_T_eq hG, ← hcard_eq]
      exact Subgroup.index_mul_card _
    have hQpos : 0 < Nat.card ↥hyp.Q := Nat.card_pos
    have hidx' : (hyp.Q.subgroupOf hyp.T).index = hyp.v * hyp.d * hyp.p := by
      have h : (hyp.Q.subgroupOf hyp.T).index * Nat.card ↥hyp.Q
          = hyp.v * hyp.d * hyp.p * Nat.card ↥hyp.Q := by
        rw [hidx]; ring
      exact Nat.eq_of_mul_eq_mul_right hQpos h
    intro hpdvd
    have hpidx : hyp.p ∣ (hyp.Q.subgroupOf hyp.T).index := by
      rw [hidx']; exact dvd_mul_left hyp.p (hyp.v * hyp.d)
    have hp1 := Nat.dvd_gcd hpdvd hpidx
    rw [Nat.Coprime.gcd_eq_one hcopIdx] at hp1
    exact hyp.p_prime.one_lt.ne' (Nat.dvd_one.mp hp1)
  -- `p^q ∣ (|Q|·(v·d))·p` with `p` prime to `|Q|·(v·d)` forces `p ∣ |Q|·(v·d)` (`q ≥ 2`) — absurd.
  have hK : ¬ hyp.p ∣ Nat.card ↥hyp.Q * (hyp.v * hyp.d) := by
    intro h
    rcases (Nat.Prime.dvd_mul hyp.p_prime).mp h with h' | h'
    exacts [hpQ h', hpV h']
  have hpow : hyp.p ^ hyp.q = hyp.p ^ (hyp.q - 1) * hyp.p := by
    rw [← pow_succ]
    congr 1
    have := hyp.q_prime.two_le
    omega
  rw [hpow] at hdvd
  have hcancel : hyp.p ^ (hyp.q - 1) ∣ Nat.card ↥hyp.Q * (hyp.v * hyp.d) :=
    (Nat.mul_dvd_mul_iff_right hyp.p_prime.pos).mp hdvd
  have hq1 : hyp.q - 1 ≠ 0 := by
    have := hyp.q_prime.two_le
    omega
  exact hK (dvd_trans (dvd_pow_self hyp.p hq1) hcancel)

open scoped FiniteInduce in
/-- **(13.3.b,c)-for-`T` θ-package** ((13.4) character gate, issue 9013 追記⁶ (a)+(b)): if the
(13.4) conclusion fails, then by (13.3.b) applied to `T` the family `𝒯` contains an irreducible
character `θ` induced from a linear character of `K = QD`, and (13.3.c) for `T` writes the
`τ₁`-image of the distinguished `ν`-row sum as a signed `η`-row.  Packaged in the exact form the
(13.4) contradiction consumes:

* `θT − ν_r` is `K^#`-supported ((13.3.a) for `T`: both are `K`-induced of equal degree `vp`);
* its Dade image (`τ = Ind_T^G` by (13.2.e) for `T`) is `θ° − δ'·∑ⱼ η_{rj}` ((13.3.c) for `T`,
  `τ₁`-additivity);
* `θ° = θ^{τ₁}` is orthogonal to the `η`-grid and to `λ^{τ₁}` ((4.1) + (5.3.b) pairwise
  orthogonality of `η_{ij}`, `λ^{τ₁}`, `θ^{τ₁}`). -/
theorem tSide_theta_package_of_not_caseB [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp)
    (_hne : ¬ (hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p)) :
    ∃ (θT : ClassFunction ↥hyp.T ℂ) (r : Fin hyp.q) (δ' : ℤ) (θG : ClassFunction G ℂ),
      (δ' = 1 ∨ δ' = -1) ∧
      ((θT - ∑ j : Fin hyp.p, hyp.nu r j).support ⊆
        {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1}) ∧
      (ClassFunction.induce hyp.T (θT - ∑ j : Fin hyp.p, hyp.nu r j)
        = θG - (δ' : ℂ) • ∑ j : Fin hyp.p, hyp.eta r j) ∧
      (∀ (i : Fin hyp.q) (j : Fin hyp.p), ClassFunction.inner (hyp.eta i j) θG = 0) ∧
      ClassFunction.inner (chars.tau1S chars.lambda) θG = 0 := by
  sorry

open scoped FiniteInduce in
/-- **Peterfalvi (13.4)**: if `S` contains a degree-`u q` character induced
from a linear character of `P C`, then case (9.7.b) holds for `T`, with
`D = 1` and `v = (q^p - 1) / (q - 1)`.

The third conjunct `|Q| = q^p` is the kernel-order component of "case (9.7.b) holds for `T`"
(the (9.7.b) field model identifies `Q̄` with a field of cardinality `q^p`); it is what the
(13.10) counting reads off ((13.10.3) computes `|Q^#|/|T| = (q^p−1)/(pq^p v)`).

**Proof structure** (issue 9013 追記⁶, textbook 04.15 mmd:49-58): by contradiction.  The T-side
θ-package (`tSide_theta_package_of_not_caseB`, (13.3.b,c)-for-`T`) supplies `β = θ − ν_r` with
`K^#`-support and Dade image `θ° − δ'·∑ⱼ η_{rj}`; the carried S-side (13.3) data give
`α = λ − μ_{j₀}` with `H^#`-support (`H ⊴ S`, equal degrees) and Dade image `λ° − δ·∑ᵢ η_{i1}`.
`(H^#)^G ∩ (K^#)^G = ∅` (`P` centralizes `H`-points, the `K^#`-centralizers lie in `T`, and no
conjugate of `P` fits in `T`), so `(α^τ, β^τ) = 0` — but the bilinear expansion leaves the shared
grid entry `δδ'·⟨η_{r1}, η_{r1}⟩ = ±1`.  Contradiction (`eta_cross_expansion_ne_zero`). -/
theorem lambda_forces_T_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  haveI := hyp.finiteG
  by_contra hne
  -- T-side θ-package from the (13.3.b,c)-for-`T` gate.
  obtain ⟨θT, r, δ', θG, hδ', hβsupp, hβform, hηθ, hLamTheta⟩ :=
    tSide_theta_package_of_not_caseB hG chars hne
  -- S-side (13.3) data: `λ = Ind thetaL` and the distinguished `μ`-column `μ_{j₀} = Ind θlin` with
  -- `τ₁`-image `δ·∑ᵢ η_{i1}`.
  obtain ⟨thetaL, hthetaLirr, hthetaL1, hlamEq, -⟩ := chars.lambda_induced_from_PC_linear
  obtain ⟨j₀, δ, θlin, hδ, hθlinirr, hθlin1, hμeq, hμtau⟩ := chars.mu_col_tau1_eta_col_one
  -- `α = λ − μ_{j₀}` is supported on `H^#` (`H ⊴ S`; both terms `H`-induced of equal degree).
  have hαsupp : (chars.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀).support ⊆
      {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1} := by
    intro s hs
    have hs0 : (chars.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀) s ≠ 0 := hs
    refine ⟨?_, ?_⟩
    · by_contra hsH
      apply hs0
      have hsH' : s ∉ hyp.H.subgroupOf hyp.S := fun h => hsH (Subgroup.mem_subgroupOf.mp h)
      rw [ClassFunction.sub_apply, hlamEq, hμeq,
        ClassFunction.induce_eq_zero_of_not_mem_normal _ hsH',
        ClassFunction.induce_eq_zero_of_not_mem_normal _ hsH', sub_zero]
    · rintro rfl
      apply hs0
      rw [ClassFunction.sub_apply, hlamEq, hμeq, ClassFunction.induce_apply_one,
        ClassFunction.induce_apply_one, hthetaL1, hθlin1, sub_self]
  -- The conjugate closures of `H^#` and `K^#` are disjoint.
  have hdisj := disjoint_conjugatesIntoSet_of_centralizer
    (A_M := {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1})
    (A_N := {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1})
    (fun _y hy => hyp.P_le_centralizer_of_mem_H hG hy.1)
    (fun z hz => QD_sharp_centralizer_le_T hG hyp z hz.1 hz.2)
    (P_conj_forall_not_le_T hG hyp)
  -- Hence `(α^τ, β^τ) = 0`.
  have h0 : ClassFunction.inner
      (ClassFunction.induce hyp.S (chars.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀))
      (ClassFunction.induce hyp.T (θT - ∑ j : Fin hyp.p, hyp.nu r j)) = 0 :=
    inner_induce_induce_eq_zero_of_disjoint hαsupp hβsupp hdisj
  -- Rewrite `α^τ = λ° − δ·∑ᵢ η_{i1}` ((13.2.e)+τ₁-additivity + the (13.3.c) column formula).
  have hαform : ClassFunction.induce hyp.S (chars.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀)
      = chars.tau1S chars.lambda
        - (δ : ℂ) • ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ := by
    conv_lhs => rw [hlamEq, hμeq]
    rw [← chars.tau1S_apply_induce_sub thetaL θlin hthetaLirr hθlinirr, map_sub, ← hlamEq, ← hμeq, hμtau]
  -- The `λ°`-side grid orthogonality, flipped to the expansion brick's slot order.
  have hLamEta : ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (chars.tau1S chars.lambda) (hyp.eta i j) = 0 := by
    intro i j
    have h := chars.tau1S_induce_inner_eta i j thetaL hthetaLirr
      (hlamEq ▸ chars.lambda_irreducible)
    rw [← hlamEq] at h
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h, star_zero]
  -- The bilinear expansion is `δ·δ' ≠ 0` — contradiction.
  rw [hαform, hβform] at h0
  exact eta_cross_expansion_ne_zero hyp.eta (fun i k j l => hyp.eta_orthonormal i k j l)
    (chars.tau1S chars.lambda) θG r ⟨1, hyp.p_prime.one_lt⟩ hLamEta hηθ hLamTheta hδ hδ' h0

open scoped Classical in
/-- `|K^#| = |K| − 1`, `Finset` form. -/
theorem card_sharp_toFinset [Fintype G] (K : Subgroup G) :
    (Set.toFinite (sharpSubgroup K)).toFinset.card = Nat.card ↥K - 1 := by
  classical
  have h : (Set.toFinite (sharpSubgroup K)).toFinset
      = (Finset.univ.filter (· ∈ K)).erase 1 := by
    ext x
    rw [Set.Finite.mem_toFinset, Finset.mem_erase, Finset.mem_filter]
    show x ∈ (K : Set G) \ {1} ↔ _
    rw [Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  rw [h, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, K.one_mem⟩)]
  congr 1
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype]

/-- **Peterfalvi (13.10.3), ℕ form**: `|G| = 1 + |G₀| + [G:S]·|H^#| + [G:T]·|Q^#|` — the
`f = 1` instance of the four-piece split. -/
theorem Hypothesis.card_univ_split [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) (hvd : hyp.v * hyp.d ≠ 1) :
    Nat.card G = 1 + hyp.G0Finset.card
      + hyp.S.index * (Nat.card ↥hyp.H - 1) + hyp.T.index * (Nat.card ↥hyp.Q - 1) := by
  have h := hyp.sum_univ_split hG (fun _ => (1 : ℕ)) (fun _ _ => rfl) hcardQ hvd
  simp only [← Finset.card_eq_sum_ones, Finset.card_univ, smul_eq_mul,
    card_sharp_toFinset] at h
  rw [Nat.card_eq_fintype_card]
  exact h

/-- **`T` normalizes `Q^#`** — the `T`-side mirror of `S_normalizes_H_sharp`, via
`normalizer_Q_eq_T`. -/
theorem T_normalizes_Q_sharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ (l : hyp.T) ⦃a : G⦄, a ∈ OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) →
      (l : G) * a * (l : G)⁻¹ ∈ OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) := by
  have hnorm : Subgroup.normalizer (hyp.Q : Set G) = hyp.T := normalizer_Q_eq_T hG hyp
  intro l a ha
  rw [OddOrder.Peterfalvi.S04.mem_sharp] at ha ⊢
  obtain ⟨haQ, ha1⟩ := ha
  have hlnorm : (l : G) ∈ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hnorm]; exact l.2
  refine ⟨(Subgroup.mem_set_normalizer_iff.mp hlnorm a).mp haQ, ?_⟩
  intro heq
  refine ha1 ?_
  calc a = (l : G)⁻¹ * ((l : G) * a * (l : G)⁻¹) * (l : G) := by group
    _ = 1 := by rw [heq]; group

/-- **The (13.8)-for-`T` Dade hypothesis for the TI-subset `(T, Q^#)`** — the `T`-side mirror of
`H_sharp_dadeHypothesis`, from the proven `Q_sharp_isTISubset` (type V excluded by `vd ≠ 1`).
The foundation of the `T`-side (13.5) ρ-machinery consumed by `exists_caseB_data_eta10_T`. -/
noncomputable def Q_sharp_dadeHypothesis [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S04.Hypothesis G (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T := by
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  refine OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset ?_ ?_ (T_normalizes_Q_sharp hG hyp)
    (Q_sharp_isTISubset hG hyp hvd)
  · intro x hx
    exact OddOrder.Peterfalvi.S04.mem_sharp.mpr
      ⟨Set.mem_univ x, (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).2⟩
  · intro x hx
    exact hQT (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).1

/-- The `(T, Q^#)` Dade datum is conjugation-invariant (`H(a) = ⊥` for the TI construction). -/
theorem Q_sharp_hconj [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    (Q_sharp_dadeHypothesis hG hyp hvd).HConjInvariant :=
  OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl)

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The (7.1) ρ-hypothesis for `(T, Q^#)` — mirror of `H_sharp_hypothesis71`. -/
noncomputable def Q_sharp_hypothesis71 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S09.Hypothesis71 G (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T :=
  { hyp := Q_sharp_dadeHypothesis hG hyp hvd
    τ := ((Q_sharp_dadeHypothesis hG hyp hvd).fullDadeIsometryData
      (Q_sharp_hconj hG hyp hvd)).toDadeIsometryData.toDadeMap
    isDadeMap := ((Q_sharp_dadeHypothesis hG hyp hvd).fullDadeIsometryData
      (Q_sharp_hconj hG hyp hvd)).toDadeIsometryData.isDadeMap
    hConjInvariant := Q_sharp_hconj hG hyp hvd }

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The (7.6) coherent-family datum for `(T, Q^#)` — mirror of `H_sharp_hypothesis76`; the
datum on which the `T`-side (13.5.a) point formula is read off. -/
noncomputable def Q_sharp_hypothesis76 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S09.Hypothesis76 G
      (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T := by
  refine OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDade (Q_sharp_hypothesis71 hG hyp hvd)
    (((Q_sharp_dadeHypothesis hG hyp hvd).fullDadeIsometryData
      (Q_sharp_hconj hG hyp hvd)).toDadeIsometryData.isDadeIsometry) hyp.Q ?_ ?_ rfl
  · rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  · intro l h hh
    have := T_normalizes_Q_sharp hG hyp
    -- `T` normalizes `Q` itself (not just `Q^#`): via the normalizer identity.
    have hnorm : Subgroup.normalizer (hyp.Q : Set G) = hyp.T := normalizer_Q_eq_T hG hyp
    have hlnorm : (l : G) ∈ Subgroup.normalizer (hyp.Q : Set G) := by
      rw [hnorm]; exact l.2
    exact (Subgroup.mem_set_normalizer_iff.mp hlnorm h).mp hh

/-- **`G₀` is cyclic-closed**: closed under `x ↦ x^k` for `k` coprime to `|G|` — the hypothesis
shape of the Galois integrality `exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed` (and of
[Is] Lemma 3.14) that makes the (13.10) atoms `slam`/`seta` rational.  The coprime power is
undone by a further coprime power (Euler), so `x^k = 1` forces `x = 1`, and a conjugate of
`H^#`/`Q^#` hitting `x^k` pulls back to one hitting `x` (subgroups are power-closed). -/
theorem Hypothesis.G0Finset_cyclicClosed [Finite G] (hyp : Hypothesis (G := G)) :
    ∀ x ∈ hyp.G0Finset, ∀ k : ℕ, k.Coprime (Nat.card G) → x ^ k ∈ hyp.G0Finset := by
  intro x hx k hk
  rw [Hypothesis.G0Finset, Set.Finite.mem_toFinset] at hx ⊢
  obtain ⟨hx1, hxH, hxQ⟩ := (hyp.mem_G0_iff x).mp hx
  -- Euler round-trip: `(x^k)^(k^(φ(|G|)−1)) = x`.
  have hN0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  set t := (Nat.card G).totient with htdef
  have ht1 : 1 ≤ t := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)
  set m : ℕ := k ^ (t - 1) with hmdef
  have hround : (x ^ k) ^ m = x := by
    rw [hmdef, ← pow_mul]
    have hkt : k * k ^ (t - 1) = k ^ t := by rw [← pow_succ']; congr 1; omega
    rw [hkt]
    have hord : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
    have hmod : k ^ t ≡ 1 [MOD orderOf x] := (Nat.ModEq.pow_totient hk).of_dvd hord
    rw [pow_eq_pow_iff_modEq.mpr hmod, pow_one]
  -- Conjugates of `K^#` hitting `x^k` pull back to `x`.
  have hpull : ∀ K : Subgroup G, x ^ k ∈ conjClassSet (sharpSubgroup K) →
      x ∈ conjClassSet (sharpSubgroup K) := by
    intro K hmem
    obtain ⟨a, ⟨haK, ha1⟩, g, hg⟩ := mem_conjClassSet.mp hmem
    refine mem_conjClassSet.mpr ⟨a ^ m, ⟨?_, ?_⟩, g, ?_⟩
    · exact SetLike.mem_coe.mpr (pow_mem (SetLike.mem_coe.mp haK) m)
    · intro h1
      rw [Set.mem_singleton_iff] at h1
      refine hx1 ?_
      rw [← hround, ← hg, conj_pow, h1, mul_one, mul_inv_cancel]
    · rw [← conj_pow, hg, hround]
  refine (hyp.mem_G0_iff _).mpr ⟨?_, fun h => hxH (hpull _ h), fun h => hxQ (hpull _ h)⟩
  intro h1
  refine hx1 ?_
  rw [← hround, h1, one_pow]

/-- `|T'| = |Q|·(vd)` — the `T`-side derived-subgroup order decomposition
(`derived_complement` of the reconciled type-`P` datum). -/
theorem Hypothesis.card_deriv_T_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥(derivedInG hyp.T) = Nat.card ↥hyp.Q * (hyp.v * hyp.d) := by
  obtain ⟨tpd, hU, -, -⟩ := reconciled_typePData_T hG hyp
  have h2 := tpd.derived_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.H_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.U_le).toEquiv, tpd.H_eq, ← hyp.Q_eq_TF,
    hU, hyp.card_V_eq_vd] at h2
  exact h2.symm

open scoped FiniteInduce in
/-- **Global Parseval four-piece split** for a norm-`1` class function (the shared spine of the
Peterfalvi (13.10.1)/(13.10.2) estimates):

  `|G| = ‖φ(1)‖² + ∑_{G₀}‖φ‖² + [G:S]·∑_{H^#}‖φ‖² + [G:T]·∑_{Q^#}‖φ‖²`.

The total `∑_G ‖φ‖² = |G|·⟨φ,φ⟩ = |G|` (Parseval, `sum_normSq_eq_card_mul_inner`), split by the
four-piece decomposition `sum_univ_split` (the summand `‖φ(·)‖²` is conjugation-invariant since
`φ` is a class function). -/
theorem Hypothesis.global_normSq_split [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (φ : ClassFunction G ℂ)
    (hn : ClassFunction.inner φ φ = 1)
    (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) (hvd : hyp.v * hyp.d ≠ 1) :
    (Nat.card G : ℝ)
      = ‖φ 1‖ ^ 2 + (∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2)
        + hyp.S.index • (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖φ x‖ ^ 2)
        + hyp.T.index • (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖φ x‖ ^ 2) := by
  have hsplit := hyp.sum_univ_split hG (fun x => ‖φ x‖ ^ 2)
    (fun g x => by
      show ‖φ (g * x * g⁻¹)‖ ^ 2 = ‖φ x‖ ^ 2
      rw [ClassFunction.conj_eq φ x g]) hcardQ hvd
  have htotal : ((∑ x : G, ‖φ x‖ ^ 2 : ℝ) : ℂ) = (Nat.card G : ℂ) := by
    rw [sum_normSq_eq_card_mul_inner, hn, mul_one]
  have htotalR : ∑ x : G, ‖φ x‖ ^ 2 = (Nat.card G : ℝ) := by exact_mod_cast htotal
  rw [← htotalR, hsplit]

end CountingLayer

end OddOrder.Peterfalvi.S15
