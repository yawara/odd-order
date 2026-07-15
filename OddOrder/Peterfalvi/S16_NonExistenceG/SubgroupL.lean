import OddOrder.Peterfalvi.S16_NonExistenceG.TTypeII
import OddOrder.Peterfalvi.S15_CaseAContradiction

/-!
# Peterfalvi §14: the subgroup L and the T/S case-B data

The post-(14.9) construction of `L`, the T- and S-side case-B packages, and their structural
consequences.  The Type-II proof for `T` lives in `TTypeII`.
-/

namespace OddOrder.Peterfalvi.S16
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped BigOperators

variable {G : Type*} [Group G]

/-- **(14.7) `hPU_disj` input**: `P ∩ U = 1`.  Since `P` is elementary abelian it
centralizes itself, so `P ⊓ U ≤ U ⊓ C_G(P) = C = 1` by (13.12) `c = 1`.  Cites the
(sorried) §13 producers `basic_structure` and `c_eq_one`. -/
theorem P_inf_U_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.P ⊓ hyp.base.U = ⊥ := by
  obtain ⟨data, _⟩ := OddOrder.Peterfalvi.S15.basic_structure hG hyp.base
  haveI : IsMulCommutative ↥hyp.base.P :=
    IsMulCommutative.of_comm data.P_elementaryAbelian.comm
  have hP_le_cent : hyp.base.P ≤ Subgroup.centralizer (hyp.base.P : Set G) :=
    Subgroup.le_centralizer (H := hyp.base.P)
  have hC_bot : hyp.base.C = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [← hyp.base.c_eq_card_C, OddOrder.Peterfalvi.S15.c_eq_one hG hyp.base]
  rw [eq_bot_iff, ← hC_bot, hyp.base.C_eq]
  exact le_inf inf_le_right (inf_le_left.trans hP_le_cent)

/-- **Peterfalvi (14.3)**: a type-I maximal subgroup `L` over `N_G(U)` exists.  Constructed by
citing the (14.5)-threaded `S15.typeII_overNormalizer_frobenius` for the
type-I-over-normalizer Frobenius data (`S` is type II by `basic_structure` + (14.1) `q < p`);
the complement order `|E| = p q` is a field `complement_card_eq_pq` of that data ((14.5) —
the small (13.17.c) alternative `E = W₁` is excluded there via the (13.19.c) dichotomy under
`q < p` and `N_G(U) ⊄ S`, the latter supplied here through the L~S rule-out chain
`P_inf_U_eq_bot` → `coprime_card_U_card_P_of_disjoint` → `exists_conj_typeP_U_of_coprime` →
`not_normalizer_U_le_S`).  The (14.3.b) Dade data is not carried — it is unused by the §14
non-existence argument, so the carrier holds exactly the structural data the proof consumes.
Placed here (ahead of the (14.4)--(14.16) lemmas) so the mid-file numeric lemmas can construct
an `LHypothesis` to feed the S-side case-(9.7.b) data `caseB_for_S`. -/
theorem exists_LHypothesis [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    Nonempty (LHypothesis hyp) := by
  obtain ⟨bdata, _⟩ := OddOrder.Peterfalvi.S15.basic_structure _hG hyp.base
  have hSII : IsTypeII hyp.base.S := bdata.q_lt_p_forces_typeII hyp.q_lt_p
  have hTII : IsTypeII hyp.base.T := T_typeII _hG hnoV hncH0C hyp
  obtain ⟨tdata⟩ := hSII
  have hNUS : ¬ Subgroup.normalizer (hyp.base.U : Set G) ≤ hyp.base.S :=
    OddOrder.Peterfalvi.S15.not_normalizer_U_le_S _hG hyp.base tdata
      (OddOrder.Peterfalvi.S15.exists_conj_typeP_U_of_coprime _hG hyp.base tdata
        (OddOrder.Peterfalvi.S15.coprime_card_U_card_P_of_disjoint hyp.base tdata
          (P_inf_U_eq_bot _hG hyp)))
  have hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.base.T :=
    ((OddOrder.BG.Ch4.S16.proposition_type_classification _hG hyp.base.T_maximal).2.1).mp hTII
  obtain ⟨typeI_data, _, _⟩ :=
    OddOrder.Peterfalvi.S15.typeII_overNormalizer_frobenius _hG hnoV hyp.base ⟨tdata⟩ hTII hT2
      hyp.q_lt_p hNUS (pins := hyp.nuGridSupply)
  exact ⟨⟨typeI_data.L, typeI_data.H, typeI_data.L_maximal, typeI_data.normalizer_U_le_L,
    typeI_data.H_eq_LF, typeI_data, rfl, rfl, typeI_data.complement_card_eq_pq⟩⟩

/-- Carrier for the case-(9.7.b) conclusion applied to `T` in Peterfalvi
(14.4). -/
structure CaseBForTData (hyp : Hypothesis (G := G)) where
  caseB_formula : Prop
  caseB_holds : caseB_formula
  D_eq_bot : hyp.base.D = ⊥
  v_eq : hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1)

namespace CaseBForTData

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
odd. -/
theorem v_odd {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    Odd hyp.base.v := by
  rw [data.v_eq]
  exact hyp.tSide_cyclotomic_quotient_odd

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
positive. -/
theorem v_pos {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    0 < hyp.base.v :=
  Odd.pos data.v_odd

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
nonzero. -/
theorem v_ne_zero {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    hyp.base.v ≠ 0 :=
  ne_of_gt data.v_pos

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
coprime to `q - 1`. -/
theorem v_coprime_q_sub_one {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    Nat.Coprime hyp.base.v (hyp.base.q - 1) := by
  rw [data.v_eq]
  exact hyp.tSide_cyclotomic_quotient_coprime

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, every
positive divisor of `v` is `1 mod p`. -/
theorem divisor_modEq_one {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    ∀ x : ℕ, x ≠ 0 → x ∣ hyp.base.v → x ≡ 1 [MOD hyp.base.p] := by
  intro x hx hxdvd
  apply hyp.tSide_cyclotomic_quotient_divisor_modEq_one x hx
  rw [data.v_eq] at hxdvd
  exact hxdvd

end CaseBForTData

/-- **Peterfalvi (14.4)**: case (9.7.b) holds for `T`, and `v = (q^p - 1) / (q - 1)`.  The numeric
content (`D = ⊥`, `v` full) is the named §13 obligation `T_side_caseB_facts`; the case-(9.7.b)
proposition is carried trivially (no consumer reads it). -/
theorem caseB_for_T [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧
        hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) :=
  ⟨⟨True, trivial, (T_side_caseB_facts _hG hyp).1, (T_side_caseB_facts _hG hyp).2⟩,
    trivial, (T_side_caseB_facts _hG hyp).2⟩

/-- **Peterfalvi (14.5)**: there is an element `y ∈ Q` such that `L = H ⋊ (W₁ W₂^y)`.
The downstream-relevant content of the split is that the conjugate `W₂^y` lands in the
Frobenius complement of `L` (the complement `W₁W₂^y`); this is the concrete form consumed by
`u_modEq_one_mod_p_of_LHypothesis` (the (14.7) fixed-point-free value argument) and, through it,
the part-(14.2.b) normalizer input `W₂^y ≤ N_G(U)`.  Its proof rules out the alternative
`L = H ⋊ W₁` of (13.17.c) via (13.19.c1)/(13.2.a). -/
theorem exists_y_L_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) :
    ∃ y ∈ hyp.base.Q, (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Ldata.typeI_data.frobenius.complement.map (Ldata.typeI_data.L).subtype :=
  Ldata.typeI_data.exists_y_W2_conj_le_complement

/-- Carrier for the case-(9.7.b) conclusion applied to `S` in Peterfalvi
(14.6). -/
structure CaseBForSData (hyp : Hypothesis (G := G)) where
  caseB_formula : Prop
  caseB_holds : caseB_formula
  order_u_eq_of_p_modEq_one :
    hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.q * (hyp.base.p - 1))
  order_u_eq_of_not_modEq_one :
    ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)
  U_rank_obstruction : Prop
  U_rank_obstruction_holds : U_rank_obstruction

namespace CaseBForSData

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, the
`p ≡ 1 mod q` branch gives the divided cyclotomic value of `u`. -/
theorem u_eq_of_p_modEq_one {hyp : Hypothesis (G := G)} (data : CaseBForSData hyp) :
    hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.q * (hyp.base.p - 1)) :=
  data.order_u_eq_of_p_modEq_one

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, the
non-`p ≡ 1 mod q` branch gives the full cyclotomic value of `u`. -/
theorem u_eq_of_not_modEq_one {hyp : Hypothesis (G := G)}
    (data : CaseBForSData hyp) :
    ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
  data.order_u_eq_of_not_modEq_one

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, `u` is at
most the full cyclotomic quotient.  The `p ≡ 1 mod q` branch divides that
quotient by the additional factor `q`; the other branch is equality. -/
theorem u_le_full_cyclotomic {hyp : Hypothesis (G := G)}
    (data : CaseBForSData hyp) :
    hyp.base.u ≤ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  by_cases hmod : hyp.base.p ≡ 1 [MOD hyp.base.q]
  · rw [data.u_eq_of_p_modEq_one hmod]
    have hp1_pos : 0 < hyp.base.p - 1 := by
      have hp2 : 2 ≤ hyp.base.p := hyp.base.p_prime.two_le
      omega
    have hden_le : hyp.base.p - 1 ≤ hyp.base.q * (hyp.base.p - 1) := by
      have hqpos : 1 ≤ hyp.base.q := hyp.base.q_prime.one_le
      nlinarith [Nat.mul_le_mul_right (hyp.base.p - 1) hqpos]
    exact Nat.div_le_div_left hden_le hp1_pos
  · rw [data.u_eq_of_not_modEq_one hmod]

end CaseBForSData

/-- **Peterfalvi (14.6)**: case (9.7.b) holds for `S`.

The Clifford dichotomy supplies either case (9.7.a) or an actual `CliffordCaseBData`
certificate.  The case-A branch is impossible by the completed type-I-over-normalizer
contradiction, using the `(13.13)` parameters and `c = 1`.  In the remaining branch,
`caseB_order_u` supplies the two alternatives for the order `u`; the qualitative field stores
the genuine nonempty case-B certificate rather than an opaque compatibility proposition. -/
theorem caseB_for_S [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) :
    ∃ data : CaseBForSData hyp, data.caseB_formula := by
  classical
  obtain ⟨chief, -⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData _hG
      (hyp.base.toTypesIIIIIIVSetupS _hG)
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy _hG
      (hyp.base.mkSection11CharacterDataS _hG chief) with hA | hB
  · obtain ⟨caseA⟩ := hA
    obtain ⟨hq, hu⟩ := OddOrder.Peterfalvi.S15.caseA_parameters _hG hyp.base caseA
    exact (OddOrder.Peterfalvi.S15.caseA_false_of_parameters_and_typeIOverNormalizerData
      _hG hyp.base caseA (OddOrder.Peterfalvi.S15.c_eq_one _hG hyp.base) hq hu
      Ldata.typeI_data).elim
  · obtain ⟨caseB⟩ := hB
    let caseB_formula : Prop := Nonempty
      (OddOrder.Peterfalvi.S11.CliffordCaseBData
        (hyp.base.mkSection11CharacterDataS _hG chief))
    have hcaseB : caseB_formula := ⟨caseB⟩
    obtain ⟨hu_mod, hu_not_mod⟩ :=
      OddOrder.Peterfalvi.S15.caseB_order_u _hG hyp.base caseB
    exact ⟨⟨caseB_formula, hcaseB, hu_mod, hu_not_mod, True, trivial⟩, hcaseB⟩

/-- Over `ℕ`, the geometric-sum identity `(p − 1) · ∑_{i<q} pⁱ = p^q − 1`. -/
private theorem pred_mul_geomSum (p q : ℕ) (hp : 1 ≤ p) :
    (p - 1) * ∑ i ∈ Finset.range q, p ^ i = p ^ q - 1 := by
  induction q with
  | zero => simp
  | succ n ih =>
      have hpn : 1 ≤ p ^ n := Nat.one_le_pow _ _ (by omega)
      have hle : p ^ n ≤ p ^ n * p := Nat.le_mul_of_pos_right _ (by omega)
      have key : (p - 1) * p ^ n = p ^ n * p - p ^ n := by
        rw [Nat.sub_mul, one_mul, Nat.mul_comm p (p ^ n)]
      rw [Finset.sum_range_succ, mul_add, ih, key, pow_succ]
      omega

/-- The geometric sum `∑_{i<q} pⁱ` is `≡ q (mod d)` whenever `p ≡ 1 (mod d)`,
since every `pⁱ ≡ 1`. -/
private theorem geomSum_modEq_card {p d : ℕ} (hpd : p ≡ 1 [MOD d]) (q : ℕ) :
    ∑ i ∈ Finset.range q, p ^ i ≡ q [MOD d] := by
  induction q with
  | zero => simp [Nat.ModEq]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hpow : p ^ n ≡ 1 [MOD d] := by simpa using hpd.pow n
      exact Nat.ModEq.add ih hpow

/-- **Peterfalvi (14.2)(a)** arithmetic core: when `q ∤ (p − 1)`, the cyclotomic
quotient `(p^q − 1)/(p − 1)` is prime to `p − 1`.  In (14.7) the hypothesis
`q ∤ (p − 1)` is `p ≢ 1 (mod q)`, which holds once `u` takes its full cyclotomic
value.  The quotient equals `∑_{i<q} pⁱ ≡ q (mod p − 1)`, so it is coprime to
`p − 1` exactly when `q` is, and `q` prime with `q ∤ (p − 1)` gives that.  This
discharges the `cyclotomic_coprime` field of `FieldNormalizerData`. -/
theorem cyclotomic_quotient_coprime_of_not_dvd {p q : ℕ} (hp : 2 ≤ p)
    (hq : q.Prime) (hnd : ¬ q ∣ (p - 1)) :
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) := by
  have hpd : p ≡ 1 [MOD (p - 1)] :=
    ((Nat.modEq_iff_dvd' (by omega : (1 : ℕ) ≤ p)).mpr (dvd_refl (p - 1))).symm
  have hdiv : (p ^ q - 1) / (p - 1) = ∑ i ∈ Finset.range q, p ^ i := by
    rw [← pred_mul_geomSum p q (by omega),
      Nat.mul_div_cancel_left _ (show 0 < p - 1 by omega)]
  have hmod : (∑ i ∈ Finset.range q, p ^ i) % (p - 1) = q % (p - 1) :=
    geomSum_modEq_card hpd q
  have hcoq : Nat.Coprime q (p - 1) := (Nat.Prime.coprime_iff_not_dvd hq).mpr hnd
  have hgcd : Nat.gcd (p - 1) (∑ i ∈ Finset.range q, p ^ i) = Nat.gcd (p - 1) q := by
    rw [Nat.gcd_rec (p - 1) (∑ i ∈ Finset.range q, p ^ i), Nat.gcd_rec (p - 1) q, hmod]
  rw [hdiv]
  have : Nat.gcd (∑ i ∈ Finset.range q, p ^ i) (p - 1) = 1 := by
    rw [Nat.gcd_comm, hgcd, Nat.gcd_comm]; exact hcoq
  exact this

/-! ### (14.7) σ-bridge: transporting the (14.2)(a) field model into `G`

The hard, *ungated* core of `field_normalizer_of_U_characteristic` is to turn the
abstract field isomorphism of Peterfalvi (14.2)(a) — produced by the Singer machinery
`exists_galoisField_repr` once the §13 inputs `Nat.card P = p^q`, `c = 1` are in hand —
into the concrete `FieldNormalizerData`, i.e. an injective `σ : 𝔽_{p^q} ⋊ U* →* G`
matching `P`, `U`, `W₂`.  The construction is a `SemidirectProduct.lift` of two transport
homomorphisms `fN : 𝔽_{p^q} →* G` (the additive kernel) and `fU : U* →* G` (the
norm-one complement), glued by the (14.2)(a) `U`-equivariance.  These pieces take the
isomorphism as *input*, so they are independent of the §13 character theory that supplies
it (`fieldNormalizerData_of_repr` below). -/

/-- **(14.7) σ-bridge, kernel half.**  Given the Peterfalvi (14.2)(a) additive
isomorphism `e : Additive ↥P ≃+ 𝔽_{p^q}`, this is the transport homomorphism
`P = 𝔽_{p^q} →* G` sending a field point `s` to the group element `e⁻¹ s ∈ P ≤ G`.
It is the kernel (`inl`) factor of the field-normalizer embedding `σ`. -/
noncomputable def fieldNormalizerKernelTransport (hyp : Hypothesis (G := G))
    (e : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q) :
    fieldNormalizerAdditiveGroup hyp →* G :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  { toFun := fun m =>
      ((Additive.toMul (e.symm (Multiplicative.toAdd m)) : ↥hyp.base.P) : G)
    map_one' := by simp
    map_mul' := fun m n => by
      simp [toAdd_mul, map_add, toMul_add] }

@[simp] theorem fieldNormalizerKernelTransport_apply (hyp : Hypothesis (G := G))
    (e : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
    (m : fieldNormalizerAdditiveGroup hyp) :
    fieldNormalizerKernelTransport hyp e m =
      ((Additive.toMul (e.symm (Multiplicative.toAdd m)) : ↥hyp.base.P) : G) :=
  rfl

/-- The kernel transport `fN` is injective: it is a coordinate-wise composition of the
bijections `e.symm`, `Additive.toMul` and the (injective) subgroup inclusion `P ↪ G`. -/
theorem fieldNormalizerKernelTransport_injective (hyp : Hypothesis (G := G))
    (e : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q) :
    Function.Injective (fieldNormalizerKernelTransport hyp e) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro m n hmn
  rw [fieldNormalizerKernelTransport_apply, fieldNormalizerKernelTransport_apply] at hmn
  have h1 : (Additive.toMul (e.symm (Multiplicative.toAdd m)) : ↥hyp.base.P) =
      Additive.toMul (e.symm (Multiplicative.toAdd n)) := Subtype.ext hmn
  have h2 : e.symm (Multiplicative.toAdd m) = e.symm (Multiplicative.toAdd n) :=
    Additive.toMul.injective h1
  have h3 : Multiplicative.toAdd m = Multiplicative.toAdd n := e.symm.injective h2
  exact Multiplicative.toAdd.injective h3

/-- The kernel transport `fN` has image exactly Peterfalvi's additive kernel `P`. -/
theorem fieldNormalizerKernelTransport_range (hyp : Hypothesis (G := G))
    (e : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q) :
    (fieldNormalizerKernelTransport hyp e).range = hyp.base.P := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    rw [fieldNormalizerKernelTransport_apply]
    exact (Additive.toMul (e.symm (Multiplicative.toAdd m))).2
  · intro g hg
    refine ⟨Multiplicative.ofAdd (e (Additive.ofMul (⟨g, hg⟩ : ↥hyp.base.P))), ?_⟩
    rw [fieldNormalizerKernelTransport_apply]
    simp

/-- **(14.7) σ-bridge, complement half.**  Given the Peterfalvi (14.2)(a)
multiplicative character `μ : U →* 𝔽_{p^q}ˣ` realizing `U` as the norm-one units `U*`,
this is the transport homomorphism `U* →* G` inverting `μ` and including back into `G`.
It is the complement (`inr`) factor of the field-normalizer embedding `σ`. -/
noncomputable def fieldNormalizerComplementTransport (hyp : Hypothesis (G := G))
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hμ_inj : Function.Injective μ)
    (hμ_range : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :
    fieldNormalizerNormOneUnits hyp →* G :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  let μ' : ↥hyp.base.U →* ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :=
    { toFun := fun u => ⟨μ u, hμ_range ▸ MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  let eU : ↥hyp.base.U ≃* ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :=
    MulEquiv.ofBijective μ'
      ⟨fun a b h => hμ_inj (congrArg Subtype.val h),
       fun u => by
         obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (by rw [hμ_range]; exact u.2)
         exact ⟨v, Subtype.ext hv⟩⟩
  hyp.base.U.subtype.comp eU.symm.toMonoidHom

/-- The defining property of the complement transport `fU`: each norm-one unit `u*`
has a preimage `u'' ∈ U` whose field character is `u*` and whose image under `fU` is
exactly `u''`.  This packages everything the `SemidirectProduct.lift` compatibility
needs about `fU`. -/
theorem fieldNormalizerComplementTransport_exists (hyp : Hypothesis (G := G))
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hμ_inj : Function.Injective μ)
    (hμ_range : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q)
    (u : fieldNormalizerNormOneUnits hyp) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    ∃ v : ↥hyp.base.U,
      (μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) = (u : (GaloisField hyp.base.p hyp.base.q)ˣ) ∧
        fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range u = (v : G) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  set μ' : ↥hyp.base.U →* ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :=
    { toFun := fun u => ⟨μ u, hμ_range ▸ MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp } with hμ'def
  set eU : ↥hyp.base.U ≃* ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :=
    MulEquiv.ofBijective μ'
      ⟨fun a b h => hμ_inj (congrArg Subtype.val h),
       fun u => by
         obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (by rw [hμ_range]; exact u.2)
         exact ⟨v, Subtype.ext hv⟩⟩ with heUdef
  refine ⟨eU.symm u, ?_, rfl⟩
  have hval : (eU (eU.symm u) : ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q)) = u :=
    eU.apply_symm_apply u
  have : (μ (eU.symm u) : (GaloisField hyp.base.p hyp.base.q)ˣ) = (u : (GaloisField hyp.base.p hyp.base.q)ˣ) := by
    have h1 : (μ' (eU.symm u) : (GaloisField hyp.base.p hyp.base.q)ˣ) =
        (u : (GaloisField hyp.base.p hyp.base.q)ˣ) := congrArg Subtype.val hval
    simpa [hμ'def] using h1
  exact this

/-- The complement transport `fU` is injective. -/
theorem fieldNormalizerComplementTransport_injective (hyp : Hypothesis (G := G))
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hμ_inj : Function.Injective μ)
    (hμ_range : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :
    Function.Injective (fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro a b hab
  obtain ⟨va, hva_mu, hva⟩ := fieldNormalizerComplementTransport_exists hyp μ hμ_inj hμ_range a
  obtain ⟨vb, hvb_mu, hvb⟩ := fieldNormalizerComplementTransport_exists hyp μ hμ_inj hμ_range b
  rw [hva, hvb] at hab
  have hvab : va = vb := Subtype.ext hab
  have : (a : (GaloisField hyp.base.p hyp.base.q)ˣ) = (b : (GaloisField hyp.base.p hyp.base.q)ˣ) := by
    rw [← hva_mu, ← hvb_mu, hvab]
  exact Subtype.ext this

/-- The complement transport `fU` has image exactly Peterfalvi's complement `U`. -/
theorem fieldNormalizerComplementTransport_range (hyp : Hypothesis (G := G))
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hμ_inj : Function.Injective μ)
    (hμ_range : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :
    (fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range).range = hyp.base.U := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    obtain ⟨v, _, hv⟩ := fieldNormalizerComplementTransport_exists hyp μ hμ_inj hμ_range u
    rw [hv]
    exact v.2
  · intro g hg
    set μ' : ↥hyp.base.U →* ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :=
      { toFun := fun u => ⟨μ u, by rw [← hμ_range]; exact MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp } with hμ'def
    set eU : ↥hyp.base.U ≃* ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :=
      MulEquiv.ofBijective μ'
        ⟨fun a b h => hμ_inj (congrArg Subtype.val h),
         fun u => by
           obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (by rw [hμ_range]; exact u.2)
           exact ⟨v, Subtype.ext hv⟩⟩ with heUdef
    refine ⟨eU (⟨g, hg⟩ : ↥hyp.base.U), ?_⟩
    show (hyp.base.U.subtype.comp eU.symm.toMonoidHom) (eU ⟨g, hg⟩) = g
    simp

/-- **(14.7) σ-bridge assembly.**  Given the full Peterfalvi (14.2)(a) field model
(the additive isomorphism `e`, the multiplicative character `μ` realizing `U = U*`, the
`U`-equivariance `hcompat`, the prime-line/`W₂` identification `hW2`), together with the
standing `P ∩ U = 1`, the cyclotomic coprimality, and part (14.2)(b) data, the concrete
`FieldNormalizerData` exists.  The embedding `σ` is the `SemidirectProduct.lift` of the
two transport homomorphisms `fN`, `fU`, glued by (14.2)(a).  Every hypothesis is an
*input* — the §13 character theory (`basic_structure`, `c_eq_one`) that produces them is
not invoked here, so this reduction is the ungated heart of (14.7). -/
theorem fieldNormalizerData_of_repr (hyp : Hypothesis (G := G))
    (e : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hμ_inj : Function.Injective μ)
    (hμ_range : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q)
    (hUP : ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
         (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.base.P)
    (hcompat : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
           e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hUP v x⟩ : ↥hyp.base.P))
             = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                 GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x))
    (hW2 : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         (((Submodule.span (ZMod hyp.base.p)
             ({(1 : GaloisField hyp.base.p hyp.base.q)} :
               Set (GaloisField hyp.base.p hyp.base.q))).toAddSubgroup).toSubgroup).map
           (fieldNormalizerKernelTransport hyp e) = hyp.base.W2)
    (hPU_disj : hyp.base.P ⊓ hyp.base.U = ⊥)
    (hcyclotomic :
       Nat.Coprime ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) (hyp.base.p - 1))
    (hQ_elemAb : IsElementaryAbelian hyp.base.q ↥hyp.base.Q)
    (hW2_norm_Q : hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.Q : Set G))
    (yQ : G) (hyQ_mem : yQ ∈ hyp.base.Q)
    (hW2_conj_y : MulAut.conj yQ • hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.U : Set G)) :
    Nonempty (FieldNormalizerData hyp) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  -- the `SemidirectProduct.lift` compatibility: `fN (u • s) = fU u * fN s * (fU u)⁻¹`,
  -- which is exactly the (14.2)(a) `U`-equivariance `hcompat` transported through the iso.
  have hcompatLift : ∀ u : OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q,
      (fieldNormalizerKernelTransport hyp e).comp
          ((OddOrder.BG.AppC.NormSet.normOneMulAction hyp.base.p hyp.base.q u).toMonoidHom)
        = (MulAut.conj (fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range u)).toMonoidHom.comp
          (fieldNormalizerKernelTransport hyp e) := by
    intro u
    ext s
    obtain ⟨v, hμv, hfUv⟩ :=
      fieldNormalizerComplementTransport_exists hyp μ hμ_inj hμ_range u
    show fieldNormalizerKernelTransport hyp e
        ((OddOrder.BG.AppC.NormSet.normOneMulAction hyp.base.p hyp.base.q u) s) =
      fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range u *
        fieldNormalizerKernelTransport hyp e s *
        (fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range u)⁻¹
    rw [hfUv]
    -- compute the action `u • s = ofAdd (↑u * toAdd s)`
    have hact : (OddOrder.BG.AppC.NormSet.normOneMulAction hyp.base.p hyp.base.q u) s =
        Multiplicative.ofAdd (((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
            GaloisField hyp.base.p hyp.base.q) *
            (Multiplicative.toAdd s : GaloisField hyp.base.p hyp.base.q)) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      conv_lhs => rw [← ofAdd_toAdd s]
      exact OddOrder.BG.AppC.NormSet.normOneMulAction_apply hyp.base.p hyp.base.q u
        (Multiplicative.toAdd s)
    rw [hact, fieldNormalizerKernelTransport_apply, fieldNormalizerKernelTransport_apply,
      toAdd_ofAdd]
    -- both sides are coercions of `↥P` elements; reduce to the conjugate identity
    set t : GaloisField hyp.base.p hyp.base.q := Multiplicative.toAdd s with htdef
    set x : ↥hyp.base.P := Additive.toMul (e.symm t) with hxdef
    have hex : e (Additive.ofMul x) = t := by
      rw [hxdef, ofMul_toMul, e.apply_symm_apply]
    have hkey : Additive.toMul (e.symm (((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
          GaloisField hyp.base.p hyp.base.q) * t)) =
        (⟨(v : G) * (x : G) * (v : G)⁻¹, hUP v x⟩ : ↥hyp.base.P) := by
      have h1 := hcompat v x
      rw [hex] at h1
      have hμvF : ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
            GaloisField hyp.base.p hyp.base.q) =
          ((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
            GaloisField hyp.base.p hyp.base.q) := by rw [hμv]
      rw [hμvF] at h1
      have h2 : Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hUP v x⟩ : ↥hyp.base.P) =
          e.symm (((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
            GaloisField hyp.base.p hyp.base.q) * t) := by
        rw [← h1, e.symm_apply_apply]
      rw [← h2, toMul_ofMul]
    rw [hkey]
  -- the field-normalizer embedding `σ`
  set sigma := SemidirectProduct.lift (fieldNormalizerKernelTransport hyp e)
    (fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range) hcompatLift with hsigma
  -- `σ (inl a) (inr b) = fN a * fU b`
  have hlift_apply : ∀ g : fieldNormalizerFrobeniusGroup hyp,
      sigma g = fieldNormalizerKernelTransport hyp e g.left *
        fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range g.right := by
    intro g
    rw [hsigma]
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
    rw [map_mul, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
  -- `σ` is injective: kernel meets complement trivially (`P ∩ U = 1`)
  have hsigma_inj : Function.Injective sigma := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker, hlift_apply] at hg
    -- `fN g.left = (fU g.right)⁻¹ ∈ P ⊓ U = ⊥`
    have hPmemP : fieldNormalizerKernelTransport hyp e g.left ∈ hyp.base.P := by
      rw [← fieldNormalizerKernelTransport_range hyp e]; exact ⟨g.left, rfl⟩
    have hinv : fieldNormalizerKernelTransport hyp e g.left =
        (fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range g.right)⁻¹ :=
      mul_eq_one_iff_eq_inv.mp hg
    have hUmemU : fieldNormalizerKernelTransport hyp e g.left ∈ hyp.base.U := by
      rw [hinv]
      apply Subgroup.inv_mem
      rw [← fieldNormalizerComplementTransport_range hyp μ hμ_inj hμ_range]
      exact ⟨g.right, rfl⟩
    have hbot : fieldNormalizerKernelTransport hyp e g.left = 1 := by
      have : fieldNormalizerKernelTransport hyp e g.left ∈ hyp.base.P ⊓ hyp.base.U :=
        ⟨hPmemP, hUmemU⟩
      rw [hPU_disj] at this
      simpa using this
    have hleft : g.left = 1 := fieldNormalizerKernelTransport_injective hyp e (by
      rw [hbot, map_one])
    have hfUone : fieldNormalizerComplementTransport hyp μ hμ_inj hμ_range g.right = 1 := by
      have hg' := hg
      rw [hbot, one_mul] at hg'
      exact hg'
    have hright : g.right = 1 :=
      fieldNormalizerComplementTransport_injective hyp μ hμ_inj hμ_range (by
        rw [hfUone, map_one])
    rw [Subgroup.mem_bot]
    exact SemidirectProduct.ext hleft hright
  -- `σ` carries the abstract kernel / complement / prime line onto `P` / `U` / `W₂`
  have hP : (fieldNormalizerKernel hyp).map sigma = hyp.base.P := by
    rw [fieldNormalizerKernel, MonoidHom.range_eq_map, Subgroup.map_map, hsigma,
      SemidirectProduct.lift_comp_inl, ← MonoidHom.range_eq_map,
      fieldNormalizerKernelTransport_range]
  have hU : (fieldNormalizerComplement hyp).map sigma = hyp.base.U := by
    rw [fieldNormalizerComplement, MonoidHom.range_eq_map, Subgroup.map_map, hsigma,
      SemidirectProduct.lift_comp_inr, ← MonoidHom.range_eq_map,
      fieldNormalizerComplementTransport_range]
  have hP0 : (fieldNormalizerPrimeLine hyp).map sigma = hyp.base.W2 := by
    rw [fieldNormalizerPrimeLine, OddOrder.BG.AppC.NormSet.normOneFrobeniusSubspaceKernel,
      Subgroup.map_map, hsigma, SemidirectProduct.lift_comp_inl]
    exact hW2
  exact ⟨{
    sigma := sigma
    sigma_injective := hsigma_inj
    sigma_P_eq_P := hP
    sigma_P0_eq_W2 := hP0
    sigma_U_eq_U := hU
    cyclotomic_coprime := hcyclotomic
    Q_elementaryAbelian := hQ_elemAb
    W2_normalizes_Q := hW2_norm_Q
    y := yQ
    y_mem_Q := hyQ_mem
    W2_conj_y_normalizes_U := hW2_conj_y }⟩

/-! ### (14.7) standing structural inputs (proved by citing the §13 Frobenius data)

These discharge the *structural* hypotheses of `fieldNormalizerData_of_repr` from the
standing Section-15 data — they cite the (sorried) §13 producers `basic_structure`/`c_eq_one`
the same way `u_modEq_one_mod_q` does, so they are proven (their own bodies are `sorry`-free).
The remaining genuine work for (14.7) is the *numeric* input `|U| = (p^q-1)/(p-1)` and the
`𝔽_p[U]`-module construction feeding `exists_galoisField_repr`. -/

/-- `U` normalizes `P`: since `P = F(S)` is normal in `S` and `U ≤ S' = PU ≤ S`. -/
theorem U_le_normalizer_P (hyp : Hypothesis (G := G)) :
    hyp.base.U ≤ Subgroup.normalizer hyp.base.P := by
  have hU_le_deriv : hyp.base.U ≤ derivedInG hyp.base.S := by
    rw [hyp.base.S_deriv_eq_PU]; exact le_sup_right
  have hderiv_le_S : derivedInG hyp.base.S ≤ hyp.base.S := Subgroup.map_subtype_le _
  have hS_le_norm : hyp.base.S ≤ Subgroup.normalizer hyp.base.P := by
    rw [hyp.base.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.S
  exact (hU_le_deriv.trans hderiv_le_S).trans hS_le_norm

/-- **(14.7) `hUP` input**: conjugating a point of `P` by an element of `U` stays in `P`. -/
theorem conj_mem_P (hyp : Hypothesis (G := G)) (v : ↥hyp.base.U) (x : ↥hyp.base.P) :
    (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.base.P := by
  have hv : (v : G) ∈ Subgroup.normalizer hyp.base.P := U_le_normalizer_P hyp v.2
  exact (Subgroup.mem_normalizer_iff.mp hv (x : G)).mp x.2

/-- `V` normalizes `Q` (`T`-side dual of `U_le_normalizer_P`): `Q = F(T)` is normal in `T` and
`V ≤ T' = Q V ≤ T` (`T_deriv_eq_QV`). -/
theorem V_le_normalizer_Q (hyp : Hypothesis (G := G)) :
    hyp.base.V ≤ Subgroup.normalizer hyp.base.Q := by
  have hV_le_deriv : hyp.base.V ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right
  have hderiv_le_T : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hT_le_norm : hyp.base.T ≤ Subgroup.normalizer hyp.base.Q := by
    rw [hyp.base.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T
  exact (hV_le_deriv.trans hderiv_le_T).trans hT_le_norm

/-- `T`-side dual of `conj_mem_P`: conjugating a point of `Q` by an element of `V` stays in `Q`. -/
theorem conj_mem_Q (hyp : Hypothesis (G := G)) (v : ↥hyp.base.V) (x : ↥hyp.base.Q) :
    (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.base.Q := by
  have hv : (v : G) ∈ Subgroup.normalizer hyp.base.Q := V_le_normalizer_Q hyp v.2
  exact (Subgroup.mem_normalizer_iff.mp hv (x : G)).mp x.2

set_option maxHeartbeats 1000000 in
open scoped IsMulCommutative in
/-- **(14.7)/(14.2)(a) field model from the §13 numeric data.**  When
`|U| = (p^q-1)/(p-1)` (the (14.7) cyclotomic value), the conjugation action of `U` on the
elementary-abelian `P` of order `p^q` makes `Additive ↥P ≅ 𝔽_{p^q}` with `U ↪ 𝔽^×`
(Singer mechanism, `exists_galoisField_repr`).  Cites the §13 producers `basic_structure`
(`|P|=p^q`, `P` elementary abelian) and `c_eq_one` (`U` faithful on `P`). -/
theorem exists_pu_field_repr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hu_full : Nat.card ↥hyp.base.U =
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    ∃ (e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
      (μ : ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ),
      Function.Injective μ ∧
      ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
        e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
            ↥hyp.base.P))
          = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
              GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  haveI : NeZero hyp.base.p := ⟨hyp.base.p_prime.ne_zero⟩
  obtain ⟨data, _⟩ := OddOrder.Peterfalvi.S15.basic_structure hG hyp.base
  haveI hPcomm : IsMulCommutative ↥hyp.base.P :=
    IsMulCommutative.of_comm data.P_elementaryAbelian.comm
  letI hUcomm : CommGroup ↥hyp.base.U :=
    { (inferInstance : Group ↥hyp.base.U) with
      mul_comm := fun a b => (isMulCommutative_iff.mp data.U_commutative) a b }
  have hpsmul : ∀ x : Additive ↥hyp.base.P, (hyp.base.p : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact data.P_elementaryAbelian.pow_eq_one x.toMul
  haveI hPmod : Module (ZMod hyp.base.p) (Additive ↥hyp.base.P) :=
    AddCommGroup.zmodModule hpsmul
  -- the conjugation representation of `U` on `Additive ↥P`
  let conjHom : ↥hyp.base.U →* MulAut ↥hyp.base.P :=
    (Subgroup.normalizerMonoidHom (H := hyp.base.P)).comp
      (Subgroup.inclusion (U_le_normalizer_P hyp))
  let ρ : Representation (ZMod hyp.base.p) ↥hyp.base.U (Additive ↥hyp.base.P) :=
    (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥hyp.base.P hyp.base.p).comp conjHom
  have hρ_apply : ∀ (c : ↥hyp.base.U) (a : Additive ↥hyp.base.P),
      ρ c a = Additive.ofMul ((conjHom c) (Additive.toMul a)) := fun _ _ => rfl
  -- `Additive ↥P` as an `𝔽_p[U]`-module *directly* (sidesteps the `asModule` synth trap)
  letI hPmodAlg :
      Module (MonoidAlgebra (ZMod hyp.base.p) ↥hyp.base.U) (Additive ↥hyp.base.P) :=
    Module.compHom (Additive ↥hyp.base.P) (ρ.asAlgebraHom).toRingHom
  have hof_smul : ∀ (c : ↥hyp.base.U) (a : Additive ↥hyp.base.P),
      MonoidAlgebra.of (ZMod hyp.base.p) ↥hyp.base.U c • a =
        Additive.ofMul ((conjHom c) (Additive.toMul a)) := by
    intro c a
    have h : MonoidAlgebra.of (ZMod hyp.base.p) ↥hyp.base.U c • a = ρ c a := by
      show (ρ.asAlgebraHom (MonoidAlgebra.of (ZMod hyp.base.p) ↥hyp.base.U c)) a = ρ c a
      rw [Representation.asAlgebraHom_of]
    rw [h, hρ_apply]
  haveI hNeZero : NeZero (Nat.card ↥hyp.base.U : ZMod hyp.base.p) := by
    refine ⟨fun h => ?_⟩
    rw [hu_full] at h
    have hdvd : hyp.base.p ∣ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
      (ZMod.natCast_eq_zero_iff _ _).mp h
    have hmod : (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) ≡ 1 [MOD hyp.base.p] := by
      have hsum_eq : ∑ k ∈ Finset.range hyp.base.q, hyp.base.p ^ k =
          (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
        Nat.geomSum_eq hyp.base.p_prime.two_le _
      rw [← hsum_eq, show hyp.base.q = (hyp.base.q - 1) + 1 by
          have := hyp.base.q_prime.pos; omega, Finset.sum_range_succ']
      have hzero : (∑ k ∈ Finset.range (hyp.base.q - 1), hyp.base.p ^ (k + 1)) ≡ 0
          [MOD hyp.base.p] := by
        rw [Nat.modEq_zero_iff_dvd]
        exact Finset.dvd_sum fun k _ => dvd_pow_self hyp.base.p (Nat.succ_ne_zero k)
      simpa using hzero.add_right 1
    have hdvd1 : hyp.base.p ∣ 1 := by
      have h0 := (Nat.modEq_zero_iff_dvd).mpr hdvd
      have h01 := h0.symm.trans hmod
      rwa [Nat.modEq_iff_dvd', Nat.sub_zero] at h01
      omega
    exact absurd (Nat.le_of_dvd one_pos hdvd1) (by have := hyp.base.p_prime.two_le; omega)
  have hcardM : Nat.card (Additive ↥hyp.base.P) = hyp.base.p ^ hyp.base.q := data.P_order
  have hfaith : ∀ c : ↥hyp.base.U,
      (∀ x : Additive ↥hyp.base.P,
          MonoidAlgebra.of (ZMod hyp.base.p) ↥hyp.base.U c • x = x) → c = 1 := by
    intro c hc
    have hcomm : ∀ y : ↥hyp.base.P, (c : G) * (y : G) = (y : G) * (c : G) := by
      intro y
      have h1 := hc (Additive.ofMul y)
      rw [hof_smul] at h1
      have h2 : (conjHom c) y = y := Additive.ofMul.injective (by simpa using h1)
      have h3 : (c : G) * (y : G) * (c : G)⁻¹ = (y : G) := congrArg Subtype.val h2
      rwa [mul_inv_eq_iff_eq_mul] at h3
    have hmem : (c : G) ∈ hyp.base.C := by
      rw [hyp.base.C_eq]
      exact ⟨c.2, Subgroup.mem_centralizer_iff.mpr (fun y hy => (hcomm ⟨y, hy⟩).symm)⟩
    have hCbot : hyp.base.C = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      rw [← hyp.base.c_eq_card_C, OddOrder.Peterfalvi.S15.c_eq_one hG hyp.base]
    rw [hCbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨e0, μ, hμinj, hcompat0⟩ :=
    OddOrder.RepresentationTheory.exists_galoisField_repr
      (C := ↥hyp.base.U) (M := Additive ↥hyp.base.P)
      hyp.base.q_prime hyp.base.q_odd hcardM hu_full hfaith
  refine ⟨e0, μ, hμinj, ?_⟩
  intro v x
  rw [← hcompat0 v (Additive.ofMul x), hof_smul v (Additive.ofMul x)]
  congr 2

/-- **(14.7) `hμ_range` input**: any injective `μ : U →* 𝔽_{p^q}ˣ` with `|U| = (p^q-1)/(p-1)`
has image exactly the norm-one units `U*`.  Both are subgroups of the cyclic group `𝔽_{p^q}ˣ`
of the same order `d = (p^q-1)/(p-1)`, hence both equal the unique subgroup `{x | x^d = 1}` of
that order (`= ker (powMonoidHom d)`, whose card is `gcd(p^q-1, d) = d`). -/
theorem mu_range_eq_normOneUnits {hyp : Hypothesis (G := G)}
    (hu_full : Nat.card ↥hyp.base.U =
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hinj : Function.Injective μ) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  set d := (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) with hd
  have hq0 : hyp.base.q ≠ 0 := hyp.base.q_prime.ne_zero
  have hGcard : Nat.card (GaloisField hyp.base.p hyp.base.q)ˣ = hyp.base.p ^ hyp.base.q - 1 := by
    rw [Nat.card_units, GaloisField.card hyp.base.p hyp.base.q hq0]
  have hpm1_dvd : (hyp.base.p - 1) ∣ (hyp.base.p ^ hyp.base.q - 1) := by
    have h1 : (1 : ℕ) ≡ hyp.base.p [MOD (hyp.base.p - 1)] :=
      (Nat.modEq_iff_dvd' (by have := hyp.base.p_prime.two_le; omega)).mpr dvd_rfl
    have hq1 : (1 : ℕ) ≡ hyp.base.p ^ hyp.base.q [MOD (hyp.base.p - 1)] := by
      simpa using h1.pow hyp.base.q
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by have := hyp.base.p_prime.two_le; omega))).mp hq1
  have hd_dvd : d ∣ (hyp.base.p ^ hyp.base.q - 1) :=
    ⟨hyp.base.p - 1, (Nat.div_mul_cancel hpm1_dvd).symm⟩
  have hkercard : Nat.card
      (powMonoidHom d :
        (GaloisField hyp.base.p hyp.base.q)ˣ →* (GaloisField hyp.base.p hyp.base.q)ˣ).ker = d := by
    rw [IsCyclic.card_powMonoidHom_ker, hGcard, Nat.gcd_eq_right hd_dvd]
  have hμcard : Nat.card (μ.range) = d := by
    have hcU := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [hu_full] at hcU
    exact hcU
  have hncard :
      Nat.card (OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) = d :=
    OddOrder.BG.AppC.NormSet.normOneUnits_card hyp.base.p hyp.base.q hq0
  have hsub : ∀ (K : Subgroup (GaloisField hyp.base.p hyp.base.q)ˣ), Nat.card K = d →
      K ≤ (powMonoidHom d :
        (GaloisField hyp.base.p hyp.base.q)ˣ →* (GaloisField hyp.base.p hyp.base.q)ˣ).ker := by
    intro K hK x hx
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    have hord : orderOf x ∣ d := by
      have h := orderOf_dvd_natCard (⟨x, hx⟩ : K)
      rw [hK] at h
      rwa [← orderOf_injective K.subtype (Subgroup.subtype_injective K) ⟨x, hx⟩] at h
    exact orderOf_dvd_iff_pow_eq_one.mp hord
  have hμeq : μ.range =
      (powMonoidHom d :
        (GaloisField hyp.base.p hyp.base.q)ˣ →* (GaloisField hyp.base.p hyp.base.q)ˣ).ker :=
    Subgroup.eq_of_le_of_card_ge (hsub _ hμcard) (le_of_eq (hkercard.trans hμcard.symm))
  have hneq : OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q =
      (powMonoidHom d :
        (GaloisField hyp.base.p hyp.base.q)ˣ →* (GaloisField hyp.base.p hyp.base.q)ˣ).ker :=
    Subgroup.eq_of_le_of_card_ge (hsub _ hncard) (le_of_eq (hkercard.trans hncard.symm))
  rw [hμeq, hneq]

/-- **(14.7) prime-line rescaling.**  The field model `e₀` produced by `exists_pu_field_repr`
is canonical only up to a nonzero field scalar — nothing in the Singer construction pins down
where it sends the prime line `W₂`.  Given `W₂ ≤ P` (a §13-structural fact), rescale
`e₀ ↦ c⁻¹ • e₀` by `c := e₀(w₀)` for a nonidentity `w₀ ∈ W₂`.  The rescaled `e` then sends
`w₀ ↦ 1`, hence carries the prime line `⟨1⟩ = (span 𝔽_p {1})` of `𝔽_{p^q}` exactly onto `W₂`
(both are cyclic of prime order `p`).  The `U`-equivariance `hcompat` survives because the
field is commutative (`c⁻¹·(μv·y) = μv·(c⁻¹·y)`).  This produces the `hW2` input of
`fieldNormalizerData_of_repr`; it is pure field algebra, *independent* of the §13 character
theory that produces `e₀` — `W₂ ≤ P` is its only structural input. -/
theorem field_repr_rescale_to_W2 (hyp : Hypothesis (G := G))
    (hW2_le_P : hyp.base.W2 ≤ hyp.base.P)
    (e₀ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hcompat₀ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
           e₀ (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
               ↥hyp.base.P))
             = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                 GaloisField hyp.base.p hyp.base.q) * e₀ (Additive.ofMul x)) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    ∃ e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q,
      (∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
          e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
              ↥hyp.base.P))
            = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x)) ∧
      (((Submodule.span (ZMod hyp.base.p)
            ({(1 : GaloisField hyp.base.p hyp.base.q)} :
              Set (GaloisField hyp.base.p hyp.base.q))).toAddSubgroup).toSubgroup).map
          (fieldNormalizerKernelTransport hyp e) = hyp.base.W2 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  haveI : NeZero hyp.base.p := ⟨hyp.base.p_prime.ne_zero⟩
  -- `ZMod p`-linearity reduces to `nsmul` (any module over `ZMod p`)
  have hsmul_red : ∀ (r : ZMod hyp.base.p) (x : GaloisField hyp.base.p hyp.base.q),
      r • x = r.val • x := by
    intro r x
    rw [← Nat.cast_smul_eq_nsmul (ZMod hyp.base.p) r.val x, ZMod.natCast_rightInverse r]
  -- a nonidentity element of the prime line `W₂ ≤ P`
  haveI hW2fin : Finite ↥hyp.base.W2 := Nat.finite_of_card_ne_zero (by
    rw [← hyp.base.p_eq_card_W2]; exact hyp.base.p_prime.ne_zero)
  haveI : Nontrivial ↥hyp.base.W2 := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [← hyp.base.p_eq_card_W2]; exact hyp.base.p_prime.one_lt)
  obtain ⟨w0', hw0'_ne⟩ := exists_ne (1 : ↥hyp.base.W2)
  have hw0G_ne : (w0' : G) ≠ 1 := fun h => hw0'_ne (OneMemClass.coe_eq_one.mp h)
  set w0 : ↥hyp.base.P := ⟨(w0' : G), hW2_le_P w0'.2⟩ with hw0def
  have hw0_ne : w0 ≠ 1 := by
    rw [hw0def, ne_eq, Subtype.ext_iff]; simpa using hw0G_ne
  -- the rescaling scalar `c = e₀ w₀ ≠ 0`
  set c : GaloisField hyp.base.p hyp.base.q := e₀ (Additive.ofMul w0) with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef, ne_eq, map_eq_zero_iff _ e₀.injective]
    rw [show (0 : Additive ↥hyp.base.P) = Additive.ofMul (1 : ↥hyp.base.P) from rfl,
      EmbeddingLike.apply_eq_iff_eq]
    exact hw0_ne
  -- multiplication by `c⁻¹` is an additive automorphism of the field
  let scale : GaloisField hyp.base.p hyp.base.q ≃+ GaloisField hyp.base.p hyp.base.q :=
    { toFun := fun x => c⁻¹ * x
      invFun := fun x => c * x
      left_inv := fun x => mul_inv_cancel_left₀ hc x
      right_inv := fun x => inv_mul_cancel_left₀ hc x
      map_add' := fun x y => mul_add c⁻¹ x y }
  set e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q := e₀.trans scale with hedef
  have he_apply : ∀ a, e a = c⁻¹ * e₀ a := fun a => rfl
  have he_w0 : e (Additive.ofMul w0) = 1 := by
    rw [he_apply, ← hcdef, inv_mul_cancel₀ hc]
  refine ⟨e, ?_, ?_⟩
  · -- `hcompat` survives rescaling by commutativity
    intro v x
    simp only [he_apply]
    rw [hcompat₀ v x]; ring
  · -- the prime line `span{1}` maps onto `W₂`
    have hSpan : (((Submodule.span (ZMod hyp.base.p)
          ({(1 : GaloisField hyp.base.p hyp.base.q)} :
            Set (GaloisField hyp.base.p hyp.base.q))).toAddSubgroup).toSubgroup)
        = Subgroup.zpowers
            (Multiplicative.ofAdd (1 : GaloisField hyp.base.p hyp.base.q)) := by
      apply le_antisymm
      · intro g hg
        rw [Multiplicative.mem_toSubgroup, Submodule.mem_toAddSubgroup,
          Submodule.mem_span_singleton] at hg
        obtain ⟨r, hr⟩ := hg
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨(r.val : ℤ), ?_⟩
        rw [zpow_natCast, ← ofAdd_nsmul, ← hsmul_red r, hr, ofAdd_toAdd]
      · rw [Subgroup.zpowers_le, Multiplicative.mem_toSubgroup, Submodule.mem_toAddSubgroup]
        exact Submodule.subset_span (by simp)
    rw [hSpan, MonoidHom.map_zpowers]
    have hfN1 : fieldNormalizerKernelTransport hyp e
        (Multiplicative.ofAdd (1 : GaloisField hyp.base.p hyp.base.q)) = (w0' : G) := by
      rw [fieldNormalizerKernelTransport_apply]
      have hsymm : e.symm (1 : GaloisField hyp.base.p hyp.base.q) = Additive.ofMul w0 := by
        rw [← he_w0, e.symm_apply_apply]
      simp [hsymm, hw0def]
    rw [hfN1]
    -- `zpowers (w0' : G) = W₂` since `w0'` has prime order `p`
    have horder : orderOf ((w0' : G)) = hyp.base.p := by
      have hne1 : orderOf ((w0' : G)) ≠ 1 := fun h => hw0G_ne (orderOf_eq_one_iff.mp h)
      have hdvd : orderOf ((w0' : G)) ∣ hyp.base.p := by
        have heq : orderOf ((w0' : G)) = orderOf w0' :=
          orderOf_injective hyp.base.W2.subtype (Subgroup.subtype_injective _) w0'
        rw [heq, hyp.base.p_eq_card_W2]
        exact orderOf_dvd_natCard w0'
      rcases (hyp.base.p_prime.eq_one_or_self_of_dvd _ hdvd) with h | h
      · exact absurd h hne1
      · exact h
    have hle : Subgroup.zpowers ((w0' : G)) ≤ hyp.base.W2 := by
      rw [Subgroup.zpowers_le]; exact w0'.2
    have hcard : Nat.card hyp.base.W2 ≤ Nat.card (Subgroup.zpowers ((w0' : G))) := by
      rw [Nat.card_zpowers, horder, ← hyp.base.p_eq_card_W2]
    exact Subgroup.eq_of_le_of_card_ge hle hcard

/-- **(14.7)/(14.2)(a) field model carrying the prime line to `W₂`.**  Chains the Singer
field model `exists_pu_field_repr` with the prime-line rescaling `field_repr_rescale_to_W2`,
producing the full `(e, μ)` package that `fieldNormalizerData_of_repr` consumes: an additive
isomorphism `e : Additive ↥P ≃+ 𝔽_{p^q}`, an injective character `μ : U →* 𝔽_{p^q}ˣ`, the
`U`-equivariance `hcompat`, and the prime-line/`W₂` identification `hW2`.  Cites the §13
producers `basic_structure` (`|P| = p^q`) and `c_eq_one` (`U` faithful) through
`exists_pu_field_repr`; its extra structural input is `W₂ ≤ P`. -/
theorem exists_pu_field_repr_W2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hu_full : Nat.card ↥hyp.base.U =
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hW2_le_P : hyp.base.W2 ≤ hyp.base.P) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    ∃ (e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
      (μ : ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ),
      Function.Injective μ ∧
      (∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
          e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
              ↥hyp.base.P))
            = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x)) ∧
      (((Submodule.span (ZMod hyp.base.p)
            ({(1 : GaloisField hyp.base.p hyp.base.q)} :
              Set (GaloisField hyp.base.p hyp.base.q))).toAddSubgroup).toSubgroup).map
          (fieldNormalizerKernelTransport hyp e) = hyp.base.W2 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  obtain ⟨e₀, μ, hμinj, hcompat₀⟩ := exists_pu_field_repr hG hyp hu_full
  obtain ⟨e, hcompat, hW2⟩ := field_repr_rescale_to_W2 hyp hW2_le_P e₀ μ hcompat₀
  exact ⟨e, μ, hμinj, hcompat, hW2⟩

/-- **(14.7) assembly engine.**  Given the §13/§14-gated structural facts as explicit
hypotheses — the cyclotomic value `|U| = (p^q-1)/(p-1)` (14.7), `U` cyclic (13), `W₂ ≤ P`
(13), the coprimality `gcd((p^q-1)/(p-1), p-1) = 1` (14.7), and part (14.2)(b)
(`Q` elementary abelian, `W₂ ≤ N_G(Q)`, and a `y ∈ Q` with `W₂^y ≤ N_G(U)`) — the concrete
`FieldNormalizerData` exists.  Every step is one of the proven (14.7) producers:
`exists_pu_field_repr_W2` (field model + prime line → `W₂`), `mu_range_eq_normOneUnits`
(`μ` onto `U*`), `conj_mem_P`/`P_inf_U_eq_bot` (the kernel/complement intersection), assembled
by the σ-bridge `fieldNormalizerData_of_repr`.  This engine carries no `sorry`; it is gated only
through the §13 producers `basic_structure`/`c_eq_one` cited inside `exists_pu_field_repr_W2`
and `P_inf_U_eq_bot` (Lane B), so it becomes unconditional exactly when those land. -/
theorem field_normalizer_of_U_characteristic_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hu_full : Nat.card ↥hyp.base.U =
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hW2_le_P : hyp.base.W2 ≤ hyp.base.P)
    (hcyc : Nat.Coprime
      ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) (hyp.base.p - 1))
    (hQ_elemAb : IsElementaryAbelian hyp.base.q ↥hyp.base.Q)
    (hW2_norm_Q : hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.Q : Set G))
    (yQ : G) (hyQ_mem : yQ ∈ hyp.base.Q)
    (hW2_conj_y : MulAut.conj yQ • hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.U : Set G)) :
    Nonempty (FieldNormalizerData hyp) := by
  obtain ⟨e, μ, hμinj, hcompat, hW2⟩ := exists_pu_field_repr_W2 hG hyp hu_full hW2_le_P
  exact fieldNormalizerData_of_repr hyp e μ hμinj
    (mu_range_eq_normOneUnits hu_full μ hμinj) (conj_mem_P hyp) hcompat hW2
    (P_inf_U_eq_bot hG hyp) hcyc hQ_elemAb hW2_norm_Q yQ hyQ_mem hW2_conj_y

/-! **Peterfalvi (14.7)** (`field_normalizer_of_U_characteristic`) is assembled **after** the
(14.5)/(13.17) fixed-point-free bridge `u_modEq_one_mod_p_of_LHypothesis` below: it consumes that
bridge (for `u ≡ 1 mod p`), the value-argument engine `field_normalizer_of_U_characteristic_of_fpf`,
and the part-(14.2.b) normalizer lemma `W2conj_le_normalizer_U_of_LHypothesis`.  See it just before
`field_normalizer_of_L_conj_M`. -/

end OddOrder.Peterfalvi.S16
