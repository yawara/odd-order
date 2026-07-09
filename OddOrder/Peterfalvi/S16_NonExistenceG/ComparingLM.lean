import OddOrder.Peterfalvi.S16_NonExistenceG.SubgroupM

/-!
# Peterfalvi (14.12)-(14.16) — comparing L and M

Split from the former monolithic `OddOrder.Peterfalvi.S16_NonExistenceG` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S16
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped BigOperators

variable {G : Type*} [Group G]


/-! ## (14.12)--(14.16): comparing `L` and `M` -/

/-! **Peterfalvi (14.12)** (`field_normalizer_of_L_conj_M`, the `L ≅ M` case) is assembled
**after** (14.7) `field_normalizer_of_U_characteristic`, which it reduces to: when `L` is conjugate
to `M`, `H` is cyclic, so `U ≤ H` is characteristic and (14.7) applies.  See it just after (14.7). -/

/-- **Peterfalvi (14.13)**: the final comparison case assumes `L` and `M` are
not conjugate and sets `h = |H|`. -/
structure NonConjugateHypothesis (hyp : Hypothesis (G := G)) where
  Ldata : LHypothesis hyp
  Mdata : MHypothesis hyp
  not_conj : ¬ ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M
  h : ℕ
  h_eq_card_H : h = Nat.card ↥Ldata.H

namespace NonConjugateHypothesis

/-- **Peterfalvi (14.13)**: since `h = |H|` and `H` is a subgroup of the
minimal odd-order group, `h` is odd. -/
theorem h_odd [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp) :
    Odd nc.h := by
  rw [nc.h_eq_card_H]
  exact _hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card nc.Ldata.H)

/-- **Peterfalvi (14.5)** cardinal consequence: `u` divides `h = |H|`.
The subgroup `U` lies in the Fitting kernel `H` of the type-I subgroup over
`N_G(U)`, while (13.12) gives `c = 1`; hence `|U| = u` and `u ∣ |H|`. -/
theorem u_dvd_h [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp) :
    hyp.base.u ∣ nc.h := by
  rw [nc.h_eq_card_H]
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc, OddOrder.Peterfalvi.S15.c_eq_one _hG hyp.base, mul_one]
  have hU_le_H : hyp.base.U ≤ nc.Ldata.H := by
    rw [← nc.Ldata.typeI_data_H_eq]
    exact nc.Ldata.typeI_data.U_le_H
  have hdvd : Nat.card ↥hyp.base.U ∣ Nat.card ↥nc.Ldata.H :=
    Subgroup.card_dvd_of_le hU_le_H
  simpa [hU_card] using hdvd

/-- **Peterfalvi (14.5)** cardinal congruences for `h = |H|`.  The type-I
Frobenius structure has kernel `M_F = H`; by (14.5) its complement has order
`p q`.  Isaacs Lemma 6.1 gives `|H| ≡ 1 mod |C|`, hence both congruences
modulo `p` and modulo `q`. -/
theorem h_modEq_one_mod_p_and_q [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp) :
    nc.h ≡ 1 [MOD hyp.base.p] ∧ nc.h ≡ 1 [MOD hyp.base.q] := by
  let H0 : Subgroup G := nc.Ldata.typeI_data.frobenius.typeI.typeF.H
  have hH0_eq_typeI_H : H0 = nc.Ldata.typeI_data.H := by
    dsimp [H0]
    rw [nc.Ldata.typeI_data.frobenius.typeI.typeF.H_eq,
      nc.Ldata.typeI_data.H_eq_LF]
  have hH0_eq_H : H0 = nc.Ldata.H :=
    hH0_eq_typeI_H.trans nc.Ldata.typeI_data_H_eq
  have hkernel_card :
      Nat.card ↥(H0.subgroupOf nc.Ldata.typeI_data.L) = Nat.card ↥nc.Ldata.H := by
    have hH0_card :
        Nat.card ↥(H0.subgroupOf nc.Ldata.typeI_data.L) = Nat.card ↥H0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (by
        dsimp [H0]
        exact nc.Ldata.typeI_data.frobenius.typeI.typeF.H_le)).toEquiv
    rw [hH0_card, hH0_eq_H]
  have hmod_pq : nc.h ≡ 1 [MOD hyp.base.p * hyp.base.q] := by
    have hmod := nc.Ldata.typeI_data.frobenius.frobenius.card_kernel_modEq_one
    rw [hkernel_card, nc.Ldata.typeI_complement_card_eq_pq] at hmod
    rwa [nc.h_eq_card_H]
  exact ⟨hmod_pq.of_dvd (dvd_mul_right hyp.base.p hyp.base.q),
    hmod_pq.of_dvd (dvd_mul_left hyp.base.q hyp.base.p)⟩

end NonConjugateHypothesis

namespace Hypothesis

/-- **Peterfalvi (14.5)** fixed-point-free cardinal consequence for `U`:
`u ≡ 1 mod q`.  The Frobenius action of `W₁` on `U` gives
`|U| ≡ 1 mod |W₁|`; using (13.12), `|U| = u`, and the definition
`q = |W₁|` gives the stated congruence. -/
theorem u_modEq_one_mod_q [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.u ≡ 1 [MOD hyp.base.q] := by
  rcases OddOrder.Peterfalvi.S15.basic_structure _hG hyp.base with ⟨data, _hdata⟩
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc, OddOrder.Peterfalvi.S15.c_eq_one _hG hyp.base, mul_one]
  have hU_sub_card :
      Nat.card ↥(hyp.base.U.subgroupOf (hyp.base.U ⊔ hyp.base.W1)) =
        Nat.card ↥hyp.base.U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : hyp.base.U ≤ hyp.base.U ⊔ hyp.base.W1)).toEquiv
  have hW1_sub_card :
      Nat.card ↥(hyp.base.W1.subgroupOf (hyp.base.U ⊔ hyp.base.W1)) =
        Nat.card ↥hyp.base.W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_right : hyp.base.W1 ≤ hyp.base.U ⊔ hyp.base.W1)).toEquiv
  have hmod := data.UW1_frobenius.card_kernel_modEq_one
  rwa [hU_sub_card, hW1_sub_card, hU_card, ← hyp.base.q_eq_card_W1] at hmod

/-- **Peterfalvi (14.7)** fixed-point-free congruence for `U` modulo `p`.  The conjugate
`W₂^y` has order `p = |W₂|`; if it acts fixed-point-freely on `U` — as it does in (14.7), since
`W₂^y` lies in the complement of the type-I Frobenius subgroup `L ⊇ N_G(U)` whose kernel
contains `U` — then `|U| ≡ 1 mod p`, hence (using `|U| = u` by (13.12)) `u ≡ 1 mod p`.  This is
the mod-`p` analogue of `u_modEq_one_mod_q`; it discharges the `hu_mod_p` input of the (14.7)
value argument from the fixed-point-free action. -/
theorem u_modEq_one_mod_p_of_fpf [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {y : G}
    (hW2y_norm : (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Subgroup.normalizer (hyp.base.U : Set G))
    (hfpf : ∀ a ∈ (MulAut.conj y • hyp.base.W2 : Subgroup G), a ≠ 1 →
      ∀ u ∈ hyp.base.U, u ≠ 1 → a * u * a⁻¹ ≠ u) :
    hyp.base.u ≡ 1 [MOD hyp.base.p] := by
  have hW2y_card : Nat.card ↥(MulAut.conj y • hyp.base.W2 : Subgroup G) = hyp.base.p := by
    rw [hyp.base.p_eq_card_W2]
    exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj y) hyp.base.W2).toEquiv).symm
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc, OddOrder.Peterfalvi.S15.c_eq_one hG hyp.base, mul_one]
  have h := card_modEq_one_of_prime_normalizing_fpf hyp.base.p_prime hW2y_card hW2y_norm hfpf
  rwa [hU_card] at h

end Hypothesis

/-- **Part (14.2.b) normalizer conclusion `W₂^y ≤ N_G(U)`, from the structural carrier.**
The (14.5) complement membership of `W₂^y` already forces `W₂^y ≤ N_G(U)`: each element of `W₂^y`
lies in `L`, normalizes the Fitting kernel `H ◁ L` (`maxNilpotentNormalHall_le_normalizer`), and
`U` is characteristic in `H`, so it normalizes `U`
(`mem_normalizer_map_subtype_of_characteristic`).  Shared by the (14.7) value argument and the
final field-normalizer assembly. -/
theorem W2conj_le_normalizer_U_of_LHypothesis
    {hyp : Hypothesis (G := G)} (Ldata : LHypothesis hyp)
    (hchar : (hyp.base.U.subgroupOf Ldata.H).Characteristic)
    {y : G}
    (hW2y_compl : (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Ldata.typeI_data.frobenius.complement.map (Ldata.typeI_data.L).subtype) :
    (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Subgroup.normalizer (hyp.base.U : Set G) := by
  haveI : (hyp.base.U.subgroupOf Ldata.H).Characteristic := hchar
  have hU_le_H : hyp.base.U ≤ Ldata.H := by
    rw [← Ldata.typeI_data_H_eq]; exact Ldata.typeI_data.U_le_H
  intro a ha
  have ha_L : a ∈ Ldata.L := by
    obtain ⟨a', -, ha'eq⟩ := Subgroup.mem_map.mp (hW2y_compl ha)
    rw [← Ldata.typeI_data_L_eq, ← ha'eq]; exact a'.2
  have ha_normH : a ∈ Subgroup.normalizer (Ldata.H : Set G) := by
    have hLnorm := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer Ldata.L ha_L
    rwa [← Ldata.H_eq_LF] at hLnorm
  have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
    (W := Ldata.H) (C := hyp.base.U.subgroupOf Ldata.H) ha_normH
  rwa [Subgroup.map_subgroupOf_eq_of_le hU_le_H] at hmem

/-- **Peterfalvi (14.7) value-argument input, assembled from (14.3)/(13.17)/(14.5).**
With the type-I-over-`N_G(U)` carrier `Ldata` — so `L ⊇ N_G(U)` is a Frobenius group (13.17.a)
with kernel `H ⊇ U` (13.17.b) — and `U` characteristic in `H` (the standing hypothesis of
(14.7)), the element `y ∈ Q` produced by (14.5) places `W₂^y` in the Frobenius complement of `L`.
Then `W₂^y` normalizes `U` (it normalizes `H ◁ L`, and `U` is characteristic in `H`) and acts
fixed-point-freely on `U` (it is a nontrivial complement element acting on the kernel), so by
`Hypothesis.u_modEq_one_mod_p_of_fpf`, `u ≡ 1 (mod p)`.  This discharges the fixed-point-free
input of the (14.7) value argument from the structural carrier, reducing it to the (14.5)
membership `W₂^y ≤ complement`. -/
theorem u_modEq_one_mod_p_of_LHypothesis [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Ldata : LHypothesis hyp)
    (hchar : (hyp.base.U.subgroupOf Ldata.H).Characteristic)
    {y : G}
    (hW2y_compl : (MulAut.conj y • hyp.base.W2 : Subgroup G) ≤
      Ldata.typeI_data.frobenius.complement.map (Ldata.typeI_data.L).subtype) :
    hyp.base.u ≡ 1 [MOD hyp.base.p] := by
  -- `U ≤ H` (13.17.b)
  have hU_le_H : hyp.base.U ≤ Ldata.H := by
    rw [← Ldata.typeI_data_H_eq]; exact Ldata.typeI_data.U_le_H
  -- the Frobenius kernel base `typeI.typeF.H` is `H`
  have hH0_eq_typeIH : Ldata.typeI_data.frobenius.typeI.typeF.H = Ldata.typeI_data.H := by
    rw [Ldata.typeI_data.frobenius.typeI.typeF.H_eq, Ldata.typeI_data.H_eq_LF]
  have hH0_eq_H : Ldata.typeI_data.frobenius.typeI.typeF.H = Ldata.H :=
    hH0_eq_typeIH.trans Ldata.typeI_data_H_eq
  -- `W₂^y ≤ N_G(U)` (part (14.2.b)), shared with the final assembly
  have hW2y_norm := W2conj_le_normalizer_U_of_LHypothesis Ldata hchar hW2y_compl
  -- `W₂^y` acts fixed-point-freely on `U` (Frobenius complement on the kernel)
  have hfpf : ∀ a ∈ (MulAut.conj y • hyp.base.W2 : Subgroup G), a ≠ 1 →
      ∀ u ∈ hyp.base.U, u ≠ 1 → a * u * a⁻¹ ≠ u := by
    intro a ha ha_ne u hu hu_ne
    refine isFrobeniusGroup_conj_ne_of_mem_map_complement
      Ldata.typeI_data.frobenius.frobenius
      Ldata.typeI_data.frobenius.typeI.typeF.H_le (hW2y_compl ha) ha_ne ?_ hu_ne
    rw [hH0_eq_H]; exact hU_le_H hu
  exact Hypothesis.u_modEq_one_mod_p_of_fpf hG hyp hW2y_norm hfpf

/-- **Peterfalvi (13.2.b)/(14.2.a): `W₂ ≤ P`.**  `W₂` is a `p`-group (`|W₂| = p`) inside `S`
(`W₂ ≤ W = S ⊓ T`), while `P = S_F` is a normal Hall `p`-subgroup of `S` (normal by
`maxNilpotentNormalHall_subgroupOf_normal`, Hall by `maxNilpotentNormalHall_isHall`, and a
`p`-group of order `p^q` by `basic_structure`).  Hence `W₂ ≤ P` — the `F_p ⊆ F` identification of
(14.2.a). -/
theorem W2_le_P [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.base.W2 ≤ hyp.base.P :=
  OddOrder.Peterfalvi.S15.W2_le_P _hG hyp.base

/-- **Peterfalvi (13.2.b) for `T`**: `Q` is elementary abelian (13.2.b applied to the dual subgroup
`T`) — the canonical §15 obligation `Q_elementaryAbelian_T` (`T` type-II from `T_typeII` (14.9)). -/
theorem Q_elemAbelian_S [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    IsElementaryAbelian hyp.base.q ↥hyp.base.Q :=
  OddOrder.Peterfalvi.S15.Q_elementaryAbelian_T _hG hyp.base (T_typeII _hG hyp)

/-- **Peterfalvi (13.2) `S`-side structural inputs for the (14.7) field model.**  The field-model
construction (14.2.a) needs two §13 structural facts about the type-`P` subgroup `S`: `W₂ ≤ P`
(the `F_p ⊆ F` identification) and `Q` elementary abelian (13.2.b for `T`).  `W₂ ≤ P` is proved
outright (`W2_le_P`); `Q` elementary abelian is the §15 obligation `Q_elemAbelian_S`.

The field model needs **no** cyclicity of `U`: the Singer representation `exists_pu_field_repr` is
built from `U` **abelian** (Peterfalvi (13.2.a): `UW₁` is Frobenius with abelian kernel `U`; coq
`PFsection14.v` `cUU : abelian U`) via the abelian Singer irreducibility
`isSimpleModule_of_abelian_faithful_card`, and the injection `μ : U ↪ 𝔽_{p^q}^×` into the cyclic unit
group is a *consequence* — never a hypothesis. -/
theorem S_field_model_structural_inputs [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.base.W2 ≤ hyp.base.P ∧
      IsElementaryAbelian hyp.base.q ↥hyp.base.Q :=
  ⟨W2_le_P _hG hyp, Q_elemAbelian_S _hG hyp⟩

/-- **Peterfalvi (14.7)**: if `U` is characteristic in `H`, then the field-normalizer
configuration (14.2) holds.  The value argument is assembled entirely from the structural
carrier: (14.5) `exists_y_L_structure` supplies `y ∈ Q` with `W₂^y` in the Frobenius complement
of `L`; the bridge `u_modEq_one_mod_p_of_LHypothesis` turns that into `u ≡ 1 mod p`; and
`W2conj_le_normalizer_U_of_LHypothesis` supplies `W₂^y ≤ N_G(U)`.  These feed the value-argument
engine `field_normalizer_of_U_characteristic_of_fpf`.  This theorem carries **no `sorry`**: the
remaining §13 structural facts are cited as the named obligation `S_field_model_structural_inputs`
(`U` cyclic / `W₂ ≤ P` / `Q` elementary abelian), while `W₂ ≤ N_G(Q)` is discharged outright
(`W₂ ≤ W ≤ T` and `Q = T_F`). -/
theorem field_normalizer_of_U_characteristic [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp)
    (hchar : (hyp.base.U.subgroupOf Ldata.H).Characteristic) :
    Nonempty (FieldNormalizerData hyp) := by
  obtain ⟨y, hyQ, hW2y_compl⟩ := exists_y_L_structure hG hyp Ldata
  have hmod := u_modEq_one_mod_p_of_LHypothesis hG Ldata hchar hW2y_compl
  have hW2_conj_y := W2conj_le_normalizer_U_of_LHypothesis Ldata hchar hW2y_compl
  -- §13 structural inputs (13.2.a/b, companion to `basic_structure`; Lane B / §13 group theory)
  obtain ⟨hW2_le_P, hQ_elemAb⟩ := S_field_model_structural_inputs hG hyp
  -- `W₂ ≤ N_G(Q)` is ungated: `W₂ ≤ W ≤ T` and `Q = T_F`
  have hW2_norm_Q : hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.Q : Set G) := by
    have hW2_le_W : hyp.base.W2 ≤ hyp.base.W := by
      rw [hyp.base.W_eq_join]; exact le_sup_right
    have hW_le_T : hyp.base.W ≤ hyp.base.T := by
      rw [hyp.base.W_eq_inter]; exact inf_le_right
    rw [hyp.base.Q_eq_TF]
    exact (hW2_le_W.trans hW_le_T).trans
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T)
  exact field_normalizer_of_U_characteristic_of_fpf hG hyp Ldata hmod hW2_le_P
    hQ_elemAb hW2_norm_Q y hyQ hW2_conj_y

/-- **Every subgroup of a finite cyclic group is characteristic.**  A subgroup `K` equals the
`|K|`-torsion `ker (powMonoidHom |K|) = {x | x ^ |K| = 1}`: it is contained in it (Lagrange:
`x ^ |K| = 1` for `x ∈ K`) and has the same cardinality (`|ker| = gcd(|C|, |K|) = |K|` as
`|K| ∣ |C|`).  The torsion is preserved by every automorphism `φ` since `φ x ^ d = φ (x ^ d)`,
so `K` is characteristic.  Used for the (14.12) `L ≅ M` case where `H` is cyclic. -/
theorem characteristic_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (K : Subgroup C) : K.Characteristic := by
  letI : CommGroup C := IsCyclic.commGroup
  have key : ∀ A : Subgroup C, A = (powMonoidHom (Nat.card A) : C →* C).ker := by
    intro A
    have hle : A ≤ (powMonoidHom (Nat.card A) : C →* C).ker := by
      intro a ha
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have h1 : (⟨a, ha⟩ : A) ^ Nat.card A = 1 := pow_card_eq_one'
      have h2 := congrArg (Subtype.val) h1
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
      exact h2
    have hdvd : Nat.card A ∣ Nat.card C := Subgroup.card_subgroup_dvd_card A
    have hcard : Nat.card (powMonoidHom (Nat.card A) : C →* C).ker = Nat.card A := by
      rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hdvd]
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
  rw [Subgroup.characteristic_iff_comap_eq]
  intro φ
  have hcard_eq : Nat.card ↥(K.comap φ.toMonoidHom) = Nat.card ↥K :=
    Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv (fun a => Subgroup.mem_comap))
  conv_lhs => rw [key (K.comap φ.toMonoidHom)]
  conv_rhs => rw [key K]
  rw [hcard_eq]

open scoped IsMulCommutative in
/-- **Peterfalvi (13.2.a) for `T`**: the `T`-side complement `V` is cyclic.  `V` is the abelian
Frobenius kernel of the type-I-over-`N_G(V)` configuration.  This is the `T`/`V`-side dual of the
`S`/`U`-side field-model cyclicity (`exists_pv_field_repr`, still to be built): once the dual Singer
representation `μ : V ↪ 𝔽_{q^p}^×` is constructed from `V` abelian via
`isSimpleModule_of_abelian_faithful_card`, `V` cyclic follows.  Used to transport `K = V` (14.11) to
`K` cyclic in `MHypothesis_kernel_cyclic`. -/
theorem V_cyclic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : IsCyclic ↥hyp.base.V := by
  letI : Fact hyp.base.q.Prime := ⟨hyp.base.q_prime⟩
  haveI : NeZero hyp.base.q := ⟨hyp.base.q_prime.ne_zero⟩
  haveI hTII : IsTypeII hyp.base.T := T_typeII hG hyp
  have hQea : IsElementaryAbelian hyp.base.q ↥hyp.base.Q := Q_elemAbelian_S hG hyp
  haveI hQcomm : IsMulCommutative ↥hyp.base.Q := IsMulCommutative.of_comm hQea.comm
  letI hVcomm : CommGroup ↥hyp.base.V :=
    { (inferInstance : Group ↥hyp.base.V) with
      mul_comm := fun a b =>
        (isMulCommutative_iff.mp
          (OddOrder.Peterfalvi.S15.isMulCommutative_V hG hyp.base hTII)) a b }
  -- `|V| = v = (q^p - 1)/(q - 1)`: `d = 1` from `D = V ⊓ C_G(Q) = ⊥` (13.12 dual), plus the
  -- `v`-value (14.4) `T_side_caseB_facts`.
  have hv_full : Nat.card ↥hyp.base.V =
      (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) := by
    have hDbot : hyp.base.D = ⊥ := by
      rw [hyp.base.D_eq]
      exact OddOrder.Peterfalvi.S15.V_inf_centralizer_Q_eq_bot hG hyp.base hTII
    have hd1 : hyp.base.d = 1 := by rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
    rw [hyp.base.card_V_eq_vd, hd1, mul_one]
    exact (T_side_caseB_facts hG hyp).2
  have hqsmul : ∀ x : Additive ↥hyp.base.Q, (hyp.base.q : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hQea.pow_eq_one x.toMul
  haveI hQmod : Module (ZMod hyp.base.q) (Additive ↥hyp.base.Q) :=
    AddCommGroup.zmodModule hqsmul
  -- the conjugation representation of `V` on `Additive ↥Q`
  let conjHom : ↥hyp.base.V →* MulAut ↥hyp.base.Q :=
    (Subgroup.normalizerMonoidHom (H := hyp.base.Q)).comp
      (Subgroup.inclusion (V_le_normalizer_Q hyp))
  let ρ : Representation (ZMod hyp.base.q) ↥hyp.base.V (Additive ↥hyp.base.Q) :=
    (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥hyp.base.Q hyp.base.q).comp conjHom
  have hρ_apply : ∀ (c : ↥hyp.base.V) (a : Additive ↥hyp.base.Q),
      ρ c a = Additive.ofMul ((conjHom c) (Additive.toMul a)) := fun _ _ => rfl
  letI hQmodAlg :
      Module (MonoidAlgebra (ZMod hyp.base.q) ↥hyp.base.V) (Additive ↥hyp.base.Q) :=
    Module.compHom (Additive ↥hyp.base.Q) (ρ.asAlgebraHom).toRingHom
  have hof_smul : ∀ (c : ↥hyp.base.V) (a : Additive ↥hyp.base.Q),
      MonoidAlgebra.of (ZMod hyp.base.q) ↥hyp.base.V c • a =
        Additive.ofMul ((conjHom c) (Additive.toMul a)) := by
    intro c a
    have h : MonoidAlgebra.of (ZMod hyp.base.q) ↥hyp.base.V c • a = ρ c a := by
      show (ρ.asAlgebraHom (MonoidAlgebra.of (ZMod hyp.base.q) ↥hyp.base.V c)) a = ρ c a
      rw [Representation.asAlgebraHom_of]
    rw [h, hρ_apply]
  haveI hNeZero : NeZero (Nat.card ↥hyp.base.V : ZMod hyp.base.q) := by
    refine ⟨fun h => ?_⟩
    rw [hv_full] at h
    have hdvd : hyp.base.q ∣ (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) :=
      (ZMod.natCast_eq_zero_iff _ _).mp h
    have hmod : (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) ≡ 1 [MOD hyp.base.q] := by
      have hsum_eq : ∑ k ∈ Finset.range hyp.base.p, hyp.base.q ^ k =
          (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) :=
        Nat.geomSum_eq hyp.base.q_prime.two_le _
      rw [← hsum_eq, show hyp.base.p = (hyp.base.p - 1) + 1 by
          have := hyp.base.p_prime.pos; omega, Finset.sum_range_succ']
      have hzero : (∑ k ∈ Finset.range (hyp.base.p - 1), hyp.base.q ^ (k + 1)) ≡ 0
          [MOD hyp.base.q] := by
        rw [Nat.modEq_zero_iff_dvd]
        exact Finset.dvd_sum fun k _ => dvd_pow_self hyp.base.q (Nat.succ_ne_zero k)
      simpa using hzero.add_right 1
    have hdvd1 : hyp.base.q ∣ 1 := by
      have h0 := (Nat.modEq_zero_iff_dvd).mpr hdvd
      have h01 := h0.symm.trans hmod
      rwa [Nat.modEq_iff_dvd', Nat.sub_zero] at h01
      omega
    exact absurd (Nat.le_of_dvd one_pos hdvd1) (by have := hyp.base.q_prime.two_le; omega)
  have hcardM : Nat.card (Additive ↥hyp.base.Q) = hyp.base.q ^ hyp.base.p :=
    OddOrder.Peterfalvi.S15.card_Q_eq hG hyp.base hTII
  have hfaith : ∀ c : ↥hyp.base.V,
      (∀ x : Additive ↥hyp.base.Q,
          MonoidAlgebra.of (ZMod hyp.base.q) ↥hyp.base.V c • x = x) → c = 1 := by
    intro c hc
    have hcomm : ∀ y : ↥hyp.base.Q, (c : G) * (y : G) = (y : G) * (c : G) := by
      intro y
      have h1 := hc (Additive.ofMul y)
      rw [hof_smul] at h1
      have h2 : (conjHom c) y = y := Additive.ofMul.injective (by simpa using h1)
      have h3 : (c : G) * (y : G) * (c : G)⁻¹ = (y : G) := congrArg Subtype.val h2
      rwa [mul_inv_eq_iff_eq_mul] at h3
    have hmem : (c : G) ∈ hyp.base.D := by
      rw [hyp.base.D_eq]
      exact ⟨c.2, Subgroup.mem_centralizer_iff.mpr (fun y hy => (hcomm ⟨y, hy⟩).symm)⟩
    have hDbot : hyp.base.D = ⊥ := by
      rw [hyp.base.D_eq]
      exact OddOrder.Peterfalvi.S15.V_inf_centralizer_Q_eq_bot hG hyp.base hTII
    rw [hDbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨e0, μ, hμinj, _⟩ :=
    OddOrder.RepresentationTheory.exists_galoisField_repr
      (C := ↥hyp.base.V) (M := Additive ↥hyp.base.Q)
      hyp.base.p_prime hyp.base.p_odd hcardM hv_full hfaith
  -- `μ : V ↪ 𝔽_{q^p}ˣ` is injective and the finite-field unit group is cyclic, so `V` is cyclic.
  exact isCyclic_of_injective μ hμinj

/-- **Peterfalvi (14.11)/(14.4)/(13.12)**: the Fitting kernel `K = M_F` of the type-I maximal
subgroup `M` over `N_G(V)` is cyclic.

This realizes the textbook route directly: by (14.11) `K = V` (`K_eq_V_index_pq`, the
(14.11.1)--(14.11.4) norm cascade), and `V` is cyclic (`V_cyclic`, 13.2.a for `T`), so `K` is
cyclic.  The remaining character-theoretic content is therefore isolated into the two named
obligations `K_eq_V_index_pq` (the (14.11) cascade, whose structural input is
`main_size_bounds_structural` and whose character input is `betaM_expansion` /
`generic_character_bound`) and `V_cyclic` (13.2.a for `T`).  Feeds the (14.12) reduction; the
`L ≅ M` case transports it to `H = L_F` purely structurally (`H_cyclic_of_L_conj_M`). -/
theorem MHypothesis_kernel_cyclic [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) : IsCyclic ↥Mdata.K := by
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hyp
  rw [(K_eq_V_index_pq _hG hyp Ldata Mdata).1]
  exact V_cyclic _hG hyp

/-- **Peterfalvi (14.12) structural input**: in the `L ≅ M` case, `H = L_F` is cyclic.  Since
`L ≅ M` (a conjugation `MulAut.conj g`), the maximal nilpotent normal Hall subgroup is
automorphism-equivariant (`maxNilpotentNormalHall_pointwise_smul`), so `H = L_F ≅ M_F = K`;
cyclicity of `K` is the §13/§14 obligation `MHypothesis_kernel_cyclic`.  This reduction is
purely structural — the character theory is confined to `MHypothesis_kernel_cyclic`. -/
theorem H_cyclic_of_L_conj_M [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp)
    (_hconj : ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M) :
    IsCyclic ↥Ldata.H := by
  obtain ⟨g, hg⟩ := _hconj
  haveI := MHypothesis_kernel_cyclic _hG hyp Mdata
  rw [Ldata.H_eq_LF]
  -- `M_F` is the `conj g`-image of `L_F`: `conj g • L_F = (conj g • L)_F = M_F = K`.
  have hmap : (maxNilpotentNormalHall Ldata.L).map ((MulAut.conj g : MulAut G) : G →* G)
      = Mdata.K := by
    rw [← pointwise_mulAut_smul_eq_map, maxNilpotentNormalHall_pointwise_smul, hg, Mdata.K_eq_MF]
  set e : ↥(maxNilpotentNormalHall Ldata.L) ≃* ↥Mdata.K :=
    (MulEquiv.subgroupMap (MulAut.conj g) (maxNilpotentNormalHall Ldata.L)).trans
      (MulEquiv.subgroupCongr hmap) with he
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

/-- **Peterfalvi (14.12)**: if `L` is conjugate to `M`, then the field-normalizer configuration
(14.2) holds.  Textbook reduction: `L ≅ M ⟹ H ≅ K` cyclic (`H_cyclic_of_L_conj_M`), so every
subgroup of `H` — in particular `U` — is characteristic (`characteristic_of_isCyclic`), and (14.7)
`field_normalizer_of_U_characteristic` applies.  Carries **no `sorry`**; gated only through the
named §13/§14 obligation `H_cyclic_of_L_conj_M`. -/
theorem field_normalizer_of_L_conj_M [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp)
    (hconj : ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M) :
    Nonempty (FieldNormalizerData hyp) := by
  haveI : IsCyclic ↥Ldata.H := H_cyclic_of_L_conj_M hG hyp Ldata Mdata hconj
  exact field_normalizer_of_U_characteristic hG hyp Ldata
    (characteristic_of_isCyclic (hyp.base.U.subgroupOf Ldata.H))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The two alternatives of **Peterfalvi (14.14)**. -/
structure OrthogonalitySwitchData {hyp : Hypothesis (G := G)}
    (nc : NonConjugateHypothesis hyp) where
  caseA : Prop
  caseA_bound :
    caseA →
      (((nc.h - 1 : ℕ) : ℚ) / (hyp.base.p * hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ))
  caseB : Prop
  caseB_params : caseB → hyp.base.q = 3 ∧ hyp.base.p = 5
  /-- **Peterfalvi (14.14.b), the case-(b) pairing**: in case (b) the L-side `β` pairs
  nontrivially with the M-side coherent test image — the first branch of the (7.9)
  dichotomy (`pairing_dichotomy`), packaged with its coherence bundles.  This carries
  the "(β_L^τ, ψ^{τ₁}) ≠ 0" half of Pf's case-(b) *definition*, which the `(q,p) = (3,5)`
  conclusion alone cannot recover; the (14.16) contradiction consumes it through
  `caseB_contradiction_data`. -/
  caseB_pairing :
    caseB →
      haveI := hyp.base.finiteG
      ∀ (hG : OddOrder.BG.IsMinimalSimpleOdd G),
      ∃ (dataL : TypeICoherent78Data nc.Ldata.L) (dataM : TypeICoherent78Data nc.Mdata.M),
        ClassFunction.inner
          ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal nc.Mdata.M_maximal
              nc.not_conj).first.beta)
          ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal nc.Mdata.M_maximal
              nc.not_conj).secondZetaImage) ≠ 0

namespace CaseBForSData

/-- **Peterfalvi (14.15)**: the congruence part of the non-full branch.  From
`h = u * x`, the congruence `h ≡ 1 mod p` supplied by (14.5), and the
fixed-point-free congruence `x ≡ 1 mod q`, the divided cyclotomic formula gives
`x ≡ q mod p`; hence `x = q + n p` for some `n`, and then `n ≡ 1 mod q`. -/
theorem exists_x_decomposition_of_nonfull_card_congruences
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (Sdata : CaseBForSData hyp)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    {x : ℕ} (hh_eq : nc.h = hyp.base.u * x)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hx_mod_q : x ≡ 1 [MOD hyp.base.q]) :
    ∃ n : ℕ, x = hyp.base.q + n * hyp.base.p ∧ n ≡ 1 [MOD hyp.base.q] := by
  let C : ℕ := (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)
  have hmod : hyp.base.p ≡ 1 [MOD hyp.base.q] := by
    by_contra hnot_mod
    exact hu_not_full (Sdata.u_eq_of_not_modEq_one hnot_mod)
  have hC_dvd : hyp.base.q ∣ C := by
    dsimp [C]
    exact OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_of_modEq_one
      hyp.base.p_prime hmod
  have hu_div : hyp.base.u = C / hyp.base.q := by
    rw [Sdata.u_eq_of_p_modEq_one hmod]
    dsimp [C]
    rw [Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm (hyp.base.p - 1) hyp.base.q]
  have hq_u : hyp.base.q * hyp.base.u = C := by
    rw [hu_div, Nat.mul_comm, Nat.div_mul_cancel hC_dvd]
  have hq_h : hyp.base.q * nc.h = C * x := by
    rw [hh_eq, ← mul_assoc, hq_u]
  have hC_mod_p : C ≡ 1 [MOD hyp.base.p] := by
    dsimp [C]
    exact cyclotomic_quotient_modEq_one_mod_base
      hyp.base.p_prime.two_le hyp.base.q_prime.pos
  have hqh_mod : hyp.base.q * nc.h ≡ hyp.base.q [MOD hyp.base.p] := by
    simpa [mul_one] using hh_mod_p.mul_left hyp.base.q
  rw [hq_h] at hqh_mod
  have hCx_mod : C * x ≡ x [MOD hyp.base.p] := by
    simpa [one_mul] using hC_mod_p.mul_right x
  have hx_mod_p : x ≡ hyp.base.q [MOD hyp.base.p] := hCx_mod.symm.trans hqh_mod
  have hq_le_x : hyp.base.q ≤ x := by
    by_contra hnot
    have hx_lt_q : x < hyp.base.q := Nat.lt_of_not_ge hnot
    have hx_eq_q : x = hyp.base.q :=
      Nat.ModEq.eq_of_lt_of_lt hx_mod_p (lt_trans hx_lt_q hyp.q_lt_p) hyp.q_lt_p
    omega
  rcases (Nat.modEq_iff_exists_eq_add hq_le_x).mp hx_mod_p.symm with
    ⟨n, hx_eq_add⟩
  have hx_eq : x = hyp.base.q + n * hyp.base.p := by
    simpa [mul_comm] using hx_eq_add
  have hnp_mod : n * hyp.base.p ≡ n [MOD hyp.base.q] := by
    simpa [mul_one] using hmod.mul_left n
  have hq_zero : hyp.base.q ≡ 0 [MOD hyp.base.q] := by
    rw [Nat.modEq_zero_iff_dvd]
  have hx_mod_n : x ≡ n [MOD hyp.base.q] := by
    rw [hx_eq]
    simpa using hq_zero.add hnp_mod
  exact ⟨n, hx_eq, hx_mod_n.symm.trans hx_mod_q⟩

/-- **Peterfalvi (14.15)**: in the non-full S-side cyclotomic branch, the
`h = u * x` decomposition and the fixed-point-free congruence estimate give the
lower comparison `p^q < h - 1`.  The proof follows the paragraph
`x > p q`, hence `h > p * (p^q - 1)/(p - 1) > p^q + 1`, with the divided
cyclotomic formula for `u` supplied by **Peterfalvi (13.15)**. -/
theorem p_pow_lt_h_sub_one_of_nonfull_decomposition
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (Sdata : CaseBForSData hyp)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    {x n : ℕ} (hh_eq : nc.h = hyp.base.u * x)
    (hx_eq : x = hyp.base.q + n * hyp.base.p)
    (hn_mod : n ≡ 1 [MOD hyp.base.q]) (hx_odd : Odd x) :
    hyp.base.p ^ hyp.base.q < nc.h - 1 := by
  let C : ℕ := (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)
  have hmod : hyp.base.p ≡ 1 [MOD hyp.base.q] := by
    by_contra hnot_mod
    exact hu_not_full (Sdata.u_eq_of_not_modEq_one hnot_mod)
  have hC_dvd : hyp.base.q ∣ C := by
    dsimp [C]
    exact OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_of_modEq_one
      hyp.base.p_prime hmod
  have hu_div : hyp.base.u = C / hyp.base.q := by
    rw [Sdata.u_eq_of_p_modEq_one hmod]
    dsimp [C]
    rw [Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm (hyp.base.p - 1) hyp.base.q]
  have hq_u : hyp.base.q * hyp.base.u = C := by
    rw [hu_div, Nat.mul_comm, Nat.div_mul_cancel hC_dvd]
  have hC_sub_ge : hyp.base.p ^ (hyp.base.q - 1) ≤ C - 1 := by
    have hleQ := cyclotomic_quotient_sub_one_ge_pow_pred
      (q := hyp.base.p) (p := hyp.base.q)
      hyp.base.p_prime.two_le hyp.base.q_prime.two_le
    dsimp [C]
    exact_mod_cast hleQ
  have hpow_pred_pos : 0 < hyp.base.p ^ (hyp.base.q - 1) :=
    pow_pos hyp.base.p_prime.pos _
  have hC_ge : hyp.base.p ^ (hyp.base.q - 1) + 1 ≤ C := by omega
  have hC_pos : 0 < C := by omega
  have hp_mul_C_gt : hyp.base.p ^ hyp.base.q + 1 < hyp.base.p * C := by
    have hq_pos : 0 < hyp.base.q := hyp.base.q_prime.pos
    have hmul_le :
        hyp.base.p * (hyp.base.p ^ (hyp.base.q - 1) + 1) ≤
          hyp.base.p * C :=
      Nat.mul_le_mul_left hyp.base.p hC_ge
    have hpow_mul :
        hyp.base.p * hyp.base.p ^ (hyp.base.q - 1) = hyp.base.p ^ hyp.base.q := by
      calc
        hyp.base.p * hyp.base.p ^ (hyp.base.q - 1) =
            hyp.base.p ^ (hyp.base.q - 1) * hyp.base.p := by rw [mul_comm]
        _ = hyp.base.p ^ ((hyp.base.q - 1) + 1) := by rw [pow_succ]
        _ = hyp.base.p ^ hyp.base.q := by rw [show hyp.base.q - 1 + 1 = hyp.base.q by omega]
    have hle : hyp.base.p ^ hyp.base.q + hyp.base.p ≤ hyp.base.p * C := by
      calc
        hyp.base.p ^ hyp.base.q + hyp.base.p =
            hyp.base.p * (hyp.base.p ^ (hyp.base.q - 1) + 1) := by
          rw [mul_add, mul_one, hpow_mul]
        _ ≤ hyp.base.p * C := hmul_le
    nlinarith [hle, hyp.base.p_prime.one_lt]
  have hx_min : hyp.base.q + (1 + hyp.base.q) * hyp.base.p ≤ x :=
    hyp.x_ge_caseA_min_of_decomposition_modEq_and_odd hx_eq hn_mod hx_odd
  have hx_gt_pq : hyp.base.p * hyp.base.q < x := by
    nlinarith [hx_min, hyp.base.p_prime.pos, hyp.base.q_prime.pos]
  have hq_h : hyp.base.q * nc.h = C * x := by
    rw [hh_eq, ← mul_assoc, hq_u]
  have hpC_lt_h : hyp.base.p * C < nc.h := by
    have hCx_gt : C * (hyp.base.p * hyp.base.q) < C * x :=
      Nat.mul_lt_mul_of_pos_left hx_gt_pq hC_pos
    have hq_lt : hyp.base.q * (hyp.base.p * C) < hyp.base.q * nc.h := by
      calc
        hyp.base.q * (hyp.base.p * C) = C * (hyp.base.p * hyp.base.q) := by ring
        _ < C * x := hCx_gt
        _ = hyp.base.q * nc.h := hq_h.symm
    exact Nat.lt_of_mul_lt_mul_left hq_lt
  have hpq_add_lt_h : hyp.base.p ^ hyp.base.q + 1 < nc.h :=
    lt_trans hp_mul_C_gt hpC_lt_h
  omega

end CaseBForSData

namespace OrthogonalitySwitchData

/-- The exceptional branch in **Peterfalvi (14.14)** is already in the
`q = 3` situation, so the Section 16 `m > 49/100` bound is available for later
use in the final comparison. -/
theorem m_gt_49_hundredths_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (hcaseB : data.caseB) :
    hyp.base.m > (49 / 100 : ℚ) := by
  exact hyp.m_gt_49_hundredths_of_q_eq_three (data.caseB_params hcaseB).1

/-- In the exceptional branch of **Peterfalvi (14.14)**, the S-side congruence
branch `p ≡ 1 mod q` is impossible: the branch has `(q,p) = (3,5)`, and
`5` is not `1 mod 3`. -/
theorem not_p_modEq_one_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (hcaseB : data.caseB) :
    ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] := by
  intro hmod
  have hparams := data.caseB_params hcaseB
  have hmod' : 5 ≡ 1 [MOD 3] := by
    simpa [hparams.1, hparams.2] using hmod
  unfold Nat.ModEq at hmod'
  norm_num at hmod'

/-- In the exceptional branch of **Peterfalvi (14.14)**, the S-side case-(9.7.b)
order data is forced into its full cyclotomic branch.  This is the consumer form
needed for **Peterfalvi (14.15)**. -/
theorem u_eq_full_cyclotomic_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
  Sdata.u_eq_of_not_modEq_one (data.not_p_modEq_one_of_caseB hcaseB)

/-- Numerically, the exceptional branch of **Peterfalvi (14.14)** gives
`u = (5^3 - 1)/(5 - 1) = 31`, once the S-side case-(9.7.b) order data has been
materialized. -/
theorem u_eq_thirty_one_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB) :
    hyp.base.u = 31 := by
  have hparams := data.caseB_params hcaseB
  have hu := data.u_eq_full_cyclotomic_of_caseB Sdata hcaseB
  rw [hparams.1, hparams.2] at hu
  norm_num at hu
  exact hu

/-- Numerically, the exceptional branch of **Peterfalvi (14.14)** gives
`v = (3^5 - 1)/(3 - 1) = 121`, once the T-side case-(9.7.b) order data from
(14.4) has been materialized. -/
theorem v_eq_one_twenty_one_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (Tdata : CaseBForTData hyp) (hcaseB : data.caseB) :
    hyp.base.v = 121 := by
  have hparams := data.caseB_params hcaseB
  rw [Tdata.v_eq, hparams.1, hparams.2]
  norm_num

/-- **Peterfalvi (14.15)**: the case-(a) bound of (14.14) turns a lower
bound `p^q < h - 1` into the key inequality `p^(q - 2) < q^2`. -/
theorem p_pow_q_sub_two_lt_q_sq_of_p_pow_lt_h_sub_one
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseA : data.caseA)
    (hpow_lt_h : hyp.base.p ^ hyp.base.q < nc.h - 1) :
    hyp.base.p ^ (hyp.base.q - 2) < hyp.base.q ^ 2 := by
  have hbound := data.caseA_bound hcaseA
  have hpq_pos_nat : 0 < hyp.base.p * hyp.base.q :=
    Nat.mul_pos hyp.base.p_prime.pos hyp.base.q_prime.pos
  have hpq_posQ : (0 : ℚ) < (hyp.base.p * hyp.base.q : ℚ) := by
    exact_mod_cast hpq_pos_nat
  have hmul := mul_le_mul_of_nonneg_right hbound (le_of_lt hpq_posQ)
  have hleQ : ((nc.h - 1 : ℕ) : ℚ) ≤
      (hyp.base.p * hyp.base.q : ℚ) * ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) := by
    rw [div_mul_cancel₀ _ (ne_of_gt hpq_posQ)] at hmul
    nlinarith [hmul]
  have hsub_ltQ : ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) <
      (hyp.base.p * hyp.base.q : ℚ) := by
    have hsub_lt : hyp.base.p * hyp.base.q - 1 < hyp.base.p * hyp.base.q := by omega
    exact_mod_cast hsub_lt
  have hpow_ltQ : ((hyp.base.p ^ hyp.base.q : ℕ) : ℚ) < ((nc.h - 1 : ℕ) : ℚ) := by
    exact_mod_cast hpow_lt_h
  have hright_lt_sq :
      (hyp.base.p * hyp.base.q : ℚ) * ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) <
        (hyp.base.p * hyp.base.q : ℚ) * (hyp.base.p * hyp.base.q : ℚ) :=
    mul_lt_mul_of_pos_left hsub_ltQ hpq_posQ
  have hpq_sqQ : ((hyp.base.p ^ hyp.base.q : ℕ) : ℚ) <
      ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ^ 2 := by
    calc
      ((hyp.base.p ^ hyp.base.q : ℕ) : ℚ) < ((nc.h - 1 : ℕ) : ℚ) := hpow_ltQ
      _ ≤ (hyp.base.p * hyp.base.q : ℚ) *
          ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) := hleQ
      _ < (hyp.base.p * hyp.base.q : ℚ) * (hyp.base.p * hyp.base.q : ℚ) :=
        hright_lt_sq
      _ = ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ^ 2 := by
        norm_num [Nat.cast_mul, pow_two]
  have hpq_sq_nat : hyp.base.p ^ hyp.base.q < (hyp.base.p * hyp.base.q) ^ 2 := by
    exact_mod_cast hpq_sqQ
  exact p_pow_sub_two_lt_q_sq_of_pow_lt_mul_sq hyp.base.q_prime.two_le hpq_sq_nat

/-- **Peterfalvi (14.15)**: the final numerical contradiction for the
case-(a) branch of (14.14). Once the bound is specialized to `(q,p) = (3,7)`,
it is incompatible with `h ≥ 31 * 19`. -/
theorem caseA_bound_contradiction_of_h_ge_thirty_one_mul_nineteen
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseA : data.caseA)
    (hq3 : hyp.base.q = 3) (hp7 : hyp.base.p = 7) (hh : 31 * 19 ≤ nc.h) :
    False := by
  have hbound := data.caseA_bound hcaseA
  rw [hq3, hp7] at hbound
  norm_num at hbound
  have hleQ : ((nc.h - 1 : ℕ) : ℚ) ≤ 420 := by nlinarith [hbound]
  have hle : nc.h - 1 ≤ 420 := by exact_mod_cast hleQ
  have hge : 588 ≤ nc.h - 1 := by omega
  omega

/-- **Peterfalvi (14.15)**: arithmetic spine of the non-full cyclotomic
case-(a) branch. Once the preceding group-theoretic part of the paragraph has
supplied `p ≡ 1 mod q`, the lower comparison `p^q < h - 1`, and
`h ≥ 31 * 19`, the case-(a) bound forces `q = 3`, then `p = 7`, and finally
the numerical contradiction `31 * 19 - 1 ≤ 20 * 21`. -/
theorem caseA_contradiction_of_p_modEq_one_and_h_bounds
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseA : data.caseA)
    (hmod : hyp.base.p ≡ 1 [MOD hyp.base.q])
    (hpow_lt_h : hyp.base.p ^ hyp.base.q < nc.h - 1)
    (hh : 31 * 19 ≤ nc.h) :
    False := by
  have hpq2 := data.p_pow_q_sub_two_lt_q_sq_of_p_pow_lt_h_sub_one hcaseA hpow_lt_h
  have hq3 := hyp.q_eq_three_of_p_pow_q_sub_two_lt_q_sq hpq2
  have hp_lt_q_sq : hyp.base.p < hyp.base.q ^ 2 := by
    simpa [hq3] using hpq2
  have hp7 :=
    hyp.p_eq_seven_of_q_eq_three_modEq_one_and_lt_q_sq hq3 hmod hp_lt_q_sq
  exact data.caseA_bound_contradiction_of_h_ge_thirty_one_mul_nineteen
    hcaseA hq3 hp7 hh

/-- **Peterfalvi (14.15)**: the non-full cyclotomic branch of the case-(a)
comparison.  If `u` is not the full cyclotomic quotient, then the S-side
case-(9.7.b) order formula puts us in the `p ≡ 1 mod q` branch and gives the
divided cyclotomic value of `u`.  Together with the `h = u * x` decomposition
and the fixed-point-free congruence/parity estimate for `x`, the case-(a) bound
forces `q = 3`, `p = 7`, `u = 19`, `x ≥ 31`, and hence the final numerical
contradiction. -/
theorem caseA_contradiction_of_nonfull_u_data
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    {x n : ℕ} (hh_eq : nc.h = hyp.base.u * x)
    (hx_eq : x = hyp.base.q + n * hyp.base.p)
    (hn_mod : n ≡ 1 [MOD hyp.base.q]) (hx_odd : Odd x) :
    False := by
  have hmod : hyp.base.p ≡ 1 [MOD hyp.base.q] := by
    by_contra hnot_mod
    exact hu_not_full (Sdata.u_eq_of_not_modEq_one hnot_mod)
  have hpow_lt_h :=
    Sdata.p_pow_lt_h_sub_one_of_nonfull_decomposition
      hu_not_full hh_eq hx_eq hn_mod hx_odd
  have hpq2 := data.p_pow_q_sub_two_lt_q_sq_of_p_pow_lt_h_sub_one hcaseA hpow_lt_h
  have hq3 := hyp.q_eq_three_of_p_pow_q_sub_two_lt_q_sq hpq2
  have hp_lt_q_sq : hyp.base.p < hyp.base.q ^ 2 := by
    simpa [hq3] using hpq2
  have hp7 :=
    hyp.p_eq_seven_of_q_eq_three_modEq_one_and_lt_q_sq hq3 hmod hp_lt_q_sq
  have hu19 : hyp.base.u = 19 := by
    have hu := Sdata.u_eq_of_p_modEq_one hmod
    rw [hq3, hp7] at hu
    norm_num at hu
    exact hu
  have hx_min : hyp.base.q + (1 + hyp.base.q) * hyp.base.p ≤ x :=
    hyp.x_ge_caseA_min_of_decomposition_modEq_and_odd hx_eq hn_mod hx_odd
  have hx31 : 31 ≤ x := by
    have hx := hx_min
    rw [hq3, hp7] at hx
    norm_num at hx
    exact hx
  have hh_ge : 31 * 19 ≤ nc.h := by
    rw [hh_eq, hu19]
    nlinarith [hx31]
  exact data.caseA_bound_contradiction_of_h_ge_thirty_one_mul_nineteen
    hcaseA hq3 hp7 hh_ge

/-- **Peterfalvi (14.15)**: consumer form of the non-full case-(a) branch with
only the cardinal/congruence inputs left from (14.5) and the fixed-point-free
`W₁` action.  The congruence theorem above derives `x = q + n p` and
`n ≡ 1 mod q`; the numerical part then closes the case-(a) contradiction. -/
theorem caseA_contradiction_of_nonfull_card_congruences
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    {x : ℕ} (hh_eq : nc.h = hyp.base.u * x)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hx_mod_q : x ≡ 1 [MOD hyp.base.q]) (hx_odd : Odd x) :
    False := by
  rcases Sdata.exists_x_decomposition_of_nonfull_card_congruences
      hu_not_full hh_eq hh_mod_p hx_mod_q with ⟨n, hx_eq, hn_mod⟩
  exact data.caseA_contradiction_of_nonfull_u_data
    Sdata hcaseA hu_not_full hh_eq hx_eq hn_mod hx_odd

/-- **Peterfalvi (14.15)**: quotient form of the non-full case-(a) branch.
Once the group-theoretic part of (14.5) has supplied `u ∣ h`, `h ≡ 1 mod p`,
and the fixed-point-free congruence for the quotient `x = h / u`, the oddness
of `x` is no longer an input: it follows from `h = |H|` in the ambient
odd-order group. -/
theorem caseA_contradiction_of_nonfull_card_divisibility
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hx_mod_q_of_quotient :
      ∀ x : ℕ, nc.h = hyp.base.u * x → x ≡ 1 [MOD hyp.base.q]) :
    False := by
  rcases hu_dvd_h with ⟨x, hh_eq⟩
  have hx_mod_q : x ≡ 1 [MOD hyp.base.q] := hx_mod_q_of_quotient x hh_eq
  have hh_odd : Odd nc.h := nc.h_odd _hG
  have hux_odd : Odd (hyp.base.u * x) := by
    rw [← hh_eq]
    exact hh_odd
  have hx_odd : Odd x := (Nat.odd_mul.mp hux_odd).2
  exact data.caseA_contradiction_of_nonfull_card_congruences
    Sdata hcaseA hu_not_full hh_eq hh_mod_p hx_mod_q hx_odd

/-- **Peterfalvi (14.15)**: fixed-point-free cardinal-congruence form of the
non-full case-(a) branch.  If the `W₁` action gives both `h ≡ 1 mod q` and
`u ≡ 1 mod q`, then for any quotient decomposition `h = u * x` the quotient
itself satisfies `x ≡ 1 mod q`, which is the congruence used in the displayed
`x = q + n p` calculation. -/
theorem caseA_contradiction_of_nonfull_fpf_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q]) :
    False := by
  exact data.caseA_contradiction_of_nonfull_card_divisibility
    _hG Sdata hcaseA hu_not_full hu_dvd_h hh_mod_p (fun x hh_eq => by
      have hux_mod_q : hyp.base.u * x ≡ x [MOD hyp.base.q] := by
        simpa [one_mul] using hu_mod_q.mul_right x
      have hh_mod_x : nc.h ≡ x [MOD hyp.base.q] := by
        rw [hh_eq]
        exact hux_mod_q
      exact hh_mod_x.symm.trans hh_mod_q)

/-- **Peterfalvi (14.16)**: the case-(a) branch cannot occur when `H` is
properly larger than `U`, once (14.15) and the fixed-point-free cardinal
congruences have been materialized.  The proof follows Peterfalvi's paragraph:
`x ≡ 1 mod p q` and odd `x ≠ 1` give `x > 2 p q`; the case-(a) bound then
forces `2 u < p q`, contradicting `u ≡ 1 mod p q` and `u > 2 q`. -/
theorem caseA_contradiction_of_full_u_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_full : hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q])
    (hx_ne_one_of_quotient : ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1) :
    False := by
  rcases hu_dvd_h with ⟨x, hh_eq⟩
  have hu_mod_p : hyp.base.u ≡ 1 [MOD hyp.base.p] := by
    rw [hu_full]
    exact cyclotomic_quotient_modEq_one_mod_base
      hyp.base.p_prime.two_le hyp.base.q_prime.pos
  have hx_mod_p : x ≡ 1 [MOD hyp.base.p] := by
    have hux_mod_p : hyp.base.u * x ≡ x [MOD hyp.base.p] := by
      simpa [one_mul] using hu_mod_p.mul_right x
    have hh_mod_x : nc.h ≡ x [MOD hyp.base.p] := by
      rw [hh_eq]
      exact hux_mod_p
    exact hh_mod_x.symm.trans hh_mod_p
  have hx_mod_q : x ≡ 1 [MOD hyp.base.q] := by
    have hux_mod_q : hyp.base.u * x ≡ x [MOD hyp.base.q] := by
      simpa [one_mul] using hu_mod_q.mul_right x
    have hh_mod_x : nc.h ≡ x [MOD hyp.base.q] := by
      rw [hh_eq]
      exact hux_mod_q
    exact hh_mod_x.symm.trans hh_mod_q
  have hh_odd : Odd nc.h := nc.h_odd _hG
  have hux_odd : Odd (hyp.base.u * x) := by
    rw [← hh_eq]
    exact hh_odd
  have hx_odd : Odd x := (Nat.odd_mul.mp hux_odd).2
  have hx_gt : 2 * (hyp.base.p * hyp.base.q) < x :=
    hyp.quotient_gt_two_mul_pq_of_modEq_one_mod_p_and_q
      hx_mod_p hx_mod_q hx_odd (hx_ne_one_of_quotient x hh_eq)
  have hu_pos : 0 < hyp.base.u := by
    have h2q := Sdata.two_q_lt_u
    omega
  have h_lower : 2 * (hyp.base.p * hyp.base.q) * hyp.base.u < nc.h := by
    have hmul :
        hyp.base.u * (2 * (hyp.base.p * hyp.base.q)) < hyp.base.u * x :=
      Nat.mul_lt_mul_of_pos_left hx_gt hu_pos
    rw [hh_eq]
    nlinarith
  have hbound := data.caseA_bound hcaseA
  have hpq_pos_nat : 0 < hyp.base.p * hyp.base.q :=
    Nat.mul_pos hyp.base.p_prime.pos hyp.base.q_prime.pos
  have hpq_posQ : (0 : ℚ) < (hyp.base.p * hyp.base.q : ℚ) := by
    exact_mod_cast hpq_pos_nat
  have hmul_bound := mul_le_mul_of_nonneg_right hbound (le_of_lt hpq_posQ)
  have h_upper_Q : ((nc.h - 1 : ℕ) : ℚ) ≤
      (hyp.base.p * hyp.base.q : ℚ) *
        ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) := by
    rw [div_mul_cancel₀ _ (ne_of_gt hpq_posQ)] at hmul_bound
    nlinarith [hmul_bound]
  have h_upper_sub : nc.h - 1 ≤
      (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q - 1) := by
    exact_mod_cast h_upper_Q
  have h_upper : nc.h ≤
      (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q - 1) + 1 := by
    omega
  have htwo_u_lt_pq : 2 * hyp.base.u < hyp.base.p * hyp.base.q := by
    by_contra hnot
    have hpq_le_2u : hyp.base.p * hyp.base.q ≤ 2 * hyp.base.u :=
      Nat.le_of_not_gt hnot
    have hpq_sq_le :
        (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) ≤
          (hyp.base.p * hyp.base.q) * (2 * hyp.base.u) :=
      Nat.mul_le_mul_left (hyp.base.p * hyp.base.q) hpq_le_2u
    have hupper_lt_sq :
        (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q - 1) + 1 <
          (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) := by
      have hpq_gt_one : 1 < hyp.base.p * hyp.base.q := by
        nlinarith [hyp.base.p_prime.one_lt, hyp.base.q_prime.one_lt]
      have hs :
          (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) =
            (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q - 1) +
              (hyp.base.p * hyp.base.q) := by
        rw [← Nat.mul_succ]
        have : (hyp.base.p * hyp.base.q - 1).succ = hyp.base.p * hyp.base.q := by
          omega
        rw [this]
      rw [hs]
      omega
    nlinarith [hpq_sq_le, h_lower, h_upper, hupper_lt_sq]
  have hpq_coprime : Nat.Coprime hyp.base.p hyp.base.q :=
    (Nat.coprime_primes hyp.base.p_prime hyp.base.q_prime).mpr hyp.p_ne_q
  have hu_mod_pq : hyp.base.u ≡ 1 [MOD hyp.base.p * hyp.base.q] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hpq_coprime).mp ⟨hu_mod_p, hu_mod_q⟩
  have hu_gt_one : 1 < hyp.base.u := by
    have h2q := Sdata.two_q_lt_u
    nlinarith [hyp.base.q_prime.one_lt]
  rcases (Nat.modEq_iff_exists_eq_add (le_of_lt hu_gt_one)).mp hu_mod_pq.symm with
    ⟨t, hu_eq⟩
  have ht_ne_zero : t ≠ 0 := by
    intro ht0
    rw [ht0, mul_zero, add_zero] at hu_eq
    omega
  have ht_ge_one : 1 ≤ t := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ht_ne_zero)
  have hu_ge_pq_add_one : hyp.base.p * hyp.base.q + 1 ≤ hyp.base.u := by
    rw [hu_eq]
    have hmul := Nat.mul_le_mul_left (hyp.base.p * hyp.base.q) ht_ge_one
    nlinarith
  nlinarith [htwo_u_lt_pq, hu_ge_pq_add_one]

/-- **Peterfalvi (14.16)**: cardinal/congruence lower bound for the proper
`H > U` alternative.  From `h = u x`, the full cyclotomic value for `u`, and
the fixed-point-free congruences, the quotient satisfies `x ≡ 1 mod p q`; if
`x ≠ 1`, oddness forces `x > 2 p q`, hence `h > 2 p q u`. -/
theorem h_gt_two_mul_pq_mul_u_of_full_u_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (hu_full : hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q])
    (hx_ne_one_of_quotient : ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1) :
    2 * (hyp.base.p * hyp.base.q) * hyp.base.u < nc.h := by
  rcases hu_dvd_h with ⟨x, hh_eq⟩
  have hu_mod_p : hyp.base.u ≡ 1 [MOD hyp.base.p] := by
    rw [hu_full]
    exact cyclotomic_quotient_modEq_one_mod_base
      hyp.base.p_prime.two_le hyp.base.q_prime.pos
  have hx_mod_p : x ≡ 1 [MOD hyp.base.p] := by
    have hux_mod_p : hyp.base.u * x ≡ x [MOD hyp.base.p] := by
      simpa [one_mul] using hu_mod_p.mul_right x
    have hh_mod_x : nc.h ≡ x [MOD hyp.base.p] := by
      rw [hh_eq]
      exact hux_mod_p
    exact hh_mod_x.symm.trans hh_mod_p
  have hx_mod_q : x ≡ 1 [MOD hyp.base.q] := by
    have hux_mod_q : hyp.base.u * x ≡ x [MOD hyp.base.q] := by
      simpa [one_mul] using hu_mod_q.mul_right x
    have hh_mod_x : nc.h ≡ x [MOD hyp.base.q] := by
      rw [hh_eq]
      exact hux_mod_q
    exact hh_mod_x.symm.trans hh_mod_q
  have hh_odd : Odd nc.h := nc.h_odd _hG
  have hux_odd : Odd (hyp.base.u * x) := by
    rw [← hh_eq]
    exact hh_odd
  have hx_odd : Odd x := (Nat.odd_mul.mp hux_odd).2
  have hx_gt : 2 * (hyp.base.p * hyp.base.q) < x :=
    hyp.quotient_gt_two_mul_pq_of_modEq_one_mod_p_and_q
      hx_mod_p hx_mod_q hx_odd (hx_ne_one_of_quotient x hh_eq)
  have hu_pos : 0 < hyp.base.u := Odd.pos (Nat.odd_mul.mp hux_odd).1
  have hmul :
      hyp.base.u * (2 * (hyp.base.p * hyp.base.q)) < hyp.base.u * x :=
    Nat.mul_lt_mul_of_pos_left hx_gt hu_pos
  rw [hh_eq]
  nlinarith

/-- **Peterfalvi (14.16)**: the numerical gap in the exceptional branch.  If
case-(b) has `(q,p)=(3,5)` and `H > U`, then the lower bound `h > 2 p q u`
gives `(h - 1)/(p q) > (v - 1)/p`; the concrete values `u=31`, `v=121` also
give `(v - 1)/p > (u - 1)/q`. -/
theorem caseB_gap_inequalities_of_h_gt_two_mul_pq_mul_u
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Tdata : CaseBForTData hyp)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB)
    (hh_lower : 2 * (hyp.base.p * hyp.base.q) * hyp.base.u < nc.h) :
    (((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  have hparams := data.caseB_params hcaseB
  have hu31 := data.u_eq_thirty_one_of_caseB Sdata hcaseB
  have hv121 := data.v_eq_one_twenty_one_of_caseB Tdata hcaseB
  have hh930 : 930 < nc.h := by
    have h := hh_lower
    rw [hparams.1, hparams.2, hu31] at h
    norm_num at h
    exact h
  have hh_sub_ge : 930 ≤ nc.h - 1 := by omega
  constructor
  · have hgeQ : (930 : ℚ) ≤ ((nc.h - 1 : ℕ) : ℚ) := by
      exact_mod_cast hh_sub_ge
    have hgt : (24 : ℚ) < ((nc.h - 1 : ℕ) : ℚ) / 15 := by
      nlinarith
    rw [hparams.1, hparams.2, hv121]
    norm_num
    exact hgt
  · rw [hparams.1, hparams.2, hu31, hv121]
    norm_num

/-- **Peterfalvi (14.16)**: the S-side gap in the exceptional branch
excludes case-(c1) of (13.19.c).  After identifying the Type-I kernel with the
current `H` and the complement index with `p q`, the inequality
`(h - 1)/(p q) > (v - 1)/p > (u - 1)/q` is exactly the strict negation of the
case-(c1) bound, so the parity alternative (c2) must hold. -/
theorem typeI_caseC2_of_caseB_sSide_gap
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L)
    (hcases : orth.caseC1 ∨ orth.caseC2)
    (hH : Nat.card ↥orth.typeISetup.H = nc.h)
    (he : orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    orth.caseC2 := by
  apply orth.caseC2_of_gap hcases
  rw [hH, he]
  exact hvu.trans hhv

/-- **Peterfalvi (14.16)**: the T-side gap in the exceptional branch excludes
the dual case-(c1) of (13.19.c).  This is the symmetric input producing the
`eta_i0` parity congruences. -/
theorem typeI_caseC2_of_caseB_tSide_gap
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L)
    (hcases : orth.caseC1_dual ∨ orth.caseC2_dual)
    (hH : Nat.card ↥orth.typeISetup.H = nc.h)
    (he : orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) :
    orth.caseC2_dual := by
  apply orth.caseC2_dual_of_gap hcases
  rw [hH, he]
  exact hhv

/-- **Peterfalvi (14.16)**: the two numerical gaps in case-(b) force both
(13.19.c2) parity alternatives, the S-side one for the `eta_0j` row and the
T-side swapped one for the `eta_i0` column. -/
theorem typeI_caseC2_pair_of_caseB_gap
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L)
    (hcases : orth.caseC1 ∨ orth.caseC2)
    (hcases_dual : orth.caseC1_dual ∨ orth.caseC2_dual)
    (hH : Nat.card ↥orth.typeISetup.H = nc.h)
    (he : orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    orth.caseC2 ∧ orth.caseC2_dual := by
  exact ⟨typeI_caseC2_of_caseB_sSide_gap orth hcases hH he hhv hvu,
    typeI_caseC2_of_caseB_tSide_gap orth hcases_dual hH he hhv⟩

/-- **Peterfalvi (14.16)**: after the case-(b) gaps force both alternatives
(13.19.c2), the usable character output is odd integer pairing on the two
zero-axis families `eta_0j` and `eta_i0`. -/
theorem typeI_eta_axes_odd_of_caseB_gap
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L)
    (hcases : orth.caseC1 ∨ orth.caseC2)
    (hcases_dual : orth.caseC1_dual ∨ orth.caseC2_dual)
    (hH : Nat.card ↥orth.typeISetup.H = nc.h)
    (he : orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    (∀ j : Fin hyp.base.p, (j : ℕ) ≠ 0 →
        OddOrder.Peterfalvi.S15.OddIntegerInner orth.betaL
          (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j)) ∧
      (∀ i : Fin hyp.base.q, (i : ℕ) ≠ 0 →
        OddOrder.Peterfalvi.S15.OddIntegerInner orth.betaL
          (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)) := by
  exact orth.eta_axes_odd_of_caseC2_pair
    (typeI_caseC2_pair_of_caseB_gap orth hcases hcases_dual hH he hhv hvu)

/-- **Peterfalvi (14.16)**: combining the actual (13.19) Type-I
orthogonality output for `L` with the case-(b) numerical gaps gives the two
zero-axis odd pairings needed for the final `eta_ij` expansion.  The remaining
inputs identify the abstract kernel and complement index in the (13.19) data
with the `H` and `p q` already fixed in Section 16. -/
theorem exists_typeI_eta_axes_odd_of_caseB_gap
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (hH_of_orth :
      ∀ orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L,
        Nat.card ↥orth.typeISetup.H = nc.h)
    (he_of_orth :
      ∀ orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L,
        orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    ∃ orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L,
      (∀ j : Fin hyp.base.p, (j : ℕ) ≠ 0 →
          OddOrder.Peterfalvi.S15.OddIntegerInner orth.betaL
            (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j)) ∧
        (∀ i : Fin hyp.base.q, (i : ℕ) ≠ 0 →
          OddOrder.Peterfalvi.S15.OddIntegerInner orth.betaL
            (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)) := by
  rcases OddOrder.Peterfalvi.S15.typeI_orthogonality_dichotomy
      _hG hyp.base nc.Ldata.L_maximal nc.Ldata.isTypeI with
    ⟨orth, horth⟩
  exact ⟨orth, typeI_eta_axes_odd_of_caseB_gap orth horth.2.2.2.1 horth.2.2.2.2
    (hH_of_orth orth) (he_of_orth orth) hhv hvu⟩

/-- Pointwise-in-the-left additivity of the canonical class-function inner product over a finite
sum: `(∑ i ∈ s, f i, ψ) = ∑ i ∈ s, (f i, ψ)`.  General-purpose `ClassFunction.inner` plumbing
(hoistable to `ClassFunction.lean`). -/
theorem inner_finset_sum_left {ι : Type*} [Fintype G]
    [Invertible (Nat.card G : ℂ)] (s : Finset ι)
    (f : ι → ClassFunction G ℂ) (ψ : ClassFunction G ℂ) :
    ClassFunction.inner (∑ i ∈ s, f i) ψ = ∑ i ∈ s, ClassFunction.inner (f i) ψ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, ClassFunction.inner_add_left, ih, Finset.sum_insert ha]

/-- **Faithful §16 carrier for the (14.16) case-(b) contradiction inputs.**

Under case-(b) of (14.14) (`(β_L^τ, ψ^{τ₁}) ≠ 0`, `q = 3`, `p = 5`) and the two strict gap
inequalities, the §16 character theory supplies (Pf (14.16), p.92):

* `betaL_expansion` — the (14.11.2)-style signed `η`-grid expansion `β_L^τ = Σ_{ij} ±η_ij − χ_L`
  (`χ_L = φ^{τ₁}` or `−φ̄^{τ₁}`), derived from `(13.19.c)` applied on both the S- and T-sides
  (`exists_typeI_eta_axes_odd_of_caseB_gap`) plus the vanishing of `β_L^τ` on `W − (W₁ ∪ W₂)`;
* `eta_orthogonal_psi` — `(η_ij, ψ^{τ₁}) = 0`: `ψ^{τ₁}` is the unit-norm component removed from the
  `η`-grid in the M-side expansion (14.11.2), hence orthogonal to the whole grid;
* `chiL_orthogonal_psi` — `(χ_L, ψ^{τ₁}) = 0`: by (4.1), `L^{τ₁}` is orthogonal to `M^{τ₁}`, and
  `χ_L ∈ L^{τ₁}`, `ψ^{τ₁} ∈ M^{τ₁}`;
* `pairing_ne_zero` — `(β_L^τ, ψ^{τ₁}) ≠ 0`, the defining property of case-(b) (14.14.b).

The genuine character theory (the expansion via (14.11.2)/(13.19.c), the orthogonalities via
(14.11.2)/(4.1), and the case-(b) pairing via (14.14)) is isolated here; the contradiction itself
is then the pure inner-product computation `(β_L^τ, ψ^{τ₁}) = 0`. -/
structure CaseBContradictionData {hyp : Hypothesis (G := G)}
    (nc : NonConjugateHypothesis hyp) [Fintype G] [Invertible (Nat.card G : ℂ)] where
  /-- The L-side virtual character `β_L^τ`. -/
  betaL : ClassFunction G ℂ
  /-- The removed unit-norm L-side character `χ_L` (`= φ^{τ₁}` or `−φ̄^{τ₁}`). -/
  chiL : ClassFunction G ℂ
  /-- The M-side test character `ψ^{τ₁}` (the coherent `ν`-image of the distinguished
  `ζ` — carried as a field so the whole datum is bundle-local; the (14.16) contradiction
  is a pure inner-product computation in the four fields and never needs the anchor
  `ψ^{τ₁} = nc.Mdata.tau1 nc.Mdata.psi` itself). -/
  psiImg : ClassFunction G ℂ
  /-- The `±1` signs of the `η`-grid expansion. -/
  signs : Fin hyp.base.q → Fin hyp.base.p → ℤ
  signs_pm_one : ∀ i j, signs i j = 1 ∨ signs i j = -1
  /-- **(14.16)** signed `η`-grid expansion `β_L^τ = Σ_{ij} ε_ij η_ij − χ_L`. -/
  betaL_expansion :
    betaL =
      (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (signs i j : ℂ) • hyp.base.eta i j) - chiL
  /-- **(14.11.2)**: `ψ^{τ₁}` is orthogonal to the `η`-grid. -/
  eta_orthogonal_psi : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
    ClassFunction.inner (hyp.base.eta i j) psiImg = 0
  /-- **(4.1)**: `χ_L ∈ L^{τ₁}` is orthogonal to `ψ^{τ₁} ∈ M^{τ₁}`. -/
  chiL_orthogonal_psi :
    ClassFunction.inner chiL psiImg = 0
  /-- **(14.14.b)**: the case-(b) nonzero pairing `(β_L^τ, ψ^{τ₁}) ≠ 0`. -/
  pairing_ne_zero :
    ClassFunction.inner betaL psiImg ≠ 0

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.b), the M-side `η`-grid orthogonality of `ψ^{τ₁} = ζ_M^ν`.**

The distinguished coherent image `ψ^{τ₁} = ζ_M^ν` (`= (dataM.h78 hG).nu (ζ_{zetaDistinct})`)
is orthogonal to the entire `η`-grid.  This is the sorry-free (3.6)–(3.8)/(13.19.b) engine
`eta_orthogonal_of_norm_one_pair_vanish` (`S16_GridExpansion`) applied to the conjugate pair
`(ζ_M^ν, ζ̄_M^ν)`: the unit norms (`nu_zeta_norm_one`), the conjugate distinctness
`⟨ζ_M^ν, ζ̄_M^ν⟩ = 0` (`nu_zeta_inner_nu_conj_eq_zero`), and the `ℤ[Irr G]` memberships
(`coh.extension_mem_ZIrr` on `ζ ∈ 𝒮`) are all supplied by the `TypeICoherent78Data` coherence
bundle.  The single genuine §13/§14 input is `hDadeAvoid` = **Peterfalvi (13.19.a)**: the M-side
Dade support `Ã(M)` avoids the regular-set saturation `Ŵ^G = (W ∖ (W₁ ∪ W₂))^G`, so the
conjugate difference `ζ_M^ν − ζ̄_M^ν` (supported in `Ã(M)`, `nu_zeta_sub_conj_support_at`)
vanishes on `Ŵ^G`. -/
theorem caseB_eta_orthogonal_psi [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (dataM : TypeICoherent78Data M)
    (hDadeAvoid : ∀ x ∈ conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (hyp.eta i j)
        ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta (dataM.h78 hG).zetaDistinct)) = 0 := by
  classical
  -- distinctness datum for the distinguished index `zetaDistinct = 0` and its conjugate `i'`
  have hjne : (dataM.h78 hG).zetaDistinct ≠ dataM.ind1H := by
    have h := (dataM.h78 hG).zetaDistinct_ne_ind1H
    rwa [dataM.h78_ind1H_eq] at h
  obtain ⟨i', hi'_ne, hi'⟩ := dataM.exists_conjIndex_at hG hjne
  -- engine inputs from the coherence bundle
  have hpsiZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta (dataM.h78 hG).zetaDistinct)
      ∈ ZIrr G := by
    rw [dataM.h78_nu_eq, dataM.h78_zetaDistinct_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset (Ne.symm dataM.ind1H_ne_zero)))
  have hconjZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta i') ∈ ZIrr G := by
    have hi'ne_data : i' ≠ dataM.ind1H := by rw [← dataM.h78_ind1H_eq]; exact hi'_ne
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hi'ne_data))
  have hpsi1 := dataM.nu_zeta_norm_one hG (dataM.h78 hG).zetaDistinct_ne_ind1H
  have hconj1 := dataM.nu_zeta_norm_one hG hi'_ne
  have hcross := dataM.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hjne hi'_ne hi'
  have hsupp := dataM.nu_zeta_sub_conj_support_at hG hjne hi'_ne hi'
  have hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta (dataM.h78 hG).zetaDistinct)
        - (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta i')) x = 0 := by
    intro x hx
    by_contra hval
    exact hDadeAvoid x hx (hsupp (ClassFunction.mem_support.mpr hval))
  exact eta_orthogonal_of_norm_one_pair_vanish hyp hpsiZ hconjZ hpsi1 hconj1 hcross hvanish

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.b), the `η`-grid orthogonality of *every* coherent image `ζ_k^ν`**
(the Coq `o_tauLeta` for the whole family, not just the distinguished index).  For any family
member `k ≠ ind1H`, the coherent image `ζ_k^ν = (dataM.h78 hG).nu (ζ_k)` is orthogonal to the
entire `η`-grid.  Identical (3.6)–(3.8)/(13.19.b) engine as `caseB_eta_orthogonal_psi`, but with
the distinguished index `zetaDistinct` replaced by an arbitrary `k`: `ζ_k^ν` has unit norm
(`nu_zeta_norm_one`), its conjugate partner `ζ_{k'}^ν` (`exists_conjIndex_at`, generic in the
index) is a distinct unit-norm virtual character (`nu_zeta_inner_nu_conj_eq_zero`), and the
conjugate difference `ζ_k^ν − ζ_{k'}^ν` (supported in `Ã(M)`, `nu_zeta_sub_conj_support_at`,
also generic) vanishes on `Ŵ^G` by the same (13.19.a) Dade-support avoidance `hDadeAvoid`. -/
theorem caseB_eta_orthogonal_nu_zeta_at [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (dataM : TypeICoherent78Data M)
    (hDadeAvoid : ∀ x ∈ conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport)
    {k : Fin (dataM.n + 1)} (hk : k ≠ (dataM.h78 hG).ind1H) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (hyp.eta i j)
        ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k)) = 0 := by
  classical
  -- the kernel-index datum for `k` and its conjugate partner `k'`
  have hkne : k ≠ dataM.ind1H := by rwa [dataM.h78_ind1H_eq] at hk
  obtain ⟨k', hk'_ne, hk'⟩ := dataM.exists_conjIndex_at hG hkne
  -- engine inputs from the coherence bundle
  have hpsiZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k) ∈ ZIrr G := by
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hkne))
  have hconjZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k') ∈ ZIrr G := by
    have hk'ne_data : k' ≠ dataM.ind1H := by rw [← dataM.h78_ind1H_eq]; exact hk'_ne
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hk'ne_data))
  have hpsi1 := dataM.nu_zeta_norm_one hG hk
  have hconj1 := dataM.nu_zeta_norm_one hG hk'_ne
  have hcross := dataM.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hkne hk'_ne hk'
  have hsupp := dataM.nu_zeta_sub_conj_support_at hG hkne hk'_ne hk'
  have hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k)
        - (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k')) x = 0 := by
    intro x hx
    by_contra hval
    exact hDadeAvoid x hx (hsupp (ClassFunction.mem_support.mpr hval))
  exact eta_orthogonal_of_norm_one_pair_vanish hyp hpsiZ hconjZ hpsi1 hconj1 hcross hvanish

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.a), σ-decomposition ingredient**: the Fitting core `M_F`
(`dataM.kernel`) of the type-`I` maximal `M`, non-conjugate to the `W`-containing maximals
`S`, `T`, has order coprime to `p·q`.  In the Coq proof of `tiA_PWG` this is `coHp`/`coHq`
(`coprime #|H| p`, `coprime #|H| q` with `H = M_F`), derived from `FT_Dade_support_partition`:
`p, q ∈ σ(S) ∪ σ(T)` are disjoint from `σ(M)` for non-conjugate maximals (`nc.not_conj`).
Deep named §13/BG §10 obligation. -/
theorem card_kernel_coprime_pq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    {M : Subgroup G} (hMmax : M ∈ maximalSubgroups G) (dataM : TypeICoherent78Data M) :
    Nat.Coprime (Nat.card ↥dataM.kernel) (hyp.base.p * hyp.base.q) := by
  classical
  -- `M`, `S`, `T` are maximal; `M` type I, `S`/`T` type II
  have hMI : IsTypeI M := ⟨dataM.typeIHyp.typeI⟩
  have hSII : IsTypeII hyp.base.S :=
    OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.base.S_maximal hyp.base.S_typeP2
  have hTII : IsTypeII hyp.base.T := T_typeII hG hyp
  -- `M_F = M_σ`, `S_σ = P`, `T_σ = Q`
  have hMF : dataM.kernel = OddOrder.BG.Ch3.S10.Msigma M := by
    show dataM.typeIHyp.typeI.typeF.H = _
    rw [dataM.typeIHyp.typeI.typeF.H_eq]
    exact OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hMmax (Or.inl hMI)
  have hMsS : OddOrder.BG.Ch3.S10.Msigma hyp.base.S = hyp.base.P := by
    rw [← OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hyp.base.S_maximal (Or.inr hSII)]
    exact hyp.base.P_eq_SF.symm
  have hMsT : OddOrder.BG.Ch3.S10.Msigma hyp.base.T = hyp.base.Q := by
    rw [← OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hyp.base.T_maximal (Or.inr hTII)]
    exact hyp.base.Q_eq_TF.symm
  -- `p ∈ σ(S)` (as `p = |W₂| ∣ |P| = |S_σ|`), `q ∈ σ(T)`
  have hpσS : hyp.base.p ∈ OddOrder.BG.Ch3.S10.sigma hyp.base.S := by
    rw [← OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hyp.base.S_maximal, hMsS]
    refine Nat.mem_primeFactors.mpr ⟨hyp.base.p_prime, ?_, Nat.card_pos.ne'⟩
    rw [hyp.base.p_eq_card_W2]
    exact Subgroup.card_dvd_of_le (OddOrder.Peterfalvi.S15.W2_le_P hG hyp.base)
  have hqσT : hyp.base.q ∈ OddOrder.BG.Ch3.S10.sigma hyp.base.T := by
    rw [← OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hyp.base.T_maximal, hMsT]
    refine Nat.mem_primeFactors.mpr ⟨hyp.base.q_prime, ?_, Nat.card_pos.ne'⟩
    rw [hyp.base.q_eq_card_W1]
    exact Subgroup.card_dvd_of_le (OddOrder.Peterfalvi.S15.W1_le_Q hG hyp.base)
  -- `M` is not conjugate to `S` or `T` (type I vs type non-I) ⟹ `σ`-disjointness
  have hMnS : ¬ ∃ g : G, MulAut.conj g • M = hyp.base.S :=
    OddOrder.Peterfalvi.S15.not_conj_of_isTypeI_of_isTypeNonI hG hMI hyp.base.S_maximal
      (Or.inl hSII)
  have hMnT : ¬ ∃ g : G, MulAut.conj g • M = hyp.base.T :=
    OddOrder.Peterfalvi.S15.not_conj_of_isTypeI_of_isTypeNonI hG hMI hyp.base.T_maximal
      (Or.inl hTII)
  have hdS := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMmax hyp.base.S_maximal hMnS
  have hdT := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMmax hyp.base.T_maximal hMnT
  -- hence `p, q ∉ σ(M) = π(|M_F|)`, so `p, q ∤ |M_F|`
  have hpMF : ¬ hyp.base.p ∣ Nat.card ↥dataM.kernel := by
    rw [hMF]; intro hdvd
    exact Set.disjoint_left.mp hdS
      ((OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hMmax hyp.base.p).mp
        (Nat.mem_primeFactors.mpr ⟨hyp.base.p_prime, hdvd, Nat.card_pos.ne'⟩)) hpσS
  have hqMF : ¬ hyp.base.q ∣ Nat.card ↥dataM.kernel := by
    rw [hMF]; intro hdvd
    exact Set.disjoint_left.mp hdT
      ((OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hMmax hyp.base.q).mp
        (Nat.mem_primeFactors.mpr ⟨hyp.base.q_prime, hdvd, Nat.card_pos.ne'⟩)) hqσT
  exact Nat.Coprime.mul_right
    (hyp.base.p_prime.coprime_iff_not_dvd.mpr hpMF).symm
    (hyp.base.q_prime.coprime_iff_not_dvd.mpr hqMF).symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.a), Dade-support ingredient**: every element `y` of the Dade support
`Ã(M) = ⋃_{x∈A(M)} (x·R(x))^G` has order *not* coprime to `|M_F|` (it is `π(M_F)`-singular).
Indeed `y` is conjugate to `x·r` with `x ∈ A(M) = M_F^#` (type-I, `1 ≠ x ∈ M_F`) and
`r ∈ R(x)` a signalizer commuting with `x` of order coprime to `|M_F|`, so
`1 < orderOf x ∣ orderOf y` and `orderOf x ∣ |M_F|`.  Deep named §8/§13 obligation
(the Dade signalizer `π`-part structure). -/
theorem dadeSupport_not_coprime_card_kernel [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (dataM : TypeICoherent78Data M)
    {y : G} (hy : y ∈ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport) :
    ¬ Nat.Coprime (orderOf y) (Nat.card ↥dataM.kernel) := by
  classical
  -- `y` is conjugate to `a·h` with `a ∈ A = M_F#`, `h ∈ H(a)` (the (8.14) signalizer)
  rw [dataM.h78_hyp_eq hG, OddOrder.Peterfalvi.S04.Hypothesis.mem_dadeSupport_iff] at hy
  obtain ⟨a, h, hh, hconj⟩ := hy
  -- `a.1 ∈ M_F`, `a.1 ≠ 1` (`A = typeIA = M_F ∖ {1}`)
  have ha2 : a.1 ∈ (dataM.kernel : Set G) \ {1} := by
    rw [← dataM.typeIA_eq_sharp hG]; exact a.2
  have haK : a.1 ∈ dataM.kernel := ha2.1
  have hane : a.1 ≠ 1 := fun h1 => ha2.2 (Set.mem_singleton_iff.mpr h1)
  have hord_ne : orderOf a.1 ≠ 1 := fun h1 => hane (orderOf_eq_one_iff.mp h1)
  have hord_dvd : orderOf a.1 ∣ Nat.card ↥dataM.kernel := dataM.kernel.orderOf_dvd_natCard haK
  -- `h` commutes with `a.1`: `H(a) ≤ C_G(a.1)` by `(2.2.b)` `C_G(a.1) = H(a) ⊔ C_L(a.1)`
  have hh_cent : h ∈ Subgroup.centralizer ({a.1} : Set G) := by
    rw [(dataM.typeIHyp.dadeData.dade).centralizer_eq_sup a]
    exact Subgroup.mem_sup_left hh
  have hcomm : Commute a.1 h := (Subgroup.mem_centralizer_singleton_iff.mp hh_cent).symm
  -- `orderOf a.1` coprime `orderOf h`: `(2.2.c)` `(|H(a)|, |C_L(a.1)|) = 1`
  have hcop_orders : Nat.Coprime (orderOf a.1) (orderOf h) := by
    have hcc := (dataM.typeIHyp.dadeData.dade).centralizer_coprime a a
    have hord_h : orderOf h ∣ Nat.card ↥((dataM.typeIHyp.dadeData.dade).H a) :=
      ((dataM.typeIHyp.dadeData.dade).H a).orderOf_dvd_natCard hh
    have haCent : a.1 ∈ OddOrder.Peterfalvi.S04.centralizerIn M a.1 :=
      OddOrder.Peterfalvi.S04.mem_centralizerIn.mpr
        ⟨(dataM.typeIHyp.dadeData.dade).mem_L a.2, rfl⟩
    have hord_a : orderOf a.1 ∣ Nat.card ↥(OddOrder.Peterfalvi.S04.centralizerIn M a.1) :=
      (OddOrder.Peterfalvi.S04.centralizerIn M a.1).orderOf_dvd_natCard haCent
    exact (Nat.Coprime.coprime_dvd_right hord_a
      (Nat.Coprime.coprime_dvd_left hord_h hcc)).symm
  -- `orderOf y = orderOf(a.1·h) = orderOf a.1 · orderOf h`, so `orderOf a.1 ∣ orderOf y`
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hsemi : SemiconjBy c (a.1 * h) y := by
    change c * (a.1 * h) = y * c; rw [← hc]; group
  have hordy : orderOf y = orderOf a.1 * orderOf h := by
    rw [← SemiconjBy.orderOf_eq c hsemi,
      hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop_orders]
  have hdvd_y : orderOf a.1 ∣ orderOf y := by rw [hordy]; exact dvd_mul_right _ _
  -- `1 < orderOf a.1 ∣ gcd(orderOf y, |M_F|) = 1` is a contradiction
  intro hcop
  have hcop' : Nat.gcd (orderOf y) (Nat.card ↥dataM.kernel) = 1 := hcop
  have hgcd : orderOf a.1 ∣ Nat.gcd (orderOf y) (Nat.card ↥dataM.kernel) :=
    Nat.dvd_gcd hdvd_y hord_dvd
  rw [hcop'] at hgcd
  exact hord_ne (Nat.dvd_one.mp hgcd)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.a), the M-side Dade-support avoidance.**  For a type-`I` maximal
`M` not conjugate to the `W`-containing maximals `S`, `T`, the Dade support `Ã(M)` avoids the
regular-set saturation `Ŵ^G = (W ∖ (W₁ ∪ W₂))^G`.  This is the Coq `tiA_PWG`
(`'A~(L) :&: PWG = set0`, PFsection13): every `x ∈ Ŵ^G` is conjugate to a `w ∈ W`, so (as
`|W₁| = q`, `|W₂| = p` are prime and `W = W₁·W₂` commutes) `orderOf x ∣ p·q`, hence `orderOf x`
is coprime to `|M_F|` (`card_kernel_coprime_pq`); but every element of `Ã(M)` is
`π(M_F)`-singular (`dadeSupport_not_coprime_card_kernel`), a contradiction.  The two named
ingredients are the genuine BG §10-level σ-decomposition inputs. -/
theorem mSide_dadeSupport_avoids_regular [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    {M : Subgroup G} (hMmax : M ∈ maximalSubgroups G) (dataM : TypeICoherent78Data M) :
    ∀ x ∈ conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))),
      x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport := by
  intro x hx hdade
  obtain ⟨w, ⟨hwW, _hwne⟩, g, hgx⟩ := hx
  -- `orderOf x = orderOf w` (conjugation preserves order)
  have hsemi : SemiconjBy g w x := by
    change g * w = x * g
    rw [← hgx]; group
  have hordx : orderOf x = orderOf w := (SemiconjBy.orderOf_eq g hsemi).symm
  -- decompose `w = a·b` with `a ∈ W₁`, `b ∈ W₂` inside the commutative `W`
  letI := hyp.base.W_cyclic
  letI : CommGroup ↥hyp.base.W := IsCyclic.commGroup
  have hwWmem : w ∈ hyp.base.W := hwW
  have hW1le : hyp.base.W1 ≤ hyp.base.W := by rw [hyp.base.W_eq_join]; exact le_sup_left
  have hW2le : hyp.base.W2 ≤ hyp.base.W := by rw [hyp.base.W_eq_join]; exact le_sup_right
  have hwmem : (⟨w, hwWmem⟩ : ↥hyp.base.W) ∈
      (hyp.base.W1.subgroupOf hyp.base.W) ⊔ (hyp.base.W2.subgroupOf hyp.base.W) := by
    have h1 : (hyp.base.W1 ⊔ hyp.base.W2).subgroupOf hyp.base.W = ⊤ := by
      rw [← hyp.base.W_eq_join, Subgroup.subgroupOf_self]
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, h1]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hwmem
  have hcoe : (a : G) * (b : G) = w := by
    have h := congrArg (Subtype.val) hab; simpa using h
  have haW1 : (a : G) ∈ hyp.base.W1 := Subgroup.mem_subgroupOf.mp ha
  have hbW2 : (b : G) ∈ hyp.base.W2 := Subgroup.mem_subgroupOf.mp hb
  -- `orderOf a ∣ q`, `orderOf b ∣ p` (Lagrange in the prime-order `W₁`, `W₂`)
  have haord : orderOf (a : G) ∣ hyp.base.q := by
    have h := hyp.base.W1.orderOf_dvd_natCard haW1
    rwa [← hyp.base.q_eq_card_W1] at h
  have hbord : orderOf (b : G) ∣ hyp.base.p := by
    have h := hyp.base.W2.orderOf_dvd_natCard hbW2
    rwa [← hyp.base.p_eq_card_W2] at h
  have hcomm : Commute (a : G) (b : G) := hyp.base.W1_commutes_W2 _ haW1 _ hbW2
  -- hence `orderOf x = orderOf w ∣ p·q`
  have hword : orderOf w ∣ hyp.base.p * hyp.base.q := by
    rw [← hcoe]
    refine hcomm.orderOf_mul_dvd_mul_orderOf.trans ?_
    rw [mul_comm hyp.base.p hyp.base.q]
    exact Nat.mul_dvd_mul haord hbord
  have hxord : orderOf x ∣ hyp.base.p * hyp.base.q := hordx ▸ hword
  -- `orderOf x` is coprime to `|M_F|`, contradicting `π(M_F)`-singularity of `Ã(M)`
  have hcop : Nat.Coprime (orderOf x) (Nat.card ↥dataM.kernel) :=
    Nat.Coprime.coprime_dvd_left hxord (card_kernel_coprime_pq hG hMmax dataM).symm
  exact dadeSupport_not_coprime_card_kernel hG dataM hdade hcop

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.2)/(13.19.a) consequence, the Coq `betaL_W_0`**: the coherence
residual `β_L = τ_L(Ind 1_H − φ)` (`(dataL.h78 hG).beta`) vanishes on the regular-set
saturation `Ŵ^G = (W ∖ (W₁ ∪ W₂))^G`.  `β_L` is supported in the Dade support `Ã(L)`
(`beta_support_subset_dadeSupport`), which avoids `Ŵ^G` by the fully-proven (13.19.a)
`mSide_dadeSupport_avoids_regular` (`L` is type-I, hence non-conjugate to the type-II
`W`-containing maximals `S`, `T`).  This is the first ingredient of the (14.11.2)/(13.19.c)
signed `η`-grid expansion (`lSide_signed_eta_expansion`). -/
theorem betaL_vanishes_on_regular_W [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (dataL : TypeICoherent78Data L) :
    ∀ x ∈ conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))),
      (dataL.h78 hG).beta x = 0 := by
  intro x hx
  by_contra hval
  exact mSide_dadeSupport_avoids_regular hG hLmax dataL x hx
    ((dataL.h78 hG).beta_support_subset_dadeSupport (ClassFunction.mem_support.mpr hval))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.7) applied to `β_L`**: the grid coefficients `a_ij = ⟨β_L, η_ij⟩` of the
coherence residual satisfy the four-corner relation `a_ij + a_00 = a_i0 + a_0j`.  Immediate
from the (3.7) engine `inner_eta_grid_relation` (`S16_GridExpansion`) and
`betaL_vanishes_on_regular_W`.  This is the (3.7) linear-relation ingredient of the
(14.11.2)/(13.19.c) signed `η`-grid expansion. -/
theorem betaL_grid_relation [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (dataL : TypeICoherent78Data L) (i : Fin hyp.base.q) (j : Fin hyp.base.p) :
    ClassFunction.inner (dataL.h78 hG).beta (hyp.base.eta i j)
        + ClassFunction.inner (dataL.h78 hG).beta
            (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩)
      = ClassFunction.inner (dataL.h78 hG).beta (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)
        + ClassFunction.inner (dataL.h78 hG).beta
            (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j) :=
  inner_eta_grid_relation hyp.base (betaL_vanishes_on_regular_W hG hLmax dataL) i j

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`β_L ∈ ℤ[Irr G]`**: the coherence residual `β_L = τ_L(Ind 1_H − ζ)` is a virtual character
(`beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible` on the bundle's `Ind 1_H`-virtuality and the
distinguished `ζ`-irreducibility).  This is the integrality input for the L-side grid coefficients
`m_ij = ⟨β_L, η_ij⟩`. -/
theorem betaL_mem_ZIrr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L : Subgroup G} (dataL : TypeICoherent78Data L) :
    (dataL.h78 hG).beta ∈ ZIrr G :=
  (dataL.h78 hG).beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (dataL.h78_ind_mem_ZIrr hG) (dataL.h78_zeta_irreducible hG)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.2)/(13.19.c), integrality of the L-side grid coefficients** (Coq
`Cint_cfdot_vchar`): each `m_ij = ⟨β_L, η_ij⟩` is an integer, since both `β_L` (`betaL_mem_ZIrr`)
and `η_ij` (`eta_mem_ZIrr`) are virtual characters (`inner_mem_ZIrr_int`).  This is the fully-proven
`coeff` ingredient of the (14.11.2) grid-coefficient carrier `LSideGridCoeffData`, available to lane
c independently of the deep §13 grid-membership content. -/
theorem betaL_grid_coeff_int [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (dataL : TypeICoherent78Data L)
    (i : Fin hyp.base.q) (j : Fin hyp.base.p) :
    ∃ m : ℤ, ClassFunction.inner (dataL.h78 hG).beta (hyp.base.eta i j) = (m : ℂ) :=
  ClassFunction.inner_mem_ZIrr_int (betaL_mem_ZIrr hG dataL) (eta_mem_ZIrr hyp.base i j)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.2)/(13.19.c), the principal grid coefficient** (Coq `a00 = 1`):
`m_00 = ⟨β_L, η_00⟩ = 1`.  The principal grid member is the trivial character
`η_00 = 1_G` (`eta_principal_eq_trivial`), and the (7.8.a) Dade decomposition
`β_L = 1_G − ζ_0^ν + Δ_L` (`beta_eq_constOne_sub_zetaImage_add_delta`, PROVEN) pairs against it as
`⟨1_G, 1_G⟩ − ⟨ζ_0^ν, 1_G⟩ + ⟨Δ_L, 1_G⟩ = 1 − 0 + 0`, using `‖1_G‖² = 1`
(`constOne_inner_self_eq_one`), the (7.8.a) source orthogonality `ζ_0^ν ⊥ 1_G`
(`BetaDecomp.orth_one` at the distinguished index) and the residual orthogonality `Δ_L ⊥ 1_G`
(`delta_orth_one`).  This is the fully-proven principal-boundary ingredient of
`LSideGridCoeffData`, available to lane c independently of the deep off-principal parity
(Coq `FTtypeI_bridge_facts`). -/
theorem betaL_grid_coeff_principal_eq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (dataL : TypeICoherent78Data L) :
    ClassFunction.inner (dataL.h78 hG).beta
        (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩) = 1 := by
  -- `η_00 = 1_G = constOne`
  have heta : hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩
      = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G := by
    rw [eta_principal_eq_trivial hyp.base]
    exact ClassFunction.ext fun _ => rfl
  rw [heta, (dataL.h78 hG).beta_eq_constOne_sub_zetaImage_add_delta,
    ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one,
    (dataL.betaDecomp hG).orth_one (dataL.h78 hG).zetaDistinct
      (dataL.h78 hG).zetaDistinct_ne_ind1H,
    (dataL.h78 hG).delta_orth_one (dataL.betaDecomp hG)]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §14 Dade carrier for the L-side `η`-grid coefficients** (Peterfalvi (13.19.c),
Coq `FTtype2_support_coherence` core).  Bundles the facts about the integer grid coefficients
`m_ij = ⟨β_L, η_ij⟩` of the coherence residual `β_L = (dataL.h78 hG).beta`, from which
`lSide_delta_grid_expansion` proves the `±1` rigidity and the grid identity.  The two lane-c
available facts are proven in-place in the producer `lSideGridCoeffData`; only the S/T type-P
bridge and §13 grid content remain as the isolated gate:

* `coeff` — the coefficients are integers, `⟨β_L, η_ij⟩ = m_ij` (**PROVEN in-place**,
  `betaL_grid_coeff_int` via `inner_mem_ZIrr_int`; the witness `m` is the integer value);
* `m_principal` — the principal coefficient `m_00 = 1` (**PROVEN in-place**,
  `betaL_grid_coeff_principal_eq_one`: `η_00 = 1_G` and `β_L = 1_G − ζ_0^ν + Δ_L` pair as
  `1 − 0 + 0`);
* `m_row_odd`/`m_col_odd` — **off-principal boundary parity** (Coq `FTtypeI_bridge_facts`, the
  S/T-side type-P bridge `cycTIiso_cfdot_exchange`): `m_0j`, `m_i0` are *odd*; genuinely
  cross-lane-gated to the type-P `S`/`T` maximals (lane b's §13/§15 layer);
* `bessel` — **the (13.19.c) Bessel bound** (Coq `orthonormal_span` + `lb_b` + `ub_e`):
  `Σ_{ij} m_ij² ≤ p q`; needs the coherent-image/grid orthogonality `ζ_i^ν ⊥ η`-grid (Coq
  `o_tauLeta`) to match `β_L`'s grid projection with `(Γ_L + 1_G)`'s and apply `‖Γ_L‖² ≤ e − 1`,
  the same §13 residual content as `grid_mem`;
* `grid_mem` — **the grid membership** (Coq `Y = 0`, issue 3002): `1_G + Δ_L = Σ_{ij} m_ij η_ij`,
  i.e. `β_L + ζ_0^ν` equals its own orthogonal projection onto the `η`-grid.

These are genuine facts about the type-I maximal `L` (its Dade isometry, coherent extension, and
the S/T-partner bridge); the concrete construction of the three off-principal/grid facts is the
remaining §13/§14 obligation, isolated here away from the pure `±1` combinatorics. -/
structure LSideGridCoeffData [Finite G] (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : TypeICoherent78Data L)
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) where
  /-- The integer grid coefficient `m_ij = ⟨β_L, η_ij⟩`. -/
  m : Fin hyp.base.q → Fin hyp.base.p → ℤ
  /-- `⟨β_L, η_ij⟩ = m_ij` (integrality, `inner_mem_ZIrr_int`).  **PROVEN in-place**. -/
  coeff : ∀ i j, ClassFunction.inner (dataL.h78 hG).beta (hyp.base.eta i j) = (m i j : ℂ)
  /-- **Principal coefficient** `m_00 = 1` (Coq `a00 = 1`).  **PROVEN in-place**. -/
  m_principal : m ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ = 1
  /-- **Off-principal row parity** (Coq `FTtypeI_bridge_facts`, gated): `m_0j` odd. -/
  m_row_odd : ∀ j, j ≠ ⟨0, hyp.base.p_prime.pos⟩ → Odd (m ⟨0, hyp.base.q_prime.pos⟩ j)
  /-- **Off-principal column parity** (Coq `FTtypeI_bridge_facts`, gated): `m_i0` odd. -/
  m_col_odd : ∀ i, i ≠ ⟨0, hyp.base.q_prime.pos⟩ → Odd (m i ⟨0, hyp.base.p_prime.pos⟩)
  /-- **Bessel bound** (Coq `ub_e`, gated): `Σ m_ij² ≤ p q`. -/
  bessel : ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2
    ≤ (hyp.base.p * hyp.base.q : ℤ)
  /-- **Grid membership** (Coq `Y = 0`): `1_G + Δ_L = Σ m_ij η_ij`. -/
  grid_mem : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + (dataL.h78 hG).delta =
    ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j : ℂ) • hyp.base.eta i j

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c), the Bessel bound `Σ m_ij² ≤ p q`** (Coq `ub_e`).  With
`m_ij = ⟨β_L, η_ij⟩` and `e_L = |L : H_L| = p q` (`hepq`), the (7.8.a) decomposition
`β_L = 1_G − ζ_0^ν + a·W + Γ_L` (`BetaDecomp.beta_eq`) *projects* onto the `η`-grid as
`⟨β_L, η_ij⟩ = ⟨1_G, η_ij⟩ + ⟨Γ_L, η_ij⟩ = ⟨1_G + Γ_L, η_ij⟩`: the distinguished image
`ζ_0^ν` and *every* member `ζ_k^ν` of the weighted sum `W` are orthogonal to the whole grid
(`caseB_eta_orthogonal_nu_zeta_at`, the Coq `o_tauLeta` for the full family, whose only input is
the (13.19.a) Dade-support avoidance `mSide_dadeSupport_avoids_regular`).  Bessel for the
orthonormal grid `{η_ij}` (`eta_orthonormal`) applied to `φ = 1_G + Γ_L` then gives
`Σ m_ij² ≤ ‖1_G + Γ_L‖² = ‖1_G‖² + ‖Γ_L‖² = 1 + ‖Γ_L‖²`, and `‖Γ_L‖² ≤ e_L − 1`
(`dataL.normEstimates.gamma_norm_sq_le`, the (7.8.b) residual bound), so
`Σ m_ij² ≤ 1 + (p q − 1) = p q`.  This is the honest (13.19.c) grid Bessel bound; the only
external datum is `hepq` (`e_L = p q`, carried by `LHypothesis` at the call site). -/
theorem betaL_grid_coeff_bessel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (dataL : TypeICoherent78Data L)
    (hepq : (dataL.h78 hG).complementIndex = hyp.base.p * hyp.base.q)
    (m : Fin hyp.base.q → Fin hyp.base.p → ℤ)
    (hcoeff : ∀ i j, ClassFunction.inner (dataL.h78 hG).beta (hyp.base.eta i j) = (m i j : ℂ)) :
    ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2
      ≤ (hyp.base.p * hyp.base.q : ℤ) := by
  classical
  haveI := dataL.kernelIn_normal
  set H78 := dataL.h78 hG with hH78
  set BD := dataL.betaDecomp hG with hBD
  -- `ζ_0^ν ⊥ η_ij` and every family member `ζ_k^ν ⊥ η_ij` (Coq `o_tauLeta`, full family).
  have hDadeAvoid := mSide_dadeSupport_avoids_regular (hyp := hyp) hG hLmax dataL
  have hetaNu : ∀ (k : Fin (dataL.n + 1)), k ≠ H78.ind1H →
      ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
        ClassFunction.inner (H78.nu (H78.hyp76.zeta k)) (hyp.base.eta i j) = 0 := by
    intro k hk i j
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      caseB_eta_orthogonal_nu_zeta_at hG hyp.base dataL hDadeAvoid hk i j, star_zero]
  -- `W = weightedNuSum ⊥ η_ij` (linear combination of the `ζ_k^ν`, `k ≠ ind1H`).
  have hWeta : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ClassFunction.inner H78.weightedNuSum (hyp.base.eta i j) = 0 := by
    intro i j
    rw [show H78.weightedNuSum
        = ∑ k ∈ (Finset.univ.erase H78.ind1H),
            (H78.hyp76.zeta k (1 : ↥L) /
              (H78.hyp76.zeta H78.zetaDistinct (1 : ↥L) *
                ClassFunction.inner (H78.hyp76.zeta k) (H78.hyp76.zeta k))) •
              H78.nu (H78.hyp76.zeta k) from rfl]
    rw [inner_sum_left]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [ClassFunction.inner_smul_left, hetaNu k (Finset.mem_erase.mp hk).1 i j, mul_zero]
  -- **The grid projection**: `⟨β_L, η_ij⟩ = ⟨1_G + Γ_L, η_ij⟩` (the `ζ_0^ν`- and `W`-parts die).
  set phi : ClassFunction G ℂ :=
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + BD.Gamma with hphi
  have hphi_coeff : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ClassFunction.inner phi (hyp.base.eta i j) = (m i j : ℂ) := by
    intro i j
    rw [← hcoeff i j, hphi,
      show H78.beta = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          - H78.nu (H78.hyp76.zeta H78.zetaDistinct)
          + (BD.a : ℂ) • H78.weightedNuSum + BD.Gamma from BD.beta_eq]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left,
      hetaNu H78.zetaDistinct H78.zetaDistinct_ne_ind1H i j, hWeta i j, mul_zero, sub_zero,
      add_zero]
  -- Pythagorean split for `φ = 1_G + Γ_L` against the orthonormal grid `{η_ij}`.
  set X : ClassFunction G ℂ :=
    ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j : ℂ) • hyp.base.eta i j with hX
  set Y : ClassFunction G ℂ := phi - X with hY
  have hXeta : ∀ (k : Fin hyp.base.q) (l : Fin hyp.base.p),
      ClassFunction.inner X (hyp.base.eta k l) = (m k l : ℂ) := by
    intro k l
    rw [hX, inner_sum_left]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _) (fun i _ hik => ?_)]
    · rw [inner_sum_left,
        Finset.sum_eq_single_of_mem l (Finset.mem_univ _) (fun j _ hjl => ?_)]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp.base,
          if_pos ⟨rfl, rfl⟩, mul_one]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp.base,
          if_neg (by rintro ⟨-, rfl⟩; exact hjl rfl), mul_zero]
    · rw [inner_sum_left]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ClassFunction.inner_smul_left, eta_orthonormal hyp.base,
        if_neg (by rintro ⟨rfl, -⟩; exact hik rfl), mul_zero]
  have hsum_sq : ∀ ψ : ClassFunction G ℂ,
      (∀ (k : Fin hyp.base.q) (l : Fin hyp.base.p),
        ClassFunction.inner ψ (hyp.base.eta k l) = (m k l : ℂ)) →
      ClassFunction.inner ψ X
        = ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℂ) := by
    intro ψ hψ
    rw [hX, inner_sum_right]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ClassFunction.inner_smul_right, hψ i j, star_intCast]
    ring
  have hXY : ClassFunction.inner X Y = 0 := by
    have h := hsum_sq X hXeta
    have h2 : ClassFunction.inner X phi
        = ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℂ) := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hsum_sq phi hphi_coeff, star_intCast]
    rw [hY, ClassFunction.inner_sub_right, h2, h, sub_self]
  have hYX : ClassFunction.inner Y X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXY, star_zero]
  have hsplit : ClassFunction.inner phi phi
      = ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℂ)
        + ClassFunction.inner Y Y := by
    have hphiXY : phi = X + Y := by rw [hY]; abel
    calc ClassFunction.inner phi phi
        = ClassFunction.inner (X + Y) (X + Y) := by rw [← hphiXY]
      _ = ClassFunction.inner X X + ClassFunction.inner X Y
          + (ClassFunction.inner Y X + ClassFunction.inner Y Y) := by
          rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
            ClassFunction.inner_add_right]
      _ = ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℂ)
          + ClassFunction.inner Y Y := by
          rw [hXY, hYX, hsum_sq X hXeta]; ring
  -- `⟨Y, Y⟩ ≥ 0`, so `Σ m² ≤ ⟨φ, φ⟩` (real parts).
  have hYY_nonneg : (0 : ℝ) ≤ (ClassFunction.inner Y Y).re :=
    OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_self_re_nonneg Y
  -- `⟨φ, φ⟩ = ‖1_G‖² + ‖Γ_L‖² = 1 + ‖Γ_L‖²` (cross term `1_G ⊥ Γ_L`).
  have hone_gamma : ClassFunction.inner
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) BD.Gamma = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, BD.Gamma_orth_one,
      star_zero]
  have hphiphi : ClassFunction.inner phi phi
      = (1 : ℂ) + ClassFunction.inner BD.Gamma BD.Gamma := by
    rw [hphi, ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right,
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one,
      hone_gamma, BD.Gamma_orth_one, add_zero, zero_add]
  -- `‖Γ_L‖² ≤ e_L − 1 = p q − 1` from the (7.8.b) `NormEstimates` residual bound.
  have hGammaBound : (ClassFunction.inner BD.Gamma BD.Gamma).re
      ≤ (H78.complementIndex : ℝ) - 1 :=
    (dataL.normEstimates hG).gamma_norm_sq_le (dataL.smallIndex hG)
  -- Take real parts and cast to `ℤ`.
  have hre : ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℝ)
      + (ClassFunction.inner Y Y).re = 1 + (ClassFunction.inner BD.Gamma BD.Gamma).re := by
    have hcs := congrArg Complex.re (hsplit.symm.trans hphiphi)
    rw [Complex.add_re, Complex.add_re, Complex.intCast_re, Complex.one_re] at hcs
    exact hcs
  have hsq_le_real : ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℝ)
      ≤ (hyp.base.p * hyp.base.q : ℤ) := by
    have hepqR : (H78.complementIndex : ℝ) = ((hyp.base.p * hyp.base.q : ℤ) : ℝ) := by
      rw [hH78] at hepq ⊢; rw [hepq]; push_cast; ring
    have : ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℝ)
        ≤ 1 + (ClassFunction.inner BD.Gamma BD.Gamma).re := by linarith
    calc ((∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (m i j) ^ 2 : ℤ) : ℝ)
        ≤ 1 + (ClassFunction.inner BD.Gamma BD.Gamma).re := this
      _ ≤ 1 + ((H78.complementIndex : ℝ) - 1) := by linarith
      _ = (H78.complementIndex : ℝ) := by ring
      _ = ((hyp.base.p * hyp.base.q : ℤ) : ℝ) := hepqR
  exact_mod_cast hsq_le_real

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §14 producer of the L-side grid-coefficient data** (policy-A descent).  The type-I
maximal `L` carries the (13.19.c)/(7.8) grid-coefficient package `LSideGridCoeffData`.  The
lane-c-available facts are **proven in-place** here — `coeff` (integrality, `betaL_grid_coeff_int`),
`m_principal` (`m_00 = 1`, `betaL_grid_coeff_principal_eq_one`), and `bessel` (the (13.19.c) grid
Bessel bound `Σ m² ≤ p q`, `betaL_grid_coeff_bessel`, from the full-family grid orthogonality
`caseB_eta_orthogonal_nu_zeta_at` + the (7.8.b) residual bound `‖Γ_L‖² ≤ e − 1`, using the carried
`hepq : e_L = p q`) — with the integer witness `m` taken from the proven integrality.  Only the
two off-principal parity facts remain as the isolated gate: `m_row_odd`/`m_col_odd` (the S/T type-P
partner bridge, Coq `FTtypeI_bridge_facts`) and `grid_mem` (the §13 `Y = 0` grid membership,
issue 3002), genuinely cross-lane-gated to lane b's §13/§15 type-P layer. -/
noncomputable def lSideGridCoeffData [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (dataL : TypeICoherent78Data L) (hq3 : hyp.base.q = 3) (hp5 : hyp.base.p = 5)
    (hepq : (dataL.h78 hG).complementIndex = hyp.base.p * hyp.base.q) :
    LSideGridCoeffData hyp dataL hG where
  -- The integer coefficient is the witness of the proven integrality `betaL_grid_coeff_int`.
  m i j := Classical.choose (betaL_grid_coeff_int hG dataL i j)
  -- `coeff` is fully proven (integrality, `inner_mem_ZIrr_int`).
  coeff i j := Classical.choose_spec (betaL_grid_coeff_int hG dataL i j)
  -- `m_00 = 1` is fully proven: the chosen integer at `(0,0)` casts to `⟨β_L, η_00⟩ = 1`.
  m_principal := by
    have hspec := Classical.choose_spec
      (betaL_grid_coeff_int hG dataL
        (hyp := hyp) ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩)
    have h1 := betaL_grid_coeff_principal_eq_one (hyp := hyp) hG dataL
    -- `(m_00 : ℂ) = ⟨β_L, η_00⟩ = 1`, hence `m_00 = 1` over `ℤ`.
    have : ((Classical.choose (betaL_grid_coeff_int hG dataL
        (hyp := hyp) ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩) : ℤ) : ℂ) = 1 :=
      hspec.symm.trans h1
    exact_mod_cast this
  -- **Genuinely cross-lane-gated (Coq `FTtypeI_bridge_facts`, the S/T type-P partner bridge).**
  -- Off-principal parity `a i j ≡ 1 (mod 2)` needs the `cycTIiso_cfdot_exchange` reciprocity of the
  -- type-P `S`/`T` maximals (`hyp.base.S_typeP2`), which lives in lane b's §13/§15 layer.
  -- **Genuinely cross-lane-gated (Coq `FTtypeI_bridge_facts`, PFsection13.v:1987; issue 3002).**
  -- `m_0j = ⟨β_L, η_0j⟩ ≡ 1 (mod 2)` is the (c2) disjunct of `FTtypeI_bridge_facts` applied to the
  -- **S-side type-P partner** `StypeP` (PFsection14.v:187, `case/betaL_P: StypeP => _ _ -> //`).
  -- That bound is the type-P coherent pairing `⟨τ β_S, τ₁ φ⟩ ≡ 1 (mod 2)` on the S-side residual
  -- `β_S`, which lives in lane b's `S15_SAndT.lean`; S16 only carries an opaque `caseB_formula`.
  -- Verified c-unreachable: the only c-available parity primitive `cfdot_real_vchar_even` needs
  -- `η_0j` real (no `eta_isReal` — `η` is a cyclic-TI image, complex) and would anyway give
  -- `⟨β_L,1⟩·⟨η_0j,1⟩ = 1·0 = 0 (mod 2)` = EVEN, the *opposite* parity.
  m_row_odd := sorry
  -- Dual of `m_row_odd`, from `FTtypeI_bridge_facts` on the **T-side type-P partner** `TtypeP`
  -- (PFsection14.v:190) — same lane-b §13 gate (issue 3002).
  m_col_odd := sorry
  -- **The (13.19.c) Bessel bound `Σ m² ≤ p q`** (Coq `ub_e`), fully proven via
  -- `betaL_grid_coeff_bessel`: the (7.8.a) decomposition projects onto the `η`-grid as
  -- `⟨β_L, η_ij⟩ = ⟨1_G + Γ_L, η_ij⟩` (`caseB_eta_orthogonal_nu_zeta_at` kills the `ζ_0^ν`/`W`
  -- parts), and Bessel + `‖Γ_L‖² ≤ e − 1` gives `Σ m² ≤ 1 + (e − 1) = e = p q` (using `hepq`).
  bessel :=
    betaL_grid_coeff_bessel hG hLmax dataL hepq _
      (fun i j => Classical.choose_spec (betaL_grid_coeff_int hG dataL i j))
  -- **The deep §13 gate (issue 3002, Coq `Y = 0`, PFsection14.v:212-251).** `1_G + Δ_L = Σ m_ij η_ij`:
  -- the coherence residual equals its own orthogonal projection onto the `η`-grid, i.e. the residual
  -- `Y := (1_G + Γ_L) − Σ m_ij η_ij` is `0`.  This is the `orthogonal_split` + `leif`-equality step
  -- forced by the tightness `e = p q` (`ub_e`) **together with** each `|m_ij|² ≥ 1` (from the parities
  -- `m_row_odd`/`m_col_odd` above, `a_odd`), so `grid_mem` genuinely *depends on* the gated boundary
  -- parity.  Verified c-unreachable: the proven `NC ≤ 2` engine
  -- `grid_eq_zero_of_relation_of_card_le_two` (S16_GridExpansion) does not apply here (all `p q ≥ 15`
  -- coefficients are `±1`, so `NC = p q ≫ 2`), and the `bessel` proof only yields `⟨Y,Y⟩ ≥ 0`, not the
  -- tight `⟨Y,Y⟩ = 0`.  Mirror: the M-side `MHypothesis.betaGrid` (identical statement) is discharged
  -- by an explicit `sorry` at `exists_MHypothesis` tagged "genuine Track A obligation (issue 3002)".
  grid_mem := sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c)/(13.1.d), the L-side `η`-grid identity of the coherence residual.**
The residual `Δ_L = β_L − 1_G + ζ_0^ν` of the (7.8.a) Dade decomposition
(`beta_eq_constOne_sub_zetaImage_add_delta`, PROVEN) combines with the principal `1_G` to a
`±1`-signed sum of the whole `η`-grid: `1_G + Δ_L = Σ_{ij} ε_ij η_ij`, `ε_ij ∈ {±1}`.

This is the L-analog of the `M`-side field `MHypothesis.betaGrid` (which `betaM_expansion`
consumes), and of the Coq `FTtype2_support_coherence` core.  Here it is *proven* from the faithful
§14 grid-coefficient carrier `LSideGridCoeffData` and the PROVEN (3.7) four-corner relation
(`betaL_grid_relation`):

* the coefficients `m_ij = ⟨β_L, η_ij⟩` satisfy `m_ij + m_00 = m_i0 + m_0j` (3.7), so with the
  carried boundary parity (`m_00 = 1`, `m_0j`/`m_i0` odd) *every* `m_ij` is odd (hence `≠ 0`);
* the carried Bessel bound `Σ m_ij² ≤ p q = #grid` then sandwiches `#grid ≤ Σ m_ij² ≤ #grid`, so
  each `m_ij² = 1`, i.e. `m_ij = ±1` (`all_pm_one_and_card_of_odd_sq_sum_le`);
* the carried grid membership `1_G + Δ_L = Σ m_ij η_ij` is the displayed identity with `±1` signs.

The three deep facts are isolated in `lSideGridCoeffData`; this theorem is the honest `±1`
rigidity assembly.  The pure-algebra rearrangement into `β_L^τ = Σ ±η_ij − ε ζ_i^ν` is
`lSide_signed_eta_expansion`. -/
theorem lSide_delta_grid_expansion [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (dataL : TypeICoherent78Data L)
    (hq3 : hyp.base.q = 3) (hp5 : hyp.base.p = 5)
    (hepq : (dataL.h78 hG).complementIndex = hyp.base.p * hyp.base.q) :
    ∃ signs : Fin hyp.base.q → Fin hyp.base.p → ℤ,
      (∀ i j, signs i j = 1 ∨ signs i j = -1) ∧
        OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + (dataL.h78 hG).delta =
          ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
            (signs i j : ℂ) • hyp.base.eta i j := by
  classical
  set i₀ : Fin hyp.base.q := ⟨0, hyp.base.q_prime.pos⟩ with hi₀
  set j₀ : Fin hyp.base.p := ⟨0, hyp.base.p_prime.pos⟩ with hj₀
  obtain ⟨m, hcoeff, hprin, hrow, hcol, hbessel, hmem⟩ :=
    lSideGridCoeffData hG hyp hLmax dataL hq3 hp5 hepq
  -- (3.7) four-corner relation on `m_ij` (from `betaL_grid_relation`, via the integrality bridge).
  have hrel : ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      m i j + m i₀ j₀ = m i j₀ + m i₀ j := by
    intro i j
    have h := betaL_grid_relation hG hLmax dataL i j
    rw [hcoeff i j, hcoeff i₀ j₀, hcoeff i j₀, hcoeff i₀ j] at h
    exact_mod_cast h
  -- every coefficient is odd: `m_ij = m_i0 + m_0j − m_00` with the three boundary values odd.
  have hodd : ∀ p : Fin hyp.base.q × Fin hyp.base.p, Odd (m p.1 p.2) := by
    rintro ⟨i, j⟩
    by_cases hi : i = i₀ <;> by_cases hj : j = j₀
    · subst hi; subst hj; rw [hprin]; exact ⟨0, rfl⟩
    · subst hi; exact hrow j hj
    · subst hj; exact hcol i hi
    · -- `m_ij = m_i0 + m_0j − 1` (rel + `m_00 = 1`), sum of two odds minus odd is odd.
      have h := hrel i j
      rw [hprin] at h
      have hval : m i j = m i j₀ + m i₀ j - 1 := by omega
      obtain ⟨r, hr⟩ := hcol i hi
      obtain ⟨s, hs⟩ := hrow j hj
      exact ⟨r + s, by rw [hval, hr, hs]; ring⟩
  -- rigidity: `Σ m_ij² ≤ pq = #grid` with all odd forces each `m_ij = ±1`.
  have hcard : Fintype.card (Fin hyp.base.q × Fin hyp.base.p) = hyp.base.p * hyp.base.q := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.mul_comm]
  have hsq : ∑ p : Fin hyp.base.q × Fin hyp.base.p, (m p.1 p.2) ^ 2
      ≤ ((hyp.base.p * hyp.base.q + 1 : ℕ) : ℤ) - 1 := by
    rw [Fintype.sum_prod_type]; push_cast; linarith [hbessel]
  have hle : ((hyp.base.p * hyp.base.q + 1 : ℕ) : ℤ)
      ≤ (Fintype.card (Fin hyp.base.q × Fin hyp.base.p) : ℤ) + 1 := by
    rw [hcard]; push_cast; omega
  obtain ⟨_, hpm⟩ := all_pm_one_and_card_of_odd_sq_sum_le
    (fun p : Fin hyp.base.q × Fin hyp.base.p => m p.1 p.2) (hyp.base.p * hyp.base.q + 1)
    hodd hsq hle
  exact ⟨m, fun i j => hpm (i, j), hmem⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`e_L = |L : H_L| = p q`** for the (14.3) L-side.  The (7.8) complement index
`complementIndex = [L : kernelIn]` of *any* coherence bundle `dataL` on `L` equals the order of
the (14.3) Frobenius complement of `L` (`Ldata.typeI_data.frobenius`), because both complement the
*same* canonical kernel `H_L = maxNilpotentNormalHall L` (`kernel_le`/`typeF.H_eq`), so both have
order `[L : H_L]`.  That complement has order `p q` by (14.3) `typeI_complement_card_eq_pq`. -/
theorem typeICoherent78_complementIndex_eq_pq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Ldata : LHypothesis hyp) (dataL : TypeICoherent78Data Ldata.L) :
    (dataL.h78 hG).complementIndex = hyp.base.p * hyp.base.q := by
  haveI := dataL.kernelIn_normal
  have hLeq : Ldata.typeI_data.L = Ldata.L := Ldata.typeI_data_L_eq
  -- `complementIndex = |dataL.C|` (Frobenius complement of `kernelIn`).
  have hcomplD : Nat.card ↥dataL.kernelIn * Nat.card ↥dataL.C = Nat.card ↥Ldata.L :=
    dataL.hFrob.isComplement.card_mul_card
  have hce : (dataL.h78 hG).complementIndex = Nat.card ↥dataL.C := by
    show Nat.card ↥Ldata.L / Nat.card dataL.kernel = Nat.card ↥dataL.C
    rw [show Nat.card dataL.kernel = Nat.card ↥dataL.kernelIn from
        (dataL.kernelOrder_eq hG) ▸ rfl,
      ← hcomplD, Nat.mul_div_cancel_left _ Nat.card_pos]
  -- `|kernelIn| · |Ldata-complement| = |L|` (the (14.3) Frobenius package), after transporting
  -- the cards from the ambient `typeI_data.L` to `L` and identifying the canonical kernel.
  have hcomplL0 :=
    Ldata.typeI_data.frobenius.frobenius.isComplement.card_mul_card
  have hkerDeq : dataL.kernel = maxNilpotentNormalHall Ldata.L := by
    rw [show dataL.kernel = dataL.typeIHyp.typeI.typeF.H from rfl,
      dataL.typeIHyp.typeI.typeF.H_eq]
  have hkercard : Nat.card ↥((Ldata.typeI_data.frobenius.typeI.typeF.H).subgroupOf
        Ldata.typeI_data.L)
      = Nat.card ↥dataL.kernelIn := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        Ldata.typeI_data.frobenius.typeI.typeF.H_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe dataL.kernel_le).toEquiv,
      hkerDeq, Ldata.typeI_data.frobenius.typeI.typeF.H_eq, hLeq]
  have hLcard : Nat.card ↥Ldata.typeI_data.L = Nat.card ↥Ldata.L := by rw [hLeq]
  have hcomplL : Nat.card ↥dataL.kernelIn
      * Nat.card ↥Ldata.typeI_data.frobenius.complement = Nat.card ↥Ldata.L := by
    rw [← hkercard, ← hLcard]; exact hcomplL0
  -- hence `|dataL.C| = |Ldata-complement| = p q`.
  have hCeq : Nat.card ↥dataL.C = Nat.card ↥Ldata.typeI_data.frobenius.complement :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcomplD.trans hcomplL.symm)
  rw [hce, hCeq]
  exact Ldata.typeI_complement_card_eq_pq

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c), the L-side signed `η`-grid expansion.**  Under case-(b)
(`(q,p) = (3,5)`) and the two gap inequalities, (13.19.c) applied on the S- and T-sides gives
the (14.11.2)-style signed expansion `β_L^τ = Σ_{ij} ε_ij η_ij − ε ζ_i^ν` of the L-side, with
the removed unit-norm member an `L`-family coherent image (`i ≠ ind1H`; the `−ψ̄^{τ₁}`
alternative is the conjugate member `conjIndex`).

De-scaffolded (lane c, mirroring the `M`-side `betaM_expansion`): the removed member is the
distinguished coherent image `ζ_0^ν = ν(ζ_{zetaDistinct})` with `ε = 1` and
`zetaDistinct ≠ ind1H`, and the whole content is the pure-algebra rearrangement of the (7.8.a)
Dade decomposition `β_L = 1_G − ζ_0^ν + Δ_L` (`beta_eq_constOne_sub_zetaImage_add_delta`, PROVEN)
together with the `η`-grid identity `1_G + Δ_L = Σ ±η_ij` (`lSide_delta_grid_expansion`, whose
`±1` rigidity is *proven* from the (3.7) relation plus the isolated §14 grid-coefficient carrier
`lSideGridCoeffData`). -/
theorem lSide_signed_eta_expansion [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (dataL : TypeICoherent78Data nc.Ldata.L)
    (hq3 : hyp.base.q = 3) (hp5 : hyp.base.p = 5)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    ∃ signs : Fin hyp.base.q → Fin hyp.base.p → ℤ,
      (∀ i j, signs i j = 1 ∨ signs i j = -1) ∧
      ∃ i : Fin (dataL.n + 1), i ≠ dataL.ind1H ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        (dataL.h78 hG).beta
          = (∑ i' : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
              (signs i' j : ℂ) • hyp.base.eta i' j)
            - (ε : ℂ) • ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)) := by
  -- `e_L = |L : H_L| = p q` (`typeICoherent78_complementIndex_eq_pq`, the (14.3) Frobenius order).
  have hepq := typeICoherent78_complementIndex_eq_pq hG nc.Ldata dataL
  obtain ⟨signs, hsigns, hgrid⟩ :=
    lSide_delta_grid_expansion hG nc.Ldata.L_maximal dataL hq3 hp5 hepq
  -- the removed member is the distinguished coherent image `ζ_0^ν` (`ε = 1`, `zetaDistinct`)
  refine ⟨signs, hsigns, (dataL.h78 hG).zetaDistinct, ?_, 1, Or.inl rfl, ?_⟩
  · -- `zetaDistinct ≠ ind1H`
    have h := (dataL.h78 hG).zetaDistinct_ne_ind1H
    rwa [dataL.h78_ind1H_eq] at h
  · -- `β_L = (1_G + Δ_L) − ζ_0^ν = Σ ±η_ij − ζ_0^ν`
    rw [Int.cast_one, one_smul, ← hgrid,
      (dataL.h78 hG).beta_eq_constOne_sub_zetaImage_add_delta]
    abel

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The (14.16) expansion input** — the §13-gated character content of the case-(b)
contradiction, split into its two genuine textbook gates and the sorry-free (13.19.b) engine.
Under case-(b) (`(q,p) = (3,5)`) and the two gap inequalities:

* the L-side signed `η`-grid expansion `β_L^τ = Σ ±η_ij − ε ζ_i^ν` is the named (13.19.c)
  producer `lSide_signed_eta_expansion`;
* the M-side orthogonality `(η_ij, ψ^{τ₁}) = 0` (`ψ^{τ₁} = ζ_M^ν`) is **proven** by the
  (3.6)–(3.8)/(13.19.b) engine `caseB_eta_orthogonal_psi`, whose one residual input is the
  named (13.19.a) Dade-support avoidance `mSide_dadeSupport_avoids_regular`. -/
theorem caseB_expansion_input [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (dataL : TypeICoherent78Data nc.Ldata.L) (dataM : TypeICoherent78Data nc.Mdata.M)
    (hq3 : hyp.base.q = 3) (hp5 : hyp.base.p = 5)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    ∃ signs : Fin hyp.base.q → Fin hyp.base.p → ℤ,
      (∀ i j, signs i j = 1 ∨ signs i j = -1) ∧
      ∃ i : Fin (dataL.n + 1), i ≠ dataL.ind1H ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        (dataL.h78 _hG).beta
          = (∑ i' : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
              (signs i' j : ℂ) • hyp.base.eta i' j)
            - (ε : ℂ) • ((dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta i)) ∧
        ∀ (i' : Fin hyp.base.q) (j : Fin hyp.base.p),
          ClassFunction.inner (hyp.base.eta i' j)
            ((dataM.h78 _hG).nu
              ((dataM.h78 _hG).hyp76.zeta (dataM.h78 _hG).zetaDistinct)) = 0 := by
  obtain ⟨signs, hsigns, i, hi, ε, hε, hexp⟩ :=
    lSide_signed_eta_expansion _hG dataL hq3 hp5 hhv hvu
  exact ⟨signs, hsigns, i, hi, ε, hε, hexp,
    caseB_eta_orthogonal_psi _hG hyp.base dataM
      (mSide_dadeSupport_avoids_regular _hG nc.Mdata.M_maximal dataM)⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §16 producer for the (14.16) case-(b) contradiction inputs.**  The case-(b)
pairing comes from the enriched `OrthogonalitySwitchData.caseB_pairing` ((7.9) dichotomy);
the `χ_L ⊥ ψ^{τ₁}` orthogonality is the proven (4.1) cross-orthogonality
`pair_cross_orthogonal`; the remaining (13.19.c)/(14.11.2) grid content is the named
`caseB_expansion_input`. -/
theorem caseB_contradiction_data [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseB : data.caseB)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    Nonempty (CaseBContradictionData nc) := by
  obtain ⟨hq3, hp5⟩ := data.caseB_params hcaseB
  obtain ⟨dataL, dataM, hpair⟩ := data.caseB_pairing hcaseB _hG
  obtain ⟨signs, hsigns, i, hi, ε, hε, hexp, horth⟩ :=
    caseB_expansion_input _hG dataL dataM hq3 hp5 hhv hvu
  have hjne : (dataM.h78 _hG).zetaDistinct ≠ dataM.ind1H := by
    have h := (dataM.h78 _hG).zetaDistinct_ne_ind1H
    rwa [dataM.h78_ind1H_eq] at h
  refine ⟨{
    betaL := (dataL.h78 _hG).beta
    chiL := (ε : ℂ) • ((dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta i))
    psiImg := (dataM.h78 _hG).nu ((dataM.h78 _hG).hyp76.zeta (dataM.h78 _hG).zetaDistinct)
    signs := signs
    signs_pm_one := hsigns
    betaL_expansion := hexp
    eta_orthogonal_psi := horth
    chiL_orthogonal_psi := ?_
    pairing_ne_zero := hpair }⟩
  rw [ClassFunction.inner_smul_left,
    pair_cross_orthogonal dataL dataM _hG nc.Ldata.L_maximal nc.Mdata.M_maximal
      nc.not_conj hi hjne, mul_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.16)**: character-theoretic endpoint of the exceptional
case.  The two strict gap inequalities let (13.19.c) be applied on both the
S- and T-sides, giving the same signed `eta_ij` expansion as in (14.11.2) for
`beta_L^tau`; this contradicts the nonzero pairing in case-(b) of (14.14).

De-opacified (W4 §16, lane-h): the genuine character theory (the `β_L^τ` expansion, the `η`-grid /
`χ_L` orthogonalities to `ψ^{τ₁}`, and the case-(b) pairing) is the faithful `CaseBContradictionData`;
the contradiction itself is the pure inner-product computation `(β_L^τ, ψ^{τ₁}) = (Σ ±η_ij − χ_L, ψ^{τ₁})
= Σ ±·0 − 0 = 0`, contradicting `(β_L^τ, ψ^{τ₁}) ≠ 0`. -/
theorem caseB_character_contradiction_of_gap_inequalities
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseB : data.caseB)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    False := by
  -- The (14.11.2)-style signed `eta_ij` expansion of `beta_L^tau` and its orthogonalities.
  obtain ⟨⟨betaL, chiL, psiImg, signs, _hsigns, hexp, heta_orth, hchiL_orth, hpair_ne⟩⟩ :=
    caseB_contradiction_data _hG data hcaseB hhv hvu
  -- `(beta_L^tau, psi^tau_1) = 0` by linearity + orthogonality, contradicting case-(b).
  refine hpair_ne ?_
  rw [hexp, ClassFunction.inner_sub_left, hchiL_orth, sub_zero, inner_finset_sum_left]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [inner_finset_sum_left]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [ClassFunction.inner_smul_left, heta_orth i j, mul_zero]

/-- **Peterfalvi (14.16)**: consumer form of the exceptional case-(b) branch
under `H > U`.  All numerical work in the paragraph is discharged here; only
the named character-theoretic endpoint remains as a producer. -/
theorem caseB_contradiction_of_full_u_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Tdata : CaseBForTData hyp)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB)
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q])
    (hx_ne_one_of_quotient : ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1) :
    False := by
  have hu_full := data.u_eq_full_cyclotomic_of_caseB Sdata hcaseB
  have hh_lower := h_gt_two_mul_pq_mul_u_of_full_u_card_congruences
    _hG hu_full hu_dvd_h hh_mod_p hh_mod_q hu_mod_q hx_ne_one_of_quotient
  rcases data.caseB_gap_inequalities_of_h_gt_two_mul_pq_mul_u
      Tdata Sdata hcaseB hh_lower with ⟨hhv, hvu⟩
  exact data.caseB_character_contradiction_of_gap_inequalities _hG hcaseB hhv hvu

end OrthogonalitySwitchData

/-- For `p ≥ 7`, `p² ≤ 3^(p-3)`: the monotonicity input for the `p = 5` step of Peterfalvi (14.14.b).
The paper's `f(x) = 3^(x-3)/x²` is increasing for `x ≥ 2` (`f(x+1)/f(x) = 3(1 − 1/(x+1))² > 1`); this
is the integer form `p² ≤ 3^(p-3)` proved by induction from `p = 7` (`7² = 49 ≤ 81 = 3⁴`). -/
private theorem sq_le_three_pow_sub_three {p : ℕ} (hp : 7 ≤ p) : p ^ 2 ≤ 3 ^ (p - 3) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
      have hsucc : 3 ^ (p + 1 - 3) = 3 * 3 ^ (p - 3) := by
        rw [show p + 1 - 3 = (p - 3) + 1 by omega, pow_succ]; ring
      rw [hsucc]
      calc (p + 1) ^ 2 ≤ 3 * p ^ 2 := by nlinarith [hp]
        _ ≤ 3 * 3 ^ (p - 3) := by gcongr

namespace Hypothesis

/-- **Peterfalvi (14.14.b)/(14.15) arithmetic core**: in case (b) of the orthogonality switch, the
`(β_L, ψ)`-pairing bound `(v−1)/(pq) ≤ pq−1` together with the (14.4) cyclotomic value
`v = (q^p−1)/(q−1)` and the (14.8.a) exponential comparison `q^(p+1) > p^(q+1)` force the
exceptional primes `q = 3` and `p = 5`.

Proof (Pf p.91): `(v−1)/(pq) < pq` gives `q^(p−1) ≤ v−1 < p²q²`, hence `q^(p−3) < p²`.  By (14.8.a)
`q^(p+1) > p^(q+1)` and `q < p`, one gets `q^(p−3) > p^(q−3)`, so `p^(q−3) < p²`, whence `q = 3`.
Then `3^(p−3) < p²`, contradicting `p² ≤ 3^(p−3)` for `p ≥ 7`, so `p = 5`. -/
theorem caseB_forces_q_three_and_p_five (hyp : Hypothesis (G := G))
    (hv : hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hbound : ((hyp.base.v - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ≤
      ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ)) :
    hyp.base.q = 3 ∧ hyp.base.p = 5 := by
  have hp_prime := hyp.base.p_prime
  have hq_prime := hyp.base.q_prime
  have hqp : hyp.base.q < hyp.base.p := hyp.q_lt_p
  have hq3le : 3 ≤ hyp.base.q := by
    rcases hyp.base.q_odd with ⟨k, hk⟩; have := hq_prime.two_le; omega
  have hp5le : 5 ≤ hyp.base.p := by rcases hyp.base.p_odd with ⟨k, hk⟩; omega
  -- Step 1: `v − 1 < p² q²` from the case-(b) bound.
  have hpq_pos : 0 < hyp.base.p * hyp.base.q := Nat.mul_pos hp_prime.pos hq_prime.pos
  have hpqQ : (0 : ℚ) < ((hyp.base.p * hyp.base.q : ℕ) : ℚ) := by exact_mod_cast hpq_pos
  have hv1_le : (hyp.base.v - 1 : ℕ) ≤
      (hyp.base.p * hyp.base.q - 1) * (hyp.base.p * hyp.base.q) := by
    have h := (div_le_iff₀ hpqQ).mp hbound
    exact_mod_cast h
  have hv1_lt : hyp.base.v - 1 < hyp.base.p ^ 2 * hyp.base.q ^ 2 := by
    have hlt : (hyp.base.p * hyp.base.q - 1) * (hyp.base.p * hyp.base.q)
        < (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) :=
      mul_lt_mul_of_pos_right (by omega) hpq_pos
    calc hyp.base.v - 1
        ≤ (hyp.base.p * hyp.base.q - 1) * (hyp.base.p * hyp.base.q) := hv1_le
      _ < (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) := hlt
      _ = hyp.base.p ^ 2 * hyp.base.q ^ 2 := by ring
  -- Step 2: `q^(p−1) ≤ v − 1` from the geometric-sum lower bound.
  have hlow : hyp.base.q ^ (hyp.base.p - 1) ≤ hyp.base.v - 1 := by
    have h := cyclotomic_quotient_sub_one_ge_pow_pred hq_prime.two_le hp_prime.two_le
    rw [← hv] at h
    exact_mod_cast h
  -- Step 3: `q^(p−3) < p²`.
  have hqpm3 : hyp.base.q ^ (hyp.base.p - 3) < hyp.base.p ^ 2 := by
    have he : hyp.base.q ^ (hyp.base.p - 1)
        = hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have hlt : hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 2
        < hyp.base.p ^ 2 * hyp.base.q ^ 2 :=
      calc hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 2
          = hyp.base.q ^ (hyp.base.p - 1) := he.symm
        _ ≤ hyp.base.v - 1 := hlow
        _ < hyp.base.p ^ 2 * hyp.base.q ^ 2 := hv1_lt
    exact lt_of_mul_lt_mul_right hlt (Nat.zero_le _)
  -- Step 4: `p^(q−3) < q^(p−3)` from (14.8.a).
  have hkey : hyp.base.p ^ (hyp.base.q + 1) < hyp.base.q ^ (hyp.base.p + 1) := hyp.q_pow_gt_p_pow
  have hgt : hyp.base.p ^ (hyp.base.q - 3) < hyp.base.q ^ (hyp.base.p - 3) := by
    by_contra hle
    rw [not_lt] at hle
    have e1 : hyp.base.q ^ (hyp.base.p + 1)
        = hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 4 := by
      rw [← pow_add]; congr 1; omega
    have e2 : hyp.base.p ^ (hyp.base.q + 1)
        = hyp.base.p ^ (hyp.base.q - 3) * hyp.base.p ^ 4 := by
      rw [← pow_add]; congr 1; omega
    have hq4p4 : hyp.base.q ^ 4 < hyp.base.p ^ 4 := Nat.pow_lt_pow_left hqp (by norm_num)
    have hppos : 0 < hyp.base.p ^ (hyp.base.q - 3) := pow_pos hp_prime.pos _
    have h1 : hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 4
        ≤ hyp.base.p ^ (hyp.base.q - 3) * hyp.base.q ^ 4 := by gcongr
    have h2 : hyp.base.p ^ (hyp.base.q - 3) * hyp.base.q ^ 4
        < hyp.base.p ^ (hyp.base.q - 3) * hyp.base.p ^ 4 :=
      mul_lt_mul_of_pos_left hq4p4 hppos
    have hchain := lt_of_le_of_lt h1 h2
    rw [← e1, ← e2] at hchain
    omega
  -- Step 5: `q = 3`.
  have hq3 : hyp.base.q = 3 := by
    have hplt : hyp.base.p ^ (hyp.base.q - 3) < hyp.base.p ^ 2 := lt_trans hgt hqpm3
    have hexp : hyp.base.q - 3 < 2 := by
      by_contra hge
      rw [not_lt] at hge
      exact absurd hplt (not_lt.mpr (Nat.pow_le_pow_right (by omega) hge))
    rcases hyp.base.q_odd with ⟨k, hk⟩
    omega
  refine ⟨hq3, ?_⟩
  -- Step 6: `p = 5`.
  rw [hq3] at hqpm3
  by_contra hp_ne
  have hp7 : 7 ≤ hyp.base.p := by rcases hyp.base.p_odd with ⟨k, hk⟩; omega
  have := sq_le_three_pow_sub_three hp7
  omega

end Hypothesis

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.14) character dichotomy** — the genuine §7/§8 content of the orthogonality
switch.  By (8.17.c) the Dade supports `Ã₁(L)` and `Ã₁(M)` are disjoint, so by (7.9) either the
`M`-side pairing `(β_M^τ, φ^τ₁) ≠ 0` or the `L`-side pairing `(β_L^τ, ψ^τ₁) ≠ 0`.  In the first
case the (7.8.b) coherence-norm bound on the `β_M`-expansion `β_M^τ = a Σ aᵢ φᵢ^{τ₁} + Δ` gives
`Σ aᵢ² ≤ pq − 1`, i.e. `(h−1)/pq ≤ pq−1`; in the second the same estimate on the `β_L`-expansion
gives `(v−1)/pq ≤ pq−1`.  This isolates the character-theoretic input to `orthogonality_switch`;
the case-(b) passage to `q = 3`, `p = 5` is the arithmetic
`Hypothesis.caseB_forces_q_three_and_p_five`. -/
theorem orthogonality_switch_pairing_bounds [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (nc : NonConjugateHypothesis hyp) :
    (((nc.h - 1 : ℕ) : ℚ) / (hyp.base.p * hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ)) ∨
      ((∀ (hG : OddOrder.BG.IsMinimalSimpleOdd G),
          ∃ (dataL : TypeICoherent78Data nc.Ldata.L)
            (dataM : TypeICoherent78Data nc.Mdata.M),
            ClassFunction.inner
              ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                  nc.Mdata.M_maximal nc.not_conj).first.beta)
              ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                  nc.Mdata.M_maximal nc.not_conj).secondZetaImage) ≠ 0) ∧
        (((hyp.base.v - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ≤
          ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ))) := by
  classical
  -- The two (14.14) coherence bundles, for `L ⊇ N_G(U)` and `M ⊇ N_G(V)`.
  obtain ⟨dataL⟩ := TypeICoherent78Data.nonempty _hG nc.Ldata.L_maximal nc.Ldata.isTypeI
  obtain ⟨dataM⟩ := TypeICoherent78Data.nonempty _hG nc.Mdata.M_maximal
    ⟨nc.Mdata.typeIHyp.typeI⟩
  have hnc' : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup nc.Mdata.M nc.Ldata.L :=
    fun h => nc.not_conj h.symm
  -- `L`-side sizes: `|H| = h` and `[L : H] = p q`.
  have hcardL : Nat.card ↥dataL.kernelIn = nc.h := by
    have h1 : Nat.card ↥dataL.kernelIn = Nat.card ↥dataL.kernel :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe dataL.kernel_le).toEquiv
    have h2 : dataL.kernel = nc.Ldata.H := by
      rw [show dataL.kernel = maxNilpotentNormalHall nc.Ldata.L from
          dataL.typeIHyp.typeI.typeF.H_eq, ← nc.Ldata.H_eq_LF]
    rw [h1, h2, nc.h_eq_card_H]
  have hidxL : (dataL.kernelIn).index = hyp.base.p * hyp.base.q := by
    have h := OddOrder.Peterfalvi.S15.typeIFrobenius_kernel_index_eq_complement
      nc.Ldata.typeI_data.frobenius
    have h2 : dataL.kernelIn
        = (maxNilpotentNormalHall nc.Ldata.L).subgroupOf nc.Ldata.L := by
      rw [show dataL.kernelIn = (dataL.typeIHyp.typeI.typeF.H).subgroupOf nc.Ldata.L
          from rfl, dataL.typeIHyp.typeI.typeF.H_eq]
    rw [h2, ← nc.Ldata.typeI_data_L_eq]
    exact h.trans nc.Ldata.typeI_complement_card_eq_pq
  -- `M`-side sizes: `|K| = v` ((14.11) `K = V`, `|V| = v·d`, `d = 1`) and `[M : K] = p q`.
  obtain ⟨hKV, hepq⟩ := K_eq_V_index_pq _hG hyp nc.Ldata nc.Mdata
  have hkerM : dataM.kernel = nc.Mdata.K := by
    rw [show dataM.kernel = maxNilpotentNormalHall nc.Mdata.M from
        dataM.typeIHyp.typeI.typeF.H_eq, ← nc.Mdata.K_eq_MF]
  have hd1 : hyp.base.d = 1 := by
    have hTII : IsTypeII hyp.base.T := T_typeII _hG hyp
    have hDbot : hyp.base.D = ⊥ := by
      rw [hyp.base.D_eq]
      exact OddOrder.Peterfalvi.S15.V_inf_centralizer_Q_eq_bot _hG hyp.base hTII
    rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
  have hcardM : Nat.card ↥dataM.kernelIn = hyp.base.v := by
    have h1 : Nat.card ↥dataM.kernelIn = Nat.card ↥dataM.kernel :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe dataM.kernel_le).toEquiv
    rw [h1, hkerM, hKV, hyp.base.card_V_eq_vd, hd1, mul_one]
  have hidxM : (dataM.kernelIn).index = hyp.base.p * hyp.base.q := by
    have h1 : dataM.kernelIn = nc.Mdata.K.subgroupOf nc.Mdata.M := by
      rw [show dataM.kernelIn = (dataM.kernel).subgroupOf nc.Mdata.M from rfl, hkerM]
    rw [h1, ← nc.Mdata.e_eq_index]
    exact hepq
  -- Convert the `ℚ`-subtractions to the `ℕ`-subtraction casts of the statement.
  have hpq1 : 1 ≤ hyp.base.p * hyp.base.q :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hyp.base.p_prime.pos.ne' hyp.base.q_prime.pos.ne')
  have hv1 : 1 ≤ hyp.base.v := by
    have hVpos : 0 < Nat.card ↥hyp.base.V := Nat.card_pos
    rw [hyp.base.card_V_eq_vd, hd1, mul_one] at hVpos
    exact hVpos
  have hh1 : 1 ≤ nc.h := (nc.h_odd _hG).pos
  -- The (7.9) pairing dichotomy, with the pairing itself retained in the case-(b) branch.
  rcases pairing_dichotomy dataL dataM _hG nc.Ldata.L_maximal nc.Mdata.M_maximal
      nc.not_conj with hfirst | hsecond
  · -- `⟨β_L, ζ_M^ν⟩ ≠ 0`: the `M`-kernel Bessel bound `(v − 1)/pq ≤ pq − 1` + the pairing.
    right
    have hMK := bessel_bound_of_inner_beta_zeta_ne_zero dataM dataL _hG
      nc.Mdata.M_maximal nc.Ldata.L_maximal hnc' hfirst
    rw [dataL.complementIndex_eq _hG, hcardM, hidxM, hidxL] at hMK
    refine ⟨fun hG' => ⟨dataL, dataM, hfirst⟩, ?_⟩
    rw [Nat.cast_sub hv1, Nat.cast_sub hpq1]
    push_cast at hMK ⊢
    convert hMK using 2
  · -- `⟨β_M, ζ_L^ν⟩ ≠ 0`: the `L`-kernel Bessel bound `(h − 1)/pq ≤ pq − 1`.
    left
    have hLH := bessel_bound_of_inner_beta_zeta_ne_zero dataL dataM _hG
      nc.Ldata.L_maximal nc.Mdata.M_maximal nc.not_conj hsecond
    rw [dataM.complementIndex_eq _hG, hcardL, hidxL, hidxM] at hLH
    rw [Nat.cast_sub hh1, Nat.cast_sub hpq1]
    push_cast at hLH ⊢
    convert hLH using 2

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.14)**: either the case-(a) bound `(h − 1)/pq ≤ pq − 1` holds (the
`β_M`--`φ` pairing is nonzero), or the case-(b) exceptional primes `q = 3`, `p = 5` hold (the
`β_L`--`ψ` pairing is nonzero).

Assembled from the (7.9)+(8.17.c) character dichotomy `orthogonality_switch_pairing_bounds`, whose
two branches supply the case-(a) norm bound and the case-(b) `(v−1)/pq ≤ pq−1` bound; in case (b)
the arithmetic `caseB_forces_q_three_and_p_five` ((14.15)/(14.8.a)) turns that bound, together with
the (14.4) cyclotomic value of `v`, into `q = 3`, `p = 5`.  The abstract `caseA`/`caseB` props of
`OrthogonalitySwitchData` are taken to be the case-(a) bound and the `(q,p)=(3,5)` conclusion
themselves, so the downstream (14.15)/(14.16) machinery reads them off directly. -/
theorem orthogonality_switch [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (nc : NonConjugateHypothesis hyp) :
    ∃ data : OrthogonalitySwitchData nc, data.caseA ∨ data.caseB := by
  obtain ⟨_Tdata, _, hv⟩ := caseB_for_T _hG hyp
  refine ⟨{
    caseA := ((nc.h - 1 : ℕ) : ℚ) / (hyp.base.p * hyp.base.q : ℚ) ≤
      ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ)
    caseA_bound := fun h => h
    caseB := (hyp.base.q = 3 ∧ hyp.base.p = 5) ∧
      haveI := hyp.base.finiteG
      ∀ (hG : OddOrder.BG.IsMinimalSimpleOdd G),
        ∃ (dataL : TypeICoherent78Data nc.Ldata.L) (dataM : TypeICoherent78Data nc.Mdata.M),
          ClassFunction.inner
            ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                nc.Mdata.M_maximal nc.not_conj).first.beta)
            ((hypothesis79OfNonconjugate dataL dataM hG nc.Ldata.L_maximal
                nc.Mdata.M_maximal nc.not_conj).secondZetaImage) ≠ 0
    caseB_params := fun h => h.1
    caseB_pairing := fun h => h.2 }, ?_⟩
  rcases orthogonality_switch_pairing_bounds _hG hyp nc with hA | ⟨hpair, hB⟩
  · exact Or.inl hA
  · exact Or.inr ⟨hyp.caseB_forces_q_three_and_p_five hv hB, hpair⟩

/-- **Peterfalvi (14.14)--(14.15)**: the full `u` value once the
cardinality consequences of (14.5) have been materialized.  The case-(b)
alternative of (14.14) is already full by the S-side order data; in case (a),
assuming the non-full value contradicts the fixed-point-free cardinal
congruences for `H` and `U`. -/
theorem u_final_value_of_fpf_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp)
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q]) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  rcases orthogonality_switch _hG hyp nc with ⟨data, hcase⟩
  rcases caseB_for_S _hG hyp nc.Ldata with ⟨Sdata, _hS_caseB⟩
  rcases hcase with hcaseA | hcaseB
  · by_contra hu_not_full
    exact data.caseA_contradiction_of_nonfull_fpf_card_congruences
      _hG Sdata hcaseA hu_not_full hu_dvd_h hh_mod_p hh_mod_q hu_mod_q
  · exact data.u_eq_full_cyclotomic_of_caseB Sdata hcaseB

/-- **Peterfalvi (14.15)**: `u` has the full cyclotomic value
`(p^q - 1) / (p - 1)`.

The proof consumes the cardinal consequences of (14.5): `u ∣ h`, the two
Frobenius-kernel congruences for `h`, and the fixed-point-free cardinal
congruence for `U`.  The arithmetic contradiction is packaged in
`u_final_value_of_fpf_card_congruences`. -/
theorem u_final_value [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  rcases nc.h_modEq_one_mod_p_and_q _hG with ⟨hh_mod_p, hh_mod_q⟩
  exact u_final_value_of_fpf_card_congruences _hG hyp nc (nc.u_dvd_h _hG)
    hh_mod_p hh_mod_q (hyp.u_modEq_one_mod_q _hG)

/-- **Peterfalvi (14.16)**: in the non-conjugate case, the kernel `H` is
exactly `U`. -/
theorem H_eq_U [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp) :
    nc.Ldata.H = hyp.base.U := by
  by_contra hHU
  rcases orthogonality_switch _hG hyp nc with ⟨data, hcase⟩
  rcases caseB_for_T _hG hyp with ⟨Tdata, _hT_caseB, _hv_eq⟩
  rcases caseB_for_S _hG hyp nc.Ldata with ⟨Sdata, _hS_caseB⟩
  have hu_full := u_final_value _hG hyp nc
  rcases nc.h_modEq_one_mod_p_and_q _hG with ⟨hh_mod_p, hh_mod_q⟩
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc, OddOrder.Peterfalvi.S15.c_eq_one _hG hyp.base, mul_one]
  have hU_le_H : hyp.base.U ≤ nc.Ldata.H := by
    rw [← nc.Ldata.typeI_data_H_eq]
    exact nc.Ldata.typeI_data.U_le_H
  have hx_ne_one_of_quotient :
      ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1 := by
    intro x hh_eq hx1
    have hH_card_eq_U_card : Nat.card ↥nc.Ldata.H = Nat.card ↥hyp.base.U := by
      rw [← nc.h_eq_card_H, hh_eq, hx1, mul_one, hU_card]
    have hU_eq_H : hyp.base.U = nc.Ldata.H :=
      Subgroup.eq_of_le_of_card_ge hU_le_H (le_of_eq hH_card_eq_U_card)
    exact hHU hU_eq_H.symm
  rcases hcase with hcaseA | hcaseB
  · exact data.caseA_contradiction_of_full_u_card_congruences
      _hG Sdata hcaseA hu_full (nc.u_dvd_h _hG) hh_mod_p hh_mod_q
      (hyp.u_modEq_one_mod_q _hG) hx_ne_one_of_quotient
  · exact data.caseB_contradiction_of_full_u_card_congruences
      _hG Tdata Sdata hcaseB (nc.u_dvd_h _hG) hh_mod_p hh_mod_q
      (hyp.u_modEq_one_mod_q _hG) hx_ne_one_of_quotient

/-- **Peterfalvi §8 / BG 15.7(a)**: the type-`P` Fitting core `P = S_F` is a TI-subgroup of `G`.
`S` is type-`P₂` (`S_typeP2`), so `F(S)` is TI (`fittingIsTI_of_isTypeP2`), whence the Fitting core
`S_F#` is TI (`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`; `sharpSubgroup = ·∖{1}`
matches `Subgroup.IsTI`).  Supplies the `P_isTI` field of `MHypothesis`. -/
theorem base_P_isTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : Subgroup.IsTI hyp.base.P := by
  rw [hyp.base.P_eq_SF]
  exact OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG
    hyp.base.S_maximal
    (OddOrder.BG.Ch4.S15.fittingIsTI_of_isTypeP2 hG hyp.base.S_maximal hyp.base.S_typeP2)

/-- **Peterfalvi §8, `T`-side**: the type-`P` Fitting core `Q = T_F` is a TI-subgroup of `G`.
`T`-side dual of `base_P_isTI` via `fittingIsTI_T` (`T` type II ⟹ type-`P₂`).  Supplies the `Q_isTI`
field of `MHypothesis`. -/
theorem base_Q_isTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTII : IsTypeII hyp.base.T) : Subgroup.IsTI hyp.base.Q := by
  rw [hyp.base.Q_eq_TF]
  exact OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG
    hyp.base.T_maximal (OddOrder.Peterfalvi.S15.fittingIsTI_T hG hyp.base hTII)

/-- **Peterfalvi §13 `normalizer_V` (the `W`-exceptional-set normalizer)**: every nonempty
`X ⊆ W − (W₁ ∪ W₂)` has `N_G(X) = W`.  Read off the S-side type-`P` data `Sdata.normalizer_V`
((8.8) `W = W₁ × W₂` cyclic-TI structure), reconciled to the base `W`/`W₁`/`W₂`
(`Sdata_W1_eq`/`Sdata_W2_eq`, `W_eq_join`).  Supplies `MHypothesis`'s `W_normalizer_V`. -/
theorem base_W_normalizer_V (hyp : Hypothesis (G := G)) :
    ∀ X : Set G, X.Nonempty →
      X ⊆ (hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)) →
      Subgroup.normalizer X = hyp.base.W := by
  have hWeq : hyp.base.Sdata.W = hyp.base.W := by
    rw [hyp.base.Sdata.W_eq, hyp.base.Sdata_W1_eq, hyp.base.Sdata_W2_eq]
    exact hyp.base.W_eq_join.symm
  intro X hX hXsub
  rw [← hWeq]
  refine hyp.base.Sdata.normalizer_V X hX ?_
  rw [hWeq, hyp.base.Sdata_W1_eq, hyp.base.Sdata_W2_eq]
  exact hXsub

/-- **Order factorization of the type-`P` maximal `S`**: `|P| · |U| · |W₁| = |S|`
(`S = (P ⋊ U) ⋊ W₁`, `P = S_F`, `S' = P ⋊ U`).  From the `Sdata` complement indices
`card_W1_eq_derived_index` (`|W₁| = [S:S']`) and `card_U_eq_index` (`|U| = [S':P]`) via
`Subgroup.card_mul_index`. -/
theorem base_card_S_eq [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.base.P * Nat.card ↥hyp.base.U * Nat.card ↥hyp.base.W1
      = Nat.card ↥hyp.base.S := by
  have hW1 : Nat.card ↥hyp.base.W1 = Nat.card ↥hyp.base.Sdata.W1 := by rw [hyp.base.Sdata_W1_eq]
  have hU : Nat.card ↥hyp.base.U = Nat.card ↥hyp.base.Sdata.U := by rw [hyp.base.Sdata_U_eq]
  have hP : hyp.base.P = maxNilpotentNormalHall hyp.base.S := hyp.base.P_eq_SF
  have hDle : derivedInG hyp.base.S ≤ hyp.base.S := Subgroup.map_subtype_le _
  have hPle : maxNilpotentNormalHall hyp.base.S ≤ derivedInG hyp.base.S := by
    rw [hyp.base.S_deriv_eq_PU, ← hP]; exact le_sup_left
  have c1 : Nat.card ↥(derivedInG hyp.base.S) * Nat.card ↥hyp.base.Sdata.W1
      = Nat.card ↥hyp.base.S := by
    rw [hyp.base.Sdata.card_W1_eq_derived_index,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv]
    exact Subgroup.card_mul_index _
  have c2 : Nat.card ↥(maxNilpotentNormalHall hyp.base.S) * Nat.card ↥hyp.base.Sdata.U
      = Nat.card ↥(derivedInG hyp.base.S) := by
    rw [hyp.base.Sdata.card_U_eq_index,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv]
    exact Subgroup.card_mul_index _
  rw [hW1, hU, hP, ← c1, ← c2]

/-- **Peterfalvi (14.11.4)**: `|N_G(P)| = |P| · u · q`.  The Fitting core `P = S_F` is normal in
the maximal `S` and nontrivial (`W₂ ≤ P`), so `N_G(P) = S`
(`normalizer_eq_self_of_subgroupOf_normal_of_ne_bot`); then `|S| = |P|·|U|·|W₁|` (`base_card_S_eq`)
with `|U| = u·c`, `c = 1` (`S15.c_eq_one`), `|W₁| = q`.  Supplies `MHypothesis`'s
`card_normalizer_P_eq`. -/
theorem base_card_normalizer_P_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G))
      = Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q := by
  have hPne : maxNilpotentNormalHall hyp.base.S ≠ ⊥ := by
    intro hbot
    have hW2 := OddOrder.Peterfalvi.S15.W2_le_P hG hyp.base
    rw [hyp.base.P_eq_SF, hbot, le_bot_iff] at hW2
    have hp1 : hyp.base.p = 1 := by rw [hyp.base.p_eq_card_W2, hW2, Subgroup.card_bot]
    exact hyp.base.p_prime.one_lt.ne' hp1
  have hNP : Subgroup.normalizer (hyp.base.P : Set G) = hyp.base.S := by
    rw [hyp.base.P_eq_SF]
    exact OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG
      hyp.base.S_maximal (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _)
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal _) hPne
  rw [hNP, ← base_card_S_eq hyp, hyp.base.card_U_eq_uc,
    OddOrder.Peterfalvi.S15.c_eq_one hG hyp.base, mul_one, hyp.base.q_eq_card_W1]

/-- **Order factorization of the type-`P` maximal `T`** (T-side dual of `base_card_S_eq`):
`|Q| · |V| · |W₂| = |T|`, from a reconciled `TypePData T` (`tpd.U = V`, `tpd.W1 = W₂`, `Q = T_F`)
via `card_W1_eq_derived_index` / `card_U_eq_index` and `Subgroup.card_mul_index`. -/
theorem base_card_T_eq [Finite G] (hyp : Hypothesis (G := G))
    (tpd : OddOrder.GroupTheory.TypePData hyp.base.T) (hU : tpd.U = hyp.base.V)
    (hW1 : tpd.W1 = hyp.base.W2) :
    Nat.card ↥hyp.base.Q * Nat.card ↥hyp.base.V * Nat.card ↥hyp.base.W2
      = Nat.card ↥hyp.base.T := by
  have hW2c : Nat.card ↥hyp.base.W2 = Nat.card ↥tpd.W1 := by rw [hW1]
  have hVc : Nat.card ↥hyp.base.V = Nat.card ↥tpd.U := by rw [hU]
  have hQ : hyp.base.Q = maxNilpotentNormalHall hyp.base.T := hyp.base.Q_eq_TF
  have hDle : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hQle : maxNilpotentNormalHall hyp.base.T ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV, ← hQ]; exact le_sup_left
  have c1 : Nat.card ↥(derivedInG hyp.base.T) * Nat.card ↥tpd.W1 = Nat.card ↥hyp.base.T := by
    rw [tpd.card_W1_eq_derived_index, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv]
    exact Subgroup.card_mul_index _
  have c2 : Nat.card ↥(maxNilpotentNormalHall hyp.base.T) * Nat.card ↥tpd.U
      = Nat.card ↥(derivedInG hyp.base.T) := by
    rw [tpd.card_U_eq_index, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv]
    exact Subgroup.card_mul_index _
  rw [hW2c, hVc, hQ, ← c1, ← c2]

/-- **Peterfalvi (14.11.4)**: `|N_G(Q)| = |Q| · v · p` (T-side dual of `base_card_normalizer_P_eq`).
`Q = T_F` is normal in the maximal `T` and nontrivial (`W₁ ≤ Q`), so `N_G(Q) = T`; then
`|T| = |Q|·|V|·|W₂|` (`base_card_T_eq`) with `|V| = v·d`, `d = 1` (`V_inf_centralizer_Q_eq_bot`,
`D = V ⊓ C_G(Q) = ⊥`), `|W₂| = p`.  Supplies `MHypothesis`'s `card_normalizer_Q_eq`. -/
theorem base_card_normalizer_Q_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTII : IsTypeII hyp.base.T) :
    Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G))
      = Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p := by
  obtain ⟨tpd, hU, hW1, hW2⟩ := OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp.base
  have hQne : maxNilpotentNormalHall hyp.base.T ≠ ⊥ := by
    intro hbot
    have hW1le : hyp.base.W1 ≤ maxNilpotentNormalHall hyp.base.T := by
      rw [← hW2]
      exact le_trans tpd.W2_le (le_trans inf_le_left (le_of_eq tpd.H_eq))
    rw [hbot, le_bot_iff] at hW1le
    have hq1 : hyp.base.q = 1 := by rw [hyp.base.q_eq_card_W1, hW1le, Subgroup.card_bot]
    exact hyp.base.q_prime.one_lt.ne' hq1
  have hNQ : Subgroup.normalizer (hyp.base.Q : Set G) = hyp.base.T := by
    rw [hyp.base.Q_eq_TF]
    exact OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG
      hyp.base.T_maximal (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _)
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal _) hQne
  have hd1 : hyp.base.d = 1 := by
    have hDbot : hyp.base.D = ⊥ := by
      rw [hyp.base.D_eq]
      exact OddOrder.Peterfalvi.S15.V_inf_centralizer_Q_eq_bot hG hyp.base hTII
    rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
  rw [hNQ, ← base_card_T_eq hyp tpd hU hW1, hyp.base.card_V_eq_vd, hd1, mul_one,
    hyp.base.p_eq_card_W2]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09 in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (7.8) for the V-side `M`** — the §7 coherence datum `S09.Hypothesis78` of the
type-I maximal subgroup `M` over `N_G(V)`, together with its structural data (maximality,
`N_G(V) ≤ M`, Fitting-kernel index `p q`).

This is the **V-side dual of `witness_L_hypothesis78`** (the (12.16) witness-side coherence):
`M`'s coherence is produced by the general type-I Frobenius engine `S14.frobenius_typeI_coherent`
(`M` is type-I Frobenius over `N_G(V)` with kernel `M_F`, from `typeII_overNormalizer_frobenius_V`),
and the (7.8) datum is assembled by the same `hypothesis78OfDade` construction (placed family
`exists_witness_placed_family`, `nu_isometry` from `coherence_extension_inner_eq_on_family`,
`hagree` from `coherence_hagree_dadeMap`).  Subsumes `exists_M_structural` and additionally supplies
the `h78` field of `MHypothesis` — the single **grid-independent** honest obligation of
`exists_MHypothesis` (the `betaGrid`/`betaM` fields remain gated on the §13 `η`-grid carrier, issue
3002). -/
theorem exists_M_hypothesis78 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTII : IsTypeII hyp.base.T) :
    ∃ (M : Subgroup G) (typeIHyp : OddOrder.Peterfalvi.S14.Hypothesis M),
      M ∈ maximalSubgroups G ∧
        Subgroup.normalizer (hyp.base.V : Set G) ≤ M ∧
          ((maxNilpotentNormalHall M).subgroupOf M).index = hyp.base.p * hyp.base.q ∧
          ∃ h78 : OddOrder.Peterfalvi.S09.Hypothesis78 G
              (OddOrder.GroupTheory.typeIA M typeIHyp.typeI) M,
            h78.hyp76.H = maxNilpotentNormalHall M ∧
              h78.hyp76.hyp71.hyp = typeIHyp.dadeData.dade ∧
              h78.hyp76.zeta h78.ind1H (1 : M)
                = (((maxNilpotentNormalHall M).subgroupOf M).index : ℂ) ∧
              ClassFunction.inner (h78.hyp76.zeta h78.zetaDistinct)
                (h78.hyp76.zeta h78.zetaDistinct) = 1 ∧
              (1 : ℝ) - (h78.complementIndex : ℝ) / (h78.kernelOrder : ℝ)
                ≤ h78.zetaNuRhoNormSq := by
  classical
  obtain ⟨vdata, _hker, _hVH⟩ :=
    OddOrder.Peterfalvi.S15.typeII_overNormalizer_frobenius_V hG hyp.base hTII
  have hMtypeI : IsTypeI vdata.L := ⟨vdata.frobenius.typeI⟩
  obtain ⟨typeIHyp⟩ :=
    OddOrder.Peterfalvi.S14.exists_typeI_hypothesis hG vdata.L_maximal hMtypeI
  have hindex : ((maxNilpotentNormalHall vdata.L).subgroupOf vdata.L).index
      = hyp.base.p * hyp.base.q := by
    rw [OddOrder.Peterfalvi.S15.typeIFrobenius_kernel_index_eq_complement vdata.frobenius]
    exact vdata.complement_card_eq_pq
  refine ⟨vdata.L, typeIHyp, vdata.L_maximal, vdata.normalizer_V_le_L, hindex, ?_⟩
  -- Coherence for `M` via the general type-I Frobenius engine: the Frobenius witness for
  -- `typeIHyp.H = M_F` comes from `vdata.frobenius` (both kernels are `maxNilpotentNormalHall M`).
  have hHeq : typeIHyp.typeI.typeF.H = vdata.frobenius.typeI.typeF.H := by
    rw [typeIHyp.typeI.typeF.H_eq, vdata.frobenius.typeI.typeF.H_eq]
  have hfrob : ∃ C : Subgroup ↥vdata.L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥vdata.L
        ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L) C :=
    ⟨vdata.frobenius.complement, by rw [hHeq]; exact vdata.frobenius.frobenius⟩
  obtain ⟨coh⟩ := OddOrder.Peterfalvi.S14.frobenius_typeI_coherent hG typeIHyp hfrob
  -- Mirror `witness_L_hypothesis78`'s `hypothesis78OfDade` assembly (generic in the hypothesis).
  have hHL : typeIHyp.typeI.typeF.H ≤ vdata.L := typeIHyp.typeI.typeF.H_le
  haveI hKnormal : ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L).Normal := by
    rw [typeIHyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal vdata.L
  have hAH : OddOrder.GroupTheory.typeIA vdata.L typeIHyp.typeI
      = (typeIHyp.typeI.typeF.H : Set G) \ {1} :=
    OddOrder.Peterfalvi.S14.Hypothesis.typeIA_eq_sharp hG typeIHyp
  have hHnorm : ∀ (l : ↥vdata.L) {h : G}, h ∈ typeIHyp.typeI.typeF.H →
      (l : G) * h * (l : G)⁻¹ ∈ typeIHyp.typeI.typeF.H := by
    intro l h hh
    have hhL : h ∈ vdata.L := hHL hh
    have hmem : (⟨h, hhL⟩ : ↥vdata.L) ∈ (typeIHyp.typeI.typeF.H).subgroupOf vdata.L :=
      (Subgroup.mem_subgroupOf).mpr hh
    have hconj := hKnormal.conj_mem ⟨h, hhL⟩ hmem l
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  obtain ⟨n, θ, ind1H, hind1H, hdeg0, htriv, hinj, hcover⟩ :=
    OddOrder.Peterfalvi.S14.exists_witness_placed_family typeIHyp
  have hSmem : ∀ i, i ≠ ind1H →
      ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
          (θ i : ClassFunction _ ℂ) ∈ typeIHyp.Sset := by
    intro i hi
    refine ⟨θ i, fun htriv_i => hi (hinj ?_), rfl⟩
    change ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
        (θ i : ClassFunction _ ℂ)
        = ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
          (θ ind1H : ClassFunction _ ℂ)
    rw [htriv_i, htriv]
  let d : Fin (n + 1) → ℂ :=
    fun i => (θ i : ClassFunction ↥((typeIHyp.typeI.typeF.H).subgroupOf vdata.L) ℂ)
      (1 : ↥((typeIHyp.typeI.typeF.H).subgroupOf vdata.L))
  have hd : ∀ i, d i = (θ i : ClassFunction ↥((typeIHyp.typeI.typeF.H).subgroupOf vdata.L) ℂ)
      (1 : ↥((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)) := fun _ => rfl
  have hdeg : ∀ i, ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
        (θ i : ClassFunction _ ℂ) (1 : ↥vdata.L)
      = d i * ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
        (θ 0 : ClassFunction _ ℂ) (1 : ↥vdata.L) := by
    intro i
    rw [ClassFunction.induce_apply_one ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
        (θ i : ClassFunction _ ℂ), hdeg0, hd i]
    ring
  have hdeg_match : ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
        (θ 0 : ClassFunction _ ℂ) (1 : ↥vdata.L)
      = ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
        (θ ind1H : ClassFunction _ ℂ) (1 : ↥vdata.L) := by
    rw [hdeg0, htriv]
    change (((typeIHyp.typeI.typeF.H).subgroupOf vdata.L).index : ℂ)
        = ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
          (trivialClassFunction ↥((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)) (1 : ↥vdata.L)
    rw [induce_trivialChar_apply_eq_index _ (Subgroup.one_mem _)]
  have psi_support : ∀ i, (ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
        (θ i : ClassFunction _ ℂ)
      - d i • ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf vdata.L)
          (θ 0 : ClassFunction _ ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.GroupTheory.typeIA vdata.L typeIHyp.typeI) vdata.L := by
    intro i
    refine (induce_diff_support (θ i) (θ 0) (d i) (hdeg i)).trans ?_
    intro x hx
    rw [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hx
    exact (mem_supportInSubgroup_sharp_subgroupOf_iff typeIHyp.typeI.typeF.H hAH x).mpr
      ⟨hx.1, hx.2⟩
  have hnu_isometry : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (coh.extension (ClassFunction.induce
          (typeIHyp.typeI.typeF.H.subgroupOf vdata.L) (θ i : ClassFunction _ ℂ)))
        (coh.extension (ClassFunction.induce
          (typeIHyp.typeI.typeF.H.subgroupOf vdata.L) (θ j : ClassFunction _ ℂ)))
        = ClassFunction.inner (ClassFunction.induce
            (typeIHyp.typeI.typeF.H.subgroupOf vdata.L) (θ i : ClassFunction _ ℂ))
          (ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
            (θ j : ClassFunction _ ℂ)) :=
    fun i j hi hj => coherence_extension_inner_eq_on_family coh (hSmem i hi) (hSmem j hj)
  have hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      typeIHyp.toHypothesis71.τ ⟨ClassFunction.induce
          (typeIHyp.typeI.typeF.H.subgroupOf vdata.L) (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
            (θ 0 : ClassFunction _ ℂ), psi_support i⟩
        = coh.extension (ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
            (θ i : ClassFunction _ ℂ))
          - d i • coh.extension (ClassFunction.induce
            (typeIHyp.typeI.typeF.H.subgroupOf vdata.L) (θ 0 : ClassFunction _ ℂ)) := by
    intro i _ hi_ind
    obtain ⟨deg_i, -, hdeg_i_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (θ i)
    exact coherence_hagree_dadeMap typeIHyp.dadeData.dade typeIHyp.hconj coh
      (hSmem i hi_ind) (hSmem 0 (Ne.symm hind1H)) (m0 := 1) (mi := deg_i) (by norm_num)
      (by rw [hd i, hdeg_i_eq, Nat.cast_one, div_one]) (psi_support i)
  refine ⟨hypothesis78OfDade typeIHyp.toHypothesis71
    (typeIHyp.dadeData.dade.fullDadeIsometryData typeIHyp.hconj).toDadeIsometryData.isDadeIsometry
    typeIHyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv
    hdeg_match coh.extension hnu_isometry hagree, ?_, rfl, ?_, ?_, ?_⟩
  · exact typeIHyp.typeI.typeF.H_eq
  · -- **Peterfalvi (7.6)/(14.10)**: the induced principal `ζ_{ind1H} = Ind_K 1_K` has
    -- degree `[M:K]` at `1` (`θ ind1H = 1_K` + `induce_trivialChar_apply_eq_index`).
    show ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
        (θ ind1H : ClassFunction _ ℂ) (1 : vdata.L)
        = (((maxNilpotentNormalHall vdata.L).subgroupOf vdata.L).index : ℂ)
    rw [htriv, ← typeIHyp.typeI.typeF.H_eq]
    exact induce_trivialChar_apply_eq_index _ (Subgroup.one_mem _)
  · -- **Peterfalvi (7.8)**: the distinguished `ζ = ζ_0 = Ind_K θ_0` (`θ_0 ≠ 1_K`) is irreducible
    -- (Frobenius, [Is] 6.34), hence `‖ζ‖² = 1` — the `ζ_0` unit-norm input to the (7.5)/(7.8) machinery.
    obtain ⟨C, hFrobG⟩ := hfrob
    have hθ0_ne : θ 0 ≠ trivialIrreducibleCharacter
        ↥(typeIHyp.typeI.typeF.H.subgroupOf vdata.L) := by
      intro h0triv
      refine hind1H ?_
      exact (hinj (show ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
            (θ 0 : ClassFunction _ ℂ)
          = ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
            (θ ind1H : ClassFunction _ ℂ) from by rw [h0triv, htriv])).symm
    show ClassFunction.inner
        (ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
          (θ 0 : ClassFunction _ ℂ))
        (ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
          (θ 0 : ClassFunction _ ℂ)) = 1
    exact inner_self_induce_eq_one_of_frobeniusGroup hFrobG (θ 0) hθ0_ne
  · -- **Peterfalvi (7.8.b)**: the coherence-norm lower bound `1 − e/h ≤ ‖ζ_0^{νρ}‖²` for the
    -- `V`-side `M`, via the concrete §7 producer `zetaNuRhoNormSqGeOfDade` (the `V`-side dual of
    -- `witness_L_zeta_bound`): feed the Dade witness `Hypothesis78` its four genuine (7.8) inputs —
    -- `ζ_0^ν ⊥ 1_G` (`witness_L_hzeta0nu`), `‖ζ_0‖² = 1` (Frobenius), `(β, ζ_0^ν) + 1 ∈ ℤ`
    -- (`exists_betaDecomp_a`), and `2e + 1 ≤ h`
    -- (`frobenius_two_mul_card_complement_add_one_le_card_kernel`).
    obtain ⟨C, hFrobG⟩ := hfrob
    have hθ0_ne : θ 0 ≠ trivialIrreducibleCharacter
        ↥(typeIHyp.typeI.typeF.H.subgroupOf vdata.L) := by
      intro h0triv
      refine hind1H ?_
      exact (hinj (show ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
            (θ 0 : ClassFunction _ ℂ)
          = ClassFunction.induce (typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
            (θ ind1H : ClassFunction _ ℂ) from by rw [h0triv, htriv])).symm
    set H78 := hypothesis78OfDade typeIHyp.toHypothesis71
      (typeIHyp.dadeData.dade.fullDadeIsometryData typeIHyp.hconj).toDadeIsometryData.isDadeIsometry
      typeIHyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv
      hdeg_match coh.extension hnu_isometry hagree with hH78def
    have hKcard : Nat.card ↥(typeIHyp.typeI.typeF.H.subgroupOf vdata.L)
        = Nat.card typeIHyp.typeI.typeF.H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
    have hKodd : Odd (Nat.card ↥(typeIHyp.typeI.typeF.H.subgroupOf vdata.L)) :=
      (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card vdata.L)).of_dvd_nat
        (Subgroup.card_subgroup_dvd_card _)
    have hCodd : Odd (Nat.card ↥C) :=
      (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card vdata.L)).of_dvd_nat
        (Subgroup.card_subgroup_dvd_card C)
    obtain ⟨a, ha⟩ := exists_betaDecomp_a H78
      (Submodule.sub_mem _
        (ClassFunction.induce_mem_ZIrr _ (θ ind1H).property.mem_ZIrr)
        (ClassFunction.induce_mem_ZIrr _ (θ 0).property.mem_ZIrr))
      (coh.extension_mem_ZIrr _ (Submodule.subset_span (hSmem 0 (Ne.symm hind1H))))
    have hsmall : H78.smallIndex := by
      have hfrobB := OddOrder.Peterfalvi.S14.frobenius_two_mul_card_complement_add_one_le_card_kernel
        hFrobG hKodd hCodd hFrobG.ne_bot_kernel
      show 2 * H78.complementIndex + 1 ≤ H78.kernelOrder
      have hke : H78.kernelOrder = Nat.card ↥(typeIHyp.typeI.typeF.H.subgroupOf vdata.L) := by
        rw [hKcard]; rfl
      have hcompl : Nat.card ↥(typeIHyp.typeI.typeF.H.subgroupOf vdata.L) * Nat.card ↥C
          = Nat.card ↥vdata.L := hFrobG.isComplement.card_mul_card
      have hce : H78.complementIndex = Nat.card ↥C := by
        show Nat.card ↥vdata.L / Nat.card typeIHyp.typeI.typeF.H = Nat.card ↥C
        rw [← hKcard, ← hcompl, Nat.mul_div_cancel_left _ Nat.card_pos]
      rw [hke, hce]; exact hfrobB
    exact zetaNuRhoNormSqGeOfDade typeIHyp.toHypothesis71
      (typeIHyp.dadeData.dade.fullDadeIsometryData typeIHyp.hconj).toDadeIsometryData.isDadeIsometry
      typeIHyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv
      hdeg_match coh.extension hnu_isometry hagree
      (OddOrder.Peterfalvi.S14.witness_L_hzeta0nu hG typeIHyp hFrobG coh (θ 0) hθ0_ne)
      (inner_self_induce_eq_one_of_frobeniusGroup hFrobG (θ 0) hθ0_ne) a ha hsmall

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.10)**: a type-I maximal subgroup `M` over `N_G(V)` together
with its Dade data exists.  Symmetric to `exists_LHypothesis`, packaging (13.17)
for the `V`-side with the Dade data and the virtual character `β_M` of (14.10).

The whole structural / σ-counting / set-theoretic content is discharged genuinely:
the type-I subgroup `M`, its `S14.Hypothesis` `typeIHyp`, and the §7 coherence datum
`h78` come from `exists_M_hypothesis78` (the V-side dual of `witness_L_hypothesis78`,
built through `typeII_overNormalizer_frobenius_V` + `frobenius_typeI_coherent`); the
`Mset`/`tau`/`tau1`/`psi`/`G0`/`betaM` data are read off `h78`; the TI / normalizer
facts are the `base_*` helpers; and the two `G0` covering facts are elementary set
algebra on the (14.11.3) complement `G₀ = G − [Ã(M) ∪ (W−(W₁∪W₂))^G ∪ (P#)^G ∪ (Q#)^G]`.

Instance coherence across the producer/consumer boundary is handled by opening
`S12.FiniteInduce` (the same scoped `Fintype`/`Invertible` instances that
`MHypothesis`'s field types and `exists_M_hypothesis78`'s existential are built with),
so no competing `Fintype.ofFinite`/`Invertible` is introduced.

Two obligations are discharged genuinely, via extra witnesses on `exists_M_hypothesis78`:
* `psi_degree_eq_e` (`ζ(1) = e = pq`): the producer witnesses `ζ_{ind1H}(1) = [M:K]`
  (`θ ind1H = 1_K` + `induce_trivialChar_apply_eq_index`), then `zeta_one_eq_ind1H_one` +
  `hindex` (`[M:K] = pq`) close it;
* `psi_tau1_norm_one` (`‖ψ^{τ₁}‖² = 1`): the producer witnesses `‖ζ‖² = 1` (the distinguished
  `ζ = Ind_K θ_0`, `θ_0 ≠ 1_K`, is Frobenius-irreducible —
  `inner_self_induce_eq_one_of_frobeniusGroup`), and `tau1 = ν` is a family isometry on it
  (`nu_isometry`).

One residual obligation remains isolated as the genuine deep §13 character content (gated on
the η-grid theory, not on this assembly): the joint existence of the `±1` signs with the
(13.1.d) η-grid expansion of `1_G + Δ` (Track A, issue 3002), consumed by the
`betaSigns`/`betaSigns_pm`/`betaGrid` fields — no specific sign choice is asserted. -/
theorem exists_MHypothesis [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (MHypothesis hyp) := by
  have hTII : IsTypeII hyp.base.T := T_typeII _hG hyp
  obtain ⟨M, typeIHyp, hM_max, hnorm_V, hindex, h78, hH_maxnilp, hhyp_dade, hdeg_ind1H, hnorm1,
      hnormSq⟩ :=
    exists_M_hypothesis78 _hG hyp hTII
  -- **Peterfalvi (13.1.d)**: the `η`-grid expansion of `1_G + Δ` with `±1` signs.  The genuine
  -- Track A obligation (issue 3002): the signs and the expansion are supplied together, so no
  -- specific (false) sign choice is asserted — only their honest joint existence is deferred.
  obtain ⟨betaSignsData, hbetaSigns_pm, hbetaGrid⟩ :
      ∃ signs : Fin hyp.base.q → Fin hyp.base.p → ℤ,
        (∀ i j, signs i j = 1 ∨ signs i j = -1) ∧
        OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + h78.delta =
          ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (signs i j : ℂ) • hyp.base.eta i j :=
    sorry
  refine ⟨{
    M := M
    K := maxNilpotentNormalHall M
    M_maximal := hM_max
    normalizer_V_le_M := hnorm_V
    K_eq_MF := rfl
    typeIHyp := typeIHyp
    h78 := h78
    Mset := Set.range h78.hyp76.zeta
    tau := h78.nu
    tau1 := h78.nu
    psi := h78.hyp76.zeta h78.zetaDistinct
    e := hyp.base.p * hyp.base.q
    k := Nat.card ↥(maxNilpotentNormalHall M)
    e_eq_index := hindex.symm
    complement_card_eq_pq := rfl
    k_eq_card_K := rfl
    psi_mem := ⟨h78.zetaDistinct, rfl⟩
    psi_degree_eq_e := ?psiDeg
    betaM := h78.beta
    betaM_formula := True
    betaM_formula_holds := trivial
    betaM_eq := rfl
    psi_tau1_eq := rfl
    betaSigns := betaSignsData
    betaSigns_pm := hbetaSigns_pm
    betaGrid := hbetaGrid
    G0 := Set.univ \ (typeIHyp.dadeData.dade.dadeSupport ∪
      (conjClassSet ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
        ∪ conjClassSet (sharpSubgroup hyp.base.P)
        ∪ conjClassSet (sharpSubgroup hyp.base.Q)))
    psi_tau1_norm_one := ?normOne
    G0_off_dadeSupport := ?offDade
    G0_orbit_cover := ?orbCover
    G0_avoid := ?avoid
    W_normalizer_V := base_W_normalizer_V hyp
    P_isTI := base_P_isTI _hG hyp
    Q_isTI := base_Q_isTI _hG hyp hTII
    card_normalizer_P_eq := base_card_normalizer_P_eq _hG hyp
    card_normalizer_Q_eq := base_card_normalizer_Q_eq _hG hyp hTII
    h78_hyp_eq := hhyp_dade
    h78_H_eq := hH_maxnilp
    h78_zetaNuRho_normSq_ge := ?normSq
  }⟩
  case offDade =>
    intro g hg hin
    exact hg.2 (Set.mem_union_left _ hin)
  -- **Peterfalvi (14.11.3)**: the concrete `G₀` avoids the three singular orbits — direct
  -- set algebra on the defining complement.
  case avoid =>
    intro g hg
    exact ⟨fun h => hg.2 (Set.mem_union_right _
        (Set.mem_union_left _ (Set.mem_union_left _ h))),
      fun h => hg.2 (Set.mem_union_right _
        (Set.mem_union_left _ (Set.mem_union_right _ h))),
      fun h => hg.2 (Set.mem_union_right _ (Set.mem_union_right _ h))⟩
  case orbCover =>
    intro g hgd hg0
    have hmem : g ∈ typeIHyp.dadeData.dade.dadeSupport ∪
        (conjClassSet ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
          ∪ conjClassSet (sharpSubgroup hyp.base.P)
          ∪ conjClassSet (sharpSubgroup hyp.base.Q)) := by
      by_contra h
      exact hg0 ⟨Set.mem_univ g, h⟩
    rcases hmem with h | h
    · exact absurd h hgd
    · exact h
  -- **Peterfalvi (7.6)/(14.10)**: `ψ(1) = ζ_{ind1H}(1) = [M:K] = e = pq` — the induced
  -- principal degree, genuinely discharged via `exists_M_hypothesis78`'s degree witness.
  case psiDeg => rw [h78.zeta_one_eq_ind1H_one, hdeg_ind1H, hindex]
  -- **Peterfalvi (7.5)/(7.8)**: `‖ψ^{τ₁}‖² = ‖ζ‖² = 1` — `τ₁ = ν` is a family isometry
  -- (`nu_isometry`, `ζ = ψ` non-`ind1H`) and `ζ` is unit-norm (`hnorm1`, Frobenius irreducible).
  case normOne =>
    rw [h78.nu_isometry h78.zetaDistinct h78.zetaDistinct h78.zetaDistinct_ne_ind1H
      h78.zetaDistinct_ne_ind1H]
    exact hnorm1
  -- **Peterfalvi (7.8.b)**: the coherence-norm lower bound, now genuinely discharged by the
  -- `exists_M_hypothesis78` witness (via the concrete §7 producer `zetaNuRhoNormSqGeOfDade`).
  case normSq => exact hnormSq

/-- **Peterfalvi (14.16)**→(14.7) bridge: if the Fitting kernel `H` of `L`
coincides with `U`, then `U` is characteristic in `H` — it is the whole of `H`,
and `⊤` is characteristic.  This is what lets the non-conjugate case `H = U` of
(14.16) feed back into (14.7). -/
theorem U_characteristic_of_H_eq_U {hyp : Hypothesis (G := G)}
    (Ldata : LHypothesis hyp) (hHU : Ldata.H = hyp.base.U) :
    (hyp.base.U.subgroupOf Ldata.H).Characteristic := by
  have htop : hyp.base.U.subgroupOf Ldata.H = ⊤ :=
    Subgroup.subgroupOf_eq_top.mpr (le_of_eq hHU)
  rw [htop]
  exact Subgroup.topCharacteristic

/-- **Peterfalvi (14.2)**: the field-normalizer configuration follows from the
Section 16 hypotheses.

This assembles Peterfalvi's concluding paragraph "By (14.12), (14.16) and (14.7),
the proof of Theorem (14.2) is complete."  Take the type-I subgroup `L` over
`N_G(U)` ((14.3), `exists_LHypothesis`) and split on whether `U` is characteristic
in `H`:

* if it is, (14.7) `field_normalizer_of_U_characteristic` finishes;
* otherwise take the type-I subgroup `M` over `N_G(V)` ((14.10),
  `exists_MHypothesis`) and split on whether `L` is conjugate to `M`:
  * if it is, (14.12) `field_normalizer_of_L_conj_M` finishes;
  * otherwise (14.13)–(14.16) `H_eq_U` give `H = U`, so `U` is characteristic in
    `H` (`U_characteristic_of_H_eq_U`), contradicting the branch assumption. -/
theorem field_normalizer_structure [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (FieldNormalizerData hyp) := by
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hyp
  by_cases hchar : (hyp.base.U.subgroupOf Ldata.H).Characteristic
  · exact field_normalizer_of_U_characteristic _hG hyp Ldata hchar
  · obtain ⟨Mdata⟩ := exists_MHypothesis _hG hyp
    by_cases hconj : ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M
    · exact field_normalizer_of_L_conj_M _hG hyp Ldata Mdata hconj
    · exact absurd
        (U_characteristic_of_H_eq_U Ldata
          (H_eq_U _hG hyp
            { Ldata := Ldata, Mdata := Mdata, not_conj := hconj,
              h := Nat.card ↥Ldata.H, h_eq_card_H := rfl }))
        hchar

/-- **Peterfalvi Section 16 + BG Appendix C**: BG Appendix C turns the
field-normalizer configuration into `p <= q`, contradicting (14.1). -/
theorem nonexistence_of_G [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (bgAppendixC : FieldNormalizerData hyp → hyp.base.p ≤ hyp.base.q) :
    False := by
  rcases field_normalizer_structure hG hyp with ⟨data⟩
  exact (not_lt_of_ge (bgAppendixC data)) hyp.q_lt_p

end OddOrder.Peterfalvi.S16

