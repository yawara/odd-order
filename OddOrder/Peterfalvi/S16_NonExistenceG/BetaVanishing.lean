import OddOrder.Peterfalvi.S16_NonExistenceG.SubgroupM
import OddOrder.Peterfalvi.S16_NonExistenceG.CoherentEtaOrthogonality

/-!
# BetaVanishing

Prefix-split from `OddOrder.Peterfalvi.S16_NonExistenceG.ComparingLM` (2000-line limit, issue 0103 第 2 パス).
-/

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


end OrthogonalitySwitchData
end OddOrder.Peterfalvi.S16
