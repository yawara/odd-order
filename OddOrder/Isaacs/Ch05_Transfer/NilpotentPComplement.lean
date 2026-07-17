/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Nilpotent
import OddOrder.Isaacs.Ch05_Transfer.Basic

/-!
# Normal `p`-complements of nilpotent groups, and their uniqueness

**Isaacs, _Finite Group Theory_ (AMS GSM 92)** — supporting facts used around §5E/§6C
(e.g. in the proof of Thm 6.24, p. 196: "Every nilpotent group has a normal
`r`-complement").

## Main results

* `OddOrder.Isaacs.Ch05.hasNormalPComplement_of_isNilpotent`: a finite nilpotent group has
  a normal `p`-complement for every prime `p` — the kernel of the direct-product
  projection onto the (normal) Sylow `p`-subgroup (`Sylow.directProductOfNormal`).
* `OddOrder.Isaacs.Ch05.eq_of_normal_pcomplement`: normal `p`-complements are unique —
  two normal subgroups complementing (single) Sylow `p`-subgroups coincide (each has
  `p'`-order, and each maps into the `p`-power-order quotient by the other).
* `OddOrder.Isaacs.Ch05.map_mulAut_of_normal_pcomplement`: hence the normal
  `p`-complement is fixed by every automorphism — in particular it is characteristic,
  and invariant under any group acting by automorphisms.
-/

namespace OddOrder.Isaacs.Ch05

open scoped Pointwise

section /- 5E supplement: normal p-complements of nilpotent groups -/

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]

/-- A normal subgroup complementing a Sylow `p`-subgroup has `p'`-order. -/
theorem not_dvd_card_of_isComplement'_sylow {K : Subgroup H} (P : Sylow p H)
    (hC : Subgroup.IsComplement' K (P : Subgroup H)) : ¬ p ∣ Nat.card K := by
  intro hdvd
  have hcardP : Nat.card ↥(P : Subgroup H) = p ^ (Nat.card H).factorization p :=
    P.card_eq_multiplicity
  have hpow : p ^ ((Nat.card H).factorization p + 1) ∣ Nat.card H := by
    conv_rhs => rw [← hC.card_mul]
    rw [pow_succ, mul_comm (p ^ _) p, ← hcardP]
    exact mul_dvd_mul hdvd dvd_rfl
  have := (Nat.Prime.pow_dvd_iff_le_factorization hp.out Nat.card_pos.ne').mp hpow
  omega

/-- **Uniqueness of the normal `p`-complement**: two normal subgroups each complementing
a Sylow `p`-subgroup of a finite group coincide.

Each complement has `p'`-order while the quotient by the other has `p`-power order, so
the image of one in the quotient by the other is trivial. -/
theorem eq_of_normal_pcomplement {K K' : Subgroup H} [K.Normal] [K'.Normal]
    {P P' : Sylow p H}
    (hK : Subgroup.IsComplement' K (P : Subgroup H))
    (hK' : Subgroup.IsComplement' K' (P' : Subgroup H)) :
    K = K' := by
  have key : ∀ (L L' : Subgroup H) (Q Q' : Sylow p H), L.Normal → L'.Normal →
      Subgroup.IsComplement' L (Q : Subgroup H) →
      Subgroup.IsComplement' L' (Q' : Subgroup H) → L' ≤ L := by
    intro L L' Q Q' hLn hL'n hL hL'
    haveI := hLn
    -- the image of `L'` in `H ⧸ L` has order dividing both a `p'`-number and a `p`-power
    have h1 : Nat.card ↥(L'.map (QuotientGroup.mk' L)) ∣ Nat.card L' :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥(L'.map (QuotientGroup.mk' L)) ∣ p ^ (Nat.card H).factorization p := by
      have hquot : Nat.card (H ⧸ L) = p ^ (Nat.card H).factorization p := by
        have hidx : L.index = Nat.card ↥(Q : Subgroup H) := by
          have hmul := hL.card_mul
          have hmul' := Subgroup.card_mul_index (H := L)
          exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [hmul, hmul'])
        rw [← Q.card_eq_multiplicity, ← hidx]
        rfl
      rw [← hquot]
      exact Subgroup.card_subgroup_dvd_card _
    -- `p'`-order of `L'` makes it coprime to the `p`-power
    have hcop : Nat.gcd (Nat.card ↥L') (p ^ (Nat.card H).factorization p) = 1 :=
      Nat.Coprime.pow_right _
        ((hp.out.coprime_iff_not_dvd).mpr (not_dvd_card_of_isComplement'_sylow Q' hL')).symm
    have hone : Nat.card ↥(L'.map (QuotientGroup.mk' L)) = 1 :=
      Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h1 h2)
    have hbot : L'.map (QuotientGroup.mk' L) = ⊥ := Subgroup.card_eq_one.mp hone
    have hle : L' ≤ (QuotientGroup.mk' L).ker := by
      rw [← Subgroup.map_eq_bot_iff]
      exact hbot
    rwa [QuotientGroup.ker_mk'] at hle
  exact le_antisymm (key K' K P' P ‹_› ‹_› hK' hK) (key K K' P P' ‹_› ‹_› hK hK')

/-- The normal `p`-complement is fixed by every automorphism of `H`. -/
theorem map_mulAut_of_normal_pcomplement {K : Subgroup H} [K.Normal]
    {P : Sylow p H} (hK : Subgroup.IsComplement' K (P : Subgroup H)) (ψ : MulAut H) :
    K.map ψ.toMonoidHom = K := by
  haveI hmapn : (K.map ψ.toMonoidHom).Normal :=
    Subgroup.Normal.map ‹K.Normal› ψ.toMonoidHom ψ.surjective
  -- `ψ • P` is a Sylow `p`-subgroup with carrier `ψ(P)`
  have hPcoe : ((ψ • P : Sylow p H) : Subgroup H) = (P : Subgroup H).map ψ.toMonoidHom := by
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hcompl :
      Subgroup.IsComplement' (K.map ψ.toMonoidHom) ((ψ • P : Sylow p H) : Subgroup H) := by
    rw [hPcoe]
    refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
    · rw [(Nat.card_congr (Subgroup.equivMapOfInjective _ _ ψ.injective).toEquiv).symm,
        (Nat.card_congr
          (Subgroup.equivMapOfInjective (P : Subgroup H) _ ψ.injective).toEquiv).symm]
      exact hK.card_mul
    · rw [disjoint_iff, ← Subgroup.map_inf _ _ ψ.toMonoidHom ψ.injective,
        disjoint_iff.mp hK.disjoint, Subgroup.map_bot]
  exact eq_of_normal_pcomplement hcompl hK

/-- A finite group with `p ∤ |H|` has a (trivial) normal `p`-complement: `⊤`. -/
theorem hasNormalPComplement_of_not_dvd_card (hnd : ¬ p ∣ Nat.card H) :
    HasNormalPComplement p H := by
  refine ⟨⊤, inferInstance, fun P => ?_⟩
  have hP_bot : (P : Subgroup H) = ⊥ := by
    have hcard := P.card_eq_multiplicity
    rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero] at hcard
    exact Subgroup.card_eq_one.mp hcard
  rw [hP_bot]
  exact Subgroup.isComplement'_top_left.mpr rfl

/-- **A finite nilpotent group has a normal `p`-complement for every prime `p`**
(Isaacs p. 196, used in the proof of Thm 6.24).

The complement is the kernel of the projection of the Sylow direct-product decomposition
(`Sylow.directProductOfNormal`) onto the `p`-component. -/
theorem hasNormalPComplement_of_isNilpotent [Group.IsNilpotent H] :
    HasNormalPComplement p H := by
  classical
  by_cases hpH : p ∣ Nat.card H
  swap
  · exact hasNormalPComplement_of_not_dvd_card hpH
  have hcard_ne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hp_mem : p ∈ (Nat.card H).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp.out, hpH, hcard_ne⟩
  let e := Sylow.directProductOfNormal (G := H) fun {q} _ Q => inferInstance
  set P : Sylow p H := default with hP_def
  let π₁ : (∀ q : (Nat.card H).primeFactors, ∀ Q : Sylow (q : ℕ) H, ↥(Q : Subgroup H)) →*
      (∀ Q : Sylow p H, ↥(Q : Subgroup H)) :=
    Pi.evalMonoidHom (fun q : (Nat.card H).primeFactors =>
      ∀ Q : Sylow (q : ℕ) H, ↥(Q : Subgroup H)) ⟨p, hp_mem⟩
  let π₂ : (∀ Q : Sylow p H, ↥(Q : Subgroup H)) →* ↥(P : Subgroup H) :=
    Pi.evalMonoidHom (fun Q : Sylow p H => ↥(Q : Subgroup H)) P
  let f : H →* ↥(P : Subgroup H) := (π₂.comp π₁).comp e.symm.toMonoidHom
  -- `f` is surjective (hit `y` from `e (mulSingle (mulSingle y))`)
  have hf_surj : Function.Surjective f := by
    intro y
    set v₂ : ∀ Q : Sylow p H, ↥(Q : Subgroup H) := Pi.mulSingle P y with hv₂
    set v₁ : ∀ q : (Nat.card H).primeFactors, ∀ Q : Sylow (q : ℕ) H, ↥(Q : Subgroup H) :=
      Pi.mulSingle ⟨p, hp_mem⟩ v₂ with hv₁
    refine ⟨e v₁, ?_⟩
    change π₂ (π₁ (e.symm (e v₁))) = y
    rw [MulEquiv.symm_apply_apply]
    change v₁ ⟨p, hp_mem⟩ P = y
    rw [hv₁, Pi.mulSingle_eq_same, hv₂, Pi.mulSingle_eq_same]
  -- the kernel of `f` complements the (unique) Sylow `p`-subgroup
  refine ⟨f.ker, inferInstance, fun Q => ?_⟩
  haveI : Subsingleton (Sylow p H) := by
    haveI := Sylow.unique_of_normal P inferInstance
    infer_instance
  rw [Subsingleton.elim Q P]
  -- coprime cardinalities: `[H : ker f] = |P|` is the full `p`-part
  have hindex : (f.ker).index = Nat.card ↥(P : Subgroup H) := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf_surj]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have hmul : Nat.card f.ker * Nat.card ↥(P : Subgroup H) = Nat.card H := by
    rw [← hindex]
    exact Subgroup.card_mul_index (H := f.ker)
  have hnd : ¬ p ∣ Nat.card f.ker := by
    intro hdvd
    have hpow : p ^ ((Nat.card H).factorization p + 1) ∣ Nat.card H := by
      conv_rhs => rw [← hmul, P.card_eq_multiplicity]
      rw [pow_succ, mul_comm (p ^ _) p]
      exact mul_dvd_mul hdvd dvd_rfl
    have := (Nat.Prime.pow_dvd_iff_le_factorization hp.out hcard_ne).mp hpow
    omega
  refine Subgroup.isComplement'_of_coprime hmul ?_
  rw [P.card_eq_multiplicity]
  exact Nat.Coprime.pow_right _ ((hp.out.coprime_iff_not_dvd.mpr hnd).symm)

end

end OddOrder.Isaacs.Ch05
