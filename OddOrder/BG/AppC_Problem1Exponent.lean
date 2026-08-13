/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_Problem1SameCoset

/-!
# BG Appendix C, Problem 1: extracting the exponent from the witness

Hypothesis (B) gives `g = x^y` normalizing `σ(U)`.  The norm-one subgroup is cyclic, every
endomorphism of a cyclic group is a power map, and `g³ = 1` bounds the exponent, so a witness
provides an exponent `e` with `g·w·g⁻¹ = wᵉ` on `σ(U)` — and `e` can be normalized to be
**odd** with `zᵉ³ = z` on the whole field (`e³ ≡ 1 mod n` on the norm-one part, and the odd
representative handles the sign part of `𝔽ˣ` by CRT).  This is the standing shape (`hexp`,
`hcube`, `he`) in which the entire Problem 1 development consumes the witness
(`notes/bg/appC_problem1_resolution.md` §1). -/

namespace OddOrder.BG.AppC.Problem1

section ExponentExtraction

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- **The exponent of a witness.**  From hypothesis (B) alone: an odd exponent `e` with
`zᵉ³ = z` on the field, acting as `w ↦ wᵉ` on `σ(U)` by `g`-conjugation. -/
theorem exists_odd_cube_exponent (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hqodd : Odd q) :
    ∃ e : ℕ, Odd e ∧ (∀ z : GaloisField p q, z ^ (e * e * e) = z) ∧
      (∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data) := by
  subst hp
  classical
  have hq0 : q ≠ 0 := hqprime.ne_zero
  -- `g` normalizes `σ(U)`
  have hnormU : conjGen data ∈ Subgroup.normalizer ((data.U : Subgroup G) : Set G) := by
    have h := data.primeLine_conj_normalizes_U
    rw [data.sigma_P0_eq_W2, data.sigma_U_eq_U] at h
    exact h ⟨data.s, data.s_mem_W2, rfl⟩
  have hconj_mem_U : ∀ w ∈ data.U, conjGen data * w * (conjGen data)⁻¹ ∈ data.U := by
    intro w hw
    have hinv : (conjGen data)⁻¹ ∈ Subgroup.normalizer ((data.U : Subgroup G) : Set G) :=
      inv_mem hnormU
    have h := (Subgroup.mem_normalizer_iff''.mp hinv w).mp hw
    simpa using h
  -- the induced endomorphism of the norm-one units
  have hunit_mem : ∀ u : NormSet.normOneUnits 3 q,
      ∃ u' : NormSet.normOneUnits 3 q,
        conjGen data * unitElt data u * (conjGen data)⁻¹ = unitElt data u' := by
    intro u
    have hw := hconj_mem_U _ (unitElt_mem_U data u)
    rw [← data.sigma_U_eq_U] at hw
    obtain ⟨w', hw'mem, heq⟩ := hw
    obtain ⟨u', hu'⟩ := hw'mem
    refine ⟨u', ?_⟩
    rw [← heq, ← hu']
    rfl
  choose φ hφ using hunit_mem
  have hunitElt_mul : ∀ u v : NormSet.normOneUnits 3 q,
      unitElt data (u * v) = unitElt data u * unitElt data v := by
    intro u v
    rw [unitElt, unitElt, unitElt, ← map_mul, ← map_mul]
  have hunitElt_inj : Function.Injective (unitElt data) := by
    intro u v huv
    exact SemidirectProduct.inr_injective (data.sigma_injective huv)
  have hφmul : ∀ u v, φ (u * v) = φ u * φ v := by
    intro u v
    refine hunitElt_inj ?_
    rw [hunitElt_mul, ← hφ (u * v), ← hφ u, ← hφ v, hunitElt_mul]
    group
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (MonoidHom.mk' φ hφmul)
  -- an ℕ-exponent representing the ℤ-power
  set n : ℕ := Nat.card (NormSet.normOneUnits 3 q) with hndef
  have hq3' : 3 ≤ q := by
    have h2 := hqprime.two_le
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hpow3 : 27 ≤ 3 ^ q := by
    calc (27 : ℕ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ q := Nat.pow_le_pow_right (by norm_num) hq3'
  have hmod4 : 3 ^ q % 4 = 3 := by
    obtain ⟨k, hk⟩ := hqodd
    subst hk
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hncard : n = (3 ^ q - 1) / 2 := by
    rw [hndef, NormSet.normOneUnits_card 3 q hq0]
  have hnodd : n % 2 = 1 := by omega
  have hn1 : 1 < n := by omega
  set e₀ : ℕ := (m % (n : ℤ)).toNat with he₀def
  have hn0' : (n : ℤ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hmnn : (0 : ℤ) ≤ m % n := Int.emod_nonneg m hn0'
  have he₀cast : ((e₀ : ℕ) : ℤ) = m % n := by
    rw [he₀def]
    exact Int.toNat_of_nonneg hmnn
  have hφpow : ∀ u : NormSet.normOneUnits 3 q, φ u = u ^ e₀ := by
    intro u
    have hdvd : orderOf u ∣ n := by
      rw [hndef]
      exact orderOf_dvd_natCard u
    have hz : u ^ m = u ^ (e₀ : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq, he₀cast]
      have hmm : m ≡ m % (n : ℤ) [ZMOD (n : ℤ)] := by
        unfold Int.ModEq
        rw [Int.emod_emod]
      exact hmm.of_dvd (Int.natCast_dvd_natCast.mpr hdvd)
    have h := hm u
    rw [hz, zpow_natCast] at h
    exact h
  -- the `G`-level exponent relation, at `e₀`
  have hexp₀ : ∀ w ∈ data.U, conjGen data * w = w ^ e₀ * conjGen data := by
    intro w hw
    rw [← data.sigma_U_eq_U] at hw
    obtain ⟨w', hw'mem, rfl⟩ := hw
    obtain ⟨u, rfl⟩ := hw'mem
    have h := hφ u
    rw [hφpow u, ← unitElt_pow] at h
    have h' : conjGen data * unitElt data u = unitElt data u ^ e₀ * conjGen data := by
      rw [← h]
      group
    exact h'
  -- `e₀³ ≡ 1 (mod n)` from `g³ = 1`
  obtain ⟨u₀, hu₀⟩ := IsCyclic.exists_generator (α := NormSet.normOneUnits 3 q)
  have hord₀ : orderOf u₀ = n := by
    rw [hndef]
    exact orderOf_eq_card_of_forall_mem_zpowers hu₀
  have hcube₀ : u₀ ^ (e₀ * e₀ * e₀) = u₀ := normOneUnits_pow_cube data rfl hexp₀ u₀
  have hcubemod : e₀ * e₀ * e₀ ≡ 1 [MOD n] := by
    have h1 : u₀ ^ (e₀ * e₀ * e₀) = u₀ ^ 1 := by simpa using hcube₀
    have h2 := pow_eq_pow_iff_modEq.mp h1
    rwa [hord₀] at h2
  -- the odd representative
  set ee : ℕ := if e₀ % 2 = 1 then e₀ else e₀ + n with heedef
  have heeodd : ee % 2 = 1 := by
    rw [heedef]
    split_ifs with h
    · exact h
    · omega
  have heemod : ee ≡ e₀ [MOD n] := by
    rw [heedef]
    split_ifs
    · rfl
    · exact Nat.add_modEq_left_iff.mpr dvd_rfl
  have hpow_congr : ∀ u : NormSet.normOneUnits 3 q, u ^ ee = u ^ e₀ := by
    intro u
    have hdvd : orderOf u ∣ n := by
      rw [hndef]
      exact orderOf_dvd_natCard u
    exact pow_eq_pow_iff_modEq.mpr (heemod.of_dvd hdvd)
  have hexp_ee : ∀ w ∈ data.U, conjGen data * w = w ^ ee * conjGen data := by
    intro w hw
    have h := hexp₀ w hw
    rw [← data.sigma_U_eq_U] at hw
    obtain ⟨w', hw'mem, rfl⟩ := hw
    obtain ⟨u, rfl⟩ := hw'mem
    rw [h]
    congr 1
    have hpow : ∀ k : ℕ, data.sigma (SemidirectProduct.inr u) ^ k
        = unitElt data (u ^ k) := by
      intro k
      rw [← unitElt_pow]
      rfl
    rw [hpow, hpow, hpow_congr u]
  -- `ee³ ≡ 1 (mod 3^q − 1)` by CRT, hence the cube identity on the whole field
  set N : ℕ := 3 ^ q - 1 with hNdef
  have hN2n : N = 2 * n := by omega
  have hcubeN : ee * ee * ee ≡ 1 [MOD N] := by
    have h2 : Nat.Coprime 2 n := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    have hmod2 : ee * ee * ee ≡ 1 [MOD 2] := by
      have h : ee ≡ 1 [MOD 2] := by
        unfold Nat.ModEq
        omega
      simpa using (h.mul h).mul h
    have hmodn : ee * ee * ee ≡ 1 [MOD n] :=
      ((heemod.mul heemod).mul heemod).trans hcubemod
    rw [hN2n]
    exact (Nat.modEq_and_modEq_iff_modEq_mul h2).mp ⟨hmod2, hmodn⟩
  letI : Fintype (GaloisField 3 q) := Fintype.ofFinite _
  have hcardu : Nat.card (GaloisField 3 q)ˣ = N := by
    rw [Nat.card_units, GaloisField.card 3 q hq0]
  have hcube_field : ∀ z : GaloisField 3 q, z ^ (ee * ee * ee) = z := by
    intro z
    rcases eq_or_ne z 0 with rfl | hz
    · have hee0 : ee ≠ 0 := by omega
      rw [zero_pow (Nat.mul_ne_zero (Nat.mul_ne_zero hee0 hee0) hee0)]
    · have hζ : Units.mk0 z hz ^ (ee * ee * ee) = Units.mk0 z hz ^ 1 := by
        have hdvd : orderOf (Units.mk0 z hz) ∣ N := by
          rw [← hcardu]
          exact orderOf_dvd_natCard _
        exact pow_eq_pow_iff_modEq.mpr (hcubeN.of_dvd hdvd)
      have h := congrArg (fun w : (GaloisField 3 q)ˣ => (w : GaloisField 3 q)) hζ
      simpa using h
  exact ⟨ee, Nat.odd_iff.mpr heeodd, hcube_field, hexp_ee⟩

/-- **For `p = 3`, condition (A) forces `q` odd**: an even `q` gives `8 ∣ 3^q - 1`, so
`n = (3^q - 1)/2` is even and not coprime to `p - 1 = 2`. -/
theorem q_odd_of_conditionA (data : FieldNormalizerData p q G) (hp : p = 3) : Odd q := by
  subst hp
  by_contra hqe
  have hq2 := data.q_prime.two_le
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hqe
  rw [← two_mul] at hk
  have hmod : 3 ^ q % 8 = 1 := by
    subst hk
    rw [pow_mul, Nat.pow_mod]
    norm_num
  have hpow1 : 1 ≤ 3 ^ q := Nat.one_le_pow _ _ (by norm_num)
  have hdvd : 2 ∣ (3 ^ q - 1) / 2 := by omega
  have hA := data.cyclotomic_coprime
  unfold conditionA at hA
  norm_num at hA
  have h1 := Nat.odd_iff.mp hA
  omega

/-- **Theorem 1, Frobenius-power case.**  If `g` acts on `σ(U)` by an exponent agreeing with a
Frobenius power `u ↦ u^{3ʲ}` on the norm-one units, hypothesis (B) fails.  The transported
Frobenius `s ↦ s^{3ʲ}` is additive on `σ(P)`, so the layered relation family feeds the twisted
engine `commute_conj_of_le_closure_twisted`; the Paley spanning transports along the Frobenius
bijection; and the resulting commutation `[x, x^g] = 1` is fatal (`not_commute_conj`).  This is
the `e ∈ ⟨3⟩` half of Theorem 1 of `notes/bg/appC_problem1_partial_resolution.md` —
`false_of_centralizing` is the specialisation `j = 0`. -/
theorem false_of_frobenius_exponent (data : FieldNormalizerData p q G) (hp : p = 3)
    {e j : ℕ} (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (hfrob : ∀ u : NormSet.normOneUnits p q, u ^ e = u ^ 3 ^ j) : False := by
  subst hp
  classical
  -- the transported Frobenius power on `σ(P)`
  set σf : G → G := fun x =>
    if h : ∃ a : Multiplicative (GaloisField 3 q), fieldHom data a = x then
      fieldHom data (Multiplicative.ofAdd (Multiplicative.toAdd (Classical.choose h) ^ 3 ^ j))
    else x with hσfdef
  have hσf_apply : ∀ a : Multiplicative (GaloisField 3 q),
      σf (fieldHom data a)
        = fieldHom data (Multiplicative.ofAdd (Multiplicative.toAdd a ^ 3 ^ j)) := by
    intro a
    have hex : ∃ b, fieldHom data b = fieldHom data a := ⟨a, rfl⟩
    simp only [hσfdef, dif_pos hex]
    have hchoose : Classical.choose hex = a :=
      fieldHom_injective data (Classical.choose_spec hex)
    rw [hchoose]
  have hσP : ∀ v ∈ data.P, σf v ∈ data.P := by
    intro v hv
    rw [← fieldHom_range data] at hv ⊢
    obtain ⟨a, rfl⟩ := hv
    rw [hσf_apply]
    exact ⟨_, rfl⟩
  have hσmul : ∀ a ∈ data.P, ∀ b ∈ data.P, σf (a * b) = σf a * σf b := by
    intro x hx y hy
    rw [← fieldHom_range data] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have harg : Multiplicative.ofAdd (Multiplicative.toAdd (a * b) ^ 3 ^ j)
        = Multiplicative.ofAdd (Multiplicative.toAdd a ^ 3 ^ j)
          * Multiplicative.ofAdd (Multiplicative.toAdd b ^ 3 ^ j) := by
      rw [← ofAdd_add]
      congr 1
      rw [toAdd_mul, add_pow_char_pow]
    rw [← map_mul, hσf_apply, harg, map_mul, ← hσf_apply, ← hσf_apply]
  -- orbit elements in field coordinates, and the twist as the `e`-power on the orbit
  have hSP : orbitS data ⊆ (data.P : Set G) := by
    rintro s ⟨v, hv, rfl⟩
    exact conj_s_mem_P data hv
  have horbit : ∀ v ∈ data.U, ∃ u : NormSet.normOneUnits 3 q, v = unitElt data u := by
    intro v hv
    rw [← data.sigma_U_eq_U] at hv
    obtain ⟨w', ⟨u, rfl⟩, rfl⟩ := hv
    exact ⟨u, rfl⟩
  have hval_pow : ∀ u : NormSet.normOneUnits 3 q,
      (((u⁻¹ : NormSet.normOneUnits 3 q) : (GaloisField 3 q)ˣ) : GaloisField 3 q) ^ 3 ^ j
        = ((((u ^ e)⁻¹ : NormSet.normOneUnits 3 q) : (GaloisField 3 q)ˣ) : GaloisField 3 q) := by
    intro u
    have h := hfrob u⁻¹
    have hval := congrArg (fun z : NormSet.normOneUnits 3 q =>
      ((z : (GaloisField 3 q)ˣ) : GaloisField 3 q)) h
    simp only [inv_pow] at hval ⊢
    exact hval.symm
  have hσf_orbit : ∀ u : NormSet.normOneUnits 3 q,
      σf ((unitElt data u)⁻¹ * data.s * unitElt data u)
        = (unitElt data u ^ e)⁻¹ * data.s * unitElt data u ^ e := by
    intro u
    rw [conj_s_unitElt data u, hσf_apply, unitElt_pow, conj_s_unitElt data (u ^ e)]
    congr 2
    simp only [toAdd_ofAdd]
    exact hval_pow u
  have hrel : ∀ s' ∈ orbitS data,
      ((conjGen data)⁻¹ * ((conjGen data)⁻¹ * σf (σf s') * conjGen data) * conjGen data) *
        ((conjGen data)⁻¹ * σf s' * conjGen data) * s' = 1 := by
    rintro s' ⟨v, hv, rfl⟩
    obtain ⟨u, rfl⟩ := horbit v hv
    have h1 : σf ((unitElt data u)⁻¹ * data.s * unitElt data u)
        = (unitElt data u ^ e)⁻¹ * data.s * unitElt data u ^ e := hσf_orbit u
    have h2 : σf ((unitElt data u ^ e)⁻¹ * data.s * unitElt data u ^ e)
        = (unitElt data u ^ (e * e))⁻¹ * data.s * unitElt data u ^ (e * e) := by
      have h := hσf_orbit (u ^ e)
      rw [← unitElt_pow, ← pow_mul] at h
      exact h
    rw [h1, h2]
    have hlay := layered_relation_of_exp data rfl hexp hv
    calc ((conjGen data)⁻¹ * ((conjGen data)⁻¹ *
            ((unitElt data u ^ (e * e))⁻¹ * data.s * unitElt data u ^ (e * e)) *
            conjGen data) * conjGen data) *
          ((conjGen data)⁻¹ * ((unitElt data u ^ e)⁻¹ * data.s * unitElt data u ^ e) *
            conjGen data) *
          ((unitElt data u)⁻¹ * data.s * unitElt data u)
        = ((conjGen data)⁻¹ * ((conjGen data)⁻¹ *
            ((unitElt data u ^ (e * e))⁻¹ * data.s * unitElt data u ^ (e * e)) *
            conjGen data) * conjGen data) *
          (((conjGen data)⁻¹ * ((unitElt data u ^ e)⁻¹ * data.s * unitElt data u ^ e) *
            conjGen data) *
          ((unitElt data u)⁻¹ * data.s * unitElt data u)) := by group
      _ = 1 := hlay
  -- the spanning hypothesis transports along the Frobenius bijection
  have hσinv : ∀ x ∈ data.P, σf x⁻¹ = (σf x)⁻¹ := by
    intro x hx
    have h1 : σf x⁻¹ * σf x = 1 := by
      rw [← hσmul x⁻¹ (inv_mem hx) x hx, inv_mul_cancel]
      rw [show (1 : G) = fieldHom data 1 from (map_one _).symm, hσf_apply]
      simp
    exact eq_inv_of_mul_eq_one_left h1
  have hclP : Subgroup.closure {s' | s' ∈ orbitS data ∧ s' * data.s ∈ orbitS data}
      ≤ data.P :=
    (Subgroup.closure_le _).mpr fun s' hs' => hSP hs'.1
  have hfrob_inj : Function.Injective (fun z : GaloisField 3 q => z ^ 3 ^ j) := by
    intro x y hxy
    simp only at hxy
    have h0 : (x - y) ^ 3 ^ j = 0 := by
      rw [sub_pow_char_pow, hxy, sub_self]
    exact sub_eq_zero.mp
      ((pow_eq_zero_iff (by positivity : 0 < 3 ^ j).ne').mp h0)
  have hσf_surj : ∀ v ∈ data.P, ∃ w ∈ data.P, σf w = v := by
    intro v hv
    rw [← fieldHom_range data] at hv
    obtain ⟨a, rfl⟩ := hv
    obtain ⟨t, ht⟩ := Finite.injective_iff_surjective.mp hfrob_inj (Multiplicative.toAdd a)
    refine ⟨fieldHom data (Multiplicative.ofAdd t), ?_, ?_⟩
    · rw [← fieldHom_range data]
      exact ⟨_, rfl⟩
    · rw [hσf_apply]
      have hta : Multiplicative.toAdd (Multiplicative.ofAdd t) ^ 3 ^ j
          = Multiplicative.toAdd a := by
        simpa using ht
      rw [hta]
      simp
  have hspan : data.P ≤ Subgroup.closure
      (σf '' {s' | s' ∈ orbitS data ∧ s' * data.s ∈ orbitS data}) := by
    intro v hv
    obtain ⟨w, hwP, rfl⟩ := hσf_surj v hv
    have hw := le_closure_orbitS data rfl hwP
    refine Subgroup.closure_induction
      (p := fun x _ => σf x ∈ Subgroup.closure
        (σf '' {s' | s' ∈ orbitS data ∧ s' * data.s ∈ orbitS data}))
      (fun x hx => Subgroup.subset_closure ⟨x, hx, rfl⟩) ?_ ?_ ?_ hw
    · have h0 : (0 : GaloisField 3 q) ^ 3 ^ j = 0 :=
        zero_pow (by positivity : (0 : ℕ) < 3 ^ j).ne'
      rw [show (1 : G) = fieldHom data 1 from (map_one _).symm, hσf_apply, toAdd_one, h0,
        ofAdd_zero, map_one]
      exact Subgroup.one_mem _
    · intro x y hxc hyc hx hy
      rw [hσmul x (hclP hxc) y (hclP hyc)]
      exact Subgroup.mul_mem _ hx hy
    · intro x hxc hx
      rw [hσinv x (hclP hxc)]
      exact Subgroup.inv_mem _ hx
  -- feed the engine and close by the fixed-point contradiction
  have ht : data.s ∈ orbitS data := ⟨1, data.U.one_mem, by group⟩
  have hcomm := commute_conj_of_le_closure_twisted (P := data.P) (g := conjGen data)
    (fun a ha b hb => P_mul_comm data ha hb) σf hσmul hσP hSP hrel ht hspan
    data.s data.s_mem_P
  exact not_commute_conj data rfl hcomm

end ExponentExtraction

end OddOrder.BG.AppC.Problem1
