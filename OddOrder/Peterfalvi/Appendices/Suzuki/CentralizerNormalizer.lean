/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerInduction
import OddOrder.Peterfalvi.Appendices.Suzuki.KCyclic

/-!
# Peterfalvi Part II, Ch. I §3: Proposition 1(b)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, pp. 105–106.

For a subgroup `X ≤ V`, Proposition 1(b) proves the ambient normalizer
factorization

`N_G(X) = C_G(X) N_V(X)`,

where `N_V(X)` means `V ∩ N_G(X)`.  The proof follows the source in three
steps: double transitivity gives `N_G(X) = C_G(X) N_D(X)`; the §1 inverted
product lemma gives `N_D(X) = N_K(X) N_V(X)`; and normality of `K` in `D`
places `[N_K(X), X]` in `X ∩ K = 1`.

Peterfalvi uses right actions.  In the Lean left-action convention the
centralizing correction is multiplied on the left.  The §1 equivalence
returns its fixed factor before its inverted factor, so it is applied to
the inverse element to recover the source order `N_K(X) N_V(X)`.

The proposition standing assumption `X ≠ 1` is not needed for part (b).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open MulAction
open scoped Pointwise

section /- §3, Proposition 1(b): normalizer factorization (pp. 105–106) -/

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {X : Subgroup G}

omit [Finite G] in
lemma smul_mem_fixedPoints_of_mem_normalizer
    {g : G} (hg : g ∈ Subgroup.normalizer X) {w : Ω}
    (hw : w ∈ fixedPoints X Ω) :
    g • w ∈ fixedPoints X Ω := by
  rw [mem_fixedPoints] at hw ⊢
  intro x
  have hx' : g⁻¹ * x * g ∈ X := by
    have hgi : g⁻¹ ∈ Subgroup.normalizer X := inv_mem hg
    simpa using (Subgroup.mem_normalizer_iff.mp hgi x).mp x.2
  calc
    (x : G) • g • w = g • ((g⁻¹ * x * g) • w) := by
      rw [smul_smul, smul_smul]
      congr 1
      group
    _ = g • w := by rw [show (g⁻¹ * x * g) • w = w by simpa using hw ⟨_, hx'⟩]


/-- **Peterfalvi Part II, Ch. I §3 Prop 1(b)**, intersection step:
`V ∩ K = 1`, since `t` centralizes `V`, inverts `K`, and `D` has odd order. -/
theorem V_inf_K_eq_bot : hyp.V ⊓ hyp.K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxV : x ∈ hyp.V := hx.1
  have hxK : x ∈ hyp.K := hx.2
  have hxKSet : x ∈ hyp.KSet := by
    rw [← hyp.coe_K]
    exact hxK
  have hfix : hyp.t * x * hyp.t = x := by
    have hcomm : Commute x hyp.t := hyp.commute_t_of_mem_V hxV
    calc
      hyp.t * x * hyp.t = x * hyp.t * hyp.t := by rw [← hcomm.eq]
      _ = x * (hyp.t * hyp.t) := mul_assoc _ _ _
      _ = x := by rw [hyp.t_mul_t, mul_one]
  have hxeq : x = x⁻¹ := hfix.symm.trans hxKSet.2
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    calc
      x * x = x⁻¹ * x := congrArg (fun z : G => z * x) hxeq
      _ = 1 := inv_mul_cancel x
  exact eq_one_of_sq_eq_one_of_odd_card hyp.D_odd
    (hyp.V_le_D hxV) hx2

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(b)**, §1 decomposition:
`N_D(X) = N_K(X) N_V(X)`.  The inverse of the `Y Z` decomposition is used
because `invertedProdEquiv` returns the fixed factor before the inverted
factor. -/
theorem normalizer_inf_D_eq_normalizer_inf_K_mul_normalizer_inf_V
    (hXV : X ≤ hyp.V) :
    ((hyp.D ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) =
      ((hyp.K ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) *
        ((hyp.V ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) := by
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let ND : Subgroup G := hyp.D ⊓ N
  have htC : hyp.t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hyp.commute_t_of_mem_V (hXV hx)).eq
  have htN : hyp.t ∈ N := Subgroup.centralizer_le_normalizer _ htC
  have hNDodd : Odd (Nat.card ND) :=
    hyp.D_odd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have htND : ∀ d ∈ ND, hyp.t * d * hyp.t ∈ ND := by
    intro d hd
    have htd : hyp.t * d * hyp.t ∈ hyp.D := by
      have htd0 := hyp.t_conj_mem_D hd.1
      rwa [hyp.t_inv_eq] at htd0
    exact ⟨htd, mul_mem (mul_mem htN hd.2) htN⟩
  ext d
  constructor
  · intro hd
    have hdND : d ∈ ND := hd
    obtain ⟨⟨⟨v, hv⟩, ⟨k, hk⟩⟩, hvk⟩ :=
      (invertedProdEquiv (X := ND) (t := hyp.t)
        hyp.t_mul_t hNDodd htND).surjective ⟨d⁻¹, inv_mem hdND⟩
    have hvV : v ∈ hyp.V := ⟨hv.1.1, hv.2⟩
    have hvN : v ∈ N := hv.1.2
    have hkK : k ∈ hyp.K := by
      change k ∈ (hyp.K : Set G)
      rw [hyp.coe_K]
      exact ⟨hk.1.1, hk.2⟩
    have hkN : k ∈ N := hk.1.2
    have hvkG : v * k = d⁻¹ := congrArg Subtype.val hvk
    have hkv : k⁻¹ * v⁻¹ = d := by
      have hi := congrArg Inv.inv hvkG
      simpa [mul_inv_rev] using hi
    rw [Set.mem_mul]
    exact ⟨k⁻¹, ⟨hyp.K.inv_mem hkK, N.inv_mem hkN⟩,
      v⁻¹, ⟨hyp.V.inv_mem hvV, N.inv_mem hvN⟩, hkv⟩
  · rw [Set.mem_mul]
    rintro ⟨k, hk, v, hv, rfl⟩
    exact ⟨mul_mem (hyp.K_le_D hk.1) (hyp.V_le_D hv.1),
      mul_mem hk.2 hv.2⟩

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(b)**, commutator step:
`N_K(X) ≤ C_G(X)`, since the commutator lies in `X ∩ K ≤ V ∩ K = 1`. -/
theorem normalizer_inf_K_le_centralizer (hXV : X ≤ hyp.V) :
    hyp.K ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.centralizer (X : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hconjX : k * x * k⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp hk.2 x).mp hx
  have hcommX : k * x * k⁻¹ * x⁻¹ ∈ X :=
    mul_mem hconjX (X.inv_mem hx)
  have hnormalK : ∀ h d, h ∈ hyp.K → d ∈ hyp.D →
      d * h * d⁻¹ ∈ hyp.K :=
    (Subgroup.normal_subgroupOf_iff hyp.K_le_D).mp
      (inferInstance : (hyp.K.subgroupOf hyp.D).Normal)
  have hconjK : x * k⁻¹ * x⁻¹ ∈ hyp.K :=
    hnormalK k⁻¹ x (hyp.K.inv_mem hk.1) (hyp.V_le_D (hXV hx))
  have hcommK : k * x * k⁻¹ * x⁻¹ ∈ hyp.K := by
    have : k * (x * k⁻¹ * x⁻¹) ∈ hyp.K := hyp.K.mul_mem hk.1 hconjK
    simpa only [mul_assoc] using this
  have hcommVK : k * x * k⁻¹ * x⁻¹ ∈ hyp.V ⊓ hyp.K :=
    ⟨hXV hcommX, hcommK⟩
  have hcomm1 : k * x * k⁻¹ * x⁻¹ = 1 := by
    rw [hyp.V_inf_K_eq_bot, Subgroup.mem_bot] at hcommVK
    exact hcommVK
  have hkx : k * x = x * k := by
    calc
      k * x = (k * x * k⁻¹ * x⁻¹) * (x * k) := by group
      _ = x * k := by rw [hcomm1, one_mul]
  exact hkx.symm

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(b)**, first factorization:
double transitivity gives `N_G(X) = C_G(X) N_D(X)`. -/
theorem normalizer_eq_centralizer_mul_normalizer_inf_D (hXV : X ≤ hyp.V) :
    (Subgroup.normalizer (X : Set G) : Set G) =
      (Subgroup.centralizer (X : Set G) : Set G) *
        ((hyp.D ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) := by
  ext g
  constructor
  · intro hg
    have hXD : X ≤ hyp.D := hXV.trans hyp.V_le_D
    have h3 : 3 ≤ (fixedPoints X Ω).ncard :=
      hyp.three_le_ncard_fixedPoints_of_le_V hXV
    have hb : hyp.basept ∈ fixedPoints X Ω :=
      hyp.basept_mem_fixedPoints hXD
    have ht : hyp.t • hyp.basept ∈ fixedPoints X Ω :=
      hyp.t_smul_basept_mem_fixedPoints hXD
    have hgb : g • hyp.basept ∈ fixedPoints X Ω :=
      smul_mem_fixedPoints_of_mem_normalizer hg hb
    have hgt : g • (hyp.t • hyp.basept) ∈ fixedPoints X Ω :=
      smul_mem_fixedPoints_of_mem_normalizer hg ht
    have htb : hyp.basept ≠ hyp.t • hyp.basept :=
      (hyp.smul_basept_ne_of_not_mem_H hyp.t_not_mem_H).symm
    have hgbt : g • hyp.basept ≠ g • (hyp.t • hyp.basept) := by
      intro heq
      exact htb (smul_left_cancel g heq)
    obtain ⟨c, hcC, hcb, hct⟩ := hyp.exists_mem_centralizer_smul_pair hXD h3
      hb ht hgb hgt htb hgbt
    let d : G := c⁻¹ * g
    have hdD : d ∈ hyp.D := by
      rw [hyp.D_eq_stabilizer_inf, Subgroup.mem_inf]
      constructor
      · rw [mem_stabilizer_iff]
        change (c⁻¹ * g) • hyp.basept = hyp.basept
        rw [mul_smul, ← hcb, inv_smul_smul]
      · rw [mem_stabilizer_iff]
        change (c⁻¹ * g) • (hyp.t • hyp.basept) = hyp.t • hyp.basept
        rw [mul_smul, ← hct, inv_smul_smul]
    have hdN : d ∈ Subgroup.normalizer (X : Set G) :=
      mul_mem (inv_mem (Subgroup.centralizer_le_normalizer _ hcC)) hg
    rw [Set.mem_mul]
    exact ⟨c, hcC, d, ⟨hdD, hdN⟩, by simp [d]⟩
  · rw [Set.mem_mul]
    rintro ⟨c, hcC, d, hd, rfl⟩
    exact mul_mem (Subgroup.centralizer_le_normalizer _ hcC) hd.2

/-- **Peterfalvi Part II, Ch. I §3 Prop 1(b)** — for `X ≤ V`,
`N_G(X) = C_G(X) N_V(X)`.  In the left-action convention the first
factorization above produces `c * d`; after the §1 inverse decomposition,
the final product is `(c * k) * v`, with `c * k ∈ C_G(X)`. -/
theorem normalizer_eq_centralizer_mul_normalizer_inf_V (hXV : X ≤ hyp.V) :
    (Subgroup.normalizer (X : Set G) : Set G) =
      (Subgroup.centralizer (X : Set G) : Set G) *
        ((hyp.V ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) := by
  ext n
  constructor
  · intro hn
    have hnCD : n ∈
        (Subgroup.centralizer (X : Set G) : Set G) *
          ((hyp.D ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) := by
      rw [← hyp.normalizer_eq_centralizer_mul_normalizer_inf_D hXV]
      exact hn
    rw [Set.mem_mul] at hnCD
    obtain ⟨c, hcC, d, hdDN, hcd⟩ := hnCD
    have hdKV : d ∈
        ((hyp.K ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) *
          ((hyp.V ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) := by
      rw [← hyp.normalizer_inf_D_eq_normalizer_inf_K_mul_normalizer_inf_V hXV]
      exact hdDN
    rw [Set.mem_mul] at hdKV
    obtain ⟨k, hkKN, v, hvVN, hkv⟩ := hdKV
    have hkC : k ∈ Subgroup.centralizer (X : Set G) :=
      hyp.normalizer_inf_K_le_centralizer hXV hkKN
    rw [Set.mem_mul]
    refine ⟨c * k, mul_mem hcC hkC, v, hvVN, ?_⟩
    calc
      (c * k) * v = c * (k * v) := mul_assoc _ _ _
      _ = c * d := by rw [hkv]
      _ = n := hcd
  · rw [Set.mem_mul]
    rintro ⟨c, hcC, v, hvVN, rfl⟩
    exact mul_mem (Subgroup.centralizer_le_normalizer _ hcC) hvVN.2

end Hypothesis

end

end OddOrder.Peterfalvi.Appendices.Suzuki
