/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepOne
import OddOrder.Peterfalvi.Appendices.Suzuki.Q1MinimalInvariant
import OddOrder.GroupTheory.RepresentationTheory.WielandtElabFrobenius
import OddOrder.GroupTheory.RepresentationTheory.WielandtElabBridge

/-!
# Peterfalvi Part II, Ch. II, step (3): the dimension identity for `M`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (3), p. 109.

For an elementary abelian `r`-subgroup `M ≤ Q` normalized by `KP`, the
kernel-FPF dimension identity ([Is] Theorem 15.16; here
`finrank_eq_card_mul_finrank_invariants_kernelFPF_zmod`) gives

`dim M = p · dim C_M(P)`,   i.e.   `|M| = |C_M(P)|^p`.

The hypotheses of the identity are supplied by Chapter I and step (1):

* `KP` is a Frobenius group with kernel `K`: `C_K(a) = 1` for `a ∈ P^#`
  is step (1)'s `C_K(P) = 1` (`K_inf_centralizer_eq_bot`), since `P` has
  prime order;
* `K` acts fixed-point-freely on `M ≤ Q` (§2 Proposition 1(a),
  `conjQByK_fixed_eq_one`), so `M^K = 0`;
* `(|E|, |U|) = (p, 2^p - 1)` are coprime (Fermat: `p ∤ 2^p - 1`);
* `r ∤ |K|`, since `r ∣ |M| ∣ |Q|` and `(|Q|, |K|) = 1`
  (`coprime_card_Q_K`).

No `r ≠ p` hypothesis is needed — the identity is characteristic-free in
`|E|`; the book obtains `r ≠ p` only as a *consequence* of the congruence
`r ≡ 2^i (mod 2^p - 1)` at the end of step (3).

As a corollary, `C_M(P) ≠ 1` for `M ≠ 1` — the book's opening Frobenius
argument for `C_M(P) ≠ 0` is subsumed by the identity itself.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory (IsElementaryAbelian fixedSubgroup elabRepresentation)
open Representation

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- **Peterfalvi Part II, Ch. II, step (3), the dimension identity**
(p. 109): for a nontrivial elementary abelian `r`-subgroup `M ≤ Q`
normalized by `KP`, `|M| = |C_M(P)|^p` (equivalently
`dim_{𝔽_r} M = p · dim_{𝔽_r} C_M(P)`, [Is] Theorem 15.16 applied to the
Frobenius group `KP` acting on `M` with `M^K = 0`). -/
theorem card_eq_card_inf_centralizer_pow {r : ℕ} (hr : r.Prime)
    {M : Subgroup G} (hMQ : M ≤ fc.toHypothesis.Q) (hMne : M ≠ ⊥)
    (helab : IsElementaryAbelian r ↥M)
    (hinv : ∀ g ∈ fc.toHypothesis.K ⊔ fc.P, ∀ m ∈ M, g * m * g⁻¹ ∈ M) :
    Nat.card ↥M =
      Nat.card ↥(M ⊓ Subgroup.centralizer (fc.P : Set G)) ^ fc.p := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  -- `L = KP` normalizes `M`, giving the conjugation action `φ`.
  have hLnorm : fc.toHypothesis.K ⊔ fc.P ≤
      Subgroup.normalizer (M : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hinv g hg x hx
    · intro hx
      have h2 := hinv g⁻¹ (inv_mem hg) _ hx
      simpa [mul_assoc] using h2
  set L : Subgroup G := fc.toHypothesis.K ⊔ fc.P with hLdef
  set φ : ↥L →* MulAut ↥M :=
    M.normalizerMonoidHom.comp (Subgroup.inclusion hLnorm) with hφdef
  have hφval : ∀ (a : ↥L) (m : ↥M),
      ((φ a m : ↥M) : G) = (a : G) * (m : G) * (a : G)⁻¹ := fun _ _ => rfl
  have hKL : fc.toHypothesis.K ≤ L := le_sup_left
  have hPL : fc.P ≤ L := le_sup_right
  set U : Subgroup ↥L := fc.toHypothesis.K.subgroupOf L with hUdef
  set E : Subgroup ↥L := fc.P.subgroupOf L with hEdef
  have hcardU : Nat.card ↥U = Nat.card ↥fc.toHypothesis.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv
  have hcardE : Nat.card ↥E = fc.p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv, fc.card_P]
  -- `U ◁ L`: `K` is normal in `D ⊇ L`.
  have hLD : L ≤ fc.toHypothesis.D :=
    sup_le fc.toHypothesis.K_le_D
      (fc.P_le_V.trans fc.toHypothesis.V_le_D)
  haveI hUnormal : U.Normal := by
    constructor
    intro n hn g
    have hn' : (n : G) ∈ fc.toHypothesis.K := hn
    have h := (inferInstance :
        (fc.toHypothesis.K.subgroupOf fc.toHypothesis.D).Normal).conj_mem
      (⟨(n : G), hLD n.2⟩ : ↥fc.toHypothesis.D)
      (Subgroup.mem_subgroupOf.mpr hn') ⟨(g : G), hLD g.2⟩
    exact Subgroup.mem_subgroupOf.mp h
  -- `U ⊔ E = ⊤` in `L = K ⊔ P`.
  have hsup : U ⊔ E = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, hUdef, hEdef,
      Subgroup.map_subgroupOf_eq_of_le hKL,
      Subgroup.map_subgroupOf_eq_of_le hPL,
      ← MonoidHom.range_eq_map, L.range_subtype]
  -- `|K| = 2^p - 1`, and `p ∤ 2^p - 1` (Fermat), so `(|E|, |U|) = 1`.
  have hcardK : Nat.card ↥fc.toHypothesis.K = 2 ^ fc.p - 1 := by
    rw [fc.toHypothesis.card_K_eq_card_Q0_sub_one, fc.card_Q0_eq_two_pow]
  have hfermat : ¬ fc.p ∣ 2 ^ fc.p - 1 := by
    intro hdvd
    have hcast : ((2 ^ fc.p - 1 : ℕ) : ZMod fc.p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod fc.p) fc.p _).mpr hdvd
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat,
      ZMod.pow_card, Nat.cast_one, sub_eq_zero] at hcast
    -- `hcast : (2 : ZMod p) = 1`, so `1 = 0` in the field `ZMod p`
    exact one_ne_zero (α := ZMod fc.p) (by linear_combination hcast)
  have hcopUE : Nat.Coprime (Nat.card ↥E) (Nat.card ↥U) := by
    rw [hcardE, hcardU, hcardK]
    exact (Nat.Prime.coprime_iff_not_dvd fc.p_prime).mpr hfermat
  have hEnt : 1 < Nat.card ↥E := by
    rw [hcardE]; exact fc.p_prime.one_lt
  -- `E` acts fixed-point-freely on `U`: step (1)'s `C_K(P) = 1`.
  have hfpf : ∀ e ∈ E, e ≠ 1 → ∀ u ∈ U, e * u * e⁻¹ = u → u = 1 := by
    intro e he hne u hu hconj
    have heP : ((e : ↥L) : G) ∈ fc.P := he
    have huK : ((u : ↥L) : G) ∈ fc.toHypothesis.K := hu
    have heG1 : ((e : ↥L) : G) ≠ 1 := fun h => hne (Subtype.ext h)
    -- `⟨e⟩ = P` since `P` has prime order.
    have hzpow : Subgroup.zpowers ((e : ↥L) : G) = fc.P := by
      have hle : Subgroup.zpowers ((e : ↥L) : G) ≤ fc.P :=
        (Subgroup.zpowers_le).mpr heP
      have horder : orderOf ((e : ↥L) : G) = fc.p := by
        have hdvd : orderOf ((e : ↥L) : G) ∣ fc.p := by
          rw [← fc.card_P]
          have h1 : orderOf ((e : ↥L) : G) =
              orderOf (⟨((e : ↥L) : G), heP⟩ : ↥fc.P) :=
            orderOf_injective fc.P.subtype fc.P.subtype_injective
              ⟨((e : ↥L) : G), heP⟩
          rw [h1]
          exact orderOf_dvd_natCard _
        rcases (fc.p_prime.eq_one_or_self_of_dvd _ hdvd) with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) heG1
        · exact h1
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [fc.card_P, Nat.card_zpowers, horder]
    -- `u` commutes with `e`, hence with all of `P = ⟨e⟩`.
    have hcomm : Commute ((e : ↥L) : G) ((u : ↥L) : G) := by
      have h := congrArg (fun z : ↥L => (z : G)) hconj
      have h' : ((e : ↥L) : G) * ((u : ↥L) : G) * ((e : ↥L) : G)⁻¹ =
          ((u : ↥L) : G) := h
      calc ((e : ↥L) : G) * ((u : ↥L) : G)
          = (((e : ↥L) : G) * ((u : ↥L) : G) * ((e : ↥L) : G)⁻¹) *
            ((e : ↥L) : G) := by group
        _ = ((u : ↥L) : G) * ((e : ↥L) : G) := by rw [h']
    have huC : ((u : ↥L) : G) ∈ Subgroup.centralizer (fc.P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [← hzpow] at hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact (hcomm.zpow_left n).eq
    have hmem : ((u : ↥L) : G) ∈
        fc.toHypothesis.K ⊓ Subgroup.centralizer (fc.P : Set G) :=
      ⟨huK, huC⟩
    rw [fc.K_inf_centralizer_eq_bot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  -- `r ∤ |U| = |K|`: `r ∣ |M| ∣ |Q|` and `(|Q|, |K|) = 1`.
  have hrM : r ∣ Nat.card ↥M := by
    haveI : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥M)
    have hxr : orderOf x = r := orderOf_eq_prime (helab.pow_eq_one x) hx1
    exact hxr ▸ orderOf_dvd_natCard x
  have hpU : ¬ r ∣ Nat.card ↥U := by
    rw [hcardU]
    intro hdvd
    have hrQ : r ∣ Nat.card ↥fc.toHypothesis.Q :=
      hrM.trans (Subgroup.card_dvd_of_le hMQ)
    have hr1 : r ∣ 1 :=
      fc.toHypothesis.coprime_card_Q_K ▸ Nat.dvd_gcd hrQ hdvd
    exact hr.ne_one (Nat.dvd_one.mp hr1)
  -- `C_M(K) = 1`: `K` acts fixed-point-freely on `Q ⊇ M` (§2 Prop 1(a)).
  have hfixU : fixedSubgroup φ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨k₀, hk₀K, hk₀1⟩ := fc.toHypothesis.exists_ne_one_mem_KSet
    have hk₀mem : k₀ ∈ fc.toHypothesis.K := by
      change k₀ ∈ (fc.toHypothesis.K : Set G)
      rw [fc.toHypothesis.coe_K]
      exact hk₀K
    have hφfix := hx (⟨k₀, hKL hk₀mem⟩ : ↥L)
      (Subgroup.mem_subgroupOf.mpr hk₀mem)
    have hxQ : ((x : ↥M) : G) ∈ fc.toHypothesis.Q := hMQ x.2
    have hQfix : fc.toHypothesis.conjQByK ⟨k₀, hk₀mem⟩
        ⟨((x : ↥M) : G), hxQ⟩ = ⟨((x : ↥M) : G), hxQ⟩ := by
      apply Subtype.ext
      rw [fc.toHypothesis.conjQByK_apply_val]
      exact congrArg (fun z : ↥M => (z : G)) hφfix
    have hk₀ne : (⟨k₀, hk₀mem⟩ : ↥fc.toHypothesis.K) ≠ 1 :=
      fun h => hk₀1 (congrArg Subtype.val h)
    have hxone := fc.toHypothesis.conjQByK_fixed_eq_one hk₀ne hQfix
    have hxG := congrArg (fun z : ↥fc.toHypothesis.Q => (z : G)) hxone
    exact Subtype.ext hxG
  -- The kernel-FPF identity in group-cardinality form ([Is] Thm 15.16).
  letI : CommGroup ↥M := helab.subgroupCommGroup
  letI : Module (ZMod r) (Additive ↥M) := helab.subgroupZmodModule
  have hkey := OddOrder.GroupTheory.WielandtKernelFPF.card_eq_card_fixedSubgroup_pow_of_frobenius
    hsup hcopUE hEnt hfpf hpU φ hfixU
  -- `C_M(P)` as an ambient subgroup: `fixedSubgroup φ E ≃ M ⊓ C_G(P)`.
  have hfixinf : Nat.card ↥(fixedSubgroup φ E) =
      Nat.card ↥(M ⊓ Subgroup.centralizer (fc.P : Set G)) := by
    apply Nat.card_congr
    refine Equiv.ofBijective
      (fun x => ⟨((x : ↥M) : G), (x : ↥M).2, ?_⟩) ⟨?_, ?_⟩
    · -- centralizer membership
      show ((x : ↥M) : G) ∈ Subgroup.centralizer (fc.P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hgL : g ∈ L := hPL hg
      have hfix := x.2 (⟨g, hgL⟩ : ↥L) (Subgroup.mem_subgroupOf.mpr hg)
      have hval : g * ((x : ↥M) : G) * g⁻¹ = ((x : ↥M) : G) :=
        congrArg (fun z : ↥M => (z : G)) hfix
      calc g * ((x : ↥M) : G)
          = (g * ((x : ↥M) : G) * g⁻¹) * g := by group
        _ = ((x : ↥M) : G) * g := by rw [hval]
    · -- injective
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(M ⊓ Subgroup.centralizer (fc.P : Set G)) =>
        (z : G)) hab
    · -- surjective
      rintro ⟨g, hgM, hgC⟩
      refine ⟨⟨⟨g, hgM⟩, ?_⟩, rfl⟩
      intro l hl
      apply Subtype.ext
      have hlP : ((l : ↥L) : G) ∈ fc.P := hl
      have hcomm := Subgroup.mem_centralizer_iff.mp hgC _ hlP
      show ((l : ↥L) : G) * g * ((l : ↥L) : G)⁻¹ = g
      rw [hcomm]
      group
  -- Assemble: `|M| = |C_M(P)|^{|E|} = |M ⊓ C_G(P)|^p`.
  exact hkey.trans (by rw [hfixinf, hcardE])

/-- **Peterfalvi Part II, Ch. II, step (3), `C_M(P) ≠ 1`** (p. 109): the
fixed points of `P` on a nontrivial `KP`-invariant elementary abelian
subgroup `M ≤ Q` are nontrivial — immediate from the dimension identity. -/
theorem inf_centralizer_ne_bot_of_invariant {r : ℕ} (hr : r.Prime)
    {M : Subgroup G} (hMQ : M ≤ fc.toHypothesis.Q) (hMne : M ≠ ⊥)
    (helab : IsElementaryAbelian r ↥M)
    (hinv : ∀ g ∈ fc.toHypothesis.K ⊔ fc.P, ∀ m ∈ M, g * m * g⁻¹ ∈ M) :
    M ⊓ Subgroup.centralizer (fc.P : Set G) ≠ ⊥ := by
  intro hbot
  apply hMne
  have hcard := fc.card_eq_card_inf_centralizer_pow hr hMQ hMne helab hinv
  rw [hbot, Subgroup.card_bot, one_pow] at hcard
  exact Subgroup.eq_bot_of_card_eq _ hcard

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
