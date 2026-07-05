import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent
import OddOrder.Peterfalvi.S11_MaximalII_III_IV
import OddOrder.GroupTheory.RepresentationTheory.ClassTwoSquareIndex

/-! # Peterfalvi (11.7): the chief-kernel triviality frame

Peterfalvi (11.7) [Peterfalvi, *Character Theory for the Odd Order Theorem*, pp. 64-65] states
that under Hypothesis (11.2) the group `H` is elementary abelian of order `p^q` with trivial
chief kernel `H₀ = 1`.  By the chief-factor data ((9.4), `ChiefFactorData`) the whole content is
`H₀ = 1`; this file builds the *frame* of the contradiction argument, at the generic
`TypesIIIIIIVSetup`/`ChiefFactorData` level of §9 (repo `S11`), with the two character-gated
inputs — `H` is a `p`-group and `H₀ = H'` (both from (11.6), proven at the §11 `Hypothesis`
level in `S13_CoreStructure`) — taken as hypotheses.

Assuming `H₀ = N ≠ ⊥`:

* `commutator_top_lt_of_normal_of_ne_bot`: `[H, H₀] < H₀` (nilpotency of `H`);
* `exists_normal_subgroup_index_prime`: a normal `Q ◁ H` with `[H, H₀] ≤ Q ≤ H₀` and
  `|H₀ : Q| = p` (Peterfalvi cites [BG] Lemma 1.22; here built from a Sylow-tower subgroup of
  the abelian quotient `H₀/[H, H₀]`, normality being automatic above `[H, H₀]`);
* in `Ĥ = H/Q` the image `Ĥ₀ = H₀/Q` is then a central subgroup of order `p` equal to the
  commutator `Ĥ' = H'^` (as `H₀ = H'`), so `Ĥ` is a class-`2` group with `|Ĥ| = p^(q+1)`.

The `U`-action dichotomy on `H̄ = H/H₀` (`chiefFactor_clifford_U_dichotomy`, Peterfalvi (9.7))
then splits:

* **case (b)** (`U` irreducible on `H̄`): the image of `Z(Ĥ)` in `H̄` is `U`-invariant, hence
  `⊥` (forcing `Z(Ĥ) = Ĥ₀` and the parity contradiction `q` even via
  `even_of_card_eq_prime_pow_succ_of_class_two`, `ClassTwoSquareIndex.lean`) or `⊤` (forcing
  `Ĥ` abelian, contradicting `Ĥ' = Ĥ₀ ≠ 1`);
* **case (a)** (a `U`-invariant order-`p` factor): the Clifford line characters `φ_w` and the
  `W₁`-chain argument force `U` to centralize `H̄`, contradicting (9.4.b)
  (`U_noncentral_on_quotient`).

Coq: `PFsection11.FTtype34_Fcore_kernel_trivial` (which recasts the linear algebra of the
original text in pure group theory; we follow the same plan, with the extraspecial-order step
replaced by the square-index theorem). -/

namespace OddOrder.Peterfalvi.S13

open OddOrder.Peterfalvi.S11
open scoped commutatorElement

/-! ## The `p`-group frame: `[K, N] < N` and the index-`p` normal subgroup -/

section PGroupFrame

variable {K : Type*} [Group K]

/-- **`[K, N] < N` for a nontrivial normal subgroup of a nilpotent group**: if `[K, N] = N` the
lower central series could never swallow `N`. -/
theorem commutator_top_lt_of_normal_of_ne_bot [Group.IsNilpotent K]
    {N : Subgroup K} [hN : N.Normal] (hNne : N ≠ ⊥) :
    ⁅(⊤ : Subgroup K), N⁆ < N := by
  refine lt_of_le_of_ne (Subgroup.commutator_le_right ⊤ N) ?_
  intro heq
  apply hNne
  obtain ⟨n, hn⟩ := nilpotent_iff_lowerCentralSeries.mp ‹Group.IsNilpotent K›
  have hle : ∀ m, N ≤ lowerCentralSeries K m := by
    intro m
    induction m with
    | zero => exact le_top
    | succ m ih =>
        have hsucc : lowerCentralSeries K (m + 1) = ⁅lowerCentralSeries K m, ⊤⁆ := by
          rw [Subgroup.commutator_def, lowerCentralSeries_succ]
          rfl
        rw [hsucc]
        calc N = ⁅⊤, N⁆ := heq.symm
          _ = ⁅N, ⊤⁆ := Subgroup.commutator_comm _ _
          _ ≤ ⁅lowerCentralSeries K m, ⊤⁆ := Subgroup.commutator_mono ih le_rfl
  exact le_bot_iff.mp (hn ▸ hle n)

/-- **The index-`p` normal subgroup below a nontrivial normal subgroup of a `p`-group**
(Peterfalvi's citation of [BG] Lemma 1.22 in (11.7)): for `⊥ ≠ N ◁ K` with `K` a finite
`p`-group there is `Q ◁ K` with `[K, N] ≤ Q ≤ N` and `|N : Q| = p`.  Any subgroup between
`[K, N]` and `N` is automatically `K`-normal, so it suffices to take a hyperplane of the
nontrivial quotient `p`-group `N/[K, N]` (Sylow tower). -/
theorem exists_normal_subgroup_index_prime [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : IsPGroup p K) {N : Subgroup K} [hNnorm : N.Normal] (hNne : N ≠ ⊥) :
    ∃ Q : Subgroup K, Q.Normal ∧ Q ≤ N ∧ ⁅(⊤ : Subgroup K), N⁆ ≤ Q ∧
      Nat.card ↥N = p * Nat.card ↥Q := by
  classical
  haveI := Fact.mk hp
  haveI : Group.IsNilpotent K := hK.isNilpotent
  have hRlt : ⁅(⊤ : Subgroup K), N⁆ < N := commutator_top_lt_of_normal_of_ne_bot hNne
  haveI hRnorm : (⁅(⊤ : Subgroup K), N⁆).Normal := Subgroup.commutator_normal ⊤ N
  set R' : Subgroup ↥N := (⁅(⊤ : Subgroup K), N⁆).subgroupOf N with hR'def
  haveI : R'.Normal := Subgroup.normal_subgroupOf
  -- the quotient `Ā = N/[K,N]` is a nontrivial finite `p`-group
  have hAbar_pgroup : IsPGroup p (↥N ⧸ R') := (hK.to_subgroup N).to_quotient R'
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hAbar_pgroup
  have hAbar_ne : Nat.card (↥N ⧸ R') ≠ 1 := by
    intro h1
    have hR'top : R' = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup R'
      rw [h1, one_mul] at hprod
      exact hprod.symm
    exact absurd (le_antisymm hRlt.le ((Subgroup.subgroupOf_eq_top).mp hR'top)) hRlt.ne
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · rw [h0, pow_zero] at hm
      exact absurd hm hAbar_ne
    · exact h
  -- a hyperplane `Q̄ ≤ Ā` of order `p^(m-1)`
  obtain ⟨Qbar, hQbarcard, -⟩ := Sylow.exists_subgroup_card_pow_prime_le p
    (n := 0) (m := m - 1)
    (by rw [hm]; exact pow_dvd_pow p (by omega)) ⊥ (by simp) (by omega)
  -- pull back to `↥N`: index `p`
  set Q₀ : Subgroup ↥N := Qbar.comap (QuotientGroup.mk' R') with hQ₀def
  have hQ₀index : Q₀.index = p := by
    rw [hQ₀def, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective R')]
    have hprod := Subgroup.index_mul_card Qbar
    rw [hQbarcard, hm] at hprod
    have hpm : p ^ m = p * p ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpm] at hprod
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) hprod
  -- `[K,N] ≤ Q₀.map N.subtype`
  have hRle : ⁅(⊤ : Subgroup K), N⁆ ≤ Q₀.map N.subtype := by
    intro r hr
    have hrN : r ∈ N := hRlt.le hr
    refine ⟨⟨r, hrN⟩, ?_, rfl⟩
    show (⟨r, hrN⟩ : ↥N) ∈ Q₀
    rw [hQ₀def, Subgroup.mem_comap]
    have : (⟨r, hrN⟩ : ↥N) ∈ R' := by
      rw [hR'def, Subgroup.mem_subgroupOf]
      exact hr
    rw [show (QuotientGroup.mk' R') ⟨r, hrN⟩ = 1 from (QuotientGroup.eq_one_iff _).mpr this]
    exact Qbar.one_mem
  have hQle : Q₀.map N.subtype ≤ N := Subgroup.map_subtype_le _
  refine ⟨Q₀.map N.subtype, ?_, hQle, hRle, ?_⟩
  · -- normality: `g q g⁻¹ = ⁅g, q⁆ * q` with `⁅g, q⁆ ∈ [K, N] ≤ Q`
    refine ⟨fun q hq g => ?_⟩
    have hcomm : ⁅g, q⁆ ∈ Q₀.map N.subtype :=
      hRle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (hQle hq))
    have hgq : g * q * g⁻¹ = ⁅g, q⁆ * q := by
      rw [commutatorElement_def]
      group
    rw [hgq]
    exact Subgroup.mul_mem _ hcomm hq
  · -- the order relation `|N| = p * |Q|`
    have hcards : Nat.card ↥(Q₀.map N.subtype) = Nat.card ↥Q₀ :=
      (Nat.card_congr (Q₀.equivMapOfInjective N.subtype N.subtype_injective).toEquiv).symm
    rw [hcards, ← hQ₀index]
    exact (Subgroup.index_mul_card Q₀).symm

end PGroupFrame

/-! ## The class-`2` structure of `Ĥ = K/Q` -/

section QuotientClassTwo

variable {K : Type*} [Group K]

/-- **The class-`2` structure of `Ĥ = K/Q`** (Peterfalvi (11.7), central-quotient step): for
`Q ◁ K` with `[K, N] ≤ Q ≤ N`, `|N : Q| = p`, and `N = K'`, in the quotient `Ĥ = K/Q` the image
`N̂ = N/Q`:

* has order `p`;
* equals the commutator `Ĥ' = K'Q/Q`;
* is *central* (directly from `[K, N] ≤ Q` — no `p`-group argument needed);

so `Ĥ` has nilpotency class `≤ 2` with `Ĥ' = N̂ ≤ Z(Ĥ)` of order `p`. -/
theorem quotient_classTwo_structure [Finite K] {p : ℕ} (hp : p.Prime)
    {N Q : Subgroup K} [hNnorm : N.Normal] (hQnorm : Q.Normal) (hQle : Q ≤ N)
    (hRQ : ⁅(⊤ : Subgroup K), N⁆ ≤ Q) (hcard : Nat.card ↥N = p * Nat.card ↥Q)
    (hNcomm : N = commutator K) :
    haveI := hQnorm
    Nat.card ↥(N.map (QuotientGroup.mk' Q)) = p ∧
      commutator (K ⧸ Q) = N.map (QuotientGroup.mk' Q) ∧
      N.map (QuotientGroup.mk' Q) ≤ Subgroup.center (K ⧸ Q) := by
  haveI := hQnorm
  refine ⟨?_, ?_, ?_⟩
  · -- `|N/Q| = p`: first isomorphism for `mk' Q` restricted to `N`
    set f : ↥N →* K ⧸ Q := (QuotientGroup.mk' Q).comp N.subtype with hf
    have hrange : f.range = N.map (QuotientGroup.mk' Q) := by
      rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    have hker : f.ker = Q.subgroupOf N := by
      rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      rfl
    have hiso := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have hkercard : Nat.card ↥f.ker = Nat.card ↥Q := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv
    rw [hiso, hrange, hkercard, hcard] at hprod
    have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hQpos hprod.symm)
  · -- `Ĥ' = N̂`: commutators map onto commutators under the surjection
    have h1 : commutator (K ⧸ Q) = (commutator K).map (QuotientGroup.mk' Q) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)]
    rw [h1, hNcomm]
  · -- `N̂ ≤ Z(Ĥ)`: `[K, N] ≤ Q` kills every commutator against `N̂`
    rintro _ ⟨n, hnN, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro ghat
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q ghat
    have hcomm : ⁅g, n⁆ ∈ Q := hRQ
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hnN)
    have h1 : (QuotientGroup.mk' Q) ⁅g, n⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1

end QuotientClassTwo

/-! ## Class-`2` commutator calculus (for case (a)) -/

section ClassTwoCalculus

variable {Γ : Type*} [Group Γ]

/-- Central factors drop out of commutators (left argument). -/
theorem commutatorElement_mul_center_left {z : Γ} (hz : z ∈ Subgroup.center Γ) (a b : Γ) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hzb : z * b = b * z := (Subgroup.mem_center_iff.mp hz b).symm
  rw [commutatorElement_def, commutatorElement_def]
  rw [show a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ by group, hzb]
  group

/-- Central factors drop out of commutators (right argument). -/
theorem commutatorElement_mul_center_right {z : Γ} (hz : z ∈ Subgroup.center Γ) (a b : Γ) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_center_left hz,
    commutatorElement_inv]

/-- The product expansion `⁅x·y, b⁆ = ⁅y, b⁆ · ⁅x, b⁆` when `⁅y, b⁆` is central
(the class-`2` "linearity" seed). -/
theorem commutatorElement_mul_left_of_center {y b : Γ}
    (hc : ⁅y, b⁆ ∈ Subgroup.center Γ) (x : Γ) :
    ⁅x * y, b⁆ = ⁅y, b⁆ * ⁅x, b⁆ := by
  have hexp : ⁅x * y, b⁆ = x * ⁅y, b⁆ * (b * x⁻¹ * b⁻¹) := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [hexp, show x * ⁅y, b⁆ * (b * x⁻¹ * b⁻¹) = x * (⁅y, b⁆ * (b * x⁻¹ * b⁻¹)) by group,
    ← Subgroup.mem_center_iff.mp hc (b * x⁻¹ * b⁻¹),
    show x * (b * x⁻¹ * b⁻¹ * ⁅y, b⁆) = (x * b * x⁻¹ * b⁻¹) * ⁅y, b⁆ by group,
    ← commutatorElement_def]
  exact Subgroup.mem_center_iff.mp hc ⁅x, b⁆

/-- **Class-`2` power bilinearity (left)**: `⁅a^k, b⁆ = ⁅a, b⁆^k` when `⁅a, b⁆` is central. -/
theorem commutatorElement_pow_left_of_center {a b : Γ}
    (hc : ⁅a, b⁆ ∈ Subgroup.center Γ) (k : ℕ) :
    ⁅a ^ k, b⁆ = ⁅a, b⁆ ^ k := by
  induction k with
  | zero => simp [commutatorElement_def]
  | succ k ih =>
      have hkc : ⁅a ^ k, b⁆ ∈ Subgroup.center Γ := by
        rw [ih]
        exact Subgroup.pow_mem _ hc k
      rw [pow_succ, show a ^ k * a = a * a ^ k by exact (Commute.pow_self a k).eq,
        commutatorElement_mul_left_of_center hkc a, ih, pow_succ]

/-- **Class-`2` power bilinearity (right)**: `⁅a, b^k⁆ = ⁅a, b⁆^k` when `⁅a, b⁆` is central. -/
theorem commutatorElement_pow_right_of_center {a b : Γ}
    (hc : ⁅a, b⁆ ∈ Subgroup.center Γ) (k : ℕ) :
    ⁅a, b ^ k⁆ = ⁅a, b⁆ ^ k := by
  have hc' : ⁅b, a⁆ ∈ Subgroup.center Γ := by
    have := Subgroup.inv_mem _ hc
    rwa [commutatorElement_inv] at this
  rw [← commutatorElement_inv, commutatorElement_pow_left_of_center hc', ← inv_pow,
    commutatorElement_inv]

end ClassTwoCalculus

/-! ## The exponent of an automorphism on an order-`p` subgroup -/

section PrimeExponent

variable {Γ : Type*} [Group Γ]

/-- **An automorphism preserving a subgroup of prime order acts by exponentiation**: if
`|T| = p` and `e` maps `T` into itself, there is `k` (indivisible by `p`) with `e h = h^k` for
all `h ∈ T`. -/
theorem exists_pow_eq_of_mapsTo_of_card_prime {p : ℕ} (hp : p.Prime)
    {T : Subgroup Γ} (hT : Nat.card ↥T = p) (e : MulAut Γ)
    (hmem : ∀ h ∈ T, e h ∈ T) :
    ∃ k : ℕ, ¬ p ∣ k ∧ ∀ h ∈ T, e h = h ^ k := by
  classical
  haveI : Finite ↥T := Nat.finite_of_card_ne_zero (hT ▸ hp.pos.ne')
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic ↥T := isCyclic_of_prime_card hT
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := ↥T)
  have htord : orderOf t = p := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ht, hT]
  have htfin : IsOfFinOrder t := isOfFinOrder_of_finite t
  -- `e t = t^k` for a natural `k`
  obtain ⟨k, hk⟩ := htfin.mem_powers_iff_mem_zpowers.mpr
    (ht (⟨e ↑t, hmem ↑t t.2⟩ : ↥T))
  have hek : e (↑t : Γ) = (↑t : Γ) ^ k := by
    have := congrArg (Subtype.val : ↥T → Γ) hk
    simpa using this.symm
  refine ⟨k, ?_, ?_⟩
  · -- `p ∤ k`: otherwise `e t = 1`, so `t = 1`, contradicting `|T| = p`
    intro hdvd
    have ht1 : t ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp (htord ▸ hdvd)
    have hcoe1 : (↑t : Γ) ^ k = 1 := by
      have := congrArg (Subtype.val : ↥T → Γ) ht1
      simpa using this
    have het1 : e (↑t : Γ) = 1 := by rw [hek, hcoe1]
    have ht1' : (↑t : Γ) = 1 := by
      have := congrArg e.symm het1
      simpa using this
    have : t = 1 := Subtype.ext (by simpa using ht1')
    rw [this, orderOf_one] at htord
    exact hp.one_lt.ne' htord.symm
  · -- every `h ∈ T` is a power of `t`, and `e` commutes with powers
    intro h hh
    obtain ⟨m, hm⟩ := htfin.mem_powers_iff_mem_zpowers.mpr (ht (⟨h, hh⟩ : ↥T))
    have hcoe : h = (↑t : Γ) ^ m := by
      have := congrArg (Subtype.val : ↥T → Γ) hm
      simpa using this.symm
    rw [hcoe, map_pow, hek, ← pow_mul, ← pow_mul, Nat.mul_comm]

end PrimeExponent

/-! ## Abelian from a commuting generating set -/

section ClosureCommute

variable {Γ : Type*} [Group Γ]

/-- A group generated by a pairwise-commuting set is abelian (elementwise form). -/
theorem commute_all_of_closure_eq_top {S : Set Γ}
    (hS : Subgroup.closure S = ⊤) (hcomm : ∀ x ∈ S, ∀ y ∈ S, Commute x y)
    (a b : Γ) : Commute a b := by
  have ha : a ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top a
  have hb : b ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top b
  refine Subgroup.closure_induction (p := fun x _ => Commute x b) ?_ (Commute.one_left b)
    (fun x y _ _ hx hy => hx.mul_left hy) (fun x _ hx => hx.inv_left) ha
  intro x hxS
  refine Subgroup.closure_induction (p := fun y _ => Commute x y)
    (fun y hyS => hcomm x hxS y hyS) (Commute.one_right x)
    (fun y z _ _ h1 h2 => h1.mul_right h2) (fun y _ h1 => h1.inv_right) hb

end ClosureCommute

section CaseB

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant)
open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

/-- **Peterfalvi (11.7), Galois case refuted**: if `H` is a `p`-group with `H₀ = N = H'` a
*nontrivial* chief kernel, `U` centralizes `N`, and `U` acts irreducibly on `H̄ = H/H₀`
(Clifford case (b) of (9.7)), then `q = |W₁|` odd is contradictory.

With `Q ◁ H`, `[H, N] ≤ Q ≤ N`, `|N : Q| = p` (`exists_normal_subgroup_index_prime`), the
quotient `Ĥ = H/Q` is class-`2` with `Ĥ' = N̂ ≤ Z(Ĥ)` of order `p`
(`quotient_classTwo_structure`).  The image of `Z(Ĥ)` in `H̄` is `U`-invariant (the `U`-action
descends past the `U`-pointwise-fixed `Q`, and centers are characteristic), so by irreducibility
it is `⊥` — giving `Z(Ĥ) = N̂` of order `p` and the parity contradiction
`even_of_card_eq_prime_pow_succ_of_class_two` (`|Ĥ| = p^(q+1)` forces `q` even) — or `⊤` —
making `Ĥ` abelian, contradicting `|Ĥ'| = p`. -/
theorem chiefKernel_caseB_false [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hpK : IsPGroup chief.p ↥data.H)
    (hNcomm : chief.N = commutator ↥data.H)
    (hUcent : ∀ (u : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (n : ↥data.H), n ∈ chief.N → typeP_conjAction data.typeP ↑u n = n)
    (hqodd : Odd data.q)
    (hNne : chief.N ≠ ⊥)
    (hirr : ∀ J : Subgroup (↥data.H ⧸ chief.N),
      IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) :
    False := by
  classical
  haveI := Fact.mk chief.p_prime
  -- the index-`p` normal subgroup `Q` and the class-`2` structure of `Ĥ = H/Q`
  obtain ⟨Q, hQnorm, hQle, hRQ, hcard⟩ :=
    exists_normal_subgroup_index_prime chief.p_prime hpK hNne
  haveI := hQnorm
  obtain ⟨hNhatCard, hcommHat, hNhatLe⟩ :=
    quotient_classTwo_structure chief.p_prime hQnorm hQle hRQ hcard hNcomm
  -- the projection `π : Ĥ → H̄`
  set π : (↥data.H ⧸ Q) →* (↥data.H ⧸ chief.N) :=
    QuotientGroup.map Q chief.N (MonoidHom.id ↥data.H) (by simpa using hQle) with hπdef
  have hπmk : ∀ x : ↥data.H, π ((QuotientGroup.mk' Q) x) = (QuotientGroup.mk' chief.N) x :=
    fun x => rfl
  have hπker : π.ker = chief.N.map (QuotientGroup.mk' Q) := by
    ext h
    constructor
    · intro hh
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q h
      rw [MonoidHom.mem_ker, hπmk] at hh
      exact ⟨x, (QuotientGroup.eq_one_iff _).mp hh, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      rw [MonoidHom.mem_ker, hπmk]
      exact (QuotientGroup.eq_one_iff _).mpr hn
  -- the `U`-action descends to `Ĥ` (as `U` fixes `Q ≤ N` pointwise)
  set φU : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) →* MulAut ↥data.H :=
    (typeP_conjAction data.typeP).comp
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype with hφUdef
  have hQinv : IsAInvariant φU Q := by
    intro u
    change Q.map (φU u).toMonoidHom = Q
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hfix : (φU u) x = x := hUcent u x (hQle hx)
      rw [show (φU u).toMonoidHom x = x from hfix]
      exact hx
    · intro x hx
      exact ⟨x, hx, hUcent u x (hQle hx)⟩
  -- the `π`-equivariance of the two descended `U`-actions
  have hπσ : ∀ (u : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (h : ↥data.H ⧸ Q),
      ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) u (π h) = π (quotientMulAutHom hQinv u h) := by
    intro u h
    refine QuotientGroup.induction_on h ?_
    intro x
    rfl
  -- centers are preserved by every automorphism
  have hZcen : ∀ (e : MulAut (↥data.H ⧸ Q)) (z : ↥data.H ⧸ Q),
      z ∈ Subgroup.center (↥data.H ⧸ Q) → e z ∈ Subgroup.center (↥data.H ⧸ Q) := by
    intro e z hz
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    calc g * e z = e (e.symm g * z) := by rw [map_mul, e.apply_symm_apply]
      _ = e (z * e.symm g) := by rw [hz (e.symm g)]
      _ = e z * g := by rw [map_mul, e.apply_symm_apply]
  -- the image of the center of `Ĥ` in `H̄` is `U`-invariant
  set J : Subgroup (↥data.H ⧸ chief.N) := (Subgroup.center (↥data.H ⧸ Q)).map π with hJdef
  have hJinv : IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
      chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
      chief.N_aInvariant).U.subtype) J := by
    intro u
    change J.map _ = J
    apply le_antisymm
    · rintro _ ⟨j, hj, rfl⟩
      rw [hJdef] at hj
      obtain ⟨z, hz, rfl⟩ := hj
      exact ⟨quotientMulAutHom hQinv u z, hZcen _ z hz, (hπσ u z).symm⟩
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨π ((quotientMulAutHom hQinv u).symm z),
        ⟨(quotientMulAutHom hQinv u).symm z, hZcen _ z hz, rfl⟩, ?_⟩
      exact (hπσ u _).trans (congrArg π ((quotientMulAutHom hQinv u).apply_symm_apply z))
  -- `|Ĥ| = p^(q+1)`
  have hHhatCard : Nat.card (↥data.H ⧸ Q) = chief.p ^ (data.q + 1) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Q
    have h2 : Nat.card ↥chief.H0 = Nat.card ↥chief.N := by
      rw [chief.H0_eq]
      exact (Nat.card_congr
        (chief.N.equivMapOfInjective data.H.subtype data.H.subtype_injective).toEquiv).symm
    have h3 := chief.quotient_order
    rw [h1, h2, hcard] at h3
    have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hQpos ?_
    rw [h3, pow_succ]
    ring
  -- the dichotomy
  rcases hirr J hJinv with hJbot | hJtop
  · -- `J = ⊥`: `Z(Ĥ) = N̂` of order `p`, and the square-index parity forces `q` even
    have hZle : Subgroup.center (↥data.H ⧸ Q) ≤ chief.N.map (QuotientGroup.mk' Q) := by
      rw [← hπker]
      exact (Subgroup.map_eq_bot_iff _).mp hJbot
    have hZeq : Subgroup.center (↥data.H ⧸ Q) = chief.N.map (QuotientGroup.mk' Q) :=
      le_antisymm hZle hNhatLe
    have heven : Even data.q := by
      refine OddOrder.RepresentationTheory.even_of_card_eq_prime_pow_succ_of_class_two
        chief.p_prime (hpK.to_quotient Q) ?_ ?_ hHhatCard
      · rw [hZeq]
        exact hNhatCard
      · rw [hcommHat, ← hZeq]
    exact (Nat.not_even_iff_odd.mpr hqodd) heven
  · -- `J = ⊤`: `Ĥ` is abelian, contradicting `|Ĥ'| = p`
    have hZtop : Subgroup.center (↥data.H ⧸ Q) = ⊤ := by
      rw [eq_top_iff]
      intro h _
      have hmemJ : π h ∈ J := by
        rw [hJtop]
        exact Subgroup.mem_top _
      obtain ⟨z, hz, hzeq⟩ := hmemJ
      have hker : z⁻¹ * h ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hzeq, inv_mul_cancel]
      have hmem : z⁻¹ * h ∈ Subgroup.center (↥data.H ⧸ Q) :=
        hNhatLe (hπker ▸ hker)
      have hsplit : h = z * (z⁻¹ * h) := by group
      rw [hsplit]
      exact Subgroup.mul_mem _ hz hmem
    have hcommbot : commutator (↥data.H ⧸ Q) = ⊥ := by
      rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro g _ h _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.mp (hZtop ▸ Subgroup.mem_top h) g
    rw [hcommbot] at hcommHat
    have : Nat.card ↥(⊥ : Subgroup (↥data.H ⧸ Q)) = chief.p := hcommHat ▸ hNhatCard
    rw [Subgroup.card_bot] at this
    exact absurd this.symm chief.p_prime.one_lt.ne'

end CaseB

/-! ## Case (a): the fixed-point endgame -/

section CaseA

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant)
open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)
open scoped Pointwise

/-- **Case (a) endgame**: if `U` fixes the order-`p` factor `S₀ ≠ ⊥` pointwise, it fixes every
`U W₁`-translate pointwise (conjugating the acting element back into the normal kernel `U`),
hence all of `H̄ = ⨆ translates` — contradicting (9.4.b) (`U_noncentral_on_quotient`). -/
theorem caseA_fixed_contradiction [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    {S₀ : Subgroup (↥data.H ⧸ chief.N)} (hS₀ne : S₀ ≠ ⊥)
    (hfix : ∀ (v : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))),
      ∀ s ∈ S₀, quotientMulAutHom chief.N_aInvariant ↑v s = s) :
    False := by
  have hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer data.typeP.W1_normalizes_U)
  have hspan := iSup_smul_eq_top_of_irreducible
    (φ := quotientMulAutHom chief.N_aInvariant) chief.quotient_chiefFactor hS₀ne
  -- every translate is fixed pointwise by the `U`-part
  have hfixT : ∀ (a : ↥(data.typeP.U ⊔ data.typeP.W1)),
      (quotientMulAutHom chief.N_aInvariant a) • S₀ ≤
        OddOrder.GroupTheory.fixedSubgroup (quotientMulAutHom chief.N_aInvariant)
          (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) := by
    intro a h hh
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hh
    obtain ⟨s, hs, rfl⟩ := hh
    rw [OddOrder.GroupTheory.mem_fixedSubgroup]
    intro l hl
    have hc : a⁻¹ * l * a ∈ data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1) := by
      simpa using hUnorm.conj_mem l hl a⁻¹
    have hkey := hfix ⟨a⁻¹ * l * a, hc⟩ s hs
    rw [MulAut.smul_def, ← MulAut.mul_apply, ← map_mul,
      show l * a = a * (a⁻¹ * l * a) by group, map_mul, MulAut.mul_apply, hkey]
  have htop : OddOrder.GroupTheory.fixedSubgroup (quotientMulAutHom chief.N_aInvariant)
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact iSup_le hfixT
  exact chief.U_noncentral_on_quotient htop

end CaseA

end OddOrder.Peterfalvi.S13
