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

end OddOrder.Peterfalvi.S13
