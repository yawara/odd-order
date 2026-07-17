import OddOrder.BG.Ch3_MaximalSubgroups.S13_PrimeAction
import OddOrder.BG.Ch3_MaximalSubgroups.S13_PrimeActionTransition
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem125
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1211
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1217
import OddOrder.BG.Ch3_MaximalSubgroups.S14_Prop142Support
import OddOrder.BG.Ch1_Preliminary.S03c_Thm37
import OddOrder.BG.Ch1_Preliminary.S03g_Thm310
import OddOrder.GroupTheory.MaximalSubgroupType
import OddOrder.GroupTheory.MaximalSubgroupTypeConj
import OddOrder.GroupTheory.PiElementDecomposition

/-!
# BG §14 — split-extension derived subgroup + kappa(M), type-P families, sigma-length

Split from the former monolithic `OddOrder.BG.Ch4_FamilyOfMaximal.S14_TypePCounting` (directory split, issue 0103).
-/
namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch3.S13
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Derived subgroup of a split extension (general group theory)

Used for BG Theorem 14.7(h): if `M = M_σ ⋊ E` and `M_σ ≤ M'`, then `M' = M_σ ⊔ E'`, so the
type-`P` complement structure reduces to `E = K ⋉ E'` inside the `σ(M)'`-complement `E`. -/

open scoped commutatorElement in
/-- **Derived subgroup of a split extension**: if `N ⊴ H` has a complement `E`
(`H = N ⋊ E`) and `N ≤ H'`, then `H' = N ⊔ ⁅E, E⁆`.

`N ⊔ ⁅E,E⁆ ≤ H'` is immediate (`N ≤ H'` by hypothesis, `⁅E,E⁆ ≤ ⁅⊤,⊤⁆ = H'`).  For
`H' ≤ N ⊔ ⁅E,E⁆`, every commutator `⁅n₁e₁, n₂e₂⁆` is congruent mod `N` to `⁅e₁,e₂⁆ ∈ ⁅E,E⁆`
(pushing through `H ↠ H/N` kills the `N`-factors), and `N ⊴ H` makes `N · ⁅E,E⁆` a subgroup. -/
theorem commutator_eq_sup_commutator_of_isComplement' {H : Type*} [Group H]
    {N E : Subgroup H} [N.Normal] (hcompl : N.IsComplement' E)
    (hNle : N ≤ commutator H) :
    commutator H = N ⊔ ⁅E, E⁆ := by
  have hsup : N ⊔ E = ⊤ := hcompl.sup_eq_top
  refine le_antisymm ?_ (sup_le hNle ?_)
  · -- `H' = ⁅⊤,⊤⁆ ≤ N ⊔ ⁅E,E⁆`.
    rw [commutator_def, ← hsup, Subgroup.commutator_le]
    intro a ha b hb
    -- Decompose `a = n₁ e₁`, `b = n₂ e₂` using `N ⊴ H`.
    obtain ⟨n₁, hn₁, e₁, he₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
    obtain ⟨n₂, hn₂, e₂, he₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hb
    -- `⁅n₁e₁, n₂e₂⁆ ≡ ⁅e₁,e₂⁆  (mod N)`, via `H ↠ H/N`.
    have hmod : ⁅n₁ * e₁, n₂ * e₂⁆ * ⁅e₁, e₂⁆⁻¹ ∈ N := by
      have hf₁ : (QuotientGroup.mk' N) n₁ = 1 := (QuotientGroup.eq_one_iff n₁).mpr hn₁
      have hf₂ : (QuotientGroup.mk' N) n₂ = 1 := (QuotientGroup.eq_one_iff n₂).mpr hn₂
      have key : (QuotientGroup.mk' N) (⁅n₁ * e₁, n₂ * e₂⁆ * ⁅e₁, e₂⁆⁻¹) = 1 := by
        simp only [map_mul, map_inv, map_commutatorElement, hf₁, hf₂, one_mul, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp (by rwa [QuotientGroup.mk'_apply] at key)
    -- `⁅n₁e₁, n₂e₂⁆ = (⁅n₁e₁,n₂e₂⁆ ⁅e₁,e₂⁆⁻¹) · ⁅e₁,e₂⁆ ∈ N · ⁅E,E⁆ ⊆ N ⊔ ⁅E,E⁆`.
    have heq : ⁅n₁ * e₁, n₂ * e₂⁆ = (⁅n₁ * e₁, n₂ * e₂⁆ * ⁅e₁, e₂⁆⁻¹) * ⁅e₁, e₂⁆ := by
      group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmod)
      (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator he₁ he₂))
  · -- `⁅E,E⁆ ≤ ⁅⊤,⊤⁆ = H'`.
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top

/-! ## Basic §14 notation: `kappa(M)`, type-P families, and sigma-length -/

/-- The set of prime divisors of a finite subgroup, used as BG's `pi(M)`. -/
def piSet (M : Subgroup G) : Set ℕ :=
  {p | p ∈ (Nat.card ↥M).primeFactors}

/-- BG `pi(M) - sigma(M)`, as a set of natural primes. -/
def sigmaComplementPrimes (M : Subgroup G) : Set ℕ :=
  piSet M \ OddOrder.BG.Ch3.S10.sigma M

/-- **BG `kappa(M)`** (mmd L3760): primes in `tau_1(M) ∪ tau_3(M)` for which
some rank-one elementary abelian `p`-subgroup has nontrivial centralizer in
`M_sigma`. -/
def kappa (M : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧ p ∈ tau1 M ∪ tau3 M ∧
    ∃ P : Subgroup G, P ∈ elemAbelianOfRank G p 1 ∧ P ≤ M ∧
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥}

/-- **BG `M_P`**: maximal subgroups with nonempty `kappa(M)`. -/
def IsTypeP (M : Subgroup G) : Prop :=
  (kappa M).Nonempty

/-- **BG `M_P1`**: type-P maximal subgroups with maximal `kappa(M)`. -/
def IsTypeP1 (M : Subgroup G) : Prop :=
  IsTypeP M ∧ kappa M = sigmaComplementPrimes M

/-- **BG `M_P2`**: type-P maximal subgroups whose `kappa(M)` is a proper subset. -/
def IsTypeP2 (M : Subgroup G) : Prop :=
  IsTypeP M ∧ kappa M ≠ sigmaComplementPrimes M

/-- **BG `M_F` family**: the Frobenius-type maximal subgroups, i.e. `kappa(M)=empty`. -/
def IsTypeF (M : Subgroup G) : Prop :=
  kappa M = ∅

/-! ### Type classification: basic relations

These hold for any group purely from the definitions (no §13 input).  They record the
`M_F = ¬M_P` complementarity and the `M_P = M_P1 ⊔ M_P2` partition that §§15--16 use when
casing on the type of a maximal subgroup. -/

theorem isTypeP_of_isTypeP1 {M : Subgroup G} (h : IsTypeP1 M) : IsTypeP M := h.1

theorem isTypeP_of_isTypeP2 {M : Subgroup G} (h : IsTypeP2 M) : IsTypeP M := h.1

/-- The type-`P` maximal subgroups split as the (disjoint) union of `M_P1` and `M_P2`. -/
theorem isTypeP_iff_isTypeP1_or_isTypeP2 {M : Subgroup G} :
    IsTypeP M ↔ IsTypeP1 M ∨ IsTypeP2 M := by
  constructor
  · intro hP
    by_cases h : kappa M = sigmaComplementPrimes M
    · exact Or.inl ⟨hP, h⟩
    · exact Or.inr ⟨hP, h⟩
  · rintro (h | h) <;> exact h.1

/-- `M_P1` and `M_P2` are disjoint: `kappa(M)` cannot both equal and differ from `π(M)∖σ(M)`. -/
theorem not_isTypeP1_and_isTypeP2 {M : Subgroup G} : ¬ (IsTypeP1 M ∧ IsTypeP2 M) := by
  rintro ⟨⟨_, h1⟩, _, h2⟩
  exact h2 h1

/-- `M_F` (Frobenius type) is exactly the complement of `M_P` (type `P`). -/
theorem isTypeF_iff_not_isTypeP {M : Subgroup G} : IsTypeF M ↔ ¬ IsTypeP M := by
  simp only [IsTypeF, IsTypeP, Set.not_nonempty_iff_eq_empty]

/-- A maximal subgroup is not simultaneously type `P` and Frobenius type. -/
theorem not_isTypeP_and_isTypeF {M : Subgroup G} : ¬ (IsTypeP M ∧ IsTypeF M) := by
  rintro ⟨hP, hF⟩
  exact (isTypeF_iff_not_isTypeP.mp hF) hP

/-- `κ(M) ⊆ τ₁(M) ∪ τ₃(M)`, directly from the definition of `κ`.  Used in Proposition 14.2:
a Hall `κ(M)`-subgroup is a `σ(M)'`-subgroup (since `τ₁, τ₃ ⊆ σ(M)'`), so the §12 `E`-setup
may be chosen to contain it. -/
theorem kappa_subset_tau1_union_tau3 {M : Subgroup G} : kappa M ⊆ tau1 M ∪ tau3 M :=
  fun _ hp => hp.2.1

/-- Every prime in `κ(M)` is prime (recorded explicitly in the definition). -/
theorem prime_of_mem_kappa {M : Subgroup G} {p : ℕ} (hp : p ∈ kappa M) : p.Prime := hp.1

/-- `κ(M) ⊆ σ(M)'`: a Hall `κ(M)`-subgroup is a `σ(M)'`-subgroup (since `τ₁, τ₃ ⊆ σ(M)'`).
This lets Proposition 14.2 feed a Hall `κ(M)`-subgroup `K` to `exists_subgroupESetup_with_le`
to obtain an `E`-setup with `K ≤ E`. -/
theorem kappa_subset_sigmaCompl {M : Subgroup G} : kappa M ⊆ (OddOrder.BG.Ch3.S10.sigma M)ᶜ := by
  intro p hp
  rcases kappa_subset_tau1_union_tau3 hp with h | h
  · exact ((mem_tau1_iff M p).mp h).1
  · exact ((mem_tau3_iff M p).mp h).1

/-- `κ(M) ⊆ π(M) ∖ σ(M)` (`sigmaComplementPrimes M`): a `κ`-prime divides `|M|` (it carries a
rank-one elementary abelian witness `P ≤ M` of order `p`) and lies outside `σ(M)`
(`kappa_subset_sigmaCompl`). -/
theorem kappa_subset_sigmaComplementPrimes [Finite G] {M : Subgroup G} :
    kappa M ⊆ sigmaComplementPrimes M := by
  intro p hpκ
  have hpsig : p ∈ (OddOrder.BG.Ch3.S10.sigma M)ᶜ := kappa_subset_sigmaCompl hpκ
  obtain ⟨hpp, _, P, hPelem, hPM, _⟩ := hpκ
  have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
  exact ⟨Nat.mem_primeFactors.mpr ⟨hpp, hPcard ▸ Subgroup.card_dvd_of_le hPM, Nat.card_pos.ne'⟩,
    hpsig⟩

/-- In a §12 `E`-setup, if the `σ(M)'`-complement `E` is a `κ(M)`-group (every prime divisor of
`|E|` lies in `κ(M)`), then `M` is type-`P₁`: `κ(M) = π(M) ∖ σ(M)`.  `E` is a `σ(M)'`-Hall, so it
carries every `σ(M)'`-prime of `M`; combined with `κ(M) ⊆ π(M) ∖ σ(M)` this forces equality.
Used to exclude the degenerate cases (`κ(M) ∩ τ₃(M) ≠ ∅`, or `E₂E₃ = 1`) when building the
matched `κ`-complement of a type-`P₂` maximal subgroup. -/
theorem kappa_eq_sigmaComplementPrimes_of_isPiGroup_card_E [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : OddOrder.BG.Ch3.S12.SubgroupESetup M E E₁ E₂ E₃)
    (hEκ : ∀ p ∈ (Nat.card ↥E).primeFactors, p ∈ kappa M) :
    kappa M = sigmaComplementPrimes M := by
  refine le_antisymm kappa_subset_sigmaComplementPrimes (fun p hp => ?_)
  obtain ⟨hpπ, hpσ⟩ := hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpπ
  have hpM : p ∣ Nat.card ↥M := Nat.dvd_of_mem_primeFactors hpπ
  -- `p ∤ |M_σ|` (`M_σ` is a `σ(M)`-group and `p ∉ σ(M)`).
  have hpMσ : ¬ p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hd =>
    hpσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p
      (Nat.mem_primeFactors.mpr ⟨hpp, hd, Nat.card_pos.ne'⟩))
  -- `p ∣ |E|` from `|M_σ| · |E| = |M|`.
  have hcardM := h.card_Msigma_mul_card_E
  have hpE : p ∣ Nat.card ↥E :=
    (hpp.dvd_mul.mp (hcardM ▸ hpM)).resolve_left hpMσ
  exact hEκ p (Nat.mem_primeFactors.mpr ⟨hpp, hpE, Nat.card_pos.ne'⟩)

/-- **`M`-conjugacy invariance of the `κ`-witness condition**: for `m ∈ M`, since `M_σ ◁ M`,
conjugation by `m` carries `M_σ ⊓ C_G(P)` to `M_σ ⊓ C_G(P^m)`, so `C_{M_σ}(P) ≠ 1` implies
`C_{M_σ}(P^m) ≠ 1`.  Used in Proposition 14.2 to transport the `κ(M)`-witness across
`M`-conjugacy (the `∃ → ∀` upgrade of BG L3807 and the WLOG `K = E₁`). -/
theorem Msigma_inf_centralizer_conj_ne_bot {M P : Subgroup G} {m : G} (hmM : m ∈ M)
    (h : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((MulAut.conj m • P : Subgroup G) : Set G) ≠ ⊥ := by
  have hmN : m ∈ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
    le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M hmM
  obtain ⟨⟨x, hxmem⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  rw [Subgroup.mem_inf] at hxmem
  obtain ⟨hxMσ, hxC⟩ := hxmem
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨m * x * m⁻¹, Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_normalizer_iff.mp hmN x).mp hxMσ, ?_⟩⟩, ?_⟩
  · -- `m x m⁻¹` centralizes `P^m`: write `y ∈ P^m` as `y = m (m⁻¹ y m) m⁻¹` with `m⁻¹ y m ∈ P`,
    -- which `x` centralizes.
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    have hyval : (MulAut.conj m)⁻¹ • y = m⁻¹ * y * m := by
      rw [inv_smul_eq_iff]
      show y = MulAut.conj m (m⁻¹ * y * m)
      rw [MulAut.conj_apply]; group
    rw [hyval] at hy
    have hcomm : (m⁻¹ * y * m) * x = x * (m⁻¹ * y * m) :=
      (Subgroup.mem_centralizer_iff.mp hxC) _ hy
    calc y * (m * x * m⁻¹)
        = m * ((m⁻¹ * y * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * y * m)) * m⁻¹ := by rw [hcomm]
      _ = (m * x * m⁻¹) * y := by group
  · -- `m x m⁻¹ ≠ 1` since `x ≠ 1`.
    intro hc
    apply hx1
    have hxe : m * x * m⁻¹ = 1 := by simpa using congrArg Subtype.val hc
    refine Subtype.ext ?_
    have hconj : m * x * m⁻¹ = m * 1 * m⁻¹ := by rw [hxe]; group
    exact mul_left_cancel (mul_right_cancel hconj)

open OddOrder.BG.Ch3.S13 in
/-- In a §12 `E`-setup, a prime `p ∈ κ(M) ∩ τ₃(M)` forces `E₃ ≠ 1` and makes `E₃` act
non-regularly on `M_σ`: the `κ`-witness `P ∈ ℰ_p¹(M)` (with `C_{M_σ}(P) ≠ 1`) is `M`-conjugate
into the Hall `τ₃`-piece `E₃` (`exists_conj_smul_le_hallPiece`), and `M_σ`-centralizer
nontriviality transports along the conjugacy (`Msigma_inf_centralizer_conj_ne_bot`).  This is
the entry to BG Proposition 14.2's `κ ∩ τ₃ ≠ ∅` case (which then invokes Corollary 13.11). -/
theorem E3_not_regular_of_mem_kappa_tau3 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} (hp : p.Prime) (hpκ : p ∈ kappa M) (hpτ3 : p ∈ tau3 M) :
    E₃ ≠ ⊥ ∧ ¬ ActsRegularlyOn (OddOrder.BG.Ch3.S10.Msigma M) E₃ := by
  obtain ⟨_, _, P, hPelem, hPM, hPC⟩ := hpκ
  haveI : Fact p.Prime := ⟨hp⟩
  have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
  have hPpi : Ch03.Subgroup.IsPiGroup (tau3 M) (P.subgroupOf M) := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, hPcard,
      hp.primeFactors, Finset.mem_singleton] at hq
    exact hq ▸ hpτ3
  have hπσ : tau3 M ⊆ (OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    fun q hq => ((mem_tau3_iff M q).mp hq).1
  obtain ⟨w, hwM, hwle⟩ :=
    exists_conj_smul_le_hallPiece hG h h.E₃_le h.E₃_hall hπσ hPM hPpi
  have hPwC : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((MulAut.conj w • P : Subgroup G) : Set G) ≠ ⊥ :=
    Msigma_inf_centralizer_conj_ne_bot hwM hPC
  have hPwne : (MulAut.conj w • P : Subgroup G) ≠ ⊥ :=
    ne_bot_of_mem_elemAbelianOfRank_one (conj_smul_mem_elemAbelianOfRank w hPelem)
  obtain ⟨⟨z, hzPw⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPwne
  have hz1' : z ≠ 1 := fun hc => hz1 (Subtype.ext hc)
  have hzE3 : z ∈ E₃ := hwle hzPw
  refine ⟨fun hE3bot => hz1' (Subgroup.mem_bot.mp (hE3bot ▸ hzE3)), ?_⟩
  intro hreg
  have hzfix := hreg z hzE3 hz1'
  rw [fixedByElement] at hzfix
  apply hPwC
  rw [eq_bot_iff, ← hzfix]
  refine inf_le_inf_left _ ?_
  intro a ha
  rw [Subgroup.mem_centralizer_iff] at ha ⊢
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  exact ha z hzPw

/-- **BG Proposition 14.2's `κ(M) ⊆ τ₁(M)` case entry** (mirror of `E3_not_regular_of_mem_kappa_tau3`):
a prime `p ∈ κ(M) ∩ τ₁(M)` forces `E₁ ≠ 1` and makes `E₁` act non-regularly on `M_σ` (the
`κ`-witness `P ∈ ℰ_p¹(M)` is `M`-conjugate into the Hall `τ₁`-piece `E₁`, transporting
`C_{M_σ}` nontriviality).  Feeds `κ(M) = τ₁(M)` and the `K^* ≠ 1` conjunct of case `τ₁`. -/
theorem E1_not_regular_of_mem_kappa_tau1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} (hp : p.Prime) (hpκ : p ∈ kappa M) (hpτ1 : p ∈ tau1 M) :
    E₁ ≠ ⊥ ∧ ¬ ActsRegularlyOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := by
  obtain ⟨_, _, P, hPelem, hPM, hPC⟩ := hpκ
  haveI : Fact p.Prime := ⟨hp⟩
  have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
  have hPpi : Ch03.Subgroup.IsPiGroup (tau1 M) (P.subgroupOf M) := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, hPcard,
      hp.primeFactors, Finset.mem_singleton] at hq
    exact hq ▸ hpτ1
  have hπσ : tau1 M ⊆ (OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    fun q hq => ((mem_tau1_iff M q).mp hq).1
  obtain ⟨w, hwM, hwle⟩ :=
    exists_conj_smul_le_hallPiece hG h h.E₁_le h.E₁_hall hπσ hPM hPpi
  have hPwC : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((MulAut.conj w • P : Subgroup G) : Set G) ≠ ⊥ :=
    Msigma_inf_centralizer_conj_ne_bot hwM hPC
  have hPwne : (MulAut.conj w • P : Subgroup G) ≠ ⊥ :=
    ne_bot_of_mem_elemAbelianOfRank_one (conj_smul_mem_elemAbelianOfRank w hPelem)
  obtain ⟨⟨z, hzPw⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPwne
  have hz1' : z ≠ 1 := fun hc => hz1 (Subtype.ext hc)
  have hzE1 : z ∈ E₁ := hwle hzPw
  refine ⟨fun hE1bot => hz1' (Subgroup.mem_bot.mp (hE1bot ▸ hzE1)), ?_⟩
  intro hreg
  have hzfix := hreg z hzE1 hz1'
  rw [fixedByElement] at hzfix
  apply hPwC
  rw [eq_bot_iff, ← hzfix]
  refine inf_le_inf_left _ ?_
  intro a ha
  rw [Subgroup.mem_centralizer_iff] at ha ⊢
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  exact ha z hzPw

/-- **Global `M_σ`-fixed point from prime action + a single non-regular point** (BG
Proposition 14.2, `κ(M) ∩ τ₃(M) ≠ ∅` case): if `E` acts in a prime manner on `M_σ` and some
`E₃ ≤ E` does not act regularly (a witness `x ∈ E₃#` has `C_{M_σ}(x) ≠ 1`), then prime action
collapses `C_{M_σ}(x) = C_{M_σ}(E)` for every `x ∈ E#`, so `C_{M_σ}(E) ≠ 1`.

Once `K = E` this is the conjunct `K^* = C_{M_σ}(K) ≠ 1`.  It also drives the `κ(M) ⊇ π(E)`
step of `K = E`: for each prime `p ∣ |E|`, a rank-one `P ≤ E` of order `p` has, by prime
action, `C_{M_σ}(P) = C_{M_σ}(E) ≠ 1`, so `p ∈ κ(M)`. -/
theorem Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular {M E E₃ : Subgroup G}
    (hEprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E) (hE3le : E₃ ≤ E)
    (hreg : ¬ ActsRegularlyOn (OddOrder.BG.Ch3.S10.Msigma M) E₃) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G) ≠ ⊥ := by
  -- A non-regular witness `x ∈ E₃#` with `C_{M_σ}(x) ≠ 1`.
  have hxex : ∃ x ∈ E₃, x ≠ 1 ∧
      fixedByElement (OddOrder.BG.Ch3.S10.Msigma M) x ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hreg fun x hx hx1 => hcon x hx hx1
  obtain ⟨x, hxE3, hx1, hxfix⟩ := hxex
  -- Prime action collapses the `x`-fixed points to the `E`-fixed points.
  have heq := hEprime x (hE3le hxE3) hx1
  rw [← fixedBy_def, ← heq]
  exact hxfix

/-- **Every prime dividing `|E|` lies in `τ₁(M) ∪ τ₃(M)`** in BG Proposition 14.2's
`κ(M) ∩ τ₃(M) ≠ ∅` case (the effective content of `E₂ = ⊥`): a prime `p ∣ |E|` is a
`σ(M)'`-prime with `r_p(M) ≤ 2`.  If `r_p(M) = 2` then `p ∈ τ₂(M)`, and Corollary 12.6
(`elemAb_normal_in_E_of_tau2`, projection on `E₃`) forces `C_{M_σ}(x) = 1` for the `E₃`-witness
`x`, contradicting `hxC`.  Hence `r_p(M) = 1`, so `p ∈ τ₁(M) ∪ τ₃(M)`.

Together with prime action (`C_{M_σ}(P) = C_{M_σ}(E) ≠ 1` for rank-one `P ≤ E`) this gives
`π(E) ⊆ κ(M)`, the key to `K = E` in the `κ ∩ τ₃` case. -/
theorem mem_tau1_union_tau3_of_mem_primeFactors_card_E [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) {x : G} (hxE3 : x ∈ E₃) (hxne : x ≠ 1)
    (hxC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥)
    {p : ℕ} (hp : p ∈ (Nat.card ↥E).primeFactors) : p ∈ tau1 M ∪ tau3 M := by
  obtain ⟨hpp, hpdvdE, -⟩ := Nat.mem_primeFactors.mp hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := h.not_mem_sigma_of_mem_primeFactors hG hp
  have hr2 : pRank ↥M p ≤ 2 := h.pRank_M_le_two hG hp
  -- `p ∣ |M|`, so `r_p(M) ≥ 1`.
  have hpM : p ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hpp, hpdvdE.trans (Subgroup.card_dvd_of_le h.E_le), Nat.card_pos.ne'⟩
  have hr1 : 1 ≤ pRank ↥M p := one_le_pRank_of_mem_primeFactors hpM
  by_cases hr : pRank ↥M p = 2
  · -- `r_p(M) = 2 ⟹ p ∈ τ₂`, which makes `E₃` regular and kills the witness.
    exfalso
    have hpτ2 : p ∈ tau2 M := (mem_tau2_iff M p).mpr ⟨hpσ, hr⟩
    obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hpτ2
    exact hxC ((elemAb_normal_in_E_of_tau2 hG h hpτ2 hA hAE).2.2.2.1 x hxE3 hxne)
  · -- `r_p(M) = 1`: `p ∈ τ₃` if `p ∣ |M'|`, else `p ∈ τ₁`.
    have hr1' : pRank ↥M p = 1 := by omega
    by_cases hd : p ∈ tau3 M
    · exact Or.inr hd
    · refine Or.inl ((mem_tau1_iff M p).mpr ⟨hpσ, ?_, hr1'⟩)
      intro hderiv
      exact hd ((mem_tau3_iff M p).mpr ⟨hpσ, hderiv, hr1'⟩)

/-- **`π(E) ⊆ κ(M)`** in BG Proposition 14.2's `κ(M) ∩ τ₃(M) ≠ ∅` case: every prime `p ∣ |E|`
lies in `κ(M)`.  By `mem_tau1_union_tau3_of_mem_primeFactors_card_E`, `p ∈ τ₁(M) ∪ τ₃(M)`; and a
rank-one `P = ⟨g⟩ ≤ E` of order `p` (Cauchy) has `C_{M_σ}(P) = C_{M_σ}(g) = C_{M_σ}(E) ≠ 1` by
prime action (using the `E₃`-witness `x`), so `P` certifies `p ∈ κ(M)`.

This is the `K = E` step: with `π(E) ⊆ κ(M)` and the complement index `[M:E] = |M_σ|` coprime to
`κ(M)`, `E` is a Hall `κ(M)`-subgroup of `M`, hence equals the Hall `κ(M)`-subgroup `K ≤ E`. -/
theorem mem_kappa_of_mem_primeFactors_card_E [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃)
    (hEprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E)
    {x : G} (hxE3 : x ∈ E₃) (hxne : x ≠ 1)
    (hxC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥)
    {p : ℕ} (hp : p ∈ (Nat.card ↥E).primeFactors) : p ∈ kappa M := by
  obtain ⟨hpp, hpdvdE, -⟩ := Nat.mem_primeFactors.mp hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hτ13 : p ∈ tau1 M ∪ tau3 M :=
    mem_tau1_union_tau3_of_mem_primeFactors_card_E hG h hxE3 hxne hxC hp
  -- `C_{M_σ}(E) ≠ 1` from the witness `x` and prime action.
  have hCE : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G) ≠ ⊥ := by
    have heqx := hEprime x (h.E₃_le hxE3) hxne
    rw [← fixedBy_def, ← heqx]; exact hxC
  -- A rank-one `P = ⟨g⟩ ≤ E` of order `p`.
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpdvdE
  have hgE : (g : G) ∈ E := g.2
  have hgord : orderOf (g : G) = p :=
    (orderOf_injective E.subtype E.subtype_injective g).trans hg
  have hgne : (g : G) ≠ 1 := by
    intro hc; rw [hc, orderOf_one] at hgord; exact hpp.ne_one hgord.symm
  have hPcard : Nat.card ↥(Subgroup.zpowers (g : G)) = p := by
    rw [Nat.card_zpowers]; exact hgord
  have hPelem : Subgroup.zpowers (g : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
  have hPM : Subgroup.zpowers (g : G) ≤ M := Subgroup.zpowers_le.mpr (h.E_le hgE)
  -- `C_{M_σ}(⟨g⟩) = C_{M_σ}(g) = C_{M_σ}(E) ≠ 1`.
  have heqg := hEprime (g : G) hgE hgne
  have hCle : Subgroup.centralizer ({(g : G)} : Set G) ≤
      Subgroup.centralizer (↑(Subgroup.zpowers (g : G)) : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Commute.zpow_left (hy (g : G) (Set.mem_singleton _)) n
  have hPC : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer (↑(Subgroup.zpowers (g : G)) : Set G) ≠ ⊥ := by
    have hne : OddOrder.BG.Ch3.S10.Msigma M ⊓
        Subgroup.centralizer ({(g : G)} : Set G) ≠ ⊥ := by
      rw [← fixedByElement_def, heqg, fixedBy_def]; exact hCE
    exact fun hbot => hne (le_bot_iff.mp ((inf_le_inf_left _ hCle).trans hbot.le))
  exact ⟨hpp, hτ13, Subgroup.zpowers (g : G), hPelem, hPM, hPC⟩

/-- **`π(E₁) ⊆ κ(M)`** in BG Proposition 14.2's `κ(M) ⊆ τ₁(M)` case: every prime `p ∣ |E₁|` lies
in `κ(M)`.  `p ∈ τ₁(M)` (as `E₁` is Hall `τ₁(M)` of `E`), and a rank-one `P = ⟨g⟩ ≤ E₁` of order
`p` has `C_{M_σ}(P) = C_{M_σ}(E₁) ≠ 1` by prime action (`hE1prime`) plus `C_{M_σ}(E₁) ≠ 1`
(`hCE1`, from `E1_not_regular`).  So `E₁` is a `κ(M)`-subgroup; with `[M:E₁]` coprime to `κ(M)`
this makes `E₁` a Hall `κ(M)`-subgroup, conjugate to `K` (the entry to WLOG `K = E₁`). -/
theorem mem_kappa_of_mem_primeFactors_card_E1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃)
    (hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁)
    (hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    {p : ℕ} (hp : p ∈ (Nat.card ↥E₁).primeFactors) : p ∈ kappa M := by
  obtain ⟨hpp, hpdvdE1, -⟩ := Nat.mem_primeFactors.mp hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpτ1 : p ∈ tau1 M := h.E₁_hall.1 p (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv]; exact hp)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpdvdE1
  have hgE1 : (g : G) ∈ E₁ := g.2
  have hgord : orderOf (g : G) = p :=
    (orderOf_injective E₁.subtype E₁.subtype_injective g).trans hg
  have hgne : (g : G) ≠ 1 := by
    intro hc; rw [hc, orderOf_one] at hgord; exact hpp.ne_one hgord.symm
  have hPcard : Nat.card ↥(Subgroup.zpowers (g : G)) = p := by
    rw [Nat.card_zpowers]; exact hgord
  have hPelem : Subgroup.zpowers (g : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
  have hPM : Subgroup.zpowers (g : G) ≤ M :=
    Subgroup.zpowers_le.mpr ((h.E₁_le.trans h.E_le) hgE1)
  have heqg := hE1prime (g : G) hgE1 hgne
  have hCle : Subgroup.centralizer ({(g : G)} : Set G) ≤
      Subgroup.centralizer (↑(Subgroup.zpowers (g : G)) : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Commute.zpow_left (hy (g : G) (Set.mem_singleton _)) n
  have hPC : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer (↑(Subgroup.zpowers (g : G)) : Set G) ≠ ⊥ := by
    have hne : OddOrder.BG.Ch3.S10.Msigma M ⊓
        Subgroup.centralizer ({(g : G)} : Set G) ≠ ⊥ := by
      rw [← fixedByElement_def, heqg, fixedBy_def]; exact hCE1
    exact fun hbot => hne (le_bot_iff.mp ((inf_le_inf_left _ hCle).trans hbot.le))
  exact ⟨hpp, Or.inl hpτ1, Subgroup.zpowers (g : G), hPelem, hPM, hPC⟩

/-- **BG Proposition 14.2(c)** for the `κ(M) ∩ τ₃(M) ≠ ∅` case: if `X ∈ ℰ_q¹(G)` lies in
`K^* = C_{M_σ}(E)` (i.e. `X ≤ M_σ ⊓ C(E)`), then `𝓜(C_G(X)) = {M}`.  Here `q ∣ |M_σ|` forces
`q ∈ σ(M)`, and `X ≤ M_σ ⊓ C(E₁)` (since `E₁ ≤ E`), so Lemma 13.6
(`maximalContaining_eq_singleton_of_E1`) applies with `P = E₁` and a Sylow `q`-subgroup of `M_σ`.
With `K = E` this is the `𝓜(C_G(X)) = {M}` half of (c); it drives conjunct (d)
(`K^* ∩ M^g = 1` for `g ∉ M`). -/
theorem maximalContaining_centralizer_of_le_Msigma_centralizer_E [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    {X : Subgroup G} {q : ℕ} [Fact q.Prime] (hX : X ∈ elemAbelianOfRank G q 1)
    (hXK : X ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G)) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  have hXMσ : X ≤ OddOrder.BG.Ch3.S10.Msigma M := hXK.trans inf_le_left
  have hXcard : Nat.card ↥X = q := by rw [(mem_elemAbelianOfRank.mp hX).2, pow_one]
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
  have hXC : X ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) :=
    le_inf hXMσ ((hXK.trans inf_le_right).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h.E₁_le)))
  obtain ⟨S, hSMσ, hSq, _, hScard⟩ := exists_einvariant_sylow_Msigma hG h q
  have hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T →
      S = T := fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
  exact (maximalContaining_eq_singleton_of_E1 hG h hqσ (le_refl E₁) hE1ne hX hXC hSMσ hSq hSmax).1

/-- **BG Proposition 14.2(c)**, `C(E₁)` form (for case `κ ⊆ τ₁`, where `K^* = C_{M_σ}(K) = C_{M_σ}(E₁)`
after the WLOG `K = E₁`): if `X ∈ ℰ_q¹(G)` lies in `M_σ ⊓ C(E₁)`, then `𝓜(C_G(X)) = {M}`.  Same as
`maximalContaining_centralizer_of_le_Msigma_centralizer_E` but takes `X ≤ M_σ ⊓ C(E₁)` directly
(Lemma 13.6 with `P = E₁`). -/
theorem maximalContaining_centralizer_of_le_Msigma_centralizer_E1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    {X : Subgroup G} {q : ℕ} [Fact q.Prime] (hX : X ∈ elemAbelianOfRank G q 1)
    (hXC : X ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G)) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  have hXMσ : X ≤ OddOrder.BG.Ch3.S10.Msigma M := hXC.trans inf_le_left
  have hXcard : Nat.card ↥X = q := by rw [(mem_elemAbelianOfRank.mp hX).2, pow_one]
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
  obtain ⟨S, hSMσ, hSq, _, hScard⟩ := exists_einvariant_sylow_Msigma hG h q
  have hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T →
      S = T := fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
  exact (maximalContaining_eq_singleton_of_E1 hG h hqσ (le_refl E₁) hE1ne hX hXC hSMσ hSq hSmax).1

/-! ### Proposition 14.2(b1), case `κ(M) ⊆ τ₁(M)`: the Frobenius normalizer argument

In this case `K = E₁` (after the WLOG), and `E = E₁ ⋉ (E₂E₃)` is a Frobenius group: `E₁` acts
regularly (fixed-point-freely) on `U = E₂E₃` (BG mmd L3840, "by Lemma 13.12 and Lemma 13.7").
The regular action gives `N_E(X) ≤ E₁` for `X ∈ ℰ¹(E₁)`, which powers conjunct (b1). -/

/-- **BG Prop 14.2(a), case `κ ⊆ τ₁`, `E₃`-half** (mmd L3840, "by Lemma 13.7"): if `κ(M) ∩ τ₃(M)`
is empty (`κ ⊆ τ₁`) then `E₁` acts regularly on `E₃` (i.e. `C_{E₃}(g) = 1` for `g ∈ E₁#`).
Otherwise Lemma 13.7 makes `E₁E₃` act in a prime manner on `M_σ`, and since
`C_{M_σ}(E₁) = K^* ≠ 1`, prime action gives `C_{M_σ}(x) ≠ 1` for every `x ∈ E₃#`, producing a
prime of `κ(M) ∩ τ₃(M)` — a contradiction. -/
theorem actsRegularlyOn_E3_E1_of_kappa_inf_tau3_empty [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty) :
    ActsRegularlyOn E₃ E₁ := by
  classical
  by_contra hreg
  have hE3ne : E₃ ≠ ⊥ := fun hb => hreg (hb ▸ actsRegularlyOn_bot_left E₁)
  -- Lemma 13.7: `E₁E₃` acts in a prime manner on `M_σ`.
  have hprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) (E₁ ⊔ E₃) :=
    E1E3_actsPrime hG h hE1ne hreg
  -- `C_{M_σ}(E₁ ⊔ E₃) = C_{M_σ}(E₁) = K^* ≠ ⊥`.
  have hfix : fixedBy (OddOrder.BG.Ch3.S10.Msigma M) (E₁ ⊔ E₃)
      = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) :=
    (fixedBy_eq_of_le_of_ne_bot hprime le_sup_left hE1ne).symm
  -- A witness `x ∈ E₃#` then has `C_{M_σ}(x) = C_{M_σ}(E₁ ⊔ E₃) ≠ ⊥`.
  obtain ⟨⟨x, hxE3⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE3ne
  have hx1' : x ≠ 1 := fun hc => hx1 (Subtype.ext hc)
  have hxC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    have hpx := hprime x (Subgroup.mem_sup_right hxE3) hx1'
    rw [fixedByElement_def] at hpx
    rw [hpx, hfix]; exact hKstar
  -- Build a `κ(M) ∩ τ₃(M)` witness: a rank-one `R ≤ ⟨x⟩ ≤ E₃` of prime order `r ∈ τ₃(M)`.
  refine hτ3 ?_
  have hxM : x ∈ M := h.E3_le_M hxE3
  have hxzpM : Subgroup.zpowers x ≤ E₃ := Subgroup.zpowers_le.mpr hxE3
  obtain ⟨r, hr, hrdvd⟩ :=
    (orderOf x).exists_prime_and_dvd (by rwa [Ne, orderOf_eq_one_iff])
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers x)) r
    (by rw [Nat.card_zpowers]; exact hrdvd)
  -- `R = ⟨z⟩`, with `z ∈ ⟨x⟩ ≤ E₃`, of order `r`.
  have hzx : (z : G) ∈ Subgroup.zpowers x := z.2
  have hRcard : Nat.card ↥(Subgroup.zpowers (z : G)) = r := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective (Subgroup.zpowers x).subtype (Subgroup.zpowers x).subtype_injective z).trans hz
  have hRelem : Subgroup.zpowers (z : G) ∈ elemAbelianOfRank G r 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hRcard, by rw [hRcard, pow_one]⟩
  have hRE3 : Subgroup.zpowers (z : G) ≤ E₃ := (Subgroup.zpowers_le.mpr (hxzpM hzx))
  have hRM : Subgroup.zpowers (z : G) ≤ M := hRE3.trans (h.E3_le_M)
  -- `r ∈ τ₃(M)` (it divides `|E₃|`).
  have hrE3 : r ∈ (Nat.card ↥E₃).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hr, hRcard ▸ Subgroup.card_dvd_of_le hRE3, Nat.card_pos.ne'⟩
  have hrτ3 : r ∈ tau3 M := by
    have hc3 : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
    exact h.E₃_hall.1 r (hc3 ▸ hrE3)
  -- `C_{M_σ}(R) ⊇ C_{M_σ}(x) ≠ ⊥` (`z ∈ ⟨x⟩`, so centralizing `x` centralizes `⟨z⟩`).
  have hCle : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers (z : G) : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff] at ha ⊢
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hy
    obtain ⟨j, rfl⟩ := hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzx
    have hxa : Commute x a := ha x rfl
    rw [← hm]
    exact ((hxa.zpow_left m).zpow_left j).eq
  have hRC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (z : G) : Subgroup G) : Set G) ≠ ⊥ :=
    fun hb => hxC (le_bot_iff.mp (hb ▸ inf_le_inf_left _ hCle))
  exact ⟨r, ⟨hr, Or.inr hrτ3, Subgroup.zpowers (z : G), hRelem, hRM, hRC⟩, hrτ3⟩

/-- `pRank` is preserved on passing to a subgroup of index coprime to `p` (the `p`-part of the
order is unchanged).  (Replicated here from the `private` copy in `S12_Corollary1216`.) -/
theorem pRank_eq_of_le_of_not_dvd_index [Finite G] {p : ℕ} [Fact p.Prime]
    {H K : Subgroup G} (hHK : H ≤ K) (hidx : ¬ p ∣ (H.subgroupOf K).index) :
    pRank ↥H p = pRank ↥K p := by
  obtain ⟨R⟩ : Nonempty (Sylow p ↥H) := inferInstance
  set Rincl : Subgroup ↥K := (R : Subgroup ↥H).map (Subgroup.inclusion hHK) with hRincl
  have hcardRincl : Nat.card ↥Rincl = p ^ (Nat.card ↥K).factorization p := by
    have hidxcard : Nat.card ↥H * (H.subgroupOf K).index = Nat.card ↥K := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
      exact (H.subgroupOf K).card_mul_index
    have hidx_ne : (H.subgroupOf K).index ≠ 0 := by
      intro hh; rw [hh, mul_zero] at hidxcard; exact (Nat.card_pos).ne' hidxcard.symm
    have hfact : (Nat.card ↥K).factorization p = (Nat.card ↥H).factorization p := by
      rw [← hidxcard, Nat.factorization_mul (Nat.card_pos).ne' hidx_ne, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
    rw [hRincl, Subgroup.card_map_of_injective (Subgroup.inclusion_injective hHK),
      R.card_eq_multiplicity, hfact]
  have eR : ↥(R : Subgroup ↥H) ≃* ↥Rincl :=
    hRincl ▸ Subgroup.equivMapOfInjective _ (Subgroup.inclusion hHK)
      (Subgroup.inclusion_injective hHK)
  have hSylK : pRank ↥Rincl p = pRank ↥K p := by
    have hh := pRank_sylow_eq (Sylow.ofCard Rincl hcardRincl)
    rwa [Sylow.coe_ofCard] at hh
  rw [← pRank_sylow_eq R, ← hSylK]
  exact le_antisymm (pRank_le_of_injective (f := eR.toMonoidHom) eR.injective)
    (pRank_le_of_injective (f := eR.symm.toMonoidHom) eR.symm.injective)

/-- For `q ∈ τ₂(M)` and a `q`-element `y' ∈ E₂#`, the `q`-torsion `Ω₁(E₂)` is a rank-two
elementary abelian `q`-subgroup of `E` containing `y'`.  (`E₂` is abelian by Corollary 12.10(b),
and `r_q(E₂) = r_q(E) = r_q(M) = 2` since the index steps `E₂ ≤ E ≤ M` are `q`-coprime.) -/
theorem exists_elemAb_rank_two_le_E_mem_of_tau2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) {q : ℕ} [Fact q.Prime] (hq : q ∈ tau2 M)
    {y' : G} (hy'E2 : y' ∈ E₂) (hy'q : y' ^ q = 1) (hy'1 : y' ≠ 1) :
    ∃ A ∈ elemAbelianOfRank G q 2, A ≤ E ∧ y' ∈ A := by
  classical
  have hE2comm : IsMulCommutative ↥E₂ := (nilpotent_sigmaComplement_abelian hG h).2.1.1
  have hcomm : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE2comm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set A : Subgroup G := omega1OfAbelian G E₂ q hcomm with hAdef
  have hAelem : A.IsElementaryAbelian q := omega1OfAbelian_isElementaryAbelian
  have hAE2 : A ≤ E₂ := omega1OfAbelian_le
  have hAE : A ≤ E := hAE2.trans h.E₂_le
  have hy'A : y' ∈ A := (mem_omega1OfAbelian).mpr ⟨hy'E2, hy'q⟩
  -- `r_q(E₂) = 2`: two `q`-coprime index steps `E₂ ≤ E ≤ M`, then `r_q(M) = 2`.
  have hpRankE2 : pRank ↥E₂ q = 2 := by
    have hr1 : pRank ↥E₂ q = pRank ↥E q :=
      pRank_eq_of_le_of_not_dvd_index h.E₂_le (fun hdvd =>
        h.E₂_hall.index_no_pi q (Nat.mem_primeFactors.mpr
          ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hq)
    have hr2 : pRank ↥E q = pRank ↥M q := by
      refine pRank_eq_of_le_of_not_dvd_index h.E_le (fun hdvd => ?_)
      have hqσ : q ∉ OddOrder.BG.Ch3.S10.sigma M := tau2_subset_sigma_compl M hq
      have hidxeq : (E.subgroupOf M).index = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
        rw [h.isComplement'_subgroupOf.index_eq_card,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
      rw [hidxeq] at hdvd
      exact hqσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
    rw [hr1, hr2, tau2_pRank_eq_two hq]
  -- `|A| = q²` from `q² ∣ |A|` (rank ≥ 2) and `log_q |A| ≤ r_q(E₂) = 2`.
  have hAcard : Nat.card ↥A = q ^ 2 := by
    have hdvd : q ^ 2 ∣ Nat.card ↥A :=
      hAdef ▸ pow_dvd_card_omega1OfAbelian_of_pos_le_pRank (by norm_num) hpRankE2.ge
    have hlog_le : Nat.log q (Nat.card ↥A) ≤ 2 := by
      have hAsub : (A.subgroupOf E₂).IsElementaryAbelian q :=
        IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAE2).symm hAelem
      have hcardeq : Nat.card ↥(A.subgroupOf E₂) = Nat.card ↥A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE2).toEquiv
      have hle := le_pRank (A.subgroupOf E₂) hAsub
      rwa [hcardeq, hpRankE2] at hle
    have hcardpow : Nat.card ↥A = q ^ Nat.log q (Nat.card ↥A) := by
      rw [hAelem.log_card_eq_finrank, hAelem.card_eq_pow_finrank]
    have h2le : 2 ≤ Nat.log q (Nat.card ↥A) := by
      rw [hcardpow] at hdvd
      exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : q.Prime).one_lt).mp hdvd
    rw [hcardpow]; congr 1; omega
  exact ⟨A, ⟨hAelem, hAcard⟩, hAE, hy'A⟩

/-- **BG Prop 14.2(a), case `κ ⊆ τ₁`, `E₂`-half** (mmd L3840, "by Lemma 13.12"): if
`C_{M_σ}(E₁) = K^* ≠ 1` (i.e. `M` is type `P` in the `κ ⊆ τ₁` case) then `E₁` acts regularly on
`E₂`.  If some `g ∈ E₁#` centralized `y' ∈ E₂#` (of prime order `q ∈ τ₂(M)`), the rank-two
`A = Ω₁(E₂) ∋ y'` would give `C_A(⟨g₀⟩) ≠ 1`, so Lemma 13.12 forces `C_{M_σ}(⟨g₀⟩) = 1`,
contradicting `C_{M_σ}(⟨g₀⟩) = C_{M_σ}(E₁) = K^* ≠ 1` (prime action). -/
theorem actsRegularlyOn_E2_E1_of_actsPrime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥) :
    ActsRegularlyOn E₂ E₁ := by
  classical
  have hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := E1_actsPrime hG h hE1ne
  intro g hgE1 hg1
  rw [fixedByElement_def]
  by_contra hne
  -- A witness `y ∈ E₂#` centralizing `g`.
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hyE2 : y ∈ E₂ := hy.1
  have hyCg : y ∈ Subgroup.centralizer ({g} : Set G) := hy.2
  have hy1' : y ≠ 1 := fun hc => hy1 (Subtype.ext hc)
  -- `g₀ ∈ ⟨g⟩` of prime order `p ∈ τ₁(M)`, `P = ⟨g₀⟩`.
  obtain ⟨p, hp, hpdvd⟩ :=
    (orderOf g).exists_prime_and_dvd (by rwa [Ne, orderOf_eq_one_iff])
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g₀, hg₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers g)) p
    (by rw [Nat.card_zpowers]; exact hpdvd)
  have hg₀g : (g₀ : G) ∈ Subgroup.zpowers g := g₀.2
  have hgE1' : Subgroup.zpowers g ≤ E₁ := Subgroup.zpowers_le.mpr hgE1
  have hg₀E1 : (g₀ : G) ∈ E₁ := hgE1' hg₀g
  have hPcard : Nat.card ↥(Subgroup.zpowers (g₀ : G)) = p := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective (Subgroup.zpowers g).subtype (Subgroup.zpowers g).subtype_injective g₀).trans hg₀
  have hPelem : Subgroup.zpowers (g₀ : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
  have hPbot : Subgroup.zpowers (g₀ : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hPelem
  have hPE1 : Subgroup.zpowers (g₀ : G) ≤ E₁ := Subgroup.zpowers_le.mpr hg₀E1
  have hPE : Subgroup.zpowers (g₀ : G) ≤ E := hPE1.trans h.E₁_le
  -- `p ∈ τ₁(M)`.
  have hpτ1 : p ∈ tau1 M := by
    have hc1 : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
    refine h.E₁_hall.1 p (hc1 ▸ Nat.mem_primeFactors.mpr ⟨hp, ?_, Nat.card_pos.ne'⟩)
    exact hPcard ▸ Subgroup.card_dvd_of_le hPE1
  -- `C_{M_σ}(P) = C_{M_σ}(E₁) = K^* ≠ ⊥`.
  have hCP : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((Subgroup.zpowers (g₀ : G) : Subgroup G) : Set G) ≠ ⊥ := by
    have := fixedBy_eq_of_le_of_ne_bot hE1prime hPE1 hPbot
    rw [fixedBy_def, fixedBy_def] at this
    rw [this]; exact hKstar
  -- `y' ∈ ⟨y⟩` of prime order `q ∈ τ₂(M)`.
  obtain ⟨q, hq, hqdvd⟩ :=
    (orderOf y).exists_prime_and_dvd (by rwa [Ne, orderOf_eq_one_iff])
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers y)) q
    (by rw [Nat.card_zpowers]; exact hqdvd)
  have hy'y : (y' : G) ∈ Subgroup.zpowers y := y'.2
  have hyE2' : Subgroup.zpowers y ≤ E₂ := Subgroup.zpowers_le.mpr hyE2
  have hy'E2 : (y' : G) ∈ E₂ := hyE2' hy'y
  have hy'ord : orderOf (y' : G) = q :=
    (orderOf_injective (Subgroup.zpowers y).subtype (Subgroup.zpowers y).subtype_injective y').trans hy'
  have hy'q : (y' : G) ^ q = 1 := by rw [← hy'ord]; exact pow_orderOf_eq_one _
  have hy'1 : (y' : G) ≠ 1 := by
    intro hc; rw [hc, orderOf_one] at hy'ord; exact hq.ne_one hy'ord.symm
  -- `q ∈ τ₂(M)`.
  have hqτ2 : q ∈ tau2 M := by
    have hc2 : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
    have hy'zpE2 : Subgroup.zpowers (y' : G) ≤ E₂ := Subgroup.zpowers_le.mpr hy'E2
    have hqdvdE2 : q ∣ Nat.card ↥E₂ := by
      have h1 : Nat.card ↥(Subgroup.zpowers (y' : G)) = q := by rw [Nat.card_zpowers, hy'ord]
      exact h1 ▸ Subgroup.card_dvd_of_le hy'zpE2
    exact h.E₂_hall.1 q (hc2 ▸ Nat.mem_primeFactors.mpr ⟨hq, hqdvdE2, Nat.card_pos.ne'⟩)
  -- rank-two `A = Ω₁(E₂) ∋ y'`.
  obtain ⟨A, hAmem, hAE, hy'A⟩ := exists_elemAb_rank_two_le_E_mem_of_tau2 hG h hqτ2 hy'E2 hy'q hy'1
  -- `y'` centralizes `g₀` (`y` centralizes `g`; `g₀ ∈ ⟨g⟩`, `y' ∈ ⟨y⟩`).
  have hComm_gy : Commute g y := hyCg g rfl
  have hy'Cg₀ : (y' : G) ∈ Subgroup.centralizer
      ((Subgroup.zpowers (g₀ : G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hw
    obtain ⟨i, rfl⟩ := hw
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hg₀g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'y
    rw [← hj, ← hk]
    exact (((hComm_gy.zpow_left j).zpow_left i).zpow_right k).eq
  have hCAP : A ⊓ Subgroup.centralizer ((Subgroup.zpowers (g₀ : G) : Subgroup G) : Set G) ≠ ⊥ :=
    fun hb => hy'1 (Subgroup.mem_bot.mp (hb ▸ Subgroup.mem_inf.mpr ⟨hy'A, hy'Cg₀⟩))
  -- Lemma 13.12: `C_{M_σ}(P) = ⊥`, contradicting `C_{M_σ}(P) = K^* ≠ ⊥`.
  exact hCP (Msigma_centralizer_eq_bot_of_tau1_tau2 hG h hpτ1 hqτ2 hPelem hPE hAmem hAE hCAP)

/-- **BG Prop 14.2(a), case `κ ⊆ τ₁`: `E₁` acts regularly on `U = E₂E₃`** (mmd L3840,
"acts regularly on `U = E₂E₃`").  Combines the `E₃`- and `E₂`-halves: `E = E₁ ⋉ (E₂E₃)` with
`E₃ ⊴ E` (Lemma 12.1(b)) and `E₁` normalizing `E₂` (Lemma 12.1(e)), so for `g ∈ E₁#` a fixed
`u = u₃u₂ ∈ E₂E₃` has both factors fixed (`E₂ ⊓ E₃ = 1`), forcing `u = 1`. -/
theorem actsRegularlyOn_E23_E1_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty) :
    ActsRegularlyOn (E₂ ⊔ E₃) E₁ := by
  classical
  have hregE3 : ActsRegularlyOn E₃ E₁ :=
    actsRegularlyOn_E3_E1_of_kappa_inf_tau3_empty hG h hE1ne hKstar hτ3
  have hregE2 : ActsRegularlyOn E₂ E₁ :=
    actsRegularlyOn_E2_E1_of_actsPrime hG h hE1ne hKstar
  have hEnormE3 : E ≤ Subgroup.normalizer (E₃ : Set G) := (subgroupE_basic hG h).2.1.2
  have hE12normE2 : E₁ ⊔ E₂ ≤ Subgroup.normalizer (E₂ : Set G) :=
    (subgroupE_basic hG h).2.2.2.2.1.2.2
  -- `E₂ ⊓ E₃ = ⊥` (coprime: `τ₂ ∩ τ₃ = ∅`).
  have hcop23 : Nat.Coprime (Nat.card ↥E₂) (Nat.card ↥E₃) := by
    by_contra hnc
    obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hc2 : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
    have hc3 : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
    have hsτ2 : s ∈ tau2 M := h.E₂_hall.1 s (hc2 ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩)
    have hsτ3 : s ∈ tau3 M := h.E₃_hall.1 s (hc3 ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩)
    have h2 := tau2_pRank_eq_two hsτ2
    have h1 := tau3_pRank_eq_one hsτ3
    omega
  have hE23disj : E₂ ⊓ E₃ = ⊥ := by
    have hd1 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₂ := Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₃ := Subgroup.card_dvd_of_le inf_le_right
    have hc1 : Nat.card ↥(E₂ ⊓ E₃) = 1 := Nat.dvd_one.mp (hcop23 ▸ Nat.dvd_gcd hd1 hd2)
    exact Subgroup.card_eq_one.mp hc1
  haveI hE3normSub : (E₃.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.E₃_le).mpr hEnormE3
  intro g hgE1 hg1
  rw [fixedByElement_def]
  have hgNE2 : g ∈ Subgroup.normalizer (E₂ : Set G) := hE12normE2 (Subgroup.mem_sup_left hgE1)
  have hgNE3 : g ∈ Subgroup.normalizer (E₃ : Set G) := hEnormE3 (h.E₁_le hgE1)
  refine le_antisymm ?_ bot_le
  intro u hu
  rw [Subgroup.mem_inf] at hu
  obtain ⟨huU, huCg⟩ := hu
  -- `gug⁻¹ = u`.
  have hgu : g * u = u * g := huCg g rfl
  -- decompose `u = u₃ * u₂` in `↥E` (`E₃` normal).
  have huE : u ∈ E := (sup_le h.E₂_le h.E₃_le) huU
  have hsupSub : (E₂ ⊔ E₃).subgroupOf E = E₃.subgroupOf E ⊔ E₂.subgroupOf E := by
    rw [Subgroup.subgroupOf_sup h.E₂_le h.E₃_le, sup_comm]
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
    (hsupSub ▸ Subgroup.mem_subgroupOf.mpr huU :
      (⟨u, huE⟩ : ↥E) ∈ E₃.subgroupOf E ⊔ E₂.subgroupOf E)
  have hu3 : (a : G) ∈ E₃ := Subgroup.mem_subgroupOf.mp ha
  have hu2 : (b : G) ∈ E₂ := Subgroup.mem_subgroupOf.mp hb
  have hu32 : (a : G) * (b : G) = u := by have hh := congrArg Subtype.val hab; simpa using hh
  -- `g·u₃·g⁻¹ ∈ E₃`, `g·u₂·g⁻¹ ∈ E₂`.
  have hw3 : g * (a : G) * g⁻¹ ∈ E₃ := (Subgroup.mem_normalizer_iff.mp hgNE3 (a : G)).mp hu3
  have hw2 : g * (b : G) * g⁻¹ ∈ E₂ := (Subgroup.mem_normalizer_iff.mp hgNE2 (b : G)).mp hu2
  -- `(g u₃ g⁻¹)(g u₂ g⁻¹) = u₃ u₂`.
  have hconj : (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹) = (a : G) * (b : G) := by
    have hgug : g * u * g⁻¹ = u := by rw [hgu]; group
    calc (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹)
        = g * ((a : G) * (b : G)) * g⁻¹ := by group
      _ = g * u * g⁻¹ := by rw [hu32]
      _ = u := hgug
      _ = (a : G) * (b : G) := hu32.symm
  -- `c := u₃⁻¹·(g u₃ g⁻¹) = u₂·(g u₂ g⁻¹)⁻¹ ∈ E₂ ⊓ E₃ = 1`.
  set c : G := (a : G)⁻¹ * (g * (a : G) * g⁻¹) with hcdef
  have hcE3 : c ∈ E₃ := E₃.mul_mem (E₃.inv_mem hu3) hw3
  have hcE2 : c = (b : G) * (g * (b : G) * g⁻¹)⁻¹ := by
    have hw3eq : g * (a : G) * g⁻¹ = (a : G) * (b : G) * (g * (b : G) * g⁻¹)⁻¹ := by
      rw [← hconj]; group
    rw [hcdef, hw3eq]; group
  have hcE2' : c ∈ E₂ := hcE2 ▸ E₂.mul_mem hu2 (E₂.inv_mem hw2)
  have hc1 : c = 1 := Subgroup.mem_bot.mp (hE23disj ▸ Subgroup.mem_inf.mpr ⟨hcE2', hcE3⟩)
  -- so `g u₃ g⁻¹ = u₃` and (symmetrically) `g u₂ g⁻¹ = u₂`; both centralized ⟹ in `E_i ⊓ C(g) = ⊥`.
  have hu3fix : g * (a : G) * g⁻¹ = (a : G) := (inv_mul_eq_one.mp (hcdef ▸ hc1)).symm
  have hw2fix : g * (b : G) * g⁻¹ = (b : G) :=
    (mul_inv_eq_one.mp (by rw [← hcE2]; exact hc1)).symm
  have hu3bot : (a : G) = 1 := by
    have hmem : (a : G) ∈ E₃ ⊓ Subgroup.centralizer ({g} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hu3, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy; rw [Set.mem_singleton_iff.mp hy]
      exact (mul_inv_eq_iff_eq_mul.mp hu3fix)
    have hr := hregE3 g hgE1 hg1
    rw [fixedByElement_def] at hr
    exact Subgroup.mem_bot.mp (hr ▸ hmem)
  have hu2bot : (b : G) = 1 := by
    have hmem : (b : G) ∈ E₂ ⊓ Subgroup.centralizer ({g} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hu2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy; rw [Set.mem_singleton_iff.mp hy]
      exact (mul_inv_eq_iff_eq_mul.mp hw2fix)
    have hr := hregE2 g hgE1 hg1
    rw [fixedByElement_def] at hr
    exact Subgroup.mem_bot.mp (hr ▸ hmem)
  rw [Subgroup.mem_bot, ← hu32, hu3bot, hu2bot, mul_one]

/-- **BG Prop 14.2(b1), case `κ ⊆ τ₁`: `N_E(X) ≤ E₁`** for `X ∈ ℰ¹(E₁)` (the Frobenius
normalizer fact).  Writing `e = u·k` (`u ∈ E₂E₃`, `k ∈ E₁`), `E₁` abelian gives `kgk⁻¹ = g`, so
`ugu⁻¹ = ege⁻¹ ∈ X ≤ E₁`; then `[u,g] ∈ E₁ ⊓ E₂E₃ = 1`, so `u` centralizes `g` and lies in
`C_{E₂E₃}(g) = 1` (regular action), forcing `u = 1`, i.e. `e = k ∈ E₁`. -/
theorem normalizer_inf_E_le_E1_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty)
    {X : Subgroup G} {p : ℕ} [Fact p.Prime] (hX : X ∈ elemAbelianOfRank G p 1)
    (hXE1 : X ≤ E₁) :
    Subgroup.normalizer (X : Set G) ⊓ E ≤ E₁ := by
  classical
  have hreg23 : ActsRegularlyOn (E₂ ⊔ E₃) E₁ :=
    actsRegularlyOn_E23_E1_of_caseTau1 hG h hE1ne hKstar hτ3
  have hE1cyc : IsCyclic ↥E₁ := (subgroupE_basic hG h).2.2.2.1.1
  have hEnormE3 : E ≤ Subgroup.normalizer (E₃ : Set G) := (subgroupE_basic hG h).2.1.2
  have hE23norm : E ≤ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) :=
    (subgroupE_basic hG h).2.2.2.2.1.2.1
  have hEsup : E = E₁ ⊔ E₂ ⊔ E₃ := (subgroupE_basic hG h).2.2.2.2.1.1
  letI : CommGroup ↥E₁ := hE1cyc.commGroup
  -- generator `g` of `X`.
  obtain ⟨⟨g, hgX⟩, hg1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (ne_bot_of_mem_elemAbelianOfRank_one hX)
  have hg1' : g ≠ 1 := fun hc => hg1 (Subtype.ext hc)
  have hgE1 : g ∈ E₁ := hXE1 hgX
  -- `E₁ ⊓ (E₂⊔E₃) = ⊥` (coprime `τ₁` vs `τ₂ ∪ τ₃`).
  have hc1E : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
  have hc2E : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
  have hc3E : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
  have hcop2 : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥E₂) := by
    by_contra hnc
    obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have := tau1_pRank_eq_one (h.E₁_hall.1 s (hc1E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
    have := tau2_pRank_eq_two (h.E₂_hall.1 s (hc2E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
    omega
  have hcop3 : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥E₃) := by
    by_contra hnc
    obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    exact not_mem_tau3_of_mem_tau1
      (h.E₁_hall.1 s (hc1E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
      (h.E₃_hall.1 s (hc3E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
  have hE23disj : E₂ ⊓ E₃ = ⊥ := by
    have hd1 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₂ := Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₃ := Subgroup.card_dvd_of_le inf_le_right
    have hcop23 : Nat.Coprime (Nat.card ↥E₂) (Nat.card ↥E₃) := by
      by_contra hnc
      obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      have := tau2_pRank_eq_two (h.E₂_hall.1 s (hc2E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
      have := tau3_pRank_eq_one (h.E₃_hall.1 s (hc3E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
      omega
    exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcop23 ▸ Nat.dvd_gcd hd1 hd2))
  have hcard23 : Nat.card ↥(E₂ ⊔ E₃) = Nat.card ↥E₂ * Nat.card ↥E₃ :=
    card_sup_eq_mul_of_le_normalizer_of_disjoint (h.E₂_le.trans hEnormE3) hE23disj
  have hE1_23_disj : E₁ ⊓ (E₂ ⊔ E₃) = ⊥ := by
    have hd1 : Nat.card ↥(E₁ ⊓ (E₂ ⊔ E₃)) ∣ Nat.card ↥E₁ := Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(E₁ ⊓ (E₂ ⊔ E₃)) ∣ Nat.card ↥(E₂ ⊔ E₃) := Subgroup.card_dvd_of_le inf_le_right
    have hcop : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥(E₂ ⊔ E₃)) :=
      hcard23 ▸ Nat.Coprime.mul_right hcop2 hcop3
    exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2))
  -- the normalizer membership.
  intro e he
  rw [Subgroup.mem_inf] at he
  obtain ⟨heN, heE⟩ := he
  -- decompose `e = u * k`, `u ∈ E₂⊔E₃` (normal), `k ∈ E₁`.
  haveI hUnorm : ((E₂ ⊔ E₃).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le h.E₂_le h.E₃_le)).mpr hE23norm
  have hsuptop : ((E₂ ⊔ E₃).subgroupOf E) ⊔ (E₁.subgroupOf E) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (sup_le h.E₂_le h.E₃_le) h.E₁_le, Subgroup.subgroupOf_eq_top,
      hEsup]
    exact sup_le (sup_le le_sup_right (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)
  obtain ⟨u, hu, k, hk, huk⟩ := Subgroup.mem_sup_of_normal_left.mp
    (hsuptop ▸ Subgroup.mem_top (⟨e, heE⟩ : ↥E))
  have huU : (u : G) ∈ E₂ ⊔ E₃ := Subgroup.mem_subgroupOf.mp hu
  have hkE1 : (k : G) ∈ E₁ := Subgroup.mem_subgroupOf.mp hk
  have huke : (u : G) * (k : G) = e := by have hh := congrArg Subtype.val huk; simpa using hh
  -- `k` commutes with `g` (`E₁` abelian).
  have hkg : (k : G) * g = g * (k : G) :=
    congrArg Subtype.val (mul_comm (⟨(k : G), hkE1⟩ : ↥E₁) (⟨g, hgE1⟩ : ↥E₁))
  -- `e g e⁻¹ = u g u⁻¹ ∈ X ≤ E₁`.
  have hege : e * g * e⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp heN g).mp hgX
  have hugu : (u : G) * g * (u : G)⁻¹ = e * g * e⁻¹ := by
    have hkgk : (k : G) * g * (k : G)⁻¹ = g := by rw [hkg]; group
    rw [← huke]
    calc (u : G) * g * (u : G)⁻¹
        = (u : G) * ((k : G) * g * (k : G)⁻¹) * (u : G)⁻¹ := by rw [hkgk]
      _ = (u : G) * (k : G) * g * ((u : G) * (k : G))⁻¹ := by group
  have huguE1 : (u : G) * g * (u : G)⁻¹ ∈ E₁ := hXE1 (hugu ▸ hege)
  -- `[u,g] ∈ E₁ ⊓ (E₂⊔E₃) = ⊥`.
  have hcommE1 : (u : G) * g * (u : G)⁻¹ * g⁻¹ ∈ E₁ := E₁.mul_mem huguE1 (E₁.inv_mem hgE1)
  have hgU : g ∈ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := hE23norm (h.E₁_le hgE1)
  have hcommU : (u : G) * g * (u : G)⁻¹ * g⁻¹ ∈ E₂ ⊔ E₃ := by
    have h1 : g * (u : G)⁻¹ * g⁻¹ ∈ E₂ ⊔ E₃ :=
      (Subgroup.mem_normalizer_iff.mp hgU (u : G)⁻¹).mp ((E₂ ⊔ E₃).inv_mem huU)
    have heq : (u : G) * g * (u : G)⁻¹ * g⁻¹ = (u : G) * (g * (u : G)⁻¹ * g⁻¹) := by group
    rw [heq]; exact (E₂ ⊔ E₃).mul_mem huU h1
  have hcomm1 : (u : G) * g * (u : G)⁻¹ * g⁻¹ = 1 :=
    Subgroup.mem_bot.mp (hE1_23_disj ▸ Subgroup.mem_inf.mpr ⟨hcommE1, hcommU⟩)
  -- `u ∈ C_{E₂⊔E₃}(g) = ⊥`, so `u = 1` and `e = k ∈ E₁`.
  have hu1 : (u : G) = 1 := by
    have hug : (u : G) * g = g * (u : G) :=
      mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hcomm1)
    have hmem : (u : G) ∈ (E₂ ⊔ E₃) ⊓ Subgroup.centralizer ({g} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨huU, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact hug.symm
    have hr := hreg23 g hgE1 hg1'
    rw [fixedByElement_def] at hr
    exact Subgroup.mem_bot.mp (hr ▸ hmem)
  rw [← huke, hu1, one_mul]; exact hkE1

/-- **The §12 complement `E` is a Frobenius group** in case `τ₁` with `U = E₂E₃ ≠ 1`.
`E₁` acts regularly (fixed-point-freely) on the normal subgroup `U = E₂ ⊔ E₃`
(`actsRegularlyOn_E23_E1_of_caseTau1`), and `E = E₁ ⋉ U` (`SubgroupESetup.eq_sup`), so `E` is a
Frobenius group with kernel `U` and complement `E₁`.  This is the Frobenius structure that
Proposition 14.2(g) feeds to Theorem 3.10(a). -/
theorem isFrobeniusGroup_E_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty)
    (hUne : (E₂ ⊔ E₃ : Subgroup G) ≠ ⊥) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥E
      ((E₂ ⊔ E₃).subgroupOf E) (E₁.subgroupOf E) := by
  classical
  have hreg : ActsRegularlyOn (E₂ ⊔ E₃) E₁ :=
    actsRegularlyOn_E23_E1_of_caseTau1 hG h hE1ne hKstar hτ3
  have hE23le : (E₂ ⊔ E₃ : Subgroup G) ≤ E := sup_le h.E₂_le h.E₃_le
  have hE1le : E₁ ≤ E := h.E₁_le
  have hE23norm : E ≤ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := h.E23_normal hG
  -- `E₁ ⊓ (E₂ ⊔ E₃) = ⊥` (a nonidentity common element would centralize itself, contra FPF).
  have hdisj : E₁ ⊓ (E₂ ⊔ E₃) = ⊥ := by
    refine le_antisymm (fun g hg => ?_) bot_le
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgE1, hgU⟩ := hg
    rw [Subgroup.mem_bot]
    by_contra hg1
    have hr := hreg g hgE1 hg1
    rw [fixedByElement_def, eq_bot_iff] at hr
    refine hg1 (Subgroup.mem_bot.mp (hr ?_))
    exact Subgroup.mem_inf.mpr ⟨hgU, Subgroup.mem_centralizer_iff.mpr
      (fun y hy => by rw [Set.mem_singleton_iff.mp hy])⟩
  -- normality of the kernel.
  haveI hKnorm : ((E₂ ⊔ E₃).subgroupOf E).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hE23norm
  refine ⟨hKnorm, ?_, ?_, ?_, ?_⟩
  · -- complement: disjoint + product covers `↥E`.
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      have hi : (E₂ ⊔ E₃).subgroupOf E ⊓ E₁.subgroupOf E = ((E₂ ⊔ E₃) ⊓ E₁).subgroupOf E := rfl
      rw [hi, inf_comm, hdisj, Subgroup.bot_subgroupOf]
    · haveI := hKnorm
      have hsupG : (E₂ ⊔ E₃) ⊔ E₁ = E := by rw [h.eq_sup hG]; ac_rfl
      have hsup : (E₂ ⊔ E₃).subgroupOf E ⊔ E₁.subgroupOf E = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hE23le hE1le, hsupG, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul ((E₂ ⊔ E₃).subgroupOf E) (E₁.subgroupOf E)
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  · rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hUne (hd.eq_bot_of_le hE23le)
  · rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hE1ne (hd.eq_bot_of_le hE1le)
  · -- Frobenius condition from the fixed-point-free action.
    intro a ha hane n hn hnne
    simp only [Subgroup.mem_subgroupOf] at ha hn
    intro hcontra
    have hval : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      have := congrArg (Subtype.val) hcontra; push_cast at this; exact this
    have hane' : (a : G) ≠ 1 := fun hc => hane (Subtype.ext (by simpa using hc))
    have hnne' : (n : G) ≠ 1 := fun hc => hnne (Subtype.ext (by simpa using hc))
    have hr := hreg (a : G) ha hane'
    rw [fixedByElement_def, eq_bot_iff] at hr
    refine hnne' (Subgroup.mem_bot.mp (hr ?_))
    exact Subgroup.mem_inf.mpr ⟨hn, Subgroup.mem_centralizer_iff.mpr
      (fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact mul_inv_eq_iff_eq_mul.mp hval)⟩

/-- The family `M_P` of type-P maximal subgroups. -/
def maximalTypePFamily (G : Type*) [Group G] : Set (Subgroup G) :=
  {M | M ∈ maximalSubgroups G ∧ IsTypeP M}

/-- The family `M_P1` of type-P1 maximal subgroups. -/
def maximalTypeP1Family (G : Type*) [Group G] : Set (Subgroup G) :=
  {M | M ∈ maximalSubgroups G ∧ IsTypeP1 M}

/-- The family `M_P2` of type-P2 maximal subgroups. -/
def maximalTypeP2Family (G : Type*) [Group G] : Set (Subgroup G) :=
  {M | M ∈ maximalSubgroups G ∧ IsTypeP2 M}

/-- The family `M_F` of Frobenius-type maximal subgroups. -/
def maximalTypeFFamily (G : Type*) [Group G] : Set (Subgroup G) :=
  {M | M ∈ maximalSubgroups G ∧ IsTypeF M}

/-- Family form of the type-`P` partition: `M_P = M_P1 ∪ M_P2`. -/
theorem maximalTypePFamily_eq_union :
    maximalTypePFamily G = maximalTypeP1Family G ∪ maximalTypeP2Family G := by
  ext M
  simp only [maximalTypePFamily, maximalTypeP1Family, maximalTypeP2Family, Set.mem_setOf_eq,
    Set.mem_union]
  constructor
  · rintro ⟨hM, hP⟩
    rcases isTypeP_iff_isTypeP1_or_isTypeP2.mp hP with h | h
    · exact Or.inl ⟨hM, h⟩
    · exact Or.inr ⟨hM, h⟩
  · rintro (⟨hM, h⟩ | ⟨hM, h⟩)
    · exact ⟨hM, isTypeP_of_isTypeP1 h⟩
    · exact ⟨hM, isTypeP_of_isTypeP2 h⟩

/-- Family form: `M_P1` and `M_P2` are disjoint. -/
theorem maximalTypeP1Family_disjoint_typeP2Family :
    Disjoint (maximalTypeP1Family G) (maximalTypeP2Family G) := by
  rw [Set.disjoint_left]
  rintro M ⟨_, h1⟩ ⟨_, h2⟩
  exact not_isTypeP1_and_isTypeP2 ⟨h1, h2⟩

/-- Family form: `M_F` is the complement of `M_P` within the maximal subgroups. -/
theorem maximalTypeFFamily_eq_diff :
    maximalTypeFFamily G = maximalSubgroups G \ maximalTypePFamily G := by
  ext M
  simp only [maximalTypeFFamily, maximalTypePFamily, Set.mem_setOf_eq, Set.mem_sdiff, not_and]
  constructor
  · rintro ⟨hM, hF⟩
    exact ⟨hM, fun _ => isTypeF_iff_not_isTypeP.mp hF⟩
  · rintro ⟨hM, hnP⟩
    exact ⟨hM, isTypeF_iff_not_isTypeP.mpr (hnP hM)⟩

/-- BG `M_sigma(x)`: maximal subgroups whose `M_sigma` contains the element `x`. -/
def maximalSigmaSubgroupsOfElement (x : G) : Set (Subgroup G) :=
  {M | M ∈ maximalSubgroups G ∧ x ∈ OddOrder.BG.Ch3.S10.Msigma M}

/-- The nonidentity part `M_σ^#` of `M_σ` (`= sharpSubgroup M_σ`).

**Naming caveat (2026-06-14):** BG's `M̃` — used in Lemma 14.5(c), Theorem 14.7(e), and the
Corollary 14.9 covering — is the *larger* set `{ x x' | x ∈ M_σ^#, x' ∈ R(x) }`, where `R(x)`
is the normal Hall subgroup of `C_G(x)` from Theorem 14.4 (it adjoins the `ℓ_σ = 2` "twisted"
elements). `R(x)` and hence `M̃` are **not yet formalized** (gated on Theorem 14.4 ⟸ §13), so
this `sigmaSharp` is only the `ℓ_σ = 1` core `M_σ^#`, a strict under-approximation of `M̃`.
Any downstream use (§15/§16, Corollary 14.9) that intends BG's `M̃` must switch to the
eventual `M̃` once `R(x)` is available. See `notes/bg/s14_typeP_counting.md`. -/
def sigmaSharp (M : Subgroup G) : Set G :=
  sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)

/-- The conjugacy saturation `C_G(M_tilde)` used in the counting formulas. -/
def sigmaConjugacySaturation (M : Subgroup G) : Set G :=
  conjClassSet (sigmaSharp M)

/-- Subgroup conjugacy in the ambient group. -/
def IsConjugateSubgroup (M N : Subgroup G) : Prop :=
  ∃ g : G, MulAut.conj g • M = N

/-- Subgroup conjugacy is reflexive (conjugate by `1`). -/
@[refl] theorem IsConjugateSubgroup.refl (M : Subgroup G) : IsConjugateSubgroup M M :=
  ⟨1, by rw [map_one, one_smul]⟩

/-- Subgroup conjugacy is symmetric (conjugate back by `g⁻¹`). -/
theorem IsConjugateSubgroup.symm {M N : Subgroup G} (h : IsConjugateSubgroup M N) :
    IsConjugateSubgroup N M := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, by rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩

/-- Subgroup conjugacy is transitive (compose the conjugators). -/
theorem IsConjugateSubgroup.trans {M N P : Subgroup G} (h₁ : IsConjugateSubgroup M N)
    (h₂ : IsConjugateSubgroup N P) : IsConjugateSubgroup M P := by
  obtain ⟨g, hg⟩ := h₁
  obtain ⟨g', hg'⟩ := h₂
  exact ⟨g' * g, by rw [map_mul, mul_smul, hg, hg']⟩

/-- Subgroup conjugacy is an equivalence relation.  (`¬ IsConjugateSubgroup` hypotheses and the
conjugacy conclusions throughout §14 — Theorem 14.7, Lemma 14.5, Corollary 14.9 — rely on these.) -/
theorem isConjugateSubgroup_equivalence : Equivalence (IsConjugateSubgroup (G := G)) :=
  ⟨IsConjugateSubgroup.refl, IsConjugateSubgroup.symm, IsConjugateSubgroup.trans⟩

/-- A conjugate of a maximal subgroup is maximal: `IsConjugateSubgroup` preserves
`maximalSubgroups`.  The type-`P` conjugacy arguments of Theorem 14.7 and Corollary 14.8 move
maximal subgroups around by conjugation, so they need maximality to be conjugacy-stable. -/
theorem mem_maximalSubgroups_of_isConjugateSubgroup {M N : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (h : IsConjugateSubgroup M N) :
    N ∈ maximalSubgroups G := by
  obtain ⟨g, rfl⟩ := h
  exact mem_maximalSubgroups.mpr
    (OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hM))

/-- `Z_tilde = Z - (K union K*)` in Theorem 14.7. -/
def zTilde (K Kstar : Subgroup G) : Set G :=
  ((K ⊔ Kstar : Subgroup G) : Set G) \ ((K : Set G) ∪ (Kstar : Set G))

/-! ### Genuine `σ`-decomposition of an element (BG §14 opening, Coq `sigma_decomposition`)

Built on the two-block π-part decomposition `OddOrder.GroupTheory.exists_isPiElement_mul`.  These
genuine definitions (`sigmaPart`, `sigmaDecomposition`, `sigmaLength`) construct the carrier that
`SigmaDecompositionData` below only *posits*: `sigmaLength` is an honest `ℕ`-valued function with
`sigmaLength_eq_zero_iff` (Coq `ell_sigma0P`) and `sigmaLength_conj` (conjugation invariance,
Coq `ell_sigmaJ`) proven from the construction, not a free structure field.  This is the upstream
foundation of the `FT_signalizer` (Theorem D(3)/(4)) port (issue 8020, Chunk 1). -/

/-- The `π`-part of a finite-order element `g`, as a *function*: the `π`-element factor of the
unique two-block decomposition `g = (π-part) * (π′-part)` (`exists_isPiElement_mul`, made into a
function via `Classical.choose`).  This is Coq's `g.`_π`. -/
noncomputable def piPart [Finite G] (π : Set ℕ) (g : G) : G :=
  (exists_isPiElement_mul π g).choose

/-- The decomposition behind `piPart`: there is a commuting `π′`-element `b`, a power of `g`, with
`piPart π g * b = g`. -/
theorem piPart_spec [Finite G] (π : Set ℕ) (g : G) :
    ∃ b : G, piPart π g * b = g ∧ Commute (piPart π g) b ∧
      IsPiElement π (piPart π g) ∧ IsPiElement πᶜ b ∧
      piPart π g ∈ Subgroup.zpowers g ∧ b ∈ Subgroup.zpowers g :=
  (exists_isPiElement_mul π g).choose_spec

/-- `piPart π g` is a `π`-element. -/
theorem isPiElement_piPart [Finite G] (π : Set ℕ) (g : G) : IsPiElement π (piPart π g) := by
  obtain ⟨_, _, _, h, _, _, _⟩ := piPart_spec π g; exact h

/-- The identity has trivial `π`-part. -/
theorem piPart_one [Finite G] (π : Set ℕ) : piPart π (1 : G) = 1 := by
  obtain ⟨b, hmul, hcomm, hpiA, hpiB, -, -⟩ := piPart_spec π (1 : G)
  exact (isPiElement_mul_unique hmul hcomm hpiA hpiB (one_mul (1 : G)) (Commute.refl 1)
    (isPiElement_one π) (isPiElement_one πᶜ)).1

/-- If the `π`-part of `g` is trivial, then `g` itself is a `π′`-element. -/
theorem isPiElement_compl_of_piPart_eq_one [Finite G] {π : Set ℕ} {g : G}
    (h : piPart π g = 1) : IsPiElement πᶜ g := by
  obtain ⟨b, hmul, -, -, hpiB, -, -⟩ := piPart_spec π g
  rw [h, one_mul] at hmul
  rwa [hmul] at hpiB

/-- Conjugation preserves the `π`-element property (the conjugate has the same order). -/
theorem isPiElement_conj {π : Set ℕ} (h : G) {a : G} (ha : IsPiElement π a) :
    IsPiElement π (h * a * h⁻¹) := by
  have key : orderOf (h * a * h⁻¹) = orderOf a := by
    have hh := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective a
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hh
  intro p hp
  rw [key] at hp
  exact ha p hp

/-- **The `π`-part is conjugation-equivariant** (`piPart π (h x h⁻¹) = h (piPart π x) h⁻¹`).
Conjugating the unique decomposition `x = (π-part)(π′-part)` gives a decomposition of `h x h⁻¹`;
uniqueness identifies its `π`-part with `h (piPart π x) h⁻¹`. -/
theorem piPart_conj [Finite G] (π : Set ℕ) (h x : G) :
    piPart π (h * x * h⁻¹) = h * piPart π x * h⁻¹ := by
  obtain ⟨bx, hxmul, hxcomm, hxpiA, hxpiB, -, -⟩ := piPart_spec π x
  obtain ⟨b', hmul', hcomm', hpiA', hpiB', -, -⟩ := piPart_spec π (h * x * h⁻¹)
  have hprod : (h * piPart π x * h⁻¹) * (h * bx * h⁻¹) = h * x * h⁻¹ := by
    calc (h * piPart π x * h⁻¹) * (h * bx * h⁻¹)
        = h * (piPart π x * bx) * h⁻¹ := by group
      _ = h * x * h⁻¹ := by rw [hxmul]
  have hBcomm : Commute (h * piPart π x * h⁻¹) (h * bx * h⁻¹) := by
    have hm := hxcomm.map (MulAut.conj h)
    simpa only [MulAut.conj_apply] using hm
  exact (isPiElement_mul_unique hmul' hcomm' hpiA' hpiB' hprod hBcomm
    (isPiElement_conj h hxpiA) (isPiElement_conj h hxpiB)).1

/-- A `π`-element is its own `π`-part. -/
theorem piPart_self_of_isPiElement [Finite G] {π : Set ℕ} {g : G} (hg : IsPiElement π g) :
    piPart π g = g := by
  obtain ⟨b, hmul, hcomm, hpiA, hpiB, -, -⟩ := piPart_spec π g
  exact (isPiElement_mul_unique hmul hcomm hpiA hpiB (mul_one g) (Commute.one_right g)
    hg (isPiElement_one πᶜ)).1

/-- A `π′`-element has trivial `π`-part. -/
theorem piPart_eq_one_of_isPiElement_compl [Finite G] {π : Set ℕ} {g : G}
    (hg : IsPiElement πᶜ g) : piPart π g = 1 := by
  obtain ⟨b, hmul, hcomm, hpiA, hpiB, -, -⟩ := piPart_spec π g
  exact (isPiElement_mul_unique hmul hcomm hpiA hpiB (one_mul g) (Commute.one_left g)
    (isPiElement_one π) hg).1

/-- The `π`-part of `g` is a power of `g`. -/
theorem piPart_mem_zpowers [Finite G] (π : Set ℕ) (g : G) :
    piPart π g ∈ Subgroup.zpowers g := by
  obtain ⟨_, _, _, _, _, hz, _⟩ := piPart_spec π g; exact hz

/-- A prime of `π` dividing `orderOf g` also divides `orderOf (piPart π g)` (it cannot land in the
`π′`-part `b`, whose order is coprime to `π`). -/
theorem prime_dvd_orderOf_piPart [Finite G] {π : Set ℕ} {p : ℕ} (hp : p.Prime) (hpπ : p ∈ π)
    {g : G} (hpg : p ∣ orderOf g) : p ∣ orderOf (piPart π g) := by
  obtain ⟨b, hmul, hcomm, _, hpiB, _, _⟩ := piPart_spec π g
  have hdvd : orderOf g ∣ orderOf (piPart π g) * orderOf b := by
    have h := hcomm.orderOf_mul_dvd_mul_orderOf; rwa [hmul] at h
  rcases hp.dvd_mul.mp (hpg.trans hdvd) with h | h
  · exact h
  · exact absurd hpπ (hpiB p (Nat.mem_primeFactors.mpr ⟨hp, h, (orderOf_pos b).ne'⟩))

/-- **The `π`-part is multiplicative on commuting elements** (Coq `consttM`): for commuting `x, y`,
`piPart π (x * y) = piPart π x * piPart π y`.  Both `π`-parts are powers of `x`, `y`, so they commute
(as do the two `π′`-parts and the cross pairs), letting `x * y = (xπ yπ)(xπ′ yπ′)` be rearranged into
a commuting `π`-element times `π′`-element; uniqueness of the `π`-decomposition
(`isPiElement_mul_unique`) identifies its `π`-part with `xπ yπ`.  The computational tool behind the
`σ`-decomposition of a `σ`-cover element `x · R(x)` (BG Lemma 14.5). -/
theorem piPart_mul_of_commute [Finite G] {π : Set ℕ} {x y : G} (hcomm : Commute x y) :
    piPart π (x * y) = piPart π x * piPart π y := by
  obtain ⟨cx, hxmul, hxc, hxπ, hxπ', hxz, hcxz⟩ := piPart_spec π x
  obtain ⟨cy, hymul, hyc, hyπ, hyπ', hyz, hcyz⟩ := piPart_spec π y
  obtain ⟨c, hmul, hc, hπ, hπ', -, -⟩ := piPart_spec π (x * y)
  -- powers of `x` commute with powers of `y` (as `x, y` commute).
  have hcross : ∀ {a b : G}, a ∈ Subgroup.zpowers x → b ∈ Subgroup.zpowers y → Commute a b := by
    intro a b ha hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hcomm.zpow_zpow m n
  have hcyx : Commute (piPart π y) cx := (hcross hcxz hyz).symm
  have hprod : (piPart π x * piPart π y) * (cx * cy) = x * y := by
    calc (piPart π x * piPart π y) * (cx * cy)
        = piPart π x * (piPart π y * cx) * cy := by group
      _ = piPart π x * (cx * piPart π y) * cy := by rw [hcyx]
      _ = (piPart π x * cx) * (piPart π y * cy) := by group
      _ = x * y := by rw [hxmul, hymul]
  have hABcomm : Commute (piPart π x * piPart π y) (cx * cy) :=
    Commute.mul_left (Commute.mul_right hxc (hcross hxz hcyz))
      (Commute.mul_right (hcross hcxz hyz).symm hyc)
  exact (isPiElement_mul_unique hmul hc hπ hπ' hprod hABcomm
    (isPiElement_mul_of_commute (hcross hxz hyz) hxπ hyπ)
    (isPiElement_mul_of_commute (hcross hcxz hcyz) hxπ' hyπ')).1

/-- The `σ(M)`-part of an element `x` (Coq `x.`_{σ(M)}`): its `σ(M)`-component in the two-block
π-part decomposition. -/
noncomputable def sigmaPart [Finite G] (M : Subgroup G) (x : G) : G :=
  piPart (OddOrder.BG.Ch3.S10.sigma M) x

/-- The `σ(M)`-part is conjugation-equivariant. -/
theorem sigmaPart_conj [Finite G] (M : Subgroup G) (h x : G) :
    sigmaPart M (h * x * h⁻¹) = h * sigmaPart M x * h⁻¹ := by
  simp only [sigmaPart]; exact piPart_conj _ h x

/-- **BG `sigma_decomposition x`** (Coq `sigma_decomposition`): the set of nonidentity `σ(M)`-parts
of `x` ranging over the maximal subgroups `M`. -/
noncomputable def sigmaDecomposition [Finite G] (x : G) : Set G :=
  {y | ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ y = sigmaPart M x} \ {1}

/-- **BG `sigma_length x = #|sigma_decomposition x|`** (Coq `sigma_length`).  `sigmaLength_eq_zero_iff`
(Coq `ell_sigma0P`) is proved further down, after `exists_mem_sigma_of_prime_dvd_card`. -/
noncomputable def sigmaLength [Finite G] (x : G) : ℕ :=
  (sigmaDecomposition x).ncard

/-- **BG `ell_sigmaJ`**: the σ-length is conjugation-invariant.  Conjugation by `h` is a bijection
of `G` carrying `sigma_decomposition x` onto `sigma_decomposition (h x h⁻¹)` (via `sigmaPart_conj`),
so the two sets have the same cardinality. -/
theorem sigmaLength_conj [Finite G] (h x : G) :
    sigmaLength (h * x * h⁻¹) = sigmaLength x := by
  have hinj : Function.Injective (fun z => h * z * h⁻¹) := fun a b hab => by simpa using hab
  have hconjset : sigmaDecomposition (h * x * h⁻¹)
      = (fun z => h * z * h⁻¹) '' sigmaDecomposition x := by
    unfold sigmaDecomposition
    rw [Set.image_sdiff hinj]
    congr 1
    · ext y
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨M, hMmax, rfl⟩
        exact ⟨sigmaPart M x, ⟨M, hMmax, rfl⟩, (sigmaPart_conj M h x).symm⟩
      · rintro ⟨z, ⟨M, hMmax, rfl⟩, rfl⟩
        exact ⟨M, hMmax, (sigmaPart_conj M h x).symm⟩
    · rw [Set.image_singleton]; simp
  rw [sigmaLength, sigmaLength, hconjset, Set.ncard_image_of_injective _ hinj]

/-- **Coq `sigma_decomposition_subG`**: if `x ∈ H` then every σ-part of `x` lies in `H` (the σ-parts
are powers of `x`), so `sigma_decomposition x ⊆ H`. -/
theorem sigmaDecomposition_subset [Finite G] {x : G} {H : Subgroup G} (hx : x ∈ H) :
    sigmaDecomposition x ⊆ (H : Set G) := by
  rintro y ⟨⟨M, hM, rfl⟩, -⟩
  exact Subgroup.zpowers_le.mpr hx (piPart_mem_zpowers (OddOrder.BG.Ch3.S10.sigma M) x)

/-- Every element of `M_σ` is a `σ(M)`-element (its order divides `|M_σ|`, a `σ(M)`-number). -/
theorem isPiElement_sigma_of_mem_Msigma [Finite G] {M : Subgroup G} {x : G}
    (hx : x ∈ OddOrder.BG.Ch3.S10.Msigma M) :
    IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x := by
  intro p hp
  have horx : orderOf x = orderOf (⟨x, hx⟩ : ↥(OddOrder.BG.Ch3.S10.Msigma M)) := by
    simp
  have hdvd : orderOf x ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
    rw [horx]; exact orderOf_dvd_natCard _
  exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p
    (Nat.primeFactors_mono hdvd (Nat.card_pos).ne' hp)

/-- **`M_σ`-membership is exactly being a `σ(M)`-element** (for `x ∈ M`).  `M_σ` is the *normal*
`σ(M)`-Hall of `M` (`Msigma_isHall`), so it absorbs every `σ(M)`-subgroup; hence `x ∈ M_σ ⟺ ⟨x⟩` is
a `σ(M)`-group `⟺ x` is a `σ(M)`-element.  In particular `M_σ`-membership of an element of `M` is
determined by its order, so it is conjugation-invariant (`isPiElement_conj`) — the BG Theorem E
"distinct orders across pieces" content for the `M_σ` piece. -/
theorem mem_Msigma_iff_isPiElement_sigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G} (hxM : x ∈ M) :
    x ∈ OddOrder.BG.Ch3.S10.Msigma M ↔ IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x := by
  refine ⟨isPiElement_sigma_of_mem_Msigma, fun hpi => ?_⟩
  have hzpi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma M) (Subgroup.zpowers x) := by
    intro p hp
    rw [Nat.card_zpowers] at hp
    exact hpi p hp
  exact OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) (Subgroup.zpowers_le.mpr hxM) hzpi
    (Subgroup.mem_zpowers x)

/-- **An element of `M` whose order is coprime to `[M : N]` lies in the normal `N ≤ M`.**  Pure
group theory: `x^[M:N] ∈ N` (`Subgroup.pow_index_mem`), and `x ∈ ⟨x^[M:N]⟩` because `[M:N]` is
coprime to `orderOf x` (`exists_pow_eq_self_of_coprime`).  The engine for "a normal `π′`-Hall of `M`
absorbs every `π′`-element of `M`" (apply with `[M:N]` a `π`-number and `x` a `π′`-element) — used
for the `A(M)` / `κ(M)′`-Hall piece of BG Theorem E's "distinct orders". -/
theorem mem_of_coprime_index [Finite G] {M N : Subgroup G} (hNM : N ≤ M)
    [(N.subgroupOf M).Normal] {x : G} (hxM : x ∈ M)
    (hcop : Nat.Coprime ((N.subgroupOf M).index) (orderOf x)) : x ∈ N := by
  have hpow : x ^ (N.subgroupOf M).index ∈ N := by
    have h := Subgroup.pow_index_mem (N.subgroupOf M) ⟨x, hxM⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact pow_mem hpow m

/-- **The index `[M : U ⊔ M_σ]` is a `κ(M)`-number** (`M` maximal, `M_σ` the `σ(M)`-Hall, `U` a
`(κ∪σ)′`-Hall).  Since `M_σ ≤ U ⊔ M_σ` and `U ≤ U ⊔ M_σ`, `[M : U⊔M_σ]` divides both `[M : M_σ]` (a
`σ′`-number, `Msigma_subgroupOf_isHall`) and `[M : U]` (a `κ∪σ`-number, `hU`), so each of its primes
avoids `σ` yet lies in `κ ∪ σ`, i.e. in `κ(M)`.  Combined with `mem_of_coprime_index`, this gives the
`A(M)`-piece absorption "a `κ(M)′`-element of `M` lies in `U ⊔ M_σ`" of BG Theorem E. -/
theorem index_U_sup_Msigma_primeFactors_subset_kappa [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} (hp : p ∈ ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index.primeFactors) :
    p ∈ kappa M := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index :=
    Nat.dvd_of_mem_primeFactors hp
  have hdvdMσ : ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index ∣
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index :=
    Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono M le_sup_right)
  have hdvdU : ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index ∣ (U.subgroupOf M).index :=
    Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono M le_sup_left)
  have hpnσ : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
    (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).index_no_pi p
      (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd.trans hdvdMσ, Subgroup.index_ne_zero_of_finite⟩)
  have hpnκσ : p ∉ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    hU.index_no_pi p
      (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd.trans hdvdU, Subgroup.index_ne_zero_of_finite⟩)
  simp only [Set.mem_compl_iff, not_not, Set.mem_union] at hpnκσ
  exact hpnκσ.resolve_right hpnσ

/-- **`|H ⊔ N|` divides `|H| · |N|`** for `N ◁ G` (Noether's second isomorphism: `[H⊔N : N] =
[H : H⊓N]`, so `|H⊔N| = [H : H⊓N]·|N|` with `[H : H⊓N] ∣ |H|`).  Used to bound `π(U ⊔ M_σ) ⊆ κ′`
from `π(U) ⊆ (κ∪σ)′` and `π(M_σ) ⊆ σ` (the `A(M)`-piece forward, with `M_σ ◁ M`). -/
theorem card_sup_dvd_mul_of_normal {H N : Subgroup G} [N.Normal] :
    Nat.card ↥(H ⊔ N) ∣ Nat.card ↥H * Nat.card ↥N := by
  have e : (N.subgroupOf H).index = (N.subgroupOf (H ⊔ N)).index := by
    have h := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H N).toEquiv
    simpa [Subgroup.index] using h
  have hN : Nat.card ↥(N.subgroupOf (H ⊔ N)) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h1 : Nat.card ↥(H ⊔ N) = (N.subgroupOf (H ⊔ N)).index * Nat.card ↥N := by
    rw [← Subgroup.card_mul_index (N.subgroupOf (H ⊔ N)), hN, mul_comm]
  rw [h1, ← e]
  exact mul_dvd_mul_right (N.subgroupOf H).index_dvd_card (Nat.card ↥N)

/-- **`U ⊔ M_σ`-membership is exactly being a `κ(M)′`-element** (for `x ∈ M`, given `U⊔M_σ ◁ M` as
`hnorm`).  `U⊔M_σ` is the normal `κ(M)′`-Hall of `M`: forward, `|U⊔M_σ| ∣ |U||M_σ|`
(`card_sup_dvd_mul_of_normal`, `M_σ ◁ M`) and `π(U), π(M_σ) ⊆ κ′`, so any `x ∈ U⊔M_σ` is a
`κ′`-element; backward, `[M:U⊔M_σ]` is a `κ`-number (`index_U_sup_Msigma_primeFactors_subset_kappa`),
coprime to a `κ′`-element's order, so `mem_of_coprime_index` puts it in `U⊔M_σ`.  The `A(M)`-piece of
BG Theorem E's "distinct orders": `U⊔M_σ`-membership of an element of `M` is order-determined. -/
theorem mem_U_sup_Msigma_iff_isPiElement_kappa_compl [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hnorm : ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal)
    {x : G} (hxM : x ∈ M) :
    x ∈ U ⊔ OddOrder.BG.Ch3.S10.Msigma M ↔ IsPiElement (kappa M)ᶜ x := by
  haveI := hnorm
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  refine ⟨fun hx p hp => ?_, fun hpi => ?_⟩
  · -- forward: `x ∈ U⊔M_σ ⟹` `p ∈ π(orderOf x) ⟹ p ∉ κ`.
    have hpord : p ∣ orderOf x := Nat.dvd_of_mem_primeFactors hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have h1 : orderOf x ∣ Nat.card ↥(U ⊔ OddOrder.BG.Ch3.S10.Msigma M) := by
      have heq : orderOf x = orderOf (⟨x, hx⟩ : ↥(U ⊔ OddOrder.BG.Ch3.S10.Msigma M)) :=
        orderOf_injective (U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subtype
          (U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subtype_injective ⟨x, hx⟩
      rw [heq]; exact orderOf_dvd_natCard _
    have h2 : Nat.card ↥(U ⊔ OddOrder.BG.Ch3.S10.Msigma M) ∣
        Nat.card ↥U * Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
      haveI : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
        rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
      have hdvd := card_sup_dvd_mul_of_normal (H := U.subgroupOf M)
        (N := (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      rw [← Subgroup.subgroupOf_sup hUM hMσM,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hUM hMσM)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv] at hdvd
      exact hdvd
    have hp2 : p ∣ Nat.card ↥U * Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      (hpord.trans h1).trans h2
    rcases (hpp.dvd_mul.mp hp2) with hpU | hpMσ
    · have hpfU : p ∈ (Nat.card ↥(U.subgroupOf M)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp,
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv) ▸ hpU, Nat.card_pos.ne'⟩
      have := hU.primeFactors_card_subset p hpfU
      simp only [Set.mem_compl_iff, Set.mem_union, not_or] at this
      exact this.1
    · have hpfMσ : p ∈ (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp,
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv) ▸ hpMσ, Nat.card_pos.ne'⟩
      exact fun hpκ => kappa_subset_sigmaCompl hpκ
        ((OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).primeFactors_card_subset p hpfMσ)
  · -- backward: `κ′`-element of `M` lies in `U⊔M_σ`.
    refine mem_of_coprime_index (sup_le hUM hMσM) hxM ?_
    refine (Nat.disjoint_primeFactors Subgroup.index_ne_zero_of_finite
      (orderOf_pos x).ne').mp ?_
    rw [Finset.disjoint_left]
    intro p hpfκ hpfo
    exact (hpi p hpfo) (index_U_sup_Msigma_primeFactors_subset_kappa hG hM hU hpfκ)

/-- For a `σ(M)`-element `x`, every `σ(L)`-part (`L` maximal) is either `x` or `1`: if `L` is
conjugate to `M` then `σ(L) = σ(M)` contains all primes of `x` (`sigmaPart L x = x`); otherwise
`σ(M) ∩ σ(L) = ∅` (`sigma_disjoint_of_nonconjugate`) so `x` avoids `σ(L)` (`sigmaPart L x = 1`). -/
theorem sigmaPart_eq_self_or_one_of_isPiElement_sigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hx : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x) {L : Subgroup G}
    (hL : L ∈ maximalSubgroups G) :
    sigmaPart L x = x ∨ sigmaPart L x = 1 := by
  simp only [sigmaPart]
  by_cases hconj : ∃ g : G, MulAut.conj g • M = L
  · obtain ⟨g, rfl⟩ := hconj
    exact Or.inl (piPart_self_of_isPiElement (fun p hp => by
      haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      exact OddOrder.BG.Ch3.S10.sigma_conj g (hx p hp)))
  · refine Or.inr (piPart_eq_one_of_isPiElement_compl (fun p hp hpL => ?_))
    exact Set.disjoint_left.mp (sigma_disjoint_of_nonconjugate hG hM hL hconj) (hx p hp) hpL

/-- **Directed `sigmaPart`, conjugate case**: a `σ(M)`-element is fixed by the `σ(L)`-part when `L`
is `M`-conjugate (`σ(L) = σ(M)`). -/
theorem sigmaPart_eq_self_of_conj [Finite G] {M : Subgroup G} {x : G}
    (hx : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x) {L : Subgroup G}
    (hconj : ∃ g : G, MulAut.conj g • M = L) : sigmaPart L x = x := by
  simp only [sigmaPart]
  obtain ⟨g, rfl⟩ := hconj
  exact piPart_self_of_isPiElement (fun p hp => by
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact OddOrder.BG.Ch3.S10.sigma_conj g (hx p hp))

/-- **Directed `sigmaPart`, non-conjugate case**: a `σ(M)`-element has trivial `σ(L)`-part when `L`
is *not* `M`-conjugate (`σ(M) ∩ σ(L) = ∅`). -/
theorem sigmaPart_eq_one_of_not_conj [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G}
    (hx : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x) {L : Subgroup G}
    (hL : L ∈ maximalSubgroups G) (hnconj : ¬ ∃ g : G, MulAut.conj g • M = L) :
    sigmaPart L x = 1 := by
  simp only [sigmaPart]
  exact piPart_eq_one_of_isPiElement_compl (fun p hp hpL =>
    Set.disjoint_left.mp (sigma_disjoint_of_nonconjugate hG hM hL hnconj) (hx p hp) hpL)

/-- **σ-decomposition of a `σ`-cover element** (Coq `sigma_cover_decomposition`, BG remark above
Lemma 14.5): for a nonidentity `σ(M)`-element `x`, a `σ(N)`-element `x'` with `M`, `N`
non-conjugate, and `x`, `x'` commuting, `sigma_decomposition (x * x') = {x} ∪ {x'}^#`.  Each `σ(L)`-part
of `x * x'` is `sigmaPart L x · sigmaPart L x'` (`piPart_mul_of_commute`); as `M`, `N` are
non-conjugate, no `L` is conjugate to both, so that part is `x` (`L ∼ M`), `x'` (`L ∼ N`) or `1`. -/
theorem sigma_cover_decomposition [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M N : Subgroup G} (hM : M ∈ maximalSubgroups G) (hN : N ∈ maximalSubgroups G)
    (hMN : ¬ ∃ g : G, MulAut.conj g • M = N)
    {x x' : G} (hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    (hx'N : x' ∈ OddOrder.BG.Ch3.S10.Msigma N) (hcomm : Commute x x') :
    sigmaDecomposition (x * x') = insert x ({x'} \ {1}) := by
  classical
  have hxσ : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x := isPiElement_sigma_of_mem_Msigma hxM
  have hx'σ : IsPiElement (OddOrder.BG.Ch3.S10.sigma N) x' := isPiElement_sigma_of_mem_Msigma hx'N
  -- conjugacy is symmetric, so `N` is not `M`-conjugate either.
  have hNM : ¬ ∃ g : G, MulAut.conj g • N = M := by
    rintro ⟨g, hg⟩
    exact hMN ⟨g⁻¹, by rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩
  have hpart : ∀ L : Subgroup G, sigmaPart L (x * x') = sigmaPart L x * sigmaPart L x' := fun L => by
    simp only [sigmaPart]; exact piPart_mul_of_commute hcomm
  ext y
  simp only [sigmaDecomposition, Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff,
    Set.mem_insert_iff]
  constructor
  · rintro ⟨⟨L, hL, rfl⟩, hne⟩
    rw [hpart L] at hne ⊢
    by_cases hLM : ∃ g : G, MulAut.conj g • M = L
    · by_cases hLN : ∃ g : G, MulAut.conj g • N = L
      · exfalso
        obtain ⟨g, hg⟩ := hLM; obtain ⟨h, hh⟩ := hLN
        refine hMN ⟨h⁻¹ * g, ?_⟩
        have hgh : MulAut.conj g • M = MulAut.conj h • N := hg.trans hh.symm
        rw [map_mul, mul_smul, hgh, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      · left
        rw [sigmaPart_eq_self_of_conj hxσ hLM,
          sigmaPart_eq_one_of_not_conj hG hN hx'σ hL hLN, mul_one]
    · by_cases hLN : ∃ g : G, MulAut.conj g • N = L
      · right
        have hval : sigmaPart L x * sigmaPart L x' = x' := by
          rw [sigmaPart_eq_one_of_not_conj hG hM hxσ hL hLM,
            sigmaPart_eq_self_of_conj hx'σ hLN, one_mul]
        exact ⟨hval, hval ▸ hne⟩
      · exact absurd (by rw [sigmaPart_eq_one_of_not_conj hG hM hxσ hL hLM,
          sigmaPart_eq_one_of_not_conj hG hN hx'σ hL hLN, mul_one]) hne
  · rintro (rfl | ⟨rfl, hne⟩)
    · refine ⟨⟨M, hM, ?_⟩, hx1⟩
      rw [hpart M, sigmaPart_eq_self_of_conj hxσ ⟨1, by rw [map_one, one_smul]⟩,
        sigmaPart_eq_one_of_not_conj hG hN hx'σ hM hNM, mul_one]
    · refine ⟨⟨N, hN, ?_⟩, hne⟩
      rw [hpart N, sigmaPart_eq_one_of_not_conj hG hM hxσ hN hMN,
        sigmaPart_eq_self_of_conj hx'σ ⟨1, by rw [map_one, one_smul]⟩, one_mul]

/-- **The signalizer maximal is not `M`-conjugate** (the `M, N` non-conjugacy behind the cover
decomposition): a nonidentity `σ(M)`-element `x` that is also a `τ₂(N)`-element forces `M`, `N`
non-conjugate.  If `M ∼ N` then `σ(M) = σ(N)`, so a prime `q ∣ |x|` lies in `σ(N)`; but `q ∈ τ₂(N) ⊆
σ(N)ᶜ` (`tau2_subset_sigma_compl`) — contradiction.  In the FT signalizer context `x ∈ M_σ^#` is a
`τ₂(N)`-element for the signalizer maximal `N` (`signalizer_structure_of_mem_sigmaSharp`). -/
theorem not_conj_of_mem_Msigma_of_tau2 [Finite G] {M N : Subgroup G}
    {x : G} (hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    (hxτ2 : ∀ p ∈ piSet (Subgroup.closure ({x} : Set G)), p ∈ tau2 N) :
    ¬ ∃ g : G, MulAut.conj g • M = N := by
  rintro ⟨g, hg⟩
  obtain ⟨q, hqp, hqdvd⟩ :=
    (orderOf x).exists_prime_and_dvd (fun h => hx1 (orderOf_eq_one_iff.mp h))
  haveI : Fact q.Prime := ⟨hqp⟩
  have hqσM : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    isPiElement_sigma_of_mem_Msigma hxM q (Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, (orderOf_pos x).ne'⟩)
  have hqσN : q ∈ OddOrder.BG.Ch3.S10.sigma N := hg ▸ OddOrder.BG.Ch3.S10.sigma_conj g hqσM
  have hcardx : Nat.card ↥(Subgroup.closure ({x} : Set G)) = orderOf x := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  have hqπ : q ∈ piSet (Subgroup.closure ({x} : Set G)) := by
    rw [piSet, Set.mem_setOf_eq, hcardx]
    exact Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, (orderOf_pos x).ne'⟩
  exact tau2_subset_sigma_compl N (hxτ2 q hqπ) hqσN

/-- **σ-decomposition of a cover element in the signalizer context** (`sigma_cover_decomposition`
specialized to `N` = the signalizer maximal): for `x ∈ M_σ^#` a `τ₂(N)`-element and `x' ∈ N_σ`
commuting with `x`, `sigma_decomposition (x * x') = {x} ∪ {x'}^#`.  The `M, N` non-conjugacy needed by
`sigma_cover_decomposition` is supplied by `not_conj_of_mem_Msigma_of_tau2`.  Discharges the cover
decomposition that BG Lemma 14.5(a) (`sigma_cover_disjoint`) reads off. -/
theorem sigma_cover_decomposition_signalizer [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M N : Subgroup G} (hM : M ∈ maximalSubgroups G) (hN : N ∈ maximalSubgroups G)
    {x x' : G} (hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    (hxτ2 : ∀ p ∈ piSet (Subgroup.closure ({x} : Set G)), p ∈ tau2 N)
    (hx'N : x' ∈ OddOrder.BG.Ch3.S10.Msigma N) (hcomm : Commute x x') :
    sigmaDecomposition (x * x') = insert x ({x'} \ {1}) :=
  sigma_cover_decomposition hG hM hN (not_conj_of_mem_Msigma_of_tau2 hxM hx1 hxτ2) hxM hx1 hx'N hcomm

/-- **`x` is a `σ`-part of the cover element `x · x'`** (Coq `mem_sigma_cover_decomposition`): immediate
from `sigma_cover_decomposition_signalizer`, `x ∈ {x} ∪ {x'}^#`.  Used in BG Lemma 14.5(a). -/
theorem mem_sigma_cover_decomposition_signalizer [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M N : Subgroup G} (hM : M ∈ maximalSubgroups G) (hN : N ∈ maximalSubgroups G)
    {x x' : G} (hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    (hxτ2 : ∀ p ∈ piSet (Subgroup.closure ({x} : Set G)), p ∈ tau2 N)
    (hx'N : x' ∈ OddOrder.BG.Ch3.S10.Msigma N) (hcomm : Commute x x') :
    x ∈ sigmaDecomposition (x * x') := by
  rw [sigma_cover_decomposition_signalizer hG hM hN hxM hx1 hxτ2 hx'N hcomm]
  exact Set.mem_insert x _

/-- **BG Corollary 14.10 (cover form): `ℓ_σ(x · x') ≤ 2`** (Coq `ell_sigma_cover`): a `σ`-cover
element has `σ`-length at most two, since its `σ`-decomposition `{x} ∪ {x'}^#` has at most two
elements (`sigma_cover_decomposition_signalizer`). -/
theorem sigmaLength_cover_le_two_signalizer [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M N : Subgroup G} (hM : M ∈ maximalSubgroups G) (hN : N ∈ maximalSubgroups G)
    {x x' : G} (hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    (hxτ2 : ∀ p ∈ piSet (Subgroup.closure ({x} : Set G)), p ∈ tau2 N)
    (hx'N : x' ∈ OddOrder.BG.Ch3.S10.Msigma N) (hcomm : Commute x x') :
    sigmaLength (x * x') ≤ 2 := by
  rw [sigmaLength, sigma_cover_decomposition_signalizer hG hM hN hxM hx1 hxτ2 hx'N hcomm]
  have h1 : ({x'} \ {1} : Set G).ncard ≤ 1 :=
    (Set.ncard_le_ncard Set.sdiff_subset (Set.finite_singleton x')).trans
      (le_of_eq (Set.ncard_singleton x'))
  calc (insert x ({x'} \ {1} : Set G)).ncard
      ≤ ({x'} \ {1} : Set G).ncard + 1 := Set.ncard_insert_le x _
    _ ≤ 2 := by omega

/-- **BG `Msigma_ell1`** (Coq BGsection14): a nonidentity element of `M_σ` has σ-length `1`.  As a
`σ(M)`-element, its σ-decomposition collapses to the single block `{x}`: every `σ(L)`-part is `x`
or `1` (`sigmaPart_eq_self_or_one_of_isPiElement_sigma`), and `sigmaPart M x = x ≠ 1`.  This is the
genuine form of the `ℓ_σ(x) = 1` property that the `SigmaDecompositionData` scaffold posits for
`x ∈ M_σ^#` (`length_one_of_isPiElement_sigma`). -/
theorem Msigma_ell1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {x : G} (hx : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1) :
    sigmaLength x = 1 := by
  have hxσ : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x := isPiElement_sigma_of_mem_Msigma hx
  have hself : sigmaPart M x = x := piPart_self_of_isPiElement hxσ
  have hset : sigmaDecomposition x = {x} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨M, hM, hself.symm⟩, ?_⟩, ?_⟩
    · simp only [Set.mem_singleton_iff]; exact hx1
    · rintro y ⟨⟨L, hL, rfl⟩, hy⟩
      rcases sigmaPart_eq_self_or_one_of_isPiElement_sigma hG hM hxσ hL with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mpr h) hy
  rw [sigmaLength, hset, Set.ncard_singleton]

/-- A named carrier for the sigma-decomposition / sigma-length data of BG §14.

The actual construction comes from Theorem 13.9 and the Hall decomposition of
finite groups.  Keeping it as explicit data avoids a false placeholder
`def sigmaLength := 0` while still letting §§15--16 state their dependencies. -/
structure SigmaDecompositionData (G : Type*) [Group G] where
  length : G → ℕ
  length_one_iff : ∀ x : G,
    length x = 1 ↔ x ≠ 1 ∧ (maximalSigmaSubgroupsOfElement x).Nonempty

end OddOrder.BG.Ch4.S14
