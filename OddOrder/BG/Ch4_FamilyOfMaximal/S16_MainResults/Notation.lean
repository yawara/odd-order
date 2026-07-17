import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_PairIntersection
import OddOrder.GroupTheory.RepresentationTheory.ExtraspecialSinger
import OddOrder.GroupTheory.MaximalSubgroupType
import OddOrder.GroupTheory.MaximalSubgroupTypeConj
import OddOrder.GroupTheory.CoprimeAction
import OddOrder.GroupTheory.AInvariantComplement

/-!
# Notation

Prefix-split from `OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.TheoremsAE` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# BG Theorem E notation + Theorems A--E

Split from the former monolithic `OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults` (directory split, issue 0103).
-/
namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S14
open OddOrder.BG.Ch4.S15
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Theorem E notation: `hat M_sigma`, `A(M)`, and `A_0(M)` -/

/-- BG Theorem E notation: `hat M_sigma = {a in M | C_{M_sigma}(a) != 1}`. -/
def hatMsigma (M : Subgroup G) : Set G :=
  {a | a ∈ M ∧ OddOrder.BG.Ch3.S10.Msigma M ⊓
    Subgroup.centralizer ({a} : Set G) ≠ ⊥}

/-- `M_σ# ⊆ \widehat{M_σ}`: every nonidentity element `x` of `M_σ` lies in `hatMsigma M`,
since `x ∈ M_σ ≤ M` and `x` centralizes itself, so `1 ≠ x ∈ M_σ ⊓ C_G(x)`.  `§14`-independent
building block for Theorems B/E (`A(M) = hatMsigma ∩ …`). -/
theorem sigmaSharp_subset_hatMsigma (M : Subgroup G) :
    S14.sigmaSharp M ⊆ hatMsigma M := by
  intro x hx
  simp only [S14.sigmaSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe,
    Set.mem_singleton_iff] at hx
  obtain ⟨hxMσ, hx1⟩ := hx
  refine ⟨OddOrder.BG.Ch3.S10.Msigma_le M hxMσ, fun hbot => hx1 (Subgroup.mem_bot.mp ?_)⟩
  rw [← hbot]
  exact Subgroup.mem_inf.mpr ⟨hxMσ, Subgroup.mem_centralizer_iff.mpr
    (fun h hh => by rw [Set.mem_singleton_iff] at hh; subst hh; rfl)⟩

/-- `1 ∈ \widehat{M_σ}` whenever `M_σ ≠ 1`: the identity is centralized by everything, so
`M_σ ⊓ C_G(1) = M_σ ≠ 1`.  Used by Theorem B(3) (`U_0 ∩ hatMsigma = {1}`).  `§14`-independent. -/
theorem one_mem_hatMsigma_of_Msigma_ne_bot {M : Subgroup G}
    (h : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥) : (1 : G) ∈ hatMsigma M := by
  refine ⟨Subgroup.one_mem M, ?_⟩
  have hC : Subgroup.centralizer ({1} : Set G) = ⊤ :=
    eq_top_iff.mpr fun g _ => Subgroup.mem_centralizer_iff.mpr
      fun h hh => by rw [Set.mem_singleton_iff] at hh; subst hh; simp
  rw [hC, inf_top_eq]
  exact h

/-- BG Theorem E notation: `A(M) = hat M_sigma ∩ U M_sigma`. -/
def ASet (M U : Subgroup G) : Set G :=
  hatMsigma M ∩ ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G)

/-- BG Theorem E notation: `A_0(M) = hat M_sigma - C_M(K#)`, represented as the
part of `hat M_sigma` outside the `M`-conjugacy saturation of `K#`. -/
def A0Set (M K : Subgroup G) : Set G :=
  hatMsigma M \ conjClassSet (sharpSubgroup K)

/-- BG Theorem D(3) action language: `R` acts sharply transitively by conjugation on
a set of maximal subgroups. -/
def ConjSharplyTransitiveOn (R : Subgroup G) (S : Set (Subgroup G)) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, ∃! r : G, r ∈ R ∧ B = MulAut.conj r • A

/-- The set of conjugates of `M` that contain `x`, from BG Theorem D(3). -/
def maximalConjugatesContaining (M : Subgroup G) (x : G) : Set (Subgroup G) :=
  {N | ∃ g : G, N = MulAut.conj g • M ∧ x ∈ N}

/-- BG Theorem D(3) local data for `R(x)`: `C_M(x)` is a Hall subgroup of
`C_G(x)`, and `R` is a normal complement acting sharply transitively on the
maximal conjugates that contain `x`.

**Encoding fix (2026-06-29, lane δ; HUB-cleared `RData` is δ-internal, not a cross-lane contract):**
conjunct 1 was `IsHallSubgroup (σ M) (C_M(x))`, which is **false** for type-`P` `M`: at `x ∈ Kstar^#`
the `κ`-Hall `K` (with `κ(M) ⊆ σ(M)ᶜ`) centralizes `x`, so `K ≤ C_M(x)`, making `C_M(x)` carry
`σ(M)′`-primes — not a `σ(M)`-group.  Coq Theorem 14.4(b)/(e) has `C_M(x)` a `σ(N)′`-Hall of `C_G(x)`
(`N` = the signalizer maximal), i.e. *intrinsically* a Hall subgroup of `C_G(x)` (its order coprime to
its index).  We encode "`C_M(x)` is a Hall subgroup of `C_G(x)`" `σ`-agnostically as this coprimality,
matching the docstring and avoiding the spurious `σ(M)` reference. -/
def RData (M : Subgroup G) (x : G) (R : Subgroup G) : Prop :=
  let Cx : Subgroup G := Subgroup.centralizer ({x} : Set G)
  Nat.Coprime (Nat.card ↥((M ⊓ Cx).subgroupOf Cx)) ((M ⊓ Cx).subgroupOf Cx).index ∧
    (R.subgroupOf Cx).Normal ∧
    Subgroup.IsComplement' ((M ⊓ Cx).subgroupOf Cx) (R.subgroupOf Cx) ∧
    ConjSharplyTransitiveOn R (maximalConjugatesContaining M x)

/-- BG Theorem E notation: `xR(x)` as a left coset, represented as a set. -/
def rCoset (x : G) (R : G → Subgroup G) : Set G :=
  {y | ∃ r ∈ R x, y = x * r}

/-- BG Theorem E notation:
`\widetilde M = \bigcup_{x \in M_sigma#} x R(x)`. -/
def tildeM (M : Subgroup G) (R : G → Subgroup G) : Set G :=
  {y | ∃ x ∈ sigmaSharp M, y ∈ rCoset x R}

/-- BG's `pi*`: the primes whose Sylow subgroup is cyclic, or has the cyclic
centralizer splitting described in the type-I alternatives. -/
def piStar (G : Type*) [Group G] : Set ℕ :=
  {p | p ∈ (Nat.card G).primeFactors ∧
    ∃ P : Sylow p G,
      IsCyclic ↥(P : Subgroup G) ∨
        ∃ A B : Subgroup G,
          A ≤ (P : Subgroup G) ∧ B ≤ (P : Subgroup G) ∧ Nat.card ↥A = p ∧
          IsCyclic ↥B ∧ Subgroup.centralizer (A : Set G) ⊓ (P : Subgroup G) = A ⊔ B}

/-! ### BG `FT_signalizer` (`R(x)`, Theorem D(3)/(4)) — concrete construction

The concrete FT signalizer `R(x) = FT_signalizer x` (Coq `FT_signalizer`, BGsection14:90), built from
`FT_signalizer_base x = N[x]`: when `x` has more than one `σ`-maximal, `N[x]` is a maximal subgroup
over `C_G(x)` (the unique one — Theorem D, via Corollary 12.14); `R(x) = (N[x])_σ ⊓ C_G(x)`.  This is
the genuine object the Theorem D(3)/(4) data `RData M x R` is built on; the deep
`FT_signalizer_context` (transitive action / Hall / uniqueness) is the remaining content. -/

open Classical in
/-- BG `FT_signalizer_base x` (`N[x]`, Coq BGsection14:87): a maximal subgroup over `C_G(x)` when `x`
has more than one `σ`-maximal (Coq picks one; Theorem D proves it unique), else `⊥`. -/
noncomputable def FT_signalizerBase (x : G) : Subgroup G :=
  if h : 1 < (maximalSigmaSubgroupsOfElement x).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G))).Nonempty then
    h.2.choose
  else ⊥

/-- BG `FT_signalizer x` (`R(x)`, Coq BGsection14:90): `(N[x])_σ ⊓ C_G(x)`. -/
noncomputable def FT_signalizer (x : G) : Subgroup G :=
  OddOrder.BG.Ch3.S10.Msigma (FT_signalizerBase x) ⊓ Subgroup.centralizer ({x} : Set G)

/-- `R(x) ≤ C_G(x)` (Coq `cent_FT_signalizer`). -/
theorem FT_signalizer_le_centralizer (x : G) :
    FT_signalizer x ≤ Subgroup.centralizer ({x} : Set G) :=
  inf_le_right

/-- **Trivial branch** (Coq: `#|M_σ[x]| ≤ 1 ⟹ R(x) = 1`): when `x` has at most one `σ`-maximal (or
no maximal lies over `C_G(x)`), `N[x] = ⊥` so `R(x) = (N[x])_σ ⊓ C_G(x) = ⊥`. -/
theorem FT_signalizer_eq_bot_of_not_branch {x : G}
    (h : ¬ (1 < (maximalSigmaSubgroupsOfElement x).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G))).Nonempty)) :
    FT_signalizer x = ⊥ := by
  have hb : FT_signalizerBase x = ⊥ := dif_neg h
  simp only [FT_signalizer, hb, le_bot_iff.mp (OddOrder.BG.Ch3.S10.Msigma_le ⊥), bot_inf_eq]

/-- In the nontrivial branch, `N[x]` is a maximal subgroup containing `C_G(x)`. -/
theorem centralizer_le_FT_signalizerBase {x : G}
    (h : 1 < (maximalSigmaSubgroupsOfElement x).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G))).Nonempty) :
    Subgroup.centralizer ({x} : Set G) ≤ FT_signalizerBase x := by
  have hb : FT_signalizerBase x = h.2.choose := dif_pos h
  rw [hb]
  exact (mem_maximalSubgroupsContaining.mp h.2.choose_spec).2

/-- **Normal Hall meets a subgroup, giving a Hall subgroup** (Coq `setI_normal_Hall`): if `A` is a
normal `π`-Hall subgroup of `N` and `H ≤ N`, then `A ⊓ H` is a `π`-Hall subgroup of `H`.  The
`π`-part is clear (`A ⊓ H ≤ A`); the `π′`-index is `[H : A ⊓ H] = (A_N).relIndex (H_N) ∣ [N : A]` by
the second isomorphism (`relIndex_sup_right`, using `A ◁ N`). -/
theorem isHallSubgroup_subgroupOf_inf_of_normal_isHall [Finite G] {π : Set ℕ} {A N H : Subgroup G}
    (hAN : A ≤ N) (hHN : H ≤ N)
    (hAhall : Ch03.IsHallSubgroup π (A.subgroupOf N))
    (hAnorm : (A.subgroupOf N).Normal) :
    Ch03.IsHallSubgroup π ((A ⊓ H).subgroupOf H) := by
  haveI : (A.subgroupOf N).Normal := hAnorm
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · -- `π`-part: `|A ⊓ H| ∣ |A|`.
    have hcard1 : Nat.card ↥((A ⊓ H).subgroupOf H) = Nat.card ↥(A ⊓ H) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ H ≤ H)).toEquiv
    have hcard2 : Nat.card ↥(A ⊓ H) ∣ Nat.card ↥(A.subgroupOf N) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact hAhall.1 p (Nat.primeFactors_mono (hcard1 ▸ hcard2) Nat.card_pos.ne' hp)
  · -- `π′`-index: `[H : A ⊓ H] = (A_N).relIndex (H_N) ∣ (A_N).index`.
    have he1 : ((A ⊓ H).subgroupOf H).index = (A.subgroupOf N).relIndex (H.subgroupOf N) := by
      change (A ⊓ H).relIndex H = _
      rw [inf_comm, Subgroup.inf_relIndex_left, ← Subgroup.relIndex_subgroupOf hHN]
    have htower := Subgroup.relIndex_mul_relIndex (A.subgroupOf N)
      ((H.subgroupOf N) ⊔ (A.subgroupOf N)) ⊤ le_sup_right le_top
    simp only [Subgroup.relIndex_top_right, Subgroup.relIndex_sup_right] at htower
    have hidvd : ((A ⊓ H).subgroupOf H).index ∣ (A.subgroupOf N).index := by
      rw [he1]; exact ⟨_, htower.symm⟩
    exact hAhall.2 p (Nat.primeFactors_mono hidvd Subgroup.index_ne_zero_of_finite hp)

/-- **General `(N)_σ ⊓ C_G(x) ◁ C_G(x)` normality** (the core of Theorem D(3) `nsRCx`): for any `N`
with `C_G(x) ≤ N`, the centralizer normalizes `(N)_σ ⊓ C_G(x)` — it normalizes `(N)_σ ◁ N` (since
`C_G(x) ≤ N`) and itself, so it normalizes the intersection (`le_normalizer_inf`).  Applies both to
`N[x]` (`FT_signalizer_normal_in_centralizer`) and to the unique maximal from
`signalizer_structure_of_mem_sigmaSharp`. -/
theorem centralizer_le_normalizer_Msigma_inf_centralizer {x : G} {N : Subgroup G}
    (hCN : Subgroup.centralizer ({x} : Set G) ≤ N) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer
      ((OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  haveI hMσN : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).Normal := by
    rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have hbaseN : N ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch3.S10.Msigma_le _)).mp hMσN
  exact OddOrder.BG.Ch3.S12.le_normalizer_inf (hCN.trans hbaseN) Subgroup.le_normalizer

/-- **BG Theorem D(3), `R(x) ◁ C_G(x)`** (Coq `nsRCx`): the first-conjunct normality, the
`N = N[x]` instance of `centralizer_le_normalizer_Msigma_inf_centralizer`. -/
theorem FT_signalizer_normal_in_centralizer {x : G}
    (h : 1 < (maximalSigmaSubgroupsOfElement x).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G))).Nonempty) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (FT_signalizer x : Set G) :=
  centralizer_le_normalizer_Msigma_inf_centralizer (centralizer_le_FT_signalizerBase h)

/-- **BG Theorem D(3), `R(x)` is a `σ(N[x])`-Hall subgroup of `C_G(x)`** (Coq `hallR`): the
first-conjunct Hall property.  `R(x) = (N[x])_σ ⊓ C_G(x)` with `(N[x])_σ` a normal `σ(N[x])`-Hall
subgroup of `N[x]` (`Msigma_subgroupOf_isHall`) and `C_G(x) ≤ N[x]`, so
`isHallSubgroup_subgroupOf_inf_of_normal_isHall` applies. -/
theorem FT_signalizer_isHall [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {x : G}
    (h : 1 < (maximalSigmaSubgroupsOfElement x).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G))).Nonempty) :
    Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma (FT_signalizerBase x))
      ((FT_signalizer x).subgroupOf (Subgroup.centralizer ({x} : Set G))) := by
  have hbasemax : FT_signalizerBase x ∈ maximalSubgroups G := by
    have hb : FT_signalizerBase x = h.2.choose := dif_pos h
    rw [hb]; exact mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp h.2.choose_spec).1
  have hnorm : ((OddOrder.BG.Ch3.S10.Msigma (FT_signalizerBase x)).subgroupOf
      (FT_signalizerBase x)).Normal := by
    rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  exact isHallSubgroup_subgroupOf_inf_of_normal_isHall
    (OddOrder.BG.Ch3.S10.Msigma_le _) (centralizer_le_FT_signalizerBase h)
    (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hbasemax) hnorm

/-- **Signalizer structure for a `σ`-sharp element** (the genuine bridge to Theorem D): for
`x ∈ M_σ^#` with more than one `σ`-maximal, the proven `sigmaLength_one_centralizer_structure`
(fed the genuine `genuineSigmaDecomposition`, with `ℓ_σ(x) = 1` from `Msigma_ell1`) yields the unique
maximal `N = N[x]` over `C_G(x)` together with the Hall property of `R = N_σ ⊓ C_G(x)`, the sharp
transitivity on `𝓜_σ(x)`, the type-F/P2 dichotomy and the complement structure.  This is what the
Theorem D(3)/(4) data is assembled from. -/
theorem signalizer_structure_of_mem_sigmaSharp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hxM : x ∈ S14.sigmaSharp M)
    (hgt : 1 < (S14.maximalSigmaSubgroupsOfElement x).ncard) :
    ∃! N : Subgroup G, N ∈ maximalSubgroups G ∧
      Subgroup.centralizer ({x} : Set G) ≤ N ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ ∧
      Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma N)
        ((OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
          (Subgroup.centralizer ({x} : Set G))) ∧
      (∀ p ∈ S14.piSet (Subgroup.closure {x}), p ∈ tau2 N) ∧
      (S14.IsTypeF N ∨ S14.IsTypeP2 N) ∧
      ∀ M' ∈ S14.maximalSigmaSubgroupsOfElement x,
        tau2 N ∩ S14.piSet N ⊆ OddOrder.BG.Ch3.S10.sigma M' ∧
        OddOrder.BG.Ch3.S10.sigma N ∩ S14.piSet M' ⊆ OddOrder.BG.Ch3.S10.beta N ∧
        Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
          ((M' ⊓ N).subgroupOf N) ∧
        (∀ L ∈ S14.maximalSigmaSubgroupsOfElement x,
          ∃! r : G, (r ∈ OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)) ∧
            MulAut.conj r • M' = L) := by
  have hx1 : x ≠ 1 := hxM.2
  exact (S14.sigmaLength_one_centralizer_structure hG (S14.genuineSigmaDecomposition hG) hx1
    (S14.Msigma_ell1 hG hM hxM.1 hx1)).2 hgt

/-- **The conjugates of `M` containing `x` are exactly the `σ`-maximals of `x`** (for `x ∈ M_σ^#`):
`maximalConjugatesContaining M x = 𝓜_σ(x)`.  This identifies the set on which Theorem D(3)/(4)'s
`RData` asks for sharp transitivity (`maximalConjugatesContaining`) with the set the proven structure
controls (`maximalSigmaSubgroupsOfElement`).
* `⊆`: a conjugate `N = M^g ∋ x` has `x` a `σ(N)`-element (`σ(N) = σ(M)`, `sigma_conj`), and the
  normal `σ(N)`-Hall `N_σ` absorbs the `σ(N)`-subgroup `⟨x⟩` (`sigma_subgroup_le_Msigma_of_isHall`),
  so `x ∈ N_σ`.
* `⊇`: `Theorem 14.4`'s `C_G(x)`-conjugacy (`exists_conj_centralizer_of_mem_maximalSigma`) makes any
  `N ∈ 𝓜_σ(x)` a conjugate `M^c` (`c ∈ C_G(x)`), and `x ∈ N_σ ≤ N`. -/
theorem maximalConjugatesContaining_eq_maximalSigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1) :
    maximalConjugatesContaining M x = S14.maximalSigmaSubgroupsOfElement x := by
  ext N
  constructor
  · rintro ⟨g, rfl, hxN⟩
    have hNmax : MulAut.conj g • M ∈ maximalSubgroups G :=
      S14.mem_maximalSubgroups_of_isConjugateSubgroup hM ⟨g, rfl⟩
    refine ⟨hNmax, ?_⟩
    have hxpi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma (MulAut.conj g • M))
        (Subgroup.zpowers x) := by
      intro p hp
      rw [Nat.card_zpowers] at hp
      haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      exact OddOrder.BG.Ch3.S10.sigma_conj g (S14.isPiElement_sigma_of_mem_Msigma hxMσ p hp)
    exact OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hNmax) (Subgroup.zpowers_le.mpr hxN) hxpi
      (Subgroup.mem_zpowers x)
  · rintro ⟨hNmax, hxNσ⟩
    obtain ⟨c, _, hcconj⟩ := S14.exists_conj_centralizer_of_mem_maximalSigma hG
      (S14.genuineSigmaDecomposition hG) (S14.Msigma_ell1 hG hM hxMσ hx1) ⟨hM, hxMσ⟩ ⟨hNmax, hxNσ⟩
    exact ⟨c, hcconj.symm, OddOrder.BG.Ch3.S10.Msigma_le N hxNσ⟩

/-- **If `C_G(x) ≤ M` then `M` is the unique `σ`-maximal of `x`** (`𝓜_σ(x) = {M}`, for `x ∈ M_σ^#`):
any `L ∈ 𝓜_σ(x)` is `M^c` with `c ∈ C_G(x)` (`exists_conj_centralizer_of_mem_maximalSigma`), and
`c ∈ C_G(x) ≤ M ≤ N_G(M)` gives `M^c = M`.  The easy direction of the `|𝓜_σ(x)|`-vs-`C_G(x) ⊆ M`
dichotomy — the trivial (`R(x) = 1`) branch of Theorem D(3). -/
theorem maximalSigmaSubgroupsOfElement_eq_singleton_of_centralizer_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    (hCM : Subgroup.centralizer ({x} : Set G) ≤ M) :
    S14.maximalSigmaSubgroupsOfElement x = {M} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hM, hxMσ⟩, fun L hL => ?_⟩
  obtain ⟨c, hcC, hcconj⟩ := S14.exists_conj_centralizer_of_mem_maximalSigma hG
    (S14.genuineSigmaDecomposition hG) (S14.Msigma_ell1 hG hM hxMσ hx1) ⟨hM, hxMσ⟩ hL
  rw [← hcconj]
  exact conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (hCM hcC))

/-- **`¬FittingIsTI M` produces an escaping `σ`-sharp element** (the honest reverse of
`not_fittingIsTI_of_mem_fittingSharp_of_centralizer_not_le`): if `F(M)` is not a `TI`-subgroup then
some `z ∈ M_σ#` has `C_G(z) ⊄ M`.  The `TI`-failure gives `g ∉ M` with `F(M) ⊓ F(M)^g ≠ ⊥`
(`exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI`); *every* prime dividing that
intersection lies in `σ(M)` (`mem_sigma_of_prime_dvd_card_inf_conj_fitting`), so any nonidentity `z`
in it is a `σ(M)`-element, hence `z ∈ M_σ#` (via `M`) and `z ∈ M_σ(M^g)` (via `M^g = conj g • M`,
`σ` conjugation-invariant).  Were `C_G(z) ≤ M`, the singleton
`maximalSigmaSubgroupsOfElement_eq_singleton_of_centralizer_le` would force `𝓜_σ(z) = {M}`,
contradicting `M^g ∈ 𝓜_σ(z)` (which would give `g ∈ N_G(M) = M`, against `g ∉ M`).  The reverse
reduction toward the all-type-I `FittingIsTI` argument (its remaining gap being the type-`P₂`
neighbour, BG Cor 15.9 / `escapingCentralizers_control`). -/
theorem exists_sigmaSharp_escape_of_not_fittingIsTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnotTI : ¬ S15.FittingIsTI M) :
    ∃ z : G, z ∈ S14.sigmaSharp M ∧ ¬ Subgroup.centralizer ({z} : Set G) ≤ M := by
  classical
  obtain ⟨g, hgM, hne⟩ := exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI hnotTI
  set H : Subgroup G :=
    S15.fittingInAmbient M ⊓ MulAut.conj g • S15.fittingInAmbient M with hHdef
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hne
  obtain ⟨x, hx1⟩ := hne
  have hxH : (x : G) ∈ H := SetLike.coe_mem x
  have hxinf : (x : G) ∈ S15.fittingInAmbient M ∧
      (x : G) ∈ MulAut.conj g • S15.fittingInAmbient M := Subgroup.mem_inf.mp (hHdef ▸ hxH)
  have hz1 : (x : G) ≠ 1 := fun h => hx1 (OneMemClass.coe_eq_one.mp h)
  -- `z = ↑x` is a `σ(M)`-element: every prime of `ord z` divides `|H| = |F(M) ⊓ F(M)^g|`.
  have hzpi : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) (x : G) := by
    intro p hp_mem
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hord : orderOf (x : G) ∣ Nat.card ↥H := by
      rw [Subgroup.orderOf_coe]; exact orderOf_dvd_natCard x
    exact mem_sigma_of_prime_dvd_card_inf_conj_fitting hG hM hgM hpp
      (hHdef ▸ ((Nat.dvd_of_mem_primeFactors hp_mem).trans hord))
  -- `z ∈ M_σ#` (via `M`).
  have hzM : (x : G) ∈ M := OddOrder.BG.Ch2.S08.fittingInG_le M hxinf.1
  have hzMsigma : (x : G) ∈ OddOrder.BG.Ch3.S10.Msigma M :=
    S14.mem_Msigma_of_isPiElement_sigma_of_mem hG hM hzM hzpi
  -- `M^g` maximal, `z ∈ M_σ(M^g)`.
  have hMg_max : (MulAut.conj g • M) ∈ maximalSubgroups G :=
    S14.mem_maximalSubgroups_of_isConjugateSubgroup hM ⟨g, rfl⟩
  have hzMg : (x : G) ∈ (MulAut.conj g • M) :=
    conj_smul_mono (MulAut.conj g) (OddOrder.BG.Ch2.S08.fittingInG_le M) hxinf.2
  have hzMsigmaG : (x : G) ∈ OddOrder.BG.Ch3.S10.Msigma (MulAut.conj g • M) :=
    S14.mem_Msigma_of_isPiElement_sigma_of_mem hG hMg_max hzMg
      (by rw [S14.sigma_conj_smul_eq]; exact hzpi)
  refine ⟨(x : G), ⟨hzMsigma, hz1⟩, ?_⟩
  intro hCzM
  have hsingle : S14.maximalSigmaSubgroupsOfElement (x : G) = {M} :=
    maximalSigmaSubgroupsOfElement_eq_singleton_of_centralizer_le hG hM hzMsigma hz1 hCzM
  have hMg_in : (MulAut.conj g • M) ∈ S14.maximalSigmaSubgroupsOfElement (x : G) :=
    ⟨hMg_max, hzMsigmaG⟩
  rw [hsingle, Set.mem_singleton_iff] at hMg_in
  have hgN : g ∈ Subgroup.normalizer M := mem_normalizer_of_conj_smul_eq_self hMg_in
  rw [S14.normalizer_eq_self_of_mem_maximalSubgroups hG hM] at hgN
  exact hgM hgN

/-- **Pointed sharp transitivity upgrades to full sharp transitivity** (regular action): if `R`
acts on `S` so that every `L ∈ S` is `M₀^r` for a *unique* `r ∈ R`, then `R` is sharply transitive
on `S` — for `A, B ∈ S` the unique `r ∈ R` with `B = A^r` is `r = b a⁻¹` (where `A = M₀^a`,
`B = M₀^b`).  Supplies the `ConjSharplyTransitiveOn` conjunct of `RData` from the proven structure's
"from `M`" transitivity (`signalizer_structure_of_mem_sigmaSharp`). -/
theorem conjSharplyTransitiveOn_of_pointed {R : Subgroup G} {S : Set (Subgroup G)} {M₀ : Subgroup G}
    (hbase : ∀ L ∈ S, ∃! r : G, r ∈ R ∧ MulAut.conj r • M₀ = L) :
    ConjSharplyTransitiveOn R S := by
  intro A hA B hB
  obtain ⟨a, ⟨haR, haM⟩, _⟩ := hbase A hA
  obtain ⟨b, ⟨hbR, hbM⟩, hbuniq⟩ := hbase B hB
  refine ⟨b * a⁻¹, ⟨R.mul_mem hbR (R.inv_mem haR), ?_⟩, ?_⟩
  · show B = MulAut.conj (b * a⁻¹) • A
    rw [← haM, ← mul_smul, ← map_mul, show (b * a⁻¹) * a = b by group, hbM]
  · rintro r ⟨hrR, hrA⟩
    have hrab : MulAut.conj (r * a) • M₀ = B := by
      rw [map_mul, mul_smul, haM, ← hrA]
    have hra : r * a = b := hbuniq (r * a) ⟨R.mul_mem hrR haR, hrab⟩
    rw [← hra]; group

/-- **Theorem D(3) `RData` assembly** (gated-endpoint skeleton): from the proven structure's data
(the maximal `N ≥ C_G(x)` and its sharp transitivity on `𝓜_σ(x)`) plus the two deep `M`-side inputs
(`C_M(x)` a Hall subgroup of `C_G(x)`, and the complement `R ⋊ C_M(x) = C_G(x)`, Coq parts (e)/(b)),
the four `RData M x R` conjuncts assemble for `R = N_σ ⊓ C_G(x)`: conjunct 2 (`R ◁ C_G(x)`) is
`centralizer_le_normalizer_Msigma_inf_centralizer`, conjunct 4 (sharp transitivity on
`maximalConjugatesContaining M x = 𝓜_σ(x)`) is `conjSharplyTransitiveOn_of_pointed`.  Reduces hD3 to
the two genuinely-remaining inputs. -/
theorem RData_of_inputs [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {x : G} (hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    {N : Subgroup G} (hCN : Subgroup.centralizer ({x} : Set G) ≤ N)
    (hsharp : ∀ L ∈ S14.maximalSigmaSubgroupsOfElement x,
      ∃! r : G, (r ∈ OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)) ∧
        MulAut.conj r • M = L)
    (hRhall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma N)
      ((OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
        (Subgroup.centralizer ({x} : Set G))))
    (hconj3 : Subgroup.IsComplement'
      ((M ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf (Subgroup.centralizer ({x} : Set G)))
      ((OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
        (Subgroup.centralizer ({x} : Set G)))) :
    RData M x (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)) := by
  refine ⟨?_, ?_, hconj3, ?_⟩
  · -- conjunct 1 (`C_M(x)` a Hall subgroup of `C_G(x)`): from `R` Hall + the complement, the order of
    -- `C_M(x)` (= the index of `R`) is coprime to its index (= the order of `R`).
    have hcop := hRhall.coprime_index
    rwa [hconj3.index_eq_card, Nat.coprime_comm, ← hconj3.symm.index_eq_card] at hcop
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
      (centralizer_le_normalizer_Msigma_inf_centralizer hCN)
  · rw [maximalConjugatesContaining_eq_maximalSigma hG hM hxMσ hx1]
    exact conjSharplyTransitiveOn_of_pointed hsharp

/-- **Theorem D(3) conjunct 3, the centralizer complement** (Coq Theorem 14.4(b),
`R ⋊ C_(M∩N)(x) = C(x)`): from the proven structure's `N`-complement `(N)_σ ⋊ (M ∩ N) = N`
(`hMcompl`), inside `C_G(x)` the subgroups `C_M(x) = M ⊓ C_G(x)` and `R = (N)_σ ⊓ C_G(x)` complement
each other.  This is the engine `IsComplement'.inf_centralizer_of_normalizer` (mathcomp `subcent_sdprod`)
applied with `K = (N)_σ` (normal in `N`), `H = M ∩ N`, and `a = x`: `x` normalizes `(N)_σ` (it lies in
`N` since `C_G(x) ≤ N`, and `(N)_σ ◁ N`) and `M ∩ N` (it lies in `M ∩ N`).  Discharges the one
genuinely-deep `RData` input of `RData_of_inputs`. -/
theorem signalizer_centralizer_isComplement {M N : Subgroup G} {x : G}
    (hMcompl : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
      ((M ⊓ N).subgroupOf N))
    (hCN : Subgroup.centralizer ({x} : Set G) ≤ N) (hxM : x ∈ M) :
    Subgroup.IsComplement'
      ((M ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf (Subgroup.centralizer ({x} : Set G)))
      ((OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
        (Subgroup.centralizer ({x} : Set G))) := by
  have hxN : x ∈ N := hCN (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  haveI hKnorm : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).Normal := by
    rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have haK : x ∈ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma N : Set G) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch3.S10.Msigma_le N)).mp hKnorm) hxN
  have haH : x ∈ Subgroup.normalizer ((M ⊓ N : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_inf.mpr ⟨hxM, hxN⟩)
  have hgen := hMcompl.inf_centralizer_of_normalizer hKnorm
    (OddOrder.BG.Ch3.S10.Msigma_le N) hCN haK haH
  rw [show (M ⊓ N) ⊓ Subgroup.centralizer ({x} : Set G)
      = M ⊓ Subgroup.centralizer ({x} : Set G) from by
      rw [inf_assoc, inf_eq_right.mpr hCN]] at hgen
  exact hgen.symm

/-- **BG Theorem D(3) for the `|𝓜_σ(x)| > 1` branch** (`∃ R, RData M x R`): when `x ∈ M_σ^#` has more
than one `σ`-maximal, the proven `signalizer_structure_of_mem_sigmaSharp` supplies the unique maximal
`N ≥ C_G(x)`, the Hall property of `R = (N)_σ ⊓ C_G(x)` and the sharp transitivity from `M`; the
centralizer complement (conjunct 3) is `signalizer_centralizer_isComplement`, and `RData_of_inputs`
assembles all four `RData` conjuncts.  This is the genuinely-deep half of `hD3`; the remaining
`|𝓜_σ(x)| ≤ 1` branch needs `C_G(x) ≤ M` (the deep converse of
`maximalSigmaSubgroupsOfElement_eq_singleton_of_centralizer_le`). -/
theorem RData_of_gt_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {x : G} (hxM : x ∈ S14.sigmaSharp M)
    (hgt : 1 < (S14.maximalSigmaSubgroupsOfElement x).ncard) :
    ∃ R : Subgroup G, RData M x R := by
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hxM.1
  have hx1 : x ≠ 1 := hxM.2
  have hxM_mem : x ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hxMσ
  obtain ⟨N, hN, -⟩ := signalizer_structure_of_mem_sigmaSharp hG hM hxM hgt
  obtain ⟨_, hCN, _, hRhall, _, _, hforall⟩ := hN
  obtain ⟨_, _, hMcompl, hMsharp⟩ := hforall M ⟨hM, hxMσ⟩
  exact ⟨_, RData_of_inputs hG hM hxMσ hx1 hCN hMsharp hRhall
    (signalizer_centralizer_isComplement hMcompl hCN hxM_mem)⟩

/-- **BG Theorem D(3), `|R(x)| = |𝓜_σ(x)|`** (Coq `oR`, the cardinality conjunct of the
`FT_signalizer_context` first block): `R` acts sharply transitively (`ConjSharplyTransitiveOn`) on
`maximalConjugatesContaining M x = 𝓜_σ(x)`, and `R ≤ C_G(x)` makes that action *closed* on `𝓜_σ(x)`
(for `r ∈ R ≤ C_G(x)`, `Mʳ ∈ 𝓜_σ(x)` since `r⁻¹xr = x ∈ M`), so `r ↦ Mʳ` is a bijection
`R ≃ 𝓜_σ(x)` (surjective + injective from the sharp `∃!`), giving `|R| = |𝓜_σ(x)|`.  This is the
count behind BG Theorem E's `|M̃| = (|M_σ| − 1)·[G:M]` (Lemma 14.5(c)). -/
theorem card_signalizer_eq_card_maximalSigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G}
    (hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1) {R : Subgroup G}
    (hRle : R ≤ Subgroup.centralizer ({x} : Set G))
    (hsharp : ConjSharplyTransitiveOn R (maximalConjugatesContaining M x)) :
    Nat.card ↥R = (S14.maximalSigmaSubgroupsOfElement x).ncard := by
  classical
  have hSeq : maximalConjugatesContaining M x = S14.maximalSigmaSubgroupsOfElement x :=
    maximalConjugatesContaining_eq_maximalSigma hG hM hxMσ hx1
  have hMmem : M ∈ maximalConjugatesContaining M x := by rw [hSeq]; exact ⟨hM, hxMσ⟩
  -- closure: `r ∈ R ⟹ Mʳ ∈ maximalConjugatesContaining M x` (uses `R ≤ C_G(x)`).
  have hclosure : ∀ r : G, r ∈ R → MulAut.conj r • M ∈ maximalConjugatesContaining M x := by
    intro r hr
    refine ⟨r, rfl, ?_⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hcalc : (MulAut.conj r)⁻¹ • x = r⁻¹ * x * r := by
      change (MulAut.conj r).symm x = _; rw [MulAut.conj_symm_apply]
    rw [hcalc]
    have hcx : r * x = x * r := Subgroup.mem_centralizer_singleton_iff.mp (hRle hr)
    have hfix : r⁻¹ * x * r = x := by rw [mul_assoc, ← hcx]; group
    rw [hfix]; exact OddOrder.BG.Ch3.S10.Msigma_le M hxMσ
  -- bijection `↥R ≃ ↥(maximalConjugatesContaining M x)`.
  let f : ↥R → ↥(maximalConjugatesContaining M x) :=
    fun r => ⟨MulAut.conj (r : G) • M, hclosure r r.2⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun r₁ r₂ hf => ?_, fun B => ?_⟩
    · have hval : MulAut.conj (r₁ : G) • M = MulAut.conj (r₂ : G) • M := Subtype.ext_iff.mp hf
      obtain ⟨_, _, huniq⟩ := hsharp M hMmem (MulAut.conj (r₁ : G) • M) (hclosure r₁ r₁.2)
      have e1 := huniq (r₁ : G) ⟨r₁.2, rfl⟩
      have e2 := huniq (r₂ : G) ⟨r₂.2, hval⟩
      exact Subtype.ext (e1.trans e2.symm)
    · obtain ⟨r, ⟨hrR, hrB⟩, _⟩ := hsharp M hMmem (B : Subgroup G) B.2
      exact ⟨⟨r, hrR⟩, Subtype.ext hrB.symm⟩
  rw [Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_coe_set_eq, hSeq]

/-- **BG Lemma 14.5(a), `σ`-cover disjointness** (Coq `sigma_cover_disjoint`, `_of_inputs` form): for
two distinct `σ`-length-one elements `x, y` with signalizer data, the cosets `x·R(x)` and `y·R(y)`
(`R(·) = (N_·)_σ ⊓ C_G(·)`) are disjoint.  If `g = x·r = y·s` were common, the `σ`-decomposition
`{x} ∪ {r}^# = σ(g) = {y} ∪ {s}^#` (`sigma_cover_decomposition_signalizer`) forces `y = r` (as `y ≠ x`)
and `s = x`; so `y ∈ (N_x)_σ` puts `N_x ∈ 𝓜_σ(y)`, and `x ∈ R(y) ∩ (N_x ⊓ C_G(y))` lands in the
trivial intersection of the `y`-complement (`signalizer_centralizer_isComplement` at `M' = N_x`),
forcing `x = 1` — contradiction.  The deep core of the `R(x)`-cover trivIset behind Lemma 14.5(c). -/
theorem sigma_cover_disjoint_of_inputs [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {Mx Nx My Ny : Subgroup G} (hMx : Mx ∈ maximalSubgroups G) (hNx : Nx ∈ maximalSubgroups G)
    (hMy : My ∈ maximalSubgroups G) (hNy : Ny ∈ maximalSubgroups G) {x y : G}
    (hxMx : x ∈ OddOrder.BG.Ch3.S10.Msigma Mx) (hx1 : x ≠ 1)
    (hyMy : y ∈ OddOrder.BG.Ch3.S10.Msigma My) (hy1 : y ≠ 1)
    (hxτ2 : ∀ p ∈ S14.piSet (Subgroup.closure ({x} : Set G)), p ∈ tau2 Nx)
    (hyτ2 : ∀ p ∈ S14.piSet (Subgroup.closure ({y} : Set G)), p ∈ tau2 Ny)
    (hCxNx : Subgroup.centralizer ({x} : Set G) ≤ Nx)
    (hCyNy : Subgroup.centralizer ({y} : Set G) ≤ Ny)
    (hy_compl : ∀ M' ∈ S14.maximalSigmaSubgroupsOfElement y,
      Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma Ny).subgroupOf Ny)
        ((M' ⊓ Ny).subgroupOf Ny))
    (hxy : x ≠ y) :
    Disjoint
      {g : G | ∃ r ∈ (OddOrder.BG.Ch3.S10.Msigma Nx ⊓ Subgroup.centralizer ({x} : Set G)),
        g = x * r}
      {g : G | ∃ s ∈ (OddOrder.BG.Ch3.S10.Msigma Ny ⊓ Subgroup.centralizer ({y} : Set G)),
        g = y * s} := by
  rw [Set.disjoint_left]
  rintro g ⟨r, hr, rfl⟩ ⟨s, hs, hgs⟩
  obtain ⟨hrMσ, hrC⟩ := Subgroup.mem_inf.mp hr
  obtain ⟨hsMσ, hsC⟩ := Subgroup.mem_inf.mp hs
  have hrcomm : Commute x r := (Subgroup.mem_centralizer_singleton_iff.mp hrC).symm
  have hscomm : Commute y s := (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  -- `σ`-decompositions of the two cover elements.
  have hdecx : S14.sigmaDecomposition (x * r) = insert x ({r} \ {1}) :=
    S14.sigma_cover_decomposition_signalizer hG hMx hNx hxMx hx1 hxτ2 hrMσ hrcomm
  -- `y` is a `σ`-part of `g = x·r` (since `g = y·s`).
  have hymem : y ∈ S14.sigmaDecomposition (x * r) := by
    rw [hgs]
    exact S14.mem_sigma_cover_decomposition_signalizer hG hMy hNy hyMy hy1 hyτ2 hsMσ hscomm
  rw [hdecx, Set.mem_insert_iff] at hymem
  have hyr : y = r := by
    rcases hymem with h | h
    · exact absurd h.symm hxy
    · exact Set.mem_singleton_iff.mp h.1
  -- `N_x ∈ 𝓜_σ(y)` and `s = x`.
  have hyMσNx : y ∈ OddOrder.BG.Ch3.S10.Msigma Nx := hyr ▸ hrMσ
  have hNxMSy : Nx ∈ S14.maximalSigmaSubgroupsOfElement y := ⟨hNx, hyMσNx⟩
  have hsx : s = x := by
    rw [← hyr] at hgs
    have hcomm_xy : x * y = y * x := hyr.symm ▸ hrcomm
    rw [hcomm_xy] at hgs
    exact (mul_left_cancel hgs).symm
  -- final contradiction via the `y`-centralizer complement at `M' = N_x`.
  have hxRy : x ∈ OddOrder.BG.Ch3.S10.Msigma Ny ⊓ Subgroup.centralizer ({y} : Set G) := hsx ▸ hs
  have hxCy : x ∈ Subgroup.centralizer ({y} : Set G) := (Subgroup.mem_inf.mp hxRy).2
  have hyNx : y ∈ Nx := OddOrder.BG.Ch3.S10.Msigma_le Nx hyMσNx
  have hxNx : x ∈ Nx := hCxNx (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hcompl_C := signalizer_centralizer_isComplement (hy_compl Nx hNxMSy) hCyNy hyNx
  have hmem : (⟨x, hxCy⟩ : Subgroup.centralizer ({y} : Set G)) ∈
      ((Nx ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf
        (Subgroup.centralizer ({y} : Set G))) ⊓
      ((OddOrder.BG.Ch3.S10.Msigma Ny ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf
        (Subgroup.centralizer ({y} : Set G))) :=
    Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hxNx, hxCy⟩),
        Subgroup.mem_subgroupOf.mpr hxRy⟩
  rw [hcompl_C.disjoint.eq_bot, Subgroup.mem_bot] at hmem
  exact hx1 (Subtype.ext_iff.mp hmem)

end OddOrder.BG.Ch4.S16
