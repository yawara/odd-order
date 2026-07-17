import OddOrder.Peterfalvi.S09_NonexistenceCertain.TwoFamilies

/-!
# CharacterEstimate

Prefix-split from `OddOrder.Peterfalvi.S09_NonexistenceCertain.FrobeniusFamily` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# Frobenius family — §7 の主定理へ向けた family 構成と assembly

Split from the former monolithic `OddOrder.Peterfalvi.S09_NonexistenceCertain` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S09
open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)
open OddOrder.GroupTheory (IsTISubset)
open OddOrder.RepresentationTheory
open scoped Pointwise

variable {G : Type*} [Group G]


namespace FrobeniusFamily

variable {k : ℕ}

/-- `(H_i^#)^G`: the set of `G`-conjugates of nonidentity elements of the `i`-th
kernel `H_i`. -/
def kernelSpread (F : FrobeniusFamily G k) (i : Fin k) : Set G :=
  {x : G | ∃ g : G, g * x * g⁻¹ ∈ (F.H i : Set G) \ {1}}

/-- **(7.10)(d).** `G₀ = G - ⋃_i (H_i^#)^G`: the elements not conjugate into any
kernel. -/
def G0 (F : FrobeniusFamily G k) : Set G :=
  {x : G | ∀ i, x ∉ F.kernelSpread i}

theorem mem_G0_iff (F : FrobeniusFamily G k) {x : G} :
    x ∈ F.G0 ↔ ∀ i, x ∉ F.kernelSpread i := Iff.rfl

/-- The implementation of kernelSpread is the usual conjugacy closure of H_i^#. -/
lemma mem_kernelSpread_iff_conjugatesOfSet (F : FrobeniusFamily G k) (i : Fin k)
    {x : G} :
    x ∈ F.kernelSpread i ↔ x ∈ Group.conjugatesOfSet ((F.H i : Set G) \ {1}) := by
  constructor
  · rintro ⟨g, hg⟩
    rw [Group.mem_conjugatesOfSet_iff]
    refine ⟨g * x * g⁻¹, hg, ?_⟩
    rw [isConj_iff]
    refine ⟨g⁻¹, ?_⟩
    group
  · intro hx
    rcases Group.mem_conjugatesOfSet_iff.mp hx with ⟨y, hy, hconj⟩
    rcases isConj_iff.mp hconj with ⟨g, hg⟩
    refine ⟨g⁻¹, ?_⟩
    rw [← hg]
    have hback : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    simpa [hback] using hy

lemma kernelSpread_eq_conjugatesOfSet (F : FrobeniusFamily G k) (i : Fin k) :
    F.kernelSpread i = Group.conjugatesOfSet ((F.H i : Set G) \ {1}) := by
  ext x
  exact F.mem_kernelSpread_iff_conjugatesOfSet i

lemma one_not_mem_kernelSpread (F : FrobeniusFamily G k) (i : Fin k) :
    (1 : G) ∉ F.kernelSpread i := by
  rintro ⟨g, hg⟩
  exact hg.2 (by simp)

lemma one_mem_G0 (F : FrobeniusFamily G k) : (1 : G) ∈ F.G0 := by
  intro i
  exact F.one_not_mem_kernelSpread i

open scoped Classical in
/-- The identity contribution in Peterfalvi (7.10): since `1 ∈ G₀`, any class
function with `1 ≤ |χ(1)|²` contributes at least `1` to the `G₀` norm sum. -/
lemma one_le_G0_norm_sum_of_one_le_norm_one [Fintype G]
    (F : FrobeniusFamily G k) (χ : ClassFunction G ℂ)
    (hone : (1 : ℝ) ≤ ‖(χ : G → ℂ) 1‖ ^ 2) :
    (1 : ℝ) ≤
      ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
        ‖(χ : G → ℂ) g‖ ^ 2 := by
  classical
  have hmem : (1 : G) ∈ Finset.univ.filter (fun g : G => g ∈ F.G0) := by
    simp [F.one_mem_G0]
  exact hone.trans
    (Finset.single_le_sum (f := fun g : G => ‖(χ : G → ℂ) g‖ ^ 2)
      (fun g _ => sq_nonneg _) hmem)

/-- A signed irreducible character has `|χ(1)|² ≥ 1`.  This is the numerical
content behind the `χ₁(1)^2` term in Peterfalvi (7.10). -/
lemma one_le_norm_sq_apply_one_of_signed_irreducible
    (χ : ClassFunction G ℂ) (ε : ℤ)
    (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hε : ε = 1 ∨ ε = -1)
    (hχ_one :
      (χ : G → ℂ) 1 =
        (ε : ℂ) * ((ξ : ClassFunction G ℂ) : G → ℂ) 1) :
    (1 : ℝ) ≤ ‖(χ : G → ℂ) 1‖ ^ 2 := by
  obtain ⟨d, hdpos, hd⟩ :=
    OddOrder.RepresentationTheory.irreducibleCharacter_apply_one_eq_pos_natCast ξ
  rw [hχ_one, hd]
  rcases hε with rfl | rfl
  · rw [Int.cast_one, one_mul, Complex.norm_natCast]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    nlinarith
  · rw [Int.cast_neg, Int.cast_one, neg_one_mul, norm_neg, Complex.norm_natCast]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    nlinarith

open scoped Classical in
/-- Signed-irreducible form of the `G₀` identity contribution used in (7.10). -/
lemma one_le_G0_norm_sum_of_signed_irreducible [Fintype G]
    (F : FrobeniusFamily G k) (χ : ClassFunction G ℂ) (ε : ℤ)
    (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hε : ε = 1 ∨ ε = -1)
    (hχ : χ = ε • (ξ : ClassFunction G ℂ)) :
    (1 : ℝ) ≤
      ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
        ‖(χ : G → ℂ) g‖ ^ 2 := by
  have hχ_one :
      (χ : G → ℂ) 1 =
        (ε : ℂ) * ((ξ : ClassFunction G ℂ) : G → ℂ) 1 := by
    rw [hχ, ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ),
      ClassFunction.smul_apply]
  exact F.one_le_G0_norm_sum_of_one_le_norm_one χ
    (one_le_norm_sq_apply_one_of_signed_irreducible χ ε ξ hε hχ_one)

/-- Elements of L_i = N_G(H_i) conjugate H_i to itself. -/
lemma mem_kernel_conj_iff_of_mem_L (F : FrobeniusFamily G k) (i : Fin k)
    {g x : G} (hg : g ∈ F.L i) :
    g * x * g⁻¹ ∈ F.H i ↔ x ∈ F.H i := by
  have hnorm : g ∈ Subgroup.normalizer (F.H i : Set G) := by
    rw [← F.normalizer_eq i]
    exact hg
  exact (Subgroup.mem_normalizer_iff.mp hnorm x).symm

/-- Elements of L_i conjugate the sharp kernel H_i^# to itself. -/
lemma mem_kernel_sharp_conj_iff_of_mem_L (F : FrobeniusFamily G k) (i : Fin k)
    {g x : G} (hg : g ∈ F.L i) :
    g * x * g⁻¹ ∈ (F.H i : Set G) \ {1} ↔ x ∈ (F.H i : Set G) \ {1} := by
  constructor
  · intro hx
    exact ⟨(F.mem_kernel_conj_iff_of_mem_L i hg).mp hx.1, by
      intro hx1
      exact hx.2 (by simpa using hx1)⟩
  · intro hx
    exact ⟨(F.mem_kernel_conj_iff_of_mem_L i hg).mpr hx.1, by
      intro hconj
      exact hx.2 (conj_eq_one_iff.mp hconj)⟩

/-- **The Peterfalvi (7.1) Dade ρ-setup for the `i`-th family member.**  The kernel `H_i` of the
`i`-th Frobenius subgroup has `H_i^#` a TI-subset of `G` (`isTI`) with normalizer `L_i`
(`normalizer_eq`, so `L_i` conjugates `H_i^#` to itself, `mem_kernel_sharp_conj_iff_of_mem_L`), so
`Hypothesis71.of_isTISubset` builds the full (7.1) datum `Hypothesis71 G (H_i^#) L_i` (with all
`H(a) = ⊥` and the canonical Dade isometry `τ`).  This is the per-member (7.1) input assembled by
(7.4)/(7.10). -/
noncomputable def hypothesis71 [Fintype G] (F : FrobeniusFamily G k) (i : Fin k) :
    Hypothesis71 G (OddOrder.Peterfalvi.S04.sharp (F.H i : Set G)) (F.L i) :=
  Hypothesis71.of_isTISubset
    (fun x hx => OddOrder.Peterfalvi.S04.mem_sharp.mpr
      ⟨Set.mem_univ x, (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).2⟩)
    (fun _x hx => F.kernel_le i (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).1)
    (fun l _a ha => (F.mem_kernel_sharp_conj_iff_of_mem_L i l.2).mpr ha)
    (F.isTI i)

/-- **The Dade support of the `i`-th (7.1) datum is the kernel spread** `(H_i^#)^G`.  For the
TI-subset construction every local subgroup `H(a) = ⊥`, so each coset `aH(a) = {a}`, and the Dade
support `⋃_{a ∈ H_i^#} {a}^G` is exactly the conjugacy spread `(H_i^#)^G = kernelSpread i`.  This
identifies the (7.4) disjointness hypothesis `Disjoint (dadeSupport i) (dadeSupport j)` with the
already-proven `kernelSpread_disjoint`. -/
lemma dadeSupport_hypothesis71_eq_kernelSpread [Fintype G] (F : FrobeniusFamily G k) (i : Fin k) :
    (F.hypothesis71 i).hyp.dadeSupport = F.kernelSpread i := by
  rw [F.kernelSpread_eq_conjugatesOfSet i]
  ext g
  rw [OddOrder.Peterfalvi.S04.Hypothesis.mem_dadeSupport_iff, Group.mem_conjugatesOfSet_iff]
  constructor
  · rintro ⟨a, h, hh, hconj⟩
    have hh1 : h = 1 := Subgroup.mem_bot.mp hh
    subst hh1
    exact ⟨a.1, a.2, by simpa using hconj⟩
  · rintro ⟨y, hy, hconj⟩
    exact ⟨⟨y, hy⟩, 1, Subgroup.one_mem _, by simpa using hconj⟩

/-- TI for H_i^# says that any element carrying one sharp-kernel element back
into H_i^# already lies in L_i. -/
lemma mem_L_of_mem_kernel_sharp_of_conj_mem_kernel_sharp
    (F : FrobeniusFamily G k) (i : Fin k) {g x : G}
    (hx : x ∈ (F.H i : Set G) \ {1})
    (hconj : g * x * g⁻¹ ∈ (F.H i : Set G) \ {1}) :
    g ∈ F.L i :=
  F.isTI i g ⟨x, hx, hconj⟩

/-- Conjugate images of `H_i^#` are equal when the conjugators differ by
an element of `L_i = N_G(H_i)`. -/
lemma kernel_sharp_conj_image_eq_of_inv_mul_mem_L
    (F : FrobeniusFamily G k) (i : Fin k) {g h : G}
    (hmem : h⁻¹ * g ∈ F.L i) :
    ((fun x : G => g * x * g⁻¹) '' ((F.H i : Set G) \ {1})) =
      ((fun x : G => h * x * h⁻¹) '' ((F.H i : Set G) \ {1})) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(h⁻¹ * g) * a * (h⁻¹ * g)⁻¹, ?_, ?_⟩
    · exact (F.mem_kernel_sharp_conj_iff_of_mem_L i hmem).mpr ha
    · group
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(h⁻¹ * g)⁻¹ * a * (h⁻¹ * g), ?_, ?_⟩
    · have hinv : (h⁻¹ * g)⁻¹ ∈ F.L i := (F.L i).inv_mem hmem
      simpa using (F.mem_kernel_sharp_conj_iff_of_mem_L i hinv).mpr ha
    · group

/-- Distinct `L_i`-cosets give disjoint conjugate images of `H_i^#`. -/
lemma disjoint_kernel_sharp_conj_image_of_inv_mul_notMem_L
    (F : FrobeniusFamily G k) (i : Fin k) {g h : G}
    (hnot : h⁻¹ * g ∉ F.L i) :
    Disjoint ((fun x : G => g * x * g⁻¹) '' ((F.H i : Set G) \ {1}))
      ((fun x : G => h * x * h⁻¹) '' ((F.H i : Set G) \ {1})) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hb_eq⟩
  have hconj : (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ ∈ (F.H i : Set G) \ {1} := by
    have hb_eq' : h * b * h⁻¹ = g * a * g⁻¹ := by
      simpa only using hb_eq
    have hab0 : h⁻¹ * (g * a * g⁻¹) * h = b := by
      rw [← hb_eq']
      group
    have hab : (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ = b := by
      calc
        (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * a * g⁻¹) * h := by group
        _ = b := hab0
    rw [hab]
    exact hb
  exact hnot (F.mem_L_of_mem_kernel_sharp_of_conj_mem_kernel_sharp i ha hconj)

/-- A centralizer of a nonidentity kernel element is contained in the corresponding
normalizer L_i. -/
lemma centralizer_le_L_of_mem_kernel_sharp (F : FrobeniusFamily G k) (i : Fin k)
    {x : G} (hx : x ∈ (F.H i : Set G) \ {1}) :
    Subgroup.centralizer ({x} : Set G) ≤ F.L i := by
  intro g hg
  refine F.mem_L_of_mem_kernel_sharp_of_conj_mem_kernel_sharp i hx ?_
  have hcomm : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hconj : g * x * g⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr hcomm
  simpa [hconj] using hx

/-- Inside H_i^#, ambient conjugacy is already L_i-conjugacy. -/
lemma exists_L_conj_of_isConj_kernel_sharp (F : FrobeniusFamily G k) (i : Fin k)
    {x y : G} (hx : x ∈ (F.H i : Set G) \ {1})
    (hy : y ∈ (F.H i : Set G) \ {1}) (hxy : IsConj x y) :
    ∃ l : F.L i, (l : G) * x * (l : G)⁻¹ = y := by
  rcases isConj_iff.mp hxy with ⟨g, hg⟩
  exact ⟨⟨g, F.mem_L_of_mem_kernel_sharp_of_conj_mem_kernel_sharp i hx (by
    simpa [hg] using hy)⟩, hg⟩

/-- The sharp kernel H_i^# has cardinality |H_i| - 1. -/
lemma ncard_kernel_sharp [Finite G] (F : FrobeniusFamily G k) (i : Fin k) :
    ((F.H i : Set G) \ ({1} : Set G)).ncard = Nat.card (F.H i) - 1 := by
  have hHcard : (F.H i : Set G).ncard = Nat.card (F.H i) := by
    rw [← Nat.card_coe_set_eq]
    rfl
  have h1_mem : (1 : G) ∈ (F.H i : Set G) := (F.H i).one_mem
  rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr h1_mem) (Set.finite_singleton _),
    Set.ncard_singleton, hHcard]

/-- A conjugate image of `H_i^#` has cardinality `|H_i| - 1`. -/
lemma ncard_kernel_sharp_conj_image [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) (g : G) :
    (((fun x : G => g * x * g⁻¹) '' ((F.H i : Set G) \ {1})).ncard =
      Nat.card (F.H i) - 1) := by
  rw [Set.ncard_image_of_injective _]
  · exact F.ncard_kernel_sharp i
  · intro a b hab
    have hcancel := congrArg (fun z : G => g⁻¹ * z * g) hab
    simpa using hcancel

/-- `kernelSpread i` is the disjoint union, indexed by `G ⧸ L_i`, of the
conjugate images of `H_i^#` from a choice of coset representatives. -/
lemma kernelSpread_eq_iUnion_quotient (F : FrobeniusFamily G k) (i : Fin k) :
    F.kernelSpread i =
      ⋃ q : G ⧸ F.L i,
        ((fun x : G => (Quotient.out q : G) * x * (Quotient.out q : G)⁻¹) ''
          ((F.H i : Set G) \ {1})) := by
  ext x
  constructor
  · rintro ⟨a, ha⟩
    let g : G := a⁻¹
    let q : G ⧸ F.L i := ⟦g⟧
    have hxg :
        x ∈ ((fun y : G => g * y * g⁻¹) '' ((F.H i : Set G) \ {1})) := by
      refine ⟨a * x * a⁻¹, ha, ?_⟩
      simp only [g]
      group
    have hout_mem : (Quotient.out q : G)⁻¹ * g ∈ F.L i := by
      have hq : (⟦(Quotient.out q : G)⟧ : G ⧸ F.L i) = ⟦g⟧ := by
        exact Quotient.out_eq' q
      exact QuotientGroup.leftRel_apply.mp (Quotient.exact' hq)
    have himg := F.kernel_sharp_conj_image_eq_of_inv_mul_mem_L i
      (g := g) (h := (Quotient.out q : G)) hout_mem
    exact Set.mem_iUnion.mpr ⟨q, himg ▸ hxg⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨q, hxq⟩
    rcases hxq with ⟨a, ha, rfl⟩
    refine ⟨(Quotient.out q : G)⁻¹, ?_⟩
    convert ha using 1
    group

/-- The quotient-indexed conjugate images of `H_i^#` are pairwise disjoint. -/
lemma kernel_sharp_conj_image_quotient_pairwiseDisjoint
    (F : FrobeniusFamily G k) (i : Fin k) :
    Pairwise (Function.onFun Disjoint fun q : G ⧸ F.L i =>
      ((fun x : G => (Quotient.out q : G) * x * (Quotient.out q : G)⁻¹) ''
        ((F.H i : Set G) \ {1}))) := by
  intro q r hqr
  apply F.disjoint_kernel_sharp_conj_image_of_inv_mul_notMem_L i
  intro hmem
  have hrel : (QuotientGroup.leftRel (F.L i)) (Quotient.out r : G)
      (Quotient.out q : G) := by
    rw [QuotientGroup.leftRel_apply]
    exact hmem
  have hrq : r = q := Quotient.out_equiv_out.mp hrel
  exact hqr hrq.symm

/-- Cardinality of a kernel spread: `|(H_i^#)^G| = [G : L_i] (|H_i| - 1)`. -/
lemma ncard_kernelSpread_eq_index_mul [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (F.kernelSpread i).ncard = (F.L i).index * (Nat.card (F.H i) - 1) := by
  classical
  letI : Fintype (G ⧸ F.L i) := Fintype.ofFinite _
  let S : G ⧸ F.L i → Set G := fun q =>
    ((fun x : G => (Quotient.out q : G) * x * (Quotient.out q : G)⁻¹) ''
      ((F.H i : Set G) \ {1}))
  have hpair : Pairwise (Function.onFun Disjoint S) := by
    simpa [S] using F.kernel_sharp_conj_image_quotient_pairwiseDisjoint i
  have h_union : (⋃ q : G ⧸ F.L i, S q).ncard =
      ∑ᶠ q : G ⧸ F.L i, (S q).ncard :=
    Set.ncard_iUnion_of_finite (s := S) (fun _ => Set.toFinite _) hpair
  have h_sum : ∑ᶠ q : G ⧸ F.L i, (S q).ncard =
      (F.L i).index * (Nat.card (F.H i) - 1) := by
    rw [finsum_eq_sum_of_fintype]
    simp_rw [S, F.ncard_kernel_sharp_conj_image]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    norm_num
  rw [F.kernelSpread_eq_iUnion_quotient i, h_union, h_sum]

/-- Cardinality of a kernel spread as a `Nat.card` identity. -/
lemma card_kernelSpread_eq_index_mul [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    Nat.card (F.kernelSpread i) = (F.L i).index * (Nat.card (F.H i) - 1) := by
  rw [Nat.card_coe_set_eq]
  exact F.ncard_kernelSpread_eq_index_mul i

lemma ne_one_of_mem_kernelSpread (F : FrobeniusFamily G k) {i : Fin k} {x : G}
    (hx : x ∈ F.kernelSpread i) : x ≠ 1 := by
  rintro rfl
  exact F.one_not_mem_kernelSpread i hx

lemma orderOf_dvd_card_kernel_of_mem_kernelSpread [Finite G]
    (F : FrobeniusFamily G k) {i : Fin k} {x : G}
    (hx : x ∈ F.kernelSpread i) : orderOf x ∣ Nat.card (F.H i) := by
  rcases hx with ⟨g, hg⟩
  have hsub : orderOf (⟨g * x * g⁻¹, hg.1⟩ : F.H i) ∣ Nat.card (F.H i) :=
    orderOf_dvd_natCard _
  have hy_dvd : orderOf (g * x * g⁻¹) ∣ Nat.card (F.H i) := by
    simpa [Subgroup.orderOf_mk] using hsub
  have hsc : SemiconjBy g x (g * x * g⁻¹) := by
    rw [SemiconjBy]
    group
  have horder : orderOf x = orderOf (g * x * g⁻¹) := SemiconjBy.orderOf_eq g hsc
  simpa [horder] using hy_dvd

/-- `(H_i^#)^G` is closed under ambient conjugation. -/
lemma kernelSpread_conj_mem (F : FrobeniusFamily G k) (i : Fin k)
    (g : G) {x : G} (hx : x ∈ F.kernelSpread i) :
    g * x * g⁻¹ ∈ F.kernelSpread i := by
  rcases hx with ⟨a, ha⟩
  refine ⟨a * g⁻¹, ?_⟩
  have hconj : (a * g⁻¹) * (g * x * g⁻¹) * (a * g⁻¹)⁻¹ = a * x * a⁻¹ := by
    group
  rwa [hconj]

lemma mem_kernelSpread_conj_iff (F : FrobeniusFamily G k) (i : Fin k)
    (g x : G) :
    g * x * g⁻¹ ∈ F.kernelSpread i ↔ x ∈ F.kernelSpread i := by
  constructor
  · intro hx
    have hback := F.kernelSpread_conj_mem i g⁻¹ hx
    simpa [mul_assoc] using hback
  · intro hx
    exact F.kernelSpread_conj_mem i g hx

/-- `G₀`, the complement of the conjugate spreads, is conjugation-invariant. -/
lemma G0_conj_mem (F : FrobeniusFamily G k) (g : G) {x : G}
    (hx : x ∈ F.G0) : g * x * g⁻¹ ∈ F.G0 := by
  intro i hsp
  have hxsp : x ∈ F.kernelSpread i := by
    have hback := F.kernelSpread_conj_mem i g⁻¹ hsp
    simpa [mul_assoc] using hback
  exact hx i hxsp

lemma mem_G0_conj_iff (F : FrobeniusFamily G k) (g x : G) :
    g * x * g⁻¹ ∈ F.G0 ↔ x ∈ F.G0 := by
  constructor
  · intro hx
    have hback := F.G0_conj_mem g⁻¹ hx
    simpa [mul_assoc] using hback
  · intro hx
    exact F.G0_conj_mem g hx

/-- Distinct kernel spreads in Peterfalvi (7.10) are disjoint.  Any element in
their intersection has order dividing both coprime kernel orders, hence is the
identity, contradicting membership in a sharp conjugate spread. -/
lemma kernelSpread_disjoint [Finite G] (F : FrobeniusFamily G k)
    {i j : Fin k} (hij : i ≠ j) : Disjoint (F.kernelSpread i) (F.kernelSpread j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hcop : Nat.Coprime (orderOf x) (Nat.card (F.H j)) :=
    Nat.Coprime.coprime_dvd_left
      (F.orderOf_dvd_card_kernel_of_mem_kernelSpread hxi) (F.coprime_kernel hij)
  have horder_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl
      (F.orderOf_dvd_card_kernel_of_mem_kernelSpread hxj)
  exact F.ne_one_of_mem_kernelSpread hxi (orderOf_eq_one_iff.mp horder_one)

lemma kernelSpread_pairwiseDisjoint [Finite G] (F : FrobeniusFamily G k) :
    ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint F.kernelSpread := by
  intro i _hi j _hj hij
  exact F.kernelSpread_disjoint hij

/-- **The (7.4) `FamilyHypothesis71` of a Frobenius family** (Peterfalvi (7.10)(a)-(c) ⟹ (7.4)).
Each member `i` supplies the (7.1) datum `Hypothesis71 G (H_i^#) L_i` (`hypothesis71`), whose Dade map
is a genuine isometry (`isDadeIsometry_of_isDadeMap`, from `isDadeMap` + `HConjInvariant`); the
supports `A_i^{τ_i} = dadeSupport_i = (H_i^#)^G` are pairwise disjoint by the coprime-kernel
`kernelSpread_disjoint` (via `dadeSupport_hypothesis71_eq_kernelSpread`).  This assembles the (7.4)
input consumed by the (7.5)/(7.10) `characterEstimateData_of_family71_*` machinery. -/
noncomputable def familyHypothesis71 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) : FamilyHypothesis71 G k where
  L := F.L
  A := fun i => OddOrder.Peterfalvi.S04.sharp (F.H i : Set G)
  fintypeL := fun i => Fintype.ofFinite _
  invertibleL := fun i => invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L i)).ne')
  hyp71 := fun i => F.hypothesis71 i
  isDadeIsometry := fun i => by
    letI : Fintype ↥(F.L i) := Fintype.ofFinite _
    letI : Invertible (Nat.card ↥(F.L i) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L i)).ne')
    exact OddOrder.Peterfalvi.S04.isDadeIsometry_of_isDadeMap (F.hypothesis71 i).hyp
      (F.hypothesis71 i).τ (F.hypothesis71 i).isDadeMap (F.hypothesis71 i).hConjInvariant
  pairwise_disjoint := fun i j hij => by
    rw [F.dadeSupport_hypothesis71_eq_kernelSpread i, F.dadeSupport_hypothesis71_eq_kernelSpread j]
    exact F.kernelSpread_disjoint hij

lemma G0_disjoint_kernelSpread (F : FrobeniusFamily G k) (i : Fin k) :
    Disjoint F.G0 (F.kernelSpread i) := by
  rw [Set.disjoint_left]
  intro x hx hxi
  exact hx i hxi

lemma kernelSpread_disjoint_G0 (F : FrobeniusFamily G k) (i : Fin k) :
    Disjoint (F.kernelSpread i) F.G0 :=
  (F.G0_disjoint_kernelSpread i).symm

lemma not_mem_G0_iff (F : FrobeniusFamily G k) {x : G} :
    x ∉ F.G0 ↔ ∃ i, x ∈ F.kernelSpread i := by
  simp [G0]

lemma mem_G0_or_exists_mem_kernelSpread (F : FrobeniusFamily G k) (x : G) :
    x ∈ F.G0 ∨ ∃ i, x ∈ F.kernelSpread i := by
  by_cases hx : x ∈ F.G0
  · exact Or.inl hx
  · exact Or.inr ((F.not_mem_G0_iff).mp hx)

/-- The sets `G₀` and the pairwise-disjoint kernel spreads partition the ambient
group.  This is the cardinality form of Peterfalvi (7.10)(d). -/
lemma card_eq_card_G0_add_sum_card_kernelSpread [Finite G]
    (F : FrobeniusFamily G k) :
    Nat.card G = Nat.card F.G0 + ∑ i : Fin k, Nat.card (F.kernelSpread i) := by
  classical
  letI := Fintype.ofFinite G
  have h_disjFin :
      ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        (fun i => (F.kernelSpread i).toFinset) := by
    intro i _hi j _hj hij
    rw [Function.onFun, Set.disjoint_toFinset]
    exact F.kernelSpread_disjoint hij
  have h_biUnion_card :
      ((Finset.univ : Finset (Fin k)).biUnion
          (fun i => (F.kernelSpread i).toFinset)).card =
        ∑ i : Fin k, (F.kernelSpread i).toFinset.card :=
    Finset.card_biUnion h_disjFin
  have h_biUnion_set :
      (Finset.univ : Finset (Fin k)).biUnion
          (fun i => (F.kernelSpread i).toFinset) = F.G0.toFinsetᶜ := by
    ext g
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_compl,
      Set.mem_toFinset, F.mem_G0_iff, not_forall, not_not]
  have hG0_le : F.G0.toFinset.card ≤ Fintype.card G := by
    rw [← Finset.card_univ (α := G)]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hG0_card_eq : F.G0.toFinset.card = Nat.card F.G0 := by
    rw [Set.toFinset_card, Nat.card_eq_fintype_card]
  have hspread_card_eq : ∀ i : Fin k,
      (F.kernelSpread i).toFinset.card = Nat.card (F.kernelSpread i) := by
    intro i
    rw [Set.toFinset_card, Nat.card_eq_fintype_card]
  have h_compl_card :
      F.G0.toFinsetᶜ.card = Nat.card G - Nat.card F.G0 := by
    rw [Finset.card_compl]
    rw [show Fintype.card G = Nat.card G from by rw [Nat.card_eq_fintype_card],
      hG0_card_eq]
  have h_biUnion_card_nat :
      ((Finset.univ : Finset (Fin k)).biUnion
          (fun i => (F.kernelSpread i).toFinset)).card =
        ∑ i : Fin k, Nat.card (F.kernelSpread i) := by
    rw [h_biUnion_card]
    exact Finset.sum_congr rfl (fun i _ => hspread_card_eq i)
  rw [h_biUnion_set] at h_biUnion_card_nat
  have hsum :
      (∑ i : Fin k, Nat.card (F.kernelSpread i)) =
        Nat.card G - Nat.card F.G0 :=
    h_biUnion_card_nat.symm.trans h_compl_card
  have hG0_le_nat : Nat.card F.G0 ≤ Nat.card G := by
    rw [← hG0_card_eq, Nat.card_eq_fintype_card]
    exact hG0_le
  omega

/-- The partition (7.10)(d) implies `|G₀| ≤ |G|`. -/
lemma card_G0_le_card_G [Finite G] (F : FrobeniusFamily G k) :
    Nat.card F.G0 ≤ Nat.card G := by
  have h := F.card_eq_card_G0_add_sum_card_kernelSpread
  omega

/-- Difference form of the (7.10)(d) partition: the spread sizes sum to
`|G| - |G₀|`. -/
lemma sum_card_kernelSpread_eq_card_G_sub_card_G0 [Finite G]
    (F : FrobeniusFamily G k) :
    (∑ i : Fin k, Nat.card (F.kernelSpread i)) = Nat.card G - Nat.card F.G0 := by
  have h := F.card_eq_card_G0_add_sum_card_kernelSpread
  omega

/-- Difference form of the (7.10)(d) partition: `|G₀|` is the complement
of the spreads. -/
lemma card_G0_eq_card_G_sub_sum_card_kernelSpread [Finite G]
    (F : FrobeniusFamily G k) :
    Nat.card F.G0 = Nat.card G - ∑ i : Fin k, Nat.card (F.kernelSpread i) := by
  have h := F.card_eq_card_G0_add_sum_card_kernelSpread
  omega

/-- The sum of spread cardinalities in normalizer-index form. -/
lemma sum_card_kernelSpread_eq_sum_index_mul [Finite G]
    (F : FrobeniusFamily G k) :
    (∑ i : Fin k, Nat.card (F.kernelSpread i)) =
      ∑ i : Fin k, (F.L i).index * (Nat.card (F.H i) - 1) := by
  exact Finset.sum_congr rfl (fun i _ => F.card_kernelSpread_eq_index_mul i)

/-- Difference form of the partition with each spread counted by normalizer index. -/
lemma card_G0_eq_card_G_sub_sum_index_mul [Finite G]
    (F : FrobeniusFamily G k) :
    Nat.card F.G0 =
      Nat.card G - ∑ i : Fin k, (F.L i).index * (Nat.card (F.H i) - 1) := by
  rw [F.card_G0_eq_card_G_sub_sum_card_kernelSpread,
    F.sum_card_kernelSpread_eq_sum_index_mul]

/-- The index-counted spreads have total size `|G| - |G₀|`. -/
lemma sum_index_mul_eq_card_G_sub_card_G0 [Finite G]
    (F : FrobeniusFamily G k) :
    (∑ i : Fin k, (F.L i).index * (Nat.card (F.H i) - 1)) =
      Nat.card G - Nat.card F.G0 := by
  rw [← F.sum_card_kernelSpread_eq_sum_index_mul,
    F.sum_card_kernelSpread_eq_card_G_sub_card_G0]

/-- Kernel order `h_i = |H_i|`. -/
noncomputable def h (F : FrobeniusFamily G k) (i : Fin k) : ℕ := Nat.card (F.H i)

/-- Complement index `e_i = |L_i : H_i|` (exact, since `H_i ≤ L_i`). -/
noncomputable def e (F : FrobeniusFamily G k) (i : Fin k) : ℕ :=
  Nat.card (F.L i) / Nat.card (F.H i)

/-- If a local (7.8) package uses the `i`-th family kernel, its local
kernel order is the family quantity `h_i`. -/
lemma localKernelOrder_eq_h [Fintype G]
    (F : FrobeniusFamily G k) {i : Fin k}
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (hH : H78.hyp76.H = F.H i) :
    H78.kernelOrder = F.h i := by
  simp [Hypothesis78.kernelOrder, FrobeniusFamily.h, hH]

/-- If a local (7.8) package uses the `i`-th family host and kernel, its local
complement index is the family quantity `e_i`. -/
lemma localComplementIndex_eq_e [Fintype G]
    (F : FrobeniusFamily G k) {i : Fin k}
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (hL : L = F.L i)
    (hH : H78.hyp76.H = F.H i) :
    H78.complementIndex = F.e i := by
  simp [Hypothesis78.complementIndex, FrobeniusFamily.e, hL, hH]

/-- Family-side small-index data `2e_i + 1 ≤ h_i` supplies the local (7.8.b)
small-index hypothesis after identifying the local host and kernel. -/
lemma localSmallIndex_of_family_cardinalities [Fintype G]
    (F : FrobeniusFamily G k) {i : Fin k}
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (hL : L = F.L i)
    (hH : H78.hyp76.H = F.H i)
    (hsmall : 2 * F.e i + 1 ≤ F.h i) :
    H78.smallIndex := by
  rw [Hypothesis78.smallIndex]
  rw [F.localComplementIndex_eq_e H78 hL hH, F.localKernelOrder_eq_h H78 hH]
  exact hsmall

/-- Family-notated source-data form of the raw `(ζ^ν)^ρ` lower bound from
Peterfalvi (7.8.b).  This is the local estimate used before the reduced-family
inequality in (7.10), with `e` and `h` stated as `F.e i` and `F.h i`. -/
lemma zetaNuRho_inner_self_re_ge_of_family_source_data [Fintype G]
    (F : FrobeniusFamily G k) {i : Fin k}
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hL : L = F.L i) (hH : H78.hyp76.H = F.H i)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i) :
    1 - (F.e i : ℝ) / (F.h i : ℝ) ≤
      (ClassFunction.inner H78.zetaNuRho H78.zetaNuRho).re := by
  have hlocal :
      1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤
        (ClassFunction.inner H78.zetaNuRho H78.zetaNuRho).re :=
    H78.zetaNuRho_inner_self_re_ge_of_inner_values_irreducible_source_data_and_uv_formula
      hBD
      (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hind_norm)
      hzeta_ind hirr hdistinct
      (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hzeta_degree)
      (by
        simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
          using hdegree_sum)
      (by
        simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
          using hzeta_uv)
      (F.localSmallIndex_of_family_cardinalities H78 hL hH hsmall)
  simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
    using hlocal

/-- **Peterfalvi (7.8.b).** Family-notated source-data form of the residual
`Γ` upper bound.  This is the `Γ` estimate consumed by the orthogonal integer
decomposition in the final assembly, with the local `e` rewritten as `F.e i`. -/
lemma gamma_inner_self_re_le_of_family_source_data [Fintype G]
    (F : FrobeniusFamily G k) {i : Fin k}
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hL : L = F.L i) (hH : H78.hyp76.H = F.H i)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i) :
    (ClassFunction.inner hBD.Gamma hBD.Gamma).re ≤ (F.e i : ℝ) - 1 := by
  have hlocal :
      (ClassFunction.inner hBD.Gamma hBD.Gamma).re ≤
        (H78.complementIndex : ℝ) - 1 :=
    H78.gamma_inner_self_re_le_of_inner_values_irreducible_source_data_and_uv_formula
      hBD
      (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hind_norm)
      hzeta_ind hirr hdistinct
      (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hzeta_degree)
      (by
        simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
          using hdegree_sum)
      (by
        simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
          using hzeta_uv)
      (F.localSmallIndex_of_family_cardinalities H78 hL hH hsmall)
  simpa [F.localComplementIndex_eq_e H78 hL hH] using hlocal

/-- **Peterfalvi (7.8.c.ii).** Family-notated source-data form of the
`(ζ^ν)^ρ` norm formula.  This rewrites the local ratio `(h - 1)/(he)` as
the family quantities `(h_i - 1)/(h_i e_i)`. -/
lemma zetaNuRhoNormSq_eq_familyRatio_mul_int_sub_one_of_source_data [Fintype G]
    (F : FrobeniusFamily G k) {i : Fin k}
    {A : Set G} {L : Subgroup G} [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hL : L = F.L i) (hH : H78.hyp76.H = F.H i)
    (hnu_irr : IsIrreducibleCharacter (H78.nu (H78.hyp76.zeta H78.zetaDistinct)))
    (hnu_orth : ∀ r : Fin (H78.hyp76.n + 1), r ≠ H78.ind1H →
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta r)) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (F.e i : ℂ)) :
    H78.zetaNuRhoNormSq =
      (((F.h i : ℝ) - 1) / ((F.h i : ℝ) * (F.e i : ℝ))) *
        (((hBD.a : ℝ) - 1) * ((hBD.a : ℝ) - 1)) := by
  have hlocal :
      H78.zetaNuRhoNormSq =
        (((H78.kernelOrder : ℝ) - 1) /
            ((H78.kernelOrder : ℝ) * (H78.complementIndex : ℝ))) *
          (((hBD.a : ℝ) - 1) * ((hBD.a : ℝ) - 1)) :=
    H78.zetaNuRhoNormSq_eq_kernelRatio_mul_int_sub_one_of_irreducible_source_data
      hBD hnu_irr hnu_orth hirr hdistinct
      (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hzeta_degree)
  simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
    using hlocal

/-- `G₀` is nonempty: it contains the identity. -/
lemma one_le_card_G0 [Finite G] (F : FrobeniusFamily G k) :
    1 ≤ Nat.card F.G0 := by
  have : Nonempty F.G0 := ⟨⟨1, F.one_mem_G0⟩⟩
  exact Nat.card_pos

/-- `e_i = |L_i : H_i|` equals the order of the Frobenius complement `C`. -/
lemma e_eq_card_complement [Finite G] (F : FrobeniusFamily G k) (i : Fin k)
    {C : Subgroup ↥(F.L i)} (hC : IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    F.e i = Nat.card C := by
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hprod : Nat.card (F.H i) * Nat.card C = Nat.card ↥(F.L i) := by
    rw [← hN_card]; exact hC.isComplement.card_mul
  have h := Nat.mul_div_cancel_left (Nat.card C) (Nat.card_pos (α := F.H i))
  rw [hprod] at h
  exact h

/-- The Frobenius product formula `|H_i| * e_i = |L_i|`. -/
lemma h_mul_e_eq_card_L [Finite G] (F : FrobeniusFamily G k) (i : Fin k) :
    F.h i * F.e i = Nat.card (F.L i) := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hprod : Nat.card (F.H i) * Nat.card C = Nat.card ↥(F.L i) := by
    rw [← hN_card]
    exact hC.isComplement.card_mul
  rw [F.e_eq_card_complement i hC]
  exact hprod

/-- The Frobenius congruence gives `e_i ∣ h_i - 1`. -/
lemma e_dvd_h_sub_one [Finite G] (F : FrobeniusFamily G k) (i : Fin k) :
    F.e i ∣ F.h i - 1 := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hmod : Nat.card (F.H i) ≡ 1 [MOD Nat.card C] := by
    have := hC.card_kernel_modEq_one
    rwa [hN_card] at this
  have hdvd : Nat.card C ∣ Nat.card (F.H i) - 1 :=
    (Nat.modEq_iff_dvd' (Nat.card_pos (α := F.H i))).mp hmod.symm
  rw [F.e_eq_card_complement i hC]
  exact hdvd

/-- A Frobenius kernel in the family is nontrivial, so `2 ≤ h_i`. -/
lemma two_le_h [Finite G] (F : FrobeniusFamily G k) (i : Fin k) : 2 ≤ F.h i := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hh_eq : F.h i = Nat.card (F.H i) := rfl
  rw [hh_eq, ← hN_card]
  have hnt : Nontrivial ((F.H i).subgroupOf (F.L i)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hC.ne_bot_kernel
  have h1 : 1 < Nat.card ((F.H i).subgroupOf (F.L i)) :=
    Finite.one_lt_card_iff_nontrivial.mpr hnt
  omega

/-- In an odd-order ambient group, each Frobenius kernel order `h_i` is odd. -/
lemma odd_h [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (i : Fin k) : Odd (F.h i) := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hprod : Nat.card (F.H i) * Nat.card C = Nat.card ↥(F.L i) := by
    rw [← hN_card]
    exact hC.isComplement.card_mul
  have hLodd : Odd (Nat.card ↥(F.L i)) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (F.L i))
  exact (Nat.odd_mul.mp (hprod ▸ hLodd)).1

/-- In an odd-order ambient group, each complement index `e_i` is odd. -/
lemma odd_e [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (i : Fin k) : Odd (F.e i) := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  have hN_card : Nat.card ((F.H i).subgroupOf (F.L i)) = Nat.card (F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hprod : Nat.card (F.H i) * Nat.card C = Nat.card ↥(F.L i) := by
    rw [← hN_card]
    exact hC.isComplement.card_mul
  have hLodd : Odd (Nat.card ↥(F.L i)) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (F.L i))
  have hCodd : Odd (Nat.card C) := (Nat.odd_mul.mp (hprod ▸ hLodd)).2
  rw [F.e_eq_card_complement i hC]
  exact hCodd

/-- The Frobenius complement of `L_i` is nontrivial, so `e_i = |L_i : H_i| ≥ 2`. -/
lemma two_le_e [Finite G] (F : FrobeniusFamily G k) (i : Fin k) : 2 ≤ F.e i := by
  obtain ⟨C, hC⟩ := F.isFrobenius i
  rw [F.e_eq_card_complement i hC]
  have hnt : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC.ne_bot_complement
  have h1 : 1 < Nat.card C := Finite.one_lt_card_iff_nontrivial.mpr hnt
  omega

/-- Lagrange plus the Frobenius product formula: `|G| = [G : L_i] h_i e_i`. -/
lemma index_mul_h_mul_e_eq_card_G [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (F.L i).index * (F.h i * F.e i) = Nat.card G := by
  rw [F.h_mul_e_eq_card_L i]
  exact (F.L i).index_mul_card

/-- The spread count in `h_i` notation. -/
lemma card_kernelSpread_eq_index_mul_h_sub_one [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    Nat.card (F.kernelSpread i) = (F.L i).index * (F.h i - 1) := by
  simpa [h] using F.card_kernelSpread_eq_index_mul i

/-- `H_i^#` has cardinality `h_i - 1` as a `Nat.card` statement. -/
lemma card_kernel_sharp_eq_h_sub_one [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    Nat.card (((F.H i : Set G) \ ({1} : Set G)) : Set G) = F.h i - 1 := by
  rw [Nat.card_coe_set_eq]
  exact F.ncard_kernel_sharp i

/-- The local sharp-kernel ratio `|H_i^#| / |L_i| = (h_i - 1)/(h_i e_i)`. -/
lemma card_kernel_sharp_div_card_L_eq_h_sub_one_div_h_mul_e [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (Nat.card (((F.H i : Set G) \ ({1} : Set G)) : Set G) : ℚ) /
        (Nat.card (F.L i) : ℚ) =
      ((F.h i : ℚ) - 1) / ((F.h i : ℚ) * (F.e i : ℚ)) := by
  have hh1 : 1 ≤ F.h i := by
    have h2 := F.two_le_h i
    omega
  rw [F.card_kernel_sharp_eq_h_sub_one i, ← F.h_mul_e_eq_card_L i]
  norm_num [Nat.cast_sub hh1]

/-- The local sharp-kernel ratio `|H_i^#| / |L_i|` as a real number, in the
denominator order used by the real reduced-family estimate. -/
lemma card_kernel_sharp_div_card_L_eq_h_sub_one_div_e_mul_h_real [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (Nat.card (((F.H i : Set G) \ ({1} : Set G)) : Set G) : ℝ) /
        (Nat.card (F.L i) : ℝ) =
      ((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ)) := by
  have hh1 : 1 ≤ F.h i := by
    have h2 := F.two_le_h i
    omega
  rw [F.card_kernel_sharp_eq_h_sub_one i, ← F.h_mul_e_eq_card_L i]
  rw [Nat.cast_sub hh1, Nat.cast_mul]
  rw [mul_comm (F.h i : ℝ) (F.e i : ℝ)]
  norm_num

/-- The global spread ratio equals the same local ratio `(h_i - 1)/(h_i e_i)`. -/
lemma card_kernelSpread_div_card_G_eq_h_sub_one_div_h_mul_e [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (Nat.card (F.kernelSpread i) : ℚ) / (Nat.card G : ℚ) =
      ((F.h i : ℚ) - 1) / ((F.h i : ℚ) * (F.e i : ℚ)) := by
  have hidx_pos : 0 < (F.L i).index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos
  have hidx_ne : ((F.L i).index : ℚ) ≠ 0 := by
    exact_mod_cast hidx_pos.ne'
  have hh1 : 1 ≤ F.h i := by
    have h2 := F.two_le_h i
    omega
  have hh_ne : (F.h i : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := F.H i)).ne'
  have he_ne : (F.e i : ℚ) ≠ 0 := by
    have h2 := F.two_le_e i
    positivity
  rw [F.card_kernelSpread_eq_index_mul_h_sub_one i, ← F.index_mul_h_mul_e_eq_card_G i]
  norm_num [Nat.cast_sub hh1]
  field_simp [hidx_ne, hh_ne, he_ne]

/-- The global spread ratio matches the local sharp-kernel ratio. -/
lemma card_kernelSpread_div_card_G_eq_card_kernel_sharp_div_card_L [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (Nat.card (F.kernelSpread i) : ℚ) / (Nat.card G : ℚ) =
      (Nat.card (((F.H i : Set G) \ ({1} : Set G)) : Set G) : ℚ) /
        (Nat.card (F.L i) : ℚ) := by
  rw [F.card_kernelSpread_div_card_G_eq_h_sub_one_div_h_mul_e,
    F.card_kernel_sharp_div_card_L_eq_h_sub_one_div_h_mul_e]

/-- The sum of all spread ratios is the complement of the `G₀` ratio. -/
lemma sum_card_kernelSpread_div_card_G_eq_one_sub_card_G0_div_card_G [Finite G]
    (F : FrobeniusFamily G k) :
    (∑ i : Fin k, (Nat.card (F.kernelSpread i) : ℚ) / (Nat.card G : ℚ)) =
      1 - (Nat.card F.G0 : ℚ) / (Nat.card G : ℚ) := by
  have hG_pos : 0 < Nat.card G := Nat.card_pos
  have hG_ne : (Nat.card G : ℚ) ≠ 0 := by
    exact_mod_cast hG_pos.ne'
  rw [← Finset.sum_div, ← Nat.cast_sum, F.sum_card_kernelSpread_eq_card_G_sub_card_G0,
    Nat.cast_sub (F.card_G0_le_card_G)]
  field_simp [hG_ne]

/-- The same balance formula in `h_i, e_i` notation. -/
lemma sum_h_sub_one_div_h_mul_e_eq_one_sub_card_G0_div_card_G [Finite G]
    (F : FrobeniusFamily G k) :
    (∑ i : Fin k, ((F.h i : ℚ) - 1) / ((F.h i : ℚ) * (F.e i : ℚ))) =
      1 - (Nat.card F.G0 : ℚ) / (Nat.card G : ℚ) := by
  calc
    (∑ i : Fin k, ((F.h i : ℚ) - 1) / ((F.h i : ℚ) * (F.e i : ℚ)))
        = ∑ i : Fin k, (Nat.card (F.kernelSpread i) : ℚ) / (Nat.card G : ℚ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            exact (F.card_kernelSpread_div_card_G_eq_h_sub_one_div_h_mul_e i).symm
    _ = 1 - (Nat.card F.G0 : ℚ) / (Nat.card G : ℚ) :=
        F.sum_card_kernelSpread_div_card_G_eq_one_sub_card_G0_div_card_G

/-- The weighted spread ratio term is nonnegative. -/
lemma h_sub_one_div_h_mul_e_nonneg [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    0 ≤ ((F.h i : ℚ) - 1) / ((F.h i : ℚ) * (F.e i : ℚ)) := by
  have hh1_nat : 1 ≤ F.h i := by
    have h2 := F.two_le_h i
    omega
  have he1_nat : 1 ≤ F.e i := by
    have h2 := F.two_le_e i
    omega
  have hh1 : (1 : ℚ) ≤ F.h i := by exact_mod_cast hh1_nat
  have hhpos : (0 : ℚ) < F.h i := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hh1_nat)
  have hepos : (0 : ℚ) < F.e i := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one he1_nat)
  exact div_nonneg (sub_nonneg.mpr hh1) (le_of_lt (mul_pos hhpos hepos))

/-- The unweighted `𝓑`-sum term from Peterfalvi (7.10) is nonnegative. -/
lemma h_sub_one_div_e_nonneg [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    0 ≤ ((F.h i : ℚ) - 1) / (F.e i : ℚ) := by
  have hh1_nat : 1 ≤ F.h i := by
    have h2 := F.two_le_h i
    omega
  have he1_nat : 1 ≤ F.e i := by
    have h2 := F.two_le_e i
    omega
  have hh1 : (1 : ℚ) ≤ F.h i := by exact_mod_cast hh1_nat
  have hepos : (0 : ℚ) < F.e i := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one he1_nat)
  exact div_nonneg (sub_nonneg.mpr hh1) (le_of_lt hepos)

/-- Removing one index from the global weighted balance. -/
lemma sum_erase_h_sub_one_div_h_mul_e_eq_one_sub_card_G0_div_card_G_sub [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    (∑ j ∈ (Finset.univ.erase i),
        ((F.h j : ℚ) - 1) / ((F.h j : ℚ) * (F.e j : ℚ))) =
      1 - (Nat.card F.G0 : ℚ) / (Nat.card G : ℚ) -
        ((F.h i : ℚ) - 1) / ((F.h i : ℚ) * (F.e i : ℚ)) := by
  have hsum := F.sum_h_sub_one_div_h_mul_e_eq_one_sub_card_G0_div_card_G
  have hi : i ∈ (Finset.univ : Finset (Fin k)) := by simp
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin k))
      (fun j => ((F.h j : ℚ) - 1) / ((F.h j : ℚ) * (F.e j : ℚ))) hi] at hsum
  linarith

/-- A subset of the non-minimal indices has weighted sum bounded by the erased
weighted balance. -/
lemma sum_h_sub_one_div_h_mul_e_le_sum_erase [Finite G]
    (F : FrobeniusFamily G k) {i : Fin k} (s : Finset (Fin k))
    (hs : s ⊆ Finset.univ.erase i) :
    (∑ j ∈ s, ((F.h j : ℚ) - 1) / ((F.h j : ℚ) * (F.e j : ℚ))) ≤
      ∑ j ∈ (Finset.univ.erase i),
        ((F.h j : ℚ) - 1) / ((F.h j : ℚ) * (F.e j : ℚ)) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hs fun j _ _ =>
    F.h_sub_one_div_h_mul_e_nonneg j

/-- A subset of the non-minimal indices has unweighted sum bounded by the erased
unweighted sum. -/
lemma sum_h_sub_one_div_e_le_sum_erase [Finite G]
    (F : FrobeniusFamily G k) {i : Fin k} (s : Finset (Fin k))
    (hs : s ⊆ Finset.univ.erase i) :
    (∑ j ∈ s, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
      ∑ j ∈ (Finset.univ.erase i), ((F.h j : ℚ) - 1) / (F.e j : ℚ) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hs fun j _ _ =>
    F.h_sub_one_div_e_nonneg j

/-- `2 e_i + 1 ≤ h_i`.  From `e_i ∣ h_i - 1` (Frobenius: `|H_i| ≡ 1 mod e_i`)
together with `|L_i|` odd (whence `e_i` is odd and `h_i - 1` is even), the
quotient `(h_i - 1)/e_i` is even and positive, so `h_i - 1 ≥ 2 e_i`. -/
lemma two_mul_e_add_one_le_h [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (i : Fin k) : 2 * F.e i + 1 ≤ F.h i := by
  obtain ⟨m, hm⟩ := F.e_dvd_h_sub_one i
  have hh_odd : Odd (F.h i) := F.odd_h hodd i
  have he_odd : Odd (F.e i) := F.odd_e hodd i
  have hh_ge2 : 2 ≤ F.h i := F.two_le_h i
  have hh_sub_even : Even (F.h i - 1) := by
    obtain ⟨j, hj⟩ := hh_odd
    exact ⟨j, by omega⟩
  have hm_even : Even m := by
    rw [hm] at hh_sub_even
    rcases Nat.even_mul.mp hh_sub_even with he_even | hm_even
    · exact absurd he_even (Nat.not_even_iff_odd.mpr he_odd)
    · exact hm_even
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, Nat.mul_zero] at hm
      omega
    · exact h0
  have hm_ge2 : 2 ≤ m := by
    rcases hm_even with ⟨t, ht⟩
    omega
  have hmul : F.e i * 2 ≤ F.e i * m := Nat.mul_le_mul_left _ hm_ge2
  omega

/-- There is an index whose kernel order is minimal among the family. -/
lemma exists_min_h_index [Finite G] (F : FrobeniusFamily G k) :
    ∃ i : Fin k, ∀ j : Fin k, F.h i ≤ F.h j := by
  classical
  have hkpos : 0 < k := by
    have htwo : 2 ≤ k := F.two_le
    omega
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, hkpos⟩, by simp⟩
  rcases Finset.exists_min_image (Finset.univ : Finset (Fin k)) (fun i => F.h i) hne with
    ⟨i, _hi, hmin⟩
  exact ⟨i, fun j => hmin j (by simp)⟩

/-- If `h_i` is chosen minimal, then every other odd coprime kernel order is at
least `h_i + 2`. -/
lemma h_add_two_le_h_of_min [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) {i j : Fin k} (hij : i ≠ j)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) : F.h i + 2 ≤ F.h j := by
  have hcop : Nat.Coprime (F.h i) (F.h j) := by
    simpa [h] using F.coprime_kernel hij
  have hne : F.h i ≠ F.h j := by
    intro heq
    have hone : F.h i = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (by
      rw [← heq])
    have h2 := F.two_le_h i
    omega
  have hi_odd : Odd (F.h i) := F.odd_h hodd i
  have hj_odd : Odd (F.h j) := F.odd_h hodd j
  have hlt : F.h i < F.h j := by
    have hle := hmin j
    omega
  obtain ⟨a, ha⟩ := hi_odd
  obtain ⟨b, hb⟩ := hj_odd
  omega

/-- A minimal kernel order gives the denominator comparison used in the
`𝓑`-sum estimate in Peterfalvi (7.10). -/
lemma h_sub_one_div_h_mul_e_le_h_sub_one_div_e_div_min_add_two [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i j : Fin k}
    (hij : i ≠ j) (hmin : ∀ l : Fin k, F.h i ≤ F.h l) :
    ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ)) ≤
      (((F.h j : ℚ) - 1) / (F.e j : ℚ)) / ((F.h i : ℚ) + 2) := by
  have hden_le_nat : F.h i + 2 ≤ F.h j := F.h_add_two_le_h_of_min hodd hij hmin
  have hhj_ge2 : 2 ≤ F.h j := F.two_le_h j
  have hej_ge2 : 2 ≤ F.e j := F.two_le_e j
  have hhj_ne : (F.h j : ℚ) ≠ 0 := by positivity
  have hei_ne : (F.e j : ℚ) ≠ 0 := by positivity
  have hden_ne : (F.h i : ℚ) + 2 ≠ 0 := by positivity
  have hden_le : (F.h i : ℚ) + 2 ≤ (F.h j : ℚ) := by
    exact_mod_cast hden_le_nat
  field_simp [hhj_ne, hei_ne, hden_ne]
  have hsub_nonneg : 0 ≤ (F.h j : ℚ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast (by omega : 1 ≤ F.h j))
  nlinarith

/-- Summed denominator comparison for any set of indices avoiding the chosen
minimal index. -/
lemma sum_h_sub_one_div_h_mul_e_le_sum_h_sub_one_div_e_div_min_add_two [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (s : Finset (Fin k))
    (hs : ∀ j ∈ s, i ≠ j) :
    (∑ j ∈ s, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ))) ≤
      (∑ j ∈ s, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) / ((F.h i : ℚ) + 2) := by
  calc
    (∑ j ∈ s, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ)))
        ≤ ∑ j ∈ s, (((F.h j : ℚ) - 1) / (F.e j : ℚ)) /
            ((F.h i : ℚ) + 2) := by
            refine Finset.sum_le_sum fun j hj => ?_
            exact F.h_sub_one_div_h_mul_e_le_h_sub_one_div_e_div_min_add_two
              hodd (hs j hj) hmin
    _ = (∑ j ∈ s, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) /
          ((F.h i : ℚ) + 2) := by
        rw [Finset.sum_div]

/-- If the unweighted `𝓑`-sum is bounded by `e_i - 1`, then the weighted sum is
bounded by `(e_i - 1)/(h_i + 2)`, as in Peterfalvi (7.10). -/
lemma sum_h_sub_one_div_h_mul_e_le_e_sub_one_div_min_add_two [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (s : Finset (Fin k))
    (hs : ∀ j ∈ s, i ≠ j)
    (hsum : (∑ j ∈ s, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1) :
    (∑ j ∈ s, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ))) ≤
      ((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2) := by
  have hden_pos : 0 < (F.h i : ℚ) + 2 := by positivity
  have hweighted := F.sum_h_sub_one_div_h_mul_e_le_sum_h_sub_one_div_e_div_min_add_two
    hodd hmin s hs
  have hscaled :
      (∑ j ∈ s, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) / ((F.h i : ℚ) + 2) ≤
        ((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2) := by
    exact div_le_div_of_nonneg_right hsum (le_of_lt hden_pos)
  linarith

/-- The explicit right-hand side in Peterfalvi (7.10) is positive for every member
of an odd-order Frobenius family.  This is the arithmetic input used in the final
(7.11) contradiction once `(7.10)` gives the lower bound. -/
lemma lowerBoundTerm_pos [Finite G] (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (i : Fin k) :
    0 < ((F.e i : ℚ) - 1) *
      (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
          ((F.e i : ℚ) * (F.h i : ℚ)) +
        2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  have he2 : (2 : ℚ) ≤ (F.e i : ℚ) := by
    exact_mod_cast F.two_le_e i
  have hh2 : 2 * (F.e i : ℚ) + 1 ≤ (F.h i : ℚ) := by
    exact_mod_cast F.two_mul_e_add_one_le_h hodd i
  have hepos : (0 : ℚ) < (F.e i : ℚ) := by linarith
  have hhpos : (0 : ℚ) < (F.h i : ℚ) := by linarith
  have heh : (0 : ℚ) < (F.e i : ℚ) * (F.h i : ℚ) := mul_pos hepos hhpos
  have hh2pos : (0 : ℚ) < (F.h i : ℚ) * ((F.h i : ℚ) + 2) :=
    mul_pos hhpos (by linarith)
  refine mul_pos (by linarith) ?_
  have h1 : 0 ≤
      ((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
        ((F.e i : ℚ) * (F.h i : ℚ)) :=
    div_nonneg (by linarith) (le_of_lt heh)
  have h2 : 0 < (2 : ℚ) / ((F.h i : ℚ) * ((F.h i : ℚ) + 2)) :=
    div_pos (by norm_num) hh2pos
  linarith

/-- The final arithmetic rearrangement in Peterfalvi (7.10). -/
lemma lowerBoundTerm_final_rearrange [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) :
    1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2)) =
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  have he_ne : (F.e i : ℚ) ≠ 0 := by
    have h2 := F.two_le_e i
    positivity
  have hh_ne : (F.h i : ℚ) ≠ 0 := by
    have h2 := F.two_le_h i
    positivity
  have hh2_ne : (F.h i : ℚ) + 2 ≠ 0 := by
    have h2 := F.two_le_h i
    positivity
  field_simp [he_ne, hh_ne, hh2_ne]
  ring

/-- The penultimate estimate in Peterfalvi (7.10) implies the displayed lower
bound for the same index. -/
lemma lowerBoundTerm_of_penultimate [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k)
    (hpen : ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2))) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  rw [← F.lowerBoundTerm_final_rearrange i]
  exact hpen

/-- Existential form of `lowerBoundTerm_of_penultimate`, matching the target shape
of Peterfalvi (7.10). -/
lemma exists_lowerBoundTerm_of_exists_penultimate [Finite G]
    (F : FrobeniusFamily G k)
    (hpen : ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        1 - (F.e i : ℚ) / (F.h i : ℚ) -
          (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
          (((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2))) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
              ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  rcases hpen with ⟨i, hi⟩
  exact ⟨i, F.lowerBoundTerm_of_penultimate i hi⟩

/-- The `𝓑`-sum estimate in Peterfalvi (7.10) gives the penultimate displayed
inequality once the main character-theoretic estimate has isolated the same
`𝓑`-sum. -/
lemma penultimate_of_Bsum_bound [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum : (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
      (F.e i : ℚ) - 1)
    (hbase :
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        1 - (F.e i : ℚ) / (F.h i : ℚ) -
          (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
          (∑ j ∈ B, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ)))) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2)) := by
  have hBweighted := F.sum_h_sub_one_div_h_mul_e_le_e_sub_one_div_min_add_two
    hodd hmin B hB_ne hBsum
  linarith

/-- The `𝓑`-sum estimate plus the main character-theoretic estimate gives the
final displayed lower bound for the same minimal index. -/
lemma lowerBoundTerm_of_Bsum_bound [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum : (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
      (F.e i : ℚ) - 1)
    (hbase :
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        1 - (F.e i : ℚ) / (F.h i : ℚ) -
          (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
          (∑ j ∈ B, ((F.h j : ℚ) - 1) / ((F.e j : ℚ) * (F.h j : ℚ)))) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  exact F.lowerBoundTerm_of_penultimate i
    (F.penultimate_of_Bsum_bound hodd hmin B hB_ne hBsum hbase)

/-- Existential wrapper for the final assembly step of Peterfalvi (7.10): once a
minimal index and its `𝓑`-set satisfy the character-theoretic base estimate and
unweighted `𝓑`-sum bound, the displayed lower bound follows. -/
lemma exists_lowerBoundTerm_of_exists_Bsum_bound [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hdata : ∃ i : Fin k, (∀ l : Fin k, F.h i ≤ F.h l) ∧
      ∃ B : Finset (Fin k),
        (∀ j ∈ B, i ≠ j) ∧
        (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
          (F.e i : ℚ) - 1 ∧
        ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
          1 - (F.e i : ℚ) / (F.h i : ℚ) -
            (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
            (∑ j ∈ B, ((F.h j : ℚ) - 1) /
              ((F.e j : ℚ) * (F.h j : ℚ)))) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
              ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  rcases hdata with ⟨i, hmin, B, hB_ne, hBsum, hbase⟩
  exact ⟨i, F.lowerBoundTerm_of_Bsum_bound hodd hmin B hB_ne hBsum hbase⟩

/-- The unweighted local contribution `(h_j - 1) / e_j` attached to an index in
Peterfalvi's `𝓑`-sum.  Naming it keeps the `ℚ`-to-`ℂ` coercion from being
elaborated as a complex division in orthogonality hypotheses. -/
noncomputable def BsumWeight (F : FrobeniusFamily G k) (j : Fin k) : ℚ :=
  ((F.h j : ℚ) - 1) / (F.e j : ℚ)

end FrobeniusFamily
end OddOrder.Peterfalvi.S09
