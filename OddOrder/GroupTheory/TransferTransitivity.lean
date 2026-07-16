/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer

/-!
# Transitivity of the transfer homomorphism

**Isaacs, Finite Group Theory, Thm 10.8** (transitivity of transfer): for
`H ≤ K ≤ G` with `|G : H| < ∞` and pretransfers `V : G → H`, `U : G → K`,
`W : K → H`, one has `V(g) ≡ W(U(g)) mod H'`.

mathlib 形の主定理 (`transfer_transfer`): 可換群 `A` への `ϕ : ↥H →* A` に対し
`MonoidHom.transfer (MonoidHom.transfer ϕ̃) = MonoidHom.transfer ϕ`
(`ϕ̃ : ↥(H.subgroupOf K) →* A` は `subgroupOfEquivOfLe` による `ϕ` の移送)。
mathlib には transfer の tower 合成則が無い (2026-07-17 現在) — upstream 候補。

## 証明の構造

`f : G ⧸ K → G`, `s : ↥K ⧸ H.subgroupOf K → ↥K` を section とすると、合成
`γ : q ↦ f Q · s r` (`(Q, r)` は fibration `quotientEquivProdOfLE'` による
`q` の座標) は `G ⧸ H` の section (`compSection`)。核心は積分解
(`diff_compSection`):
`diff ϕ (γ[f,s]) (γ[f',s]) = diff W (f) (f')` — 左辺を fibration に沿って
二重積に並べ替えると、`Q`-fiber ごとの内積が `W((f Q)⁻¹ f' Q) = diff ϕ̃ S (k⁻¹ • S)`
の因子と一致する。あとは `g • (γ[f,s]) = γ[g·f, s]` (集合として) と
`transfer_def` 2 回で主定理。
-/

namespace OddOrder.GroupTheory

open Subgroup Subgroup.leftTransversals MulAction
open scoped Pointwise

variable {G : Type*} [Group G] {H K : Subgroup G} {A : Type*} [CommGroup A]

section TransferTransitivity

/-- Transport `ϕ : ↥H →* A` to the copy `H.subgroupOf K` of `H` inside `K`. -/
def transferRes (hHK : H ≤ K) (ϕ : ↥H →* A) : ↥(H.subgroupOf K) →* A :=
  ϕ.comp (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom

@[simp]
lemma transferRes_apply (hHK : H ≤ K) (ϕ : ↥H →* A) (x : ↥(H.subgroupOf K)) :
    transferRes hHK ϕ x = ϕ ⟨(x : ↥K), x.2⟩ :=
  rfl

/-- Naturality of the transfer in the coefficient homomorphism:
`transfer (ψ ∘ ϕ) = ψ ∘ transfer ϕ` for `ψ : A →* B` between commutative groups.
(Products commute with `ψ` in the defining `diff`.) -/
theorem transfer_comp_left {B : Type*} [CommGroup B] [H.FiniteIndex]
    (ψ : A →* B) (ϕ : ↥H →* A) :
    MonoidHom.transfer (ψ.comp ϕ) = ψ.comp (MonoidHom.transfer ϕ) := by
  ext g
  rw [MonoidHom.comp_apply, MonoidHom.transfer_def (ψ.comp ϕ) default g,
    MonoidHom.transfer_def ϕ default g]
  unfold Subgroup.leftTransversals.diff
  rw [map_prod]
  rfl

/-- Transfer along a subgroup of index one evaluates, up to an inner
conjugation of the argument, as the coefficient map itself: there is `r : G`
with `transfer ϕ g = ϕ (r⁻¹ g r)`. (Used for the trivial double coset in
Yoshida's theorem, where the conjugation is then absorbed by normality.) -/
theorem exists_transfer_eq_conj_of_index_eq_one {H : Subgroup G} [H.FiniteIndex]
    (hidx : H.index = 1) (ϕ : ↥H →* A) (g : G) :
    ∃ r : G, MonoidHom.transfer ϕ g
      = ϕ ⟨r⁻¹ * g * r, by rw [Subgroup.index_eq_one.mp hidx]; trivial⟩ := by
  classical
  letI := H.fintypeQuotientOfFiniteIndex
  haveI hsub : Subsingleton (G ⧸ H) := by
    have h1 : Nat.card (G ⧸ H) = 1 := by rw [← Subgroup.index_eq_card, hidx]
    exact (Nat.card_eq_one_iff_unique.mp h1).1
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  haveI : Subsingleton (Quotient (MulAction.orbitRel
      (Subgroup.zpowers g) (G ⧸ H))) := Quotient.instSubsingletonQuotient _
  rw [Fintype.prod_subsingleton _
    (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))
      (((1 : G) : G ⧸ H)))]
  refine ⟨(Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))
      (((1 : G) : G ⧸ H))).out.out, congrArg ϕ (Subtype.ext ?_)⟩
  show _ * g ^ Function.minimalPeriod _ _ * _ = _
  rw [Function.minimalPeriod_eq_one_of_subsingleton, pow_one]

variable (hHK : H ≤ K)

/-- The composite section of `G ⧸ H` induced by a section `f` of `G ⧸ K` and a
section `s` of `↥K ⧸ H.subgroupOf K`: the coset `q` with fibration coordinates
`(Q, r)` is represented by `f Q * s r`. -/
noncomputable def compSection (f : G ⧸ K → G)
    (hf : Function.RightInverse f QuotientGroup.mk)
    (s : ↥K ⧸ H.subgroupOf K → ↥K) : G ⧸ H → G := fun q =>
  f (Subgroup.quotientEquivProdOfLE' hHK f hf q).1
    * ↑(s (Subgroup.quotientEquivProdOfLE' hHK f hf q).2)

/-- The fibration inverse at explicit coordinates:
`(quotientEquivProdOfLE' hHK f hf).symm (Q, ⟦b⟧) = ⟦f Q * b⟧`. -/
lemma quotientEquivProdOfLE'_symm_mk (f : G ⧸ K → G)
    (hf : Function.RightInverse f QuotientGroup.mk)
    (Q : G ⧸ K) (b : ↥K) :
    (Subgroup.quotientEquivProdOfLE' hHK f hf).symm
        (Q, ((b : ↥K) : ↥K ⧸ H.subgroupOf K))
      = ((f Q * (b : G) : G) : G ⧸ H) :=
  rfl

/-- `compSection` is a section of `G ⧸ H`. -/
lemma compSection_spec (f : G ⧸ K → G)
    (hf : Function.RightInverse f QuotientGroup.mk)
    (s : ↥K ⧸ H.subgroupOf K → ↥K)
    (hs : Function.RightInverse s QuotientGroup.mk) :
    ∀ q : G ⧸ H, ((compSection hHK f hf s q : G) : G ⧸ H) = q := by
  intro q
  set e := Subgroup.quotientEquivProdOfLE' hHK f hf with he_def
  have h1 : e.symm (e q) = q := e.symm_apply_apply q
  calc ((compSection hHK f hf s q : G) : G ⧸ H)
      = e.symm ((e q).1, (((s (e q).2 : ↥K) : ↥K ⧸ H.subgroupOf K))) :=
        (quotientEquivProdOfLE'_symm_mk hHK f hf (e q).1 (s (e q).2)).symm
    _ = e.symm ((e q).1, (e q).2) := by rw [hs (e q).2]
    _ = q := h1

/-- A subgroup containing a finite-index subgroup has finite index. -/
lemma finiteIndex_of_le (hHK : H ≤ K) [H.FiniteIndex] : K.FiniteIndex :=
  ⟨fun h0 => Subgroup.FiniteIndex.index_ne_zero (H := H)
    (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_dvd_of_le hHK))⟩

/-- A finite-index subgroup has finite relative index in an intermediate group. -/
lemma finiteIndex_subgroupOf (hHK : H ≤ K) [H.FiniteIndex] :
    (H.subgroupOf K).FiniteIndex :=
  ⟨fun h0 => Subgroup.FiniteIndex.index_ne_zero (H := H) (by
    rw [← Subgroup.relIndex_mul_index hHK, show H.relIndex K = 0 from h0, zero_mul])⟩

/-- The `g`-translate of a section of `G ⧸ K`. -/
noncomputable def smulSection (g : G) (f : G ⧸ K → G) : G ⧸ K → G :=
  fun Q => g * f (g⁻¹ • Q)

lemma smulSection_spec (g : G) (f : G ⧸ K → G)
    (hf : Function.RightInverse f QuotientGroup.mk) :
    Function.RightInverse (smulSection g f) QuotientGroup.mk := by
  intro Q
  change ((g * f (g⁻¹ • Q) : G) : G ⧸ K) = Q
  have h1 : ((g * f (g⁻¹ • Q) : G) : G ⧸ K) = g • ((f (g⁻¹ • Q) : G) : G ⧸ K) := rfl
  rw [h1, hf (g⁻¹ • Q), smul_inv_smul]

/-- Translating the outer-section transversal: `g • range f = range (smulSection g f)`. -/
lemma smul_range_section (g : G) (f : G ⧸ K → G)
    (hf : Function.RightInverse f QuotientGroup.mk) :
    g • Set.range f = Set.range (smulSection g f) := by
  ext y
  constructor
  · rintro ⟨-, ⟨Q, rfl⟩, rfl⟩
    refine ⟨g • Q, ?_⟩
    show smulSection g f (g • Q) = g • f Q
    rw [smulSection, inv_smul_smul]
    rfl
  · rintro ⟨Q, rfl⟩
    refine ⟨f (g⁻¹ • Q), ⟨g⁻¹ • Q, rfl⟩, ?_⟩
    show g • f (g⁻¹ • Q) = smulSection g f Q
    rfl

variable [H.FiniteIndex] [K.FiniteIndex] [(H.subgroupOf K).FiniteIndex]

/-- **Key product decomposition**: the `diff` of two composite transversals with
the same fiber section `s` equals the `diff` of the outer transversals under the
`K`-level transfer. (The inner products over each fiber assemble into the values
`W((f Q)⁻¹ f' Q)` of the transfer `W = transfer ϕ̃ : K →* A`.) -/
private lemma diff_compSection (ϕ : ↥H →* A)
    (f f' : G ⧸ K → G) (hf : Function.RightInverse f QuotientGroup.mk)
    (hf' : Function.RightInverse f' QuotientGroup.mk)
    (s : ↥K ⧸ H.subgroupOf K → ↥K)
    (hs : Function.RightInverse s QuotientGroup.mk) :
    diff ϕ ⟨Set.range (compSection hHK f hf s),
        isComplement_range_left (compSection_spec hHK f hf s hs)⟩
      ⟨Set.range (compSection hHK f' hf' s),
        isComplement_range_left (compSection_spec hHK f' hf' s hs)⟩
      = diff (MonoidHom.transfer (transferRes hHK ϕ))
          ⟨Set.range f, isComplement_range_left hf⟩
          ⟨Set.range f', isComplement_range_left hf'⟩ := by
  classical
  letI := H.fintypeQuotientOfFiniteIndex
  letI := K.fintypeQuotientOfFiniteIndex
  letI := (H.subgroupOf K).fintypeQuotientOfFiniteIndex
  set e := Subgroup.quotientEquivProdOfLE' hHK f hf with he_def
  set γ : G ⧸ H → G := compSection hHK f hf s with hγ_def
  set γ' : G ⧸ H → G := compSection hHK f' hf' s with hγ'_def
  -- both diffs as explicit products over sections
  have hdiff1 : diff ϕ ⟨Set.range γ,
      isComplement_range_left (compSection_spec hHK f hf s hs)⟩
      ⟨Set.range γ', isComplement_range_left (compSection_spec hHK f' hf' s hs)⟩
      = ∏ q : G ⧸ H, ϕ ⟨(γ q)⁻¹ * γ' q, by
          rw [← QuotientGroup.eq]
          rw [compSection_spec hHK f hf s hs q, compSection_spec hHK f' hf' s hs q]⟩ := by
    unfold Subgroup.leftTransversals.diff
    refine Finset.prod_congr rfl fun q _ => ?_
    refine congrArg ϕ (Subtype.ext ?_)
    show _ * _ = _
    rw [IsComplement.leftQuotientEquiv_apply (compSection_spec hHK f hf s hs),
      IsComplement.leftQuotientEquiv_apply (compSection_spec hHK f' hf' s hs)]
  have hdiff2 : diff (MonoidHom.transfer (transferRes hHK ϕ))
      ⟨Set.range f, isComplement_range_left hf⟩
      ⟨Set.range f', isComplement_range_left hf'⟩
      = ∏ Q : G ⧸ K, MonoidHom.transfer (transferRes hHK ϕ)
          ⟨(f Q)⁻¹ * f' Q, by
            rw [← QuotientGroup.eq, hf Q, hf' Q]⟩ := by
    unfold Subgroup.leftTransversals.diff
    refine Finset.prod_congr rfl fun Q _ => ?_
    refine congrArg (MonoidHom.transfer (transferRes hHK ϕ)) (Subtype.ext ?_)
    show _ * _ = _
    rw [IsComplement.leftQuotientEquiv_apply hf, IsComplement.leftQuotientEquiv_apply hf']
  rw [hdiff1, hdiff2]
  -- reindex the H-product along the fibration e
  rw [← Equiv.prod_comp e.symm]
  rw [Fintype.prod_prod_type]
  -- match fiberwise: the Q-th inner product is the transfer value at k = (f Q)⁻¹ f' Q
  refine Finset.prod_congr rfl fun Q _ => ?_
  have hk : (f Q)⁻¹ * f' Q ∈ K := by
    rw [← QuotientGroup.eq, hf Q, hf' Q]
  set k : ↥K := ⟨(f Q)⁻¹ * f' Q, hk⟩ with hk_def
  -- the K-level transversal built from s and the transfer at k
  have htransfer : MonoidHom.transfer (transferRes hHK ϕ) k
      = ∏ r : ↥K ⧸ H.subgroupOf K, transferRes hHK ϕ
          ⟨(s r)⁻¹ * (k * s (k⁻¹ • r)), by
            rw [← QuotientGroup.eq, hs r]
            have h1 : ((k * s (k⁻¹ • r) : ↥K) : ↥K ⧸ H.subgroupOf K)
                = k • ((s (k⁻¹ • r) : ↥K) : ↥K ⧸ H.subgroupOf K) := rfl
            rw [h1, hs (k⁻¹ • r), smul_inv_smul]⟩ := by
    rw [MonoidHom.transfer_def _ ⟨Set.range s, isComplement_range_left hs⟩]
    unfold Subgroup.leftTransversals.diff
    refine Finset.prod_congr rfl fun r _ => ?_
    refine congrArg (transferRes hHK ϕ) (Subtype.ext ?_)
    show _ * _ = _
    rw [IsComplement.leftQuotientEquiv_apply hs]
    rw [smul_apply_eq_smul_apply_inv_smul, IsComplement.leftQuotientEquiv_apply hs]
    rfl
  rw [htransfer]
  -- factor-by-factor match over the fiber
  refine Finset.prod_congr rfl fun r _ => ?_
  -- compute γ and γ' at the point e.symm (Q, r)
  induction r using QuotientGroup.induction_on with
  | H b =>
    -- the base point q₀ = ⟦f Q * b⟧
    have hq0 : e.symm (Q, ((b : ↥K) : ↥K ⧸ H.subgroupOf K))
        = ((f Q * (b : G) : G) : G ⧸ H) :=
      quotientEquivProdOfLE'_symm_mk hHK f hf Q b
    -- γ at q₀: fibration coordinates are (Q, ⟦b⟧)
    have hγq : γ (e.symm (Q, ((b : ↥K) : ↥K ⧸ H.subgroupOf K)))
        = f Q * ↑(s (((b : ↥K) : ↥K ⧸ H.subgroupOf K))) := by
      rw [hγ_def]
      unfold compSection
      rw [e.apply_symm_apply (Q, ((b : ↥K) : ↥K ⧸ H.subgroupOf K))]
    -- γ' at q₀: fibration coordinates w.r.t. f' are (Q, k⁻¹ • ⟦b⟧)
    have hsmul_b : k⁻¹ • (((b : ↥K) : ↥K ⧸ H.subgroupOf K))
        = ((k⁻¹ * b : ↥K) : ↥K ⧸ H.subgroupOf K) := rfl
    have hsymm : (Subgroup.quotientEquivProdOfLE' hHK f' hf').symm
        (Q, k⁻¹ • (((b : ↥K) : ↥K ⧸ H.subgroupOf K)))
        = e.symm (Q, ((b : ↥K) : ↥K ⧸ H.subgroupOf K)) := by
      rw [hsmul_b, quotientEquivProdOfLE'_symm_mk hHK f' hf' Q (k⁻¹ * b), hq0]
      apply congrArg
      have hcoe : ((k⁻¹ * b : ↥K) : G) = ((f Q)⁻¹ * f' Q)⁻¹ * (b : G) := rfl
      rw [hcoe]
      group
    have he' : Subgroup.quotientEquivProdOfLE' hHK f' hf'
        (e.symm (Q, ((b : ↥K) : ↥K ⧸ H.subgroupOf K)))
        = (Q, k⁻¹ • (((b : ↥K) : ↥K ⧸ H.subgroupOf K))) := by
      rw [← hsymm, Equiv.apply_symm_apply]
    have hγ'q : γ' (e.symm (Q, ((b : ↥K) : ↥K ⧸ H.subgroupOf K)))
        = f' Q * ↑(s (k⁻¹ • (((b : ↥K) : ↥K ⧸ H.subgroupOf K)))) := by
      rw [hγ'_def]
      unfold compSection
      rw [he']
    -- both factors are ϕ of the same element of H
    refine congrArg ϕ (Subtype.ext ?_)
    show (γ (e.symm (Q, ((b : ↥K) : ↥K ⧸ H.subgroupOf K))))⁻¹
        * γ' (e.symm (Q, ((b : ↥K) : ↥K ⧸ H.subgroupOf K)))
      = (((s (((b : ↥K) : ↥K ⧸ H.subgroupOf K)))⁻¹
          * (k * s (k⁻¹ • (((b : ↥K) : ↥K ⧸ H.subgroupOf K)))) : ↥K) : G)
    have hcoe2 : (((s (((b : ↥K) : ↥K ⧸ H.subgroupOf K)))⁻¹
          * (k * s (k⁻¹ • (((b : ↥K) : ↥K ⧸ H.subgroupOf K)))) : ↥K) : G)
        = ((s (((b : ↥K) : ↥K ⧸ H.subgroupOf K)) : ↥K) : G)⁻¹
          * (((f Q)⁻¹ * f' Q)
            * ((s (k⁻¹ • (((b : ↥K) : ↥K ⧸ H.subgroupOf K))) : ↥K) : G)) := rfl
    rw [hγq, hγ'q, hcoe2]
    group

omit [H.FiniteIndex] [K.FiniteIndex] [(H.subgroupOf K).FiniteIndex] in
/-- Translating the composite transversal: the `g`-translate of
`range (compSection f s)` is the composite transversal of the translated outer
section with the same fiber section. -/
lemma smul_range_compSection (g : G) (f : G ⧸ K → G)
    (hf : Function.RightInverse f QuotientGroup.mk)
    (s : ↥K ⧸ H.subgroupOf K → ↥K)
    (hs : Function.RightInverse s QuotientGroup.mk) :
    g • Set.range (compSection hHK f hf s)
      = Set.range (compSection hHK (smulSection g f) (smulSection_spec g f hf) s) := by
  -- both sides are sections of G ⧸ H differing by the reparametrization q ↦ g • q;
  -- pointwise: compSection (smulSection g f) s (g • q) = g * compSection f s q
  have hpoint : ∀ q : G ⧸ H,
      compSection hHK (smulSection g f) (smulSection_spec g f hf) s (g • q)
        = g * compSection hHK f hf s q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hgq : (g • ((x : G) : G ⧸ H)) = ((g * x : G) : G ⧸ H) := rfl
      rw [hgq]
      unfold compSection
      -- both fibration coordinates: outer cosets are g-shifted, fibers agree
      have hfst : (Subgroup.quotientEquivProdOfLE' hHK (smulSection g f)
          (smulSection_spec g f hf) ((g * x : G) : G ⧸ H)).1
          = g • (Subgroup.quotientEquivProdOfLE' hHK f hf ((x : G) : G ⧸ H)).1 := rfl
      have hsnd : (Subgroup.quotientEquivProdOfLE' hHK (smulSection g f)
          (smulSection_spec g f hf) ((g * x : G) : G ⧸ H)).2
          = (Subgroup.quotientEquivProdOfLE' hHK f hf ((x : G) : G ⧸ H)).2 := by
        show Quotient.mk'' _ = Quotient.mk'' _
        apply congrArg
        refine Subtype.ext ?_
        show (smulSection g f ((g * x : G) : G ⧸ K))⁻¹ * (g * x)
          = (f ((x : G) : G ⧸ K))⁻¹ * x
        rw [smulSection]
        have h2 : g⁻¹ • ((g * x : G) : G ⧸ K) = ((x : G) : G ⧸ K) := by
          have h3 : ((g * x : G) : G ⧸ K) = g • ((x : G) : G ⧸ K) := rfl
          rw [h3, inv_smul_smul]
        rw [h2]
        group
      rw [hfst, hsnd]
      have h4 : smulSection g f (g • (Subgroup.quotientEquivProdOfLE' hHK f hf
          ((x : G) : G ⧸ H)).1)
          = g * f ((Subgroup.quotientEquivProdOfLE' hHK f hf ((x : G) : G ⧸ H)).1) := by
        rw [smulSection, inv_smul_smul]
      rw [h4, mul_assoc]
  ext y
  constructor
  · rintro ⟨-, ⟨q, rfl⟩, rfl⟩
    exact ⟨g • q, (hpoint q).trans rfl⟩
  · rintro ⟨q, rfl⟩
    refine ⟨compSection hHK f hf s (g⁻¹ • q), ⟨g⁻¹ • q, rfl⟩, ?_⟩
    have h5 := hpoint (g⁻¹ • q)
    rw [smul_inv_smul] at h5
    rw [h5]
    rfl

/-- **Transitivity of the transfer homomorphism** (Isaacs, *Finite Group Theory*,
Thm 10.8): for `H ≤ K ≤ G` of finite index and `ϕ : H →* A` into a commutative
group, the transfer `G →* A` of the transfer `K →* A` of `ϕ` equals the transfer
of `ϕ`:
`transfer (transfer ϕ̃) = transfer ϕ`, where `ϕ̃` is `ϕ` viewed on `H.subgroupOf K`.

(In Isaacs' pretransfer language: `V(g) ≡ W(U(g)) mod H'` for pretransfers
`V : G → H`, `U : G → K`, `W : K → H`.) -/
theorem transfer_transfer (ϕ : ↥H →* A) :
    MonoidHom.transfer (MonoidHom.transfer (transferRes hHK ϕ))
      = MonoidHom.transfer ϕ := by
  classical
  ext g
  -- base sections
  set f₀ : G ⧸ K → G := Quotient.out with hf₀_def
  have hf₀ : Function.RightInverse f₀ QuotientGroup.mk := fun Q => Quotient.out_eq' Q
  set s₀ : ↥K ⧸ H.subgroupOf K → ↥K := Quotient.out with hs₀_def
  have hs₀ : Function.RightInverse s₀ QuotientGroup.mk := fun r => Quotient.out_eq' r
  -- evaluate both transfers with the built transversals
  rw [MonoidHom.transfer_def (MonoidHom.transfer (transferRes hHK ϕ))
    ⟨Set.range f₀, isComplement_range_left hf₀⟩ g]
  rw [MonoidHom.transfer_def ϕ ⟨Set.range (compSection hHK f₀ hf₀ s₀),
    isComplement_range_left (compSection_spec hHK f₀ hf₀ s₀ hs₀)⟩ g]
  -- rewrite the g-translates as section-built transversals
  have hT : (g • (⟨Set.range f₀, isComplement_range_left hf₀⟩ : K.LeftTransversal))
      = ⟨Set.range (smulSection g f₀),
          isComplement_range_left (smulSection_spec g f₀ hf₀)⟩ :=
    Subtype.ext (smul_range_section g f₀ hf₀)
  have hTS : (g • (⟨Set.range (compSection hHK f₀ hf₀ s₀),
        isComplement_range_left (compSection_spec hHK f₀ hf₀ s₀ hs₀)⟩
        : H.LeftTransversal))
      = ⟨Set.range (compSection hHK (smulSection g f₀) (smulSection_spec g f₀ hf₀) s₀),
          isComplement_range_left
            (compSection_spec hHK (smulSection g f₀) (smulSection_spec g f₀ hf₀) s₀ hs₀)⟩ :=
    Subtype.ext (smul_range_compSection hHK g f₀ hf₀ s₀ hs₀)
  rw [hT, hTS]
  exact (diff_compSection hHK ϕ f₀ (smulSection g f₀) hf₀
    (smulSection_spec g f₀ hf₀) s₀ hs₀).symm

end TransferTransitivity

end OddOrder.GroupTheory
