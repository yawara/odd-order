/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.DoubleCoset
import OddOrder.GroupTheory.TransferTransitivity

/-!
# Mackey transfer (Isaacs Thm 10.10)

**Isaacs, Finite Group Theory, Thm 10.10** (Mackey transfer): `H, K ≤ G` with
`|G : H| < ∞`, `X` a set of `(H,K)`-double-coset representatives, `V : G → H` a
pretransfer, and `W_x : K → K ∩ Hˣ` pretransfers. Then for `k ∈ K`,
`V(k) ≡ ∏_{x ∈ X} x·W_x(k)·x⁻¹ mod H'`.

## mathlib 形 (左剰余類 mirror)

mathlib の transfer は左剰余類 `G ⧸ H` ベースなので、Isaacs の右剰余類
`(H,K)`-double coset `HxK` を `(K,H)`-double coset `KxH` に鏡映する:
`k ∈ K` に対し

`transfer ϕ k = ∏_{q : DoubleCoset.Quotient K H} transfer (mackeyRes ϕ q.out) ⟨k, hk⟩`

— `mackeyRes ϕ x : ↥((conjSubgroup x H) ⊓ K).subgroupOf K →* A`,
`w ↦ ϕ ⟨x⁻¹ · w · x, _⟩` (`conjSubgroup x H = x H x⁻¹` は `xH`-剰余類の
`K`-固定化群)。

## 証明の構造 (`TransferTransitivity` と同型の fibration 論法)

1. `G ⧸ H` は `K`-軌道 (= `(K,H)`-double coset) 上に fiber 化され、`q = KxH` 上の
   fiber は `↥K ⧸ (x•H ⊓ K).subgroupOf K` (軌道-固定化群対応)。
2. 各 double coset の代表 `x` と fiber section `s_q` から `G ⧸ H` の合成 section
   `q ↦ (代表) · (fiber 代表)` を作る (`compSection` の double-coset 版)。
3. `diff ϕ (合成 section) (k • 合成 section)` を fibration に沿って二重積に
   並べ替えると、`q`-fiber の内積が `transfer (mackeyRes ϕ x) ⟨k⟩` の
   `diff`-展開と因子単位で一致 (`k • ` が double coset を保つことがポイント —
   `k ∈ K` の左乗法は各 `KxH` を保存)。
4. `transfer_def` で両辺を結ぶ。

-/

namespace OddOrder.GroupTheory

open Subgroup MulAction
open scoped Pointwise

variable {G : Type*} [Group G] {H K : Subgroup G} {A : Type*} [CommGroup A]

section MackeyTransfer

/-- The stabilizer subgroup datum of the Mackey decomposition at a double-coset
representative `x`: the conjugate `x H x⁻¹` (the stabilizer in `G` of the left
coset `xH`), to be intersected with `K`. -/
def conjSubgroup (x : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj x).toMonoidHom

lemma mem_conjSubgroup {x g : G} :
    g ∈ conjSubgroup x H ↔ x⁻¹ * g * x ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    have h1 : x⁻¹ * ((MulAut.conj x).toMonoidHom h) * x = h := by
      show x⁻¹ * (x * h * x⁻¹) * x = h
      group
    rwa [h1]
  · intro hg
    refine ⟨x⁻¹ * g * x, hg, ?_⟩
    show x * (x⁻¹ * g * x) * x⁻¹ = g
    group

/-- The Mackey coefficient datum at a representative `x`: the restriction of
`ϕ : H →* A` to `(x H x⁻¹ ⊓ K).subgroupOf K` along conjugation by `x⁻¹`. -/
def mackeyRes (ϕ : ↥H →* A) (x : G) :
    ↥((conjSubgroup x H ⊓ K).subgroupOf K) →* A where
  toFun w := ϕ ⟨x⁻¹ * (w : G) * x, mem_conjSubgroup.mp w.2.1⟩
  map_one' := by
    have h1 : (⟨x⁻¹ * ((1 : ↥((conjSubgroup x H ⊓ K).subgroupOf K)) : G) * x,
        mem_conjSubgroup.mp (1 : ↥((conjSubgroup x H ⊓ K).subgroupOf K)).2.1⟩ : ↥H)
        = 1 := by
      ext
      show x⁻¹ * _ * x = 1
      norm_num
    rw [h1, map_one]
  map_mul' w₁ w₂ := by
    rw [← map_mul]
    refine congrArg ϕ (Subtype.ext ?_)
    show x⁻¹ * _ * x = (x⁻¹ * _ * x) * (x⁻¹ * _ * x)
    push_cast
    group

/-- Underlying map of the Mackey fibration: the fiber class of `w : ↥K` over
the double coset `q` is sent to the left coset `(w · q.out) H`. -/
noncomputable def dosetFiberMap (q : DoubleCoset.Quotient (K : Set G) H)
    (r : ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K) : G ⧸ H :=
  r.liftOn' (fun w => (((w : G) * q.out : G) : G ⧸ H)) (fun w w' hww' => by
    have h1 : w⁻¹ * w' ∈ (conjSubgroup q.out H ⊓ K).subgroupOf K :=
      QuotientGroup.leftRel_apply.mp hww'
    have h2 : ((w⁻¹ * w' : ↥K) : G) ∈ conjSubgroup q.out H := h1.1
    rw [QuotientGroup.eq]
    have h3 : ((w : G) * q.out)⁻¹ * ((w' : G) * q.out)
        = q.out⁻¹ * ((w⁻¹ * w' : ↥K) : G) * q.out := by
      push_cast
      group
    rw [h3]
    exact mem_conjSubgroup.mp h2)

lemma dosetFiberMap_mk (q : DoubleCoset.Quotient (K : Set G) H) (w : ↥K) :
    dosetFiberMap q ((w : ↥K) : ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K)
      = (((w : G) * q.out : G) : G ⧸ H) :=
  rfl

lemma dosetFiberMap_bijective :
    Function.Bijective (fun a : Σ q : DoubleCoset.Quotient (K : Set G) H,
        ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K =>
      dosetFiberMap a.1 a.2) := by
  constructor
  · rintro ⟨q, r⟩ ⟨q', r'⟩ h
    induction r using QuotientGroup.induction_on with
    | H w =>
    induction r' using QuotientGroup.induction_on with
    | H w' =>
      simp only [dosetFiberMap_mk] at h
      -- the double cosets agree
      have hq : q = q' := by
        have h1 : DoubleCoset.mk K H ((w : G) * q.out) = q := by
          conv_rhs => rw [← DoubleCoset.out_eq' K H q]
          rw [DoubleCoset.eq]
          exact ⟨(w : G)⁻¹, K.inv_mem w.2, 1, H.one_mem, by group⟩
        have h2 : DoubleCoset.mk K H ((w' : G) * q'.out) = q' := by
          conv_rhs => rw [← DoubleCoset.out_eq' K H q']
          rw [DoubleCoset.eq]
          exact ⟨(w' : G)⁻¹, K.inv_mem w'.2, 1, H.one_mem, by group⟩
        rw [← h1, ← h2, DoubleCoset.eq]
        exact ⟨1, K.one_mem, ((w : G) * q.out)⁻¹ * ((w' : G) * q'.out),
          QuotientGroup.eq.mp h, by group⟩
      subst hq
      -- the fiber classes agree
      have hfiber : ((w : ↥K) : ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K)
          = ((w' : ↥K) : ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K) := by
        rw [QuotientGroup.eq]
        have h4 : ((w⁻¹ * w' : ↥K) : G) ∈ conjSubgroup q.out H := by
          rw [mem_conjSubgroup]
          have h5 := QuotientGroup.eq.mp h
          have h6 : ((w : G) * q.out)⁻¹ * ((w' : G) * q.out)
              = q.out⁻¹ * ((w⁻¹ * w' : ↥K) : G) * q.out := by
            push_cast
            group
          rwa [h6] at h5
        exact ⟨h4, (w⁻¹ * w').2⟩
      exact congrArg (fun z => (⟨q, z⟩ : Σ q : DoubleCoset.Quotient (K : Set G) H,
        ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K)) hfiber
  · intro c
    induction c using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k₀, h₀, hk₀, hh₀, hout⟩ := DoubleCoset.mk_out_eq_mul K H g
      refine ⟨⟨DoubleCoset.mk K H g,
        ((⟨k₀⁻¹, K.inv_mem hk₀⟩ : ↥K) : ↥K ⧸ _)⟩, ?_⟩
      show ((k₀⁻¹ * (DoubleCoset.mk K H g).out : G) : G ⧸ H) = ((g : G) : G ⧸ H)
      rw [hout, QuotientGroup.eq]
      have h7 : (k₀⁻¹ * (k₀ * g * h₀))⁻¹ * g = h₀⁻¹ := by group
      rw [h7]
      exact H.inv_mem hh₀

/-- The Mackey fibration: `G ⧸ H` decomposes over the `(K,H)`-double cosets,
with fiber `↥K ⧸ (x H x⁻¹ ⊓ K).subgroupOf K` over the coset of `x = q.out`
(orbit–stabilizer for the left `K`-action on `G ⧸ H`). -/
noncomputable def dosetFiberEquiv :
    (Σ q : DoubleCoset.Quotient (K : Set G) H,
      ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K) ≃ G ⧸ H :=
  Equiv.ofBijective _ dosetFiberMap_bijective

lemma dosetFiberEquiv_mk (q : DoubleCoset.Quotient (K : Set G) H) (w : ↥K) :
    dosetFiberEquiv ⟨q, ((w : ↥K) : ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K)⟩
      = (((w : G) * q.out : G) : G ⧸ H) :=
  rfl

/-- The Mackey fibration is `K`-equivariant in the fiber coordinate. -/
lemma dosetFiberEquiv_smul (q : DoubleCoset.Quotient (K : Set G) H)
    (r : ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K) (u : ↥K) :
    dosetFiberEquiv ⟨q, u • r⟩ = (u : G) • dosetFiberEquiv ⟨q, r⟩ := by
  induction r using QuotientGroup.induction_on with
  | H w =>
    show dosetFiberEquiv ⟨q, ((u * w : ↥K) : ↥K ⧸ _)⟩ = _
    rw [dosetFiberEquiv_mk]
    show _ = ((u : G) * ((w : G) * q.out) : G ⧸ H)
    apply congrArg
    push_cast
    group

/-- The composite section of `G ⧸ H` from a family of fiber sections. -/
noncomputable def mackeySection
    (s : ∀ q : DoubleCoset.Quotient (K : Set G) H,
      ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K → ↥K) : G ⧸ H → G := fun c =>
  ((s ((dosetFiberEquiv (K := K) (H := H)).symm c).1
      ((dosetFiberEquiv (K := K) (H := H)).symm c).2 : ↥K) : G)
    * (((dosetFiberEquiv (K := K) (H := H)).symm c).1).out

lemma mackeySection_spec
    (s : ∀ q : DoubleCoset.Quotient (K : Set G) H,
      ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K → ↥K)
    (hs : ∀ q r, ((s q r : ↥K) : ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K) = r) :
    ∀ c : G ⧸ H, ((mackeySection s c : G) : G ⧸ H) = c := by
  intro c
  have h1 : ((mackeySection s c : G) : G ⧸ H)
      = dosetFiberEquiv ⟨((dosetFiberEquiv (K := K) (H := H)).symm c).1,
          ((s ((dosetFiberEquiv (K := K) (H := H)).symm c).1
              ((dosetFiberEquiv (K := K) (H := H)).symm c).2 : ↥K) :
            ↥K ⧸ _)⟩ :=
    (dosetFiberEquiv_mk _ _).symm
  rw [h1, hs]
  exact (dosetFiberEquiv (K := K) (H := H)).apply_symm_apply c

variable [H.FiniteIndex]
  [Fintype (DoubleCoset.Quotient (K : Set G) H)]
  [∀ q : DoubleCoset.Quotient (K : Set G) H,
    ((conjSubgroup q.out H ⊓ K).subgroupOf K).FiniteIndex]

/-- **Key product decomposition** for the Mackey formula: the `diff` of two
composite Mackey sections is the product, over double cosets, of the fiber-level
`diff`s under the conjugated data `mackeyRes`. -/
private lemma diff_mackeySection (ϕ : ↥H →* A)
    (s s' : ∀ q : DoubleCoset.Quotient (K : Set G) H,
      ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K → ↥K)
    (hs : ∀ q r, ((s q r : ↥K) : ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K) = r)
    (hs' : ∀ q r, ((s' q r : ↥K) : ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K) = r) :
    Subgroup.leftTransversals.diff ϕ
        ⟨Set.range (mackeySection s),
          isComplement_range_left (mackeySection_spec s hs)⟩
        ⟨Set.range (mackeySection s'),
          isComplement_range_left (mackeySection_spec s' hs')⟩
      = ∏ q : DoubleCoset.Quotient (K : Set G) H,
          Subgroup.leftTransversals.diff (mackeyRes ϕ q.out)
            ⟨Set.range (s q), isComplement_range_left (hs q)⟩
            ⟨Set.range (s' q), isComplement_range_left (hs' q)⟩ := by
  classical
  letI := H.fintypeQuotientOfFiniteIndex
  letI : ∀ q : DoubleCoset.Quotient (K : Set G) H,
      Fintype (↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K) := fun q =>
    ((conjSubgroup q.out H ⊓ K).subgroupOf K).fintypeQuotientOfFiniteIndex
  set γ := mackeySection (K := K) s with hγ_def
  set γ' := mackeySection (K := K) s' with hγ'_def
  have hdiff1 : Subgroup.leftTransversals.diff ϕ
      ⟨Set.range γ, isComplement_range_left (mackeySection_spec s hs)⟩
      ⟨Set.range γ', isComplement_range_left (mackeySection_spec s' hs')⟩
      = ∏ c : G ⧸ H, ϕ ⟨(γ c)⁻¹ * γ' c, by
          rw [← QuotientGroup.eq, mackeySection_spec s hs c,
            mackeySection_spec s' hs' c]⟩ := by
    unfold Subgroup.leftTransversals.diff
    refine Finset.prod_congr rfl fun c _ => ?_
    refine congrArg ϕ (Subtype.ext ?_)
    show _ * _ = _
    rw [IsComplement.leftQuotientEquiv_apply (mackeySection_spec s hs),
      IsComplement.leftQuotientEquiv_apply (mackeySection_spec s' hs')]
  have hdiff2 : ∀ q : DoubleCoset.Quotient (K : Set G) H,
      Subgroup.leftTransversals.diff (mackeyRes ϕ q.out)
        ⟨Set.range (s q), isComplement_range_left (hs q)⟩
        ⟨Set.range (s' q), isComplement_range_left (hs' q)⟩
      = ∏ r : ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K,
          mackeyRes ϕ q.out ⟨(s q r)⁻¹ * s' q r, by
            rw [← QuotientGroup.eq, hs q r, hs' q r]⟩ := by
    intro q
    unfold Subgroup.leftTransversals.diff
    refine Finset.prod_congr rfl fun r _ => ?_
    refine congrArg (mackeyRes ϕ q.out) (Subtype.ext ?_)
    show _ * _ = _
    rw [IsComplement.leftQuotientEquiv_apply (hs q),
      IsComplement.leftQuotientEquiv_apply (hs' q)]
  rw [hdiff1]
  rw [← Equiv.prod_comp (dosetFiberEquiv (K := K) (H := H))]
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [hdiff2 q]
  refine Finset.prod_congr rfl fun r _ => ?_
  -- coordinates of the composite sections at Φ ⟨q, r⟩
  have hcoord : ((dosetFiberEquiv (K := K) (H := H)).symm
      (dosetFiberEquiv ⟨q, r⟩)) = ⟨q, r⟩ :=
    (dosetFiberEquiv (K := K) (H := H)).symm_apply_apply _
  have hγq : γ (dosetFiberEquiv ⟨q, r⟩) = ((s q r : ↥K) : G) * q.out := by
    rw [hγ_def]
    unfold mackeySection
    rw [hcoord]
  have hγ'q : γ' (dosetFiberEquiv ⟨q, r⟩) = ((s' q r : ↥K) : G) * q.out := by
    rw [hγ'_def]
    unfold mackeySection
    rw [hcoord]
  refine congrArg ϕ (Subtype.ext ?_)
  show (γ (dosetFiberEquiv ⟨q, r⟩))⁻¹ * γ' (dosetFiberEquiv ⟨q, r⟩)
    = q.out⁻¹ * (((s q r)⁻¹ * s' q r : ↥K) : G) * q.out
  rw [hγq, hγ'q]
  push_cast
  group

/-- **Isaacs Theorem 10.10 (Mackey transfer)**: for `k ∈ K`, the transfer
`G →* A` of `ϕ : H →* A` evaluates as the product over `(K,H)`-double cosets of
the `K`-level transfers of the conjugated data `mackeyRes ϕ q.out`:
`V(k) = ∏_x x·W_x(k)·x⁻¹` in Isaacs' pretransfer language (left-coset mirror).

Instances: `Fintype` of the double-coset quotient and finite index of each
`(x H x⁻¹ ⊓ K).subgroupOf K` follow from `[H.FiniteIndex]`; they are taken as
hypotheses to keep the statement elaboration direct. -/
theorem transfer_eq_prod_doubleCoset (ϕ : ↥H →* A)
    {k : G} (hk : k ∈ K) :
    MonoidHom.transfer ϕ k
      = ∏ q : DoubleCoset.Quotient (K : Set G) H,
          MonoidHom.transfer (mackeyRes ϕ q.out) ⟨k, hk⟩ := by
  classical
  letI : ∀ q : DoubleCoset.Quotient (K : Set G) H,
      Fintype (↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K) := fun q =>
    ((conjSubgroup q.out H ⊓ K).subgroupOf K).fintypeQuotientOfFiniteIndex
  set khat : ↥K := ⟨k, hk⟩ with hkhat_def
  -- base and shifted fiber sections
  set s : ∀ q : DoubleCoset.Quotient (K : Set G) H,
      ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K → ↥K :=
    fun _ => Quotient.out with hs_def
  have hs : ∀ q r, ((s q r : ↥K) : ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K) = r :=
    fun _ r => Quotient.out_eq' r
  set s' : ∀ q : DoubleCoset.Quotient (K : Set G) H,
      ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K → ↥K :=
    fun q => smulSection khat (s q) with hs'_def
  have hs' : ∀ q r, ((s' q r : ↥K) : ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K) = r :=
    fun q => smulSection_spec khat (s q) (hs q)
  -- the k-translate of the composite transversal is the shifted composite
  have hpoint : ∀ c : G ⧸ H,
      mackeySection s' (k • c) = k * mackeySection s c := by
    intro c
    have hc : dosetFiberEquiv ((dosetFiberEquiv (K := K) (H := H)).symm c) = c :=
      (dosetFiberEquiv (K := K) (H := H)).apply_symm_apply c
    have hsymm : (dosetFiberEquiv (K := K) (H := H)).symm (k • c)
        = ⟨((dosetFiberEquiv (K := K) (H := H)).symm c).1,
            khat • ((dosetFiberEquiv (K := K) (H := H)).symm c).2⟩ := by
      rw [Equiv.symm_apply_eq, dosetFiberEquiv_smul]
      have h0 : (⟨((dosetFiberEquiv (K := K) (H := H)).symm c).1,
            ((dosetFiberEquiv (K := K) (H := H)).symm c).2⟩
          : Σ q : DoubleCoset.Quotient (K : Set G) H,
            ↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K)
          = (dosetFiberEquiv (K := K) (H := H)).symm c := rfl
      rw [h0, hc]
    unfold mackeySection
    rw [hsymm]
    have h8 : s' ((dosetFiberEquiv (K := K) (H := H)).symm c).1
          (khat • ((dosetFiberEquiv (K := K) (H := H)).symm c).2)
        = khat * s ((dosetFiberEquiv (K := K) (H := H)).symm c).1
            ((dosetFiberEquiv (K := K) (H := H)).symm c).2 := by
      rw [hs'_def]
      show smulSection khat (s ((dosetFiberEquiv (K := K) (H := H)).symm c).1)
        (khat • ((dosetFiberEquiv (K := K) (H := H)).symm c).2) = _
      rw [smulSection, inv_smul_smul]
    rw [h8]
    push_cast
    rw [mul_assoc]
  -- assemble via transfer_def on both levels
  have hshift : k • Set.range (mackeySection (K := K) s)
      = Set.range (mackeySection (K := K) s') := by
    ext y
    constructor
    · rintro ⟨-, ⟨c, rfl⟩, rfl⟩
      refine ⟨k • c, ?_⟩
      rw [hpoint c]
      rfl
    · rintro ⟨c, rfl⟩
      refine ⟨mackeySection s (k⁻¹ • c), ⟨k⁻¹ • c, rfl⟩, ?_⟩
      have h9 := hpoint (k⁻¹ • c)
      rw [smul_inv_smul] at h9
      rw [h9]
      rfl
  rw [MonoidHom.transfer_def ϕ ⟨Set.range (mackeySection (K := K) s),
    isComplement_range_left (mackeySection_spec s hs)⟩ k]
  rw [show (k • (⟨Set.range (mackeySection (K := K) s),
      isComplement_range_left (mackeySection_spec s hs)⟩ : H.LeftTransversal))
    = ⟨Set.range (mackeySection (K := K) s'),
        isComplement_range_left (mackeySection_spec s' hs')⟩ from Subtype.ext hshift]
  rw [diff_mackeySection ϕ s s' hs hs']
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [MonoidHom.transfer_def (mackeyRes ϕ q.out)
    ⟨Set.range (s q), isComplement_range_left (hs q)⟩ khat]
  congr 1
  exact (Subtype.ext (smul_range_section khat (s q) (hs q))).symm

end MackeyTransfer

end OddOrder.GroupTheory
