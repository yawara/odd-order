import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF.OpicoreCentralizer

/-!
# BG Theorem 15.7(e) — pinning the witness prime to the TI-failure intersection

BG's Theorem 15.7(e) states its second and third cases in terms of `p = |X|`, where
`X = F(M) ∩ F(M)ᵍ` is the intersection witnessing the failure of `F(M)` to be `TI`.  Getting there
takes three steps (BG mmd L4264-4266):

1. `X` is a `p`-group — this file.
2. `B = X₁ × Ω₁(Z(P))` is a maximal elementary abelian subgroup of `P = O_p(M_F)` of rank two.
3. Lemma 10.13(b) then gives `C_P(X₁) = X₁ × Z` with `Z` cyclic, whence `X = X₁` and `p = |X|`.

Split out of `PisetBetaDisjoint` (which supplies the witness and the `O_p`/`O_{p'}` structure) to
keep that file under the 1500-line split trigger; see issues 3022 and 0124.
-/
namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S14
open scoped Pointwise
open scoped IsMulCommutative
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **BG Theorem 15.7(e), *"`X` is a `p`-group"*** (mmd L4264).

BG states this in a single clause — *"Then `O_{p'}(H)` is abelian because `C_H(X₁)` is abelian.
Hence `P = O_p(H)` is not abelian and `X` is a `p`-group"* — without spelling out why the last
conjunct follows.  The argument is a collision between two facts already established for the
non-TI witness:

* **every** prime `d ∣ |X|` has `O_d(M_F)` non-cyclic.  This is BG's opening step (*"If `O_p(M)` is
  cyclic, then `X₁` is normal in both `M` and `M^g`, which is impossible"*), available here as
  `not_isCyclic_opiCore_mf_of_orderP_le_conj` — it applies at `d` because an order-`d` subgroup of
  `X` lies in **both** `M_F` and `M_F^g` (`inf_conj_fitting_le_Msigma` and its conjugate, plus
  `M_F = M_σ`);
* `O_{p'}(M_F)` **is** cyclic when `M_F` is non-abelian
  (`typeF_nonabelian_cyclic_opiCore_compl`), and for `d ≠ p` the core `O_d(M_F)` sits inside it.

So no prime other than `p` can divide `|X|`. -/
theorem inf_conj_fitting_isPGroup_of_not_isMulCommutative [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnotTI : ¬ FittingIsTI M) {g : G} (hgM : g ∉ M) {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ MF M)
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M)
    (hnab : ¬ IsMulCommutative ↥(MF M)) :
    IsPGroup p ↥(fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M : Subgroup G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set X : Subgroup G := fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M with hXdef
  have hMFeq : MF M = OddOrder.BG.Ch3.S10.Msigma M := mf_eq_msigma_of_not_fittingIsTI hG hM hnotTI
  -- `X ≤ M_F` and `X ≤ M_F^g` (Theorem 15.7(b), with `M_F = M_σ`).
  have hXMF : X ≤ MF M := (inf_conj_fitting_le_Msigma hG hM hgM).trans (le_of_eq hMFeq.symm)
  have hXcMF : X ≤ MulAut.conj g • MF M := by
    rw [hMFeq]; exact inf_conj_fitting_le_conj_Msigma hG hM hgM
  -- `O_{p'}(M_F)` is cyclic (BG (e2)/(e3) conjunct B).
  have hRcyc : IsCyclic ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (MF M)) :=
    (typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF hCGnotM hnab).2
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
  intro d hd hdvd
  by_contra hdp
  haveI : Fact d.Prime := ⟨hd⟩
  -- an order-`d` subgroup `Z ≤ X`, hence `Z ≤ M_F` and `Z ≤ M_F^g`.
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) d hdvd
  set Z : Subgroup G := (Subgroup.zpowers z).map X.subtype with hZdef
  have hZX : Z ≤ X := hZdef ▸ Subgroup.map_subtype_le _
  have hZcard : Nat.card ↥Z = d := by
    rw [hZdef, Subgroup.card_map_of_injective X.subtype_injective, Nat.card_zpowers, hzord]
  -- BG's opening step at `d`: `O_d(M_F)` is not cyclic.
  refine not_isCyclic_opiCore_mf_of_orderP_le_conj hG hM hd hgM hZcard (hZX.trans hXMF)
    (hZX.trans hXcMF) ?_
  -- ... but `d ≠ p` puts `O_d(M_F)` inside the cyclic `O_{p'}(M_F)`.
  have hle : opiCoreInG ({d} : Set ℕ) (MF M) ≤ opiCoreInG (({p} : Set ℕ)ᶜ) (MF M) :=
    Subgroup.map_mono (OddOrder.Isaacs.Ch03.oPiCore_mono
      (Set.singleton_subset_iff.mpr (Set.mem_compl_singleton_iff.mpr hdp)) ↥(MF M))
  haveI : IsCyclic ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (MF M)) := hRcyc
  exact Subgroup.isCyclic_of_le hle

end OddOrder.BG.Ch4.S15
