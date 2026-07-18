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

/-- **BG Theorem 15.7(e), conjunct A per-prime witness** (Coq `oZ`: `|Ω₁(Z(O_q(H)))| = q`): for the
non-TI witness data and a non-abelian `M_F`, every prime `q ∈ π(M_F)` has an order-`q` subgroup `Z`
of `M_F` that is normal in `M` (hence `td.U0`-invariant), feeding
`typeF_exponent_dvd_sub_one_of_invariant_card`.

* `q ≠ p`: `O_q(M_F) ≤ O_{p'}(M_F)` is cyclic (`typeF_nonabelian_cyclic_opiCore_compl`), so its unique
  order-`q` subgroup `Ω₁(O_q(M_F))` is characteristic (`characteristic_of_subgroup_of_isCyclic`) in
  `O_q(M_F)`, characteristic in `M_F`, hence normal in `M`.
* `q = p`: `Z = Ω₁(Z(O_p(M_F)))`; `|Z| = p` because `B = X₁ ⊔ Z` is elementary abelian of `p`-rank
  `≤ rank (M_F ⊓ C_G(X₁)) < 3`, forcing `pRank Z ≤ 1`, and `Z ≠ ⊥` (`O_p(M_F)` is a nontrivial
  `p`-group); `X₁ ⊄ Z` because `O_p(M_F)` is non-abelian (else `M_F = O_p ⊔ O_{p'}` abelian).

The conclusion also records `¬ X₁ ≤ Z` (`X₁ ⊄ Z`): for `q = p` this is the structural fact above;
for `q ≠ p` it is immediate from `|X₁| = p`, `|Z| = q` coprime.  This feeds the type-V Singer-case
faithfulness `K ⊓ C_G(O_p(M_F)) = ⊥` (`kappaHall_inf_centralizer_opiCore_eq_bot`). -/
theorem exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ MF M)
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M)
    (hrank3 : rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3)
    (hnab : ¬ IsMulCommutative ↥(MF M))
    {q : ℕ} (hq : q.Prime) (hqπ : q ∈ (Nat.card ↥(MF M)).primeFactors) :
    ∃ Z : Subgroup G, Z ≤ MF M ∧ Nat.card ↥Z = q ∧
      M ≤ Subgroup.normalizer (Z : Set G) ∧ ¬ X₁ ≤ Z ∧
      (q = p → Z = OddOrder.BG.Ch3.S10.omega1CenterInG (opiCoreInG ({p} : Set ℕ) (MF M)) p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  have hMNMF : M ≤ Subgroup.normalizer ((MF M : Subgroup G) : Set G) :=
    maxNilpotentNormalHall_le_normalizer M
  by_cases hqp : q = p
  · -- `q = p`: `Z = Ω₁(Z(O_p(M_F)))`, `|Z| = p` by the rank argument (Coq `oZ0`, L1085-1117).
    set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (MF M) with hPdef
    -- `X₁ ≤ P`, and `P` is a nontrivial `p`-group.
    have hX₁ne : X₁ ≠ ⊥ :=
      fun h => hp.one_lt.ne' (by rw [← hX₁card, h, Subgroup.card_bot])
    have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
    have hX₁P : X₁ ≤ P :=
      OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
    have hPne : P ≠ ⊥ := fun h => hX₁ne (le_bot_iff.mp (h ▸ hX₁P))
    haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
    have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (MF M)
    -- `P` non-abelian; `C₁ = C_{M_F}(X₁)` abelian.
    have hPnab : ¬ IsMulCommutative ↥P :=
      opiCore_singleton_not_isMulCommutative_of_witness hG hM hp hX₁card hX₁MF hCGnotM hnab
    set C1 : Subgroup G := MF M ⊓ Subgroup.centralizer (X₁ : Set G) with hC1def
    have hC1ab : IsMulCommutative ↥C1 :=
      isMulCommutative_mf_inf_centralizer_of_not_le hG hM hX₁ne hCGnotM
    -- `Z := Ω₁(Z(P))`, elementary abelian, `≤ P ≤ M_F`.
    set Z : Subgroup G := OddOrder.BG.Ch3.S10.omega1CenterInG P p with hZdef
    have hZP : Z ≤ P := OddOrder.BG.Ch3.S10.omega1CenterInG_le P p
    have hZMF : Z ≤ MF M := hZP.trans (opiCoreInG_le _ _)
    have hWea : (omega1OfAbelian ↥P (Subgroup.center ↥P) p
        (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm)).IsElementaryAbelian p :=
      omega1OfAbelian_isElementaryAbelian
    have hZea : Z.IsElementaryAbelian p := by rw [hZdef]; exact hWea.map P.subtype_injective
    -- `X₁` centralizes `Z` (`Z ≤ Z(P)`, `X₁ ≤ P`).
    have hX₁CZ : X₁ ≤ Subgroup.centralizer (Z : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [SetLike.mem_coe, hZdef, OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map] at hz
      obtain ⟨z', hz', hz'eq⟩ := hz
      have hz'c : z' ∈ Subgroup.center ↥P := (mem_omega1OfAbelian.mp hz').1
      rw [← hz'eq]
      simpa using (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'c ⟨x, hX₁P hx⟩)).symm
    -- `X₁ ⊄ Z`: else `X₁ ≤ Z(P)` ⟹ `P ≤ C_G(X₁)` ⟹ `P ≤ C₁` abelian (vs `hPnab`).
    have hX₁notZ : ¬ X₁ ≤ Z := by
      intro hsub
      refine hPnab ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      have hPCX₁ : P ≤ Subgroup.centralizer (X₁ : Set G) := by
        intro g hg
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hxZ : x ∈ Z := hsub hx
        rw [hZdef, OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map] at hxZ
        obtain ⟨x', hx', hx'eq⟩ := hxZ
        have hx'c : x' ∈ Subgroup.center ↥P := (mem_omega1OfAbelian.mp hx').1
        rw [← hx'eq]
        simpa using (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx'c ⟨g, hg⟩)).symm
      have hPC1 : P ≤ C1 := le_inf (opiCoreInG_le _ _) hPCX₁
      simpa using congrArg Subtype.val
        (isMulCommutative_iff.mp hC1ab ⟨(a : G), hPC1 a.2⟩ ⟨(b : G), hPC1 b.2⟩)
    -- `X₁ ⊓ Z = ⊥` (`X₁` prime order, `X₁ ⊄ Z`).
    have hX₁Zbot : X₁ ⊓ Z = ⊥ := by
      have hdvd : Nat.card ↥(X₁ ⊓ Z) ∣ p :=
        hX₁card ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpp
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exact absurd (inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left
          (by rw [hX₁card, hpp]))) hX₁notZ
    -- `B = X₁ ⊔ Z` elementary abelian, `≤ C₁`.
    have hX₁ea : X₁.IsElementaryAbelian p :=
      Subgroup.IsElementaryAbelian.of_card_prime hX₁card
    have hBea : (X₁ ⊔ Z).IsElementaryAbelian p :=
      isElementaryAbelian_sup_of_le_centralizer hX₁ea hZea hX₁CZ
    have hX₁C1 : X₁ ≤ C1 :=
      le_inf hX₁MF (le_centralizer_self_of_isElementaryAbelian hX₁ea)
    have hZC1 : Z ≤ C1 := by
      refine le_inf hZMF (fun z hz => ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hX₁CZ hx) z hz).symm
    have hBC1 : (X₁ ⊔ Z) ≤ C1 := sup_le hX₁C1 hZC1
    -- `|X₁ ⊔ Z| = p · |Z|`.
    have hX₁NZ : X₁ ≤ Subgroup.normalizer Z :=
      hX₁CZ.trans (Subgroup.centralizer_le_normalizer (Z : Set G))
    have hcoe : (↑X₁ * ↑Z : Set G) = ↑(X₁ ⊔ Z) :=
      (Subgroup.coe_mul_of_left_le_normalizer_right X₁ Z hX₁NZ).symm
    have hcardform : Nat.card ↥(X₁ ⊔ Z) = p * Nat.card ↥Z := by
      have h := Subgroup.card_HK_mul_card_inf_eq_card_mul_card X₁ Z
      rw [hcoe, hX₁Zbot, Subgroup.card_bot, mul_one, hX₁card] at h
      exact h
    -- `log_p |X₁ ⊔ Z| ≤ rank C₁ < 3`.
    have hBlog : Nat.log p (Nat.card ↥(X₁ ⊔ Z)) ≤ 2 := by
      have hB'ea : ((X₁ ⊔ Z).subgroupOf C1).IsElementaryAbelian p :=
        OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe hBC1).symm hBea
      have hB'card : Nat.card ↥((X₁ ⊔ Z).subgroupOf C1) = Nat.card ↥(X₁ ⊔ Z) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC1).toEquiv
      have h1 : Nat.log p (Nat.card ↥(X₁ ⊔ Z)) ≤ pRank ↥C1 p := by
        rw [← hB'card]; exact le_pRank _ hB'ea
      have h2 : pRank ↥C1 p ≤ rank ↥C1 := pRank_le_rank p
      have h3 : rank ↥C1 < 3 := hrank3
      omega
    -- `Z` is a nontrivial `p`-group, so `|Z| = p`.
    have hZpow : Nat.card ↥Z = p ^ (Nat.log p (Nat.card ↥Z)) := by
      rw [hZea.log_card_eq_finrank]; exact hZea.card_eq_pow_finrank
    have hZne : Z ≠ ⊥ := by
      haveI hcNt : Nontrivial ↥(Subgroup.center ↥P) := hPpg.center_nontrivial
      have hcdvd : Nat.card ↥(Subgroup.center ↥P) ∣ Nat.card ↥P :=
        Subgroup.card_subgroup_dvd_card _
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPpg
      have hpdvd : p ∣ Nat.card ↥(Subgroup.center ↥P) := by
        have h1 : 1 < Nat.card ↥(Subgroup.center ↥P) :=
          Finite.one_lt_card_iff_nontrivial.mpr hcNt
        rw [hk] at hcdvd
        obtain ⟨j, _, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hcdvd
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · rw [pow_zero] at hjeq; omega
        · rw [hjeq]; exact dvd_pow_self p hjpos.ne'
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥P)) p hpdvd
      have hwne : ((w : ↥P) : G) ≠ 1 := by
        intro hcoe1
        have : (w : ↥P) = 1 := by ext; simpa using hcoe1
        have hw1 : w = 1 := by ext; simpa using this
        rw [hw1, orderOf_one] at hw; exact hp.one_lt.ne' hw.symm
      refine fun hbot => hwne ?_
      have hmem : ((w : ↥P) : G) ∈ Z := by
        rw [hZdef, OddOrder.BG.Ch3.S10.omega1CenterInG]
        refine Subgroup.mem_map.mpr ⟨(w : ↥P), mem_omega1OfAbelian.mpr ⟨w.2, ?_⟩, rfl⟩
        have : w ^ p = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
        simpa using congrArg (Subtype.val (p := fun a => a ∈ Subgroup.center ↥P)) this
      rw [hbot] at hmem; simpa using hmem
    obtain ⟨d, hd⟩ : ∃ d, Nat.card ↥Z = p ^ d := ⟨_, hZpow⟩
    have hsupeq : Nat.card ↥(X₁ ⊔ Z) = p ^ (d + 1) := by rw [hcardform, hd, pow_succ']
    rw [hsupeq, Nat.log_pow hp.one_lt] at hBlog
    have hd_ge : 1 ≤ d := by
      by_contra h
      have hd0 : d = 0 := by omega
      rw [hd0, pow_zero] at hd
      exact hZne (Subgroup.eq_bot_of_card_eq _ hd)
    have hZcard : Nat.card ↥Z = p := by
      rw [hd, show d = 1 from le_antisymm (by omega) hd_ge, pow_one]
    -- `M ≤ N(Z)`: `M ≤ N(P) ≤ N(Ω₁(Z(P))) = N(Z)`.
    have hMNP : M ≤ Subgroup.normalizer (P : Set G) :=
      le_normalizer_opiCoreInG_of_le_normalizer ({p} : Set ℕ) hMNMF
    have hMNZ : M ≤ Subgroup.normalizer (Z : Set G) := by
      rw [hZdef]
      exact hMNP.trans (OddOrder.BG.Ch3.S10.normalizer_le_normalizer_omega1CenterInG P p)
    exact ⟨Z, hZMF, hZcard.trans hqp.symm, hMNZ, hX₁notZ, fun _ => hZdef⟩
  · -- `q ≠ p`: `O_q(M_F) ≤ O_{p'}(M_F)` is cyclic; take its order-`q` subgroup.
    have hqdvd : q ∣ Nat.card ↥(MF M) := (Nat.mem_primeFactors.mp hqπ).2.1
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(MF M)) q hqdvd
    set Z : Subgroup G := (Subgroup.zpowers x).map (MF M).subtype with hZdef
    have hZcard : Nat.card ↥Z = q := by
      rw [hZdef, Subgroup.card_map_of_injective (MF M).subtype_injective, Nat.card_zpowers, hxord]
    have hZMF : Z ≤ MF M := hZdef ▸ Subgroup.map_subtype_le _
    have hZpg : IsPGroup q ↥Z := IsPGroup.of_card (n := 1) (by rw [hZcard, pow_one])
    -- `Z ≤ O_q(M_F)` (a `q`-group inside the nilpotent `M_F`).
    have hZOq : Z ≤ opiCoreInG ({q} : Set ℕ) (MF M) :=
      OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hZMF hZpg
    -- `O_q(M_F) ≤ O_{p'}(M_F)` (as `q ≠ p`), and `O_{p'}(M_F)` is cyclic, so `O_q(M_F)` is cyclic.
    have hcyc : IsCyclic ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (MF M)) :=
      (typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF hCGnotM hnab).2
    have hOqle : opiCoreInG ({q} : Set ℕ) (MF M) ≤ opiCoreInG (({p} : Set ℕ)ᶜ) (MF M) :=
      Subgroup.map_mono (OddOrder.Isaacs.Ch03.oPiCore_mono
        (Set.singleton_subset_iff.mpr (Set.mem_compl_singleton_iff.mpr hqp)) ↥(MF M))
    haveI : IsCyclic ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (MF M)) := hcyc
    haveI hOqcyc : IsCyclic ↥(opiCoreInG ({q} : Set ℕ) (MF M)) := Subgroup.isCyclic_of_le hOqle
    -- `Z.subgroupOf O_q(M_F)` is characteristic (subgroup of a cyclic group).
    haveI hWchar : (Z.subgroupOf (opiCoreInG ({q} : Set ℕ) (MF M))).Characteristic :=
      OddOrder.Isaacs.Ch04.characteristic_of_subgroup_of_isCyclic _
    -- `M ≤ N(O_q(M_F)) ≤ N(Z)`.
    have hMNOq : M ≤ Subgroup.normalizer ((opiCoreInG ({q} : Set ℕ) (MF M) : Subgroup G) : Set G) :=
      le_normalizer_opiCoreInG_of_le_normalizer ({q} : Set ℕ) hMNMF
    have hZeq : (Z.subgroupOf (opiCoreInG ({q} : Set ℕ) (MF M))).map
        (opiCoreInG ({q} : Set ℕ) (MF M)).subtype = Z :=
      Subgroup.map_subgroupOf_eq_of_le hZOq
    have hMNZ : M ≤ Subgroup.normalizer (Z : Set G) := by
      rw [← hZeq]
      exact hMNOq.trans (OddOrder.Isaacs.Ch07.normalizer_le_normalizer_map_of_characteristic)
    -- `¬ X₁ ≤ Z`: `|X₁| = p`, `|Z| = q`, `p ≠ q`, so `X₁ ≤ Z` would force `p ∣ q`.
    have hX₁notZ : ¬ X₁ ≤ Z := by
      intro hle
      have hdvd : p ∣ q := by
        have h := Subgroup.card_dvd_of_le hle; rwa [hX₁card, hZcard] at h
      exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd).symm
    exact ⟨Z, hZMF, hZcard, hMNZ, hX₁notZ, fun h => absurd h hqp⟩

/-! ### The TI-failure intersection `X = F(M) ∩ F(M)ᵍ` (BG Theorem 15.7(b))

BG Theorem 15.7 fixes `g ∈ G − M` with `X = F(M) ∩ F(M)^g ≠ 1` and asserts in (b) that this
*particular* `X` satisfies `X ⊆ H = M_F` and is cyclic.  The three lemmas below supply exactly
that pinned form, so that `fitting_not_ti_cases` can state (b) about `F(M) ⊓ F(M)^g` itself rather
than about *some* cyclic subgroup of `M_F` (which would be equivalent to `M_F ≠ 1`; see issue
3022). -/

/-- **BG Theorem 15.7(e), the rank-two elementary abelian `B = X₁ × Ω₁(Z(P))`** (mmd L4266:
*"Let `Z₀ = Ω₁(Z(P))`.  Clearly `X₁ ≠ Z₀`.  Let `B = X₁ × Z₀`.  Now we know
`B ∈ ℰ²(P) ∩ ℰ*(P)` because `C_H(X₁)` has rank less than 3.  Thus `|Z₀| = p`"*).

Step 2 of the `p = |X|` chain.  Everything about `Z₀` itself — `|Z₀| = p`, `X₁ ⊄ Z₀`, and the
identification `Z₀ = Ω₁(Z(O_p(M_F)))` — is already delivered by
`exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI` at `q := p` (its `q = p` branch *is* BG's
rank argument), so this lemma only assembles `B` on top of it: `X₁ ∩ Z₀ = 1` from `|X₁| = p` prime
and `X₁ ⊄ Z₀`, `X₁` centralizes `Z₀` because `Z₀ ≤ Z(P)` and `X₁ ≤ P`, and hence `B = X₁ ⊔ Z₀` is
elementary abelian of order `p²` inside the abelian `C₁ = C_{M_F}(X₁)`.

⚠ The **maximality** half of BG's `B ∈ ℰ*(P)` is *not* included: `IsMaximalElementaryAbelian` is
stated relative to the ambient group (here `G`), whereas BG asserts maximality in `P`, and the two
need a bridge.  Lemma 10.13 consumes the ambient-`G` form, so that bridge is the remaining gap
(issue 3022). -/
theorem exists_rankTwo_elemAbelian_of_witness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ MF M)
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M)
    (hrank3 : rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3)
    (hnab : ¬ IsMulCommutative ↥(MF M)) :
    ∃ Z : Subgroup G,
      Z = OddOrder.BG.Ch3.S10.omega1CenterInG (opiCoreInG ({p} : Set ℕ) (MF M)) p ∧
      Nat.card ↥Z = p ∧ Z ≤ opiCoreInG ({p} : Set ℕ) (MF M) ∧
      X₁ ⊓ Z = ⊥ ∧ X₁ ≤ Subgroup.centralizer (Z : Set G) ∧
      (X₁ ⊔ Z).IsElementaryAbelian p ∧
      Nat.card ↥(X₁ ⊔ Z) = p ^ 2 ∧
      (X₁ ⊔ Z) ≤ MF M ⊓ Subgroup.centralizer (X₁ : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (MF M) with hPdef
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hX₁P : X₁ ≤ P :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  -- `p ∈ π(M_F)`, so the per-prime witness applies at `q := p`.
  have hpπ : p ∈ (Nat.card ↥(MF M)).primeFactors :=
    (typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF hCGnotM hnab).1
  obtain ⟨Z, hZMF, hZcard, -, hX₁notZ, hZeq⟩ :=
    exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI hG hM hp hX₁card hX₁MF hCGnotM hrank3 hnab
      hp hpπ
  have hZdef : Z = OddOrder.BG.Ch3.S10.omega1CenterInG P p := hZeq rfl
  have hZP : Z ≤ P := hZdef ▸ OddOrder.BG.Ch3.S10.omega1CenterInG_le P p
  -- `X₁` centralizes `Z` (`Z ≤ Z(P)` and `X₁ ≤ P`).
  have hX₁CZ : X₁ ≤ Subgroup.centralizer (Z : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [SetLike.mem_coe, hZdef, OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map] at hz
    obtain ⟨z', hz', hz'eq⟩ := hz
    have hz'c : z' ∈ Subgroup.center ↥P := (mem_omega1OfAbelian.mp hz').1
    rw [← hz'eq]
    simpa using (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'c ⟨x, hX₁P hx⟩)).symm
  -- `X₁ ∩ Z = 1` (`|X₁| = p` prime and `X₁ ⊄ Z`).
  have hX₁Zbot : X₁ ⊓ Z = ⊥ := by
    have hdvd : Nat.card ↥(X₁ ⊓ Z) ∣ p := hX₁card ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpp
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exact absurd (inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left
        (by rw [hX₁card, hpp]))) hX₁notZ
  -- `B = X₁ ⊔ Z` is elementary abelian of order `p²`, inside the abelian `C₁ = C_{M_F}(X₁)`.
  have hX₁ea : X₁.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hX₁card
  have hZea : Z.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hZcard
  have hBea : (X₁ ⊔ Z).IsElementaryAbelian p :=
    isElementaryAbelian_sup_of_le_centralizer hX₁ea hZea hX₁CZ
  have hBcard : Nat.card ↥(X₁ ⊔ Z) = p ^ 2 := by
    have hX₁NZ : X₁ ≤ Subgroup.normalizer Z :=
      hX₁CZ.trans (Subgroup.centralizer_le_normalizer (Z : Set G))
    have hcoe : (↑X₁ * ↑Z : Set G) = ↑(X₁ ⊔ Z) :=
      (Subgroup.coe_mul_of_left_le_normalizer_right X₁ Z hX₁NZ).symm
    have h := Subgroup.card_HK_mul_card_inf_eq_card_mul_card X₁ Z
    rw [hcoe, hX₁Zbot, Subgroup.card_bot, mul_one, hX₁card, hZcard] at h
    rw [sq]
    exact h
  have hX₁C1 : X₁ ≤ MF M ⊓ Subgroup.centralizer (X₁ : Set G) :=
    le_inf hX₁MF (le_centralizer_self_of_isElementaryAbelian hX₁ea)
  have hZC1 : Z ≤ MF M ⊓ Subgroup.centralizer (X₁ : Set G) := by
    refine le_inf hZMF (fun z hz => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hX₁CZ hx) z hz).symm
  exact ⟨Z, hZdef, hZcard, hZP, hX₁Zbot, hX₁CZ, hBea, hBcard, sup_le hX₁C1 hZC1⟩

end OddOrder.BG.Ch4.S15
