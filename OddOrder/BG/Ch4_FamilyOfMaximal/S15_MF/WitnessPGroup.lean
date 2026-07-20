import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF.TIFailure

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

* `q ≠ p`: `O_q(M_F) ≤ O_{p'}(M_F)` is cyclic (`typeF_nonabelian_cyclic_opiCore_compl`),
  so its unique
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

/-- **`O_p(M_F)` is a Sylow `p`-subgroup of `G`** (Coq `sylP_G`): for a maximal `M` with
`M_F = M_σ` and `p ∈ σ(M)`, the `p`-core `P = O_p(M_F)` is a Sylow `p`-subgroup of `G`.

`P` is a `{p}`-Hall (hence Sylow) subgroup of the nilpotent `M_F = M_σ`
(`oPiCore_isHall_of_isNilpotent`: `p ∤ [M_F : P]`), so `|P| = p^{v_p(|M_F|)}` is the full `p`-part
of
`|M_σ|`; and since `M_σ` is the `σ`-Hall of `G` with `p ∈ σ` (`Msigma_isHall`: `p ∤ [G : M_σ]`),
that
`p`-part equals `v_p(|G|)`.  Thus `|P| = p^{v_p(|G|)}`, so `Sylow.ofCard` exhibits `P` as a Sylow
`p`-subgroup of `G`.  This is the `mFT_rank2_Sylow_cprod` Sylow input for the type-V Singer case
(`card_opiCore_eq_prime_cube_singer`). -/
theorem exists_sylow_eq_opiCore_of_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hmf : MF M = OddOrder.BG.Ch3.S10.Msigma M) {p : ℕ} (hp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M) :
    ∃ S : Sylow p G, (S : Subgroup G) = opiCoreInG ({p} : Set ℕ) (MF M) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (MF M) with hPdef
  -- `P` is a `p`-group: `|P| = p^a`.
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (MF M)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hPpg
  suffices hcard : Nat.card ↥P = p ^ (Nat.card G).factorization p by
    exact ⟨Sylow.ofCard P hcard, Sylow.coe_ofCard P hcard⟩
  -- `v_p(|M_F|) = a`: `P = O_p(M_F)` is a `{p}`-Hall of `M_F` (`p ∤ [M_F : P]`).
  have hP'hall : Ch03.IsHallSubgroup ({p} : Set ℕ) (Ch03.oPiCore ({p} : Set ℕ) ↥(MF M)) :=
    OddOrder.BG.Ch3.S10.oPiCore_isHall_of_isNilpotent _
  have hPcard : Nat.card ↥P = Nat.card ↥(Ch03.oPiCore ({p} : Set ℕ) ↥(MF M)) :=
    Subgroup.card_map_of_injective (MF M).subtype_injective
  have hpidxP : ¬ p ∣ (Ch03.oPiCore ({p} : Set ℕ) ↥(MF M)).index := fun h =>
    hP'hall.2 p (Nat.mem_primeFactors.mpr ⟨hp, h, Subgroup.index_ne_zero_of_finite⟩)
      (Set.mem_singleton_iff.mpr rfl)
  have hMFfact : (Nat.card ↥(MF M)).factorization p = a := by
    rw [← Subgroup.card_mul_index (Ch03.oPiCore ({p} : Set ℕ) ↥(MF M)),
      Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpidxP, add_zero, ← hPcard, ha,
      Nat.factorization_pow_self hp]
  -- `v_p(|G|) = v_p(|M_σ|)`: `M_σ` is the `σ`-Hall of `G`, `p ∈ σ`, so `p ∤ [G : M_σ]`.
  have hσHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG hM
  have hpidxσ : ¬ p ∣ (OddOrder.BG.Ch3.S10.Msigma M).index := fun h =>
    hσHall.2 p (Nat.mem_primeFactors.mpr ⟨hp, h, Subgroup.index_ne_zero_of_finite⟩) hpσ
  have hGa : (Nat.card G).factorization p = a := by
    rw [← Subgroup.card_mul_index (OddOrder.BG.Ch3.S10.Msigma M),
      Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpidxσ, add_zero, ← hmf, hMFfact]
  rw [ha, hGa]

/-- **BG Theorem 15.7(e), maximality of `B = X₁ × Ω₁(Z(P))`** (mmd L4266 *"`B ∈ ℰ²(P) ∩ ℰ*(P)`
because `C_H(X₁)` has rank less than 3"*; Coq `BGsection15.v` `max_rB` / `p2maxElemB`).

Note BG's `ℰ*(P)` means *maximal in `G`, contained in `P`* — the Coq statement is
`B \in 'E_p^2(G) :&: 'E*_p(G)`, and `IsMaximalElementaryAbelian` here likewise quantifies over the
ambient `G`.

The rank bound `rank (M_F ⊓ C_G(X₁)) < 3` only constrains subgroups **inside** `P`, so an arbitrary
elementary abelian `A ⊇ B` must first be pushed into `P` by conjugation:

* `P = O_p(M_F)` is a Sylow `p`-subgroup of `G` (`exists_sylow_eq_opiCore_of_mf_eq_msigma`, Coq
  `sylP_G`), so Sylow conjugacy gives `a` with `A^a ≤ P`.
* `a` need not normalize `X₁`.  It is corrected by **σ-Hall tameness** (BG Corollary 15.3(b),
  `mf_hall_centralizer_control`): `x₁` and `x₁^a` both lie in the Hall subgroup `P` of `M_σ` and are
  `G`-conjugate, so `x₁^a = x₁^n` for some `n ∈ N_G(P)`.  Then `c = n⁻¹a` centralizes `x₁` — hence
  normalizes `X₁` — and still satisfies `A^c ≤ P`.
* `A` is abelian and contains `X₁`, so `A ≤ C_G(X₁)`; as `c` normalizes `X₁`, also `A^c ≤ C_G(X₁)`.
  Thus `A^c ≤ M_F ⊓ C_G(X₁)`, whose rank is `< 3`, giving `|A| = |A^c| ≤ p²`.

Since `|B| = p²` and `B ≤ A`, this forces `A = B`. -/
theorem isMaximalElementaryAbelian_sup_omega1Center_of_witness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hmf : MF M = OddOrder.BG.Ch3.S10.Msigma M) {p : ℕ} {X₁ Z : Subgroup G} (hp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ MF M)
    (hrank3 : rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3)
    (_hZP : Z ≤ opiCoreInG ({p} : Set ℕ) (MF M))
    (hBea : (X₁ ⊔ Z).IsElementaryAbelian p)
    (hBcard : Nat.card ↥(X₁ ⊔ Z) = p ^ 2) :
    IsMaximalElementaryAbelian p (X₁ ⊔ Z) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (MF M) with hPdef
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hX₁P : X₁ ≤ P :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  have hPMF : P ≤ MF M := opiCoreInG_le _ _
  refine ⟨hBea, fun A hAea hBA => ?_⟩
  -- `A` is a `p`-group containing `X₁`, and abelian, so `A ≤ C_G(X₁)`.
  have hApg : IsPGroup p ↥A := hAea.isPGroup
  have hX₁A : X₁ ≤ A := le_sup_left.trans hBA
  have hACX₁ : A ≤ Subgroup.centralizer (X₁ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simpa using congrArg Subtype.val (hAea.1 ⟨y, hX₁A hy⟩ ⟨x, hx⟩)
  -- `P` is a Sylow `p`-subgroup of `G` (Coq `sylP_G`); push `A` into it.
  obtain ⟨SP, hSP⟩ := exists_sylow_eq_opiCore_of_mf_eq_msigma hG hM hmf hp hpσ
  obtain ⟨SA, hASA⟩ := hApg.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G SA SP
  have hAaP : MulAut.conj a • A ≤ P := by
    have h1 : MulAut.conj a • A ≤ MulAut.conj a • (SA : Subgroup G) :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hASA
    have h2 : MulAut.conj a • (SA : Subgroup G) = (SP : Subgroup G) := by
      rw [← ha]; rfl
    rw [hPdef]
    rw [hSP] at h2
    exact h1.trans (le_of_eq h2)
  -- A generator `x₁` of the order-`p` group `X₁`.
  have hX₁ne : X₁ ≠ ⊥ := fun h => hp.one_lt.ne' (by rw [← hX₁card, h, Subgroup.card_bot])
  obtain ⟨x₁', hx₁ne'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX₁ne
  set x₁ : G := (x₁' : G) with hx₁val
  have hx₁X : x₁ ∈ X₁ := x₁'.2
  have hx₁ne : x₁ ≠ 1 := fun h => hx₁ne' (Subtype.ext h)
  have hX₁gen : Subgroup.zpowers x₁ = X₁ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx₁X) ?_
    have hdvd : Nat.card ↥(Subgroup.zpowers x₁) ∣ p :=
      hX₁card ▸ Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx₁X)
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpp
    · exact absurd (Subgroup.mem_bot.mp ((Subgroup.eq_bot_of_card_eq _ h1) ▸
        Subgroup.mem_zpowers x₁)) hx₁ne
    · rw [hX₁card, hpp]
  -- σ-Hall tameness (BG Cor 15.3(b)) at the Hall subgroup `P` of `M_σ`.
  have hPMσ : P ≤ OddOrder.BG.Ch3.S10.Msigma M := hmf ▸ hPMF
  have hPne : P ≠ ⊥ := fun h => hX₁ne (le_bot_iff.mp (h ▸ hX₁P))
  haveI hMσnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := hmf ▸ hMFnil
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (MF M)
  have hPpiSet : S14.piSet P = ({p} : Set ℕ) := by
    ext q
    simp only [S14.piSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hq
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPpg
      have hqd := (Nat.mem_primeFactors.mp hq).2.1
      rw [hk] at hqd
      exact (Nat.prime_dvd_prime_iff_eq (Nat.mem_primeFactors.mp hq).1 hp).mp
        ((Nat.mem_primeFactors.mp hq).1.dvd_of_dvd_pow hqd)
    · intro hqp
      rw [hqp]
      have h1 : 1 < Nat.card ↥P :=
        Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot P).mpr hPne)
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPpg
      have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk; omega
      exact Nat.mem_primeFactors.mpr ⟨hp, hk ▸ dvd_pow_self p hk0, Nat.card_pos.ne'⟩
  have hPsubOf : P.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)
      = Ch03.oPiCore ({p} : Set ℕ) ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
    rw [hPdef, hmf, opiCoreInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (OddOrder.BG.Ch3.S10.Msigma M).subtype_injective]
  have hPhall : Ch03.IsHallSubgroup (S14.piSet P)
      (P.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) := by
    rw [hPpiSet, hPsubOf]
    exact OddOrder.BG.Ch3.S10.oPiCore_isHall_of_isNilpotent _
  have htame := (mf_hall_centralizer_control hG hM hPMσ hPhall hPne).2
  have hx₁P : x₁ ∈ P := hX₁P hx₁X
  have hax₁P : a * x₁ * a⁻¹ ∈ P := by
    refine hAaP ?_
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hX₁A hx₁X
  obtain ⟨n, hnN, hn⟩ := htame x₁ hx₁P (a * x₁ * a⁻¹) hax₁P ⟨a, rfl⟩
  -- `c = n⁻¹a` fixes `x₁`, and still maps `A` into `P`.
  set c : G := n⁻¹ * a with hcdef
  have hcx₁ : c * x₁ * c⁻¹ = x₁ := by
    have hstep : n⁻¹ * (a * x₁ * a⁻¹) * n = x₁ := by
      rw [hn]; group
    calc c * x₁ * c⁻¹ = n⁻¹ * (a * x₁ * a⁻¹) * n := by rw [hcdef]; group
      _ = x₁ := hstep
  have hAcP : MulAut.conj c • A ≤ P := by
    have hnP : MulAut.conj n⁻¹ • P = P :=
      conj_smul_eq_self_of_mem_normalizer (inv_mem hnN)
    calc MulAut.conj c • A = MulAut.conj n⁻¹ • (MulAut.conj a • A) := by
          rw [hcdef, ← mul_smul, ← map_mul]
      _ ≤ MulAut.conj n⁻¹ • P := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hAaP
      _ = P := hnP
  -- `A ≤ C_G(X₁)` and `c` fixes `x₁`, so `A^c ≤ C_G(X₁)` too.
  have hAcCX₁ : MulAut.conj c • A ≤ Subgroup.centralizer (X₁ : Set G) := by
    intro y hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    set z : G := c⁻¹ * y * c with hzdef
    have hzA : z ∈ A := by
      simpa [MulAut.smul_def, MulAut.conj_apply, hzdef, mul_assoc] using hy
    have hyz : y = c * z * c⁻¹ := by rw [hzdef]; group
    have hzx₁ : z * x₁ = x₁ * z :=
      (Subgroup.mem_centralizer_iff.mp (hACX₁ hzA) x₁ hx₁X).symm
    have hcomm : Commute y x₁ := by
      show y * x₁ = x₁ * y
      calc y * x₁ = c * z * c⁻¹ * (c * x₁ * c⁻¹) := by rw [← hyz, hcx₁]
        _ = c * (z * x₁) * c⁻¹ := by group
        _ = c * (x₁ * z) * c⁻¹ := by rw [hzx₁]
        _ = (c * x₁ * c⁻¹) * (c * z * c⁻¹) := by group
        _ = x₁ * y := by rw [hcx₁, ← hyz]
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [← hX₁gen, SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hw
    obtain ⟨k, rfl⟩ := hw
    exact ((hcomm.zpow_right k).symm : _)
  -- `A^c ≤ M_F ⊓ C_G(X₁)`, whose `p`-rank is `< 3`; hence `|A| ≤ p²`.
  set C1 : Subgroup G := MF M ⊓ Subgroup.centralizer (X₁ : Set G) with hC1def
  have hAcC1 : MulAut.conj c • A ≤ C1 := le_inf (hAcP.trans hPMF) hAcCX₁
  have hAcea : (MulAut.conj c • A).IsElementaryAbelian p :=
    OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
      (Subgroup.equivSMul (MulAut.conj c) A) hAea
  have hAccard : Nat.card ↥(MulAut.conj c • A) = Nat.card ↥A :=
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj c) A).toEquiv).symm
  have hlog : Nat.log p (Nat.card ↥A) ≤ 2 := by
    have hA'ea : ((MulAut.conj c • A).subgroupOf C1).IsElementaryAbelian p :=
      OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hAcC1).symm hAcea
    have hA'card : Nat.card ↥((MulAut.conj c • A).subgroupOf C1)
        = Nat.card ↥(MulAut.conj c • A) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAcC1).toEquiv
    have h1 : Nat.log p (Nat.card ↥A) ≤ pRank ↥C1 p := by
      rw [← hAccard, ← hA'card]; exact le_pRank _ hA'ea
    have h2 : pRank ↥C1 p ≤ rank ↥C1 := pRank_le_rank p
    have h3 : rank ↥C1 < 3 := hrank3
    omega
  have hAcardle : Nat.card ↥A ≤ p ^ 2 := by
    have hApow : Nat.card ↥A = p ^ (Nat.log p (Nat.card ↥A)) := by
      rw [hAea.log_card_eq_finrank]; exact hAea.card_eq_pow_finrank
    calc Nat.card ↥A = p ^ (Nat.log p (Nat.card ↥A)) := hApow
      _ ≤ p ^ 2 := Nat.pow_le_pow_right hp.one_lt.le hlog
  exact (Subgroup.eq_of_le_of_card_ge hBA (by rw [hBcard]; exact hAcardle)).symm

/-- **BG Theorem 15.7(e), `p = |X|`** (mmd L4266, *"Moreover, by Lemma 10.13(b),
`C_P(X₁) = C_P(B) = X₁ × Z` with `Z` cyclic.  Thus `X = X₁`"*; Coq `defX`).

The last step of the `p = |X|` chain: the TI-failure intersection `X = F(M) ∩ F(M)ᵍ` is *exactly*
the order-`p` witness `X₁`, so `|X| = p`.

`X` is a `p`-group (`inf_conj_fitting_isPGroup_of_not_isMulCommutative`) inside `M_F`, hence inside
`P = O_p(M_F)`, and it is cyclic (Theorem 15.7(b)).  It centralizes `B = X₁ ⊔ Z₀`: it contains `X₁`
and is abelian, and `Z₀ ≤ Z(P)` is centralized by all of `P`.  So Lemma 10.13(b), applied at
`A := B` and `A₀ := X₁`, puts `X` inside `C_G(B) ⊓ P = X₁ ⊔ Z` with `Z` cyclic and `X₁ ∩ Z = 1`.

Then `X ∩ Z = 1`: otherwise `X ∩ Z` would contain an order-`p` subgroup, which in the *cyclic* `X`
must be `X₁` itself (`eq_of_le_isCyclic_of_card_eq`), contradicting `X₁ ∩ Z = 1`.  Finally every
`x ∈ X` factors as `x = u·v` with `u ∈ X₁`, `v ∈ Z` (they commute, both lying in `C_G(B)`), and
`X₁` has exponent `p`, so `x^p = v^p ∈ X ∩ Z = 1`.  A cyclic group of exponent dividing `p`
containing the order-`p` group `X₁` is `X₁`. -/
theorem inf_conj_fitting_eq_of_not_isMulCommutative [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnotTI : ¬ FittingIsTI M) {g : G} (hgM : g ∉ M) {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M) (hX₁card : Nat.card ↥X₁ = p)
    (hX₁X : X₁ ≤ (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M : Subgroup G))
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M)
    (hrank3 : rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3)
    (hnab : ¬ IsMulCommutative ↥(MF M)) :
    (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M : Subgroup G) = X₁ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set X : Subgroup G := fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M with hXdef
  have hmf : MF M = OddOrder.BG.Ch3.S10.Msigma M := mf_eq_msigma_of_not_fittingIsTI hG hM hnotTI
  haveI hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (MF M) with hPdef
  have hXMF : X ≤ MF M := (inf_conj_fitting_le_Msigma hG hM hgM).trans (le_of_eq hmf.symm)
  have hX₁MF : X₁ ≤ MF M := hX₁X.trans hXMF
  have hXpg : IsPGroup p ↥X :=
    inf_conj_fitting_isPGroup_of_not_isMulCommutative hG hM hnotTI hgM hp hX₁card hX₁MF hCGnotM hnab
  have hXP : X ≤ P :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hXMF hXpg
  haveI hXcyc : IsCyclic ↥X := inf_conj_fitting_isCyclic hG hM hgM
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hX₁P : X₁ ≤ P :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  have hX₁ne : X₁ ≠ ⊥ := fun h => hp.one_lt.ne' (by rw [← hX₁card, h, Subgroup.card_bot])
  -- The rank-two `B = X₁ ⊔ Z₀` and its maximality.
  obtain ⟨Z₀, hZ₀def, hZ₀card, hZ₀P, hX₁Z₀bot, hX₁CZ₀, hBea, hBcard, hBC1⟩ :=
    exists_rankTwo_elemAbelian_of_witness hG hM hp hX₁card hX₁MF hCGnotM hrank3 hnab
  have hBmax := isMaximalElementaryAbelian_sup_omega1Center_of_witness hG hM hmf hp hpσ hX₁card
    hX₁MF hrank3 hZ₀P hBea hBcard
  have hBP : (X₁ ⊔ Z₀) ≤ P := sup_le hX₁P hZ₀P
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (MF M)
  have hPnab : ¬ IsMulCommutative ↥P :=
    opiCore_singleton_not_isMulCommutative_of_witness hG hM hp hX₁card hX₁MF hCGnotM hnab
  have hpG : p ∈ (Nat.card G).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hX₁card ▸ Subgroup.card_subgroup_dvd_card X₁, Nat.card_pos.ne'⟩
  have hX₁ea : X₁.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hX₁card
  have hX₁neZ₀ : X₁ ≠ OddOrder.BG.Ch3.S10.omega1CenterInG P p := by
    rw [← hZ₀def]
    intro h
    rw [h, inf_idem] at hX₁Z₀bot
    exact hX₁ne (h.trans hX₁Z₀bot)
  -- Lemma 10.13(b) at `A := B`, `A₀ := X₁`.
  obtain ⟨-, ⟨Z, hZP, hZcyc, -, hX₁Zbot, hCPB⟩, -⟩ :=
    OddOrder.BG.Ch3.S10.nonabelian_pSubgroup_rankTwo_elemAbelian_structure hG hpG
      ⟨hBea, hBcard⟩ hBmax hPpg hPnab hBP ⟨⟨hX₁ea, by rw [hX₁card, pow_one]⟩, le_sup_left⟩
      hX₁neZ₀
  -- `X ≤ C_G(B) ⊓ P = X₁ ⊔ Z`.
  have hXCZ₀ : X ≤ Subgroup.centralizer (Z₀ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [SetLike.mem_coe, hZ₀def, OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map] at hz
    obtain ⟨z', hz', hz'eq⟩ := hz
    have hz'c : z' ∈ Subgroup.center ↥P := (mem_omega1OfAbelian.mp hz').1
    rw [← hz'eq]
    simpa using (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'c ⟨x, hXP hx⟩)).symm
  have hXCB : X ≤ Subgroup.centralizer ((X₁ ⊔ Z₀ : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hXab : ∀ u v : ↥X, u * v = v * u := fun u v =>
      (IsCyclic.commGroup (α := ↥X)).mul_comm u v
    have hxX₁ : ∀ y ∈ X₁, y * x = x * y := fun y hy => by
      simpa using congrArg Subtype.val (hXab ⟨y, hX₁X hy⟩ ⟨x, hx⟩)
    have hxZ₀ : ∀ y ∈ Z₀, y * x = x * y := fun y hy =>
      Subgroup.mem_centralizer_iff.mp (hXCZ₀ hx) y hy
    have hcoe : (↑X₁ * ↑Z₀ : Set G) = ↑(X₁ ⊔ Z₀) :=
      (Subgroup.coe_mul_of_left_le_normalizer_right X₁ Z₀
        (hX₁CZ₀.trans (Subgroup.centralizer_le_normalizer _))).symm
    have hwset : w ∈ (↑X₁ * ↑Z₀ : Set G) := by rw [hcoe]; exact hw
    obtain ⟨u, hu, v, hv, rfl⟩ := hwset
    rw [mul_assoc, hxZ₀ v hv, ← mul_assoc, hxX₁ u hu, mul_assoc]
  have hXsup : X ≤ X₁ ⊔ Z := hCPB ▸ le_inf hXCB hXP
  -- `X ∩ Z = 1`.
  have hXZbot : X ⊓ Z = ⊥ := by
    by_contra hne
    obtain ⟨y, hyne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hypg : IsPGroup p ↥(X ⊓ Z) := hXpg.to_le inf_le_left
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X ⊓ Z)) p
      (by
        have h1 : 1 < Nat.card ↥(X ⊓ Z) :=
          Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot _).mpr hne)
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hypg
        have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk; omega
        exact hk ▸ dvd_pow_self p hk0)
    set W : Subgroup G := (Subgroup.zpowers w).map (X ⊓ Z).subtype with hWdef
    have hWcard : Nat.card ↥W = p := by
      rw [hWdef, Subgroup.card_map_of_injective (X ⊓ Z).subtype_injective, Nat.card_zpowers, hw]
    have hWX : W ≤ X := (hWdef ▸ Subgroup.map_subtype_le _ : W ≤ X ⊓ Z).trans inf_le_left
    have hWZ : W ≤ Z := (hWdef ▸ Subgroup.map_subtype_le _ : W ≤ X ⊓ Z).trans inf_le_right
    have hWX₁ : W = X₁ :=
      eq_of_le_isCyclic_of_card_eq (C := X) hWX hX₁X (by rw [hWcard, hX₁card])
    exact hX₁ne (le_bot_iff.mp (hX₁Zbot ▸ le_inf (hWX₁ ▸ le_refl W) (hWX₁ ▸ hWZ)))
  -- Every `x ∈ X` has `x^p ∈ X ⊓ Z = 1`, so `X` has exponent dividing `p`.
  have hZCX₁ : Z ≤ Subgroup.centralizer (X₁ : Set G) := by
    intro z hz
    have hmem : z ∈ Subgroup.centralizer ((X₁ ⊔ Z₀ : Subgroup G) : Set G) ⊓ P := by
      rw [hCPB]; exact (le_sup_right : Z ≤ X₁ ⊔ Z) hz
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hmem.1
  have hX₁CZ : X₁ ≤ Subgroup.centralizer (Z : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hZCX₁ hz) y hy).symm
  have hXexp : ∀ x ∈ X, x ^ p = 1 := by
    intro x hx
    have hcoe : (↑X₁ * ↑Z : Set G) = ↑(X₁ ⊔ Z) :=
      (Subgroup.coe_mul_of_left_le_normalizer_right X₁ Z
        (hX₁CZ.trans (Subgroup.centralizer_le_normalizer _))).symm
    have hxset : x ∈ (↑X₁ * ↑Z : Set G) := by rw [hcoe]; exact hXsup hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hxset
    have hcomm : Commute u v := Subgroup.mem_centralizer_iff.mp (hZCX₁ hv) u hu
    have hup : u ^ p = 1 := by
      have hsub : (⟨u, hu⟩ : ↥X₁) ^ p = 1 := by rw [← hX₁card]; exact pow_card_eq_one'
      simpa using congrArg Subtype.val hsub
    have hxp : (u * v) ^ p = v ^ p := by rw [hcomm.mul_pow, hup, one_mul]
    have hmem : (u * v) ^ p ∈ X ⊓ Z := ⟨pow_mem hx p, hxp ▸ pow_mem hv p⟩
    rw [hXZbot, Subgroup.mem_bot] at hmem
    exact hmem
  -- A cyclic group of exponent dividing `p` containing the order-`p` `X₁` equals `X₁`.
  refine (Subgroup.eq_of_le_of_card_ge hX₁X ?_).symm
  have hXcard_dvd : Nat.card ↥X ∣ p := by
    obtain ⟨x, hx⟩ := hXcyc.exists_generator
    have hord : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (by
      have := hXexp (x : G) x.2
      exact Subtype.ext (by simpa using this))
    have : Nat.card ↥X = orderOf x := by
      rw [← Nat.card_zpowers x, (Subgroup.eq_top_iff' _).mpr hx]
      exact (Nat.card_congr (Subgroup.topEquiv).toEquiv).symm
    rw [this]; exact hord
  rcases (Nat.dvd_prime hp).mp hXcard_dvd with h1 | hpp
  · exact absurd (le_bot_iff.mp (Subgroup.eq_bot_of_card_eq _ h1 ▸ hX₁X)) hX₁ne
  · rw [hpp, hX₁card]

/-- **BG Theorem 15.7(e), `p = |X|`** — the cardinality form BG's (e2)/(e3) actually quote.
Immediate from `inf_conj_fitting_eq_of_not_isMulCommutative` (`X = X₁`) and `|X₁| = p`. -/
theorem card_inf_conj_fitting_eq_of_not_isMulCommutative [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnotTI : ¬ FittingIsTI M) {g : G} (hgM : g ∉ M) {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M) (hX₁card : Nat.card ↥X₁ = p)
    (hX₁X : X₁ ≤ (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M : Subgroup G))
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M)
    (hrank3 : rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3)
    (hnab : ¬ IsMulCommutative ↥(MF M)) :
    Nat.card ↥(fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M : Subgroup G) = p := by
  rw [inf_conj_fitting_eq_of_not_isMulCommutative hG hM hnotTI hgM hp hpσ hX₁card hX₁X hCGnotM
    hrank3 hnab]
  exact hX₁card

/-- **`|K*| = p` in the type-`P₁` non-TI case** (Coq `oKs`, `BGsection15.v:1178`): for a type-`P₁`
maximal `M` with `M_F = M_σ` and cyclic `O_{p'}(M_F)`, the order of `K* = C_{M_σ}(K)` is exactly the
witness prime `p`.

This is the step that lets BG's `(e2)` branch conclude `q = p` from `Z_q = K*` (the per-prime
witnesses satisfy `|Z_q| = q`, so `Z_q = K*` forces `q = |K*|`).

The route follows Coq's `sKsP`: `K* ⊆ M''` is Corollary 15.6 (`typeP_kstar_in_mf`), and
`M'' ⊆ O_p(M_F)` because `M' = M_σ = M_F` for type `P₁` (`typeP1_msigma_eq_derivedInG` plus `hmf`)
and `M_F` is nilpotent with commutative `O_{p'}(M_F)`
(`commutator_le_oPiCore_of_isMulCommutative_compl_of_isNilpotent`).  So `K*` is a `p`-group, and
being of prime order (`kstar_card_prime_of_inputs`) it has order exactly `p`.

⚠ The similarly-named `kstar_le_opiCore_of_inputs` does **not** apply here: it assumes
`M_F ≠ M_σ`, which is the opposite of the `hmf` hypothesis of Theorem 15.7(e). -/
theorem kstar_card_eq_witness_prime_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hmf : MF M = OddOrder.BG.Ch3.S10.Msigma M) {p : ℕ} (hp : p.Prime)
    (hcyc : IsCyclic ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (MF M))) :
    Nat.card ↥Kstar = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  -- `O_{p'}(M_F)` is commutative, transferred from the ambient copy to the subtype level.
  haveI := hcyc
  haveI hcyc' : IsCyclic ↥(Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥(MF M)) := by
    have he : ↥(Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥(MF M)) ≃*
        ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (MF M)) :=
      Subgroup.equivMapOfInjective _ (MF M).subtype (MF M).subtype_injective
    exact isCyclic_of_surjective he.symm.toMonoidHom he.symm.surjective
  have hab : IsMulCommutative ↥(Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥(MF M)) := inferInstance
  -- `M'' = (M_F)' ≤ O_p(M_F)`.
  have hM'eq : derivedInG M = MF M := by
    rw [hmf]; exact (typeP1_msigma_eq_derivedInG hG hM hP1 hKM hK hKstar).symm
  have hderiv : derivedInG (derivedInG M) ≤ opiCoreInG ({p} : Set ℕ) (MF M) := by
    rw [hM'eq]
    exact Subgroup.map_mono
      (OddOrder.BG.Ch3.S10.commutator_le_oPiCore_of_isMulCommutative_compl_of_isNilpotent _ hab)
  -- `K* ≤ M'' ≤ O_p(M_F)`, so `K*` is a `p`-group.
  have hKsP : Kstar ≤ opiCoreInG ({p} : Set ℕ) (MF M) :=
    ((typeP_kstar_in_mf hG hM hP1.1 hKM hK hKstar).2.2.2.1).trans hderiv
  have hKspg : IsPGroup p ↥Kstar :=
    (isPGroup_opiCoreInG_singleton (MF M)).to_le hKsP
  -- Prime order plus `p`-group forces `|K*| = p`.
  have hprime : (Nat.card ↥Kstar).Prime := kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥Kstar)).mp hKspg
  rw [hn] at hprime ⊢
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hprime
    exact Nat.not_prime_one hprime
  exact ((Nat.prime_dvd_prime_iff_eq hp hprime).mp (dvd_pow_self p hn0)).symm

end OddOrder.BG.Ch4.S15
