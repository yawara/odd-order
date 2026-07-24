import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF.SetupLemma151
import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF.TypeP1Forcing

/-!
# BG Theorem 15.2 — §14-gated conditional helpers

Split from the former monolithic `OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF` (directory split, issue
0103).
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

/-- **BG Theorem 15.2, `M_σ = M'` for a type-`P₁` member** (mmd L4188 "`M_σ = M'`"): for a type-`P₁`
maximal subgroup `M` with Hall `κ(M)`-subgroup `K`, the `σ`-core equals the derived subgroup.

`M_σ ≤ M'` always (`Msigma_le_derived`).  For the reverse, compare orders: the derived subgroup
complements `K` in `M` (Theorem 14.7(h) duality, `typeP_duality`), so `|M'|·|K| = |M|`, while
`typeP1_card_eq` gives `|M| = |M_σ|·|K|`; cancelling `|K|` yields `|M'| = |M_σ|`, so `M_σ = M'`.
This is `§14`-gated only through `typeP_duality`/`typeP1_card_eq` (both sorry-free).  Supplies
conjunct `M_σ = M'` of Theorem 15.2, and the `M_σ ⋊ K` complement of its proof. -/
theorem typeP1_msigma_eq_derivedInG [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    OddOrder.BG.Ch3.S10.Msigma M = derivedInG M := by
  classical
  obtain ⟨hcomplD, _, _⟩ := S14.typeP_duality hG hM hP1.1 hKM hK hKstar
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hcardM' : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv
  have hcardK' : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have hmul := hcomplD.card_mul
  rw [hcardM', hcardK'] at hmul
  have hcardM := S14.typeP1_card_eq hG hM hP1 hKM hK
  have heq : Nat.card ↥(derivedInG M) = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hmul, hcardM])
  exact Subgroup.eq_of_le_of_card_ge (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM) heq.le

/-- **BG Theorem 15.2, the prime-manner action in `G`** (Proposition 14.2(a), mmd L4192 "`K` acts
in a prime manner on `M_σ`"): for a type-`P` maximal `M` with Hall `κ(M)`-subgroup `K`, every
nontrivial `x ∈ K` has `C_G(x) ⊓ M_σ = K* = C_{M_σ}(K)`.

Unpacks `ActsPrimeOn (M_σ) K` (`typeP_structure` conjunct (a)) — `C_{M_σ}(x) = C_{M_σ}(K)` for
`x ∈ K#` — and rewrites via `hKstar`.  The Hall `(κ ∪ σ)'`-subgroup `U` needed by `typeP_structure`
is built by Hall's theorem in the solvable `M` (`Ch03.hall_E_exists`).  Supplies the `hprime`
hypothesis of `centralizer_le_Msigma_of_primeManner`, `isFrobeniusGroup_DK_of_primeManner`, etc. -/
theorem actsPrimeManner_of_typeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    ∀ x ∈ K, x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  have hprimeOn := (S14.typeP_structure hG hM hP hKM hK hKstar hU).1
  intro x hxK hx1
  have hpm := hprimeOn x hxK hx1
  rw [OddOrder.BG.Ch3.S13.fixedByElement_def, OddOrder.BG.Ch3.S13.fixedBy_def] at hpm
  rw [inf_comm, hpm, hKstar]

/-- **The prime-manner action in the `↥M`-internal form** (Theorem 15.2 step 2 plumbing): the
`↥M`-rephrasing of `actsPrimeManner_of_typeP`, supplying the `hcond2` hypothesis of
`kstar_le_opiCore_of_inputs`.  For `x ∈ (κ(M))^#` (as an `↥M`-element), the centralizer
`C_{↥M}({x}) ⊓ (M_σ ↾ M)` equals `C_{↥M}(K ↾ M) ⊓ (M_σ ↾ M)` — both restrict to `K* ↾ M` via
`centralizer_subgroupOf` (`C_{↥M}(T) = C_G(M.subtype '' T) ↾ M`) and the global prime-manner
identity `C_G(x) ⊓ M_σ = K* = M_σ ⊓ C_G(K)`. -/
theorem actsPrimeManner_subgroupOf_of_typeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    ∀ x ∈ (K.subgroupOf M : Set ↥M), x ≠ 1 →
      Subgroup.centralizer ({x} : Set ↥M) ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M
        = Subgroup.centralizer (K.subgroupOf M : Set ↥M)
            ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M := by
  classical
  have hprime := actsPrimeManner_of_typeP hG hM hP hKM hK hKstar
  intro x hxK hx1
  have hxKM : x ∈ K.subgroupOf M := hxK
  have hxG : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hxKM
  have hxG1 : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have himg_x : M.subtype '' ({x} : Set ↥M) = ({(x : G)} : Set G) := by
    rw [Set.image_singleton]; rfl
  have himg_K : M.subtype '' (K.subgroupOf M : Set ↥M) = (K : Set G) := by
    rw [← Subgroup.coe_map, Subgroup.map_subgroupOf_eq_of_le hKM]
  have sgInf : ∀ A B : Subgroup G, A.subgroupOf M ⊓ B.subgroupOf M = (A ⊓ B).subgroupOf M :=
    fun A B => (Subgroup.comap_inf A B M.subtype).symm
  -- both sides equal `Kstar.subgroupOf M`.
  have hL : Subgroup.centralizer ({x} : Set ↥M) ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M
      = Kstar.subgroupOf M := by
    rw [OddOrder.BG.Ch1.S03h.centralizer_subgroupOf ({x} : Set ↥M), himg_x, sgInf,
      hprime (x : G) hxG hxG1]
  have hR : Subgroup.centralizer (K.subgroupOf M : Set ↥M)
        ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M = Kstar.subgroupOf M := by
    rw [OddOrder.BG.Ch1.S03h.centralizer_subgroupOf (K.subgroupOf M : Set ↥M), himg_K, sgInf,
      inf_comm, ← hKstar]
  rw [hL, hR]

/-- **The normal `q`-Sylow of `↥M` underlying `Q = O_q(M)`** (Theorem 15.2 step 5 plumbing): when
`Q = O_q(M)` is the normal Sylow `q`-subgroup of `M` (a `q`-group with `q ∤ [M : Q]`), there is a
`Sylow q ↥M` whose image under `M.subtype` is `Q`.  `Q ↾ M` is a `q`-group (`comap_subtype`) of
`q'`-index, hence a Sylow (`IsPGroup.toSylow`); being normal (`Q ⊴ M`), its ambient image is the
singleton core `O_q(M) = Q` (`sylowMap_eq_opiCoreInG_singleton_of_normal`).  Supplies the Sylow
witness `(P, hQP)` of `D_centralizes_Q_of_not_mem_beta`. -/
theorem exists_sylow_eq_opiCore [Finite G] {M Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hQ : Q = opiCoreInG ({q} : Set ℕ) M) (hQM : Q ≤ M)
    (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hQpg : IsPGroup q ↥Q) (hidx : ¬ q ∣ (Q.subgroupOf M).index) :
    ∃ P : Sylow q ↥M, Q = (P : Subgroup ↥M).map M.subtype := by
  have hQsubpg : IsPGroup q ↥(Q.subgroupOf M) := hQpg.comap_subtype
  refine ⟨hQsubpg.toSylow hidx, ?_⟩
  haveI hPnorm : (hQsubpg.toSylow hidx : Subgroup ↥M).Normal := by
    rw [hQsubpg.toSylow_coe hidx]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMnormQ
  rw [OddOrder.BG.Ch3.S10.sylowMap_eq_opiCoreInG_singleton_of_normal _ hPnorm, ← hQ]

/-- **§14-independent Frattini factorization** (BG Corollary 15.3 proof, mmd L4213 "by the
Frattini argument").  If `Q ⊴ M`, `QH ⊴ M`, `Q ∩ H = 1`, `|Q|` and `|H|` are coprime, and `M`
is solvable, then `M = N_M(H)·Q`: every `m ∈ M` factors as `m = n·a` with `n ∈ N_G(H)` and
`a ∈ Q`.

Proof: inside `L = QH`, both `H` and the conjugate `H^{m⁻¹} = m⁻¹Hm` are complements of the
normal subgroup `Q` (coprime orders, so `Q` is a normal Hall subgroup of `L`), hence are
conjugate by some `q ∈ Q` (Schur–Zassenhaus conjugacy, `IsComplement'.exists_conj_of_coprime`):
`H^q = H^{m⁻¹}`.  Then `mq ∈ N_G(H)` and `m = (mq)·q⁻¹`.

This discharges the `hfratt` hypothesis of `mf_hall_centralizer_control_of_inputs` (Cor 15.3)
once Theorem 15.2 supplies the normal `q`-subgroup `Q` with `M_σ/Q` nilpotent (issue 8010). -/
theorem frattini_factorization [Finite G] {M Q H : Subgroup G}
    (hQM : Q ≤ M) (hHM : H ≤ M)
    (hQnorm : (Q.subgroupOf M).Normal)
    (hQHnorm : ((Q ⊔ H).subgroupOf M).Normal)
    (hdisj : Disjoint Q H)
    (hcop : Nat.Coprime (Nat.card ↥Q) (Nat.card ↥H))
    (hsolv : IsSolvable ↥M) :
    ∀ m ∈ M, ∃ n a : G, n ∈ Subgroup.normalizer (H : Set G) ∧ a ∈ Q ∧ m = n * a := by
  classical
  have hQL : Q ≤ Q ⊔ H := le_sup_left
  have hHL : H ≤ Q ⊔ H := le_sup_right
  have hLM : Q ⊔ H ≤ M := sup_le hQM hHM
  have hMNQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mp hQnorm
  have hMNL : M ≤ Subgroup.normalizer ((Q ⊔ H : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hQHnorm
  -- `Q ⊴ L` (as a subgroup of `↥(Q ⊔ H)`).
  haveI hQnL : (Q.subgroupOf (Q ⊔ H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQL).mpr (le_trans hLM hMNQ)
  -- `↥(Q ⊔ H)` is solvable, hence so is its quotient by `Q.subgroupOf (Q ⊔ H)`.
  haveI hLsolv : IsSolvable ↥(Q ⊔ H) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hLM)
  -- A complement-builder inside `↥(Q ⊔ H)`: a `K ≤ L` with `Q ⊓ K = ⊥` and `Q ⊔ K = Q ⊔ H`
  -- complements `Q` in `L`.
  have mk_compl : ∀ K : Subgroup G, K ≤ Q ⊔ H → (Q ⊓ K : Subgroup G) = ⊥ → Q ⊔ K = Q ⊔ H →
      Subgroup.IsComplement' (Q.subgroupOf (Q ⊔ H)) (K.subgroupOf (Q ⊔ H)) := by
    intro K hKL hQK hQKL
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [Subgroup.disjoint_def]
      intro x hxQ hxK
      rw [Subgroup.mem_subgroupOf] at hxQ hxK
      have hxQK : (x : G) ∈ Q ⊓ K := ⟨hxQ, hxK⟩
      rw [hQK, Subgroup.mem_bot] at hxQK
      exact Subtype.ext hxQK
    · have hsup : Q.subgroupOf (Q ⊔ H) ⊔ K.subgroupOf (Q ⊔ H) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQL hKL, hQKL, Subgroup.subgroupOf_self]
      have := Subgroup.normal_mul (Q.subgroupOf (Q ⊔ H)) (K.subgroupOf (Q ⊔ H))
      rw [hsup, Subgroup.coe_top] at this
      exact this.symm
  intro m hmM
  have hminvM : m⁻¹ ∈ M := M.inv_mem hmM
  -- `conj m⁻¹` fixes `Q` and `L` (both normal in `M`, and `m⁻¹ ∈ M`).
  have hmiQ : MulAut.conj m⁻¹ • Q = Q := conj_smul_eq_self_of_mem_normalizer (hMNQ hminvM)
  have hmiL : MulAut.conj m⁻¹ • (Q ⊔ H) = Q ⊔ H :=
    conj_smul_eq_self_of_mem_normalizer (hMNL hminvM)
  -- `H' := m⁻¹Hm = conj m⁻¹ • H` is a complement of `Q` in `L`.
  have hH'L : MulAut.conj m⁻¹ • H ≤ Q ⊔ H := by
    rw [← hmiL]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hHL
  have hQH'disj : (Q ⊓ MulAut.conj m⁻¹ • H : Subgroup G) = ⊥ := by
    rw [← hmiQ, ← Subgroup.smul_inf, disjoint_iff.mp hdisj, Subgroup.smul_bot]
  have hQH'sup : Q ⊔ MulAut.conj m⁻¹ • H = Q ⊔ H := by
    rw [← hmiQ, ← Subgroup.smul_sup, hmiQ, hmiL]
  -- The two complements `H` and `H'`.
  have hcompl_H : Subgroup.IsComplement' (Q.subgroupOf (Q ⊔ H)) (H.subgroupOf (Q ⊔ H)) :=
    mk_compl H hHL (disjoint_iff.mp hdisj) rfl
  have hcompl_H' : Subgroup.IsComplement' (Q.subgroupOf (Q ⊔ H))
      ((MulAut.conj m⁻¹ • H).subgroupOf (Q ⊔ H)) :=
    mk_compl (MulAut.conj m⁻¹ • H) hH'L hQH'disj hQH'sup
  -- Coprimality `(|Q.subgroupOf L|, (Q.subgroupOf L).index)`: index `= |H|` by `hcompl_H`.
  have hcardQ : Nat.card ↥(Q.subgroupOf (Q ⊔ H)) = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
  have hcardH : Nat.card ↥(H.subgroupOf (Q ⊔ H)) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
  have hcop' : Nat.Coprime (Nat.card ↥(Q.subgroupOf (Q ⊔ H)))
      (Q.subgroupOf (Q ⊔ H)).index := by
    rw [hcardQ, hcompl_H.symm.index_eq_card, hcardH]; exact hcop
  -- Schur–Zassenhaus conjugacy: `H` and `H'` are conjugate by some `q' ∈ Q.subgroupOf L`.
  obtain ⟨q', hq'mem, hq'eq⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop' (Or.inr inferInstance) hcompl_H hcompl_H'
  -- Lift the conjugacy back to `G` along `L.subtype`: `conj q'.val • H = conj m⁻¹ • H`.
  set q : G := (q' : G) with hqdef
  have hqQ : q ∈ Q := Subgroup.mem_subgroupOf.mp hq'mem
  have hintertwine : (Q ⊔ H).subtype.comp (MulAut.conj q').toMonoidHom =
      ((MulAut.conj q).toMonoidHom).comp (Q ⊔ H).subtype := by
    ext x; rfl
  have hmapH : (H.subgroupOf (Q ⊔ H)).map (Q ⊔ H).subtype = H := by
    rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_of_le_right hHL]
  have hmapH' : ((MulAut.conj m⁻¹ • H).subgroupOf (Q ⊔ H)).map (Q ⊔ H).subtype =
      MulAut.conj m⁻¹ • H := by
    rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_of_le_right hH'L]
  have hlift : MulAut.conj q • H = MulAut.conj m⁻¹ • H := by
    have hlifted := congrArg (·.map (Q ⊔ H).subtype) hq'eq
    rw [Subgroup.map_map, hintertwine, ← Subgroup.map_map, hmapH, hmapH'] at hlifted
    rw [Subgroup.pointwise_smul_def]
    exact hlifted
  -- `n := m·q ∈ N_G(H)`, `a := q⁻¹ ∈ Q`, `m = n·a`.
  refine ⟨m * q, q⁻¹, ?_, Q.inv_mem hqQ, by group⟩
  apply mem_normalizer_of_conj_smul_eq_self
  rw [map_mul, mul_smul, hlift, ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]

/-- **A Hall subgroup of a nilpotent `M_σ` is normal in `M`** (BG Corollary 15.3(b) entry, mmd
L4213 "Then `M_σ` is not nilpotent").  If `M_σ = O_σ(M)` is nilpotent and `H` is a Hall subgroup of
`M_σ`, then `H = O_{π(H)}(M_σ)` (the `π`-core of the nilpotent `M_σ`, hence characteristic), so the
`M`-normalizer of `M_σ` normalizes `H`; thus `H ⊴ M`.

Contrapositive: if `H ⋬ M` (the case `hfratt` handles), then `M_σ` is **not** nilpotent, i.e.
`M_F ≠ M_σ`, which lets Theorem 15.2 supply the normal `q`-subgroup `Q`. -/
theorem hall_subgroupOf_normal_of_msigma_nilpotent [Finite G]
    {M H : Subgroup G} (hHMσ : H ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hHhall : Ch03.IsHallSubgroup (S14.piSet H) (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)))
    (hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M)) :
    (H.subgroupOf M).Normal := by
  classical
  set Mσ : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  set π : Set ℕ := S14.piSet H with hπdef
  have hHM : H ≤ M := hHMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
  -- `H ≤ O_π(M_σ)` (a `π`-subgroup of the nilpotent `M_σ`).
  have hH_le_Oπ : H ≤ OddOrder.GroupTheory.opiCoreInG π Mσ :=
    OddOrder.BG.Ch3.S12.piGroup_le_opiCoreInG_of_nilpotent (fun r hr => hr) hHMσ
  -- `O_π(M_σ)` is a `π`-group, and `H` is Hall `π` in `M_σ`, so `|O_π| ∣ |H|`; with `H ≤ O_π`,
  -- `H = O_π(M_σ)`.
  have hOπMσ : OddOrder.GroupTheory.opiCoreInG π Mσ ≤ Mσ := OddOrder.GroupTheory.opiCoreInG_le _ _
  have hOπ_pi_Mσ : Ch03.Subgroup.IsPiGroup π
      ((OddOrder.GroupTheory.opiCoreInG π Mσ).subgroupOf Mσ) := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOπMσ).toEquiv] at hr
    exact OddOrder.GroupTheory.isPiSubgroup_opiCoreInG π Mσ r hr
  have hcard_dvd : Nat.card ↥((OddOrder.GroupTheory.opiCoreInG π Mσ).subgroupOf Mσ)
      ∣ Nat.card ↥(H.subgroupOf Mσ) := hHhall.card_dvd_of_isPiGroup hOπ_pi_Mσ
  have hcard_dvd' : Nat.card ↥(OddOrder.GroupTheory.opiCoreInG π Mσ) ∣ Nat.card ↥H := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOπMσ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHMσ).toEquiv] at hcard_dvd
  have hHeq : H = OddOrder.GroupTheory.opiCoreInG π Mσ :=
    Subgroup.eq_of_le_of_card_ge hH_le_Oπ (Nat.le_of_dvd Nat.card_pos hcard_dvd')
  -- `M ≤ N_G(M_σ) ⟹ M ≤ N_G(O_π(M_σ)) = N_G(H)`, hence `H.subgroupOf M ⊴ M`.
  have hM_norm_Mσ : M ≤ Subgroup.normalizer (Mσ : Set G) := by
    rw [hMσdef, OddOrder.BG.Ch3.S10.Msigma]
    exact OddOrder.GroupTheory.le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  have hM_norm_H : M ≤ Subgroup.normalizer (H : Set G) := by
    rw [hHeq]
    exact OddOrder.GroupTheory.le_normalizer_opiCoreInG_of_le_normalizer π hM_norm_Mσ
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mpr hM_norm_H

/-- **A Hall `π`-subgroup of a finite nilpotent group is its `π`-core** (hence characteristic).
General-`Γ` form of the core step inside `hall_subgroupOf_normal_of_msigma_nilpotent`: in a
nilpotent group every `π`-subgroup lies in `O_π(Γ)` (`isPiGroup_le_of_normal_isHallSubgroup`,
`O_π` being a normal Hall `π`-subgroup), and a Hall `π`-subgroup exhausts `O_π` by orders. -/
theorem isHallSubgroup_eq_oPiCore_of_nilpotent {Γ : Type*} [Group Γ] [Finite Γ]
    [Group.IsNilpotent Γ] {π : Set ℕ} {H : Subgroup Γ} (hHall : Ch03.IsHallSubgroup π H) :
    H = Ch03.oPiCore π Γ := by
  have hOHall : Ch03.IsHallSubgroup π (Ch03.oPiCore π Γ) :=
    OddOrder.BG.Ch3.S10.oPiCore_isHall_of_isNilpotent π
  have hOpi : Ch03.Subgroup.IsPiGroup π (Ch03.oPiCore π Γ) := Ch03.oPiCore.isPiGroup π
  have hHpi : Ch03.Subgroup.IsPiGroup π H := fun p hp => hHall.1 p hp
  haveI : (Ch03.oPiCore π Γ).Normal := inferInstance
  have hHle : H ≤ Ch03.oPiCore π Γ :=
    OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hOHall hHpi
  have hdvd : Nat.card ↥(Ch03.oPiCore π Γ) ∣ Nat.card ↥H := hHall.card_dvd_of_isPiGroup hOpi
  exact Subgroup.eq_of_le_of_card_ge hHle (Nat.le_of_dvd Nat.card_pos hdvd)

/-- **The image of a Hall `π`-subgroup under a quotient map is Hall `π` in the quotient.**
`|H̄| ∣ |H|` keeps the `π`-group property; and `[Γ/N : H̄] = [Γ : HN]` divides `[Γ : H]`
(as `H ≤ HN`), a `π'`-number. -/
theorem isHallSubgroup_map_mk' {Γ : Type*} [Group Γ] [Finite Γ] {N : Subgroup Γ} [N.Normal]
    {π : Set ℕ} {H : Subgroup Γ} (hHall : Ch03.IsHallSubgroup π H) :
    Ch03.IsHallSubgroup π (H.map (QuotientGroup.mk' N)) := by
  refine ⟨?_, ?_⟩
  · -- `π`-group: `|H̄| ∣ |H|`.
    intro p hp
    have hdvd : Nat.card ↥(H.map (QuotientGroup.mk' N)) ∣ Nat.card ↥H :=
      Subgroup.card_map_dvd _ _
    rw [Nat.mem_primeFactors] at hp
    exact hHall.1 p (Nat.mem_primeFactors.mpr ⟨hp.1, hp.2.1.trans hdvd, Nat.card_pos.ne'⟩)
  · -- `π'`-index: `[Γ/N : H̄] = [Γ : NH] ∣ [Γ : H]`.
    intro p hp
    have hidx : (H.map (QuotientGroup.mk' N)).index = (N ⊔ H).index := by
      rw [← QuotientGroup.comap_map_mk' N H,
        Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)]
    have hdvd : (N ⊔ H).index ∣ H.index := Subgroup.index_dvd_of_le le_sup_right
    rw [hidx, Nat.mem_primeFactors] at hp
    exact hHall.2 p (Nat.mem_primeFactors.mpr
      ⟨hp.1, hp.2.1.trans hdvd, Subgroup.index_ne_zero_of_finite⟩)

/-- **`N ⊔ H` is characteristic when `Γ/N` is nilpotent** (`N` characteristic, `H` a Hall
`π`-subgroup).  The image `H̄ = H.map (mk' N)` is the Hall `π`-subgroup of the nilpotent `Γ/N`,
hence equals `O_π(Γ/N)` (characteristic, `isHallSubgroup_eq_oPiCore_of_nilpotent`), and
`N ⊔ H = (mk' N)⁻¹(H̄)` is characteristic as the preimage of a characteristic subgroup under the
quotient by the characteristic `N` (`Subgroup.Characteristic.comap_quotient_mk`).

This is the BG Corollary 15.3 step "`QH ◁ M` because `M_σ/Q` is nilpotent" (mmd L4213), applied
with `Γ = ↥M_σ`, `N = Q.subgroupOf M_σ` (`= O_q(M_σ)`, characteristic), `H = H.subgroupOf M_σ`. -/
theorem characteristic_sup_hall_of_quotient_nilpotent {Γ : Type*} [Group Γ] [Finite Γ]
    {N : Subgroup Γ} [N.Characteristic] (hNil : Group.IsNilpotent (Γ ⧸ N)) {π : Set ℕ}
    {H : Subgroup Γ} (hHall : Ch03.IsHallSubgroup π H) : (N ⊔ H).Characteristic := by
  haveI := hNil
  have hHbar : Ch03.IsHallSubgroup π (H.map (QuotientGroup.mk' N)) := isHallSubgroup_map_mk' hHall
  have hHbar_eq : H.map (QuotientGroup.mk' N) = Ch03.oPiCore π (Γ ⧸ N) :=
    isHallSubgroup_eq_oPiCore_of_nilpotent hHbar
  haveI hHbar_char : (H.map (QuotientGroup.mk' N)).Characteristic := by
    rw [hHbar_eq]; exact Ch03.oPiCore.characteristic π (Γ ⧸ N)
  rw [← QuotientGroup.comap_map_mk' N H]
  exact Subgroup.Characteristic.comap_quotient_mk hHbar_char

/-- **`O_π(M) = O_π(N)`** when `N ◁ M` (in the ambient sense `M ≤ N_G(N)`) and `O_π(M) ≤ N`
(BG Corollary 15.3 plumbing).  `O_π(M)` is a normal `π`-subgroup of `N`, so `≤ O_π(N)`;
conversely `O_π(N)` is characteristic in `N`, hence (as `N ◁ M`) a normal `π`-subgroup of `M`,
so `≤ O_π(M)`.  Used to identify `Q = O_q(M)` (which lies in `M_σ`) with `O_q(M_σ)`, which makes
`Q.subgroupOf M_σ` characteristic in `↥M_σ`. -/
theorem opiCoreInG_eq_of_normal_le [Finite G] {π : Set ℕ} {M N : Subgroup G}
    (hNM : N ≤ M) (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hQN : opiCoreInG π M ≤ N) :
    opiCoreInG π M = opiCoreInG π N := by
  refine le_antisymm ?_ ?_
  · exact le_opiCoreInG_of_normal_of_isPiSubgroup hQN
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mpr
        (hNM.trans (le_normalizer_opiCoreInG π M))) (isPiSubgroup_opiCoreInG π M)
  · have hON_le_M : opiCoreInG π N ≤ M := (opiCoreInG_le π N).trans hNM
    exact le_opiCoreInG_of_normal_of_isPiSubgroup hON_le_M
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hON_le_M).mpr
        (le_normalizer_opiCoreInG_of_le_normalizer π hMN)) (isPiSubgroup_opiCoreInG π N)

/-- **A characteristic subgroup of an `M`-normal subgroup is `M`-normal** (relative version of the
private `normal_of_characteristic_subgroupOf`, for `N ◁ M` rather than `N ◁ G`).  If `N ≤ M` with
`M ≤ N_G(N)`, `A ≤ N`, and `A.subgroupOf N` is characteristic in `↥N`, then `A.subgroupOf M` is
normal in `↥M`.  Each `x ∈ M` restricts to an automorphism `ψ` of `↥N`; it fixes the characteristic
`A.subgroupOf N`, so conjugation by `x` fixes `A = (A.subgroupOf N).map N.subtype`.  This lifts the
`QH` characteristic-in-`M_σ` step (`characteristic_sup_hall_of_quotient_nilpotent`) to `QH ◁ M`. -/
theorem normal_subgroupOf_of_characteristic_subgroupOf_le {M N A : Subgroup G}
    (hNM : N ≤ M) (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hAN : A ≤ N)
    (hchar : (A.subgroupOf N).Characteristic) : (A.subgroupOf M).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (hAN.trans hNM)).mpr ?_
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxN : x ∈ Subgroup.normalizer (N : Set G) := hMN hx
  let ψ : MulAut ↥N := N.normalizerMonoidHom ⟨x, hxN⟩
  have hAeq : (A.subgroupOf N).map N.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAN
  have hfix := Subgroup.characteristic_iff_comap_eq.mp hchar ψ
  rw [← hAeq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨ψ z, ?_, ?_⟩
    · have hzc : z ∈ (A.subgroupOf N).comap ψ.toMonoidHom := by rw [hfix]; exact hz
      exact Subgroup.mem_comap.mp hzc
    · change (ψ z : G) = x * (z : G) * x⁻¹
      rfl
  · intro hy
    obtain ⟨z, hz, hz_eq⟩ := hy
    have hyN : y ∈ N := (Subgroup.mem_normalizer_iff.mp hxN y).mpr (hz_eq ▸ z.2)
    have hzy : z = ψ.toMonoidHom ⟨y, hyN⟩ := by
      apply Subtype.ext; change (z : G) = x * y * x⁻¹; exact hz_eq
    have hyc : (⟨y, hyN⟩ : ↥N) ∈ (A.subgroupOf N).comap ψ.toMonoidHom := by
      rw [Subgroup.mem_comap, ← hzy]; exact hz
    rw [hfix] at hyc
    exact ⟨⟨y, hyN⟩, hyc, rfl⟩

/-- **A normal `π`-subgroup is contained in every Hall `π`-subgroup** (finite group).  `L ⊔ K`
is a `π`-group (`L` normal, so `↑L · ↑K = ↑(L ⊔ K)`), and `K` is a maximal `π`-subgroup (Hall),
so `L ⊔ K = K`.  Dual of `isPiGroup_le_of_normal_isHallSubgroup` (which assumes the *Hall*
subgroup normal); here the normal `π`-subgroup `L` need not be Hall and `K` need not be normal.
Used in BG Corollary 15.3(b) to place `Q = O_q(M_σ) ≤ H` when `q ∈ π(H)`. -/
theorem normal_isPiGroup_le_isHall {Γ : Type*} [Group Γ] [Finite Γ] {π : Set ℕ}
    {L K : Subgroup Γ} [L.Normal] (hL : Ch03.Subgroup.IsPiGroup π L)
    (hK : Ch03.IsHallSubgroup π K) : L ≤ K := by
  have hSup_pi : Ch03.Subgroup.IsPiGroup π (L ⊔ K : Subgroup Γ) := by
    intro r hr
    rw [Nat.mem_primeFactors] at hr
    obtain ⟨hr_prime, hr_dvd, _⟩ := hr
    have h_card_eq : Nat.card ↥(L ⊔ K : Subgroup Γ) * Nat.card ↥(L ⊓ K : Subgroup Γ)
        = Nat.card ↥L * Nat.card ↥K := by
      have h_hk := Subgroup.card_HK_mul_card_inf_eq_card_mul_card L K
      rwa [show (↑L * ↑K : Set Γ) = ↑(L ⊔ K : Subgroup Γ) from
        (Subgroup.normal_mul L K).symm] at h_hk
    have h_dvd_prod : r ∣ Nat.card ↥L * Nat.card ↥K := by
      rw [← h_card_eq]; exact hr_dvd.mul_right _
    rcases hr_prime.dvd_mul.mp h_dvd_prod with hL_dvd | hK_dvd
    · exact hL r (Nat.mem_primeFactors.mpr ⟨hr_prime, hL_dvd, Nat.card_pos.ne'⟩)
    · exact hK.1 r (Nat.mem_primeFactors.mpr ⟨hr_prime, hK_dvd, Nat.card_pos.ne'⟩)
  have h_card_dvd : Nat.card ↥(L ⊔ K : Subgroup Γ) ∣ Nat.card ↥K :=
    hK.card_dvd_of_isPiGroup hSup_pi
  have h_card_ge : Nat.card ↥K ≤ Nat.card ↥(L ⊔ K : Subgroup Γ) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective (le_sup_right (a := L)))
  have h_sup_eq : (L ⊔ K : Subgroup Γ) = K :=
    (Subgroup.eq_of_le_of_card_ge le_sup_right
      (Nat.le_antisymm (Nat.le_of_dvd Nat.card_pos h_card_dvd) h_card_ge).le).symm
  intro x hx
  have hx_sup : x ∈ (L ⊔ K : Subgroup Γ) := Subgroup.mem_sup_left hx
  rwa [h_sup_eq] at hx_sup

/-- **§14-independent assembly engine for BG Corollary 15.3** (mmd L4204).  Packages the
*logic* of Corollary 15.3 with its `§14`/`§15` inputs taken as named hypotheses, so that once
those land (Lane H), the wrapper `mf_hall_centralizer_control` discharges each by a single
citation and applies this skeleton (the gated-endpoint pattern, cf.
`typeP_kstar_in_mf_of_inputs`).  Hypothesis provenance (mmd L4209-4213):

* `ha` (the `C_M(H) = C_{M_σ}(H)·X` decomposition) ← Proposition 14.2(b1)(e) (`C_M(H)` is a
  `κ(M)'`-group) + Lemma 15.1(c) (the `X` cyclic-`τ₂` extraction);
* `hconj` (any `G`-conjugacy of `H`-elements is realized inside `M`) ← Theorem 14.4 (find
  `c ∈ C_G(x)` with `M^{gc} = M`) + self-normalizing `N_G(M) = M`
  (`normalizer_eq_self_of_mem_maximalSubgroups`); the witness is `m = gc`;
* `hfratt` (the Frattini factorization `M = N_M(H)·Q` when `H ⋬ M`) ← Theorem 15.2's normal
  `Q = O_q(M)` with `M_σ/Q` nilpotent (so `QH ⊴ M`, `Q ∩ H = 1`) + the Frattini argument.

The nontrivial step is the `H ⋬ M` glue: writing the realizing `m = n·a` (`n ∈ N_M(H)`,
`a ∈ Q`), the element `w = a x a⁻¹` lies in `H` (it is `n⁻¹ y n`) and `w x⁻¹ ∈ Q` (`Q ⊴ M`,
`x ∈ M`), so `w x⁻¹ ∈ Q ∩ H = 1`, whence `w = x` and `y = n x n⁻¹`. -/
theorem mf_hall_centralizer_control_of_inputs [Finite G]
    {M H : Subgroup G} (hHM : H ≤ M)
    (ha : ∃ X : Subgroup G, IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M) ∧
      Subgroup.centralizer (H : Set G) ⊓ M =
        (Subgroup.centralizer (H : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M) ⊔ X)
    (hconj : ∀ x ∈ H, ∀ y ∈ H, ∀ g : G, y = g * x * g⁻¹ → ∃ m ∈ M, y = m * x * m⁻¹)
    (hfratt : ¬ (H.subgroupOf M).Normal → ∃ Q : Subgroup G, Q ≤ M ∧ (Q.subgroupOf M).Normal ∧
      Disjoint Q H ∧
      ∀ m ∈ M, ∃ n a : G, n ∈ Subgroup.normalizer (H : Set G) ∧ a ∈ Q ∧ m = n * a) :
    (∃ X : Subgroup G, IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M) ∧
      Subgroup.centralizer (H : Set G) ⊓ M =
        (Subgroup.centralizer (H : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M) ⊔ X) ∧
    (∀ x ∈ H, ∀ y ∈ H, (∃ g : G, y = g * x * g⁻¹) →
      ∃ n ∈ Subgroup.normalizer (H : Set G), y = n * x * n⁻¹) := by
  refine ⟨ha, ?_⟩
  rintro x hx y hy ⟨g, hg⟩
  obtain ⟨m, hmM, hmy⟩ := hconj x hx y hy g hg
  by_cases hHnorm : (H.subgroupOf M).Normal
  · -- `H ⊴ M`:  `m ∈ M ⊆ N_G(H)`, so `n = m` works directly.
    exact ⟨m, ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hHnorm) hmM, hmy⟩
  · -- `H ⋬ M`:  Frattini-factor `m = n·a` and run the commutator argument.
    obtain ⟨Q, hQM, hQnorm, hQH, hfact⟩ := hfratt hHnorm
    obtain ⟨n, a, hnN, haQ, hmna⟩ := hfact m hmM
    refine ⟨n, hnN, ?_⟩
    -- `y = n · (a x a⁻¹) · n⁻¹`.
    have hyw : y = n * (a * x * a⁻¹) * n⁻¹ := by rw [hmy, hmna]; group
    -- `w := a x a⁻¹ = n⁻¹ y n ∈ H`.
    have hwH : a * x * a⁻¹ ∈ H := by
      have hmem := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (H : Set G)).inv_mem hnN) y).mp hy
      rw [inv_inv] at hmem
      have hweq : a * x * a⁻¹ = n⁻¹ * y * n := by rw [hyw]; group
      rw [hweq]; exact hmem
    -- `w x⁻¹ = a (x a⁻¹ x⁻¹) ∈ Q`  (`Q ⊴ M`, `x ∈ M`).
    have hwxQ : (a * x * a⁻¹) * x⁻¹ ∈ Q := by
      have hxnorm : x ∈ Subgroup.normalizer (Q : Set G) :=
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mp hQnorm) (hHM hx)
      have hxax : x * a⁻¹ * x⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hxnorm a⁻¹).mp (Q.inv_mem haQ)
      have hrw : (a * x * a⁻¹) * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
      rw [hrw]; exact Subgroup.mul_mem _ haQ hxax
    -- `w x⁻¹ ∈ Q ∩ H = ⊥`, so `w = x` and `y = n x n⁻¹`.
    have hwxH : (a * x * a⁻¹) * x⁻¹ ∈ H := Subgroup.mul_mem _ hwH (H.inv_mem hx)
    have hwx1 : (a * x * a⁻¹) * x⁻¹ = 1 := by
      have : (a * x * a⁻¹) * x⁻¹ ∈ Q ⊓ H := Subgroup.mem_inf.mpr ⟨hwxQ, hwxH⟩
      rw [disjoint_iff.mp hQH] at this
      exact Subgroup.mem_bot.mp this
    have hwx : a * x * a⁻¹ = x := by
      have := mul_eq_one_iff_eq_inv.mp hwx1
      rw [this]; group
    rw [hyw, hwx]

/-- **BG Corollary 15.3(a) for `H = M_σ`** (mmd L4204-4209), *sorry-free*.  The centralizer
`C_M(M_σ)` decomposes as `(C_G(M_σ) ⊓ M_σ) ⊔ X` with `X` a cyclic `τ₂(M)`-subgroup.

This is exactly the `ha` input that `fitting_decomposition` (Corollary 15.5) consumes at
`H = M_σ`; using it in place of the (sorried, general) `mf_hall_centralizer_control` makes the
A(8) `FittingIsTI` chain axiom-clean (issue 8016).

Proof (BG L4209).  `C := C_M(M_σ)` is a `κ(M)'`-group
(`centralizer_msigma_isPiSubgroup_kappa_compl`, = Prop 14.2(b1)(e)).  Its normal Hall
`σ`-subgroup `N = M_σ ⊓ C` has a complement `X` by Schur–Zassenhaus: `[C : N] = M_σ.relIndex C`
divides `[M : M_σ]` (`relIndex_subgroupOf` + `relIndex_dvd_index_of_normal`, a `σ'`-number),
coprime to `|N| ∣ |M_σ|`.  Then `C = N ⊔ X` and `X` is a `(κ∪σ)'`-group (`|X| = [C:N]` is
`σ'`, and `X ≤ C` is `κ'`).  As `X ≤ M`, Hall's theorem (`hall_D`) embeds it in a Hall
`(κ∪σ)'`-subgroup `U` of `M`; `X` centralizes `M_σ` (so `C_{M_σ}(X) = M_σ ≠ 1`), and Lemma
15.1(c) (`typeP_hall_small_subgroup_cyclic_tau2`) makes `X` cyclic `τ₂`. -/
theorem mf_centralizer_msigma_decomp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∃ X : Subgroup G, IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M) ∧
      Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) ⊓ M =
        (Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) ⊓
          OddOrder.BG.Ch3.S10.Msigma M) ⊔ X := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  set C : Subgroup G := Subgroup.centralizer (Mσ : Set G) ⊓ M with hCdef
  have hC_le_M : C ≤ M := inf_le_right
  have hC_le_cent : C ≤ Subgroup.centralizer (Mσ : Set G) := inf_le_left
  -- `M ≤ N_G(M_σ)`, so `C ≤ N_G(M_σ)`, hence `N := M_σ.subgroupOf C ⊴ C`.
  have hM_norm_Mσ : M ≤ Subgroup.normalizer (Mσ : Set G) := by
    rw [hMσdef, OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  have hMσinfC_le_C : Mσ ⊓ C ≤ C := inf_le_right
  have hC_norm_MσinfC : C ≤ Subgroup.normalizer ((Mσ ⊓ C : Subgroup G) : Set G) := by
    have h1 : C ≤ Subgroup.normalizer (Mσ : Set G) := hC_le_M.trans hM_norm_Mσ
    exact (le_inf h1 Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  haveI hN_normal : ((Mσ ⊓ C).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMσinfC_le_C).mpr hC_norm_MσinfC
  set N : Subgroup ↥C := (Mσ ⊓ C).subgroupOf C with hNdef
  have hN_eq_Mσ : N = Mσ.subgroupOf C := by rw [hNdef, Subgroup.inf_subgroupOf_right]
  -- `|N| = |M_σ ⊓ C|` (a `σ`-number).
  have hNcard : Nat.card ↥N = Nat.card ↥(Mσ ⊓ C : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσinfC_le_C).toEquiv
  have hN_pi : ∀ p ∈ (Nat.card ↥N).primeFactors, p ∈ OddOrder.BG.Ch3.S10.sigma M := by
    intro p hp
    rw [hNcard] at hp
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le (inf_le_left : Mσ ⊓ C ≤ Mσ))
        Nat.card_pos.ne' hp)
  -- `N.index = M_σ.relIndex C ∣ (M_σ.subgroupOf M).index`, a `σ'`-number.
  haveI hMσM_normal : ((Mσ).subgroupOf M).Normal := by
    rw [hMσdef, OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have hNindex_dvd : N.index ∣ (Mσ.subgroupOf M).index := by
    have hNi : N.index = Mσ.relIndex C := by rw [hN_eq_Mσ]; rfl
    rw [hNi, ← Subgroup.relIndex_subgroupOf hC_le_M]
    exact Subgroup.relIndex_dvd_index_of_normal (Mσ.subgroupOf M) (C.subgroupOf M)
  have hMσM_hall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (Mσ.subgroupOf M) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
  have hNindex_pi' : ∀ p ∈ N.index.primeFactors, p ∉ OddOrder.BG.Ch3.S10.sigma M := by
    intro p hp
    exact hMσM_hall.index_no_pi p (Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp,
        (Nat.dvd_of_mem_primeFactors hp).trans hNindex_dvd, Subgroup.index_ne_zero_of_finite⟩)
  -- Coprimality for Schur–Zassenhaus.
  have hcop : Nat.Coprime (Nat.card ↥N) N.index :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := OddOrder.BG.Ch3.S10.sigma M) Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite
      hN_pi hNindex_pi'
  -- Schur–Zassenhaus: complement `H''` of `N` in `↥C`; `X := H''.map C.subtype`.
  obtain ⟨H'', hH''⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set X : Subgroup G := H''.map C.subtype with hXdef
  have hX_le_C : X ≤ C := hXdef ▸ Subgroup.map_subtype_le H''
  have hX_le_M : X ≤ M := hX_le_C.trans hC_le_M
  -- `C = (M_σ ⊓ C) ⊔ X`.
  have hCeq0 : Mσ ⊓ C ⊔ X = C := by
    have htop : N ⊔ H'' = ⊤ := hH''.sup_eq_top
    have hmap := congrArg (Subgroup.map C.subtype) htop
    rw [Subgroup.map_sup, hNdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMσinfC_le_C,
      ← hXdef] at hmap
    rw [hmap, ← Subgroup.subgroupOf_self C, Subgroup.subgroupOf_map_subtype, inf_idem]
  -- `|X| = N.index` (complement card).
  have hXcard : Nat.card ↥X = N.index := by
    rw [hXdef, ← Nat.card_congr
        (Subgroup.equivMapOfInjective H'' C.subtype C.subtype_injective).toEquiv,
      (hH''.symm).index_eq_card]
  -- `X` is a `(κ ∪ σ)'`-group:  `κ'` (from `X ≤ C`) and `σ'` (from `|X| = N.index`).
  have hX_pi : ∀ p ∈ (Nat.card ↥X).primeFactors, p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
      by
    intro p hp
    rw [Set.mem_compl_iff, Set.mem_union]
    push Not
    refine ⟨?_, ?_⟩
    · -- `p ∉ κ(M)`: `X ≤ C`, and `C` is a `κ'`-group.
      have hpC : p ∈ (Nat.card ↥C).primeFactors :=
        Nat.primeFactors_mono (Subgroup.card_dvd_of_le hX_le_C) Nat.card_pos.ne' hp
      have := centralizer_msigma_isPiSubgroup_kappa_compl hG hM
      exact (Set.mem_compl_iff _ _).mp (this p hpC)
    · -- `p ∉ σ(M)`: `|X| = N.index`, a `σ'`-number.
      rw [hXcard] at hp; exact hNindex_pi' p hp
  -- A Hall `(κ ∪ σ)'`-subgroup `U` of `M` containing `X` (Hall D).
  have hX_pi_M : ∀ p ∈ (Nat.card ↥(X.subgroupOf M)).primeFactors,
      p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ := by
    intro p hp
    exact hX_pi p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_le_M).toEquiv] at hp)
  obtain ⟨U₀, hU₀hall, hXU₀⟩ := Ch03.hall_D (G := ↥M) hX_pi_M
  set U : Subgroup G := U₀.map M.subtype with hUdef
  have hUof : U.subgroupOf M = U₀ :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U₀
  have hUM : U ≤ M := hUdef ▸ Subgroup.map_subtype_le U₀
  have hUhall : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M) := by rw [hUof]; exact hU₀hall
  have hXU : X ≤ U := by
    have h1 : X.subgroupOf M ≤ U.subgroupOf M := by rw [hUof]; exact hXU₀
    calc X = (X.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hX_le_M).symm
      _ ≤ (U.subgroupOf M).map M.subtype := Subgroup.map_mono h1
      _ = U := Subgroup.map_subgroupOf_eq_of_le hUM
  -- `X` centralizes `M_σ`, so `C_{M_σ}(X) = M_σ ≠ 1`.
  have hX_cent : X ≤ Subgroup.centralizer (Mσ : Set G) := hX_le_C.trans hC_le_cent
  have hMσinfCX : Mσ ⊓ Subgroup.centralizer (X : Set G) = Mσ := by
    rw [inf_eq_left]; exact Subgroup.le_centralizer_iff.mp hX_cent
  have hMσne : Mσ ≠ ⊥ := hMσdef ▸ OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
  have hCXne : Mσ ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by rw [hMσinfCX]; exact hMσne
  -- Conclude.
  refine ⟨X, ?_, ?_, ?_⟩
  · -- `X` cyclic.
    by_cases hXbot : X = ⊥
    · rw [hXbot]; infer_instance
    · exact (typeP_hall_small_subgroup_cyclic_tau2 hG hM hUM hUhall hXU hXbot hCXne).2.1
  · -- `π(X) ⊆ τ₂`.
    by_cases hXbot : X = ⊥
    · rw [hXbot]; simp
    · exact (typeP_hall_small_subgroup_cyclic_tau2 hG hM hUM hUhall hXU hXbot hCXne).2.2
  · -- `C_G(M_σ) ⊓ M = (C_G(M_σ) ⊓ M_σ) ⊔ X`.
    have hMσinfC_eq : Mσ ⊓ C = Subgroup.centralizer (Mσ : Set G) ⊓ Mσ := by
      rw [hCdef, inf_comm (Subgroup.centralizer (Mσ : Set G)) M, ← inf_assoc,
        inf_eq_left.mpr (OddOrder.BG.Ch3.S10.Msigma_le M), inf_comm]
    rw [hMσinfC_eq] at hCeq0
    exact hCeq0.symm

/-- **BG Corollary 15.3(a), `ha` input for general Hall `H`** (mmd L4209), reducing to the single
`κ(M)'` fact.  Given that `C_M(H)` is a `κ(M)'`-group (the genuine residual, BG Prop 14.2(b1)/(e)),
the centralizer decomposes as `C_M(H) = C_{M_σ}(H) X` with `X` a cyclic `τ₂(M)`-subgroup.  This
generalizes `mf_centralizer_msigma_decomp` (the `H = M_σ` case): the proof is identical except the
`κ'` step now uses the hypothesis `hkappa` instead of `centralizer_msigma_isPiSubgroup_kappa_compl`,
and `C_{M_σ}(X) ≠ 1` follows from `H ≤ M_σ ⊓ C_G(X)` (as `X ≤ C_G(H)`) with `H ≠ ⊥`. -/
theorem mf_centralizer_hall_decomp_of_kappaCompl [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hHMσ : H ≤ OddOrder.BG.Ch3.S10.Msigma M) (hHne : H ≠ ⊥)
    (hkappa : Subgroup.IsPiSubgroup (kappa M)ᶜ (Subgroup.centralizer (H : Set G) ⊓ M)) :
    ∃ X : Subgroup G, IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M) ∧
      Subgroup.centralizer (H : Set G) ⊓ M =
        (Subgroup.centralizer (H : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M) ⊔ X := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  set C : Subgroup G := Subgroup.centralizer (H : Set G) ⊓ M with hCdef
  have hC_le_M : C ≤ M := inf_le_right
  have hC_le_cent : C ≤ Subgroup.centralizer (H : Set G) := inf_le_left
  have hM_norm_Mσ : M ≤ Subgroup.normalizer (Mσ : Set G) := by
    rw [hMσdef, OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  have hMσinfC_le_C : Mσ ⊓ C ≤ C := inf_le_right
  have hC_norm_MσinfC : C ≤ Subgroup.normalizer ((Mσ ⊓ C : Subgroup G) : Set G) := by
    have h1 : C ≤ Subgroup.normalizer (Mσ : Set G) := hC_le_M.trans hM_norm_Mσ
    exact (le_inf h1 Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  haveI hN_normal : ((Mσ ⊓ C).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMσinfC_le_C).mpr hC_norm_MσinfC
  set N : Subgroup ↥C := (Mσ ⊓ C).subgroupOf C with hNdef
  have hN_eq_Mσ : N = Mσ.subgroupOf C := by rw [hNdef, Subgroup.inf_subgroupOf_right]
  have hNcard : Nat.card ↥N = Nat.card ↥(Mσ ⊓ C : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσinfC_le_C).toEquiv
  have hN_pi : ∀ p ∈ (Nat.card ↥N).primeFactors, p ∈ OddOrder.BG.Ch3.S10.sigma M := by
    intro p hp
    rw [hNcard] at hp
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le (inf_le_left : Mσ ⊓ C ≤ Mσ))
        Nat.card_pos.ne' hp)
  haveI hMσM_normal : ((Mσ).subgroupOf M).Normal := by
    rw [hMσdef, OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have hNindex_dvd : N.index ∣ (Mσ.subgroupOf M).index := by
    have hNi : N.index = Mσ.relIndex C := by rw [hN_eq_Mσ]; rfl
    rw [hNi, ← Subgroup.relIndex_subgroupOf hC_le_M]
    exact Subgroup.relIndex_dvd_index_of_normal (Mσ.subgroupOf M) (C.subgroupOf M)
  have hMσM_hall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (Mσ.subgroupOf M) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
  have hNindex_pi' : ∀ p ∈ N.index.primeFactors, p ∉ OddOrder.BG.Ch3.S10.sigma M := by
    intro p hp
    exact hMσM_hall.index_no_pi p (Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp,
        (Nat.dvd_of_mem_primeFactors hp).trans hNindex_dvd, Subgroup.index_ne_zero_of_finite⟩)
  have hcop : Nat.Coprime (Nat.card ↥N) N.index :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := OddOrder.BG.Ch3.S10.sigma M) Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite
      hN_pi hNindex_pi'
  obtain ⟨H'', hH''⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set X : Subgroup G := H''.map C.subtype with hXdef
  have hX_le_C : X ≤ C := hXdef ▸ Subgroup.map_subtype_le H''
  have hX_le_M : X ≤ M := hX_le_C.trans hC_le_M
  have hCeq0 : Mσ ⊓ C ⊔ X = C := by
    have htop : N ⊔ H'' = ⊤ := hH''.sup_eq_top
    have hmap := congrArg (Subgroup.map C.subtype) htop
    rw [Subgroup.map_sup, hNdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMσinfC_le_C,
      ← hXdef] at hmap
    rw [hmap, ← Subgroup.subgroupOf_self C, Subgroup.subgroupOf_map_subtype, inf_idem]
  have hXcard : Nat.card ↥X = N.index := by
    rw [hXdef, ← Nat.card_congr
        (Subgroup.equivMapOfInjective H'' C.subtype C.subtype_injective).toEquiv,
      (hH''.symm).index_eq_card]
  have hX_pi : ∀ p ∈ (Nat.card ↥X).primeFactors,
      p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ := by
    intro p hp
    rw [Set.mem_compl_iff, Set.mem_union]
    push Not
    refine ⟨?_, ?_⟩
    · have hpC : p ∈ (Nat.card ↥C).primeFactors :=
        Nat.primeFactors_mono (Subgroup.card_dvd_of_le hX_le_C) Nat.card_pos.ne' hp
      exact (Set.mem_compl_iff _ _).mp (hkappa p hpC)
    · rw [hXcard] at hp; exact hNindex_pi' p hp
  have hX_pi_M : ∀ p ∈ (Nat.card ↥(X.subgroupOf M)).primeFactors,
      p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ := by
    intro p hp
    exact hX_pi p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_le_M).toEquiv] at hp)
  obtain ⟨U₀, hU₀hall, hXU₀⟩ := Ch03.hall_D (G := ↥M) hX_pi_M
  set U : Subgroup G := U₀.map M.subtype with hUdef
  have hUof : U.subgroupOf M = U₀ :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U₀
  have hUM : U ≤ M := hUdef ▸ Subgroup.map_subtype_le U₀
  have hUhall : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M) := by rw [hUof]; exact hU₀hall
  have hXU : X ≤ U := by
    have h1 : X.subgroupOf M ≤ U.subgroupOf M := by rw [hUof]; exact hXU₀
    calc X = (X.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hX_le_M).symm
      _ ≤ (U.subgroupOf M).map M.subtype := Subgroup.map_mono h1
      _ = U := Subgroup.map_subgroupOf_eq_of_le hUM
  -- `X` centralizes `H ≤ M_σ`, so `M_σ ⊓ C_G(X) ⊇ H ≠ 1`.
  have hH_le_CX : H ≤ Subgroup.centralizer (X : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    exact hX_le_C.trans hC_le_cent
  have hCXne : Mσ ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
    intro hbot
    exact hHne (le_bot_iff.mp (hbot ▸ le_inf hHMσ hH_le_CX))
  refine ⟨X, ?_, ?_, ?_⟩
  · by_cases hXbot : X = ⊥
    · rw [hXbot]; infer_instance
    · exact (typeP_hall_small_subgroup_cyclic_tau2 hG hM hUM hUhall hXU hXbot hCXne).2.1
  · by_cases hXbot : X = ⊥
    · rw [hXbot]; simp
    · exact (typeP_hall_small_subgroup_cyclic_tau2 hG hM hUM hUhall hXU hXbot hCXne).2.2
  · have hMσinfC_eq : Mσ ⊓ C = Subgroup.centralizer (H : Set G) ⊓ Mσ := by
      rw [hCdef, inf_comm (Subgroup.centralizer (H : Set G)) M, ← inf_assoc,
        inf_eq_left.mpr (OddOrder.BG.Ch3.S10.Msigma_le M), inf_comm]
    rw [hMσinfC_eq] at hCeq0
    exact hCeq0.symm

/-- **BG Corollary 15.3(a) for a general nontrivial Hall subgroup `H` of `M_σ`** (mmd L4209),
*sorry-free* and unconditional.  The `ha` input of `mf_hall_centralizer_control`, with the `κ(M)'`
hypothesis of `mf_centralizer_hall_decomp_of_kappaCompl` now discharged by
`centralizer_hall_isPiSubgroup_kappa_compl` (= BG Prop 14.2(b1)(e), the κ'-fact whose final gate was
Prop 14.2(e) `S ⊄ K*`).  Generalizes `mf_centralizer_msigma_decomp` (`H = M_σ`) to any Hall `H`. -/
theorem mf_centralizer_hall_decomp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hHMσ : H ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hHhall : Ch03.IsHallSubgroup (S14.piSet H) (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)))
    (hHne : H ≠ ⊥) :
    ∃ X : Subgroup G, IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M) ∧
      Subgroup.centralizer (H : Set G) ⊓ M =
        (Subgroup.centralizer (H : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M) ⊔ X :=
  mf_centralizer_hall_decomp_of_kappaCompl hG hM hHMσ hHne
    (centralizer_hall_isPiSubgroup_kappa_compl hG hM hHMσ hHhall hHne)

/-- **General helper (§14-independent, reusable).**  A nonidentity maximal subgroup of a minimal
simple group is self-normalizing: `N_G(M) = M`.  If `M ⊊ N_G(M)`, maximality forces `N_G(M) = G`,
so `M ⊴ G`; simplicity then gives `M = ⊥` or `M = ⊤`, both excluded.  This is the step of BG
Corollary 15.3(b) that turns `M^{gc} = M` into `gc ∈ M`. -/
theorem normalizer_eq_self_of_mem_maximalSubgroups [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMne : M ≠ ⊥) :
    Subgroup.normalizer M = M := by
  refine le_antisymm ?_ Subgroup.le_normalizer
  rcases eq_or_lt_of_le (Subgroup.le_normalizer (H := M)) with heq | hlt
  · exact le_of_eq heq.symm
  · have hnorm : M.Normal := Subgroup.normalizer_eq_top_iff.mp
      ((mem_maximalSubgroups.mp hM).2 _ hlt)
    rcases hG.simple.eq_bot_or_eq_top_of_normal M hnorm with hbot | htop
    · exact absurd hbot hMne
    · exact absurd htop (mem_maximalSubgroups.mp hM).1

/-- **§15 helper (§14-independent, reusable).**  The `G`-normalizer of `M_σ` is `M`:
`N_G(M_σ) = M`.  Since `M_σ = O_{σ(M)}(M)` is normal in `M` (`le_normalizer_opiCoreInG`),
`M ≤ N_G(M_σ)`; if the containment were proper, maximality would force `N_G(M_σ) = G`, so
`M_σ ⊴ G`, and simplicity would give `M_σ ∈ {⊥, ⊤}` — both excluded (`Msigma_ne_bot`,
`M_σ ≤ M ⊊ G`).  This turns the `N_G(M_σ)`-fusion of Corollary 15.3(b) at `H := M_σ` into the
`M`-fusion of BG Theorem D(1). -/
theorem normalizer_Msigma_eq_self [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) = M := by
  have hle : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  refine le_antisymm ?_ hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact le_of_eq heq.symm
  · have hnorm : (OddOrder.BG.Ch3.S10.Msigma M).Normal :=
      Subgroup.normalizer_eq_top_iff.mp ((mem_maximalSubgroups.mp hM).2 _ hlt)
    rcases hG.simple.eq_bot_or_eq_top_of_normal _ hnorm with hbot | htop
    · exact absurd hbot (OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM)
    · exact absurd (top_le_iff.mp (htop ▸ OddOrder.BG.Ch3.S10.Msigma_le M))
        (mem_maximalSubgroups.mp hM).1

/-- **General helper (§14-independent, reusable).**  A subgroup `K` of a finite group that
contains a full Sylow `p`-subgroup for every prime `p` is the whole group.  (No nilpotency:
each Sylow's order is the `p`-part of `|G|`, so `K.index` is divisible by no prime and equals `1`.)
This is the assembly step of BG Corollary 15.4 — once every Sylow subgroup of the nilpotent Hall
subgroup `H` has been placed inside `M_σ`, this forces `H ⊆ M_σ` (applied inside `↥H`). -/
theorem eq_top_of_forall_sylow_le {H : Type*} [Group H] [Finite H] {K : Subgroup H}
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p H), (P : Subgroup H) ≤ K) : K = ⊤ := by
  rw [← Subgroup.index_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  haveI := Fact.mk hp
  obtain ⟨P⟩ : Nonempty (Sylow p H) := inferInstance
  exact P.not_dvd_index (hpdvd.trans (Subgroup.index_dvd_of_le (h p P)))

/-- **§15 helper (§14-independent, reusable).**  A nonidentity Sylow `p`-subgroup `S` of `G`
whose `G`-normalizer lies in a maximal subgroup `M` is contained in `M_σ`.  This is the σ-theory
content of the first step of BG Corollary 15.4 ("`S ⊆ M_σ`"): `N_G(S) ≤ M` exhibits `S` as a
Sylow witness for `p ∈ σ(M)` (`mem_sigma_iff`), and `M_σ`, the `σ(M)`-Hall subgroup of `M`
(`Msigma_isHall`), absorbs the `σ(M)`-subgroup `S` (`sigma_subgroup_le_Msigma_of_isHall`). -/
theorem sylow_le_Msigma_of_normalizer_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (hSne : (S : Subgroup G) ≠ ⊥)
    (hN : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M) :
    (S : Subgroup G) ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  have hSM : (S : Subgroup G) ≤ M := le_trans Subgroup.le_normalizer hN
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := (S : Subgroup G))).mp S.isPGroup'
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact hSne hn
  have hpdvdM : p ∣ Nat.card ↥M := by
    have h1 : Nat.card (S : Subgroup G) ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hSM
    rw [hn] at h1
    exact (dvd_pow_self p hn0).trans h1
  have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M := by
    rw [OddOrder.BG.Ch3.S10.mem_sigma_iff]
    exact ⟨Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvdM, Nat.card_pos.ne'⟩,
      S.subtype hSM, by
        rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSM]; exact hN⟩
  refine OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) hSM (fun q hq => ?_)
  rw [hn, Nat.primeFactors_prime_pow hn0 Fact.out, Finset.mem_singleton] at hq
  exact hq ▸ hpσ

/-- **§15 helper for BG Corollary 15.4.**  A full Sylow `p`-subgroup `S` of `G` contained in
`M_σ` is a `π(S)`-Hall subgroup of `M_σ` (where `π(S) = {p}`).  This packages the hypothesis
shape `mf_hall_centralizer_control` (Corollary 15.3) requires when instantiated at `H := S`:
`S` is a `p`-group so `π(S) = {p}`, and `S` is a Sylow `p` of `M_σ` (a Sylow of `G` inside a
subgroup is a Sylow of that subgroup), so `p ∤ [M_σ : S]`. -/
theorem sylow_isHall_piSet_subgroupOf_Msigma [Finite G] {M : Subgroup G}
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (hSne : (S : Subgroup G) ≠ ⊥)
    (hSMσ : (S : Subgroup G) ≤ OddOrder.BG.Ch3.S10.Msigma M) :
    Ch03.IsHallSubgroup (S14.piSet (S : Subgroup G))
      ((S : Subgroup G).subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) := by
  -- `π(S) = {p}`: `S` is a nontrivial `p`-group.
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := (S : Subgroup G))).mp S.isPGroup'
  have hn0 : n ≠ 0 := by
    rintro rfl; rw [pow_zero, Subgroup.card_eq_one] at hn; exact hSne hn
  have hpiS : S14.piSet (S : Subgroup G) = {p} := by
    ext r
    rw [S14.piSet, Set.mem_setOf_eq, hn, Nat.primeFactors_prime_pow hn0 Fact.out,
      Finset.mem_singleton, Set.mem_singleton_iff]
  -- `card (S.subgroupOf M_σ) = card S`, so its prime factors are `{p} = π(S)`.
  have hcardK : Nat.card ↥((S : Subgroup G).subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) =
      Nat.card ↥(S : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSMσ).toEquiv
  -- `p ∤ [M_σ : S]`: `S` restricts to a Sylow `p`-subgroup of `M_σ`.
  have hpndvd : ¬ p ∣ ((S : Subgroup G).subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).index := by
    have := (S.subtype hSMσ).not_dvd_index
    rwa [Sylow.coe_subtype] at this
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · rw [hpiS]; rw [hcardK, hn, Nat.primeFactors_prime_pow hn0 Fact.out,
      Finset.mem_singleton] at hr; exact hr
  · rw [hpiS, Set.mem_singleton_iff]
    rintro rfl; exact hpndvd (Nat.mem_primeFactors.mp hr).2.1

/-- **KEY LEMMA for BG Corollary 15.4** (mmd L4215, the bracketed step of the proof).  Let
`M` be a maximal subgroup, `S` a nonidentity full Sylow `p`-subgroup of `G` with `S ≤ M_σ`, and
`Q` a Sylow `q`-subgroup of `M` whose image in `G` centralizes `S` (i.e. lies in `C_M(S)`).
Then `Q ≤ M_σ`.

Proof (BG): by Corollary 15.3(a) (`mf_hall_centralizer_control` at `H := S`),
`C_M(S) = (C_{M_σ}(S)) ⊔ X` with `X` cyclic and `π(X) ⊆ τ₂(M)`.  Write `A = C_{M_σ}(S)`, a
`σ(M)`-group; `A ⊴ C := C_M(S)`.  If `q ∈ σ(M)`, then `Q ≤ M_σ` since `M_σ` is the normal Hall
`σ(M)`-subgroup.  If `q ∉ σ(M)`: `Q ⊓ A = 1` (coprime), so `Q` embeds into the cyclic group
`C/A` (a quotient of `X`), forcing `Q` cyclic **and** `q ∣ |X|`, hence `q ∈ τ₂(M)`, i.e.
`r_q(M) = 2`.  But `Q` is a Sylow `q` of `M`, so `r_q(M) = r_q(Q) ≤ 1` (cyclic) — contradiction.
So `q ∈ σ(M)` and `Q ≤ M_σ`. -/
theorem sylow_le_Msigma_of_le_centralizer_sylow [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (hSne : (S : Subgroup G) ≠ ⊥)
    (hSMσ : (S : Subgroup G) ≤ OddOrder.BG.Ch3.S10.Msigma M)
    {q : ℕ} [Fact q.Prime] (Q : Sylow q ↥M) (hQne : (Q : Subgroup ↥M) ≠ ⊥)
    (hQC : (Q : Subgroup ↥M).map M.subtype ≤ Subgroup.centralizer (S : Set G)) :
    (Q : Subgroup ↥M).map M.subtype ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  set Qbar : Subgroup G := (Q : Subgroup ↥M).map M.subtype with hQbar
  have hQbar_le_M : Qbar ≤ M := Subgroup.map_subtype_le _
  -- `Qbar` is a `q`-group, nontrivial.
  have hQbar_pg : IsPGroup q ↥Qbar :=
    Q.isPGroup'.map M.subtype
  have hcardQbar : Nat.card ↥Qbar = Nat.card ↥(Q : Subgroup ↥M) := by
    rw [hQbar, Subgroup.card_map_of_injective M.subtype_injective]
  have hQbar_ne : Qbar ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardQbar
    exact hQne (Subgroup.card_eq_one.mp hcardQbar.symm)
  obtain ⟨m, hm⟩ := hQbar_pg.exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl; rw [pow_zero] at hm; exact hQbar_ne (Subgroup.card_eq_one.mp hm)
  have hq_dvd_Qbar : q ∣ Nat.card ↥Qbar := hm ▸ dvd_pow_self q hm0
  -- Whether `q ∈ σ(M)`.
  by_cases hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M
  · -- `q ∈ σ(M)`: `Qbar` is a `σ(M)`-group inside `M`, hence `≤ M_σ`.
    refine OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) hQbar_le_M (fun r hr => ?_)
    have hrq : r = q := by
      have hrdvd : r ∣ q ^ m := hm ▸ (Nat.mem_primeFactors.mp hr).2.1
      exact (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hr) Fact.out).mp
        ((Nat.prime_of_mem_primeFactors hr).dvd_of_dvd_pow hrdvd)
    exact hrq ▸ hqσ
  · -- `q ∉ σ(M)`: derive a contradiction (so this branch is vacuous, but we conclude `≤ M_σ`).
    exfalso
    -- Corollary 15.3(a): `C_M(S) = C_{M_σ}(S) ⊔ X`, `X` cyclic with `π(X) ⊆ τ₂(M)`.
    -- (Cite `mf_centralizer_hall_decomp` — the `ha` half of Corollary 15.3 — directly, since only
    -- the centralizer decomposition is needed here; this keeps `sylow_le_Msigma` independent of the
    -- full `mf_hall_centralizer_control` whose `hfratt` input lands later in the file.)
    obtain ⟨X, hXcyc, hXτ₂, hCeq⟩ :=
      mf_centralizer_hall_decomp hG hM hSMσ
        (sylow_isHall_piSet_subgroupOf_Msigma S hSne hSMσ) hSne
    set A : Subgroup G := Subgroup.centralizer (S : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M with hA
    set C : Subgroup G := Subgroup.centralizer (S : Set G) ⊓ M with hC
    -- `Qbar ≤ C`.
    have hQbar_C : Qbar ≤ C := le_inf hQC hQbar_le_M
    -- `A ≤ C`.
    have hA_C : A ≤ C := inf_le_inf_left _ (OddOrder.BG.Ch3.S10.Msigma_le M)
    -- `A ⊴ C`: `C` normalizes `A = C_G(S) ⊓ M_σ` (centralizer normalizes itself, `M` normalizes
    -- `M_σ`).
    have hC_norm_A : C ≤ Subgroup.normalizer A := by
      have h1 : C ≤ Subgroup.normalizer (Subgroup.centralizer (S : Set G)) :=
        inf_le_left.trans Subgroup.le_normalizer
      have h2 : C ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
        inf_le_right.trans
          (OddOrder.GroupTheory.le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M)
      exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
    haveI hA_normal : (A.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer_inf).mpr
        (by rw [inf_eq_left.mpr hA_C]; exact hC_norm_A)
    -- `q ∤ |A|`: `A ≤ M_σ` is a `σ(M)`-group and `q ∉ σ(M)`.
    have hq_ndvd_A : ¬ q ∣ Nat.card ↥A := by
      intro hdvd
      exact hqσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
        (Nat.mem_primeFactors.mpr ⟨Fact.out,
          hdvd.trans (Subgroup.card_dvd_of_le (inf_le_right)), Nat.card_pos.ne'⟩))
    -- `Qbar ⊓ A = ⊥`: coprime orders.
    have hQbar_inf_A : Qbar ⊓ A = ⊥ := by
      have hcop : Nat.Coprime (Nat.card ↥Qbar) (Nat.card ↥A) := by
        rw [hm, Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hm0)]
        exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hq_ndvd_A
      exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
    -- `X ≤ C` (from `C = A ⊔ X`).
    have hX_C : X ≤ C := le_sup_right.trans hCeq.ge
    -- Work inside `↥C`, with `a = A∩C`, `x = X∩C`, `Qc = Qbar∩C` as subgroups of `↥C`.
    -- `a ⊔ x = ⊤`: `(A ⊔ X) ∩ C = C ∩ C = ⊤`.
    have haxtop : A.subgroupOf C ⊔ X.subgroupOf C = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hA_C hX_C, show A ⊔ X = C from hCeq.symm,
        Subgroup.subgroupOf_self]
    -- `Qc ⊓ a = ⊥`.
    have hQc_inf_a : Qbar.subgroupOf C ⊓ A.subgroupOf C = ⊥ := by
      rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, hQbar_inf_A,
        MonoidHom.comap_bot]
      exact C.ker_subtype
    -- The composite `Qc ↪ ↥C ⧸ a` is injective.
    have hinj : Function.Injective
        ((QuotientGroup.mk' (A.subgroupOf C)).comp (Qbar.subgroupOf C).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hy
      have hmem : (Qbar.subgroupOf C).subtype y ∈ Qbar.subgroupOf C ⊓ A.subgroupOf C :=
        ⟨y.2, hy⟩
      rw [hQc_inf_a, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      exact Subtype.ext hmem
    -- `↥C ⧸ a` is cyclic: it is a quotient image of the cyclic `↥x` (image of `X ≤ C`).
    haveI hxcyc : IsCyclic ↥(X.subgroupOf C) := by
      haveI : IsCyclic ↥X := hXcyc
      exact isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hX_C).symm.surjective
    haveI hquot_cyc : IsCyclic (↥C ⧸ A.subgroupOf C) := by
      have hsurj : Function.Surjective
          ((QuotientGroup.mk' (A.subgroupOf C)).comp (X.subgroupOf C).subtype) := by
        rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
        have h1 : (A.subgroupOf C ⊔ X.subgroupOf C).map (QuotientGroup.mk' (A.subgroupOf C)) =
            ⊤ := by
          rw [haxtop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
        have hkerbot : (A.subgroupOf C).map (QuotientGroup.mk' (A.subgroupOf C)) = ⊥ := by
          rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        rw [Subgroup.map_sup, hkerbot, bot_sup_eq] at h1
        rw [h1]
      exact isCyclic_of_surjective _ hsurj
    -- Hence `Qc` is cyclic (iso to a subgroup of the cyclic `↥C ⧸ a`).
    haveI hQc_cyc : IsCyclic ↥(Qbar.subgroupOf C) :=
      isCyclic_of_surjective _ (MonoidHom.ofInjective hinj).symm.surjective
    -- `Qbar` is cyclic (`Qbar ≅ Qc`).
    haveI hQbar_cyc : IsCyclic ↥Qbar :=
      isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hQbar_C).surjective
    -- `Q` is cyclic (`Q ≅ Qbar`).
    haveI hQ_cyc : IsCyclic ↥(Q : Subgroup ↥M) :=
      isCyclic_of_surjective _
        (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).symm.surjective
    -- `q ∈ τ₂(M)`: `q ∣ |Qbar| ∣ a.index ∣ |X|`, and `π(X) ⊆ τ₂(M)`.
    have hcardQc : Nat.card ↥(Qbar.subgroupOf C) = Nat.card ↥Qbar :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQbar_C).toEquiv
    have hdvd1 : Nat.card ↥Qbar ∣ (A.subgroupOf C).index := by
      rw [← hcardQc, Subgroup.index_eq_card]
      exact Subgroup.card_dvd_of_injective _ hinj
    have hdvd2 : (A.subgroupOf C).index ∣ Nat.card ↥X := by
      have hidx : (A.subgroupOf C).index = (A.subgroupOf C).relIndex (X.subgroupOf C) := by
        rw [← Subgroup.relIndex_top_right, ← haxtop, Subgroup.relIndex_sup_left]
      have hcardx : Nat.card ↥(X.subgroupOf C) = Nat.card ↥X :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_C).toEquiv
      rw [hidx, ← hcardx]
      exact Subgroup.relIndex_dvd_card (A.subgroupOf C) (X.subgroupOf C)
    have hq_dvd_X : q ∣ Nat.card ↥X := (hq_dvd_Qbar.trans hdvd1).trans hdvd2
    have hqτ₂ : q ∈ tau2 M := hXτ₂ (Nat.mem_primeFactors.mpr ⟨Fact.out, hq_dvd_X, Nat.card_pos.ne'⟩)
    -- Contradiction: `r_q(M) = 2` (from `τ₂`) but `Q` is a cyclic Sylow `q` of `M`.
    have hrank2 : pRank ↥M q = 2 := ((mem_tau2_iff M q).mp hqτ₂).2
    have hrankQ : pRank ↥(Q : Subgroup ↥M) q = 2 := (pRank_sylow_eq Q).trans hrank2
    obtain ⟨B, _, hBnc⟩ :=
      exists_isElementaryAbelian_not_isCyclic_of_two_le_pRank
        (G := ↥(Q : Subgroup ↥M)) (p := q) (le_of_eq hrankQ.symm)
    exact hBnc (Subgroup.isCyclic B)

/-- **BG Corollary 15.4** (mmd L4215): a nonidentity nilpotent **Hall** subgroup `H` of `G`
can be embedded in `M_σ` for a suitable maximal subgroup `M` (`H ⊆ M_σ`).

Faithfulness fix (Lane G): the previous scaffold dropped the **Hall** hypothesis (mmd requires
`H` Hall of `G`) and over-claimed `H ≤ M_F` — the proof only gives `H ⊆ M_σ` (the textbook
conclusion), and `H ⊆ M_F` does not follow (`H` need not be normal in `M`). -/
theorem nilpotent_hall_embeds_in_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {H : Subgroup G}
    (hHnil : Group.IsNilpotent ↥H) (hHne : H ≠ ⊥)
    (hHall : Ch03.IsHallSubgroup (S14.piSet H) H) :
    ∃ M : Subgroup G, M ∈ maximalSubgroupsContaining H ∧
      H ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  haveI := hHnil
  -- Step 1: pick a prime `p₀ ∣ |H|` and the (unique, normal) Sylow `p₀`-subgroup `S` of `↥H`.
  obtain ⟨p₀, hp₀⟩ : ∃ p, p ∈ (Nat.card ↥H).primeFactors := by
    have hne1 : Nat.card ↥H ≠ 1 := fun h => hHne (Subgroup.card_eq_one.mp h)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne1
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩⟩
  haveI : Fact p₀.Prime := ⟨Nat.prime_of_mem_primeFactors hp₀⟩
  set S : Sylow p₀ ↥H := default with hSdef
  set Sbar : Subgroup G := (S : Subgroup ↥H).map H.subtype with hSbar
  have hSbar_le_H : Sbar ≤ H := Subgroup.map_subtype_le _
  have hS_normal : (S : Subgroup ↥H).Normal := Ch01.Sylow.normal_of_isNilpotent S
  -- `S ≠ ⊥`: `p₀ ∣ |↥H|` so `p₀ ∣ |S|`.
  have hn1 : (Nat.card ↥H).factorization p₀ ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd Fact.out Nat.card_pos.ne'
      (Nat.mem_primeFactors.mp hp₀).2.1).ne'
  have hScard_dvd : p₀ ∣ Nat.card ↥(S : Subgroup ↥H) := by
    rw [S.card_eq_multiplicity]; exact dvd_pow_self p₀ hn1
  have hcardSbar : Nat.card ↥Sbar = Nat.card ↥(S : Subgroup ↥H) := by
    rw [hSbar, Subgroup.card_map_of_injective H.subtype_injective]
  have hSbar_ne : Sbar ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardSbar
    rw [← hcardSbar] at hScard_dvd
    exact (Nat.Prime.one_lt Fact.out).ne (Nat.dvd_one.mp hScard_dvd).symm
  -- Step 2: `Sbar` is a full Sylow `p₀`-subgroup of `G` (since `H` is a Hall subgroup of `G`).
  have hSbar_pg : IsPGroup p₀ ↥Sbar := S.isPGroup'.map H.subtype
  have hSbarOf : Sbar.subgroupOf H = (S : Subgroup ↥H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hp₀_ndvd_index : ¬ p₀ ∣ Sbar.index := by
    have hrel : Sbar.relIndex H * H.index = Sbar.index := Subgroup.relIndex_mul_index hSbar_le_H
    rw [← hrel]
    refine (Nat.Prime.not_dvd_mul Fact.out ?_ ?_)
    · -- `p₀ ∤ [H : Sbar] = [↥H : S]`.
      rw [Subgroup.relIndex, hSbarOf]; exact S.not_dvd_index
    · -- `p₀ ∤ [G : H]` because `p₀ ∈ π(H)` and `H` is Hall.
      intro hdvd
      exact (hHall.2 p₀ (Nat.mem_primeFactors.mpr
        ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩)) hp₀
  -- Package `Sbar` as a Sylow `p₀`-subgroup of `G`.
  set Sp : Sylow p₀ G := hSbar_pg.toSylow hp₀_ndvd_index with hSp
  have hSpcoe : (Sp : Subgroup G) = Sbar := hSbar_pg.toSylow_coe hp₀_ndvd_index
  -- Step 3: choose `M ∈ ℳ(N_G(Sbar))`.
  have hNlt : Subgroup.normalizer ((Sp : Subgroup G) : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hSpnormal : (Sp : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal _ hSpnormal with hbot | htop'
    · exact hSbar_ne (hSpcoe ▸ hbot)
    · haveI : IsSolvable ↥(Sp : Subgroup G) := by
        haveI := Sp.isPGroup'.isNilpotent; infer_instance
      rw [htop'] at this
      haveI := this
      exact hG.notSolvable (solvable_of_surjective
        (f := (Subgroup.topEquiv (G := G)).toMonoidHom) (Subgroup.topEquiv (G := G)).surjective)
  obtain ⟨M, hMco, hNM⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer ((Sp : Subgroup G) : Set G))).resolve_left
      hNlt.ne
  have hM : M ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMco
  have hSbar_le_M : Sbar ≤ M := hSpcoe ▸ (Subgroup.le_normalizer.trans hNM)
  -- `Sbar ≤ M_σ`.
  have hSbar_Mσ : Sbar ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    have := sylow_le_Msigma_of_normalizer_le hG hM Sp (hSpcoe ▸ hSbar_ne) hNM
    rwa [hSpcoe] at this
  -- Step 4: every Sylow subgroup of `↥H` maps into `M_σ`.  Then `H ≤ M_σ`.
  -- Suffices: `(Msigma M).subgroupOf H = ⊤`, i.e. each Sylow of `↥H` lies in
  -- `(Msigma M).subgroupOf H`.
  have hH_Mσ : H ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    have htop : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf H = ⊤ := by
      refine eq_top_of_forall_sylow_le (fun q _ P => ?_)
      -- Goal: `(P : Subgroup ↥H) ≤ (Msigma M).subgroupOf H`, i.e. `P.map H.subtype ≤ Msigma M`.
      rw [Subgroup.subgroupOf, ← Subgroup.map_le_iff_le_comap]
      set Pbar : Subgroup G := (P : Subgroup ↥H).map H.subtype with hPbar
      have hPbar_le_H : Pbar ≤ H := Subgroup.map_subtype_le _
      have hP_normal : (P : Subgroup ↥H).Normal := Ch01.Sylow.normal_of_isNilpotent P
      -- If `P` is trivial the goal is immediate.
      by_cases hPtriv : (P : Subgroup ↥H) = ⊥
      · rw [hPbar, hPtriv, Subgroup.map_bot]; exact bot_le
      by_cases hqp : q = p₀
      · -- `q = p₀`: `P = S` (unique Sylow of nilpotent `↥H`), so `Pbar = Sbar ≤ M_σ`.
        subst hqp
        haveI : Unique (Sylow q ↥H) := P.unique_of_normal hP_normal
        have hPS : P = S := Subsingleton.elim _ _
        rw [hPbar, hPS]; exact hSbar_Mσ
      · -- `q ≠ p₀`: `[P, S] = 1`, so `Pbar ≤ C_G(Sbar) ≤ M`, a Sylow `q` of `M`; KEY LEMMA.
        have hdisj : Disjoint (P : Subgroup ↥H) (S : Subgroup ↥H) :=
          IsPGroup.disjoint_of_ne q p₀ hqp _ _ P.isPGroup' S.isPGroup'
        -- `Pbar ≤ C_G(Sbar)`.
        have hPbar_cent : Pbar ≤ Subgroup.centralizer (Sbar : Set G) := by
          rw [hPbar]
          rintro _ ⟨z, hz, rfl⟩
          rw [Subgroup.mem_centralizer_iff]
          rintro _ ⟨w, hw, rfl⟩
          have hcomm : Commute z w :=
            Subgroup.commute_of_normal_of_disjoint _ _ hP_normal hS_normal hdisj z w hz hw
          have hcg : (H.subtype z) * (H.subtype w) = (H.subtype w) * (H.subtype z) := by
            rw [← map_mul, ← map_mul, hcomm]
          exact hcg.symm
        -- `Pbar ≤ M`.
        have hPbar_M : Pbar ≤ M :=
          hPbar_cent.trans ((Subgroup.centralizer_le_normalizer _).trans (hSpcoe ▸ hNM))
        -- `Pbar` is a nontrivial full Sylow `q` of `G`.
        have hPbar_pg : IsPGroup q ↥Pbar := P.isPGroup'.map H.subtype
        have hcardP : Nat.card ↥Pbar = Nat.card ↥(P : Subgroup ↥H) := by
          rw [hPbar, Subgroup.card_map_of_injective H.subtype_injective]
        have hPbar_ne : Pbar ≠ ⊥ := by
          intro hb
          rw [hb, Subgroup.card_bot] at hcardP
          exact hPtriv (Subgroup.card_eq_one.mp hcardP.symm)
        obtain ⟨c, hc⟩ := hPbar_pg.exists_card_eq
        have hc0 : c ≠ 0 := by
          rintro rfl; rw [pow_zero] at hc; exact hPbar_ne (Subgroup.card_eq_one.mp hc)
        have hqdvdH : q ∣ Nat.card ↥H :=
          (hc ▸ dvd_pow_self q hc0).trans (Subgroup.card_dvd_of_le hPbar_le_H)
        have hPbarOf : Pbar.subgroupOf H = (P : Subgroup ↥H) :=
          Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
        have hq_ndvd : ¬ q ∣ Pbar.index := by
          have hrel : Pbar.relIndex H * H.index = Pbar.index := Subgroup.relIndex_mul_index
              hPbar_le_H
          rw [← hrel]
          refine Nat.Prime.not_dvd_mul Fact.out ?_ ?_
          · rw [Subgroup.relIndex, hPbarOf]; exact P.not_dvd_index
          · intro hdvd
            exact (hHall.2 q (Nat.mem_primeFactors.mpr
              ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩))
              (Nat.mem_primeFactors.mpr ⟨Fact.out, hqdvdH, Nat.card_pos.ne'⟩)
        set Pp : Sylow q G := hPbar_pg.toSylow hq_ndvd with hPp
        have hPpcoe : (Pp : Subgroup G) = Pbar := hPbar_pg.toSylow_coe hq_ndvd
        -- Restrict `Pp` to a (nontrivial) Sylow `q`-subgroup `Q'` of `↥M`.
        obtain ⟨Q', hQ'⟩ :=
          OddOrder.BG.Ch3.S10.exists_sylow_subgroupOf_of_le Pp (hPpcoe ▸ hPbar_M)
        have hQ'map : (Q' : Subgroup ↥M).map M.subtype = Pbar := by
          rw [hQ', Subgroup.map_subgroupOf_eq_of_le (hPpcoe ▸ hPbar_M), hPpcoe]
        have hQ'ne : (Q' : Subgroup ↥M) ≠ ⊥ := by
          intro hb
          rw [hb, Subgroup.map_bot] at hQ'map
          exact hPbar_ne hQ'map.symm
        -- KEY LEMMA: `Q'.map M.subtype ≤ M_σ`.
        have hQ'C : (Q' : Subgroup ↥M).map M.subtype ≤ Subgroup.centralizer (Sp : Set G) := by
          have hset : (Sp : Set G) = (Sbar : Set G) := SetLike.coe_set_eq.mpr hSpcoe
          rw [hQ'map, hset]; exact hPbar_cent
        have hfinal := sylow_le_Msigma_of_le_centralizer_sylow hG hM Sp (hSpcoe ▸ hSbar_ne)
          (hSpcoe ▸ hSbar_Mσ) Q' hQ'ne hQ'C
        rw [hQ'map] at hfinal
        rw [hPbar]; exact hfinal
    intro y hy
    have hmem : (⟨y, hy⟩ : ↥H) ∈ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf H := by
      rw [htop]; trivial
    exact hmem
  exact ⟨M, mem_maximalSubgroupsContaining.mpr
    ⟨hMco, hH_Mσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M)⟩, hH_Mσ⟩

end OddOrder.BG.Ch4.S15
