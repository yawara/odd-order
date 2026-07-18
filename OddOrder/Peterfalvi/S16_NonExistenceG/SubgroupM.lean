import OddOrder.GroupTheory.RepresentationTheory.ConjugationFieldModel
import OddOrder.Peterfalvi.S16_NonExistenceG.SubgroupMCore

/-!
# Peterfalvi (14.4)/(14.6)/(14.11.3) — the `S`/`T`-side Frobenius kernels over the `M`-carrier

Split from the former monolithic `OddOrder.Peterfalvi.S16_NonExistenceG` (directory split, issue
0103); the `MHypothesis` carrier and the (14.11) numeric/parity groundwork are in the prefix
`SubgroupMCore.lean` (2000-line limit split).
-/
namespace OddOrder.Peterfalvi.S16
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped BigOperators

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Coq `frobPU` (`PFsection14.v:111-124`), realized**: given a (9.7.b) field-model package —
an additive isomorphism `e : Additive ↥P ≃+ 𝔽_{p^q}` with an **injective** character
`μ : U ↪ 𝔽_{p^q}^×` linearizing the conjugation action of `U` on `P` — the derived subgroup
`S' = P ⋊ U` is a **Frobenius group with kernel `P`**.  This is the Lean form of the Coq
derivation `typeP_Galois_P … → Frobenius_semiregularP`: a `U`-element fixing a nonidentity
`P`-point forces `μ(u) = 1`, i.e. `u = 1` — the Frobenius (semiregularity) condition.  The
`u`-**value** `|U| = (p^q−1)/(p−1)` is deliberately *not* an input: (13.15) supplies it only in
the `p ≢ 1 (mod q)` branch (`qu = (p^q−1)/(p−1)` in the other), and Coq's `frobPU` never
consumes it — only the injectivity of the model (issue 0115 statement audit).  The complement
structure is the carrier: `S' = P ⊔ U` (`S_deriv_eq_PU`), `P ⊓ U = ⊥` (`P_inf_U_eq_bot`), `P`
normal in `S` (`maxNilpotentNormalHall`), `P ≠ ⊥` (`P_ne_bot`), and `U ≠ ⊥` from the §13
`U ⋊ W₁` Frobenius structure (`basic_structure`). -/
theorem frobenius_PU_of_field_repr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hrepr : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
      ∃ (e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
        (μ : ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ),
        Function.Injective μ ∧
        ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
          e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
              ↥hyp.base.P))
            = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x)) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG hyp.base.S)
      (hyp.base.P.subgroupOf (derivedInG hyp.base.S))
      (hyp.base.U.subgroupOf (derivedInG hyp.base.S)) := by
  classical
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hP_le : hyp.base.P ≤ derivedInG hyp.base.S := by
    rw [hyp.base.S_deriv_eq_PU]; exact le_sup_left
  have hU_le : hyp.base.U ≤ derivedInG hyp.base.S := by
    rw [hyp.base.S_deriv_eq_PU]; exact le_sup_right
  have hS'_le : derivedInG hyp.base.S ≤ hyp.base.S := Subgroup.map_subtype_le _
  -- `P` is `S`-conjugation-stable (`maxNilpotentNormalHall` is normal in `S`)
  have hPconjS : ∀ s ∈ hyp.base.S, ∀ x ∈ hyp.base.P, s * x * s⁻¹ ∈ hyp.base.P := by
    intro s hs x hx
    have hnrm := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.base.S
    have := hnrm.conj_mem ⟨x, hP_le.trans hS'_le hx⟩
      (by rw [Subgroup.mem_subgroupOf]; exact hyp.base.P_eq_SF ▸ hx) ⟨s, hs⟩
    rw [Subgroup.mem_subgroupOf] at this
    exact hyp.base.P_eq_SF ▸ this
  -- normality of `P.subgroupOf S'` in `↥S'` (used twice: the field and the product)
  have hnormal : (hyp.base.P.subgroupOf (derivedInG hyp.base.S)).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hPconjS (g : G) (hS'_le g.2) (n : G) hn
  refine
    { isNormal := hnormal
      isComplement := ?_
      ne_bot_kernel := ?_
      ne_bot_complement := ?_
      conj_frobenius := ?_ }
  · -- complement: disjoint + full product
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro z hzP hzU
      rw [Subgroup.mem_subgroupOf] at hzP hzU
      have : (z : G) ∈ hyp.base.P ⊓ hyp.base.U := ⟨hzP, hzU⟩
      rw [P_inf_U_eq_bot hG hyp, Subgroup.mem_bot] at this
      exact Subtype.ext this
    · -- `N ⊔ A = ⊤` (carrier `S' = P ⊔ U`) and `N` normal ⟹ `↑N * ↑A = univ`
      haveI := hnormal
      have hsup : hyp.base.P.subgroupOf (derivedInG hyp.base.S)
          ⊔ hyp.base.U.subgroupOf (derivedInG hyp.base.S) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hP_le hU_le, ← hyp.base.S_deriv_eq_PU]
        exact Subgroup.subgroupOf_self _
      calc (hyp.base.P.subgroupOf (derivedInG hyp.base.S) : Set ↥(derivedInG hyp.base.S))
            * (hyp.base.U.subgroupOf (derivedInG hyp.base.S) : Set ↥(derivedInG hyp.base.S))
          = ((hyp.base.P.subgroupOf (derivedInG hyp.base.S)
              ⊔ hyp.base.U.subgroupOf (derivedInG hyp.base.S) :
                Subgroup ↥(derivedInG hyp.base.S)) : Set ↥(derivedInG hyp.base.S)) := by
            rw [Subgroup.normal_mul]
        _ = Set.univ := by rw [hsup]; simp
  · -- `P ≠ ⊥`
    intro hbot
    have hPbot : hyp.base.P = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hP_le hx⟩ : ↥(derivedInG hyp.base.S))
          ∈ hyp.base.P.subgroupOf (derivedInG hyp.base.S) :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [hbot, Subgroup.mem_bot] at this
      simpa using congrArg Subtype.val this
    exact P_ne_bot hG hyp.base hPbot
  · -- `U ≠ ⊥`: the §13 `U ⋊ W₁` Frobenius structure has nontrivial kernel `U`
    intro hbot
    have hUbot : hyp.base.U = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hU_le hx⟩ : ↥(derivedInG hyp.base.S))
          ∈ hyp.base.U.subgroupOf (derivedInG hyp.base.S) :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [hbot, Subgroup.mem_bot] at this
      simpa using congrArg Subtype.val this
    obtain ⟨data, -⟩ := OddOrder.Peterfalvi.S15.basic_structure hG hyp.base
    exact data.UW1_frobenius.ne_bot_kernel (by rw [hUbot, Subgroup.bot_subgroupOf])
  · -- semiregularity from the (9.7.b) field model
    intro a haA ha1 n hnN hn1 heq
    rw [Subgroup.mem_subgroupOf] at haA hnN
    obtain ⟨e, μ, hμinj, hcompat⟩ := hrepr
    set v : ↥hyp.base.U := ⟨(a : G), haA⟩
    set x : ↥hyp.base.P := ⟨(n : G), hnN⟩
    have hGeq : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      simpa using congrArg Subtype.val heq
    -- transport the fix through the field model: `e(x) = μ(v)·e(x)`
    have hfix : e (Additive.ofMul x) =
        ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
          GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x) := by
      have h := hcompat v x
      rw [show (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ : ↥hyp.base.P) = x from
        Subtype.ext hGeq] at h
      exact h
    -- a field element fixed by a nontrivial unit is zero; injectivity finishes
    have hcases : ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
        GaloisField hyp.base.p hyp.base.q) = 1 ∨ e (Additive.ofMul x) = 0 := by
      have : (((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
          GaloisField hyp.base.p hyp.base.q) - 1) * e (Additive.ofMul x) = 0 := by
        rw [sub_mul, one_mul, ← hfix, sub_self]
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr h
    rcases hcases with h | h
    · -- `μ(v) = 1 → v = 1 → a = 1`
      apply ha1
      have hv1 : v = 1 := hμinj (by ext : 1; simpa using h)
      exact Subtype.ext (show (a : G) = 1 from congrArg Subtype.val hv1)
    · -- `e(x) = 0 → x = 1 → n = 1`
      apply hn1
      have hx0 : Additive.ofMul x = 0 := e.injective (by rw [map_zero]; exact h)
      have hx1 : x = 1 := Additive.ofMul.injective hx0
      exact Subtype.ext (show (n : G) = 1 from congrArg Subtype.val hx1)

/-- **The (9.7.b) `S`-side field-model package** (Coq `typeP_Galois_P` for `S` with the §13
trivial kernels `Ptype_Fcore_kernel_trivial`/`Ptype_Fcompl_kernel_trivial`,
`PFsection14.v:115-118`): an additive isomorphism `e : Additive ↥P ≃+ 𝔽_{p^q}` and an
injective character `μ : U ↪ 𝔽_{p^q}^×` linearizing the conjugation action of `U` on `P`.

This is the **branch-independent** honest (9.7.b) gate — it deliberately does *not* posit the
`u`-value `|U| = (p^q−1)/(p−1)`: by (13.15) that value holds only in the `p ≢ 1 (mod q)`
branch (in the other branch `qu = (p^q−1)/(p−1)`), so positing it unconditionally was a
statement-level overclaim (issue 0115 audit).  The package itself is what `typeP_Galois S`
supplies in **both** branches (Schur: an abelian group acting faithfully and irreducibly on
`𝔽_p^q` lies in a Singer torus `𝔽_{p^q}^×`).

The branch-independent package is assembled from the unconditional (10.10) exclusion of type V,
the unconditional (11.3) `H₀C` noncoherence refuter, and the canonical (14.3)/(14.5)
`LHypothesis.typeI_data`.  The S-side dispatcher then uses (13.12) `c = 1`; only an actual
Clifford case-(a) certificate requests the (13.13) sharp parameters, while case (b) returns the
transported §9 Singer realization directly (issue 0117). -/
theorem s_side_field_repr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    ∃ (e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
      (μ : ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ),
      Function.Injective μ ∧
      ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
        e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
            ↥hyp.base.P))
          = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
              GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x) := by
  have hnoV := OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG
  have hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G :=
    fun s13 =>
      OddOrder.Peterfalvi.S13.S_H0C_not_coherent_unconditional hG s13
  obtain ⟨Ldata⟩ := exists_LHypothesis hG hnoV hncH0C hyp
  simpa using
    OddOrder.Peterfalvi.S15.sSide_galoisField_repr_of_c_eq_one_and_caseA_parameters
      hG hyp.base
        (hyp.base.c_eq_one_of_lambda_dichotomy hG hyp.nuGridSupply)
        (fun caseA =>
          hyp.base.caseA_parameters_of_clifford_caseA
            hG caseA (pins := hyp.nuGridSupply))
        Ldata.typeI_data

/-- **Peterfalvi (14.6)+(13.12), the S-side Frobenius kernel** — `C_{S'}(x) ≤ P` for
`x ∈ P#`.  Follows Coq `PFsection14.v:111-141` *exactly*: the (9.7.b) resolution for `S`
(`typeP_Galois S`, via `typeP_Galois_P` and the §13 (13.12) structure) makes
`S' = P ⋊ U` a **Frobenius group with kernel `P`** (Coq `frobPU`), and the containment is
the standard Frobenius kernel-centralizer property `Frobenius_cent1_ker` — here the proven
Isaacs Thm 6.4 transport `IsFrobeniusGroup.centralizer_kernel_le`.

The `typeP_Galois_P` package is the theorem `s_side_field_repr` above, assembled upstream from
the §9 realization and the §13–§14 structural producers.  The remaining argument is Coq's
`frobPU` semiregularity plus the `↥S'`-coordinate transport.  (The alternative route through the
(14.2) field model `FieldNormalizerData` is *not* used here: `field_normalizer_structure` sits
downstream of `exists_MHypothesis`, which consumes (14.11.3) and hence this very lemma.) -/
theorem s_side_frobenius_kernel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ x ∈ sharpSubgroup hyp.base.P,
      derivedInG hyp.base.S ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.base.P := by
  intro x hx
  rw [sharpSubgroup, Set.mem_sdiff_singleton] at hx
  obtain ⟨hxP, hx1⟩ := hx
  have frobPU : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG hyp.base.S)
      (hyp.base.P.subgroupOf (derivedInG hyp.base.S))
      (hyp.base.U.subgroupOf (derivedInG hyp.base.S)) :=
    frobenius_PU_of_field_repr hG hyp (s_side_field_repr hG hyp)
  -- `P ≤ S'` (carrier: `S' = P ⊔ U`)
  have hP_le : hyp.base.P ≤ derivedInG hyp.base.S := by
    rw [hyp.base.S_deriv_eq_PU]; exact le_sup_left
  -- transport the Isaacs 6.4 kernel-centralizer containment from `↥S'`-coordinates
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgS', hgC⟩ := hg
  have hkey := frobPU.centralizer_kernel_le
    (⟨x, hP_le hxP⟩ : ↥(derivedInG hyp.base.S)) (Subgroup.mem_subgroupOf.mpr hxP)
    (fun hc => hx1 (by simpa using congrArg Subtype.val hc))
  have hgP : (⟨g, hgS'⟩ : ↥(derivedInG hyp.base.S))
      ∈ hyp.base.P.subgroupOf (derivedInG hyp.base.S) := by
    apply hkey
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : g * x = x * g := by
      have := Subgroup.mem_centralizer_iff.mp hgC x rfl
      -- `mem_centralizer_iff` gives `∀ h ∈ {x}, h * g = g * h`; normalize orientation
      exact this.symm
    exact Subtype.ext (by simpa using hcomm)
  exact Subgroup.mem_subgroupOf.mp hgP

/-- **The `(9.7.b)` T-side field model** (issue 9078 / 9000 sphere, issue 0115 Campaign B): the
T-side field-algebra package assembled into a `TFieldModelData hyp.base` via the proven producer
`tFieldModelData_of_repr` (`SemidirectFieldModel.fieldModelEmbedding`, `E = Q`, `C = V`).

**Now proven** by instantiating the lane-a shared adapter
`ConjugationFieldModel.exists_normOne_galoisField_conjugation_repr` (issue 9097) at
`(r, s, E, C) = (q, p, Q, V)`.  Its inputs are supplied as follows:

* `D = ⊥`, the `v`-value `v = (q^p−1)/(q−1)`, and `|Q| = q^p` — the (13.4)/(14.4) case-(9.7.b)
  facts `S15.T_caseB_facts_unconditional`; via `D_eq`/`d_eq_card_D`/`card_V_eq_vd` these give the
  faithfulness `V ⊓ C_G(Q) = ⊥` and `|V| = (q^p−1)/(q−1)` (no branch issue on the `T`-side:
  `q ≡ 1 (mod p)` is impossible for `q < p`);
* `V` abelian — the unconditional (13.2.a)-for-`T` `isMulCommutative_V_unconditional`;
* `Q` elementary abelian — `Q_elementaryAbelian_T` from the (14.9) `T_typeII` (the one input
  still threading the type-II structure, hence the `hnoV`/`hncH0C` parameters);
* `V ≤ N_G(Q)` — `V ≤ T' ≤ T = N_G(Q)` (`normalizer_Q_eq_T`). -/
theorem t_side_caseB_fieldModel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) : Nonempty (TFieldModelData hyp.base) := by
  letI : Fact hyp.base.q.Prime := ⟨hyp.base.q_prime⟩
  -- `V` normalizes `Q`: `V ≤ T' ≤ T = N_G(Q)` (`normalizer_Q_eq_T`).
  have hVN : hyp.base.V ≤ Subgroup.normalizer (hyp.base.Q : Set G) := by
    intro g hg
    rw [OddOrder.Peterfalvi.S15.normalizer_Q_eq_T hG hyp.base]
    exact ((show hyp.base.V ≤ derivedInG hyp.base.T by
      rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right).trans (Subgroup.map_subtype_le _)) hg
  have hVQ : ∀ (v : ↥hyp.base.V) (x : ↥hyp.base.Q),
      (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.base.Q := by
    intro v x
    exact (Subgroup.mem_set_normalizer_iff.mp (hVN v.2) (x : G)).mp x.2
  -- `(9.7.b)` field-algebra package `(e, μ, hcompat)` for `T`, via the 9097 adapter
  obtain ⟨e, μ, hμ_inj, hμ_range, hcompat⟩ :
      ∃ (e : Additive ↥hyp.base.Q ≃+ GaloisField hyp.base.q hyp.base.p)
        (μ : ↥hyp.base.V →* (GaloisField hyp.base.q hyp.base.p)ˣ)
        (_ : Function.Injective μ)
        (_ : μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.q hyp.base.p),
        ∀ (v : ↥hyp.base.V) (x : ↥hyp.base.Q),
          e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hVQ v x⟩ : ↥hyp.base.Q))
            = ((μ v : (GaloisField hyp.base.q hyp.base.p)ˣ) : GaloisField hyp.base.q hyp.base.p) *
                e (Additive.ofMul x) := by
    -- (13.4)/(14.4): `D = ⊥`, the `v`-value, `|Q| = q^p`.
    obtain ⟨hDbot, hv, hcardQ⟩ :=
      OddOrder.Peterfalvi.S15.T_caseB_facts_unconditional hG hyp.base hyp.q_lt_p
        (pins := hyp.nuGridSupply)
    have hQ_elemAb : IsElementaryAbelian hyp.base.q ↥hyp.base.Q :=
      OddOrder.Peterfalvi.S15.Q_elementaryAbelian_T hG hyp.base (T_typeII hG hnoV hncH0C hyp)
    have hVcomm : IsMulCommutative ↥hyp.base.V :=
      hyp.base.isMulCommutative_V_unconditional hG
    -- faithfulness `V ⊓ C_G(Q) = ⊥` and `|V| = v` from `D = ⊥` (`d = 1`).
    have hfaith : hyp.base.V ⊓ Subgroup.centralizer (hyp.base.Q : Set G) = ⊥ := by
      rw [← hyp.base.D_eq]; exact hDbot
    have hd1 : hyp.base.d = 1 := by
      rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
    have hcardV : Nat.card ↥hyp.base.V =
        (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) := by
      rw [hyp.base.card_V_eq_vd, hd1, mul_one, hv]
    obtain ⟨e, μ, hμinj, hμrange, hcompat₀⟩ :=
      OddOrder.RepresentationTheory.ConjugationFieldModel.exists_normOne_galoisField_conjugation_repr
        hyp.base.q_prime hyp.base.p_prime hyp.base.p_odd hQ_elemAb hVcomm hVN hcardQ hcardV hfaith
    refine ⟨e, μ, hμinj, hμrange, fun v x => ?_⟩
    have h := hcompat₀ v x
    rwa [show OddOrder.RepresentationTheory.ConjugationFieldModel.conjugate hVN v x
        = (⟨(v : G) * (x : G) * (v : G)⁻¹, hVQ v x⟩ : ↥hyp.base.Q) from
      Subtype.ext (by simp)] at h
  exact tFieldModelData_of_repr hyp.base e μ hμ_inj hμ_range hVQ hcompat

/-- **Peterfalvi (14.4)+(13.12), the T-side Frobenius kernel** — `C_{T'}(x) ≤ Q` for
`x ∈ Q#` (dual of `s_side_frobenius_kernel`: (14.4) puts `T` in case (9.7.b), and the
T-side field model has Frobenius kernel `Q`).  Discharged (engine proven, `S16_G0Coprime`) by the
minimal (14.4) carrier `TFieldModelData` from `t_side_caseB_fieldModel` (injective
`σ : F_{q^p} ⋊ V* →* G` with kernel `Q`, complement `V`) through the proven transport
`TFieldModelData.derived_inf_centralizer_le_Q`. -/
theorem t_side_frobenius_kernel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    ∀ x ∈ sharpSubgroup hyp.base.Q,
      derivedInG hyp.base.T ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.base.Q := by
  intro x hx
  obtain ⟨data⟩ := t_side_caseB_fieldModel hG hnoV hncH0C hyp
  exact data.derived_inf_centralizer_le_Q hx

/-- **Peterfalvi (14.11.3), support half**: every element of the generic set `G₀` has order
prime to `pq`.  The avoidance fields of `MHypothesis` (`G0_avoid`) feed the proven
(14.11.3) chain `orderOf_coprime_pq_of_not_mem_conj` (W-orbit bridge + per-side
Sylow/TI/(2.1) coset collapse, `S16_G0Coprime`), with the two case-(9.7.b) Frobenius-kernel
inputs supplied by `s_side_frobenius_kernel`/`t_side_frobenius_kernel`. -/
theorem MHypothesis.G0_orderOf_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) {g : G} (hg : g ∈ Mdata.G0) :
    Nat.Coprime (orderOf g) (hyp.base.p * hyp.base.q) := by
  obtain ⟨hreg, hP, hQ⟩ := Mdata.G0_avoid g hg
  exact orderOf_coprime_pq_of_not_mem_conj hG hyp.base (T_typeII hG hnoV hncH0C hyp)
    (s_side_frobenius_kernel hG hyp) (t_side_frobenius_kernel hG hnoV hncH0C hyp) hreg hP hQ

/-- **Peterfalvi (3.9.a,c) for the `η`-grid on the generic set `G₀`** (faithful §3 Dade obligation).
For `g ∈ G₀` (an element of order prime to `pq` lying outside `Ã(M)`):

* (3.9.c) each grid value `η_ij(g)` is a rational integer (`eta_int`);
* (3.9.a) the grid is invariant under the conjugation `(i,j) ↦ (−i,−j)` (`finNeg`), i.e. the values
  pair up (`eta_pair`), with principal value `η₀₀(g) = 1` (`eta_principal`);
* `β_M^τ(g) = 0`, since `g ∉ Ã(M)` (`betaM_vanish`).

These are the Dade-character integrality/symmetry facts of Peterfalvi (3.9) specialised to the
`M`-grid plus the support vanishing of (14.10); their honest construction lives in the §3/§4
Dade-isometry layer (the abstract §16 `ω`/`η`/`tau3` carriers do not yet pin it). -/
structure EtaGenericData [Finite G]
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) where
  eta_int : ∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
    ∃ m : ℤ, hyp.base.eta i j g = (m : ℂ)
  eta_pair : ∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
    hyp.base.eta (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) g
      = hyp.base.eta i j g
  eta_principal : ∀ g ∈ Mdata.G0,
    hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ g = 1
  betaM_vanish : ∀ g ∈ Mdata.G0, Mdata.betaM g = 0

/-- **Peterfalvi (3.9.a/c), the Galois half of the `η`-grid facts** — the genuine §3/§5
obligation still gated on the `τ₃`-Galois-equivariance (issue 3002 follow-up; the carried
grid primitives determine `η` on `W`-regular values but not its Galois behaviour off `W`):
on the generic set `G₀`, the `η`-grid takes integer values (3.9.c) and pairs under the
negation involution (3.9.a). -/
theorem eta_grid_galois_facts_on_G0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) :
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ∃ m : ℤ, hyp.base.eta i j g = (m : ℂ)) ∧
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      hyp.base.eta (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) g
        = hyp.base.eta i j g) := by
  -- Now **proven** by citing the issue-3002 keystone fields threaded into `S15.Hypothesis`
  -- by lane b (`eta_intCast_of_coprime` = (3.9.c), `eta_pair_of_coprime` = (3.9.a)), which apply
  -- to every `g` of order coprime to `pq` — and `G₀` elements are exactly such
  -- (`MHypothesis.G0_orderOf_coprime`).
  refine ⟨fun g hg i j => ?_, fun g hg i j => ?_⟩
  · exact hyp.base.eta_intCast_of_coprime g (Mdata.G0_orderOf_coprime hG hnoV hncH0C hg) i j
  · exact hyp.base.eta_pair_of_coprime g (Mdata.G0_orderOf_coprime hG hnoV hncH0C hg) i j

/-- **Peterfalvi (3.9.a/c) `η`-grid facts on `G₀`**: on the generic set `G₀`, the `η`-grid
takes integer values (3.9.c), pairs under the negation involution (3.9.a), and has principal
entry `η₀₀ = 1`.  The principal entry is now genuine (`eta_principal_apply_eq_one`, the
issue-2033 grid-semantics payoff, `S16_GridExpansion`); the Galois half remains the named
obligation `eta_grid_galois_facts_on_G0`. -/
theorem eta_grid_facts_on_G0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) :
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ∃ m : ℤ, hyp.base.eta i j g = (m : ℂ)) ∧
    (∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      hyp.base.eta (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) g
        = hyp.base.eta i j g) ∧
    (∀ g ∈ Mdata.G0,
      hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ g = 1) := by
  obtain ⟨hint, hpair⟩ := eta_grid_galois_facts_on_G0 hG hnoV hncH0C hyp Mdata
  exact ⟨hint, hpair, fun g _ => eta_principal_apply_eq_one hyp.base g⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.9)/(14.10) generic-set producer.**  The `η`-grid integrality/symmetry on `G₀`
(`eta_grid_facts_on_G0`, the §3/§5 grid obligation) together with the **now-genuine** support
vanishing `β_M^τ = 0` on `G₀`: `β_M = β` is a Dade image, so its support lies in `Ã(M)`
(`beta_support_subset_dadeSupport`), while `G₀` avoids `Ã(M)` (`G0_off_dadeSupport`). -/
theorem eta_generic_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) :
    EtaGenericData hyp Mdata := by
  obtain ⟨hint, hpair, hprinc⟩ := eta_grid_facts_on_G0 hG hnoV hncH0C hyp Mdata
  refine { eta_int := hint, eta_pair := hpair, eta_principal := hprinc, betaM_vanish := ?_ }
  -- **Peterfalvi (14.11.3)**: `β_M^τ` vanishes off its Dade support `Ã(M)`, and `G₀ ⊆ G ∖ Ã(M)`.
  intro g hg
  rw [Mdata.betaM_eq]
  by_contra hne
  have hmem := Mdata.h78.beta_support_subset_dadeSupport (Function.mem_support.mpr hne)
  rw [Mdata.h78_hyp_eq] at hmem
  exact Mdata.G0_off_dadeSupport g hg hmem

/-- **Peterfalvi (14.11.3)**: on the generic set `G_0`, the extended character `ψ^{τ₁}` has
absolute value at least one: `|ψ^{τ₁}(g)| ≥ 1` for `g ∈ G_0`.

De-opacified (lane-c §16 char-endpoint): the former opaque carrier field
`generic_bound_formula : G → Prop` is replaced by this concrete inequality on the `ℤ`-linear
Dade extension `τ₁` applied to `ψ`.  Proof recipe (Pf p.89): for `g ∈ G_0`, `β_M^τ(g) = 0` (as
`g ∉ Ã(M)`), so by (14.11.2) `ψ^{τ₁}(g) = ±Σ_{i,j}(±η_ij(g))`; `g` has order prime to `pq`, so by
(3.9.c) each `η_ij(g) ∈ ℤ` and by (3.9.a) they pair under conjugation, and `η₀₀(g) = 1`, whence
`Σ(±η_ij(g)) ∈ 2ℤ+1`, giving absolute value `≥ 1`.  Depends on `betaM_expansion` (14.11.2). -/
theorem generic_character_bound [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    ∀ g : G, g ∈ Mdata.G0 → 1 ≤ ‖(Mdata.tau1 Mdata.psi) g‖ := by
  classical
  -- (14.11.2): the signed `η`-grid expansion of `β_M^τ`.
  obtain ⟨_he, ε, hε, χ, hχnorm, hexp⟩ := betaM_expansion _hG hnoV hncH0C hyp Mdata hne
  -- (3.9)/(14.10): the `η`-grid is integral and conjugation-symmetric on `G₀`, and `β_M^τ`
  -- vanishes there.
  have hdata := eta_generic_data _hG hnoV hncH0C hyp Mdata
  intro g hg
  -- (3.9.c) integer values of the `η`-grid at `g`.
  choose n hn using hdata.eta_int g hg
  -- Evaluate the (14.11.2) expansion at `g` pointwise.
  have happ : Mdata.betaM g
      = (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
          (ε i j : ℂ) * (hyp.base.eta i j g)) - χ g := by
    rw [hexp, ClassFunction.sub_apply, classFunction_sum_apply]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [classFunction_sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ClassFunction.smul_apply]
  -- `β_M^τ(g) = 0` gives `χ(g) = Σ ε_ij η_ij(g) = Σ ε_ij (n_ij : ℂ)`.
  have hχ2 : χ g = ∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (ε i j : ℂ) * (n i j : ℂ) := by
    have h0 : (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
        (ε i j : ℂ) * (hyp.base.eta i j g)) - χ g = 0 := by
      rw [← happ]; exact hdata.betaM_vanish g hg
    rw [(sub_eq_zero.mp h0).symm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hn i j]
  -- (3.9.a) the integer grid pairs under negation with principal value `1`.
  have hpair : ∀ i j,
      n (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) = n i j := by
    intro i j
    have he := hdata.eta_pair g hg i j
    rw [hn, hn] at he
    exact_mod_cast he
  have h00 : n ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ = 1 := by
    have he := hdata.eta_principal g hg
    rw [hn] at he
    exact_mod_cast he
  -- The signed paired sum has norm `≥ 1` (14.11.3 arithmetic core), and `‖χ‖ = ‖ψ^{τ₁}‖`.
  calc (1 : ℝ)
      ≤ ‖∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (ε i j : ℂ) * (n i j : ℂ)‖ :=
        one_le_norm_eta_grid_signed_sum hyp.base.q_prime.pos hyp.base.p_prime.pos
          hyp.base.q_odd hyp.base.p_odd n ε hε hpair h00
    _ = ‖χ g‖ := by rw [hχ2]
    _ = ‖(Mdata.tau1 Mdata.psi) g‖ := hχnorm g

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4), line-83 upper-bound step** — the V-side `M`-analogue of
`S12.Hypothesis.chiRhoNormSq_zeta_le_line83`.  Applying the family inequality (7.5)
`S09.family_inequality` to the norm-one character `ψ^{τ₁}` (`psi_tau1_norm_one`) and dropping the
`G₀`-part of the sum via (14.11.3) `generic_character_bound` (`|ψ^{τ₁}(g)| ≥ 1` on `G₀`) together
with the inclusion `G₀ ⊆ famG₀` (`G0_off_dadeSupport`) gives
`‖ψ^{τ₁ρ}‖² ≤ |A(M)|/|M| + (1/|G|)(|famG₀| − |G₀|)`.

This is the first step of (14.11.4)'s upper bound; the remaining passage to the displayed
`1 − 1/p − 1/q + …` is the `|K#|/|M|` evaluation and the §8 TI-counting of the `(W#)^G`/`(P#)^G`/
`(Q#)^G` contributions, isolated for the cascade producer `normCascadeData`.  `famG₀ =
(toFamilyHypothesis71).G0 = G − Ã(M)` and `G₀ = Mdata.G0`. -/
theorem MHypothesis.chiRhoNormSq_psi_le_line83 [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0
      ≤ (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
          / (Nat.card ↥Mdata.M : ℝ)
        + (Nat.card G : ℝ)⁻¹ * ((Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
          - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)) := by
  haveI := Mdata.finiteG
  have hA0 : (Mdata.toFamilyHypothesis71).A 0
      = OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI := rfl
  have hL0 : (Mdata.toFamilyHypothesis71).L 0 = Mdata.M := rfl
  -- (7.5) line 81 (single member, `k = 1`).
  have h81 := OddOrder.Peterfalvi.S09.family_inequality (Mdata.toFamilyHypothesis71)
    (Mdata.tau1 Mdata.psi) Mdata.psi_tau1_norm_one
  rw [Fin.sum_univ_one, hA0, hL0] at h81
  -- `G₀ ⊆ famG₀`: every `g ∈ G₀` is off the Dade support `Ã(M)`.
  have hsub : Finset.univ.filter (fun g : G => g ∈ Mdata.G0)
      ⊆ Finset.univ.filter (fun g : G => g ∈ (Mdata.toFamilyHypothesis71).G0) := by
    intro g hg
    rw [Finset.mem_filter] at hg ⊢
    exact ⟨Finset.mem_univ g, fun _ => Mdata.G0_off_dadeSupport g hg.2⟩
  -- Drop the `G₀`-part: `|G₀| ≤ Σ_{G₀} ‖ψ^{τ₁}‖² ≤ Σ_{famG₀} ‖ψ^{τ₁}‖²`.
  have hge : ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
      ≤ ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ Mdata.G0),
          ‖(Mdata.tau1 Mdata.psi : G → ℂ) g‖ ^ 2 := by
    calc ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
        = ∑ _g ∈ Finset.univ.filter (fun g : G => g ∈ Mdata.G0), (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ Mdata.G0),
            ‖(Mdata.tau1 Mdata.psi : G → ℂ) g‖ ^ 2 := by
          refine Finset.sum_le_sum (fun g hg => ?_)
          have hg2 : g ∈ Mdata.G0 := (Finset.mem_filter.mp hg).2
          have h1 := generic_character_bound _hG hnoV hncH0C hyp Mdata hne g hg2
          nlinarith [h1, norm_nonneg ((Mdata.tau1 Mdata.psi : G → ℂ) g)]
  have hdrop : ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
      ≤ ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ (Mdata.toFamilyHypothesis71).G0),
          ‖(Mdata.tau1 Mdata.psi : G → ℂ) g‖ ^ 2 :=
    le_trans hge (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => by positivity))
  have hGinv : (0 : ℝ) ≤ (Nat.card G : ℝ)⁻¹ := by positivity
  have hcS := mul_le_mul_of_nonneg_left hdrop hGinv
  rw [mul_sub] at h81 ⊢
  linarith [h81, hcS]

/-- **`S09.Hypothesis71.chiRho` depends only on the support hypothesis `H71.hyp`.**  Two `(7.1)`
data with the same underlying `S04.Hypothesis` (the same `H(a)`-family) induce the same `ρ`-image
of any `χ`, even if their chosen Dade maps `τ` differ — `chiRho` never mentions `τ`.  Used to
identify the family-inequality `ρ`-norm of (14.11.4) with the (7.8.b) `ρ`-norm of `h78`. -/
theorem chiRhoCF_congr_hyp [Fintype G] {A : Set G} {L : Subgroup G}
    {H71a H71b : OddOrder.Peterfalvi.S09.Hypothesis71 G A L}
    (h : H71a.hyp = H71b.hyp) (χ : ClassFunction G ℂ) :
    H71a.chiRhoCF χ = H71b.chiRhoCF χ := by
  apply ClassFunction.ext
  intro a
  simp only [OddOrder.Peterfalvi.S09.Hypothesis71.chiRhoCF_apply]
  unfold OddOrder.Peterfalvi.S09.Hypothesis71.chiRho
  rw [h]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4) norm bridge.**  The family-inequality `ρ`-norm of `ψ^{τ₁}` (the LHS of
the line-83 bound) equals the (7.8.b) `ρ`-norm `h78.zetaNuRhoNormSq`.  Both are `‖(ψ^{τ₁})^ρ‖²` for
the `(M, A(M))` map `ρ`: `psi_tau1_eq` (`ψ^{τ₁} = ζ^ν`) matches the characters, and `h78_hyp_eq`
(same Dade support hypothesis) plus `chiRhoCF_congr_hyp` (independence of `chiRho` from `τ`) matches
the `ρ`-images.  This is the linchpin tying the (7.5) family-inequality layer to the (7.8.b)
coherence-norm layer of (14.11.4). -/
theorem MHypothesis.chiRhoNormSq_eq_zetaNuRhoNormSq [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0
      = Mdata.h78.zetaNuRhoNormSq := by
  have hcf : ((Mdata.toFamilyHypothesis71).hyp71 0).chiRhoCF (Mdata.tau1 Mdata.psi)
      = Mdata.h78.zetaNuRho := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRho, Mdata.psi_tau1_eq]
    exact chiRhoCF_congr_hyp Mdata.h78_hyp_eq.symm _
  simp only [OddOrder.Peterfalvi.S09.FamilyHypothesis71.chiRhoNormSq,
    OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRhoNormSq, hcf]
  congr 1

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (7.8.b), the unconditional lower bound**
`1 − e/k ≤ ‖ψ^{τ₁ρ}‖²`.  Combines the coherence-norm estimate for the type-I `M`
(`h78_zetaNuRho_normSq_ge`) with `h78.kernelOrder = |K| = k` and
`h78.complementIndex = |M:K| = e` (`h78_H_eq`, `e_eq_index`) via
`chiRhoNormSq_eq_zetaNuRhoNormSq`.  The conditional producer `normCascadeData` rewrites
`e = p q` only after (14.11.2). -/
theorem MHypothesis.rhoNormSq_ge_lower [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    1 - (Mdata.e : ℝ) / (Mdata.k : ℝ)
      ≤ (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0 := by
  rw [Mdata.chiRhoNormSq_eq_zetaNuRhoNormSq]
  -- `h78.kernelOrder = |K| = k`.
  have hko : Mdata.h78.kernelOrder = Mdata.k := by
    rw [Mdata.k_eq_card_K]
    change Nat.card ↥(Mdata.h78.hyp76.H) = Nat.card ↥Mdata.K
    rw [Mdata.h78_H_eq]
  -- Rewrite the (7.8.b) carrier into `e`/`k` and conclude.
  have key := Mdata.h78_zetaNuRho_normSq_ge
  rw [Mdata.h78_complementIndex_eq_e, hko] at key
  exact key

/-- **The type-I Dade support is the kernel sharp** `A(M) = K#`, the §8 cardinality input
`|A(M)| = |K#| = k − 1` of Peterfalvi (14.11.4) (Coq `PFsection14`: the `Dade_cover_inequality`
support term `#|A| = k.-1`).  For a Frobenius group `M` with kernel `N` (the complement acts
fixed-point-freely on `N#`), the centralizer-support
`centralizerSupport N# M = {y ∈ M : y ≠ 1, ∃ x ∈ N#, [y,x]=1}` is exactly `N#`: the forward
inclusion is the Frobenius FPF property `centralizer_kernel_le` (`C_M(x) ≤ N` for `x ∈ N#`), the
reverse takes `x = y`.  Applied with `N = K = M_F`, this is `typeIA M = K#`. -/
theorem centralizerSupport_sharpSubgroup_eq_of_frobenius [Finite G] {M N : Subgroup G}
    {C : Subgroup ↥M}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (N.subgroupOf M) C) (hNM : N ≤ M) :
    OddOrder.GroupTheory.centralizerSupport (OddOrder.GroupTheory.sharpSubgroup N) M
      = OddOrder.GroupTheory.sharpSubgroup N := by
  ext y
  simp only [OddOrder.GroupTheory.centralizerSupport, OddOrder.GroupTheory.sharpSubgroup,
    Set.mem_setOf_eq, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyM, hy1, x, ⟨hxN, hx1⟩, hyx⟩
    have hxM : x ∈ M := hNM hxN
    have hxMsub : (⟨x, hxM⟩ : ↥M) ∈ N.subgroupOf M := (Subgroup.mem_subgroupOf).mpr hxN
    have hx1' : (⟨x, hxM⟩ : ↥M) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hycomm : (⟨y, hyM⟩ : ↥M) ∈ Subgroup.centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hyx ⊢
      exact Subtype.ext hyx
    have hyN : (⟨y, hyM⟩ : ↥M) ∈ N.subgroupOf M :=
      hfrob.centralizer_kernel_le _ hxMsub hx1' hycomm
    exact ⟨(Subgroup.mem_subgroupOf).mp hyN, hy1⟩
  · rintro ⟨hyN, hy1⟩
    refine ⟨hNM hyN, hy1, y, ⟨hyN, hy1⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]

/-- **Peterfalvi (14.11.4): `|A(M)| = k − 1`** — the §8 cardinality input of the upper bound.  The
type-I Dade support `A(M) = typeIA M` equals `K#`
(`centralizerSupport_sharpSubgroup_eq_of_frobenius`
applied to the Frobenius structure of `M` from `typeI_frobenius` (12.7), kernel `K = M_F`), so its
cardinality is `|K| − 1 = k − 1`. -/
theorem MHypothesis.card_typeIA_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) = Mdata.k - 1 := by
  -- Frobenius witness for `M` (kernel `M_F`), from (12.7).
  obtain ⟨fdata, _⟩ :=
    OddOrder.Peterfalvi.S14.typeI_frobenius hG hnoV Mdata.M_maximal ⟨Mdata.typeIHyp.typeI⟩
  -- The two kernels both equal `maxNilpotentNormalHall M`.
  have hKf : fdata.typeI.typeF.H = Mdata.typeIHyp.typeI.typeF.H := by
    rw [fdata.typeI.typeF.H_eq, Mdata.typeIHyp.typeI.typeF.H_eq]
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥Mdata.M
      (Mdata.typeIHyp.typeI.typeF.H.subgroupOf Mdata.M) fdata.complement := hKf ▸ fdata.frobenius
  -- `typeIA M = K#` (FPF support identity).
  have hTI : OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup Mdata.typeIHyp.typeI.typeF.H :=
    centralizerSupport_sharpSubgroup_eq_of_frobenius hfrob Mdata.typeIHyp.typeI.typeF.H_le
  -- `typeF.H = K`, so `|K#| = |K| − 1 = k − 1`.
  have hHK : Mdata.typeIHyp.typeI.typeF.H = Mdata.K := by
    rw [Mdata.typeIHyp.typeI.typeF.H_eq, Mdata.K_eq_MF]
  have hc : Nat.card ↥Mdata.K = ((Mdata.K : Set G)).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  rw [hTI, hHK, Mdata.k_eq_card_K, Nat.card_coe_set_eq, OddOrder.GroupTheory.sharpSubgroup,
    Set.ncard_sdiff (Set.singleton_subset_iff.mpr Mdata.K.one_mem), Set.ncard_singleton, hc]

/-- **Peterfalvi (14.10): `|M| = e k`** — the unconditional order of the type-I maximal `M`,
from `[M : K] = e` (`e_eq_index`) and `|K| = k` (`k_eq_card_K`) by Lagrange.  The conditional
(14.11.4) upper bound substitutes `e = p q` only after (14.11.2). -/
theorem MHypothesis.card_M_eq {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Nat.card ↥Mdata.M = Mdata.e * Mdata.k := by
  have hKleM : Mdata.K ≤ Mdata.M :=
    Mdata.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le Mdata.M
  have hcardK : Nat.card ↥(Mdata.K.subgroupOf Mdata.M) = Nat.card ↥Mdata.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleM).toEquiv
  have hidx : Nat.card ↥Mdata.K * (Mdata.K.subgroupOf Mdata.M).index = Nat.card ↥Mdata.M := by
    rw [← hcardK]; exact Subgroup.card_mul_index _
  have hidxe : (Mdata.K.subgroupOf Mdata.M).index = Mdata.e :=
    Mdata.e_eq_index.symm
  rw [hidxe] at hidx
  rw [← hidx, Mdata.k_eq_card_K]; ring

/-- **The exceptional set `W − (W₁ ∪ W₂)` of a cyclic `W = W₁ × W₂` is a TI-subset with
normalizer-bound `W`** — the abstract core of Peterfalvi's `V`-set TI property, generalising
`S12.typePData_V_ti` to take the singleton/subset normalizer fact `N_G(X) = W` (`hnorm`) directly.
Given `g` conjugating some `a` of the set into it, `N_G({a}) = W = N_G({g a g⁻¹})` forces `g` to
normalize `W`, and cyclic-uniqueness (`cyclic_subgroup_eq_of_card_eq`) makes `W₁`, `W₂`
`g`-stable, so `g` normalizes the set, whence `g ∈ N_G(set) = W`.  The `W`-orbit TI input to the
(14.11.4) §8 count (`hnorm` is the genuine §13 structural fact, supplied from the partner type-`P`
structure). -/
theorem isTISubset_sdiff_sup_of_normalizer_eq [Finite G] {W W1 W2 : Subgroup G}
    (hWcyc : IsCyclic ↥W) (hWeq : W = W1 ⊔ W2)
    (hnorm : ∀ X : Set G, X.Nonempty →
      X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W) :
    OddOrder.GroupTheory.IsTISubset ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) W := by
  classical
  set vset : Set G := (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) with hvset
  haveI : IsCyclic ↥W := hWcyc
  have hW1le : W1 ≤ W := hWeq ▸ le_sup_left
  have hW2le : W2 ≤ W := hWeq ▸ le_sup_right
  have mem_norm_sing : ∀ c z : G,
      z ∈ Subgroup.normalizer ({c} : Set G) ↔ z * c * z⁻¹ = c := by
    intro c z
    rw [Subgroup.mem_set_normalizer_iff]
    constructor
    · intro hz; have := (hz c).mp rfl; simpa using this
    · intro hz h
      simp only [Set.mem_singleton_iff]
      refine ⟨fun hrfl => hrfl ▸ hz, fun hh => ?_⟩
      have hcc : z * h * z⁻¹ = z * c * z⁻¹ := by rw [hh, hz]
      exact mul_left_cancel (mul_right_cancel hcc)
  intro g hg
  obtain ⟨a, haV, hbV⟩ := hg
  have hNa : Subgroup.normalizer ({a} : Set G) = W :=
    hnorm {a} (Set.singleton_nonempty a) (Set.singleton_subset_iff.mpr haV)
  have hNb : Subgroup.normalizer ({g * a * g⁻¹} : Set G) = W :=
    hnorm {g * a * g⁻¹} (Set.singleton_nonempty _) (Set.singleton_subset_iff.mpr hbV)
  have hgW : ∀ h, h ∈ W ↔ g * h * g⁻¹ ∈ W := by
    intro h
    have e1 : (h ∈ W) ↔ h * a * h⁻¹ = a := by rw [← hNa, mem_norm_sing]
    have e2 : (g * h * g⁻¹ ∈ W) ↔ h * a * h⁻¹ = a := by
      rw [← hNb, mem_norm_sing]
      have hexp : g * h * g⁻¹ * (g * a * g⁻¹) * (g * h * g⁻¹)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ := by
        group
      rw [hexp]
      exact ⟨fun hh => mul_left_cancel (mul_right_cancel hh), fun hh => by rw [hh]⟩
    rw [e1, e2]
  have hstab : ∀ (A : Subgroup G), A ≤ W → ∀ x : G, g * x * g⁻¹ ∈ A ↔ x ∈ A := by
    intro A hAW
    have hmap_le : A.map (MulAut.conj g).toMonoidHom ≤ W := by
      rintro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hzA, rfl⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (hgW z).mp (hAW hzA)
    have hcard : Nat.card ↥(A.map (MulAut.conj g).toMonoidHom) = Nat.card ↥A :=
      (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv).symm
    have hsubeq : (A.map (MulAut.conj g).toMonoidHom).subgroupOf W = A.subgroupOf W := by
      apply OddOrder.BG.Ch3.S10.cyclic_subgroup_eq_of_card_eq (C := ↥W)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmap_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv, hcard]
    have hmapeq : A.map (MulAut.conj g).toMonoidHom = A := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hmap_le, hsubeq,
        Subgroup.map_subgroupOf_eq_of_le hAW]
    intro x
    constructor
    · intro hx
      have hmem : g * x * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := by rw [hmapeq]; exact hx
      rw [Subgroup.mem_map] at hmem
      obtain ⟨z, hzA, hz⟩ := hmem
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hz
      have hzx : z = x := mul_left_cancel (mul_right_cancel hz)
      rwa [hzx] at hzA
    · intro hx
      have hmem : (MulAut.conj g).toMonoidHom x ∈ A.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hmapeq] at hmem
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
  rw [← hnorm vset ⟨a, haV⟩ Set.Subset.rfl, Subgroup.mem_set_normalizer_iff]
  intro h
  simp only [hvset, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe]
  rw [hgW h, hstab W1 hW1le h, hstab W2 hW2le h]

/-- **`W` stabilises its exceptional set `W − (W₁ ∪ W₂)` under conjugation** — the `hstab` input to
the `W`-orbit count `ncard_conjClassSet_of_isTISubset`/`orbit_normSq_term`, generalising
`S12.typePData_W_normalizes_typePV`.  Every `l ∈ W = N_G(set)` (via `hnorm`) normalizes the set. -/
theorem conj_smul_sdiff_sup_eq_of_normalizer_eq [Finite G] {W W1 W2 : Subgroup G}
    (hnorm : ∀ X : Set G, X.Nonempty →
      X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W)
    (hne : ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).Nonempty) :
    ∀ l ∈ W, MulAut.conj l • ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)))
      = (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) := by
  intro l hl
  have hlN : l ∈ Subgroup.normalizer ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) := by
    rw [hnorm _ hne Set.Subset.rfl]; exact hl
  rw [Subgroup.mem_set_normalizer_iff] at hlN
  ext x
  simp only [Set.mem_smul_set, MulAut.smul_def, MulAut.conj_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact (hlN v).mp hv
  · intro hx
    refine ⟨l⁻¹ * x * l, (hlN _).mpr ?_, by group⟩
    rw [show l * (l⁻¹ * x * l) * l⁻¹ = x by group]; exact hx

/-- **Orbit measure of a TI-subset** `|𝒞_G(A)|/|G| = |A|/|N|` — the real-valued form of the §8
TI-counting `ncard_conjClassSet_of_isTISubset` (`|𝒞_G(A)| = |A|·[G:N]`).  For a TI-subset `A` with
normalizer-bound `N` stabilizing `A`, the conjugacy-saturation `𝒞_G(A) = A^G` has relative measure
`|A|/|N|` in `G`.  The reusable bridge turning each (14.11.4) orbit `(W#)^G`/`(P#)^G`/`(Q#)^G` into
a
`1/|N_G(·)|`-term (Pf 04.16 lines 109–115). -/
theorem orbit_normSq_term [Finite G] {A : Set G} {L : Subgroup G}
    (hTI : OddOrder.GroupTheory.IsTISubset A L)
    (hstab : ∀ l ∈ L, MulAut.conj l • A = A) :
    ((OddOrder.GroupTheory.conjClassSet A).ncard : ℝ) / (Nat.card G : ℝ)
      = (A.ncard : ℝ) / (Nat.card ↥L : ℝ) := by
  rw [OddOrder.BG.Ch4.S14.ncard_conjClassSet_of_isTISubset hTI hstab, ← L.card_mul_index]
  have hidx : (L.index : ℝ) ≠ 0 := by exact_mod_cast Subgroup.index_ne_zero_of_finite
  push_cast
  rw [mul_div_mul_right _ _ hidx]

/-- **`W`-orbit relative measure** `|(W − (W₁ ∪ W₂))^G|/|G| = |W − (W₁ ∪ W₂)|/|W|` — the assembled
`W`-orbit term of Peterfalvi (14.11.4), combining the TI core
(`isTISubset_sdiff_sup_of_normalizer_eq`), the `W`-stability
(`conj_smul_sdiff_sup_eq_of_normalizer_eq`), and the orbit bridge (`orbit_normSq_term`).  Given the
cyclic structure `W = W₁ × W₂` and the singleton/subset normalizer fact `N_G(X) = W` (`hnorm`). -/
theorem orbit_sdiff_sup_normSq_term [Finite G] {W W1 W2 : Subgroup G}
    (hWcyc : IsCyclic ↥W) (hWeq : W = W1 ⊔ W2)
    (hnorm : ∀ X : Set G, X.Nonempty →
      X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W)
    (hne : ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).Nonempty) :
    ((OddOrder.GroupTheory.conjClassSet
        ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)))).ncard : ℝ) / (Nat.card G : ℝ)
      = (((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).ncard : ℝ) / (Nat.card ↥W : ℝ) :=
  orbit_normSq_term (isTISubset_sdiff_sup_of_normalizer_eq hWcyc hWeq hnorm)
    (conj_smul_sdiff_sup_eq_of_normalizer_eq hnorm hne)

/-- **The normalizer of `P` stabilises `P# = P ∖ {1}` under conjugation** — the `hstab` input to the
`P#`-orbit count `orbit_normSq_term`.  For `l ∈ N_G(P)`, conjugation by `l` permutes `P` and fixes
`1`, so it permutes `P#`.  (With `IsTI P` — definitionally `IsTISubset (P ∖ {1}) (N_G(P))` — this
gives `|(P#)^G|/|G| = (|P|−1)/|N_G(P)|`, the `P`/`Q` orbit terms of Peterfalvi (14.11.4).) -/
theorem conj_smul_sharpSubgroup_eq_of_mem_normalizer {P : Subgroup G} {l : G}
    (hl : l ∈ Subgroup.normalizer (P : Set G)) :
    MulAut.conj l • (OddOrder.GroupTheory.sharpSubgroup P)
      = OddOrder.GroupTheory.sharpSubgroup P := by
  rw [Subgroup.mem_set_normalizer_iff] at hl
  ext x
  simp only [Set.mem_smul_set, MulAut.smul_def, MulAut.conj_apply,
    OddOrder.GroupTheory.sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, ⟨hvP, hv1⟩, rfl⟩
    refine ⟨(hl v).mp hvP, fun h => hv1 ?_⟩
    have : v = l⁻¹ * (l * v * l⁻¹) * l := by group
    rw [this, h]; group
  · rintro ⟨hxP, hx1⟩
    refine ⟨l⁻¹ * x * l, ⟨(hl _).mpr ?_, fun h => hx1 ?_⟩, by group⟩
    · rw [show l * (l⁻¹ * x * l) * l⁻¹ = x by group]; exact hxP
    · rw [show x = l * (l⁻¹ * x * l) * l⁻¹ by group, h]; group

/-- **`P#`-orbit relative measure** `|(P#)^G|/|G| = |P#|/|N_G(P)|` — the `P`/`Q` orbit term of
Peterfalvi (14.11.4), for a TI-subgroup `P` (`Subgroup.IsTI P`, definitionally
`IsTISubset (P ∖ {1}) (N_G(P))`).  Combines the TI property with the `P#`-stability
(`conj_smul_sharpSubgroup_eq_of_mem_normalizer`) via the orbit bridge `orbit_normSq_term`. -/
theorem orbit_sharpSubgroup_normSq_term [Finite G] {P : Subgroup G} (hTI : Subgroup.IsTI P) :
    ((OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup P)).ncard : ℝ)
        / (Nat.card G : ℝ)
      = ((OddOrder.GroupTheory.sharpSubgroup P).ncard : ℝ)
        / (Nat.card ↥(Subgroup.normalizer (P : Set G)) : ℝ) :=
  orbit_normSq_term hTI (fun _ hl => conj_smul_sharpSubgroup_eq_of_mem_normalizer hl)

/-- **`|P#| + 1 = |P|`** — the cardinality of the sharp subgroup (the `|P| − 1` numerator of the
`P`/`Q` orbit term of (14.11.4)), additive form. -/
theorem ncard_sharpSubgroup_add_one {P : Subgroup G} [Finite ↥P] :
    (OddOrder.GroupTheory.sharpSubgroup P).ncard + 1 = Nat.card ↥P := by
  have hc : Nat.card ↥P = (P : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  rw [hc, OddOrder.GroupTheory.sharpSubgroup, ← Set.ncard_singleton (1 : G),
    Set.ncard_sdiff_add_ncard_of_subset (Set.singleton_subset_iff.mpr P.one_mem)]

/-- **`|W − (W₁ ∪ W₂)| + |W₁| + |W₂| = |W| + 1`** — the cardinality of the exceptional set, by
inclusion–exclusion with `W₁ ∩ W₂ = {1}` (`hdisj`).  The numerator of the `W`-orbit term
`|W − (W₁ ∪ W₂)|/|W|` of Peterfalvi (14.11.4) (additive form, avoiding `ℕ`-truncation). -/
theorem ncard_sdiff_sup_add_eq [Finite G] {W W1 W2 : Subgroup G}
    (hW1le : W1 ≤ W) (hW2le : W2 ≤ W) (hdisj : W1 ⊓ W2 = ⊥) :
    ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).ncard + Nat.card ↥W1 + Nat.card ↥W2
      = Nat.card ↥W + 1 := by
  have hsub : ((W1 : Set G) ∪ (W2 : Set G)) ⊆ (W : Set G) :=
    Set.union_subset (SetLike.coe_subset_coe.mpr hW1le) (SetLike.coe_subset_coe.mpr hW2le)
  have h1 := Set.ncard_sdiff_add_ncard_of_subset hsub
  have h2 := Set.ncard_union_add_ncard_inter (W1 : Set G) (W2 : Set G)
  have h3 : ((W1 : Set G) ∩ (W2 : Set G)).ncard = 1 := by
    rw [← Subgroup.coe_inf, hdisj, Subgroup.coe_bot, Set.ncard_singleton]
  have hcW : Nat.card ↥W = (W : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  have hcW1 : Nat.card ↥W1 = (W1 : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  have hcW2 : Nat.card ↥W2 = (W2 : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  rw [hcW, hcW1, hcW2]
  omega

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4), the `G₀`-drop set reduction** — `|famG₀| − |G₀| ≤ |(W−(W₁∪W₂))^G| +
|(P#)^G| + |(Q#)^G|` (as `ncard`s).  Since `G₀ ⊆ famG₀` (`G0_off_dadeSupport`) and `famG₀ ∖ G₀` is
covered by the three orbits (`G0_orbit_cover`, the (14.11.3) `G₀ = G − [Ã(M) ∪ orbits]`), the
difference is bounded by the orbit cardinalities (`Set.ncard_sdiff` + `Set.ncard_union_le`).  The
set-theoretic core of the (14.11.4) §8 TI-counting, feeding `orbit_normSq_term` per orbit. -/
theorem MHypothesis.famG0_sub_filter_card_le_orbit_ncard [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    (Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
        - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
      ≤ ((OddOrder.GroupTheory.conjClassSet
            ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))).ncard : ℝ)
        + ((OddOrder.GroupTheory.conjClassSet
            (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)).ncard : ℝ)
        + ((OddOrder.GroupTheory.conjClassSet
            (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)).ncard : ℝ) := by
  classical
  haveI := Mdata.finiteG
  set famG0 := (Mdata.toFamilyHypothesis71).G0 with hfamdef
  set Worb := OddOrder.GroupTheory.conjClassSet
    ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
  set Porb := OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)
  set Qorb := OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)
  -- `g ∈ famG₀ ↔ g ∉ Ã(M)` (single-member family).
  have hmemfam : ∀ g : G, g ∈ famG0 ↔ g ∉ Mdata.typeIHyp.dadeData.dade.dadeSupport := by
    intro g
    refine ⟨fun hg => hg 0, fun hg i => ?_⟩
    fin_cases i; exact hg
  -- `G₀ ⊆ famG₀` and `famG₀ ∖ G₀ ⊆ orbits`.
  have hsub : Mdata.G0 ⊆ famG0 := fun g hg => (hmemfam g).mpr (Mdata.G0_off_dadeSupport g hg)
  have hcover : famG0 \ Mdata.G0 ⊆ Worb ∪ Porb ∪ Qorb := by
    rintro g ⟨hgfam, hgG0⟩
    exact Mdata.G0_orbit_cover g ((hmemfam g).mp hgfam) hgG0
  -- ncard reduction.
  have hdiff : (famG0 \ Mdata.G0).ncard ≤ Worb.ncard + Porb.ncard + Qorb.ncard :=
    le_trans (Set.ncard_le_ncard hcover)
      (le_trans (Set.ncard_union_le _ _) (by gcongr; exact Set.ncard_union_le _ _))
  have hdeq : (famG0 \ Mdata.G0).ncard = famG0.ncard - Mdata.G0.ncard := Set.ncard_sdiff hsub
  have hG0le : Mdata.G0.ncard ≤ famG0.ncard := Set.ncard_le_ncard hsub
  -- `Nat.card famG₀ = famG₀.ncard`, `|filter| = G₀.ncard`.
  have hfamcard : Nat.card famG0 = famG0.ncard := Nat.card_coe_set_eq famG0
  have hfiltcard : (Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card = Mdata.G0.ncard := by
    rw [Set.ncard_eq_toFinset_card']; congr 1; ext g; simp
  rw [hfamcard, hfiltcard]
  have hcast : (famG0.ncard : ℝ) - (Mdata.G0.ncard : ℝ)
      = ((famG0.ncard - Mdata.G0.ncard : ℕ) : ℝ) := (Nat.cast_sub hG0le).symm
  rw [hcast, ← hdeq]
  calc ((famG0 \ Mdata.G0).ncard : ℝ) ≤ ((Worb.ncard + Porb.ncard + Qorb.ncard : ℕ) : ℝ) := by
        exact_mod_cast hdiff
    _ = (Worb.ncard : ℝ) + (Porb.ncard : ℝ) + (Qorb.ncard : ℝ) := by push_cast; ring

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4), the upper-bound §8 TI-counting step** (04.16 lines 109–115).  Brings the
line-83 bound `|A(M)|/|M| + (1/|G|)(|famG₀| − |G₀|)` (`chiRhoNormSq_psi_le_line83`, proven) up to
the displayed `NormCascadeData.upper`.  The genuine §8 content: `|A(M)|/|M| = (k−1)/(kpq)`
(`card_typeIA_eq`/`card_M_eq`); the `G₀`-drop `famG0_sub_filter_card_le_orbit_ncard` (set-reduction,
proven) plus the orbit measures (`orbit_sdiff_sup_normSq_term`/`orbit_sharpSubgroup_normSq_term`)
and the structural values (`|W|`/`|N_G(P)|`, `IsTI P`/`IsTI Q`, `normalizer_V`) bound the orbits,
then `normCascade_upper_loosen`.  The remaining §8 structural input is the TI/normalizer data of the
Frobenius pieces `W`, `P`, `Q` (the type-I analogue of S12 (10.8)'s `G₁ ⊆ (H#)^G ∪ V^G`). -/
theorem MHypothesis.line83_le_displayed_upper [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) (hepq : Mdata.e = hyp.base.p * hyp.base.q) :
    (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
        / (Nat.card ↥Mdata.M : ℝ)
      + (Nat.card G : ℝ)⁻¹ * ((Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
        - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ))
      ≤ 1 - (1 : ℝ) / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
        + 2 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ)
        + 1 / ((hyp.base.u * hyp.base.q : ℕ) : ℝ)
        + 1 / ((hyp.base.v * hyp.base.p : ℕ) : ℝ) := by
  haveI := Mdata.finiteG
  -- abbreviations
  have hW1le : hyp.base.W1 ≤ hyp.base.W := hyp.base.W_eq_join ▸ le_sup_left
  have hW2le : hyp.base.W2 ≤ hyp.base.W := hyp.base.W_eq_join ▸ le_sup_right
  -- positivity (`p`, `q` prime; `u`, `v` from the faithful normalizer carriers; `k`/cards `> 0`).
  have hp : (0 : ℝ) < hyp.base.p := by exact_mod_cast hyp.base.p_prime.pos
  have hq : (0 : ℝ) < hyp.base.q := by exact_mod_cast hyp.base.q_prime.pos
  have hkpos : 0 < Mdata.k := Mdata.k_eq_card_K ▸ Nat.card_pos
  have hPpos : 0 < Nat.card ↥hyp.base.P := Nat.card_pos
  have hQpos : 0 < Nat.card ↥hyp.base.Q := Nat.card_pos
  have hNPpos : 0 < Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G)) := Nat.card_pos
  have hNQpos : 0 < Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G)) := Nat.card_pos
  have hupos : 0 < hyp.base.u := by
    by_contra hc
    have hu0 : hyp.base.u = 0 := Nat.le_zero.mp (not_lt.mp hc)
    have : Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G)) = 0 := by
      rw [Mdata.card_normalizer_P_eq, hu0, mul_zero, zero_mul]
    omega
  have hvpos : 0 < hyp.base.v := by
    by_contra hc
    have hv0 : hyp.base.v = 0 := Nat.le_zero.mp (not_lt.mp hc)
    have : Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G)) = 0 := by
      rw [Mdata.card_normalizer_Q_eq, hv0, mul_zero, zero_mul]
    omega
  -- orbit measures (equalities).
  have hWm := orbit_sdiff_sup_normSq_term hyp.base.W_cyclic hyp.base.W_eq_join
    Mdata.W_normalizer_V (S15.W_sdiff_nonempty hyp.base)
  have hPm := orbit_sharpSubgroup_normSq_term Mdata.P_isTI
  have hQm := orbit_sharpSubgroup_normSq_term Mdata.Q_isTI
  -- cardinalities of the supports.
  have hWc := ncard_sdiff_sup_add_eq hW1le hW2le hyp.base.W1_inf_W2_eq_bot
  have hPc := ncard_sharpSubgroup_add_one (P := hyp.base.P)
  have hQc := ncard_sharpSubgroup_add_one (P := hyp.base.Q)
  -- `|W-set| = pq + 1 − (p+q)`, `|N_G(P)| = |P| u q`, etc. (`ℕ`-level facts → `ℝ`).
  have hWsetR : (((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))).ncard : ℝ)
      = (hyp.base.p : ℝ) * hyp.base.q + 1 - hyp.base.p - hyp.base.q := by
    have : ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))).ncard
        + (hyp.base.p + hyp.base.q) = hyp.base.p * hyp.base.q + 1 := by
      rw [← S15.card_W1_add_W2 hyp.base,
        ← S15.card_W_eq_pq hyp.base]
      omega
    have hR : (((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))).ncard : ℝ)
        + ((hyp.base.p : ℝ) + hyp.base.q) = (hyp.base.p : ℝ) * hyp.base.q + 1 := by
      exact_mod_cast this
    linarith
  -- the three orbit-term values (equalities).
  have hWterm : (OddOrder.GroupTheory.conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))).ncard
        / (Nat.card G : ℝ)
      = 1 - 1 / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
        + 1 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ) := by
    rw [hWm, hWsetR]
    have hWcardR : (Nat.card ↥hyp.base.W : ℝ) = (hyp.base.p : ℝ) * hyp.base.q := by
      rw [S15.card_W_eq_pq hyp.base]; push_cast; ring
    rw [hWcardR]; push_cast; field_simp; ring
  have hPterm : (OddOrder.GroupTheory.conjClassSet
        (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)).ncard / (Nat.card G : ℝ)
      = ((Nat.card ↥hyp.base.P : ℝ) - 1)
        / ((Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q : ℕ) : ℝ) := by
    rw [hPm]
    have hsharpR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.P).ncard : ℝ)
        = (Nat.card ↥hyp.base.P : ℝ) - 1 := by
      have hR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.P).ncard : ℝ) + 1
          = (Nat.card ↥hyp.base.P : ℝ) := by exact_mod_cast hPc
      linarith
    rw [hsharpR, Mdata.card_normalizer_P_eq]
  have hQterm : (OddOrder.GroupTheory.conjClassSet
        (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)).ncard / (Nat.card G : ℝ)
      = ((Nat.card ↥hyp.base.Q : ℝ) - 1)
        / ((Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p : ℕ) : ℝ) := by
    rw [hQm]
    have hsharpR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.Q).ncard : ℝ)
        = (Nat.card ↥hyp.base.Q : ℝ) - 1 := by
      have hR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.Q).ncard : ℝ) + 1
          = (Nat.card ↥hyp.base.Q : ℝ) := by exact_mod_cast hQc
      linarith
    rw [hsharpR, Mdata.card_normalizer_Q_eq]
  -- `|A(M)|/|M| = (k−1)/(kpq)`.
  have hAterm : (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
        / (Nat.card ↥Mdata.M : ℝ)
      = ((Mdata.k : ℝ) - 1) / ((Mdata.k * hyp.base.p * hyp.base.q : ℕ) : ℝ) := by
    rw [Mdata.card_typeIA_eq hG hnoV, Mdata.card_M_eq, hepq]
    have hkR : ((Mdata.k - 1 : ℕ) : ℝ) = (Mdata.k : ℝ) - 1 := by
      have : 1 ≤ Mdata.k := hkpos
      push_cast [Nat.cast_sub this]; ring
    rw [hkR]; push_cast; ring
  -- the `G₀`-drop, scaled by `1/|G|`.
  have hGinv : (0 : ℝ) ≤ (Nat.card G : ℝ)⁻¹ := by positivity
  have hdrop := mul_le_mul_of_nonneg_left Mdata.famG0_sub_filter_card_le_orbit_ncard hGinv
  -- `(1/|G|)·Σ ncard = Σ (ncard/|G|) = hWterm + hPterm + hQterm`.
  have hsum : (Nat.card G : ℝ)⁻¹ * (((OddOrder.GroupTheory.conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))).ncard : ℝ)
      + ((OddOrder.GroupTheory.conjClassSet
          (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)).ncard : ℝ)
      + ((OddOrder.GroupTheory.conjClassSet
          (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)).ncard : ℝ))
      = (1 - 1 / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ) + 1 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ))
        + ((Nat.card ↥hyp.base.P : ℝ) - 1)
            / ((Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q : ℕ) : ℝ)
        + ((Nat.card ↥hyp.base.Q : ℝ) - 1)
            / ((Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p : ℕ) : ℝ) := by
    rw [← hWterm, ← hPterm, ← hQterm]; ring
  -- assemble: `line83-RHS ≤ raw bound`.
  have hraw : (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
        / (Nat.card ↥Mdata.M : ℝ)
      + (Nat.card G : ℝ)⁻¹ * ((Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
        - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ))
      ≤ 1 - 1 / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
          + 1 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ)
        + ((Nat.card ↥hyp.base.P : ℝ) - 1)
            / ((Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q : ℕ) : ℝ)
        + ((Nat.card ↥hyp.base.Q : ℝ) - 1)
            / ((Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p : ℕ) : ℝ)
        + ((Mdata.k : ℝ) - 1) / ((Mdata.k * hyp.base.p * hyp.base.q : ℕ) : ℝ) := by
    rw [hAterm]; rw [hsum] at hdrop; linarith
  -- loosen the raw bound to the displayed one.
  exact le_trans hraw (normCascade_upper_loosen hyp.base.p_prime.pos hyp.base.q_prime.pos
    hupos hvpos hkpos hPpos hQpos)

/-- **Faithful §7 carrier for the `ρ`-norm two-sided bound of Peterfalvi (14.11.4).**

The character theory of (14.11.4) reduces to a two-sided bound on `‖ψ^{τ₁ρ}‖²`, where `ρ` is the
Hypothesis (7.1) map for `(M, A(M))` (Pf (14.11.4), p.90):

* `lower` — **(7.8.b)** (Pf 04.16 line 113): the §7 coherence-norm formula `‖ζ^{νρ}‖² ≥ 1 − e/h`
  for the coherent type-I `M` (with `e = |M:K| = pq`, `h = |K| = k`) gives `1 − pq/k ≤ ‖ψ^{τ₁ρ}‖²`.
  **Proven** (`MHypothesis.rhoNormSq_ge_lower`), via the `h78` coherence carrier and the norm bridge
  `chiRhoNormSq_eq_zetaNuRhoNormSq`.
* `upper` — **(7.5) + (14.11.3) + §8 TI-counting**: the (7.5) family inequality applied to the
  norm-one `ψ^{τ₁}`, dropping the `G_0`-part via `|ψ^{τ₁}(g)| ≥ 1` (`generic_character_bound`,
  14.11.3) to line 83 (`chiRhoNormSq_psi_le_line83`), then the §8 TI-counting of the
  `(W#)^G`/`(P#)^G`/`(Q#)^G` orbit contributions giving the raw estimate, loosened by
  `(|P|−1)/|P| ≤ 1`, `(|Q|−1)/|Q| ≤ 1`, `(k−1)/k ≤ 1` (`normCascade_upper_loosen`) to the
  `normCascadeBound` error terms `2/(pq) + 1/(uq) + 1/(vp)`.

The two-sided structure mirrors the textbook's two-step derivation; the `lower` (7.8.b) bound is
proven, and the remaining genuine obligation is the upper §8 TI-counting, isolated in
`normCascadeData`. -/
structure NormCascadeData (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) where
  /-- `‖ψ^{τ₁ρ}‖²`, the squared `L`-norm of the Hypothesis (7.1) `ρ`-image of `ψ^{τ₁}`.
  Real-valued (matching `S09.FamilyHypothesis71.chiRhoNormSq : ℝ`), so the (7.5)/(7.8.b)
  derivation lives in `ℝ`; the passage to the rational `normCascadeBound` is a final cast. -/
  rhoNormSq : ℝ
  /-- **(7.8.b)** lower bound: `1 − pq/k ≤ ‖ψ^{τ₁ρ}‖²`
  (proven, `MHypothesis.rhoNormSq_ge_lower`). -/
  lower :
    (1 : ℝ) - ((hyp.base.p * hyp.base.q : ℕ) : ℝ) / (Mdata.k : ℝ) ≤ rhoNormSq
  /-- **(7.5) + (14.11.3) + §8 TI-counting** upper bound (loosened to the `normCascadeBound`
  error terms). -/
  upper :
    rhoNormSq ≤ 1 - (1 : ℝ) / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
      + 2 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ)
      + 1 / ((hyp.base.u * hyp.base.q : ℕ) : ℝ)
      + 1 / ((hyp.base.v * hyp.base.p : ℕ) : ℝ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §7 Dade producer for (14.11.4).**  The `ρ`-norm is the concrete family-inequality
norm `(toFamilyHypothesis71).chiRhoNormSq (ψ^{τ₁}) 0` for the `(M, A(M))` map `ρ`.

* `lower` uses the **proven** unconditional estimate `1 − e/k ≤ ‖ψ^{τ₁ρ}‖²`
  (`MHypothesis.rhoNormSq_ge_lower`, via `h78` and `chiRhoNormSq_eq_zetaNuRhoNormSq`) and rewrites
  `e = p q` only after the conditional (14.11.2) producer.
* `upper` is the remaining genuine obligation: the **§8 TI-counting** of the `(W#)^G`/`(P#)^G`/
  `(Q#)^G` orbit contributions that turns the line-83 bound (`chiRhoNormSq_psi_le_line83`, proven)
  into the raw estimate, which `normCascade_upper_loosen` (proven) then loosens to the displayed
  `normCascadeBound` error terms.  Both arithmetic ends of `upper` are honest; the gap is the §8
  orbit cardinality `|K#|/|M|`, `|(W#)^G|`/`|(P#)^G|`/`|(Q#)^G|` count. -/
noncomputable def normCascadeData [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    NormCascadeData hyp Mdata := by
  have hepq := (betaM_expansion _hG hnoV hncH0C hyp Mdata hne).1
  refine {
    rhoNormSq := (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0
    lower := ?_
    upper := ?_
  }
  · rw [← hepq]
    exact Mdata.rhoNormSq_ge_lower
  · -- line-83 (`chiRhoNormSq_psi_le_line83`, proven) chained with the §8 TI-counting step
    -- (`line83_le_displayed_upper`, the single remaining gate).
    exact le_trans (Mdata.chiRhoNormSq_psi_le_line83 _hG hnoV hncH0C hne)
      (Mdata.line83_le_displayed_upper _hG hnoV hepq)

/-- **Peterfalvi (14.11.4)**: the character-theoretic norm calculation produces the displayed
rational inequality `normCascadeBound hyp k`.

De-opacified (W4 §16→§7 bridge, lane-h): the genuine character theory is the two-sided `ρ`-norm
bound `NormCascadeData` (the (7.5) family inequality + (14.11.3)/(7.8.b) norm estimates); the
passage to `normCascadeBound` is then the pure rational rearrangement
`1 − pq/k ≤ ‖ψ^{τ₁ρ}‖² ≤ 1 − 1/p − 1/q + 2/(pq) + 1/(uq) + 1/(vp)` ⟹
`1/p + 1/q ≤ pq/k + 2/(pq) + 1/(uq) + 1/(vp)` (`linarith`).  Everything downstream of
`normCascadeBound` is the arithmetic cascade already discharged in `norm_cascade_contradiction`. -/
theorem normCascadeBound_of_charData [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    normCascadeBound hyp Mdata.k := by
  obtain ⟨R, hlower, hupper⟩ := normCascadeData _hG hnoV hncH0C hyp Mdata hne
  unfold normCascadeBound
  -- The two-sided `ℝ` bound `1 − pq/k ≤ R ≤ 1 − 1/p − 1/q + 2/(pq) + 1/(uq) + 1/(vp)` gives the
  -- displayed rational inequality; lift the `ℚ` goal to `ℝ` and close by `linarith`.
  rw [← Rat.cast_le (K := ℝ)]
  push_cast at hlower hupper ⊢
  linarith [hlower, hupper]

/-- **Peterfalvi (14.11.4)**: the norm inequality cascade contradicts `K != V`.

This is now a transparent composition rather than an opaque obligation: the
case-(9.7.b) outputs of `caseB_for_T` (14.4) and `caseB_for_S` (14.6) supply the
T-side/S-side cyclotomic size data, `main_size_bounds` (14.11.1) supplies
`k > 2 p v`, and `normCascadeBound_of_charData` (14.11.2)--(14.11.3) supplies the
displayed norm inequality.  The arithmetic consumer
`norm_cascade_contradiction_of_caseB_outputs_main_size_bounds` then closes the
cascade.  The only remaining genuine `sorry`s are the named producers above. -/
theorem contradiction_of_K_ne_V [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    False :=
  norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
    (caseB_for_T _hG hyp) (caseB_for_S _hG hyp Ldata) Mdata
    (main_size_bounds _hG hnoV hncH0C hyp Mdata hne)
    (normCascadeBound_of_charData _hG hnoV hncH0C hyp Mdata hne)

/-- **Peterfalvi (13.17.c)-dual specialised in the §14 context.**  Once `K = V`, the
alternative complement branch `e = p` is excluded by (14.9), leaving `e = p q`.

This is the second named hand-off boundary from issue 3004.  It deliberately depends on the
proved kernel equality instead of restoring an unconditional `e = p q` field on
`MHypothesis`. -/
theorem MHypothesis.complementIndex_eq_pq_of_K_eq_V [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) (_hKV : Mdata.K = hyp.base.V)
    (_hcases : Mdata.e = hyp.base.p ∨ Mdata.e = hyp.base.p * hyp.base.q) :
    Mdata.e = hyp.base.p * hyp.base.q := by
  classical
  rcases _hcases with hp | hpq
  · exfalso
    have hMI : IsTypeI Mdata.M := ⟨Mdata.typeIHyp.typeI⟩
    obtain ⟨frob, _hker, hW2E⟩ :=
      OddOrder.Peterfalvi.S15.exists_typeIFrobeniusData_W2_le
        _hG hnoV hyp.base Mdata.M_maximal hMI Mdata.normalizer_V_le_M
    have hEcard : Nat.card ↥(frob.complement.map Mdata.M.subtype) =
        Nat.card ↥frob.complement :=
      Subgroup.card_map_of_injective (K := frob.complement) Mdata.M.subtype_injective
    have hCcard : Nat.card ↥frob.complement = Mdata.e := by
      rw [← OddOrder.Peterfalvi.S15.typeIFrobenius_kernel_index_eq_complement frob,
        ← Mdata.K_eq_MF, ← Mdata.e_eq_index]
    have hEW2 : frob.complement.map Mdata.M.subtype = hyp.base.W2 := by
      apply Eq.symm
      apply Subgroup.eq_of_le_of_card_ge hW2E
      rw [hEcard, hCcard, hp, hyp.base.p_eq_card_W2]
    have hH_V : frob.typeI.typeF.H = hyp.base.V := by
      rw [frob.typeI.typeF.H_eq, ← Mdata.K_eq_MF, _hKV]
    have hdecomp :
        frob.typeI.typeF.H ⊔ frob.complement.map Mdata.M.subtype = Mdata.M := by
      have hmap := congrArg (Subgroup.map Mdata.M.subtype)
        frob.frobenius.isComplement.sup_eq_top
      rwa [Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le frob.typeI.typeF.H_le,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    have hM_eq : Mdata.M = hyp.base.V ⊔ hyp.base.W2 := by
      rw [hH_V, hEW2] at hdecomp
      exact hdecomp.symm
    have hVleT : hyp.base.V ≤ hyp.base.T :=
      (le_sup_right.trans hyp.base.T_deriv_eq_QV.ge).trans (Subgroup.map_subtype_le _)
    have hW2leW : hyp.base.W2 ≤ hyp.base.W := by
      rw [hyp.base.W_eq_join]
      exact le_sup_right
    have hWleT : hyp.base.W ≤ hyp.base.T := by
      rw [hyp.base.W_eq_inter]
      exact inf_le_right
    have hMleT : Mdata.M ≤ hyp.base.T := by
      rw [hM_eq]
      exact sup_le hVleT (hW2leW.trans hWleT)
    obtain ⟨tdata⟩ := T_typeII _hG hnoV hncH0C hyp
    have hcop := OddOrder.Peterfalvi.S15.coprime_card_V_card_Q_of_disjoint
      hyp.base tdata hyp.base.Q_inf_V_eq_bot
    have hNVT : ¬ Subgroup.normalizer (hyp.base.V : Set G) ≤ hyp.base.T :=
      OddOrder.Peterfalvi.S15.not_normalizer_V_le_T _hG hyp.base tdata
        (OddOrder.Peterfalvi.S15.exists_conj_typeP_V_of_coprime
          _hG hyp.base tdata hcop)
    exact hNVT (Mdata.normalizer_V_le_M.trans hMleT)
  · exact hpq

/-- **Peterfalvi (14.11)**: `K = V` and `|M : K| = p q`.

The `K = V` half is now a genuine consequence of the (14.11.1)--(14.11.4)
contradiction: assuming `K ≠ V` invokes `contradiction_of_K_ne_V`.  The index
computation `|M : K| = p q` (here `Mdata.e = p q`) is the remaining genuine
obligation; note `betaM_expansion`'s `e = p q` is unavailable here because it
is conditioned on `K ≠ V`, so the equal-index value under `K = V` needs the
type-I structure of `M` directly. -/
theorem K_eq_V_index_pq [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp) :
    Mdata.K = hyp.base.V ∧ Mdata.e = hyp.base.p * hyp.base.q := by
  have hKV : Mdata.K = hyp.base.V := by
    -- (14.11.1)--(14.11.4): `K ≠ V` is contradictory.
    by_contra hne
    exact contradiction_of_K_ne_V _hG hnoV hncH0C hyp Ldata Mdata hne
  have hcases := Mdata.complementIndex_eq_p_or_pq _hG
  exact ⟨hKV, Mdata.complementIndex_eq_pq_of_K_eq_V _hG hnoV hncH0C hKV hcases⟩

end OddOrder.Peterfalvi.S16
