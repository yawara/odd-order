import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF.Theorem152Helpers

/-!
# BG Corollary 15.5 helpers (§14-independent) + Theorem 15.2 assembly

Split from the former monolithic `OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF` (directory split, issue 0103).
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


/-! ### Corollary 15.5 helpers (`§14`-independent, reusable)

The `F(M) = F(M_σ) × O_{σ'}(F(M))` decomposition splits into two case-independent pieces:
the nilpotent Hall splitting of `F(M)` (`opiCoreInG_sup_compl_eq_of_isNilpotent` applied to the
nilpotent `F(M)`), and the identification `O_σ(F(M)) = F(M_σ)` (`opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma`, BG Corollary 15.5's "Lemma 1").
The `τ₂`/cyclic content of the `σ'`-part is then supplied case by case in `fitting_decomposition`. -/

/-- **Ambient nilpotent Hall splitting**: for a finite nilpotent subgroup `H`, the ambient
realizations of `O_π(H)` and `O_{π'}(H)` join to all of `H`.  (Image under `H.subtype` of the
`↥H`-internal `O_π(↥H) ⊔ O_{π'}(↥H) = ⊤`.)  Combined with `opiCoreInG_commutator_compl_eq_bot`
and `inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl`, this is the direct-product splitting
`H = O_π(H) × O_{π'}(H)` of a nilpotent group into its Hall `π`/`π'` parts. -/
theorem opiCoreInG_sup_compl_eq_of_isNilpotent [Finite G] (π : Set ℕ) {H : Subgroup G}
    [Group.IsNilpotent ↥H] :
    opiCoreInG π H ⊔ opiCoreInG πᶜ H = H := by
  refine le_antisymm (sup_le (opiCoreInG_le π H) (opiCoreInG_le πᶜ H)) ?_
  have htop : (Ch03.oPiCore π ↥H ⊔ Ch03.oPiCore {p | p ∉ π} ↥H).map H.subtype =
      opiCoreInG π H ⊔ opiCoreInG πᶜ H := by
    rw [Subgroup.map_sup]; rfl
  calc H = (⊤ : Subgroup ↥H).map H.subtype := by
            rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ ≤ (Ch03.oPiCore π ↥H ⊔ Ch03.oPiCore {p | p ∉ π} ↥H).map H.subtype :=
        Subgroup.map_mono
          (OddOrder.BG.Ch3.S10.top_le_oPiCore_sup_compl_of_isNilpotent (K := ↥H) π)
    _ = opiCoreInG π H ⊔ opiCoreInG πᶜ H := htop

/-- **Normalizing a subgroup normalizes its centralizer** (`§14`-independent, reusable):
`N_G(H) ≤ N_G(C_G(H))`.  If `g` normalizes `H`, conjugation by `g` permutes the elements of `H`,
hence preserves the set of elements commuting with all of `H`. -/
theorem normalizer_le_normalizer_centralizer (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (Subgroup.centralizer (H : Set G)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ {z : G}, z ∈ Subgroup.normalizer (H : Set G) →
      ∀ c, c ∈ Subgroup.centralizer (H : Set G) → z * c * z⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
    intro z hz c hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : z⁻¹ * x * z ∈ H := (Subgroup.mem_normalizer_iff''.mp hz x).mp hx
    have hcx : (z⁻¹ * x * z) * c = c * (z⁻¹ * x * z) :=
      Subgroup.mem_centralizer_iff.mp hc _ hx'
    calc x * (z * c * z⁻¹) = z * ((z⁻¹ * x * z) * c) * z⁻¹ := by group
      _ = z * (c * (z⁻¹ * x * z)) * z⁻¹ := by rw [hcx]
      _ = (z * c * z⁻¹) * x := by group
  intro c
  refine ⟨fun hc => key hg c hc, fun hc => ?_⟩
  have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normalizer (H : Set G)).inv_mem hg
  have := key hginv (g * c * g⁻¹) hc
  simpa [mul_assoc] using this

/-- **Commuting nilpotent join is nilpotent** (`§14`-independent, reusable): if two subgroups
`A`, `B` are each nilpotent and elementwise commute (`⁅A, B⁆ = ⊥`), then `A ⊔ B` is nilpotent.
The join is the range of the homomorphism `↥A × ↥B → G`, `(a, b) ↦ a · b` (well-defined since
`A`, `B` commute), so it is a quotient image of the nilpotent direct product `↥A × ↥B`. -/
theorem isNilpotent_sup_of_commutator_eq_bot {A B : Subgroup G}
    [Group.IsNilpotent ↥A] [Group.IsNilpotent ↥B] (hcomm : ⁅A, B⁆ = ⊥) :
    Group.IsNilpotent ↥(A ⊔ B) := by
  have hAcB : A ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hcomm' : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) := by
    intro a b
    exact (Subgroup.mem_centralizer_iff.mp (hAcB a.2) (b : G) b.2).symm
  set f : ↥A × ↥B →* G := (A.subtype).noncommCoprod (B.subtype) hcomm' with hf
  have hrange : f.range = A ⊔ B := by
    rw [hf, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  haveI : Group.IsNilpotent ↥(f.range) :=
    Group.nilpotent_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact hrange ▸ this

/-- **`C_Q(D) ⊊ Q` for a non-nilpotent would-be-commuting join** (`§14`-independent, reusable): if
`Q` and `D` are nilpotent but `Q ⊔ D` is not, then `D` does not centralize `Q`, i.e.
`Q ⊓ C_G(D) ≠ Q`.  (Otherwise `Q ≤ C_G(D)` gives `⁅Q, D⁆ = ⊥`, making `Q ⊔ D` nilpotent by
`isNilpotent_sup_of_commutator_eq_bot`.)

In Theorem 15.2's step 3 (mmd L4194) this is `Q₀ = C_Q(D) ⊊ Q` for the `K`-invariant complement
`D` of `Q` in `M_σ` (`Q ⊔ D = M_σ` non-nilpotent, `Q` the `q`-Sylow, `D` nilpotent by
`complement_isNilpotent_of_inputs`): the proper subgroup that starts the minimal-normal `Q̄`
analysis. -/
theorem inf_centralizer_ne_self_of_sup_not_nilpotent {Q D : Subgroup G}
    [Group.IsNilpotent ↥Q] [Group.IsNilpotent ↥D]
    (hnot : ¬ Group.IsNilpotent ↥(Q ⊔ D)) :
    Q ⊓ Subgroup.centralizer (D : Set G) ≠ Q := fun hQ0 =>
  hnot (isNilpotent_sup_of_commutator_eq_bot
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hQ0 ▸ inf_le_right)))

/-- **`Q₀ = C_Q(D)` is `KD`-invariant** (`§14`-independent, reusable): if `K` and `D` each
normalize `Q`, and `K` normalizes `D`, then `K ⊔ D` normalizes `Q ⊓ C_G(D)`.  (`D` always
normalizes its own centralizer and `Q`; `K` normalizes `C_G(D)` because it normalizes `D`
[`normalizer_le_normalizer_centralizer`]; both then normalize the intersection
[`le_normalizer_inf`].)

In Theorem 15.2's step 3 (mmd L4194) this makes `Q₀ = C_Q(D)` a `KD`-invariant subgroup of `Q`,
so that `K` and `D` act on `N_M(Q₀)/Q₀` (whence the minimal normal `Q₁/Q₀`). -/
theorem sup_le_normalizer_centralizer_inf {Q D K : Subgroup G}
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hKD : K ≤ Subgroup.normalizer (D : Set G)) :
    K ⊔ D ≤ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
  sup_le
    (le_normalizer_inf hKQ (hKD.trans (normalizer_le_normalizer_centralizer D)))
    (le_normalizer_inf hDQ (Subgroup.le_normalizer.trans (normalizer_le_normalizer_centralizer D)))

/-- **Normalizers grow in a nilpotent group** (`§14`-independent, reusable): a proper subgroup
`Q₀ < Q` of a nilpotent `Q` is properly contained in its `G`-normalizer, `Q₀ < N_G(Q₀)`.

Inside `↥Q` the proper subgroup `Q₀.subgroupOf Q < ⊤` is properly contained in its normalizer (the
normalizer condition for nilpotent groups, `lt_normalizer_of_isNilpotent_of_lt_top`); transport to
`G` via `subgroupOf_normalizer_eq`.  In Theorem 15.2's step 3 (mmd L4194) this is `N_Q(Q₀) ⊃ Q₀`,
so `N_M(Q₀)/Q₀` is nontrivial and has a minimal normal subgroup `Q₁/Q₀`. -/
theorem lt_normalizer_of_lt_of_isNilpotent {Q Q0 : Subgroup G} [Group.IsNilpotent ↥Q]
    (hQ0Q : Q0 < Q) :
    Q0 < Subgroup.normalizer (Q0 : Set G) := by
  have hQ0le : Q0 ≤ Q := hQ0Q.le
  have hlt : Q0.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top, ne_eq, Subgroup.subgroupOf_eq_top]
    exact hQ0Q.2
  have h := OddOrder.Isaacs.Ch01.lt_normalizer_of_isNilpotent_of_lt_top (G := ↥Q) hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hQ0le] at h
  rw [lt_iff_le_and_ne]
  refine ⟨Subgroup.le_normalizer, fun heq => ?_⟩
  rw [← heq] at h
  exact lt_irrefl _ h

/-- **Strict normalizer growth, intersected form** (`§14`-independent, reusable): for a proper
subgroup `Q0 < Q` of a nilpotent `Q`, a witness normalizing `Q0` lies *inside* `Q`, so
`Q0 < Q ⊓ N_G(Q0) = N_Q(Q0)`.  Sharper than `lt_normalizer_of_lt_of_isNilpotent` (which keeps only
`Q0 < N_G(Q0)`, dropping the `≤ Q` containment): the strict step is obtained inside `↥Q` and pushed
back through `Q.subtype` (`map_lt_map_iff_of_injective` + `subgroupOf_map_subtype`).

In Theorem 15.2's brick D (mmd L4194) this furnishes the nontrivial chain top `Q1 < N_Q(Q1)` handed
to `exists_minimal_normalOver` (ambient `N_M(Q1)`, `T = N_Q(Q1) ≤ Q`) to build the next chief
factor `Q2/Q1` with `Q1 < Q2 ≤ Q`. -/
theorem lt_inf_normalizer_of_lt_of_isNilpotent {Q Q0 : Subgroup G} [Group.IsNilpotent ↥Q]
    (hQ0Q : Q0 < Q) :
    Q0 < Q ⊓ Subgroup.normalizer (Q0 : Set G) := by
  have hQ0le : Q0 ≤ Q := hQ0Q.le
  have hlt : Q0.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top, ne_eq, Subgroup.subgroupOf_eq_top]; exact hQ0Q.2
  have h := OddOrder.Isaacs.Ch01.lt_normalizer_of_isNilpotent_of_lt_top (G := ↥Q) hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hQ0le] at h
  -- `h : Q0.subgroupOf Q < (N_G Q0).subgroupOf Q`; map back to `G` along the injective `Q.subtype`.
  have hmap := (Subgroup.map_lt_map_iff_of_injective Q.subtype_injective).mpr h
  rw [Subgroup.map_subgroupOf_eq_of_le hQ0le, Subgroup.subgroupOf_map_subtype] at hmap
  rwa [inf_comm] at hmap

/-- **Minimal `N`-normal subgroup over `Q₀`** (`§14`-independent, reusable): given a nontrivial
`N`-normal subgroup `T` strictly above `Q₀`, there is a minimal `N`-normal subgroup `Q₁` with
`Q₀ < Q₁ ≤ T` (no `N`-normal subgroup lies strictly between `Q₀` and `Q₁`).  This is the
subgroup-lattice (quotient-free) form of "the quotient `N/Q₀` has a minimal normal subgroup inside
`T/Q₀`", obtained from finiteness of the subgroup lattice (`Set.Finite.exists_minimal`).

In Theorem 15.2's step 3 (mmd L4194) `N = N_M(Q₀)` and `T = N_Q(Q₀) = Q ⊓ N_M(Q₀)` (nontrivial over
`Q₀` by `lt_normalizer_of_lt_of_isNilpotent`), giving the minimal normal `Q₁/Q₀` with `Q₁ ≤ Q`. -/
theorem exists_minimal_normalOver [Finite G] {N Q0 T : Subgroup G}
    (hQ0T : Q0 < T) (hTnorm : (T.subgroupOf N).Normal) :
    ∃ Q1 : Subgroup G, Q0 < Q1 ∧ Q1 ≤ T ∧ (Q1.subgroupOf N).Normal ∧
      ∀ H : Subgroup G, Q0 < H → H ≤ Q1 → (H.subgroupOf N).Normal → Q1 ≤ H := by
  let S : Set (Subgroup G) := {H | Q0 < H ∧ H ≤ T ∧ (H.subgroupOf N).Normal}
  have hS_fin : S.Finite := Set.toFinite S
  have hS_ne : S.Nonempty := ⟨T, hQ0T, le_refl T, hTnorm⟩
  obtain ⟨Q1, ⟨hQ0Q1, hQ1T, hQ1norm⟩, hQ1min⟩ := hS_fin.exists_minimal hS_ne
  exact ⟨Q1, hQ0Q1, hQ1T, hQ1norm, fun H hQ0H hHQ1 hHnorm =>
    hQ1min ⟨hQ0H, hHQ1.trans hQ1T, hHnorm⟩ hHQ1⟩

/-- **Chief factor over `Q₁` normalized by `D` and `K₁`** (Theorem 15.2 brick D construction,
mmd L4194).  If `Q₁ < Q` with `Q` nilpotent, `Q ⊴ M` (`Q ≤ M ≤ N_G(Q)`), and `D, K₁ ≤ M ⊓ N_G(Q₁)`,
then there is a chief factor `Q₂/Q₁` with `Q₁ < Q₂ ≤ Q` whose `Q₂` is normalized by `D` and `K₁`
and itself normalizes `Q₁`.

Ambient `N = M ⊓ N_G(Q₁)` contains `D` and `K₁` and normalizes `T = N_Q(Q₁) = Q ⊓ N_G(Q₁) ≤ Q`
(`N ≤ N_G(Q)` since `N ≤ M ≤ N_G(Q)`, and `N ≤ N_G(N_G(Q₁))` by `le_normalizer`, so `N ≤ N_G(T)` by
`le_normalizer_inf`).  `lt_inf_normalizer_of_lt_of_isNilpotent` gives the nontrivial top
`Q₁ < N_Q(Q₁)`; `exists_minimal_normalOver` then produces the minimal `N`-normal `Q₂` over `Q₁`
inside `T`, and `Q₂ ⊴ N` transfers to `D, K₁ ≤ N_G(Q₂)`. -/
theorem exists_chiefFactor_over_normalized [Finite G]
    {M Q Q1 D K1 : Subgroup G} [Group.IsNilpotent ↥Q]
    (hQ1Q : Q1 < Q) (hQM : Q ≤ M) (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hDN : D ≤ M ⊓ Subgroup.normalizer (Q1 : Set G))
    (hK1N : K1 ≤ M ⊓ Subgroup.normalizer (Q1 : Set G)) :
    ∃ Q2 : Subgroup G, Q1 < Q2 ∧ Q2 ≤ Q ∧
      D ≤ Subgroup.normalizer (Q2 : Set G) ∧
      K1 ≤ Subgroup.normalizer (Q2 : Set G) ∧
      Q2 ≤ Subgroup.normalizer (Q1 : Set G) := by
  -- Nontrivial chain top `Q₁ < N_Q(Q₁) = Q ⊓ N_G(Q₁)`.
  have hQ1T : Q1 < Q ⊓ Subgroup.normalizer (Q1 : Set G) :=
    lt_inf_normalizer_of_lt_of_isNilpotent hQ1Q
  -- `T = N_Q(Q₁) ≤ N = N_M(Q₁)`.
  have hTN : Q ⊓ Subgroup.normalizer (Q1 : Set G) ≤ M ⊓ Subgroup.normalizer (Q1 : Set G) :=
    inf_le_inf hQM le_rfl
  -- `N` normalizes `T` (it normalizes `Q` via `M ≤ N_G(Q)` and `N_G(Q₁)` via `le_normalizer`).
  have hN_normT : M ⊓ Subgroup.normalizer (Q1 : Set G) ≤
      Subgroup.normalizer ((Q ⊓ Subgroup.normalizer (Q1 : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf (inf_le_left.trans hMQ) (inf_le_right.trans Subgroup.le_normalizer)
  have hTnorm : ((Q ⊓ Subgroup.normalizer (Q1 : Set G)).subgroupOf
      (M ⊓ Subgroup.normalizer (Q1 : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).mpr hN_normT
  -- Minimal `N`-normal subgroup over `Q₁` inside `T`.
  obtain ⟨Q2, hQ1Q2, hQ2T, hQ2norm, _⟩ := exists_minimal_normalOver hQ1T hTnorm
  have hQ2Q : Q2 ≤ Q := hQ2T.trans inf_le_left
  have hQ2Q1norm : Q2 ≤ Subgroup.normalizer (Q1 : Set G) := hQ2T.trans inf_le_right
  -- `Q₂ ⊴ N`, so `N`—and hence `D`, `K₁`—normalizes `Q₂`.
  have hN_normQ2 : M ⊓ Subgroup.normalizer (Q1 : Set G) ≤ Subgroup.normalizer (Q2 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hQ2T.trans hTN)).mp hQ2norm
  exact ⟨Q2, hQ1Q2, hQ2Q, hDN.trans hN_normQ2, hK1N.trans hN_normQ2, hQ2Q1norm⟩

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **Coprime lifting over a normal `D`-invariant subgroup** (`§14`-independent, reusable; the
practical non-abelian form of `N = ⁅N,D⁆·C_N(D)` instantiated at a *given* normal subgroup `M₀`
containing `⁅N,D⁆`).  If `D` normalizes `N`, `M₀ ≤ N` is normalized by both `N` and `D`,
`⁅N, D⁆ ≤ M₀`, and `(|D|, |N|) = 1` (with `D` or `N` solvable), then `N = M₀·C_N(D)`, i.e.
`N ≤ M₀ ⊔ (N ⊓ C_G(D))`.

Quotienting by the *normal* `M₀` sidesteps the (not-free) `⁅N,D⁆ ⊴ N`: since `⁅N,D⁆ ⊆ M₀`, `D` acts
trivially on `N/M₀`, so the quotient fixed points are `⊤`; the coprime fixed-point lifting
`fixedPointsOfMulAut_quotientMulAutHom_eq_map` (BG Proposition 1.5(d)) rewrites them as the
push-forward `C_N(D)·M₀/M₀`, whence `N = C_N(D)·M₀`.  The conjugation action of `D` on `↥N` is
`(normalizerMonoidHom N).comp (inclusion hDN)`, matching the `S06`/`S03h` bridges
(`actionCommutator_conj_map_subtype`, `fixedPointsOfMulAut_conj_map_subtype`).

In Theorem 15.2's step 3 part (ii) (mmd L4194): with `N = Q₁`, `M₀ = Q₀ = C_Q(D)`, an extra
`C_{Q₁}(D) ⊆ Q₀` forces `Q₁ ⊆ Q₀`, contradicting `Q₀ < Q₁`. -/
theorem le_sup_inf_centralizer_of_commutator_le [Finite G]
    {N M₀ D : Subgroup G}
    (hM₀N : M₀ ≤ N)
    (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hN_M₀ : N ≤ Subgroup.normalizer (M₀ : Set G))
    (hDM₀ : D ≤ Subgroup.normalizer (M₀ : Set G))
    (hcomm : ⁅N, D⁆ ≤ M₀)
    (hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥N))
    (hSolv : IsSolvable ↥D ∨ IsSolvable ↥N) :
    N ≤ M₀ ⊔ (N ⊓ Subgroup.centralizer (D : Set G)) := by
  -- The conjugation action of `D` on `↥N` (`D ≤ N_G(N)`).
  set φ : ↥D →* MulAut ↥N :=
    (Subgroup.normalizerMonoidHom N).comp (Subgroup.inclusion hDN) with hφ
  -- `M₀.subgroupOf N` is normal in `↥N` and `D`-invariant.
  haveI hM₀N_normal : (M₀.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hM₀N).mpr hN_M₀
  have hMinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (M₀.subgroupOf N) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    show (a : G) * (x : G) * (a : G)⁻¹ ∈ M₀
    exact (Subgroup.mem_normalizer_iff.mp (hDM₀ a.2) (x : G)).mp hx
  -- `actionCommutator φ ≤ M₀.subgroupOf N` (from `⁅N,D⁆ ⊆ M₀`).
  have hac_map : (OddOrder.Isaacs.Ch04.actionCommutator φ).map N.subtype = ⁅N, D⁆ :=
    OddOrder.BG.Ch1.S06.actionCommutator_conj_map_subtype hDN
  have hac_le : OddOrder.Isaacs.Ch04.actionCommutator φ ≤ M₀.subgroupOf N := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have : (N.subtype y) ∈ (OddOrder.Isaacs.Ch04.actionCommutator φ).map N.subtype :=
      ⟨y, hy, rfl⟩
    rw [hac_map] at this
    exact hcomm this
  -- `D` acts trivially on `N/M₀`: the quotient fixed points are `⊤`.
  have htop : Subgroup.fixedPointsOfMulAut
      (quotientMulAutHom hMinv) = ⊤ := by
    have hbot : OddOrder.Isaacs.Ch04.actionCommutator
        (quotientMulAutHom hMinv) = ⊥ := by
      rw [OddOrder.Isaacs.Ch04.actionCommutator_quotient_eq_map, Subgroup.map_eq_bot_iff,
        QuotientGroup.ker_mk']
      exact hac_le
    rw [Subgroup.eq_top_iff']
    intro g
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    exact (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially _).mp hbot a g
  -- Proposition 1.5(d): quotient fixed points are the push-forward of `C_N(D)`.
  have hmap := OddOrder.BG.Ch1.S03h.fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := φ) hcop hSolv hMinv
  rw [htop] at hmap
  -- `C_N(D) ⊔ M₀ = ⊤` in `↥N`.
  have hsup : Subgroup.fixedPointsOfMulAut φ ⊔ M₀.subgroupOf N = ⊤ := by
    have hcme := Subgroup.comap_map_eq (f := QuotientGroup.mk' (M₀.subgroupOf N))
      (Subgroup.fixedPointsOfMulAut φ)
    rw [QuotientGroup.ker_mk', ← hmap, Subgroup.comap_top] at hcme
    exact hcme.symm
  -- Map back to `G`: `(C_G(D) ⊓ N) ⊔ M₀ = N`.
  have hbridge : (Subgroup.fixedPointsOfMulAut φ).map N.subtype =
      Subgroup.centralizer (D : Set G) ⊓ N :=
    OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hDN
  have hmapN := congrArg (Subgroup.map N.subtype) hsup
  rw [Subgroup.map_sup, hbridge, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hM₀N,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmapN
  refine le_of_eq ?_
  calc N = Subgroup.centralizer (D : Set G) ⊓ N ⊔ M₀ := hmapN.symm
    _ = M₀ ⊔ (N ⊓ Subgroup.centralizer (D : Set G)) := by rw [inf_comm, sup_comm]

/-- **Step 3(ii) contradiction engine** for Theorem 15.2 (mmd L4194): in the configuration
`Q₀ = C_Q(D) ≤ Q₁ ≤ Q` with `D`/`Q₁` normalizing the relevant subgroups and `(|D|, |Q₁|) = 1`, if
`D` centralizes `Q₁/Q₀` (`⁅Q₁, D⁆ ≤ Q₀`) then `Q₁ ≤ Q₀`.  This is the collapse that makes "`D`
centralizes `Q₁/Q₀`" contradict `Q₀ < Q₁`: the lifting `le_sup_inf_centralizer_of_commutator_le`
gives `Q₁ ≤ Q₀ ⊔ C_{Q₁}(D)`, and `C_{Q₁}(D) = Q₁ ⊓ C_G(D) ≤ Q ⊓ C_G(D) = Q₀` (since `Q₁ ≤ Q`),
so `Q₁ ≤ Q₀`.  In the proof of (e), `D` centralizing `Q₁/Q₀` is what the regular `K`-action on
`DQ₁/Q₀` (via Theorem 3.7) forces, so this lemma turns that into the contradiction `Q₁ = Q₀`. -/
theorem le_of_commutator_le_centralizerCap [Finite G]
    {Q Q0 Q1 D : Subgroup G}
    (hQ0 : Q0 = Q ⊓ Subgroup.centralizer (D : Set G))
    (hQ01 : Q0 ≤ Q1) (hQ1Q : Q1 ≤ Q)
    (hDQ1 : D ≤ Subgroup.normalizer (Q1 : Set G))
    (hQ1Q0 : Q1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hDQ0 : D ≤ Subgroup.normalizer (Q0 : Set G))
    (hcomm : ⁅Q1, D⁆ ≤ Q0)
    (hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q1))
    (hSolv : IsSolvable ↥D ∨ IsSolvable ↥Q1) :
    Q1 ≤ Q0 := by
  have hlift := le_sup_inf_centralizer_of_commutator_le hQ01 hDQ1 hQ1Q0 hDQ0 hcomm hcop hSolv
  have hcap : Q1 ⊓ Subgroup.centralizer (D : Set G) ≤ Q0 := by
    rw [hQ0]; exact inf_le_inf_right _ hQ1Q
  exact hlift.trans (sup_le le_rfl hcap)

/-- **General collapse** (Theorem 15.2 step 3(ii)): `⁅N,D⁆ ≤ M₀` and `N ⊓ C_G(D) ≤ M₀` give
`N ≤ M₀` (the lifting `le_sup_inf_centralizer_of_commutator_le` plus the centralizer cap).
Generalizes `le_of_commutator_le_centralizerCap` by taking the cap directly, so it also applies to
brick D's `(Q₁, Q₂)` step where `M₀ = Q₁ ≠ C_Q(D)`. -/
theorem le_of_commutator_le_of_inf_centralizer_le [Finite G] {N M₀ D : Subgroup G}
    (hM₀N : M₀ ≤ N) (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hN_M₀ : N ≤ Subgroup.normalizer (M₀ : Set G))
    (hDM₀ : D ≤ Subgroup.normalizer (M₀ : Set G))
    (hcomm : ⁅N, D⁆ ≤ M₀) (hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥N))
    (hSolv : IsSolvable ↥D ∨ IsSolvable ↥N)
    (hcap : N ⊓ Subgroup.centralizer (D : Set G) ≤ M₀) :
    N ≤ M₀ :=
  (le_sup_inf_centralizer_of_commutator_le hM₀N hDN hN_M₀ hDM₀ hcomm hcop hSolv).trans
    (sup_le le_rfl hcap)

/-- **Nilpotent ⟹ coprime normal `q`-part centralizes `q′`-part** (`§14`-independent, reusable): in
a nilpotent finite group, a normal `q`-subgroup `A` (`q` prime) and a `q′`-subgroup `B` satisfy
`⁅A, B⁆ = ⊥`.  `B` lies in the normal Hall `q′`-subgroup `O_{q′} = opiCoreInG {q}ᶜ ⊤` (nilpotency,
`piGroup_le_opiCoreInG_of_nilpotent`), which is normal of order coprime to the `q`-group `A`, so
`⁅A, B⁆ ≤ ⁅A, O_{q′}⁆ ≤ A ⊓ O_{q′} = ⊥`.

This is the kernel of Theorem 15.2 step 3(ii): the nilpotent quotient `DQ₁/Q₀` (from Theorem 3.7
on the regular `K`-action) has the `q′`-image of `D` centralizing the normal `q`-subgroup `Q₁/Q₀`,
i.e. `⁅Q₁, D⁆ ⊆ Q₀` after pulling back. -/
theorem commutator_eq_bot_of_isNilpotent_of_normal_isPGroup
    {𝓗 : Type*} [Group 𝓗] [Finite 𝓗] [Group.IsNilpotent 𝓗]
    {q : ℕ} [Fact q.Prime] {A B : Subgroup 𝓗} [A.Normal] (hA : IsPGroup q A)
    (hB : q ∉ (Nat.card ↥B).primeFactors) :
    ⁅A, B⁆ = ⊥ := by
  haveI : Group.IsNilpotent ↥(⊤ : Subgroup 𝓗) :=
    Group.nilpotent_of_mulEquiv Subgroup.topEquiv.symm
  haveI hOnorm : (opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗)).Normal :=
    opiCoreInG_normal ({q}ᶜ : Set ℕ)
  -- `B ≤ O_{q′}` (a `q′`-subgroup of a nilpotent group).
  have hBO : B ≤ opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗) := by
    refine piGroup_le_opiCoreInG_of_nilpotent (fun r hr => ?_) le_top
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl; exact hB hr
  -- `A ⊓ O_{q′} = ⊥` (`q`-group vs `q′`-group).
  have hAO : A ⊓ opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗) = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime
      (coprime_of_forall_prime_not_dvd (fun r hr hrA hrO => ?_))
    have hrq : r = q := by
      have hπA : Subgroup.IsPiSubgroup ({q} : Set ℕ) A :=
        isPiSubgroup_of_isPGroup_of_mem hA rfl
      exact hπA r (Nat.mem_primeFactors.mpr ⟨hr, hrA, Nat.card_pos.ne'⟩)
    rw [hrq] at hr hrO
    exact (isPiSubgroup_opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗) q
      (Nat.mem_primeFactors.mpr ⟨hr, hrO, Nat.card_pos.ne'⟩)) rfl
  rw [eq_bot_iff]
  have hmono : ⁅A, B⁆ ≤ ⁅A, opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗)⁆ :=
    Subgroup.commutator_mono le_rfl hBO
  have hinf : ⁅A, opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗)⁆ ≤
      A ⊓ opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗) :=
    Subgroup.commutator_le_inf A (opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗))
  exact (hmono.trans hinf).trans hAO.le

/-- **B1 of Theorem 15.2 step 3(ii)** (`§14`-independent, reusable): if the quotient `N/Q₀'` is
nilpotent, `A₀ ⊴ N` is a `q`-group (`q` prime) and `B₀ ≤ N` is a `q′`-group, then `⁅A₀, B₀⁆ ≤ Q₀'`.
The images `Ā₀ = A₀·Q₀'/Q₀'` (normal `q`-group) and `B̄₀` (`q′`-group) of the nilpotent quotient
satisfy `⁅Ā₀, B̄₀⁆ = ⊥` (`commutator_eq_bot_of_isNilpotent_of_normal_isPGroup`); since
`⁅Ā₀, B̄₀⁆ = ⁅A₀, B₀⁆·Q₀'/Q₀'` (`map_commutator`), the commutator lands in `ker = Q₀'`.

For the regular-action contradiction (mmd L4194): with `N = ↥(D ⊔ Q₁)`, `Q₀' = Q₀.subgroupOf`,
`A₀ = Q₁.subgroupOf`, `B₀ = D.subgroupOf`, once `DQ₁/Q₀` is nilpotent (Theorem 3.7) this gives
`⁅Q₁, D⁆ ⊆ Q₀`, feeding `le_of_commutator_le_centralizerCap` for the contradiction. -/
theorem commutator_le_of_quotient_isNilpotent {N : Type*} [Group N] [Finite N]
    {q : ℕ} [Fact q.Prime] {Q0' A0 B0 : Subgroup N} [Q0'.Normal] [A0.Normal]
    (hNilp : Group.IsNilpotent (N ⧸ Q0'))
    (hA0 : IsPGroup q A0) (hB0 : q ∉ (Nat.card ↥B0).primeFactors) :
    ⁅A0, B0⁆ ≤ Q0' := by
  haveI := hNilp
  haveI : (A0.map (QuotientGroup.mk' Q0')).Normal :=
    ‹A0.Normal›.map _ (QuotientGroup.mk'_surjective Q0')
  have hAq : IsPGroup q (A0.map (QuotientGroup.mk' Q0')) := hA0.map _
  have hBq' : q ∉ (Nat.card ↥(B0.map (QuotientGroup.mk' Q0'))).primeFactors := fun hq =>
    hB0 (Nat.primeFactors_mono (Subgroup.card_map_dvd (H := B0) _) Nat.card_pos.ne' hq)
  have hbot : ⁅A0.map (QuotientGroup.mk' Q0'), B0.map (QuotientGroup.mk' Q0')⁆ = ⊥ :=
    commutator_eq_bot_of_isNilpotent_of_normal_isPGroup hAq hBq'
  rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

/-- **Second-isomorphism nilpotency transfer** (reusable): for `N ⊴ G` and `H ≤ G`, if the image
`H.map (mk' N)` (`= H·N/N`) is nilpotent then so is the quotient `↥H / (N.subgroupOf H)`.
The map `mk' N ∘ H.subtype : ↥H → G/N` has kernel `N.subgroupOf H` and range `H.map (mk' N)`, so
Noether's first isomorphism (`quotientKerEquivRange`) gives the iso, and nilpotency transfers.

Brick B2 of Theorem 15.2 step 3(ii): once Theorem 3.7 makes the image of `D ⊔ Q₁` in the ambient
quotient nilpotent, this transfers it to `IsNilpotent (↥(D ⊔ Q₁) / Q₀.subgroupOf _)`, feeding `B1`
(`commutator_le_of_quotient_isNilpotent`). -/
theorem isNilpotent_quotient_subgroupOf_of_isNilpotent_map {G : Type*} [Group G]
    {N H : Subgroup G} [N.Normal]
    (hNilp : Group.IsNilpotent ↥(H.map (QuotientGroup.mk' N))) :
    Group.IsNilpotent (↥H ⧸ N.subgroupOf H) := by
  set φ : ↥H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype with hφ
  have hker : φ.ker = N.subgroupOf H := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
  have hrange : φ.range = H.map (QuotientGroup.mk' N) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  haveI : Group.IsNilpotent ↥φ.range := by rw [hrange]; exact hNilp
  have e : ↥H ⧸ N.subgroupOf H ≃* ↥φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  exact Group.nilpotent_of_mulEquiv e.symm

/-- **Brick B2 core of Theorem 15.2 step 3(ii)** (mmd L4194, regular-action ⟹ nilpotent step):
if `K₁` (prime order) acts regularly on `DQ₁/Q₀` — the preimage fixed-point-free condition `hFPF`
(`k` fixes `x` mod `Q₀` only when `x ∈ Q₀`) — then `↥(D ⊔ Q₁) / Q₀.subgroupOf _` is nilpotent.

Ambient `P = D ⊔ Q₁ ⊔ K₁` (so `Q₀ ⊴ P`), `Γ = ↥P / Q₀`; push `D ⊔ Q₁`, `K₁` into `Γ` via
`ψ, ρ = π ∘ inclusion`.  Theorem 3.7 on the images `N̄ = ψ.range`, `R̄ = ρ.range` gives
`IsNilpotent ↥N̄`; Noether's first isomorphism (`quotientKerEquivRange ψ`, kernel `Q₀.subgroupOf _`)
transfers it to the quotient.  Feeds `commutator_le_of_quotient_isNilpotent` (B1). -/
theorem isNilpotent_DQ1_quotient_of_regular [Finite G]
    {D Q1 K1 Q0 : Subgroup G} [(Q0.subgroupOf (D ⊔ Q1)).Normal]
    (hPsolv : IsSolvable ↥(D ⊔ Q1 ⊔ K1))
    (hPQ0 : D ⊔ Q1 ⊔ K1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hK1DQ1 : K1 ≤ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G))
    (hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p)
    (hdisj : Disjoint (D ⊔ Q1) K1)
    (hK1Q0disj : Disjoint K1 Q0)
    (hQ0lt : Q0 < D ⊔ Q1)
    (hFPF : ∀ k ∈ K1, k ≠ 1 → ∀ x ∈ D ⊔ Q1, k * x⁻¹ * k⁻¹ * x ∈ Q0 → x ∈ Q0) :
    Group.IsNilpotent (↥(D ⊔ Q1) ⧸ (Q0.subgroupOf (D ⊔ Q1))) := by
  have hDQ1P : D ⊔ Q1 ≤ D ⊔ Q1 ⊔ K1 := le_sup_left
  have hK1P : K1 ≤ D ⊔ Q1 ⊔ K1 := le_sup_right
  haveI hQ0P_normal : (Q0.subgroupOf (D ⊔ Q1 ⊔ K1)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hPQ0
  set π : ↥(D ⊔ Q1 ⊔ K1) →* ↥(D ⊔ Q1 ⊔ K1) ⧸ (Q0.subgroupOf (D ⊔ Q1 ⊔ K1)) :=
    QuotientGroup.mk' _ with hπ
  set ψ : ↥(D ⊔ Q1) →* ↥(D ⊔ Q1 ⊔ K1) ⧸ (Q0.subgroupOf (D ⊔ Q1 ⊔ K1)) :=
    π.comp (Subgroup.inclusion hDQ1P) with hψ
  set ρ : ↥K1 →* ↥(D ⊔ Q1 ⊔ K1) ⧸ (Q0.subgroupOf (D ⊔ Q1 ⊔ K1)) :=
    π.comp (Subgroup.inclusion hK1P) with hρ
  haveI := hPsolv
  -- Kernels of `ψ`, `ρ` and the "trivial image ⟺ lies in `Q₀`" criteria.
  have hkerψ : ψ.ker = Q0.subgroupOf (D ⊔ Q1) := by
    rw [hψ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
  have hkerρ : ρ.ker = Q0.subgroupOf K1 := by
    rw [hρ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
  have hψ1 : ∀ b : ↥(D ⊔ Q1), ψ b = 1 ↔ (b : G) ∈ Q0 := fun b => by
    rw [← MonoidHom.mem_ker, hkerψ, Subgroup.mem_subgroupOf]
  have hρ1 : ∀ b : ↥K1, ρ b = 1 ↔ (b : G) ∈ Q0 := fun b => by
    rw [← MonoidHom.mem_ker, hkerρ, Subgroup.mem_subgroupOf]
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, hkerρ, Subgroup.subgroupOf_eq_bot]
    exact hK1Q0disj.symm
  -- Quotient-equality criterion and the values of `ψ`, `ρ`.
  have hπeq : ∀ u v : ↥(D ⊔ Q1 ⊔ K1), π u = π v ↔ (u : G)⁻¹ * (v : G) ∈ Q0 := by
    intro u v
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  have hψval : ∀ b : ↥(D ⊔ Q1), ψ b = π (Subgroup.inclusion hDQ1P b) := fun b => rfl
  have hρval : ∀ c : ↥K1, ρ c = π (Subgroup.inclusion hK1P c) := fun c => rfl
  haveI : IsSolvable ↥(ψ.range ⊔ ρ.range) :=
    solvable_of_solvable_injective (Subgroup.subtype_injective _)
  -- `ψ.range` is normal in `Γ`: `P = D ⊔ Q₁ ⊔ K₁ ≤ N_G(D ⊔ Q₁)` (as `K₁` normalizes `D ⊔ Q₁`).
  have hψrange : ψ.range = ((D ⊔ Q1).subgroupOf (D ⊔ Q1 ⊔ K1)).map π := by
    rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
  haveI hNPnormal : ((D ⊔ Q1).subgroupOf (D ⊔ Q1 ⊔ K1)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hK1DQ1)
  haveI hψrange_normal : (ψ.range).Normal := by
    rw [hψrange]; exact hNPnormal.map π (QuotientGroup.mk'_surjective _)
  have hNilpN : Group.IsNilpotent ↥(ψ.range) := by
    refine OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree
      (N := ψ.range) (R := ρ.range) ?_ ?_ ?_ ?_ ?_ ?_
    · -- `ρ.range ≤ N(ψ.range) = ⊤` since `ψ.range ⊴ Γ`.
      exact le_top.trans_eq (Subgroup.normalizer_eq_top_iff.mpr hψrange_normal).symm
    · -- `Disjoint ψ.range ρ.range`: a common image lifts to `(D ⊔ Q₁) ⊓ K₁ = ⊥`.
      rw [Subgroup.disjoint_def]
      intro y hyψ hyρ
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hyψ
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hyρ
      have hbc : (b : G)⁻¹ * (c : G) ∈ Q0 :=
        (hπeq (Subgroup.inclusion hDQ1P b) (Subgroup.inclusion hK1P c)).mp
          (by rw [← hψval, ← hρval]; exact hc.symm)
      have hcDQ1 : (c : G) ∈ D ⊔ Q1 := by
        have hrw : (c : G) = (b : G) * ((b : G)⁻¹ * (c : G)) := by group
        rw [hrw]
        exact (D ⊔ Q1).mul_mem b.2 (hQ0lt.le hbc)
      have hmem : (c : G) ∈ (D ⊔ Q1) ⊓ K1 := ⟨hcDQ1, c.2⟩
      rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
      rw [← hc, show c = 1 from Subtype.ext hmem, map_one]
    · -- `ψ.range ≠ ⊥`: the image of an `x ∈ (D ⊔ Q₁) ∖ Q₀` is nontrivial.
      obtain ⟨x, hxDQ1, hxQ0⟩ := SetLike.exists_of_lt hQ0lt
      intro hbot
      refine hxQ0 ((hψ1 ⟨x, hxDQ1⟩).mp ?_)
      have hmem : ψ ⟨x, hxDQ1⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hmem
    · -- `ρ.range ≠ ⊥`: `K₁` is nontrivial and meets `Q₀` trivially.
      obtain ⟨p, hp, hcard⟩ := hK1prime
      haveI : Nontrivial ↥K1 := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; exact hp.one_lt)
      obtain ⟨k, hk1⟩ := exists_ne (1 : ↥K1)
      intro hbot
      refine hk1 (Subtype.ext ?_)
      have hρk : ρ k = 1 := by
        have hmem : ρ k ∈ ρ.range := MonoidHom.mem_range.mpr ⟨k, rfl⟩
        rwa [hbot, Subgroup.mem_bot] at hmem
      have hmem : (k : G) ∈ K1 ⊓ Q0 := ⟨k.2, (hρ1 k).mp hρk⟩
      rw [hK1Q0disj.eq_bot, Subgroup.mem_bot] at hmem
      exact hmem
    · -- `card ρ.range = card K₁ = p` (`ρ` injective).
      obtain ⟨p, hp, hcard⟩ := hK1prime
      exact ⟨p, hp, by rw [← hcard]; exact Nat.card_congr (MonoidHom.ofInjective hρinj).symm.toEquiv⟩
    · -- Fixed-point-free: a fixed nontrivial image contradicts `hFPF` (`k` fixes `x` mod `Q₀`).
      intro r hr hr1 n hn hn1 heq
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hr
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hn
      have hk1 : (a : G) ≠ 1 := fun h => hr1 (by
        rw [hρval, show Subgroup.inclusion hK1P a = 1 from Subtype.ext h, map_one])
      have hconj : ρ a * ψ b * (ρ a)⁻¹ = π (Subgroup.inclusion hK1P a *
          Subgroup.inclusion hDQ1P b * (Subgroup.inclusion hK1P a)⁻¹) := by
        rw [hρval, hψval, map_mul, map_mul, map_inv]
      rw [hconj, hψval b] at heq
      have hmem := (hπeq _ _).mp heq
      refine hn1 ((hψ1 b).mpr (hFPF (a : G) a.2 hk1 (b : G) b.2 ?_))
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, mul_inv_rev,
        inv_inv, mul_assoc] using hmem
  have e : (↥(D ⊔ Q1) ⧸ Q0.subgroupOf (D ⊔ Q1)) ≃* ↥(ψ.range) :=
    (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  exact Group.nilpotent_of_mulEquiv e.symm

/-- **Regular-action ⟹ quotient nilpotent, single-subgroup form** (`§14`-independent, reusable;
generalises `isNilpotent_DQ1_quotient_of_regular` from `N = D ⊔ Q₁` to an arbitrary `N`).  If a
prime-order subgroup `K₁` acts on `N/Q₀` (`Q₀ ⊴ N`, `Q₀ < N`, `K₁ ≤ N_G(N)`, `K₁ ⊓ N = ⊥`,
`K₁ ⊓ Q₀ = ⊥`) fixed-point-freely on preimages — `k·x⁻¹·k⁻¹·x ∈ Q₀ ⟹ x ∈ Q₀` for `1 ≠ k ∈ K₁`,
`x ∈ N` — then `↥N / Q₀.subgroupOf N` is nilpotent.

Ambient `P = N ⊔ K₁`, `Γ = ↥P / Q₀`; the images `N̄ = ψ.range`, `K̄₁ = ρ.range` form a Frobenius
group (Theorem 3.7), making `N̄` nilpotent, and Noether's first isomorphism transfers it to the
quotient.  Used in Theorem 15.2 step (c)(d) with `N = M_σ`, `Q₀ = Q`, to prove `M_σ/Q` nilpotent
("`K` acts regularly on `M_σ/Q`", since `C_{M_σ}(K) = K* ⊆ Q`). -/
theorem isNilpotent_quotient_of_regular_general [Finite G]
    {N K1 Q0 : Subgroup G} [(Q0.subgroupOf N).Normal]
    (hPsolv : IsSolvable ↥(N ⊔ K1))
    (hPQ0 : N ⊔ K1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hK1N : K1 ≤ Subgroup.normalizer (N : Set G))
    (hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p)
    (hdisj : Disjoint N K1)
    (hK1Q0disj : Disjoint K1 Q0)
    (hQ0lt : Q0 < N)
    (hFPF : ∀ k ∈ K1, k ≠ 1 → ∀ x ∈ N, k * x⁻¹ * k⁻¹ * x ∈ Q0 → x ∈ Q0) :
    Group.IsNilpotent (↥N ⧸ (Q0.subgroupOf N)) := by
  have hNP : N ≤ N ⊔ K1 := le_sup_left
  have hK1P : K1 ≤ N ⊔ K1 := le_sup_right
  haveI hQ0P_normal : (Q0.subgroupOf (N ⊔ K1)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hPQ0
  set π : ↥(N ⊔ K1) →* ↥(N ⊔ K1) ⧸ (Q0.subgroupOf (N ⊔ K1)) :=
    QuotientGroup.mk' _ with hπ
  set ψ : ↥N →* ↥(N ⊔ K1) ⧸ (Q0.subgroupOf (N ⊔ K1)) :=
    π.comp (Subgroup.inclusion hNP) with hψ
  set ρ : ↥K1 →* ↥(N ⊔ K1) ⧸ (Q0.subgroupOf (N ⊔ K1)) :=
    π.comp (Subgroup.inclusion hK1P) with hρ
  haveI := hPsolv
  have hkerψ : ψ.ker = Q0.subgroupOf N := by
    rw [hψ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
  have hkerρ : ρ.ker = Q0.subgroupOf K1 := by
    rw [hρ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
  have hψ1 : ∀ b : ↥N, ψ b = 1 ↔ (b : G) ∈ Q0 := fun b => by
    rw [← MonoidHom.mem_ker, hkerψ, Subgroup.mem_subgroupOf]
  have hρ1 : ∀ b : ↥K1, ρ b = 1 ↔ (b : G) ∈ Q0 := fun b => by
    rw [← MonoidHom.mem_ker, hkerρ, Subgroup.mem_subgroupOf]
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, hkerρ, Subgroup.subgroupOf_eq_bot]
    exact hK1Q0disj.symm
  have hπeq : ∀ u v : ↥(N ⊔ K1), π u = π v ↔ (u : G)⁻¹ * (v : G) ∈ Q0 := by
    intro u v
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  have hψval : ∀ b : ↥N, ψ b = π (Subgroup.inclusion hNP b) := fun b => rfl
  have hρval : ∀ c : ↥K1, ρ c = π (Subgroup.inclusion hK1P c) := fun c => rfl
  haveI : IsSolvable ↥(ψ.range ⊔ ρ.range) :=
    solvable_of_solvable_injective (Subgroup.subtype_injective _)
  have hψrange : ψ.range = (N.subgroupOf (N ⊔ K1)).map π := by
    rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
  haveI hNPnormal : (N.subgroupOf (N ⊔ K1)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hK1N)
  haveI hψrange_normal : (ψ.range).Normal := by
    rw [hψrange]; exact hNPnormal.map π (QuotientGroup.mk'_surjective _)
  have hNilpN : Group.IsNilpotent ↥(ψ.range) := by
    refine OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree
      (N := ψ.range) (R := ρ.range) ?_ ?_ ?_ ?_ ?_ ?_
    · exact le_top.trans_eq (Subgroup.normalizer_eq_top_iff.mpr hψrange_normal).symm
    · rw [Subgroup.disjoint_def]
      intro y hyψ hyρ
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hyψ
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hyρ
      have hbc : (b : G)⁻¹ * (c : G) ∈ Q0 :=
        (hπeq (Subgroup.inclusion hNP b) (Subgroup.inclusion hK1P c)).mp
          (by rw [← hψval, ← hρval]; exact hc.symm)
      have hcN : (c : G) ∈ N := by
        have hrw : (c : G) = (b : G) * ((b : G)⁻¹ * (c : G)) := by group
        rw [hrw]
        exact N.mul_mem b.2 (hQ0lt.le hbc)
      have hmem : (c : G) ∈ N ⊓ K1 := ⟨hcN, c.2⟩
      rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
      rw [← hc, show c = 1 from Subtype.ext hmem, map_one]
    · obtain ⟨x, hxN, hxQ0⟩ := SetLike.exists_of_lt hQ0lt
      intro hbot
      refine hxQ0 ((hψ1 ⟨x, hxN⟩).mp ?_)
      have hmem : ψ ⟨x, hxN⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hmem
    · obtain ⟨p, hp, hcard⟩ := hK1prime
      haveI : Nontrivial ↥K1 := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; exact hp.one_lt)
      obtain ⟨k, hk1⟩ := exists_ne (1 : ↥K1)
      intro hbot
      refine hk1 (Subtype.ext ?_)
      have hρk : ρ k = 1 := by
        have hmem : ρ k ∈ ρ.range := MonoidHom.mem_range.mpr ⟨k, rfl⟩
        rwa [hbot, Subgroup.mem_bot] at hmem
      have hmem : (k : G) ∈ K1 ⊓ Q0 := ⟨k.2, (hρ1 k).mp hρk⟩
      rw [hK1Q0disj.eq_bot, Subgroup.mem_bot] at hmem
      exact hmem
    · obtain ⟨p, hp, hcard⟩ := hK1prime
      exact ⟨p, hp, by rw [← hcard]; exact Nat.card_congr (MonoidHom.ofInjective hρinj).symm.toEquiv⟩
    · intro r hr hr1 n hn hn1 heq
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hr
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hn
      have hk1 : (a : G) ≠ 1 := fun h => hr1 (by
        rw [hρval, show Subgroup.inclusion hK1P a = 1 from Subtype.ext h, map_one])
      have hconj : ρ a * ψ b * (ρ a)⁻¹ = π (Subgroup.inclusion hK1P a *
          Subgroup.inclusion hNP b * (Subgroup.inclusion hK1P a)⁻¹) := by
        rw [hρval, hψval, map_mul, map_mul, map_inv]
      rw [hconj, hψval b] at heq
      have hmem := (hπeq _ _).mp heq
      refine hn1 ((hψ1 b).mpr (hFPF (a : G) a.2 hk1 (b : G) b.2 ?_))
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, mul_inv_rev,
        inv_inv, mul_assoc] using hmem
  have e : (↥N ⧸ Q0.subgroupOf N) ≃* ↥(ψ.range) :=
    (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  exact Group.nilpotent_of_mulEquiv e.symm

/-- **Brick A "core" of Theorem 15.2 step 3(ii)** (mmd L4194): under the `K*`-condition, the fixed
points of `k` (with prime-manner action `C_{M_σ}(k) = K*`) inside `D ⊔ Q₁` land in `Q₀`.
`C(k) ⊓ (D ⊔ Q₁) ⊆ C(k) ⊓ M_σ = K*`; since `K* ≤ Q` and `Q ⊓ (D ⊔ Q₁) = Q₁` (Dedekind, `D ⊓ Q = ⊥`,
`C(k) ⊓ (D ⊔ Q₁) ⊆ C(k) ⊓ M_σ = K*`; since `K* ≤ Q` and `Q ⊓ (D ⊔ Q₁) = Q₁` (Dedekind, `D ⊓ Q = ⊥`,
`D ≤ N_G(Q₁)`), the fixed points lie in `K* ⊓ Q₁`, which is `≤ Q₀` (if `K* ≤ Q₀`) or trivial (if
`K* ⊄ Q₁`, as `|K*|` is prime).  Supplies `C_{DQ₁}(k) ⊆ Q₀` to brick A's Prop 1.5(d) lift. -/
theorem centralizer_inf_DQ1_le_Q0 [Finite G]
    {Mσ D Q Q1 Q0 Kstar : Subgroup G} {k : G}
    (hKstar : Subgroup.centralizer ({k} : Set G) ⊓ Mσ = Kstar)
    (hKstarQ : Kstar ≤ Q) (hDQ1Mσ : D ⊔ Q1 ≤ Mσ)
    (hQ1Q : Q1 ≤ Q) (hDQ : Disjoint D Q)
    (hDnormQ1 : D ≤ Subgroup.normalizer (Q1 : Set G))
    (hcond : Kstar ≤ Q0 ∨ ¬ Kstar ≤ Q1)
    (hprime : ∃ q : ℕ, q.Prime ∧ Nat.card ↥Kstar = q) :
    Subgroup.centralizer ({k} : Set G) ⊓ (D ⊔ Q1) ≤ Q0 := by
  have hDed : (Q1 ⊔ D) ⊓ Q = Q1 :=
    Subgroup.inf_sup_eq_of_le_normalizer_of_inf_eq_bot hQ1Q hDQ.eq_bot hDnormQ1
  have hsub : Subgroup.centralizer ({k} : Set G) ⊓ (D ⊔ Q1) ≤ Kstar ⊓ Q1 := by
    intro y hy
    obtain ⟨hyC, hyDQ1⟩ := Subgroup.mem_inf.mp hy
    have hyKstar : y ∈ Kstar := hKstar ▸ Subgroup.mem_inf.mpr ⟨hyC, hDQ1Mσ hyDQ1⟩
    refine Subgroup.mem_inf.mpr ⟨hyKstar, ?_⟩
    have hmem : y ∈ (Q1 ⊔ D) ⊓ Q := ⟨by rw [sup_comm]; exact hyDQ1, hKstarQ hyKstar⟩
    rwa [hDed] at hmem
  refine hsub.trans ?_
  rcases hcond with hc | hc
  · exact inf_le_left.trans hc
  · have hbot : Kstar ⊓ Q1 = ⊥ := by
      obtain ⟨q, hq, hcard⟩ := hprime
      have hdvd : Nat.card ↥(Kstar ⊓ Q1) ∣ Nat.card ↥Kstar := Subgroup.card_dvd_of_le inf_le_left
      rw [hcard] at hdvd
      rcases (Nat.dvd_prime hq).mp hdvd with h1 | hqq
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exact absurd ((Subgroup.eq_of_le_of_card_ge inf_le_left
          (by rw [hcard]; exact hqq.symm.le)) ▸ inf_le_right) hc
    rw [hbot]; exact bot_le

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Brick A "lift" of Theorem 15.2 step 3(ii)** (Prop 1.5(d)): from `C(k) ⊓ (D ⊔ Q₁) ≤ Q₀`
(brick A-core) and the coprime conjugation action of `⟨k⟩` on `D ⊔ Q₁`, `k` acts fixed-point-freely
on `(D ⊔ Q₁)/Q₀` — i.e. `k·x⁻¹·k⁻¹·x ∈ Q₀ ⟹ x ∈ Q₀`.  The quotient fixed points push forward from
`C_{D⊔Q₁}(⟨k⟩) = C(k) ⊓ (D ⊔ Q₁) ⊆ Q₀` (`fixedPointsOfMulAut_quotientMulAutHom_eq_map`), so they
are trivial; a `k`-fixed `x̄` is `⟨k⟩`-fixed (generator argument), hence `1`. -/
theorem fpf_of_centralizer_inf_le [Finite G]
    {D Q1 Q0 : Subgroup G} {k : G}
    (hk_norm : k ∈ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G))
    (hk_normQ0 : k ∈ Subgroup.normalizer (Q0 : Set G))
    (hDQ1Q0 : D ⊔ Q1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hQ0DQ1 : Q0 ≤ D ⊔ Q1)
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q1)))
    (hsolv : IsSolvable ↥(Subgroup.zpowers k) ∨ IsSolvable ↥(D ⊔ Q1))
    (hCk : Subgroup.centralizer ({k} : Set G) ⊓ (D ⊔ Q1) ≤ Q0) :
    ∀ x ∈ D ⊔ Q1, k * x⁻¹ * k⁻¹ * x ∈ Q0 → x ∈ Q0 := by
  have hkz : Subgroup.zpowers k ≤ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hk_norm
  have hkzQ0 : Subgroup.zpowers k ≤ Subgroup.normalizer (Q0 : Set G) :=
    Subgroup.zpowers_le.mpr hk_normQ0
  set φ : ↥(Subgroup.zpowers k) →* MulAut ↥(D ⊔ Q1) :=
    (Subgroup.normalizerMonoidHom (D ⊔ Q1)).comp (Subgroup.inclusion hkz) with hφ
  haveI hQ0_normal : (Q0.subgroupOf (D ⊔ Q1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0DQ1).mpr hDQ1Q0
  have hMinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (Q0.subgroupOf (D ⊔ Q1)) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    show (a : G) * (x : G) * (a : G)⁻¹ ∈ Q0
    exact (Subgroup.mem_normalizer_iff.mp (hkzQ0 a.2) (x : G)).mp hx
  -- Prop 1.5(d) + brick A-core: the quotient fixed points are trivial.
  have hbridge : (Subgroup.fixedPointsOfMulAut φ).map (D ⊔ Q1).subtype =
      Subgroup.centralizer ((Subgroup.zpowers k : Subgroup G) : Set G) ⊓ (D ⊔ Q1) :=
    OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hkz
  have hfp_le : Subgroup.fixedPointsOfMulAut φ ≤ Q0.subgroupOf (D ⊔ Q1) := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have hym : ((D ⊔ Q1).subtype y) ∈ (Subgroup.fixedPointsOfMulAut φ).map (D ⊔ Q1).subtype :=
      ⟨y, hy, rfl⟩
    rw [hbridge] at hym
    obtain ⟨hcent, _⟩ := Subgroup.mem_inf.mp hym
    exact hCk (Subgroup.mem_inf.mpr
      ⟨Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers k)) hcent, y.2⟩)
  have hmap := OddOrder.BG.Ch1.S03h.fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := φ) hcop hsolv hMinv
  have hfpbot : Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv) = ⊥ := by
    rw [hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hfp_le
  intro x hx hpre
  -- A `MulAut` fixing `y` fixes `y` under all its `zpowers` (stabilizer is a subgroup).
  have hpow : ∀ (f : MulAut (↥(D ⊔ Q1) ⧸ Q0.subgroupOf (D ⊔ Q1)))
      (y : ↥(D ⊔ Q1) ⧸ Q0.subgroupOf (D ⊔ Q1)), f y = y → ∀ i : ℤ, (f ^ i) y = y :=
    fun f y hf i => MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer (MulAut (↥(D ⊔ Q1) ⧸ Q0.subgroupOf (D ⊔ Q1))) y).zpow_mem
        (MulAction.mem_stabilizer_iff.mpr hf) i)
  -- The generator `k` fixes `x̄` (the premise `k·x⁻¹·k⁻¹·x ∈ Q₀`).
  have hkbar : quotientMulAutHom hMinv ⟨k, Subgroup.mem_zpowers k⟩
      (QuotientGroup.mk' (Q0.subgroupOf (D ⊔ Q1)) ⟨x, hx⟩) =
      QuotientGroup.mk' (Q0.subgroupOf (D ⊔ Q1)) ⟨x, hx⟩ := by
    rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    show (k * x * k⁻¹)⁻¹ * x ∈ Q0
    have heq : (k * x * k⁻¹)⁻¹ * x = k * x⁻¹ * k⁻¹ * x := by group
    rw [heq]; exact hpre
  -- Hence `x̄` is fixed by all of `⟨k⟩`, so lies in the trivial fixed-point set.
  have hxbar : QuotientGroup.mk' (Q0.subgroupOf (D ⊔ Q1)) ⟨x, hx⟩ ∈
      Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv) := by
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have ha : a = ⟨k, Subgroup.mem_zpowers k⟩ ^ i := Subtype.ext (by rw [← hi, Subgroup.coe_zpow])
    rw [ha, map_zpow]
    exact hpow (quotientMulAutHom hMinv ⟨k, Subgroup.mem_zpowers k⟩)
      (QuotientGroup.mk' (Q0.subgroupOf (D ⊔ Q1)) ⟨x, hx⟩) hkbar i
  rw [hfpbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hxbar
  exact hxbar

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Single-subgroup form of `fpf_of_centralizer_inf_le`** (`§14`-independent, reusable): the
Prop 1.5(d) fixed-point lift for an arbitrary subgroup `A` (not just `D ⊔ Q₁`).  If `k` normalizes
`A` and the normal `Q₀ ≤ A`, acts coprimely (`(|⟨k⟩|, |A|) = 1`, one-sided solvable), and
`C_G(k) ⊓ A ≤ Q₀`, then `k` acts fixed-point-freely on `A/Q₀`: `k·x⁻¹·k⁻¹·x ∈ Q₀ ⟹ x ∈ Q₀` for
`x ∈ A`.  Used in Theorem 15.2 step (c)(d) with `A = M_σ`, `Q₀ = Q` (the regular `K`-action on
`M_σ/Q` from `C_{M_σ}(k) = K* ⊆ Q`). -/
theorem fpf_of_centralizer_inf_le_general [Finite G]
    {A Q0 : Subgroup G} {k : G}
    (hk_norm : k ∈ Subgroup.normalizer (A : Set G))
    (hk_normQ0 : k ∈ Subgroup.normalizer (Q0 : Set G))
    (hAQ0 : A ≤ Subgroup.normalizer (Q0 : Set G))
    (hQ0A : Q0 ≤ A)
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥A))
    (hsolv : IsSolvable ↥(Subgroup.zpowers k) ∨ IsSolvable ↥A)
    (hCk : Subgroup.centralizer ({k} : Set G) ⊓ A ≤ Q0) :
    ∀ x ∈ A, k * x⁻¹ * k⁻¹ * x ∈ Q0 → x ∈ Q0 := by
  have hkz : Subgroup.zpowers k ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.zpowers_le.mpr hk_norm
  have hkzQ0 : Subgroup.zpowers k ≤ Subgroup.normalizer (Q0 : Set G) :=
    Subgroup.zpowers_le.mpr hk_normQ0
  set φ : ↥(Subgroup.zpowers k) →* MulAut ↥A :=
    (Subgroup.normalizerMonoidHom A).comp (Subgroup.inclusion hkz) with hφ
  haveI hQ0_normal : (Q0.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0A).mpr hAQ0
  have hMinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (Q0.subgroupOf A) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    show (a : G) * (x : G) * (a : G)⁻¹ ∈ Q0
    exact (Subgroup.mem_normalizer_iff.mp (hkzQ0 a.2) (x : G)).mp hx
  have hbridge : (Subgroup.fixedPointsOfMulAut φ).map A.subtype =
      Subgroup.centralizer ((Subgroup.zpowers k : Subgroup G) : Set G) ⊓ A :=
    OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hkz
  have hfp_le : Subgroup.fixedPointsOfMulAut φ ≤ Q0.subgroupOf A := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have hym : (A.subtype y) ∈ (Subgroup.fixedPointsOfMulAut φ).map A.subtype := ⟨y, hy, rfl⟩
    rw [hbridge] at hym
    obtain ⟨hcent, _⟩ := Subgroup.mem_inf.mp hym
    exact hCk (Subgroup.mem_inf.mpr
      ⟨Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers k)) hcent, y.2⟩)
  have hmap := OddOrder.BG.Ch1.S03h.fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := φ) hcop hsolv hMinv
  have hfpbot : Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv) = ⊥ := by
    rw [hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hfp_le
  intro x hx hpre
  have hpow : ∀ (f : MulAut (↥A ⧸ Q0.subgroupOf A)) (y : ↥A ⧸ Q0.subgroupOf A),
      f y = y → ∀ i : ℤ, (f ^ i) y = y :=
    fun f y hf i => MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer (MulAut (↥A ⧸ Q0.subgroupOf A)) y).zpow_mem
        (MulAction.mem_stabilizer_iff.mpr hf) i)
  have hkbar : quotientMulAutHom hMinv ⟨k, Subgroup.mem_zpowers k⟩
      (QuotientGroup.mk' (Q0.subgroupOf A) ⟨x, hx⟩) =
      QuotientGroup.mk' (Q0.subgroupOf A) ⟨x, hx⟩ := by
    rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    show (k * x * k⁻¹)⁻¹ * x ∈ Q0
    have heq : (k * x * k⁻¹)⁻¹ * x = k * x⁻¹ * k⁻¹ * x := by group
    rw [heq]; exact hpre
  have hxbar : QuotientGroup.mk' (Q0.subgroupOf A) ⟨x, hx⟩ ∈
      Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv) := by
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have ha : a = ⟨k, Subgroup.mem_zpowers k⟩ ^ i := Subtype.ext (by rw [← hi, Subgroup.coe_zpow])
    rw [ha, map_zpow]
    exact hpow (quotientMulAutHom hMinv ⟨k, Subgroup.mem_zpowers k⟩)
      (QuotientGroup.mk' (Q0.subgroupOf A) ⟨x, hx⟩) hkbar i
  rw [hfpbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hxbar
  exact hxbar

/-- **Brick A assembled** (Theorem 15.2 step 3(ii)): the `K*`-condition gives the regular/FPF
condition `hFPF` for every `k ∈ K₁^#`, by composing brick A-core (`centralizer_inf_DQ1_le_Q0`,
the `C(k)⊓(D⊔Q₁) ⊆ Q₀` step) with brick A-lift (`fpf_of_centralizer_inf_le`, the Prop 1.5(d)
fixed-point lift).  Per-`k` normalizer/coprimality data is drawn from the `K₁`-level hypotheses.

This is general over `(Q₀, Q₁)` (it does *not* require `Q₀ = C_Q(D)`), so it serves both the
`(Q₀, Q₁)` application and brick D's re-application with `(Q₁, Q₂)`. -/
theorem hFPF_of_kstar_condition [Finite G]
    {Mσ D Q Q1 Q0 Kstar K1 : Subgroup G}
    (hprime_manner : ∀ k ∈ K1, k ≠ 1 → Subgroup.centralizer ({k} : Set G) ⊓ Mσ = Kstar)
    (hKstarQ : Kstar ≤ Q) (hDQ1Mσ : D ⊔ Q1 ≤ Mσ)
    (hQ1Q : Q1 ≤ Q) (hDQ : Disjoint D Q)
    (hDnormQ1 : D ≤ Subgroup.normalizer (Q1 : Set G))
    (hcond : Kstar ≤ Q0 ∨ ¬ Kstar ≤ Q1)
    (hKstar_prime : ∃ q : ℕ, q.Prime ∧ Nat.card ↥Kstar = q)
    (hK1DQ1 : K1 ≤ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G))
    (hK1Q0 : K1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hDQ1Q0 : D ⊔ Q1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hQ0DQ1 : Q0 ≤ D ⊔ Q1)
    (hcop : ∀ k ∈ K1, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q1)))
    (hsolv : IsSolvable ↥(D ⊔ Q1)) :
    ∀ k ∈ K1, k ≠ 1 → ∀ x ∈ D ⊔ Q1, k * x⁻¹ * k⁻¹ * x ∈ Q0 → x ∈ Q0 := by
  intro k hk hk1
  have hCk := centralizer_inf_DQ1_le_Q0 (hprime_manner k hk hk1) hKstarQ hDQ1Mσ hQ1Q hDQ hDnormQ1
    hcond hKstar_prime
  exact fpf_of_centralizer_inf_le (hK1DQ1 hk) (hK1Q0 hk) hDQ1Q0 hQ0DQ1 (hcop k hk)
    (Or.inr hsolv) hCk

/-- **Part-(ii) contradiction core** (Theorem 15.2 step 3(ii)): from the regular condition `hFPF`,
the chain `B2-core → B1` gives `⁅Q₁, D⁆ ⊆ Q₀`.  `isNilpotent_DQ1_quotient_of_regular` makes
`(D ⊔ Q₁)/Q₀` nilpotent; `commutator_le_of_quotient_isNilpotent` (normal `q`-subgroup `Q₁`,
`q′`-subgroup `D`) gives `⁅Q₁, D⁆ ≤ Q₀` inside `↥(D ⊔ Q₁)`, pushed back to `G` via the subtype
(`map_commutator` + `subgroupOf_map_subtype`).  Composed with `hFPF_of_kstar_condition` and a
collapse, this yields the `K*`-condition contradiction. -/
theorem commutator_le_Q0_of_fpf [Finite G]
    {D Q1 K1 Q0 : Subgroup G} {q : ℕ} [Fact q.Prime]
    [(Q0.subgroupOf (D ⊔ Q1)).Normal] [(Q1.subgroupOf (D ⊔ Q1)).Normal]
    (hPsolv : IsSolvable ↥(D ⊔ Q1 ⊔ K1))
    (hPQ0 : D ⊔ Q1 ⊔ K1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hK1DQ1 : K1 ≤ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G))
    (hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p)
    (hdisj : Disjoint (D ⊔ Q1) K1) (hK1Q0disj : Disjoint K1 Q0)
    (hQ0lt : Q0 < D ⊔ Q1)
    (hQ1q : IsPGroup q (Q1.subgroupOf (D ⊔ Q1)))
    (hDq' : q ∉ (Nat.card ↥(D.subgroupOf (D ⊔ Q1))).primeFactors)
    (hQ0DQ1 : Q0 ≤ D ⊔ Q1)
    (hFPF : ∀ k ∈ K1, k ≠ 1 → ∀ x ∈ D ⊔ Q1, k * x⁻¹ * k⁻¹ * x ∈ Q0 → x ∈ Q0) :
    ⁅Q1, D⁆ ≤ Q0 := by
  have hNilp := isNilpotent_DQ1_quotient_of_regular hPsolv hPQ0 hK1DQ1 hK1prime hdisj hK1Q0disj
    hQ0lt hFPF
  have hB1 := commutator_le_of_quotient_isNilpotent (q := q) hNilp hQ1q hDq'
  have hmap := Subgroup.map_mono (f := (D ⊔ Q1).subtype) hB1
  simp only [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (le_sup_right : Q1 ≤ D ⊔ Q1), inf_eq_left.mpr (le_sup_left : D ≤ D ⊔ Q1),
    inf_eq_left.mpr hQ0DQ1] at hmap
  exact hmap

/-- **Part-(ii) regular-action contradiction engine** (Theorem 15.2 step 3(ii), mmd L4194): the
`K*`-condition `Kstar ≤ Q0 ∨ ¬ Kstar ≤ Q1` is contradictory with the chief chain `Q0 < Q1 ≤ Q` and
the type-`P` structural data.  Composes the three landed bricks:
`hFPF_of_kstar_condition` (the regular `K₁`-action `hFPF` from the prime-manner centralizer
`C_{M_σ}(k) = K*`), `commutator_le_Q0_of_fpf` (`B2-core → B1`: `⁅Q₁, D⁆ ≤ Q₀`) and the collapse
`le_of_commutator_le_of_inf_centralizer_le` (`Q₁ ≤ Q₀`), against `Q₀ < Q₁`.

Invoked twice in Theorem 15.2.  With `(Q₀, Q₁) = (C_Q(D), minimal normal over Q₀)` it refutes the
`K*`-condition, forcing `K* ⊄ Q₀ ∧ K* ⊆ Q₁`.  For brick D, with `(Q₁, Q₂)` (a chief factor over the
already-established `Q₁`), the left disjunct `K* ⊆ Q₁` holds, so the engine fires and forces
`Q₁ = Q`. -/
theorem false_of_kstar_condition_of_lt [Finite G]
    {Mσ D Q Q1 Q0 Kstar K1 : Subgroup G} {q : ℕ} [Fact q.Prime]
    [(Q0.subgroupOf (D ⊔ Q1)).Normal] [(Q1.subgroupOf (D ⊔ Q1)).Normal]
    (hprime_manner : ∀ k ∈ K1, k ≠ 1 → Subgroup.centralizer ({k} : Set G) ⊓ Mσ = Kstar)
    (hKstarQ : Kstar ≤ Q) (hKstar_prime : ∃ q : ℕ, q.Prime ∧ Nat.card ↥Kstar = q)
    (hDQ1Mσ : D ⊔ Q1 ≤ Mσ) (hQ1Q : Q1 ≤ Q)
    (hQ0DQ1 : Q0 ≤ D ⊔ Q1) (hQ0lt : Q0 < Q1)
    (hDQ : Disjoint D Q) (hdisj : Disjoint (D ⊔ Q1) K1) (hK1Q0disj : Disjoint K1 Q0)
    (hDnormQ1 : D ≤ Subgroup.normalizer (Q1 : Set G))
    (hK1DQ1 : K1 ≤ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G))
    (hDQ1Q0 : D ⊔ Q1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hPQ0 : D ⊔ Q1 ⊔ K1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p)
    (hQ1q : IsPGroup q (Q1.subgroupOf (D ⊔ Q1)))
    (hDq' : q ∉ (Nat.card ↥(D.subgroupOf (D ⊔ Q1))).primeFactors)
    (hcopZ : ∀ k ∈ K1, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q1)))
    (hcopDQ1 : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q1))
    (hsolvDQ1 : IsSolvable ↥(D ⊔ Q1)) (hPsolv : IsSolvable ↥(D ⊔ Q1 ⊔ K1))
    (hcond : Kstar ≤ Q0 ∨ ¬ Kstar ≤ Q1)
    (hcap : Q1 ⊓ Subgroup.centralizer (D : Set G) ≤ Q0) :
    False := by
  -- Regular `K₁`-action on `(D ⊔ Q₁)/Q₀` from the `K*`-condition (brick A).
  have hFPF := hFPF_of_kstar_condition hprime_manner hKstarQ hDQ1Mσ hQ1Q hDQ hDnormQ1 hcond
    hKstar_prime hK1DQ1 (le_sup_right.trans hPQ0) hDQ1Q0 hQ0DQ1 hcopZ hsolvDQ1
  -- `⁅Q₁, D⁆ ≤ Q₀` (brick B: B2-core → transfer → B1).
  have hcomm := commutator_le_Q0_of_fpf (q := q) hPsolv hPQ0 hK1DQ1 hK1prime hdisj hK1Q0disj
    (hQ0lt.trans_le le_sup_right) hQ1q hDq' hQ0DQ1 hFPF
  -- `Q₁ ≤ Q₀` (collapse), contradicting `Q₀ < Q₁`.
  haveI := hsolvDQ1
  haveI hsolvQ1 : IsSolvable ↥Q1 :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective (le_sup_right : Q1 ≤ D ⊔ Q1))
  have hle := le_of_commutator_le_of_inf_centralizer_le hQ0lt.le hDnormQ1
    (le_sup_right.trans hDQ1Q0) (le_sup_left.trans hDQ1Q0) hcomm hcopDQ1 (Or.inr hsolvQ1) hcap
  exact absurd (lt_of_lt_of_le hQ0lt hle) (lt_irrefl Q0)

/-- **Step 1 of Theorem 15.2 part (ii)** (mmd L4194): the `K*`-condition is *false*, hence
`K* ⊆ Q₁` and `K* ⊄ Q₀`.  Direct contrapositive of `false_of_kstar_condition_of_lt`: were either
disjunct of `Kstar ≤ Q0 ∨ ¬ Kstar ≤ Q1` to hold, the regular `K₁`-action would collapse `Q₁ ≤ Q₀`,
against `Q₀ < Q₁`.  Supplies the `Kstar ≤ Q₁` premise that brick D feeds back into the engine at the
next chief factor `(Q₁, Q₂)`. -/
theorem kstar_le_Q1_of_inputs [Finite G]
    {Mσ D Q Q1 Q0 Kstar K1 : Subgroup G} {q : ℕ} [Fact q.Prime]
    [(Q0.subgroupOf (D ⊔ Q1)).Normal] [(Q1.subgroupOf (D ⊔ Q1)).Normal]
    (hprime_manner : ∀ k ∈ K1, k ≠ 1 → Subgroup.centralizer ({k} : Set G) ⊓ Mσ = Kstar)
    (hKstarQ : Kstar ≤ Q) (hKstar_prime : ∃ q : ℕ, q.Prime ∧ Nat.card ↥Kstar = q)
    (hDQ1Mσ : D ⊔ Q1 ≤ Mσ) (hQ1Q : Q1 ≤ Q)
    (hQ0DQ1 : Q0 ≤ D ⊔ Q1) (hQ0lt : Q0 < Q1)
    (hDQ : Disjoint D Q) (hdisj : Disjoint (D ⊔ Q1) K1) (hK1Q0disj : Disjoint K1 Q0)
    (hDnormQ1 : D ≤ Subgroup.normalizer (Q1 : Set G))
    (hK1DQ1 : K1 ≤ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G))
    (hDQ1Q0 : D ⊔ Q1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hPQ0 : D ⊔ Q1 ⊔ K1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p)
    (hQ1q : IsPGroup q (Q1.subgroupOf (D ⊔ Q1)))
    (hDq' : q ∉ (Nat.card ↥(D.subgroupOf (D ⊔ Q1))).primeFactors)
    (hcopZ : ∀ k ∈ K1, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q1)))
    (hcopDQ1 : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q1))
    (hsolvDQ1 : IsSolvable ↥(D ⊔ Q1)) (hPsolv : IsSolvable ↥(D ⊔ Q1 ⊔ K1))
    (hcap : Q1 ⊓ Subgroup.centralizer (D : Set G) ≤ Q0) :
    ¬ Kstar ≤ Q0 ∧ Kstar ≤ Q1 := by
  have hkey : ¬ (Kstar ≤ Q0 ∨ ¬ Kstar ≤ Q1) := fun hcond =>
    false_of_kstar_condition_of_lt hprime_manner hKstarQ hKstar_prime hDQ1Mσ hQ1Q hQ0DQ1 hQ0lt
      hDQ hdisj hK1Q0disj hDnormQ1 hK1DQ1 hDQ1Q0 hPQ0 hK1prime hQ1q hDq' hcopZ hcopDQ1 hsolvDQ1
      hPsolv hcond hcap
  rw [not_or, not_not] at hkey
  exact hkey

/-- **Brick D of Theorem 15.2 part (ii)** (mmd L4194): once step 1 has established `K* ⊆ Q₁`, the
chief factor `Q₁` is in fact all of `Q`.  Were `Q₁ < Q`, `exists_chiefFactor_over_normalized` builds
the next chief factor `Q₂/Q₁` (with `Q₁ < Q₂ ≤ Q`, normalized by `D` and `K₁`); the regular-action
engine `false_of_kstar_condition_of_lt` then fires at `(Q₁, Q₂)` — its `K*`-condition holds via the
*left* disjunct `K* ⊆ Q₁` — giving `Q₂ ≤ Q₁`, against `Q₁ < Q₂`.  Hence `Q₁ = Q`.

The `(Q₁, Q₂)`-level engine hypotheses are mechanically derived from the global structural data:
order/coprimality facts descend along `Q₂ ≤ Q` (monotonicity of `Disjoint`, `Nat.Coprime`,
`IsPGroup`, `card_dvd_of_le`); normalization comes from `Q₂`'s construction; the centralizer cap
`Q₂ ⊓ C(D) ≤ Q₁` factors through `Q ⊓ C(D) ≤ Q₁`. -/
theorem Q1_eq_Q_of_inputs [Finite G]
    {M Mσ D Q Q1 Kstar K1 : Subgroup G} {q : ℕ} [Fact q.Prime] [Group.IsNilpotent ↥Q]
    (hprime_manner : ∀ k ∈ K1, k ≠ 1 → Subgroup.centralizer ({k} : Set G) ⊓ Mσ = Kstar)
    (hKstarQ : Kstar ≤ Q) (hKstar_prime : ∃ q : ℕ, q.Prime ∧ Nat.card ↥Kstar = q)
    (hDQMσ : D ⊔ Q ≤ Mσ) (hDQ : Disjoint D Q)
    (hDQK1disj : Disjoint (D ⊔ Q) K1) (hK1Qdisj : Disjoint K1 Q)
    (hK1normD : K1 ≤ Subgroup.normalizer (D : Set G))
    (hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p)
    (hQ_pg : IsPGroup q Q) (hD_q' : q ∉ (Nat.card ↥D).primeFactors)
    (hcopZ : ∀ k ∈ K1, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q)))
    (hcopDQ : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q)) (hsolv : IsSolvable ↥(D ⊔ Q ⊔ K1))
    (hcap : Q ⊓ Subgroup.centralizer (D : Set G) ≤ Q1)
    (hQM : Q ≤ M) (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hDM : D ≤ M) (hK1M : K1 ≤ M)
    (hQ1Q : Q1 ≤ Q) (hKstarQ1 : Kstar ≤ Q1)
    (hDnormQ1 : D ≤ Subgroup.normalizer (Q1 : Set G))
    (hK1normQ1 : K1 ≤ Subgroup.normalizer (Q1 : Set G)) :
    Q1 = Q := by
  by_contra hne
  have hQ1ltQ : Q1 < Q := lt_of_le_of_ne hQ1Q hne
  obtain ⟨Q2, hQ1Q2, hQ2Q, hDnormQ2, hK1normQ2, hQ2normQ1⟩ :=
    exists_chiefFactor_over_normalized hQ1ltQ hQM hMnormQ (le_inf hDM hDnormQ1) (le_inf hK1M hK1normQ1)
  -- (Q₁, Q₂)-level engine hypotheses, descended from the global data.
  have hDQ2Mσ : D ⊔ Q2 ≤ Mσ := (sup_le_sup_left hQ2Q D).trans hDQMσ
  have hQ1DQ2 : Q1 ≤ D ⊔ Q2 := hQ1Q2.le.trans le_sup_right
  have hdisj2 : Disjoint (D ⊔ Q2) K1 := hDQK1disj.mono_left (sup_le_sup_left hQ2Q D)
  have hK1Q1disj : Disjoint K1 Q1 := hK1Qdisj.mono_right hQ1Q
  have hK1DQ2 : K1 ≤ Subgroup.normalizer ((D ⊔ Q2 : Subgroup G) : Set G) :=
    le_normalizer_sup hK1normD hK1normQ2
  have hDQ2normQ1 : D ⊔ Q2 ≤ Subgroup.normalizer (Q1 : Set G) := sup_le hDnormQ1 hQ2normQ1
  have hPnormQ1 : D ⊔ Q2 ⊔ K1 ≤ Subgroup.normalizer (Q1 : Set G) := sup_le hDQ2normQ1 hK1normQ1
  have hcardD : Nat.card ↥(D.subgroupOf (D ⊔ Q2)) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : D ≤ D ⊔ Q2)).toEquiv
  have hDq'2 : q ∉ (Nat.card ↥(D.subgroupOf (D ⊔ Q2))).primeFactors := by rw [hcardD]; exact hD_q'
  have hQ2_pg : IsPGroup q (Q2.subgroupOf (D ⊔ Q2)) := (hQ_pg.to_le hQ2Q).comap_subtype
  have hcopZ2 : ∀ k ∈ K1, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q2)) :=
    fun k hk => (hcopZ k hk).coprime_dvd_right (Subgroup.card_dvd_of_le (sup_le_sup_left hQ2Q D))
  have hcopDQ2 : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q2) :=
    hcopDQ.coprime_dvd_right (Subgroup.card_dvd_of_le hQ2Q)
  haveI := hsolv
  have hsolv2 : IsSolvable ↥(D ⊔ Q2) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective
      ((sup_le_sup_left hQ2Q D).trans (le_sup_left : D ⊔ Q ≤ D ⊔ Q ⊔ K1)))
  have hPsolv2 : IsSolvable ↥(D ⊔ Q2 ⊔ K1) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective
      (sup_le_sup_right (sup_le_sup_left hQ2Q D) K1))
  have hcap2 : Q2 ⊓ Subgroup.centralizer (D : Set G) ≤ Q1 := (inf_le_inf_right _ hQ2Q).trans hcap
  haveI : (Q1.subgroupOf (D ⊔ Q2)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ1DQ2).mpr hDQ2normQ1
  haveI : (Q2.subgroupOf (D ⊔ Q2)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hDnormQ2 Subgroup.le_normalizer)
  exact false_of_kstar_condition_of_lt hprime_manner hKstarQ hKstar_prime hDQ2Mσ hQ2Q hQ1DQ2
    hQ1Q2 hDQ hdisj2 hK1Q1disj hDnormQ2 hK1DQ2 hDQ2normQ1 hPnormQ1 hK1prime hQ2_pg hDq'2
    hcopZ2 hcopDQ2 hsolv2 hPsolv2 (Or.inl hKstarQ1) hcap2

/-- **BG Theorem 15.2 step 3, the chief-factor construction `Q₀ = C_Q(D) ⊴ M`** (mmd L4194).
Given the type-`P₁` data with the `K`-invariant complement `D` of `Q = O_q(M)` in `M_σ`
(`exists_kInvariant_qComplement`), this assembles the minimal chief factor: `Q₀ = C_Q(D)` is
proper in `Q` (`M_σ` not nilpotent), and the minimal normal subgroup `Q₁/Q₀` of `N_M(Q₀)/Q₀`
inside `Q` is shown to equal `Q` (`Q₁_eq_Q_of_inputs`), giving:

* **`M ≤ N_G(Q₀)`** (conjuncts (e)/13-14): `Q = Q₁ ≤ N_G(Q₀)` (the chief factor lives in `N_M(Q₀)`)
  and `K, D ≤ N_G(Q₀)` (`Q₀` is `KD`-invariant), so `M = M_σ K = (Q ⊔ D) ⊔ K ≤ N_G(Q₀)`;
* **`¬ K* ≤ Q₀`** (`kstar_le_Q1_of_inputs`, the regular-action dichotomy);
* **`Q₀ < Q`** (`inf_centralizer_ne_self_of_sup_not_nilpotent`);
* the **lattice-minimality** of `Q` over `Q₀` among `M`-normal subgroups (feeds the elementary
  abelian chief-factor `Q̄ = Q/Q₀` and the chief-factor engine).

The `§14`-gated inputs are folded into the type-`P₁` hypotheses (`hP1`, `hKstar`); `hMσnotnil`
(`M_σ` not nilpotent) is the Theorem 15.2 hypothesis `M_F ≠ M_σ`, `hDq'` (`q ∤ |D|`) the Sylow
fact from `q_not_dvd_index_of_msigma_quotient_isNilpotent`. -/
theorem chiefFactor_Q0_normal_minimal_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar Q D : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hQ : Q = opiCoreInG ({q} : Set ℕ) M)
    (hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M) (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hKstarQ : Kstar ≤ Q) (hQneMσ : Q ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hKne : K ≠ ⊥) (hKMσdisj : Disjoint K (OddOrder.BG.Ch3.S10.Msigma M))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)))
    (hMσnotnil : ¬ Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M))
    (hDq' : q ∉ (Nat.card ↥D).primeFactors)
    (hDMσ : D ≤ OddOrder.BG.Ch3.S10.Msigma M) (hKnormD : K ≤ Subgroup.normalizer (D : Set G))
    (hQDdisj : Disjoint Q D)
    (hcomplD : Subgroup.IsComplement' (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))
      (D.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)))
    (hDnil : Group.IsNilpotent ↥D) (hDne : D ≠ ⊥) :
    M ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
      ¬ Kstar ≤ (Q ⊓ Subgroup.centralizer (D : Set G)) ∧
      (Q ⊓ Subgroup.centralizer (D : Set G)) < Q ∧
      (∀ H : Subgroup G, (Q ⊓ Subgroup.centralizer (D : Set G)) < H → H ≤ Q →
        (H.subgroupOf M).Normal → Q ≤ H) := by
  classical
  set Mσ : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  set Q0 : Subgroup G := Q ⊓ Subgroup.centralizer (D : Set G) with hQ0def
  have hMσM : Mσ ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  haveI : IsSolvable ↥Mσ := solvable_of_solvable_injective (Subgroup.inclusion_injective hMσM)
  have hQpg : IsPGroup q ↥Q := by rw [hQ]; exact isPGroup_opiCoreInG_singleton M
  haveI hQnil : Group.IsNilpotent ↥Q := hQpg.isNilpotent
  have hDM : D ≤ M := hDMσ.trans hMσM
  have hQM : Q ≤ M := hQMσ.trans hMσM
  -- `Q ⊔ D = M_σ` (complement), so `M_σ` not nilpotent gives `Q₀ = C_Q(D) ⊊ Q`.
  have hQDsup : Q ⊔ D = Mσ := by
    have : (Q ⊔ D).subgroupOf Mσ = ⊤ := by
      rw [Subgroup.subgroupOf_sup hQMσ hDMσ]; exact hcomplD.sup_eq_top
    exact le_antisymm (sup_le hQMσ hDMσ) (Subgroup.subgroupOf_eq_top.mp this)
  have hQDnotnil : ¬ Group.IsNilpotent ↥(Q ⊔ D) := by rw [hQDsup]; exact hMσnotnil
  have hQ0ltQ : Q0 < Q :=
    lt_of_le_of_ne inf_le_left (inf_centralizer_ne_self_of_sup_not_nilpotent hQDnotnil)
  have hQ0le : Q0 ≤ Q := hQ0ltQ.le
  -- `Q₀ = C_Q(D)` is `KD`-invariant: `K, D ≤ N_G(Q₀)`.
  have hKNQ : K ≤ Subgroup.normalizer (Q : Set G) := hKM.trans hMnormQ
  have hDNQ : D ≤ Subgroup.normalizer (Q : Set G) := hDM.trans hMnormQ
  have hKDNQ0 : K ⊔ D ≤ Subgroup.normalizer (Q0 : Set G) :=
    sup_le_normalizer_centralizer_inf hKNQ hDNQ hKnormD
  have hKNQ0 : K ≤ Subgroup.normalizer (Q0 : Set G) := le_sup_left.trans hKDNQ0
  have hDNQ0 : D ≤ Subgroup.normalizer (Q0 : Set G) := le_sup_right.trans hKDNQ0
  -- a prime-order subgroup `K₁ ≤ K` and the prime-manner action.
  have hprime := actsPrimeManner_of_typeP hG hM hP1.1 hKM hK hKstar
  have hKcard1 : Nat.card ↥K ≠ 1 := fun hc => hKne (Subgroup.card_eq_one.mp hc)
  obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hKcard1
  haveI : Fact r.Prime := ⟨hr_prime⟩
  obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) r hr_dvd
  set K1 : Subgroup G := Subgroup.zpowers (c : G) with hK1
  have hcK : (c : G) ∈ K := c.2
  have hK1K : K1 ≤ K := by rw [hK1]; exact Subgroup.zpowers_le.mpr hcK
  have hK1M : K1 ≤ M := hK1K.trans hKM
  have hord_coe : orderOf (c : G) = r := by rw [Subgroup.orderOf_coe, hc_ord]
  have hcardK1 : Nat.card ↥K1 = r := by rw [hK1, Nat.card_zpowers, hord_coe]
  have hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p := ⟨r, hr_prime, hcardK1⟩
  have hK1normD : K1 ≤ Subgroup.normalizer (D : Set G) := hK1K.trans hKnormD
  have hK1NQ0 : K1 ≤ Subgroup.normalizer (Q0 : Set G) := hK1K.trans hKNQ0
  -- the prime-manner action restricted to `K₁`.
  have hprimeK1 : ∀ k ∈ K1, k ≠ 1 →
      Subgroup.centralizer ({k} : Set G) ⊓ Mσ = Kstar := fun k hk => hprime k (hK1K hk)
  have hKstar_prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥Kstar = p :=
    ⟨Nat.card ↥Kstar, kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar, rfl⟩
  -- `q ∤ |D|`, hence `Coprime |D| |Q|` (`Q` a `q`-group).
  have hqD : ¬ q ∣ Nat.card ↥D := fun hdvd =>
    hDq' (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)
  have hcopDQ : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    rw [hn]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simpa using Nat.coprime_one_right _
    · rw [Nat.coprime_pow_right_iff h0]
      exact ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hqD).symm
  -- coprimality of cyclic `⟨k⟩ ≤ K` with `|M_σ|`, restricted along `D ⊔ Q ≤ M_σ`.
  have hcopKMσ : ∀ k ∈ K, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k))
      (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) := fun k hk =>
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hk))
  -- set up the ambient `N = M ⊓ N_G(Q₀)` and the nontrivial chain top `T = N_Q(Q₀)`.
  set N : Subgroup G := M ⊓ Subgroup.normalizer (Q0 : Set G) with hNdef
  have hQ0T : Q0 < Q ⊓ Subgroup.normalizer (Q0 : Set G) :=
    lt_inf_normalizer_of_lt_of_isNilpotent hQ0ltQ
  have hTN : Q ⊓ Subgroup.normalizer (Q0 : Set G) ≤ N := inf_le_inf hQM le_rfl
  have hNnormT : N ≤ Subgroup.normalizer
      ((Q ⊓ Subgroup.normalizer (Q0 : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf (inf_le_left.trans hMnormQ) (inf_le_right.trans Subgroup.le_normalizer)
  have hTnorm : ((Q ⊓ Subgroup.normalizer (Q0 : Set G)).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).mpr hNnormT
  obtain ⟨Q1, hQ0Q1, hQ1T, hQ1normalN, hQ1min⟩ := exists_minimal_normalOver hQ0T hTnorm
  have hQ1Q : Q1 ≤ Q := hQ1T.trans inf_le_left
  have hQ1NQ0 : Q1 ≤ Subgroup.normalizer (Q0 : Set G) := hQ1T.trans inf_le_right
  -- `D, K₁ ≤ N` and `N ≤ N_G(Q₁)`.
  have hDN : D ≤ N := le_inf hDM hDNQ0
  have hK1N : K1 ≤ N := le_inf hK1M hK1NQ0
  have hNnormQ1 : N ≤ Subgroup.normalizer (Q1 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hQ1T.trans hTN)).mp hQ1normalN
  have hDnormQ1 : D ≤ Subgroup.normalizer (Q1 : Set G) := hDN.trans hNnormQ1
  have hK1normQ1 : K1 ≤ Subgroup.normalizer (Q1 : Set G) := hK1N.trans hNnormQ1
  -- structural facts shared by `kstar_le_Q1_of_inputs` and `Q1_eq_Q_of_inputs`.
  have hDQ : Disjoint D Q := hQDdisj.symm
  have hDQMσ : D ⊔ Q ≤ Mσ := sup_le hDMσ hQMσ
  have hDQ1Mσ : D ⊔ Q1 ≤ Mσ := sup_le hDMσ (hQ1Q.trans hQMσ)
  have hQ0DQ1 : Q0 ≤ D ⊔ Q1 := hQ0Q1.le.trans le_sup_right
  have hdisjQ1 : Disjoint (D ⊔ Q1) K1 :=
    (hKMσdisj.symm.mono_left hDQ1Mσ).mono_right hK1K
  have hK1Q0disj : Disjoint K1 Q0 := (hKMσdisj.mono_left hK1K).mono_right (hQ0le.trans hQMσ)
  have hK1DQ1 : K1 ≤ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G) :=
    le_normalizer_sup hK1normD hK1normQ1
  have hDQ1Q0 : D ⊔ Q1 ≤ Subgroup.normalizer (Q0 : Set G) := sup_le hDNQ0 hQ1NQ0
  have hPQ0 : D ⊔ Q1 ⊔ K1 ≤ Subgroup.normalizer (Q0 : Set G) := sup_le hDQ1Q0 hK1NQ0
  have hQ1q : IsPGroup q (Q1.subgroupOf (D ⊔ Q1)) := (hQpg.to_le hQ1Q).comap_subtype
  have hcardD1 : Nat.card ↥(D.subgroupOf (D ⊔ Q1)) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : D ≤ D ⊔ Q1)).toEquiv
  have hDq'1 : q ∉ (Nat.card ↥(D.subgroupOf (D ⊔ Q1))).primeFactors := by rw [hcardD1]; exact hDq'
  have hcopZ1 : ∀ k ∈ K1, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q1)) :=
    fun k hk => (hcopKMσ k (hK1K hk)).coprime_dvd_right
      (Subgroup.card_dvd_of_le (le_trans hDQ1Mσ le_rfl))
  have hcopDQ1 : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q1) :=
    hcopDQ.coprime_dvd_right (Subgroup.card_dvd_of_le hQ1Q)
  have hsolvDQ1 : IsSolvable ↥(D ⊔ Q1) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective (hDQ1Mσ.trans hMσM))
  have hPsolvQ1 : IsSolvable ↥(D ⊔ Q1 ⊔ K1) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective
      (sup_le (hDQ1Mσ.trans hMσM) hK1M))
  have hcapQ1 : Q1 ⊓ Subgroup.centralizer (D : Set G) ≤ Q0 := by
    rw [hQ0def]; exact inf_le_inf_right _ hQ1Q
  haveI hQ0normDQ1 : (Q0.subgroupOf (D ⊔ Q1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0DQ1).mpr hDQ1Q0
  haveI hQ1normDQ1 : (Q1.subgroupOf (D ⊔ Q1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right)).mpr
      (sup_le hDnormQ1 Subgroup.le_normalizer)
  -- `¬ K* ≤ Q₀` and `K* ≤ Q₁`.
  obtain ⟨hKstarNotQ0, hKstarQ1⟩ := kstar_le_Q1_of_inputs hprimeK1 hKstarQ hKstar_prime hDQ1Mσ hQ1Q
    hQ0DQ1 hQ0Q1 hDQ hdisjQ1 hK1Q0disj hDnormQ1 hK1DQ1 hDQ1Q0 hPQ0 hK1prime hQ1q hDq'1
    hcopZ1 hcopDQ1 hsolvDQ1 hPsolvQ1 hcapQ1
  -- `Q₁ = Q` (brick D).
  have hcopZQ : ∀ k ∈ K1, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q)) :=
    fun k hk => (hcopKMσ k (hK1K hk)).coprime_dvd_right
      (Subgroup.card_dvd_of_le (hDQMσ.trans le_rfl))
  have hsolvDQK1 : IsSolvable ↥(D ⊔ Q ⊔ K1) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective
      (sup_le (hDQMσ.trans hMσM) hK1M))
  have hcapQ : Q ⊓ Subgroup.centralizer (D : Set G) ≤ Q1 := by rw [← hQ0def]; exact hQ0Q1.le
  have hQ1eqQ : Q1 = Q :=
    Q1_eq_Q_of_inputs hprimeK1 hKstarQ hKstar_prime hDQMσ hDQ
      ((hKMσdisj.symm.mono_left hDQMσ).mono_right hK1K) (hKMσdisj.mono_left hK1K |>.mono_right hQMσ)
      hK1normD hK1prime hQpg hDq' hcopZQ hcopDQ hsolvDQK1 hcapQ hQM hMnormQ hDM hK1M hQ1Q hKstarQ1
      hDnormQ1 hK1normQ1
  -- `Q ≤ N_G(Q₀)` (from `Q = Q₁`), hence `M = M_σ K ≤ N_G(Q₀)`.
  have hQNQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G) := hQ1eqQ ▸ hQ1NQ0
  have hMσNQ0 : Mσ ≤ Subgroup.normalizer (Q0 : Set G) := by
    rw [← hQDsup]; exact sup_le hQNQ0 hDNQ0
  -- `M = M_σ ⊔ K` (type-`P₁` complement, `M_σ = M'`).
  have hMσderived : Mσ = derivedInG M := typeP1_msigma_eq_derivedInG hG hM hP1 hKM hK hKstar
  obtain ⟨hcomplK, _, _⟩ := S14.typeP_duality hG hM hP1.1 hKM hK hKstar
  have hMeq : Mσ ⊔ K = M := by
    have hsup : (Mσ.subgroupOf M) ⊔ (K.subgroupOf M) = ⊤ := by
      rw [hMσderived]; exact hcomplK.sup_eq_top
    have h := congrArg (Subgroup.map M.subtype) hsup
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hMσM, inf_eq_left.mpr hKM, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
  have hMNQ0 : M ≤ Subgroup.normalizer (Q0 : Set G) := by
    rw [← hMeq]; exact sup_le hMσNQ0 hKNQ0
  -- minimality of `Q` over `Q₀` among `M`-normal subgroups (from `Q₁ = Q`, `N = M`).
  have hNeqM : N = M := by rw [hNdef]; exact inf_eq_left.mpr hMNQ0
  refine ⟨hMNQ0, hKstarNotQ0, hQ0ltQ, ?_⟩
  intro H hH1 hH2 hH3
  have hH3' : (H.subgroupOf N).Normal := by rw [hNeqM]; exact hH3
  have := hQ1min H hH1 (hQ1eqQ ▸ hH2) hH3'
  rwa [hQ1eqQ] at this

/-- **BG Theorem 15.2 step 3, the elementary abelian chief factor `Q̄ = Q/Q₀`** (mmd L4194-4196,
"`Q̄` is a minimal normal subgroup of `M/Q₀` and is elementary abelian of order `q^p`").  Given the
lattice-minimality of `Q` over `Q₀` among `M`-normal subgroups (output of
`chiefFactor_Q0_normal_minimal_of_inputs`) with `Q ⊴ M`, `Q₀ ⊴ M`, `Q₀ < Q` and `Q` a `q`-group,
the chief factor `Q/Q₀` is elementary abelian (and nontrivial).

Proof: the image `E = Q/Q₀` of `Q` in the solvable quotient `M/Q₀` is a *minimal normal* subgroup —
the lattice-minimality `hmin` transfers along the correspondence `comap (mk' Q₀)` — so by Isaacs
Theorem 3.11 (`solvable_minimal_normal_isElementaryAbelian`) it is elementary abelian for some
prime; the first isomorphism theorem (`quotientKerEquivRange` of `↥Q → M/Q₀`) identifies `E` with
`↥Q ⧸ Q₀.subgroupOf Q`, and as a quotient of the `q`-group `Q` that prime is `q`.

Discharges the `hEA`/`hNT` hypotheses of `chiefFactor_card_and_commutator_of_inputs`. -/
theorem isElementaryAbelian_chiefFactor_of_minimalNormal [Finite G]
    {M Q Q0 : Subgroup G} {q : ℕ} [Fact q.Prime] [IsSolvable ↥M] [(Q0.subgroupOf Q).Normal]
    (hQ0Q : Q0 < Q) (hQM : Q ≤ M) (hQpg : IsPGroup q ↥Q)
    (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hMnormQ0 : M ≤ Subgroup.normalizer (Q0 : Set G))
    (hmin : ∀ H : Subgroup G, Q0 < H → H ≤ Q → (H.subgroupOf M).Normal → Q ≤ H) :
    OddOrder.GroupTheory.IsElementaryAbelian q (↥Q ⧸ Q0.subgroupOf Q) ∧
      Nontrivial (↥Q ⧸ Q0.subgroupOf Q) := by
  classical
  have hQ0M : Q0 ≤ M := hQ0Q.le.trans hQM
  haveI hQ0nM : (Q0.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0M).mpr hMnormQ0
  haveI hQnM : (Q.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMnormQ
  -- `Nontrivial Q̄` (`Q₀ < Q`).
  obtain ⟨x0, hx0Q, hx0Q0⟩ := (SetLike.lt_iff_le_and_exists.mp hQ0Q).2
  haveI hNT : Nontrivial (↥Q ⧸ Q0.subgroupOf Q) := by
    refine ⟨QuotientGroup.mk ⟨x0, hx0Q⟩, 1, ?_⟩
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hx0Q0
  -- ambient quotient `M/Q₀` and the chief-factor image `E = (Q ↾ M)·Q₀ / Q₀`.
  set N0 : Subgroup ↥M := Q0.subgroupOf M with hN0def
  set E : Subgroup (↥M ⧸ N0) := (Q.subgroupOf M).map (QuotientGroup.mk' N0) with hEdef
  have hN0QM : N0 ≤ Q.subgroupOf M := by rw [hN0def]; exact Subgroup.comap_mono hQ0Q.le
  -- `E` is minimal normal in the solvable `M/Q₀`.
  have hEmin : OddOrder.Isaacs.Ch02.IsMinimalNormal E := by
    refine ⟨hQnM.map (QuotientGroup.mk' N0) (QuotientGroup.mk'_surjective N0), ?_, ?_⟩
    · -- `E ≠ ⊥`.
      intro hEbot
      rw [hEdef, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hEbot
      have hQle : Q ≤ Q0 := by
        intro x hxQ
        have hxM : x ∈ M := hQM hxQ
        have hmem : (⟨x, hxM⟩ : ↥M) ∈ Q0.subgroupOf M :=
          hEbot (Subgroup.mem_subgroupOf.mpr hxQ)
        exact Subgroup.mem_subgroupOf.mp hmem
      exact hQ0Q.ne (le_antisymm hQ0Q.le hQle)
    · -- minimality via the correspondence.
      intro N' hN'norm hN'E
      haveI := hN'norm
      set N'' : Subgroup ↥M := Subgroup.comap (QuotientGroup.mk' N0) N' with hN''def
      have hN0N'' : N0 ≤ N'' := QuotientGroup.le_comap_mk' N0 N'
      have hN''QM : N'' ≤ Q.subgroupOf M := by
        have hsub : N'' ≤ Subgroup.comap (QuotientGroup.mk' N0) E := Subgroup.comap_mono hN'E
        rwa [hEdef, QuotientGroup.comap_map_mk', sup_eq_right.mpr hN0QM] at hsub
      set H : Subgroup G := N''.map M.subtype with hHdef
      have hHsubM : H.subgroupOf M = N'' :=
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective N''
      have hQ0H : Q0 ≤ H := by
        rw [hHdef]
        intro y hy
        have hyM : y ∈ M := hQ0M hy
        exact ⟨⟨y, hyM⟩, hN0N'' (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
      have hHQ : H ≤ Q := by
        rw [hHdef]
        rintro _ ⟨w, hwN'', rfl⟩
        exact (Subgroup.mem_subgroupOf.mp (hN''QM hwN''))
      have hHnorm : (H.subgroupOf M).Normal := by rw [hHsubM]; infer_instance
      have hN'eq : N' = N''.map (QuotientGroup.mk' N0) := by
        rw [hN''def, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N0)]
      rcases eq_or_lt_of_le hQ0H with hHeq | hHlt
      · -- `H = Q₀`, so `N'' = N0`, `N' = ⊥`.
        left
        have hHQ0 : H = Q0 := hHeq.symm
        have hN''N0 : N'' = N0 := by rw [← hHsubM, hHQ0]
        rw [hN'eq, hN''N0, Subgroup.map_eq_bot_iff]
        exact (QuotientGroup.ker_mk' N0).ge
      · -- `Q₀ < H`, so `hmin` forces `H = Q`, `N'' = Q.subgroupOf M`, `N' = E`.
        right
        have hHeqQ : H = Q := le_antisymm hHQ (hmin H hHlt hHQ hHnorm)
        have hN''QMeq : N'' = Q.subgroupOf M := by rw [← hHsubM, hHeqQ]
        rw [hN'eq, hN''QMeq, hEdef]
  -- elementary abelian for some prime `p`.
  obtain ⟨p, hp_prime, hEAp⟩ :=
    OddOrder.Isaacs.Ch03.solvable_minimal_normal_isElementaryAbelian hEmin
  -- the first isomorphism `↥Q ⧸ Q₀ ≃* ↥E`.
  set f : ↥Q →* (↥M ⧸ N0) := (QuotientGroup.mk' N0).comp (Subgroup.inclusion hQM) with hfdef
  have hfker : f.ker = Q0.subgroupOf Q := by
    ext z
    rw [hfdef, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hN0def, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hfrange : f.range = E := by
    rw [hfdef, MonoidHom.range_comp, Subgroup.inclusion_range, hEdef]
  let e : (↥Q ⧸ Q0.subgroupOf Q) ≃* ↥E :=
    (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hfrange))
  -- transport elementary abelian to `Q̄`, and identify the prime as `q`.
  have hEAp' : OddOrder.GroupTheory.IsElementaryAbelian p (↥Q ⧸ Q0.subgroupOf Q) :=
    OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv e.symm hEAp
  have hpgp : IsPGroup p (↥Q ⧸ Q0.subgroupOf Q) := hEAp'.isPGroup
  have hpgq : IsPGroup q (↥Q ⧸ Q0.subgroupOf Q) := hQpg.to_quotient (Q0.subgroupOf Q)
  haveI : Finite (↥Q ⧸ Q0.subgroupOf Q) := inferInstance
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hpq : p = q := by
    obtain ⟨a, ha⟩ := hpgp.exists_card_eq
    obtain ⟨b, hb⟩ := hpgq.exists_card_eq
    have hqdvd : q ∣ Nat.card (↥Q ⧸ Q0.subgroupOf Q) := by
      rw [hb]
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · rw [h0, pow_zero] at hb
        exact absurd hb (Finite.one_lt_card_iff_nontrivial.mpr hNT).ne'
      · exact dvd_pow_self q h0.ne'
    rw [ha] at hqdvd
    exact ((Nat.prime_dvd_prime_iff_eq Fact.out hp_prime).mp
      ((Fact.out : q.Prime).dvd_of_dvd_pow hqdvd)).symm
  exact ⟨hpq ▸ hEAp', hNT⟩

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
open scoped commutatorElement in
/-- **Theorem 15.2 step 4, the fixed-point-free fact `C_{Q̄}(D) = 1`** (Proposition 1.5(d), mmd
L4196).  With `Q₀ = C_Q(D)` and `D` acting coprimely on `Q` (`D ≤ N_G(Q)`, `Q, D ≤ N_G(Q₀)`), `D`
acts fixed-point-freely on `Q̄ = Q/Q₀`: any `x ∈ Q` whose class is centralized by `D`
(`⁅d, x⁆ ∈ Q₀` for every `d ∈ D`) already lies in `Q₀`.

This is the `C_M(U) = 1` hypothesis (`hCU`) of BG Theorem 3.10
(`prime_card_complement_of_frobenius_conj`) in the `M = Q̄`, `U = D̄` instantiation that yields
`|K|` prime (Theorem 15.2 conjunct (f)): a class of `Q̄` centralizing `D̄` lifts to a representative
`x` with `⁅d, x⁆ ∈ Q₀` for all `d ∈ D`, forced by this lemma into `Q₀`, i.e. the class is trivial.

Proof (mirrors `fpf_of_centralizer_inf_le`, but the fixed-point source is the *definitional*
`C_Q(D) = Q₀` rather than a separate centralizer bound, and no generator lift is needed since the
whole group `D` acts): the `D`-fixed points of `Q/Q₀` push forward from `C_{↥Q}(D) = Q₀`
(`fixedPointsOfMulAut_quotientMulAutHom_eq_map`, Proposition 1.5(d)), hence are trivial.  The
bracket conversion `⁅a, x⁻¹⁆ = x⁻¹ ⁅a, x⁆⁻¹ x` uses `x ∈ Q ≤ N_G(Q₀)`. -/
theorem mem_centralizer_of_centralizes_quotient [Finite G]
    {Q D Q0 : Subgroup G} (hQ0 : Q0 = Q ⊓ Subgroup.centralizer (D : Set G))
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hQQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G))
    (hDQ0 : D ≤ Subgroup.normalizer (Q0 : Set G))
    (hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q))
    (hSolv : IsSolvable ↥D ∨ IsSolvable ↥Q)
    {x : G} (hxQ : x ∈ Q) (hfix : ∀ d ∈ D, ⁅d, x⁆ ∈ Q0) :
    x ∈ Q0 := by
  have hQ0Q : Q0 ≤ Q := by rw [hQ0]; exact inf_le_left
  set φ : ↥D →* MulAut ↥Q :=
    (Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hDQ) with hφ
  haveI hQ0_normal : (Q0.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0Q).mpr hQQ0
  -- `Q₀.subgroupOf Q` is `D`-invariant.
  have hMinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (Q0.subgroupOf Q) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    show (a : G) * (y : G) * (a : G)⁻¹ ∈ Q0
    exact (Subgroup.mem_normalizer_iff.mp (hDQ0 a.2) (y : G)).mp hy
  -- Proposition 1.5(d): the quotient fixed points push forward from `C_{↥Q}(D) = Q₀`, hence `⊥`.
  have hbridge : (Subgroup.fixedPointsOfMulAut φ).map Q.subtype =
      Subgroup.centralizer (D : Set G) ⊓ Q :=
    OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hDQ
  have hfp_le : Subgroup.fixedPointsOfMulAut φ ≤ Q0.subgroupOf Q := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have hym : (Q.subtype y) ∈ (Subgroup.fixedPointsOfMulAut φ).map Q.subtype := ⟨y, hy, rfl⟩
    rw [hbridge] at hym
    obtain ⟨hcent, _⟩ := Subgroup.mem_inf.mp hym
    rw [hQ0]; exact Subgroup.mem_inf.mpr ⟨y.2, hcent⟩
  have hmap := OddOrder.BG.Ch1.S03h.fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := φ) hcop hSolv hMinv
  have hfpbot : Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv) = ⊥ := by
    rw [hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hfp_le
  -- The class of `x` is `D`-fixed (each `a ∈ D` fixes it, by the premise), hence trivial.
  have hxN : x ∈ Subgroup.normalizer (Q0 : Set G) := hQQ0 hxQ
  have hxbar : QuotientGroup.mk' (Q0.subgroupOf Q) ⟨x, hxQ⟩ ∈
      Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv) := by
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    show ((a : G) * x * (a : G)⁻¹)⁻¹ * x ∈ Q0
    have h1 : ⁅(a : G), x⁆ ∈ Q0 := hfix a a.2
    have h2 : ((a : G) * x * (a : G)⁻¹)⁻¹ * x = x⁻¹ * ⁅(a : G), x⁆⁻¹ * (x⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem hxN)
      (⁅(a : G), x⁆⁻¹)).mp (Q0.inv_mem h1)
  rw [hfpbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hxbar
  exact hxbar

/-- **Theorem 15.2 step (c)(d) — `M_σ/Q` is nilpotent** (mmd L4192, "`K` acts regularly on `M_σ/Q`,
therefore by Theorem 3.7 (applied to `K₁M_σ/Q`), `M_σ/Q` is nilpotent").  In the type-`P` setting
with `K` a Hall `κ`-subgroup, `K* = C_{M_σ}(K) ⊆ Q = O_q(M)` (step 2), so `K` acts fixed-point-freely
on `M_σ/Q` (Proposition 1.5(d): the fixed classes lift to `C_{M_σ}(k) = K* ⊆ Q`).  Theorem 3.7
applied to a prime-order `K₁ ≤ K` makes `M_σ/Q` nilpotent.

The FPF condition for `M_σ/Q` is `fpf_of_centralizer_inf_le_general` (`A = M_σ`, `Q₀ = Q`) with the
prime-manner input `C_G(k) ⊓ M_σ = K* ≤ Q` (`actsPrimeManner_of_typeP` + `hKstarQ`); the nilpotence
of `M_σ/Q` is then `isNilpotent_quotient_of_regular_general` (`N = M_σ`, `Q₀ = Q`, `K₁` of prime
order in `K`).  The disjointness/normalizer data comes from `K` complementing `M_σ` in `M`
(`hcompl`, `hcop`) and `Q ⊴ M` (`hMnormQ`, `hQMσ`).  Gated only through `§14`/structural inputs
(`hP`, `hKstarQ`, `hQneMσ`), all already discharged. -/
theorem msigma_quotient_isNilpotent_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar Q : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M) (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hKstarQ : Kstar ≤ Q) (hQneMσ : Q ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hKne : K ≠ ⊥)
    (hKMσdisj : Disjoint K (OddOrder.BG.Ch3.S10.Msigma M))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)))
    [(Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal] :
    Group.IsNilpotent (↥(OddOrder.BG.Ch3.S10.Msigma M) ⧸
      Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) := by
  classical
  set Mσ : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  have hMσM : Mσ ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hMnormMσ : M ≤ Subgroup.normalizer (Mσ : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M
  -- the prime-manner action `C_G(x) ⊓ M_σ = K*` for `x ∈ K#`.
  have hprime := actsPrimeManner_of_typeP hG hM hP hKM hK hKstar
  -- `K₁ ≤ K` of prime order (Cauchy in `↥K`).
  have hKcard1 : Nat.card ↥K ≠ 1 := fun hc => hKne (Subgroup.card_eq_one.mp hc)
  obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hKcard1
  haveI : Fact r.Prime := ⟨hr_prime⟩
  obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) r hr_dvd
  set K1 : Subgroup G := Subgroup.zpowers (c : G) with hK1
  have hcK : (c : G) ∈ K := c.2
  have hK1K : K1 ≤ K := by rw [hK1]; exact Subgroup.zpowers_le.mpr hcK
  have hK1M : K1 ≤ M := hK1K.trans hKM
  have hord_coe : orderOf (c : G) = r := by rw [Subgroup.orderOf_coe, hc_ord]
  have hcardK1 : Nat.card ↥K1 = r := by rw [hK1, Nat.card_zpowers, hord_coe]
  have hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p := ⟨r, hr_prime, hcardK1⟩
  -- structural facts for `isNilpotent_quotient_of_regular_general` (`N = M_σ`, `Q₀ = Q`, `K₁`).
  have hQltMσ : Q < Mσ := lt_of_le_of_ne hQMσ hQneMσ
  have hMσK1solv : IsSolvable ↥(Mσ ⊔ K1) := by
    haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
    exact solvable_of_solvable_injective (Subgroup.inclusion_injective (sup_le hMσM hK1M))
  have hMσK1normQ : Mσ ⊔ K1 ≤ Subgroup.normalizer (Q : Set G) := sup_le (hMσM.trans hMnormQ)
    (hK1M.trans hMnormQ)
  have hK1normMσ : K1 ≤ Subgroup.normalizer (Mσ : Set G) := hK1M.trans hMnormMσ
  have hMσK1disj : Disjoint Mσ K1 := (hKMσdisj.symm).mono_right hK1K
  have hK1Qdisj : Disjoint K1 Q := (hKMσdisj.mono_left hK1K).mono_right hQMσ
  -- the FPF condition `k·x⁻¹·k⁻¹·x ∈ Q ⟹ x ∈ Q` for `k ∈ K₁#`.
  have hFPF : ∀ k ∈ K1, k ≠ 1 → ∀ x ∈ Mσ, k * x⁻¹ * k⁻¹ * x ∈ Q → x ∈ Q := by
    intro k hkK1 hk1 x hxMσ hpre
    have hkK : k ∈ K := hK1K hkK1
    -- `C_G(k) ⊓ M_σ = K* ≤ Q`.
    have hCk : Subgroup.centralizer ({k} : Set G) ⊓ Mσ ≤ Q := by
      rw [hprime k hkK hk1]; exact hKstarQ
    -- coprime `(|⟨k⟩|, |M_σ|)`: `|⟨k⟩| ∣ |K|` coprime `|M_σ|`.
    have hcopk : Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥Mσ) :=
      hcop.coprime_dvd_left (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hkK))
    have hkM : k ∈ M := hKM hkK
    have hk_normMσ : k ∈ Subgroup.normalizer (Mσ : Set G) := hMnormMσ hkM
    have hk_normQ : k ∈ Subgroup.normalizer (Q : Set G) := hMnormQ hkM
    have hMσnormQ : Mσ ≤ Subgroup.normalizer (Q : Set G) := hMσM.trans hMnormQ
    haveI : IsSolvable ↥Mσ :=
      have : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
      solvable_of_solvable_injective (Subgroup.inclusion_injective hMσM)
    exact fpf_of_centralizer_inf_le_general (k := k) hk_normMσ hk_normQ hMσnormQ hQMσ hcopk
      (Or.inr inferInstance) hCk x hxMσ hpre
  exact isNilpotent_quotient_of_regular_general hMσK1solv hMσK1normQ hK1normMσ hK1prime
    hMσK1disj hK1Qdisj hQltMσ hFPF

/-- **A nilpotent group with trivial `q`-core is a `q'`-group** (`§14`-independent, reusable):
if `O_q(H) = ⊥` for a finite nilpotent `H`, then `q ∤ |H|`.  The Sylow `q`-subgroup of a nilpotent
group is normal (`Group.normalizerCondition_of_isNilpotent`), hence equals `O_q(H)`
(`Sylow.eq_opCore_of_normal`); if that is `⊥` then `q ∤ |H|`. -/
theorem not_dvd_card_of_opCore_eq_bot {H : Type*} [Group H] [Finite H] {q : ℕ} [Fact q.Prime]
    [Group.IsNilpotent H] (hbot : OddOrder.Isaacs.Ch01.opCore q H = ⊥) : ¬ q ∣ Nat.card H := by
  intro hdvd
  obtain ⟨P⟩ := Sylow.nonempty (p := q) (G := H)
  have hPnorm : (P : Subgroup H).Normal :=
    Sylow.normal_of_normalizerCondition Group.normalizerCondition_of_isNilpotent P
  have hPcore : (P : Subgroup H) = OddOrder.Isaacs.Ch01.opCore q H :=
    OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal P hPnorm
  exact (OddOrder.Isaacs.Ch07.Sylow.ne_bot_of_dvd_card hdvd P) (hPcore.trans hbot)

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Theorem 15.2 step (c) — `Q = O_q(M)` is the Sylow `q`-subgroup of `M_σ`** (mmd L4192, the
implicit content of "choose a complement `D` of `Q` in `M_σ`"): with `M_σ/Q` nilpotent (step (c)(d),
`msigma_quotient_isNilpotent_of_inputs`) and `Q = O_q(M)` the maximal normal `q`-subgroup of `M`,
the index `[M_σ : Q]` is coprime to `q`, i.e. `Q` is a Hall `{q}`-subgroup (= normal Sylow `q`) of
`M_σ`.

Argument: were `q ∣ [M_σ : Q]`, the (characteristic, since `M_σ/Q` is nilpotent) `q`-core
`R̄ = O_q(M_σ/Q)` would be nontrivial; its preimage `R` in `M_σ` is a `q`-group properly above `Q`,
and `R.map M_σ.subtype ⊴ M` (the `q`-core `R̄` is characteristic, so preserved by the `M`-conjugation
automorphisms of `M_σ/Q`; `M` normalizes `M_σ` and `Q`).  A normal `q`-subgroup of `M` lies in
`O_q(M) = Q`, forcing `R = Q`, i.e. `R̄ = ⊥` — contradiction.  Hence `O_q(M_σ/Q) = ⊥`, and
`not_dvd_card_of_opCore_eq_bot` gives `q ∤ [M_σ : Q]`. -/
theorem q_not_dvd_index_of_msigma_quotient_isNilpotent [Finite G]
    {M Mσ Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hQMσ : Q ≤ Mσ) (hMσM : Mσ ≤ M) (hQpg : IsPGroup q ↥Q)
    (hMnormMσ : M ≤ Subgroup.normalizer (Mσ : Set G))
    (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hQmax : ∀ R : Subgroup G, R ≤ M → (R.subgroupOf M).Normal → IsPGroup q ↥R → R ≤ Q)
    [hQn : (Q.subgroupOf Mσ).Normal]
    (hNil : Group.IsNilpotent (↥Mσ ⧸ Q.subgroupOf Mσ)) :
    ¬ q ∣ (Q.subgroupOf Mσ).index := by
  classical
  haveI := hNil
  set Cq : Subgroup (↥Mσ ⧸ Q.subgroupOf Mσ) := OddOrder.Isaacs.Ch01.opCore q (↥Mσ ⧸ Q.subgroupOf Mσ)
    with hCq
  -- It suffices to show `Cq = ⊥` (then `q ∤ |Mσ/Q| = [Mσ:Q]`).
  suffices hbot : Cq = ⊥ by
    have h := not_dvd_card_of_opCore_eq_bot (H := ↥Mσ ⧸ Q.subgroupOf Mσ) (q := q) hbot
    rwa [show Nat.card (↥Mσ ⧸ Q.subgroupOf Mσ) = (Q.subgroupOf Mσ).index from rfl] at h
  -- `R := preimage of Cq in ↥Mσ`, a `q`-group containing `Q.subgroupOf Mσ`.
  set R : Subgroup ↥Mσ := Cq.comap (QuotientGroup.mk' (Q.subgroupOf Mσ)) with hR
  set RG : Subgroup G := R.map Mσ.subtype with hRG
  have hRG_le_Mσ : RG ≤ Mσ := Subgroup.map_subtype_le _
  have hRG_le_M : RG ≤ M := hRG_le_Mσ.trans hMσM
  have hmem : ∀ x : G, x ∈ RG ↔
      ∃ hx : x ∈ Mσ, QuotientGroup.mk' (Q.subgroupOf Mσ) ⟨x, hx⟩ ∈ Cq := by
    intro x
    constructor
    · rintro ⟨z, hzR, rfl⟩
      have : QuotientGroup.mk' (Q.subgroupOf Mσ) z ∈ Cq := Subgroup.mem_comap.mp hzR
      exact ⟨z.2, this⟩
    · rintro ⟨hx, hxC⟩
      exact ⟨⟨x, hx⟩, Subgroup.mem_comap.mpr hxC, rfl⟩
  have hQsub_le_R : Q.subgroupOf Mσ ≤ R := by
    intro x hx
    rw [hR, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Cq.one_mem
  -- `R` is a `q`-group: extension of the `q`-group `Q.subgroupOf Mσ` by the `q`-group `Cq`.
  have hQpg' : IsPGroup q ↥(Q.subgroupOf Mσ) :=
    hQpg.comap_of_injective (Subgroup.subtype Mσ) Mσ.subtype_injective
  have hCq_pg : IsPGroup q ↥Cq := OddOrder.Isaacs.Ch01.opCore_isPGroup q _
  have hR_pg : IsPGroup q ↥R := by
    -- the map `g : ↥R → Cq`, `r ↦ [r]`, is surjective with kernel `(Q.subgroupOf Mσ).subgroupOf R`.
    have hmem_Cq : ∀ r : ↥R, QuotientGroup.mk' (Q.subgroupOf Mσ) (R.subtype r) ∈ Cq := fun r =>
      Subgroup.mem_comap.mp r.2
    set g : ↥R →* ↥Cq :=
      ((QuotientGroup.mk' (Q.subgroupOf Mσ)).comp R.subtype).codRestrict Cq hmem_Cq with hg
    have hgsurj : Function.Surjective g := by
      rintro ⟨w, hw⟩
      obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective w
      have hzmem : z ∈ R := by
        rw [hR, Subgroup.mem_comap]; rw [← hz] at hw; exact hw
      refine ⟨⟨z, hzmem⟩, Subtype.ext ?_⟩
      rw [hg]
      show (QuotientGroup.mk' (Q.subgroupOf Mσ) (R.subtype ⟨z, hzmem⟩) : ↥Mσ ⧸ Q.subgroupOf Mσ) = w
      rw [QuotientGroup.mk'_apply]; exact hz
    have hgval : ∀ r : ↥R, (g r : ↥Mσ ⧸ Q.subgroupOf Mσ)
        = QuotientGroup.mk' (Q.subgroupOf Mσ) (R.subtype r) := fun r => rfl
    have hgker : g.ker = (Q.subgroupOf Mσ).subgroupOf R := by
      ext r
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        ← Subtype.coe_inj, hgval, OneMemClass.coe_one, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    rw [IsPGroup.iff_card]
    have hkpg : IsPGroup q ↥g.ker := by
      rw [hgker]
      exact hQpg'.of_equiv (Subgroup.subgroupOfEquivOfLe hQsub_le_R).symm
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hkpg
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hCq_pg
    have hcard : Nat.card ↥R = Nat.card ↥g.ker * Nat.card ↥Cq := by
      have he : (↥R ⧸ g.ker) ≃* ↥Cq :=
        QuotientGroup.quotientKerEquivOfSurjective g hgsurj
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker, Nat.card_congr he.toEquiv,
        mul_comm]
    exact ⟨a + b, by rw [hcard, ha, hb, ← pow_add]⟩
  have hRG_pg : IsPGroup q ↥RG := hR_pg.map Mσ.subtype
  -- `RG ⊴ M`: the `q`-core `Cq` of `M_σ/Q` is characteristic, so preserved by `M`-conjugation.
  haveI hCq_char : Cq.Characteristic := by rw [hCq]; infer_instance
  have hRG_normM : (RG.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hRG_le_M]
    intro m hm
    have hmMσ : m ∈ Subgroup.normalizer (Mσ : Set G) := hMnormMσ hm
    -- conj by `m` on `↥Mσ`, the induced quotient automorphism `ᾱ`, and the `Q`-invariance of `α`.
    set α : ↥Mσ ≃* ↥Mσ := (Subgroup.normalizerMonoidHom Mσ) ⟨m, hmMσ⟩ with hα
    have hαval : ∀ x : ↥Mσ, (α x : G) = m * (x : G) * m⁻¹ := fun x => rfl
    -- `α z ∈ Q.subgroupOf Mσ ↔ z ∈ Q.subgroupOf Mσ` (conjugation by `m ∈ N_G(Q)`).
    have hαQiff : ∀ z : ↥Mσ, (α z ∈ Q.subgroupOf Mσ) ↔ (z ∈ Q.subgroupOf Mσ) := by
      intro z
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      show (α z : G) ∈ Q ↔ (z : G) ∈ Q
      rw [hαval]
      exact (Subgroup.mem_normalizer_iff.mp (hMnormQ hm) (z : G)).symm
    have hαmapQ : (Q.subgroupOf Mσ).map α.toMonoidHom = Q.subgroupOf Mσ := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨z, hzQ, rfl⟩; exact (hαQiff z).mpr hzQ
      · intro hxQ
        exact ⟨α.symm x, (hαQiff (α.symm x)).mp (by rw [α.apply_symm_apply]; exact hxQ),
          α.apply_symm_apply x⟩
    set ᾱ : (↥Mσ ⧸ Q.subgroupOf Mσ) ≃* (↥Mσ ⧸ Q.subgroupOf Mσ) :=
      QuotientGroup.congr (Q.subgroupOf Mσ) (Q.subgroupOf Mσ) α hαmapQ with hαbar
    have hαbarval : ∀ x : ↥Mσ, ᾱ (QuotientGroup.mk' (Q.subgroupOf Mσ) x)
        = QuotientGroup.mk' (Q.subgroupOf Mσ) (α x) := fun x => by
      rw [hαbar]; exact QuotientGroup.congr_mk' (Q.subgroupOf Mσ) (Q.subgroupOf Mσ) α hαmapQ x
    -- `ᾱ c ∈ Cq ↔ c ∈ Cq` (`Cq` characteristic ⟹ `ᾱ`-invariant).
    have hCqiff : ∀ c : ↥Mσ ⧸ Q.subgroupOf Mσ, (ᾱ c ∈ Cq) ↔ (c ∈ Cq) := by
      intro c
      have hfix := hCq_char.fixed ᾱ
      constructor
      · intro h; rw [← hfix, Subgroup.mem_comap]; exact h
      · intro h; rw [← hfix, Subgroup.mem_comap] at h; exact h
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hmem, hmem]
    constructor
    · rintro ⟨hyMσ, hyC⟩
      have hmym : m * y * m⁻¹ ∈ Mσ := (Subgroup.mem_normalizer_iff.mp hmMσ y).mp hyMσ
      refine ⟨hmym, ?_⟩
      -- `mk'⟨m·y·m⁻¹⟩ = ᾱ(mk'⟨y⟩) ∈ ᾱ(Cq) = Cq`.
      have heqcls : QuotientGroup.mk' (Q.subgroupOf Mσ) ⟨m * y * m⁻¹, hmym⟩
          = ᾱ (QuotientGroup.mk' (Q.subgroupOf Mσ) ⟨y, hyMσ⟩) := by
        rw [hαbarval]
        exact congrArg (QuotientGroup.mk' (Q.subgroupOf Mσ)) (Subtype.ext (hαval ⟨y, hyMσ⟩).symm)
      rw [heqcls]; exact (hCqiff _).mpr hyC
    · rintro ⟨hmymMσ, hmymC⟩
      -- `mk'⟨m·y·m⁻¹⟩ ∈ Cq ⟹ mk'⟨y⟩ ∈ Cq` (via `ᾱ`-invariance).
      have hyMσ : y ∈ Mσ := (Subgroup.mem_normalizer_iff.mp hmMσ y).mpr hmymMσ
      refine ⟨hyMσ, ?_⟩
      have heqcls : QuotientGroup.mk' (Q.subgroupOf Mσ) ⟨m * y * m⁻¹, hmymMσ⟩
          = ᾱ (QuotientGroup.mk' (Q.subgroupOf Mσ) ⟨y, hyMσ⟩) := by
        rw [hαbarval]
        exact congrArg (QuotientGroup.mk' (Q.subgroupOf Mσ)) (Subtype.ext (hαval ⟨y, hyMσ⟩).symm)
      rw [heqcls] at hmymC
      exact (hCqiff _).mp hmymC
  have hRG_le_Q : RG ≤ Q := hQmax RG hRG_le_M hRG_normM hRG_pg
  -- `R ≤ Q.subgroupOf Mσ`, so combined with `hQsub_le_R`, `R = Q.subgroupOf Mσ`, forcing `Cq = ⊥`.
  have hR_le_Qsub : R ≤ Q.subgroupOf Mσ := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hRG_le_Q ⟨x, hx, rfl⟩
  have hReq : R = Q.subgroupOf Mσ := le_antisymm hR_le_Qsub hQsub_le_R
  -- `comap (mk') Cq = R = Q.subgroupOf Mσ = ker (mk') = comap (mk') ⊥`; `mk'` surjective ⟹ `Cq = ⊥`.
  have hcomapbot : Cq.comap (QuotientGroup.mk' (Q.subgroupOf Mσ))
      = (⊥ : Subgroup (↥Mσ ⧸ Q.subgroupOf Mσ)).comap (QuotientGroup.mk' (Q.subgroupOf Mσ)) := by
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    rw [← hR]; exact hReq
  exact (Subgroup.comap_injective (QuotientGroup.mk'_surjective _)) hcomapbot

/-- **`Q.subgroupOf M_σ` is a Hall `{q}`-subgroup of `↥M_σ`** (`§14`-independent helper): for a
`q`-subgroup `Q ≤ M_σ` with `q ∤ [M_σ : Q]`, the relative subgroup is a `{q}`-Hall (= normal Sylow
`q`) of `↥M_σ`.  Used to complement `Q` by a `{q}ᶜ`-Hall in the `D`-construction. -/
theorem isHallSubgroup_subgroupOf_of_pgroup_of_not_dvd_index [Finite G]
    {Mσ Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hQMσ : Q ≤ Mσ) (hQpg : IsPGroup q ↥Q) (hidx : ¬ q ∣ (Q.subgroupOf Mσ).index) :
    Ch03.IsHallSubgroup ({q} : Set ℕ) (Q.subgroupOf Mσ) := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · have hcard : Nat.card ↥(Q.subgroupOf Mσ) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQMσ).toEquiv
    rw [hcard] at hp
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    rw [hn] at hp
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · simp [hn0] at hp
    · rw [Nat.primeFactors_prime_pow hn0.ne' Fact.out, Finset.mem_singleton] at hp
      exact Set.mem_singleton_iff.mpr hp
  · rw [Set.mem_singleton_iff]; rintro rfl; exact hidx (Nat.dvd_of_mem_primeFactors hp)

/-- **Theorem 15.2 step 3 — the `K`-invariant complement `D` of `Q` in `M_σ`** (mmd L4194, "By
Proposition 1.5(a), we may choose a `K`-invariant complement `D` of `Q` in `M_σ`").  In the
type-`P₁` setting (`hP`, `hKstarQ`, `hQneMσ` giving `M_σ` non-nilpotent), with `Q = O_q(M)` the
normal Sylow `q`-subgroup of `M_σ` (`msigma_quotient_isNilpotent_of_inputs` +
`q_not_dvd_index_of_msigma_quotient_isNilpotent`), Proposition 1.5(a) (`exists_aInvariant_hall`)
furnishes a `K`-invariant `{q}ᶜ`-Hall subgroup `D` of `M_σ`, which complements `Q` (coprime Hall
orders) and is nilpotent (`complement_isNilpotent_of_inputs`).

Output (matching the wrapper's existential block): `D ≤ M_σ`, `K ≤ N_G(D)`, `Disjoint Q D`, the
complement `IsComplement' (Q.subgroupOf M_σ) (D.subgroupOf M_σ)`, `D` nilpotent, and `D ≠ ⊥`. -/
theorem exists_kInvariant_qComplement [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hQ : Q = opiCoreInG ({q} : Set ℕ) M)
    (hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M) (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hKstarQ : Kstar ≤ Q) (hQneMσ : Q ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hKne : K ≠ ⊥) (hKMσdisj : Disjoint K (OddOrder.BG.Ch3.S10.Msigma M))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M))) :
    ∃ D : Subgroup G, D ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
      K ≤ Subgroup.normalizer (D : Set G) ∧ Disjoint Q D ∧
      Subgroup.IsComplement' (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))
        (D.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) ∧
      Group.IsNilpotent ↥D ∧ D ≠ ⊥ ∧ q ∉ (Nat.card ↥D).primeFactors := by
  classical
  set Mσ : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  have hMσM : Mσ ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hMnormMσ : M ≤ Subgroup.normalizer (Mσ : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  haveI : IsSolvable ↥Mσ := solvable_of_solvable_injective (Subgroup.inclusion_injective hMσM)
  have hQpg : IsPGroup q ↥Q := by rw [hQ]; exact isPGroup_opiCoreInG_singleton M
  haveI hQnMσ : (Q.subgroupOf Mσ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQMσ).mpr (hMσM.trans hMnormQ)
  -- `M_σ/Q` nilpotent (step (c)(d)) and `q ∤ [M_σ:Q]` (step (c), `Q` is the Sylow `q`).
  have hNil : Group.IsNilpotent (↥Mσ ⧸ Q.subgroupOf Mσ) :=
    msigma_quotient_isNilpotent_of_inputs hG hM hP hKM hK hKstar hQMσ hMnormQ hKstarQ hQneMσ hKne
      hKMσdisj hcop
  have hQmax : ∀ R : Subgroup G, R ≤ M → (R.subgroupOf M).Normal → IsPGroup q ↥R → R ≤ Q := by
    intro R hRM hRnorm hRpg
    rw [hQ]
    refine le_opiCoreInG_of_normal_of_isPiSubgroup hRM hRnorm ?_
    intro p hp
    obtain ⟨n, hn⟩ := hRpg.exists_card_eq
    rw [hn] at hp
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0] at hp
    · rw [Nat.primeFactors_prime_pow h0.ne' Fact.out, Finset.mem_singleton] at hp
      exact Set.mem_singleton_iff.mpr hp
  have hidx : ¬ q ∣ (Q.subgroupOf Mσ).index :=
    q_not_dvd_index_of_msigma_quotient_isNilpotent hQMσ hMσM hQpg hMnormMσ hMnormQ hQmax hNil
  have hQHall : Ch03.IsHallSubgroup ({q} : Set ℕ) (Q.subgroupOf Mσ) :=
    isHallSubgroup_subgroupOf_of_pgroup_of_not_dvd_index hQMσ hQpg hidx
  -- the `K`-conjugation action on `↥M_σ` and the `K`-invariant `{q}ᶜ`-Hall `D_M`.
  have hKnormMσ : K ≤ Subgroup.normalizer (Mσ : Set G) := hKM.trans hMnormMσ
  set φ : ↥K →* MulAut ↥Mσ :=
    (Subgroup.normalizerMonoidHom Mσ).comp (Subgroup.inclusion hKnormMσ) with hφ
  obtain ⟨DM, hDM_hall, hDM_inv⟩ :=
    OddOrder.BG.Ch1.S01.exists_aInvariant_hall (G := ↥Mσ) (A := ↥K) (φ := φ) hcop ({q}ᶜ : Set ℕ)
  set D : Subgroup G := DM.map Mσ.subtype with hD
  have hD_le_Mσ : D ≤ Mσ := Subgroup.map_subtype_le _
  have hDsub_eq : D.subgroupOf Mσ = DM := by
    rw [hD, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Mσ.subtype_injective]
  -- `{q}ᶜ`-Hall `DM` = `{p ∉ {q}}`-Hall (defeq, for `hall_compl_isComplement`).
  have hDM_hall' : Ch03.IsHallSubgroup {p | p ∉ ({q} : Set ℕ)} DM := hDM_hall
  -- `IsComplement' DM (Q.subgroupOf Mσ)`, hence `IsComplement' (Q.subgroupOf Mσ) (D.subgroupOf Mσ)`.
  have hcompl : Subgroup.IsComplement' (Q.subgroupOf Mσ) (D.subgroupOf Mσ) := by
    rw [hDsub_eq]
    exact (OddOrder.BG.Ch1.S01.hall_compl_isComplement hDM_hall' hQHall).symm
  -- `Disjoint Q D`: complement disjointness lifted to `G`.
  have hdisjQD : Disjoint Q D := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxD
    have hxMσ : x ∈ Mσ := hQMσ hxQ
    have hmem : (⟨x, hxMσ⟩ : ↥Mσ) ∈ (Q.subgroupOf Mσ) ⊓ (D.subgroupOf Mσ) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxQ, Subgroup.mem_subgroupOf.mpr hxD⟩
    rw [hcompl.disjoint.eq_bot, Subgroup.mem_bot] at hmem
    exact congrArg (Subgroup.subtype Mσ) hmem
  -- `K ≤ N_G(D)`: `K`-invariance of `DM` (`φ k • DM = DM`) ⟹ `k·d·k⁻¹ ∈ D` for `d ∈ D`.
  have hKnormD : K ≤ Subgroup.normalizer (D : Set G) := by
    intro k hk
    refine Subgroup.mem_normalizer_fintype ?_
    intro x hxD
    rw [hD] at hxD ⊢
    obtain ⟨w, hwDM, rfl⟩ := hxD
    -- `k·↑w·k⁻¹ = ↑(φk w)`, and `φk w ∈ DM` (invariance `φk • DM = DM`).
    have hφwDM : φ ⟨k, hk⟩ w ∈ DM := by
      have hmem : φ ⟨k, hk⟩ w ∈ φ ⟨k, hk⟩ • DM := by
        rw [Subgroup.pointwise_smul_def]; exact Subgroup.mem_map.mpr ⟨w, hwDM, rfl⟩
      rwa [hDM_inv ⟨k, hk⟩] at hmem
    refine ⟨φ ⟨k, hk⟩ w, hφwDM, ?_⟩
    show ((φ ⟨k, hk⟩ w : ↥Mσ) : G) = k * (Mσ.subtype w) * k⁻¹
    rfl
  -- `D` nilpotent (`complement_isNilpotent_of_inputs`, prime-order `K₁ ≤ K`).
  -- (assembled below via a prime-order `K₁ ≤ K` and the prime-manner action).
  refine ⟨D, hD_le_Mσ, hKnormD, hdisjQD, hcompl, ?_, ?_, ?_⟩
  · -- `D` nilpotent: prime-order `K₁ ≤ K` acts FPF on `D` (Theorem 3.7).
    have hprime := actsPrimeManner_of_typeP hG hM hP hKM hK hKstar
    have hKcard1 : Nat.card ↥K ≠ 1 := fun hc => hKne (Subgroup.card_eq_one.mp hc)
    obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hKcard1
    haveI : Fact r.Prime := ⟨hr_prime⟩
    obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) r hr_dvd
    set K1 : Subgroup G := Subgroup.zpowers (c : G) with hK1
    have hcK : (c : G) ∈ K := c.2
    have hK1K : K1 ≤ K := by rw [hK1]; exact Subgroup.zpowers_le.mpr hcK
    have hK1M : K1 ≤ M := hK1K.trans hKM
    have hDM_le_M : D ≤ M := hD_le_Mσ.trans hMσM
    have hord_coe : orderOf (c : G) = r := by rw [Subgroup.orderOf_coe, hc_ord]
    have hcardK1 : Nat.card ↥K1 = r := by rw [hK1, Nat.card_zpowers, hord_coe]
    -- `D ≠ ⊥`: else `Q = M_σ` (`Q ⊔ D = M_σ`), contradicting `hQneMσ`.
    have hDne : D ≠ ⊥ := by
      intro hbot
      apply hQneMσ
      have : Q.subgroupOf Mσ = ⊤ := by
        have hsup : Q.subgroupOf Mσ ⊔ D.subgroupOf Mσ = ⊤ := hcompl.sup_eq_top
        rw [hbot] at hsup; simpa using hsup
      have hQeq : Q.subgroupOf Mσ = (⊤ : Subgroup Mσ) := this
      have := Subgroup.subgroupOf_eq_top.mp hQeq
      exact le_antisymm hQMσ this
    have hK1ne : K1 ≠ ⊥ := by
      rw [hK1, Ne, Subgroup.zpowers_eq_bot]
      intro hc1
      have : orderOf (c : G) = 1 := by rw [hc1]; exact orderOf_one
      rw [hord_coe] at this; exact hr_prime.ne_one this
    have hDQ_disj : Disjoint D Q := hdisjQD.symm
    have hDK1disj : Disjoint D K1 := (hKMσdisj.symm.mono_left hD_le_Mσ).mono_right hK1K
    have hK1normD : K1 ≤ Subgroup.normalizer (D : Set G) := hK1K.trans hKnormD
    refine complement_isNilpotent_of_inputs hG hM hDM_le_M hK1M hD_le_Mσ hDQ_disj hK1K
      hK1normD hDK1disj hDne hK1ne ⟨r, hr_prime, hcardK1⟩ ?_
    -- `hCentleQ`: `C_G(r) ⊓ M_σ = K* ⊆ Q` for `r ∈ K#` (prime-manner + `K* ⊆ Q`).
    intro x hxK hx1
    rw [hprime x hxK hx1]; exact hKstarQ
  · -- `D ≠ ⊥`: as above.
    intro hbot
    apply hQneMσ
    have hsup : Q.subgroupOf Mσ ⊔ D.subgroupOf Mσ = ⊤ := hcompl.sup_eq_top
    rw [hbot] at hsup; simp only [Subgroup.bot_subgroupOf, sup_bot_eq] at hsup
    exact le_antisymm hQMσ (Subgroup.subgroupOf_eq_top.mp hsup)
  · -- `q ∤ |D|`: `|D| = [M_σ : Q]` (complement) and `q ∤ [M_σ : Q]` (`hidx`).
    intro hmem
    apply hidx
    have hDcard : Nat.card ↥D = (Q.subgroupOf Mσ).index := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_le_Mσ).toEquiv]
      exact (hcompl.symm.index_eq_card).symm
    rw [← hDcard]; exact (Nat.mem_primeFactors.mp hmem).2.1

/-- **Theorem 15.2 step 4, the `D`-side fixed-point fact** (BG Proposition 1.5(d)/1.6(d), mmd
L4196-4200): a single `q'`-element `d` (here `d ∈ D`, coprime to `Q`) that *centralizes the chief
factor* `Q̄ = Q/Q₀` (`⁅d, y⁆ ∈ Q₀` for every `y ∈ Q`) already centralizes `Q` itself, **provided**
`Q₀ ⊆ C_G(d)` (which holds since `Q₀ = C_Q(D) ⊆ C_G(d)` for `d ∈ D`).

This is the BG step "`C_D(Q̄) = C_D(Q)`".  Proof via the coprime decomposition (Proposition 1.6(d),
`subgroup_coprime_decomposition`): for the coprime action of `A = ⟨d⟩` on `Q`,
`Q = C_Q(⟨d⟩) ⊔ ⁅Q, ⟨d⟩⁆`.  The set of `x ∈ N(Q₀)` whose conjugation centralizes `Q̄` is a subgroup
containing `d` (closure uses `⁅x x', y⁆ = x ⁅x', y⁆ x⁻¹ · ⁅x, y⁆`), hence `⟨d⟩`, so `⁅Q, ⟨d⟩⁆ ≤ Q₀`.
With `Q₀ ⊆ C_G(d)` and `C_Q(⟨d⟩) ⊆ C_G(d)` (as `d ∈ ⟨d⟩`), both summands centralize `d`, so does `Q`.

Used in `centralizer_msigma_quotient_le_fittingInAmbient` to decompose `C_{M_σ}(Q̄) = Q·C_D(Q)`. -/
theorem centralizes_Q_of_centralizes_quotient [Finite G]
    {Q Q0 : Subgroup G} {d : G}
    (hdN : d ∈ Subgroup.normalizer (Q : Set G))
    (hQQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G))
    (hdQ0 : d ∈ Subgroup.normalizer (Q0 : Set G))
    (hQ0Q : Q0 ≤ Q) (hQ0d : Q0 ≤ Subgroup.centralizer ({d} : Set G))
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers d)) (Nat.card ↥Q))
    (hSolv : IsSolvable ↥Q)
    (hfix : ∀ y ∈ Q, ⁅d, y⁆ ∈ Q0) :
    Q ≤ Subgroup.centralizer ({d} : Set G) := by
  classical
  have hAN : Subgroup.zpowers d ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.zpowers_le).mpr hdN
  -- The set of `x ∈ N(Q₀)` whose conjugation centralizes `Q̄` (`⁅x, y⁆ ∈ Q₀` for all `y ∈ Q`) is a
  -- subgroup of `G`; it contains `d`, hence all of `⟨d⟩`.  `⁅x x', y⁆ = x ⁅x', y⁆ x⁻¹ · ⁅x, y⁆`.
  let T : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (Q0 : Set G) ∧ ∀ y ∈ Q, ⁅x, y⁆ ∈ Q0}
      one_mem' := ⟨(Subgroup.normalizer (Q0 : Set G)).one_mem, fun y _ => by
        rw [commutatorElement_one_left]; exact Q0.one_mem⟩
      mul_mem' := fun {x x'} hx hx' => ⟨(Subgroup.normalizer (Q0 : Set G)).mul_mem hx.1 hx'.1,
        fun y hyQ => by
          have heq : ⁅x * x', y⁆ = (x * ⁅x', y⁆ * x⁻¹) * ⁅x, y⁆ := by
            rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
          rw [heq]
          exact Q0.mul_mem ((Subgroup.mem_normalizer_iff.mp hx.1 ⁅x', y⁆).mp (hx'.2 y hyQ))
            (hx.2 y hyQ)⟩
      inv_mem' := fun {x} hx => ⟨(Subgroup.normalizer (Q0 : Set G)).inv_mem hx.1, fun y hyQ => by
        have heq : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * (x⁻¹)⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]; group
        rw [heq]
        exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem hx.1)
          ⁅x, y⁆⁻¹).mp (Q0.inv_mem (hx.2 y hyQ))⟩ }
  have hdT : d ∈ T := ⟨hdQ0, hfix⟩
  have hzpT : Subgroup.zpowers d ≤ T := (Subgroup.zpowers_le).mpr hdT
  -- Hence `⁅Q, ⟨d⟩⁆ ≤ Q₀`.
  have hcommQ0 : ⁅Q, Subgroup.zpowers d⁆ ≤ Q0 := by
    rw [Subgroup.commutator_le]
    intro y hyQ a ha
    rw [← commutatorElement_inv]
    exact Q0.inv_mem ((hzpT ha).2 y hyQ)
  -- Proposition 1.6(d): `Q = C_Q(⟨d⟩) ⊔ ⁅Q, ⟨d⟩⁆`.
  have hdecomp := OddOrder.BG.Ch3.S13.subgroup_coprime_decomposition hAN hcop (Or.inr hSolv)
  -- Both summands centralize `d`: `C(⟨d⟩) ⊆ C(d)` and `⁅Q, ⟨d⟩⁆ ≤ Q₀ ⊆ C(d)`.
  rw [hdecomp]
  refine sup_le (inf_le_left.trans ?_) (hcommQ0.trans hQ0d)
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers d))

/-- From an `IsComplement'` of `H.subgroupOf N` and `K.subgroupOf N` (with `H, K ≤ N`), every
`x ∈ N` factors as `x = a·b` with `a ∈ H`, `b ∈ K` (`§14`-independent, generic helper; keeps the
`↥N`-complement reasoning away from later `M_σ`-unfolding). -/
theorem exists_mul_mem_of_isComplement_subgroupOf {N H K : Subgroup G} (hHN : H ≤ N) (hKN : K ≤ N)
    (hcompl : Subgroup.IsComplement' (H.subgroupOf N) (K.subgroupOf N))
    {x : G} (hxN : x ∈ N) : ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  -- `(H.subgroupOf N) * (K.subgroupOf N) = univ` (complement), so `⟨x, _⟩` factors there.
  have hmul : (⟨x, hxN⟩ : ↥N) ∈
      ((H.subgroupOf N : Set ↥N) * (K.subgroupOf N : Set ↥N)) := by
    rw [hcompl.mul_eq]; exact Set.mem_univ _
  obtain ⟨u, huH, v, hvK, huv⟩ := Set.mem_mul.mp hmul
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at huH hvK
  refine ⟨(u : G), huH, (v : G), hvK, ?_⟩
  have hcoe : ((⟨x, hxN⟩ : ↥N) : G) = ((u * v : ↥N) : G) := congrArg _ huv.symm
  rw [Subgroup.coe_mul] at hcoe
  exact hcoe

set_option maxHeartbeats 1600000 in
open scoped commutatorElement in
/-- **Theorem 15.2(g) — the section-Fitting containment `C_{M_σ}(Q̄) ⊆ F(M)`** (mmd L4196-4198,
"`F(M) = Q·C_M(Q) = C_{M_σ}(Q̄)`"), which discharges `hsecFit` of
`derivedDerived_le_fittingInAmbient_of_inputs`.  Unlike the *full* centralizer `C_M(Q)` (which needs
the genuine `σ`-uniqueness gate `C_M(Q) ⊆ M_σ`), the `M_σ`-section centralizer `C_{M_σ}(Q̄)` lands in
`F(M)` from the local `M_σ = Q ⋊ D` structure alone:

* `S := C_{M_σ}(Q̄) = {x ∈ M_σ : ⁅x, y⁆ ∈ Q₀ ∀ y ∈ Q}` decomposes as `S = Q ⊔ (D ⊓ S)`: writing
  `x ∈ M_σ` as `a·d'` (`a ∈ Q`, `d' ∈ D`, the complement), `a ∈ Q ⊆ S` (`Q̄` abelian, `hQab`), so
  `d' = a⁻¹x ∈ D ⊓ S`;
* `D ⊓ S ⊆ C_G(Q)`: each `d' ∈ D ⊓ S` centralizes `Q̄` and is a `q'`-element, hence centralizes `Q`
  (`centralizes_Q_of_centralizes_quotient`);
* so `⁅Q, D ⊓ S⁆ = ⊥`, and `S = Q ⊔ (D ⊓ S)` is nilpotent (`Q` a `q`-group, `D ⊓ S ⊆ D` nilpotent,
  commuting: `isNilpotent_sup_of_commutator_eq_bot`);
* `S ◁ M` (`M` normalizes `Q`, `Q₀`, and `M_σ`), so a nilpotent normal subgroup of `M` lands in
  `F(M)` (`nilpotent_normal_le_fitting`).

No `σ`-uniqueness input is needed (the `C_M(Q) ⊆ M_σ` gate is only for the *full* `C_M(Q)`). -/
theorem centralizer_msigma_quotient_le_fittingInAmbient [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M Q Q0 D : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : M ∈ maximalSubgroups G)
    (hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M) (hDMσ : D ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hQ0 : Q0 = Q ⊓ Subgroup.centralizer (D : Set G)) (hQ0Q : Q0 ≤ Q)
    (hcompl : Subgroup.IsComplement' (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))
      (D.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)))
    (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hMnormQ0 : M ≤ Subgroup.normalizer (Q0 : Set G))
    (hQpg : IsPGroup q ↥Q) (hDnil : Group.IsNilpotent ↥D)
    (hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q))
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Q0) :
    ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M,
      (∀ y ∈ Q, ⁅x, y⁆ ∈ Q0) → x ∈ fittingInAmbient M := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  set Mσ : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  have hMσM : Mσ ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hMnormMσ : M ≤ Subgroup.normalizer (Mσ : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M
  have hQM : Q ≤ M := hQMσ.trans hMσM
  have hDM : D ≤ M := hDMσ.trans hMσM
  haveI : IsSolvable ↥Q := solvable_of_solvable_injective (Subgroup.inclusion_injective hQM)
  -- The section centralizer `S = C_{M_σ}(Q̄)`, realized as a subgroup of `G`.
  -- (Membership in `M_σ` already gives `x ∈ N(Q₀)` since `M_σ ≤ M ≤ N(Q₀)`.)
  have hMσnormQ0 : Mσ ≤ Subgroup.normalizer (Q0 : Set G) := hMσM.trans hMnormQ0
  let S : Subgroup G :=
    { carrier := {x | x ∈ Mσ ∧ ∀ y ∈ Q, ⁅x, y⁆ ∈ Q0}
      one_mem' := ⟨Mσ.one_mem, fun y _ => by rw [commutatorElement_one_left]; exact Q0.one_mem⟩
      mul_mem' := fun {x x'} hx hx' => ⟨Mσ.mul_mem hx.1 hx'.1, fun y hyQ => by
        have heq : ⁅x * x', y⁆ = (x * ⁅x', y⁆ * x⁻¹) * ⁅x, y⁆ := by
          rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
        rw [heq]
        have hxN0 : x ∈ Subgroup.normalizer (Q0 : Set G) := hMσnormQ0 hx.1
        exact Q0.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN0 ⁅x', y⁆).mp (hx'.2 y hyQ))
          (hx.2 y hyQ)⟩
      inv_mem' := fun {x} hx => ⟨Mσ.inv_mem hx.1, fun y hyQ => by
        have heq : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * (x⁻¹)⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]; group
        rw [heq]
        have hxN0 : x ∈ Subgroup.normalizer (Q0 : Set G) := hMσnormQ0 hx.1
        exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem hxN0)
          ⁅x, y⁆⁻¹).mp (Q0.inv_mem (hx.2 y hyQ))⟩ }
  have hSmem : ∀ x, x ∈ S ↔ x ∈ Mσ ∧ ∀ y ∈ Q, ⁅x, y⁆ ∈ Q0 := fun x => Iff.rfl
  have hSMσ : S ≤ Mσ := fun x hx => hx.1
  -- `Q ≤ S` (`Q̄` abelian) and `D ⊓ S ⊆ C_G(Q)` (the `q'`-elements of `S` centralize `Q`).
  have hQS : Q ≤ S := fun a haQ => ⟨hQMσ haQ, fun y hyQ => hQab a haQ y hyQ⟩
  have hDScent : (D ⊓ S : Subgroup G) ≤ Subgroup.centralizer (Q : Set G) := by
    intro d hd
    rw [Subgroup.mem_inf] at hd
    obtain ⟨hdD, hdS⟩ := hd
    have hdN : d ∈ Subgroup.normalizer (Q : Set G) := hMnormQ (hDM hdD)
    have hdN0 : d ∈ Subgroup.normalizer (Q0 : Set G) := hMnormQ0 (hDM hdD)
    -- coprimality `|⟨d⟩| | |Q|`.
    have hcopd : Nat.Coprime (Nat.card ↥(Subgroup.zpowers d)) (Nat.card ↥Q) :=
      hcop.coprime_dvd_left (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hdD))
    -- `Q₀ ⊆ C_G(d)` (since `Q₀ = Q ⊓ C(D)` and `d ∈ D`).
    have hQ0d : Q0 ≤ Subgroup.centralizer ({d} : Set G) := by
      rw [hQ0]
      refine inf_le_right.trans ?_
      exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdD)
    have hQN0 : Q ≤ Subgroup.normalizer (Q0 : Set G) := hQMσ.trans hMσnormQ0
    have hQleCd : Q ≤ Subgroup.centralizer ({d} : Set G) :=
      centralizes_Q_of_centralizes_quotient hdN hQN0 hdN0 hQ0Q hQ0d hcopd ‹IsSolvable ↥Q› hdS.2
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp (hQleCd hg) d (Set.mem_singleton d)).symm
  -- `S = Q ⊔ (D ⊓ S)`: the `M_σ = Q·D` decomposition lands the `q'`-part in `D ⊓ S`.
  have hSdecomp : S = Q ⊔ (D ⊓ S) := by
    refine le_antisymm (fun x hx => ?_) (sup_le hQS inf_le_right)
    -- `x ∈ M_σ = Q·D`, so `x = a·b` with `a ∈ Q`, `b ∈ D`; then `b = a⁻¹x ∈ D ⊓ S`.
    obtain ⟨a, haQ, b, hbD, hxeq⟩ :=
      exists_mul_mem_of_isComplement_subgroupOf hQMσ hDMσ hcompl (hSMσ hx)
    have haS : a ∈ S := hQS haQ
    have hbS : b ∈ S := by
      have hbeq : b = a⁻¹ * x := by rw [hxeq]; group
      rw [hbeq]; exact S.mul_mem (S.inv_mem haS) hx
    rw [hxeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haQ)
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hbD, hbS⟩))
  -- `S` is nilpotent: `Q ⊔ (D ⊓ S)` with `⁅Q, D ⊓ S⁆ = ⊥` (`D ⊓ S` centralizes `Q`).
  haveI : Group.IsNilpotent ↥Q := hQpg.isNilpotent
  haveI hDSnil : Group.IsNilpotent ↥((D ⊓ S : Subgroup G).subgroupOf D) := inferInstance
  haveI : Group.IsNilpotent ↥(D ⊓ S : Subgroup G) :=
    Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : (D ⊓ S : Subgroup G) ≤ D))
  have hcommbot : ⁅Q, (D ⊓ S : Subgroup G)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDScent
  haveI : Group.IsNilpotent ↥S := by
    rw [hSdecomp]; exact isNilpotent_sup_of_commutator_eq_bot hcommbot
  -- `S ◁ M`: `M` normalizes `Q`, `Q₀`, and `M_σ`, hence the section centralizer.  Single direction
  -- `m·S·m⁻¹ ⊆ S` for `m ∈ M`, applied to `m` and `m⁻¹` gives normality.
  have hpreserve : ∀ m ∈ M, ∀ z ∈ S, m * z * m⁻¹ ∈ S := by
    intro m hm z hz
    obtain ⟨hzMσ, hzc⟩ := hz
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hMnormMσ hm) z).mp hzMσ, fun y hyQ => ?_⟩
    -- `⁅m z m⁻¹, y⁆ = m ⁅z, m⁻¹ y m⁆ m⁻¹ ∈ m Q₀ m⁻¹ = Q₀`.
    have hyQ' : m⁻¹ * y * m ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hMnormQ (M.inv_mem hm)) y).mp hyQ
      rwa [inv_inv] at this
    have hc := hzc (m⁻¹ * y * m) hyQ'
    have heq : ⁅m * z * m⁻¹, y⁆ = m * ⁅z, m⁻¹ * y * m⁆ * m⁻¹ := by
      rw [conjugate_commutatorElement]; congr 1 <;> group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp (hMnormQ0 hm) ⁅z, m⁻¹ * y * m⁆).mp hc
  have hMnormS : M ≤ Subgroup.normalizer (S : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz; exact hpreserve m hm z hz
    · intro hz
      have := hpreserve m⁻¹ (M.inv_mem hm) (m * z * m⁻¹) hz
      rwa [show m⁻¹ * (m * z * m⁻¹) * m⁻¹⁻¹ = z by group] at this
  -- `S` nilpotent + normal in `M` ⟹ `S ⊆ F(M)`.
  haveI hSnormM : (S.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hSMσ.trans hMσM)).mpr hMnormS
  haveI : Group.IsNilpotent ↥(S.subgroupOf M) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hSMσ.trans hMσM)).symm
  have hSF : S ≤ fittingInAmbient M := by
    calc S = (S.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le (hSMσ.trans hMσM)).symm
      _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype :=
          Subgroup.map_mono OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
      _ = fittingInAmbient M := rfl
  intro x hxMσ hxc
  exact hSF ⟨hxMσ, hxc⟩

/-- A finite `ZMod q`-module of cardinality `q` (`q` prime) has `Module.finrank ≤ 1`
(`§14`-independent, reusable).  Used to feed the cyclicity hypothesis `hcyc` of BG Theorem 3.10(c)
once `|C_{Q̄}(K)| = q` is known. -/
theorem finrank_le_one_of_card_eq {q : ℕ} [Fact q.Prime] {Mod : Type*}
    [AddCommGroup Mod] [Module (ZMod q) Mod] [Finite Mod] (h : Nat.card Mod = q) :
    Module.finrank (ZMod q) Mod ≤ 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : Fintype Mod := Fintype.ofFinite Mod
  have hpow : Fintype.card Mod = q ^ Module.finrank (ZMod q) Mod := by
    rw [Module.card_eq_pow_finrank (K := ZMod q), ZMod.card]
  rw [Nat.card_eq_fintype_card, hpow] at h
  have hfin : Module.finrank (ZMod q) Mod = 1 :=
    Nat.pow_right_injective (Fact.out : q.Prime).two_le (h.trans (pow_one q).symm)
  omega

/-- **Counting the invariants of a quotient module by its fixed-point subgroup** (`§14`-independent,
reusable).  For a finite commutative `H`-module `Mod` over `ZMod q` (with `H` acting through a
`MulDistribMulAction`) and a subgroup `R ≤ H`, if `Cbar ≤ Mod` is exactly the set of `R`-fixed
points (`hchar`), then the `R`-invariants of the associated representation have cardinality `|Cbar|`.

This isolates the `Module.End`/`Additive` instance bookkeeping (the module is an *instance argument*
here, mirroring `card_eq_pow_card_invariants_of_elemAbelian_general`), so the caller can apply it
without re-synthesising the representation.  Used in Theorem 15.2(f) to read off `|C_{Q̄}(K)|`. -/
theorem card_invariants_eq_card_of_fixedPoints {q : ℕ} {H : Type*} [Group H]
    {Mod : Type*} [CommGroup Mod] [Finite Mod] [Module (ZMod q) (Additive Mod)]
    [MulDistribMulAction H Mod] {R : Subgroup H} (Cbar : Subgroup Mod)
    (hchar : ∀ w : Mod, (∀ r : ↥R, (r : H) • w = w) ↔ w ∈ Cbar) :
    Nat.card ↥(Representation.invariants
      ((Representation.ofDistribMulAction (ZMod q) H (Additive Mod)).comp R.subtype))
      = Nat.card ↥Cbar := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv Additive.toMul (fun v => ?_)
  rw [Representation.mem_invariants, ← hchar (Additive.toMul v)]
  refine forall_congr' (fun r => ?_)
  show ((r : H) • v = v) ↔ ((r : H) • Additive.toMul v = Additive.toMul v)
  constructor
  · intro h
    have := congrArg Additive.toMul h
    rwa [show Additive.toMul ((r : H) • v) = (r : H) • Additive.toMul v from rfl] at this
  · intro h
    apply Additive.toMul.injective
    rwa [show Additive.toMul ((r : H) • v) = (r : H) • Additive.toMul v from rfl]

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
open scoped commutatorElement in
open scoped IsMulCommutative in
/-- **Theorem 15.2(f)+(g) — `[Q : Q₀] = q^p` and `D' ⊆ C_D(Q̄)`, gated-endpoint skeleton**
(mmd L4196-4200, BG Theorem 3.10(b)(c)).  The Frobenius group `D ⋊ K` (kernel `D`, complement `K`)
acts by conjugation on the elementary-abelian chief factor `Q̄ = Q/Q₀` (`hEA`).  The
caller-supplied subgroup `C` records the `K`-fixed classes (`C/Q₀ = C_{Q̄}(K)` via `hCfix`, with
`|C : Q₀| = q` via `hCcard`), so `|C_{Q̄}(K)| = q`.  Then:

* **(f)** BG Theorem 3.10(b) (`card_eq_pow_card_invariants_of_elemAbelian_general`) gives
  `|Q̄| = |C_{Q̄}(K)|^{|K|} = q^{|K|}`, i.e. `[Q : Q₀] = q^{|K|}`;
* **(g)** BG Theorem 3.10(c) (`commutator_acts_trivially_of_elemAbelian_general`, with the cyclicity
  hypothesis discharged by `finrank_le_one_of_card_eq` from `|C_{Q̄}(K)| = q`) gives
  `D' ⊆ C_D(Q̄)`, i.e. `∀ g ∈ ⁅D,D⁆, ∀ x ∈ Q, ⁅g, x⁆ ∈ Q₀`.

The §14-gated inputs are `hcond3` (prime-manner action of `K`, Proposition 14.2(a)) and
`hCcard`/`hCfix` (`|K*| = q`, Theorem 14.7(f)); `hFPF` is discharged by
`mem_centralizer_of_centralizes_quotient`.  Both BG Theorem 3.10 forms share the one conjugation
`MulDistribMulAction` setup built here. -/
theorem chiefFactor_card_and_commutator_of_inputs [Finite G]
    {Q Q0 D K C : Subgroup G} {q : ℕ} [Fact q.Prime] [(Q0.subgroupOf Q).Normal]
    (hQ0Q : Q0 ≤ Q) (hQ0C : Q0 ≤ C) (hCQ : C ≤ Q) (hDne : D ≠ ⊥)
    (hEA : OddOrder.GroupTheory.IsElementaryAbelian q (↥Q ⧸ Q0.subgroupOf Q))
    (hNT : Nontrivial (↥Q ⧸ Q0.subgroupOf Q))
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hDQ0 : D ≤ Subgroup.normalizer (Q0 : Set G)) (hKQ0 : K ≤ Subgroup.normalizer (Q0 : Set G))
    (hQQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G))
    (hsolv : IsSolvable ↥(D ⊔ K))
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(D ⊔ K)
      (D.subgroupOf (D ⊔ K)) (K.subgroupOf (D ⊔ K)))
    (hcop : Nat.Coprime (Nat.card ↥(D ⊔ K)) (Nat.card ↥Q))
    (hFPF : ∀ x ∈ Q, (∀ d ∈ D, ⁅d, x⁆ ∈ Q0) → x ∈ Q0)
    (hcond3 : ∀ x ∈ K, x ≠ 1 → ∀ y ∈ Q, (⁅x, y⁆ ∈ Q0 ↔ ∀ s ∈ K, ⁅s, y⁆ ∈ Q0))
    (hCfix : ∀ x ∈ Q, ((∀ k ∈ K, ⁅k, x⁆ ∈ Q0) ↔ x ∈ C))
    (hCcard : (Q0.subgroupOf C).index = q) :
    (Nat.card ↥K).Prime ∧
      (Q0.subgroupOf Q).index = q ^ Nat.card ↥K ∧
      ∀ g ∈ ⁅D, D⁆, ∀ x ∈ Q, ⁅g, x⁆ ∈ Q0 := by
  classical
  set H : Subgroup G := D ⊔ K with hH
  have hDH : D ≤ H := le_sup_left
  have hKH : K ≤ H := le_sup_right
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := sup_le hDQ hKQ
  have hHQ0 : H ≤ Subgroup.normalizer (Q0 : Set G) := sup_le hDQ0 hKQ0
  haveI : Finite ↥H := inferInstance
  haveI hHsolv : IsSolvable ↥H := hsolv
  -- conjugation hom of `H = D ⊔ K` on `↥Q`, descended to the chief factor `Q̄ = Q/Q₀`.
  set φ : ↥H →* MulAut ↥Q :=
    (Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hHQ) with hφ
  have hMinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (Q0.subgroupOf Q) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    show (a : G) * (y : G) * (a : G)⁻¹ ∈ Q0
    exact (Subgroup.mem_normalizer_iff.mp (hHQ0 a.2) (y : G)).mp hy
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  letI act : MulDistribMulAction ↥H (↥Q ⧸ Q0.subgroupOf Q) :=
    MulDistribMulAction.compHom _ (quotientMulAutHom hMinv)
  haveI hcomm : IsMulCommutative (↥Q ⧸ Q0.subgroupOf Q) :=
    (isMulCommutative_iff).mpr (fun a b => hEA.comm a b)
  letI : CommGroup (↥Q ⧸ Q0.subgroupOf Q) := inferInstance
  letI : Module (ZMod q) (Additive (↥Q ⧸ Q0.subgroupOf Q)) := hEA.zmodModule
  -- the conjugation-fixed-class characterization: `a • [x] = [x] ↔ ⁅a, x⁆ ∈ Q₀`.
  have hsmul_iff : ∀ (a : ↥H) (x : ↥Q),
      ((a • (QuotientGroup.mk x : ↥Q ⧸ Q0.subgroupOf Q)) = QuotientGroup.mk x)
        ↔ ⁅(a : G), (x : G)⁆ ∈ Q0 := by
    intro a x
    show (quotientMulAutHom hMinv a (QuotientGroup.mk' (Q0.subgroupOf Q) x)
        = QuotientGroup.mk' (Q0.subgroupOf Q) x) ↔ ⁅(a : G), (x : G)⁆ ∈ Q0
    rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    show ((a : G) * (x : G) * (a : G)⁻¹)⁻¹ * (x : G) ∈ Q0 ↔ ⁅(a : G), (x : G)⁆ ∈ Q0
    have hxN : (x : G) ∈ Subgroup.normalizer (Q0 : Set G) := hQQ0 x.2
    have heq : ((a : G) * (x : G) * (a : G)⁻¹)⁻¹ * (x : G)
        = (x : G)⁻¹ * ⁅(a : G), (x : G)⁆⁻¹ * ((x : G)⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [heq]
    have htransfer : ((x : G)⁻¹ * ⁅(a : G), (x : G)⁆⁻¹ * ((x : G)⁻¹)⁻¹ ∈ Q0)
        ↔ ⁅(a : G), (x : G)⁆⁻¹ ∈ Q0 :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem hxN)
        (⁅(a : G), (x : G)⁆⁻¹)).symm
    rw [htransfer, Subgroup.inv_mem_iff]
  -- **BG Theorem 3.10(b)** applied to `Q̄`, kernel `K_thm = D̄`, complement `R_thm = K̄`.
  have hRne : K.subgroupOf H ≠ ⊥ := hfrob.ne_bot_complement
  haveI hKnormal : (D.subgroupOf H).Normal := hfrob.isNormal
  have hKne : D.subgroupOf H ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hDH]; exact hDne
  -- `q ∣ |Q|`, hence `¬ q ∣ |H|` by coprimality.
  have hqdvdQ : q ∣ Nat.card ↥Q := by
    have h1 : q ∣ (Q0.subgroupOf Q).index := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).mp hEA.isPGroup
      have : (Q0.subgroupOf Q).index = Nat.card (↥Q ⧸ Q0.subgroupOf Q) := rfl
      rw [this, hn]
      rcases n with _ | n
      · simp only [pow_zero] at hn
        exact absurd hn (Finite.one_lt_card_iff_nontrivial.mpr hNT).ne'
      · exact dvd_pow_self q (Nat.succ_ne_zero n)
    exact h1.trans (Subgroup.index_dvd_card (Q0.subgroupOf Q))
  have hpH : ¬ q ∣ Nat.card ↥H := by
    intro hqH
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hqH hqdvdQ)
  -- module-level `hCK`, `hFrob`, `hcond3`.
  have hCK : ∀ m : ↥Q ⧸ Q0.subgroupOf Q,
      (∀ k : ↥(D.subgroupOf H), ((k : ↥H) • m = m)) → m = 1 := by
    intro m hm
    induction m using QuotientGroup.induction_on with
    | _ x =>
      have hd : ∀ d ∈ D, ⁅d, (x : G)⁆ ∈ Q0 := by
        intro d hdD
        have hdsub : (⟨d, hDH hdD⟩ : ↥H) ∈ D.subgroupOf H := (Subgroup.mem_subgroupOf).mpr hdD
        exact (hsmul_iff ⟨d, hDH hdD⟩ x).mp (hm ⟨⟨d, hDH hdD⟩, hdsub⟩)
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hFPF (x : G) x.2 hd
  have hFrob : ∀ r ∈ K.subgroupOf H, r ≠ 1 → ∀ k ∈ D.subgroupOf H, k ≠ 1 →
      r * k * r⁻¹ ≠ k := hfrob.conj_frobenius
  have hcond3' : ∀ x : ↥H, x ∈ K.subgroupOf H → x ≠ 1 →
      ∀ m : ↥Q ⧸ Q0.subgroupOf Q,
        ((x : ↥H) • m = m) ↔ (∀ s : ↥(K.subgroupOf H), (s : ↥H) • m = m) := by
    intro x hxK hx1 m
    induction m using QuotientGroup.induction_on with
    | _ y =>
      have hxG : (x : G) ∈ K := (Subgroup.mem_subgroupOf).mp hxK
      have hxG1 : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
      rw [hsmul_iff x y]
      rw [hcond3 (x : G) hxG hxG1 (y : G) y.2]
      constructor
      · intro h s
        have hsG : (s : G) ∈ K := (Subgroup.mem_subgroupOf).mp s.2
        exact (hsmul_iff (s : ↥H) y).mpr (h (s : G) hsG)
      · intro h s hsK
        have hsHmem : (⟨s, hKH hsK⟩ : ↥H) ∈ K.subgroupOf H := (Subgroup.mem_subgroupOf).mpr hsK
        exact (hsmul_iff ⟨s, hKH hsK⟩ y).mp (h ⟨⟨s, hKH hsK⟩, hsHmem⟩)
  have hmain := OddOrder.BG.Ch1.S03.card_eq_pow_card_invariants_of_elemAbelian_general
    (p := q) (H := ↥H) (M := ↥Q ⧸ Q0.subgroupOf Q)
    (K := D.subgroupOf H) (R := K.subgroupOf H) hRne hKne hpH
    (by
      have := (hfrob.coprime_card_kernel_complement)
      rwa [Nat.coprime_comm] at this)
    hCK hFrob hcond3'
  have hcardK : Nat.card ↥(K.subgroupOf H) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  -- **BG Theorem 3.10(a)**: `|K| = |K̄|` is prime (the same Frobenius/module data).
  obtain ⟨pK, hpK_prime, hpK_eq, _⟩ :=
    OddOrder.BG.Ch1.S03.prime_card_and_finrank_of_elemAbelian_general
      (p := q) (H := ↥H) (M := ↥Q ⧸ Q0.subgroupOf Q)
      (K := D.subgroupOf H) (R := K.subgroupOf H) hRne hKne hpH
      (by
        have := (hfrob.coprime_card_kernel_complement)
        rwa [Nat.coprime_comm] at this)
      hCK hFrob hcond3'
  have hKprime : (Nat.card ↥K).Prime := by rw [← hcardK, hpK_eq]; exact hpK_prime
  -- `g : ↥C →* Q̄`, the natural map `c ↦ [c]`; its range is the image of `C`, of order `[C:Q₀]=q`.
  set g : ↥C →* (↥Q ⧸ Q0.subgroupOf Q) :=
    (QuotientGroup.mk' (Q0.subgroupOf Q)).comp (Subgroup.inclusion hCQ) with hg
  have hg_mem : ∀ x : ↥Q,
      (QuotientGroup.mk x : ↥Q ⧸ Q0.subgroupOf Q) ∈ g.range ↔ (x : G) ∈ C := by
    intro x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨c, hc⟩
      rw [hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hc
      have h1 : ((c : G)⁻¹ * (x : G)) ∈ Q0 := hc
      have hx' : (x : G) = (c : G) * ((c : G)⁻¹ * (x : G)) := by group
      rw [hx']; exact C.mul_mem c.2 (hQ0C h1)
    · intro hxC
      refine ⟨⟨(x : G), hxC⟩, ?_⟩
      rw [hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      show ((x : G))⁻¹ * (x : G) ∈ Q0
      rw [inv_mul_cancel]; exact Q0.one_mem
  -- the `K`-fixed classes of `Q̄` are exactly `g.range` (the image of `C`), via `hsmul_iff`+`hCfix`.
  have hchar : ∀ w : ↥Q ⧸ Q0.subgroupOf Q,
      (∀ r : ↥(K.subgroupOf H), (r : ↥H) • w = w) ↔ w ∈ g.range := by
    intro w
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective w
    rw [← hx, hg_mem x, ← hCfix (x : G) x.2]
    constructor
    · intro h k hkK
      exact (hsmul_iff ⟨k, hKH hkK⟩ x).mp (h ⟨⟨k, hKH hkK⟩, (Subgroup.mem_subgroupOf).mpr hkK⟩)
    · intro h r
      exact (hsmul_iff (r : ↥H) x).mpr (h _ ((Subgroup.mem_subgroupOf).mp r.2))
  -- `ker g = Q₀.subgroupOf C`, so `|g.range| = [C : Q₀] = q` (first isomorphism theorem).
  have hker : g.ker = Q0.subgroupOf C := by
    ext c
    simp only [hg, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hinvq : Nat.card ↥(g.range) = q := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hker,
      ← Subgroup.index_eq_card]
    exact hCcard
  refine ⟨hKprime, ?_, ?_⟩
  · -- **(f)**: `[Q : Q₀] = q^{|K|}` (Thm 3.10(b), with `|C_{Q̄}(K)| = |g.range| = q`).
    rw [show (Q0.subgroupOf Q).index = Nat.card (↥Q ⧸ Q0.subgroupOf Q) from rfl, hmain, hcardK]
    congr 1
    rw [card_invariants_eq_card_of_fixedPoints g.range hchar]; exact hinvq
  · -- **(g)**: `D' ⊆ C_D(Q̄)`, i.e. `∀ g ∈ ⁅D,D⁆, ∀ x ∈ Q, ⁅g,x⁆ ∈ Q₀` (Thm 3.10(c)).
    -- `hcyc` (C_{Q̄}(K) cyclic) holds since `|C_{Q̄}(K)| = q` (`finrank_le_one_of_card_eq`).
    have hcomm := OddOrder.BG.Ch1.S03.commutator_acts_trivially_of_elemAbelian_general
      (p := q) (H := ↥H) (M := ↥Q ⧸ Q0.subgroupOf Q) (K := D.subgroupOf H) (R := K.subgroupOf H)
      hfrob hRne hKne hpH hCK hcond3'
      (by apply finrank_le_one_of_card_eq
          rw [card_invariants_eq_card_of_fixedPoints g.range hchar]; exact hinvq)
    intro g0 hg0 x hxQ
    -- lift `g0 ∈ ⁅D,D⁆` to `⁅D̄,D̄⁆ ≤ ↥H`, apply `hcomm`, and read off via `hsmul_iff`.
    have hmapeq : (⁅D.subgroupOf H, D.subgroupOf H⁆ : Subgroup ↥H).map H.subtype = ⁅D, D⁆ := by
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDH]
    rw [← hmapeq] at hg0
    obtain ⟨gbar, hgbarmem, hgbareq⟩ := Subgroup.mem_map.mp hg0
    have hbrk := (hsmul_iff gbar ⟨x, hxQ⟩).mp (hcomm gbar hgbarmem (QuotientGroup.mk ⟨x, hxQ⟩))
    have hg0eq : ((gbar : ↥H) : G) = g0 := hgbareq
    rw [← hg0eq]; exact hbrk

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
open scoped commutatorElement in
/-- **`C_{Q̄}(K)` is the image of `K* ⊔ Q₀`** (BG Proposition 1.5(d), the `hCfix` core of Theorem
15.2(f)).  For a coprime `K`-action on the `q`-group `Q` (with `Q ≤ M_σ`, `K* = C_{M_σ}(K)`,
`K* ≤ Q`, `Q₀ ⊴` normalized by `K` and `Q`), a class `[x]` of `Q̄ = Q/Q₀` is `K`-fixed iff its
representative lies in `K* ⊔ Q₀`:
`(∀ k ∈ K, ⁅k, x⁆ ∈ Q₀) ↔ x ∈ K* ⊔ Q₀`.

Proof: `C_{↥Q}(K)` pushes forward to `C_G(K) ⊓ Q = M_σ ⊓ C_G(K) = K*`
(`fixedPointsOfMulAut_conj_map_subtype`); Proposition 1.5(d)
(`fixedPointsOfMulAut_quotientMulAutHom_eq_map`) gives `C_{Q̄}(K) = (C_{↥Q}(K))·Q₀/Q₀`, whose
preimage in `Q` is `C_{↥Q}(K) ⊔ (Q₀ ↾ Q)`, mapping to `K* ⊔ Q₀` in `G`.

Used both by `card_centralizer_quotient_eq_of_kstar` (its `hCfix` half) and by
`actsPrimeManner_quotient_of_inputs` (applying it to `K` and to each `⟨x⟩`, `x ∈ K#`, whose `K*`
coincides by the prime-manner action) to discharge the chief-factor engine's `hcond3`. -/
theorem centralizes_quotient_iff_mem_kstar_sup [Finite G]
    {Q Q0 K Kstar Mσ : Subgroup G} [(Q0.subgroupOf Q).Normal]
    (hKstar : Kstar = Mσ ⊓ Subgroup.centralizer (K : Set G))
    (hQMσ : Q ≤ Mσ) (hKstarQ : Kstar ≤ Q) (hQ0Q : Q0 ≤ Q)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hQQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G))
    (hKQ0 : K ≤ Subgroup.normalizer (Q0 : Set G))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Q))
    (hSolv : IsSolvable ↥K ∨ IsSolvable ↥Q) :
    ∀ x ∈ Q, ((∀ k ∈ K, ⁅k, x⁆ ∈ Q0) ↔ x ∈ Kstar ⊔ Q0) := by
  classical
  set φ : ↥K →* MulAut ↥Q :=
    (Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hKQ) with hφ
  have hfixmap : (Subgroup.fixedPointsOfMulAut φ).map Q.subtype = Kstar := by
    rw [OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hKQ]
    apply le_antisymm
    · rw [hKstar]; exact le_inf (inf_le_right.trans hQMσ) inf_le_left
    · rw [hKstar] at hKstarQ ⊢; exact le_inf inf_le_right hKstarQ
  have hMinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (Q0.subgroupOf Q) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    show (a : G) * (y : G) * (a : G)⁻¹ ∈ Q0
    exact (Subgroup.mem_normalizer_iff.mp (hKQ0 a.2) (y : G)).mp hy
  have hsmul_iff : ∀ (a : ↥K) (x : ↥Q),
      ((quotientMulAutHom hMinv a (QuotientGroup.mk' (Q0.subgroupOf Q) x)
          = QuotientGroup.mk' (Q0.subgroupOf Q) x)) ↔ ⁅(a : G), (x : G)⁆ ∈ Q0 := by
    intro a x
    rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    show ((a : G) * (x : G) * (a : G)⁻¹)⁻¹ * (x : G) ∈ Q0 ↔ ⁅(a : G), (x : G)⁆ ∈ Q0
    have hxN : (x : G) ∈ Subgroup.normalizer (Q0 : Set G) := hQQ0 x.2
    have heq : ((a : G) * (x : G) * (a : G)⁻¹)⁻¹ * (x : G)
        = (x : G)⁻¹ * ⁅(a : G), (x : G)⁆⁻¹ * ((x : G)⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [heq]
    have htransfer : ((x : G)⁻¹ * ⁅(a : G), (x : G)⁆⁻¹ * ((x : G)⁻¹)⁻¹ ∈ Q0)
        ↔ ⁅(a : G), (x : G)⁆⁻¹ ∈ Q0 :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem hxN)
        (⁅(a : G), (x : G)⁆⁻¹)).symm
    rw [htransfer, Subgroup.inv_mem_iff]
  have hmap := OddOrder.BG.Ch1.S03h.fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := φ) hcop hSolv hMinv
  have hpreimage : (Subgroup.fixedPointsOfMulAut φ ⊔ Q0.subgroupOf Q).map Q.subtype
      = Kstar ⊔ Q0 := by
    rw [Subgroup.map_sup, hfixmap, Subgroup.map_subgroupOf_eq_of_le hQ0Q]
  intro x hxQ
  have hcomapeq : (Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv)).comap
        (QuotientGroup.mk' (Q0.subgroupOf Q))
      = Subgroup.fixedPointsOfMulAut φ ⊔ Q0.subgroupOf Q := by
    rw [hmap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hkey : (∀ k ∈ K, ⁅k, x⁆ ∈ Q0) ↔ (⟨x, hxQ⟩ : ↥Q) ∈
      (Subgroup.fixedPointsOfMulAut φ ⊔ Q0.subgroupOf Q) := by
    rw [← hcomapeq, Subgroup.mem_comap, Subgroup.mem_fixedPointsOfMulAut]
    constructor
    · intro h r
      rcases r with ⟨k, hk⟩
      exact (hsmul_iff ⟨k, hk⟩ ⟨x, hxQ⟩).mpr (h k hk)
    · intro h k hk
      exact (hsmul_iff ⟨k, hk⟩ ⟨x, hxQ⟩).mp (h ⟨k, hk⟩)
  rw [hkey]
  constructor
  · intro hx
    have : x ∈ (Subgroup.fixedPointsOfMulAut φ ⊔ Q0.subgroupOf Q).map Q.subtype :=
      ⟨⟨x, hxQ⟩, hx, rfl⟩
    rwa [hpreimage] at this
  · intro hx
    have hx' : x ∈ (Subgroup.fixedPointsOfMulAut φ ⊔ Q0.subgroupOf Q).map Q.subtype := by
      rwa [hpreimage]
    obtain ⟨z, hz, hzeq⟩ := hx'
    have : z = ⟨x, hxQ⟩ := Subtype.ext hzeq
    rwa [this] at hz

/-- **Theorem 15.2(f) — the chief-factor `C`-interface `|C_{Q̄}(K)| = q`, gated producer** (mmd
L4196, BG Theorem 14.7(f)).  Discharges the `hCfix`/`hCcard` hypotheses of
`chiefFactor_card_and_commutator_of_inputs` by exhibiting the subgroup `C = K* ⊔ Q₀` of `Q` whose
image in `Q̄ = Q/Q₀` is the `K`-fixed-class subgroup `C_{Q̄}(K)`, and showing `[C : Q₀] = q`.

In the type-`P₁` situation `K* = C_{M_σ}(K) = M_σ ⊓ C_G(K)` (`hKstar`) with `|K*| = q` prime
(`hKstar_prime`), `K* ≤ Q ≤ M_σ` (`hKstarQ`, `hQMσ`), and `K* ⊄ Q₀` (`hKstarQ0`, an output of
`kstar_le_Q1_of_inputs`).  The argument (verified):

* **`C_Q(K) = K*`**: the conjugation-fixed points of `K` on `↥Q` push forward to `C_G(K) ⊓ Q`
  (`fixedPointsOfMulAut_conj_map_subtype`), and `C_G(K) ⊓ Q = M_σ ⊓ C_G(K) = K*` since `Q ≤ M_σ`
  and `K* ≤ Q`.
* **`C_{Q̄}(K)` is the image of `K*·Q₀`** (BG Proposition 1.5(d), coprime `K`-action, `hcop`):
  `C_{Q̄}(K) = (C_{↥Q}(K))·Q₀/Q₀` via `fixedPointsOfMulAut_quotientMulAutHom_eq_map`, so the
  `K`-fixed-class preimage in `Q` is `C_{↥Q}(K) ⊔ (Q₀ ↾ Q) = (K* ⊔ Q₀) ↾ Q` (`comap_map_eq`).
  This gives the membership iff `hCfix`.
* **`K* ⊓ Q₀ = ⊥`**: since `|K*| = q` is prime, `Q₀ ↾ K*` is `⊥` or `⊤`
  (`eq_bot_or_eq_top_of_prime_card`); `⊤` would force `K* ≤ Q₀`, against `hKstarQ0`.  Hence
  `|K* ⊔ Q₀| = |K*|·|Q₀|` (`card_sup_eq_mul_of_le_normalizer_of_disjoint`), so
  `[K* ⊔ Q₀ : Q₀] = |K*| = q` (`hCcard`).

The §14-gated input is `hKstar_prime` (`|K*| = q`, Theorem 14.7(f)); the normalizer/coprimality
data are structural.  Removes `hCfix`/`hCcard` from being unproduced named hypotheses of the engine:
the wrapper instantiates the engine with `C := K* ⊔ Q₀` and these two facts. -/
theorem card_centralizer_quotient_eq_of_kstar [Finite G]
    {Q Q0 K Kstar Mσ : Subgroup G} {q : ℕ} [Fact q.Prime] [(Q0.subgroupOf Q).Normal]
    (hKstar : Kstar = Mσ ⊓ Subgroup.centralizer (K : Set G))
    (hQMσ : Q ≤ Mσ) (hKstarQ : Kstar ≤ Q) (hKstar_prime : Nat.card ↥Kstar = q)
    (hQ0Q : Q0 ≤ Q) (hKstarQ0 : ¬ Kstar ≤ Q0)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hQQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G))
    (hKQ0 : K ≤ Subgroup.normalizer (Q0 : Set G))
    (hKstarQ0norm : Kstar ≤ Subgroup.normalizer (Q0 : Set G))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Q))
    (hSolv : IsSolvable ↥K ∨ IsSolvable ↥Q) :
    ∃ C : Subgroup G, Q0 ≤ C ∧ C ≤ Q ∧
      (∀ x ∈ Q, ((∀ k ∈ K, ⁅k, x⁆ ∈ Q0) ↔ x ∈ C)) ∧
      (Q0.subgroupOf C).index = q := by
  classical
  refine ⟨Kstar ⊔ Q0, le_sup_right, sup_le hKstarQ hQ0Q,
    centralizes_quotient_iff_mem_kstar_sup hKstar hQMσ hKstarQ hQ0Q hKQ hQQ0 hKQ0 hcop hSolv, ?_⟩
  · -- `hCcard`: `[K* ⊔ Q₀ : Q₀] = |K*| = q` via `|K* ⊔ Q₀| = |K*|·|Q₀|` and `card_mul_index`.
    haveI hprime : Fact (Nat.card ↥Kstar).Prime := ⟨hKstar_prime ▸ Fact.out⟩
    -- `K* ⊓ Q₀ = ⊥`: `Q₀ ↾ K*` is `⊥` or `⊤`; `⊤` forces `K* ≤ Q₀`, against `hKstarQ0`.
    have hdisj : Kstar ⊓ Q0 = ⊥ := by
      rcases (Q0.subgroupOf Kstar).eq_bot_or_eq_top_of_prime_card with hbot | htop
      · have : Disjoint Q0 Kstar := Subgroup.subgroupOf_eq_bot.mp hbot
        rw [disjoint_iff, inf_comm] at this; exact this
      · exact absurd (Subgroup.subgroupOf_eq_top.mp htop) hKstarQ0
    have hKstarN : Kstar ≤ Subgroup.normalizer (Q0 : Set G) := hKstarQ0norm
    -- `|K* ⊔ Q₀| = |K*|·|Q₀|`.
    have hcard_sup : Nat.card ↥(Kstar ⊔ Q0) = Nat.card ↥Kstar * Nat.card ↥Q0 :=
      card_sup_eq_mul_of_le_normalizer_of_disjoint hKstarN hdisj
    -- `|Q₀ ↾ (K* ⊔ Q₀)| = |Q₀|` and `card · index = |K* ⊔ Q₀|`.
    have hcardQ0sub : Nat.card ↥(Q0.subgroupOf (Kstar ⊔ Q0)) = Nat.card ↥Q0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : Q0 ≤ Kstar ⊔ Q0)).toEquiv
    have hmul := Subgroup.card_mul_index (Q0.subgroupOf (Kstar ⊔ Q0))
    rw [hcardQ0sub, hcard_sup, hKstar_prime, mul_comm q (Nat.card ↥Q0)] at hmul
    -- `hmul : |Q₀| * index = |Q₀| * q`; cancel `|Q₀| > 0`.
    have hQ0pos : 0 < Nat.card ↥Q0 := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hQ0pos hmul

open scoped commutatorElement in
/-- **Theorem 15.2(f) — `K` acts in a prime manner on the chief factor `Q̄ = Q/Q₀`** (mmd L4196,
the chief-factor engine's `hcond3`).  For a coprime `K`-action on the `q`-group `Q` with the
prime-manner action `C_{M_σ}(x) = K*` (∀ `x ∈ K#`, Proposition 14.2(a), `hprime`), every nontrivial
`x ∈ K` and `y ∈ Q` satisfy
`⁅x, y⁆ ∈ Q₀ ↔ ∀ s ∈ K, ⁅s, y⁆ ∈ Q₀` (i.e. `C_{Q̄}(x) = C_{Q̄}(K)`).

Proof: both `C_{Q̄}(x)` and `C_{Q̄}(K)` equal the image of `K* ⊔ Q₀`
(`centralizes_quotient_iff_mem_kstar_sup`, applied to `K` and to `⟨x⟩`, whose
`K* = M_σ ⊓ C_G(⟨x⟩) = M_σ ⊓ C_G(x)` coincides by the prime-manner action).  The bridge
`⁅x, y⁆ ∈ Q₀ → ∀ k ∈ ⟨x⟩, ⁅k, y⁆ ∈ Q₀` uses that `{g ∈ N_G(Q₀) | ⁅g, y⁆ ∈ Q₀}` is a subgroup
containing `x` (the standard `⁅g g', y⁆ = g ⁅g', y⁆ g⁻¹ · ⁅g, y⁆` closure), hence `⟨x⟩`.

Discharges the `hcond3` named hypothesis of `chiefFactor_card_and_commutator_of_inputs` — the only
one of its inputs without a producer. -/
theorem actsPrimeManner_quotient_of_inputs [Finite G]
    {Q Q0 K Kstar Mσ : Subgroup G} [(Q0.subgroupOf Q).Normal]
    (hKstar : Kstar = Mσ ⊓ Subgroup.centralizer (K : Set G))
    (hprime : ∀ x ∈ K, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ⊓ Mσ = Kstar)
    (hQMσ : Q ≤ Mσ) (hKstarQ : Kstar ≤ Q) (hQ0Q : Q0 ≤ Q)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hQQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G))
    (hKQ0 : K ≤ Subgroup.normalizer (Q0 : Set G))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Q))
    (hSolv : IsSolvable ↥K ∨ IsSolvable ↥Q) :
    ∀ x ∈ K, x ≠ 1 → ∀ y ∈ Q, (⁅x, y⁆ ∈ Q0 ↔ ∀ s ∈ K, ⁅s, y⁆ ∈ Q0) := by
  classical
  have hCfixK := centralizes_quotient_iff_mem_kstar_sup hKstar hQMσ hKstarQ hQ0Q hKQ hQQ0 hKQ0
    hcop hSolv
  intro x hxK hx1 y hyQ
  have hxN0 : x ∈ Subgroup.normalizer (Q0 : Set G) := hKQ0 hxK
  have hxzK : Subgroup.zpowers x ≤ K := Subgroup.zpowers_le.mpr hxK
  -- `C_G(⟨x⟩) = C_G(x)`, so the `⟨x⟩`-version's `K*` is the same `Kstar`.
  have hcentEq : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
      = Subgroup.centralizer ({x} : Set G) := by
    apply le_antisymm
    · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers x))
    · intro g hg
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      exact (Commute.zpow_left (hg x (Set.mem_singleton x)) n)
  have hKstarX : Kstar = Mσ ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [hcentEq, inf_comm]; exact (hprime x hxK hx1).symm
  haveI : IsSolvable ↥(Subgroup.zpowers x) := inferInstance
  have hCfixX := centralizes_quotient_iff_mem_kstar_sup hKstarX hQMσ hKstarQ hQ0Q
    (hxzK.trans hKQ) hQQ0 (hxzK.trans hKQ0)
    (hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hxzK)) (Or.inl inferInstance)
  refine ⟨fun hxy => (hCfixK y hyQ).mpr ((hCfixX y hyQ).mp ?_), fun h => h x hxK⟩
  -- bridge: `{g ∈ N_G(Q₀) | ⁅g, y⁆ ∈ Q₀}` is a subgroup containing `x`, hence `⟨x⟩`.
  let T : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (Q0 : Set G) ∧ ⁅g, y⁆ ∈ Q0}
      one_mem' := ⟨(Subgroup.normalizer (Q0 : Set G)).one_mem, by
        rw [commutatorElement_one_left]; exact Q0.one_mem⟩
      mul_mem' := fun {a b} ha hb => ⟨(Subgroup.normalizer (Q0 : Set G)).mul_mem ha.1 hb.1, by
        have heq : ⁅a * b, y⁆ = (a * ⁅b, y⁆ * a⁻¹) * ⁅a, y⁆ := by
          rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
        rw [heq]
        exact Q0.mul_mem ((Subgroup.mem_normalizer_iff.mp ha.1 ⁅b, y⁆).mp hb.2) ha.2⟩
      inv_mem' := fun {a} ha => ⟨(Subgroup.normalizer (Q0 : Set G)).inv_mem ha.1, by
        have heq : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * (a⁻¹)⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]; group
        rw [heq]
        exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem ha.1)
          ⁅a, y⁆⁻¹).mp (Q0.inv_mem ha.2)⟩ }
  have hxT : x ∈ T := ⟨hxN0, hxy⟩
  exact fun k hk => ((Subgroup.zpowers_le.mpr hxT) hk).2

/-- **§14-independent `⊆`-half of Theorem 15.2(g)** (mmd L4198, the easy inclusion of
`F(M) = Q ⊔ (C_G(Q) ⊓ M)`): the nilpotent `F(M)` splits as `O_π(F(M)) ⊔ O_{π'}(F(M))`
(`opiCoreInG_sup_compl_eq_of_isNilpotent`), and the `π'`-part centralizes the `π`-part
(`opiCoreInG_commutator_compl_eq_bot`) while lying in `M`, so
`F(M) ≤ O_π(F(M)) ⊔ (C_G(O_π(F(M))) ⊓ M)`.  Instantiated at `π = {q}` (with `O_q(F(M)) = Q`) this
is the easy inclusion of conjunct (g); the reverse `Q ⊔ (C_G(Q) ⊓ M) ≤ F(M)` is the
situation-specific `C_M(Q) ⊆ F(M)` (`D` nilpotent, `M_σ` not), deferred to the step-4 core. -/
theorem fittingInAmbient_le_opiCore_sup_centralizer_inf [Finite G] {M : Subgroup G} (π : Set ℕ) :
    fittingInAmbient M ≤ opiCoreInG π (fittingInAmbient M) ⊔
      (Subgroup.centralizer ((opiCoreInG π (fittingInAmbient M) : Subgroup G) : Set G) ⊓ M) := by
  haveI : Group.IsNilpotent ↥(fittingInAmbient M) := OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M
  have hsplit : opiCoreInG π (fittingInAmbient M) ⊔ opiCoreInG πᶜ (fittingInAmbient M) =
      fittingInAmbient M := opiCoreInG_sup_compl_eq_of_isNilpotent π
  have hcomm : ⁅opiCoreInG π (fittingInAmbient M), opiCoreInG πᶜ (fittingInAmbient M)⁆ = ⊥ :=
    OddOrder.BG.Ch2.S08.opiCoreInG_commutator_compl_eq_bot π (fittingInAmbient M)
  have hcent : opiCoreInG πᶜ (fittingInAmbient M) ≤
      Subgroup.centralizer ((opiCoreInG π (fittingInAmbient M) : Subgroup G) : Set G) := by
    have hcomm' : ⁅opiCoreInG πᶜ (fittingInAmbient M), opiCoreInG π (fittingInAmbient M)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]; exact hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
  have hleM : opiCoreInG πᶜ (fittingInAmbient M) ≤ M :=
    (OddOrder.GroupTheory.opiCoreInG_le πᶜ (fittingInAmbient M)).trans
      (OddOrder.BG.Ch2.S08.fittingInG_le M)
  calc fittingInAmbient M
      = opiCoreInG π (fittingInAmbient M) ⊔ opiCoreInG πᶜ (fittingInAmbient M) := hsplit.symm
    _ ≤ opiCoreInG π (fittingInAmbient M) ⊔
          (Subgroup.centralizer ((opiCoreInG π (fittingInAmbient M) : Subgroup G) : Set G) ⊓ M) :=
        sup_le_sup_left (le_inf hcent hleM) _

/-- **`O_q(F(M)) = O_q(M)`** (`§14`-independent, reusable): the `q`-core of the Fitting subgroup
equals the `q`-core of `M`.  `O_q(M) ≤ F(M)` (`opiCoreInG_singleton_le_fittingInG`) is normal in
`F(M)` (it is normal in `M ⊇ F(M)`) and a `q`-group, so `O_q(M) ≤ O_q(F(M))`; conversely
`O_q(F(M))` is normal in `M` (`M` normalizes `F(M)`, hence its `q`-core) and a `q`-subgroup of `M`,
so `O_q(F(M)) ≤ O_q(M)`.  Bridges `fittingInAmbient_le_opiCore_sup_centralizer_inf` (phrased with
`O_q(F(M))`) to Theorem 15.2's `Q = O_q(M)`. -/
theorem opiCore_singleton_fittingInAmbient_eq [Finite G] {M : Subgroup G} {q : ℕ} [Fact q.Prime] :
    opiCoreInG ({q} : Set ℕ) (fittingInAmbient M) = opiCoreInG ({q} : Set ℕ) M := by
  refine le_antisymm ?_ ?_
  · -- `O_q(F(M)) ≤ O_q(M)`: normal in `M` (char in `F(M) ◁ M`), a `q`-subgroup of `M`.
    have hle : opiCoreInG ({q} : Set ℕ) (fittingInAmbient M) ≤ M :=
      (OddOrder.GroupTheory.opiCoreInG_le _ _).trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
    have hMnorm : M ≤ Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) (fittingInAmbient M)) :=
      OddOrder.GroupTheory.le_normalizer_opiCoreInG_of_le_normalizer _
        (fun x hx => OddOrder.BG.Ch2.S08.mem_normalizer_fittingInG_of_mem hx)
    exact OddOrder.GroupTheory.le_opiCoreInG_of_normal_of_isPiSubgroup hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hMnorm)
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG _ _)
  · -- `O_q(M) ≤ O_q(F(M))`: `≤ F(M)`, normal in `F(M)`, a `q`-subgroup.
    have hle : opiCoreInG ({q} : Set ℕ) M ≤ fittingInAmbient M :=
      OddOrder.BG.Ch2.S08.opiCoreInG_singleton_le_fittingInG M
    have hFnorm : fittingInAmbient M ≤ Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) M) :=
      (OddOrder.BG.Ch2.S08.fittingInG_le M).trans
        (OddOrder.GroupTheory.le_normalizer_opiCoreInG_of_le_normalizer _ Subgroup.le_normalizer)
    exact OddOrder.GroupTheory.le_opiCoreInG_of_normal_of_isPiSubgroup hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hFnorm)
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG _ _)

/-- **Theorem 15.2(g), `⊆`-conjunct in the `Q = O_q(M)` form** (`§14`-independent): combines the
`O_π` decomposition (`fittingInAmbient_le_opiCore_sup_centralizer_inf` at `π = {q}`) with the bridge
`O_q(F(M)) = O_q(M)` (`opiCore_singleton_fittingInAmbient_eq`), giving the wrapper-ready inclusion
`F(M) ≤ Q ⊔ (C_G(Q) ⊓ M)` for the theorem's `Q = O_q(M)`.  The reverse inclusion `C_M(Q) ⊆ F(M)`
(the situation-specific step-4 core) completes the equality. -/
theorem fittingInAmbient_le_sup_centralizer_inf_of_eq_qcore [Finite G] {M Q : Subgroup G} {q : ℕ}
    [Fact q.Prime] (hQ : Q = opiCoreInG ({q} : Set ℕ) M) :
    fittingInAmbient M ≤ Q ⊔ (Subgroup.centralizer (Q : Set G) ⊓ M) := by
  subst hQ
  have h := fittingInAmbient_le_opiCore_sup_centralizer_inf (M := M) ({q} : Set ℕ)
  rwa [opiCore_singleton_fittingInAmbient_eq] at h

/-- **Theorem 15.2(g) equality — gated-endpoint skeleton** (`§14`-independent assembly): from the
hard step-4 inclusion `C_M(Q) ⊆ F(M)` (hypothesis `hcent`; the situation-specific content of
"Proposition 1.5(d) yields `F(M) = Q C_M(Q)`", which holds because `D` is nilpotent while `M_σ` is
not) together with the landed `⊆`-half (`fittingInAmbient_le_sup_centralizer_inf_of_eq_qcore`) and
`O_q(M) ⊆ F(M)`, this gives the conjunct-(g) equality `F(M) = Q ⊔ (C_G(Q) ⊓ M)` for `Q = O_q(M)`.
Once the step-4 core discharges `hcent`, the equality becomes unconditional. -/
theorem fittingInAmbient_eq_sup_centralizer_inf_of_inputs [Finite G] {M Q : Subgroup G} {q : ℕ}
    [Fact q.Prime] (hQ : Q = opiCoreInG ({q} : Set ℕ) M)
    (hcent : Subgroup.centralizer (Q : Set G) ⊓ M ≤ fittingInAmbient M) :
    fittingInAmbient M = Q ⊔ (Subgroup.centralizer (Q : Set G) ⊓ M) := by
  refine le_antisymm (fittingInAmbient_le_sup_centralizer_inf_of_eq_qcore hQ) (sup_le ?_ hcent)
  rw [hQ]; exact OddOrder.BG.Ch2.S08.opiCoreInG_singleton_le_fittingInG M

/-- **Central-extension nilpotency** (`§14`-independent, reusable): a subgroup `H ≤ K` that
centralizes a normal subgroup `Q ◁ K` is nilpotent whenever the quotient `K/Q` is nilpotent.
`H ∩ Q` lies in the centre of `H` (since `H` centralizes `Q`), and `H/(H ∩ Q)` embeds in the
nilpotent `K/Q`, so `H` is a central extension of a nilpotent group, hence nilpotent
(`Subgroup.isNilpotent_of_ker_le_center` applied to `H → K/Q`).

This is the crux of Theorem 15.2(g)'s reverse inclusion: with `K = M_σ`, `Q = O_q(M)`, and
`H = C_M(Q) ⊆ M_σ`, it shows `C_M(Q)` is nilpotent, hence (being normal in `M`) lands in `F(M)`. -/
theorem isNilpotent_of_centralizes_normal_of_quotient_isNilpotent {Q K H : Subgroup G}
    [(Q.subgroupOf K).Normal] [Group.IsNilpotent (↥K ⧸ Q.subgroupOf K)]
    (hHK : H ≤ K) (hHQ : H ≤ Subgroup.centralizer (Q : Set G)) :
    Group.IsNilpotent ↥H := by
  refine Subgroup.isNilpotent_of_ker_le_center
    ((QuotientGroup.mk' (Q.subgroupOf K)).comp (Subgroup.inclusion hHK)) ?_
  intro x hx
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact (Subgroup.mem_centralizer_iff.mp (hHQ y.2) _ hx).symm

/-- **`κ(M)`-subgroup pushed into the `κ`-Hall complement `K`** (§14 Prop 14.2 Hall machinery):
in a maximal subgroup `M` (solvable, BG `IsMinimalSimpleOdd`) with a `κ(M)`-Hall subgroup `K ≤ M`,
any `κ(M)`-subgroup `X ≤ M` is `M`-conjugate into `K`: some `w ∈ M` has `w X w⁻¹ ≤ K`.

Mirrors `exists_conj_smul_le_hallPiece` (which targets the `E`-setup Hall pieces) but targets the
ambient `κ`-Hall `K` directly: `aInvariant_piSubgroup_le_aInvariant_hall` (trivial `Unit`-action)
embeds `X` in some `κ`-Hall subgroup `H` of `↥M`, and `exists_conj_eq_of_isHall_subgroupOf`
conjugates `H` to `K` (both `κ`-Hall of the solvable `M`). -/
theorem exists_conj_smul_le_isHall_kappa [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    {X : Subgroup G} (hXM : X ≤ M)
    (hXpi : Ch03.Subgroup.IsPiGroup (S14.kappa M) (X.subgroupOf M)) :
    ∃ w ∈ M, MulAut.conj w • X ≤ K := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- Embed `X.subgroupOf M` in a `κ`-Hall subgroup `H` of `↥M` (trivial `Unit`-action).
  obtain ⟨H, hH_hall, -, hX_le_H⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (A := Unit) (φ := (1 : Unit →* MulAut ↥M))
      (by rw [Nat.card_unique]; exact Nat.coprime_one_left _)
      hXpi (fun _ => one_smul _ _)
  set HG : Subgroup G := H.map M.subtype with hHGdef
  have hHG_le_M : HG ≤ M := Subgroup.map_subtype_le _
  have hHG_hall : Ch03.IsHallSubgroup (S14.kappa M) (HG.subgroupOf M) := by
    rwa [hHGdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  -- Conjugate `HG` to `K` (both `κ`-Hall of the solvable `M`).
  obtain ⟨w, hwM, hw⟩ :=
    OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf inferInstance hHG_le_M hKM
      hHG_hall hK
  have hXHG : X ≤ HG := by
    intro x hx
    rw [hHGdef]
    exact Subgroup.mem_map.mpr ⟨⟨x, hXM hx⟩, hX_le_H (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  exact ⟨w, hwM, (conj_smul_mono (MulAut.conj w) hXHG).trans hw.le⟩

/-- **`C_M(Q) ⊆ M_σ` from the prime-manner action** (BG Theorem 15.2, mmd L4196-4198): for a
type-`P₁` maximal subgroup `M = M_σ ⋊ K` with `K` acting in a prime manner on `M_σ`
(BG Prop 14.2(a)), the centralizer `C_M(Q)` of the normal `q`-subgroup `Q ⊴ M` (with `Q ≤ M_σ`,
`K* = C_{M_σ}(K) ⊊ Q`) lies in `M_σ`.

This *corrects an earlier misdiagnosis* (the `M = (C₇⋊C₃)×(C₃₁⋊C₅)` "counterexample" violates the
prime-manner action: there a `κ`-element centralizes all of `M_σ`, so `C_{M_σ}(x) ≠ K*`).  In the
genuine type-`P₁` setting the prime-manner action makes `C_M(Q) ⊆ M_σ` derivable.

Proof: it suffices to show `C := C_M(Q)` is a `σ(M)`-group (then
`sigma_subgroup_le_Msigma_of_isHall` gives `C ⊆ M_σ`).  Suppose a prime `r ∣ |C|` with
`r ∉ σ(M)`.  As `M` is type-`P₁`,
`κ(M) = π(M) ∖ σ(M)`, so `r ∈ κ(M)`; Cauchy gives a `κ`-element `c ∈ C` of order `r`.  By the Hall
machinery (`exists_conj_smul_le_isHall_kappa`) some `w ∈ M` conjugates `⟨c⟩` into `K`: `cʷ ∈ K`,
`cʷ ≠ 1`.  Since `Q ⊴ M` (`M ≤ N_G(Q)`) and `c` centralizes `Q`, `cʷ` centralizes `Qʷ = Q`, so
`Q ≤ C_{M_σ}(cʷ) = K*` (prime manner).  With `K* ≤ Q` this forces `Q = K*`, against `K* ≠ Q`.
Hence no such `r`, i.e. `C` is a `σ`-group. -/
theorem centralizer_le_Msigma_of_primeManner [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Q Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M)
    (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hprime : ∀ x ∈ K, x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar)
    (hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hKstarQ : Kstar ≤ Q) (hKstarneQ : Kstar ≠ Q) :
    Subgroup.centralizer (Q : Set G) ⊓ M ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  set C : Subgroup G := Subgroup.centralizer (Q : Set G) ⊓ M with hCdef
  -- It suffices to show `C` is a `σ(M)`-group.
  refine OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) inf_le_right ?_
  -- `C` is a `σ(M)`-group: every prime `r ∣ |C|` lies in `σ(M)`.
  intro r hr
  by_contra hrσ
  have hr_prime : r.Prime := (Nat.mem_primeFactors.mp hr).1
  haveI : Fact r.Prime := ⟨hr_prime⟩
  -- `r ∈ π(M)` (since `r ∣ |C|` and `C ≤ M`), and `r ∉ σ(M)`, so `r ∈ κ(M)` (type-`P₁`).
  have hrπ : r ∈ S14.piSet M := by
    refine Nat.mem_primeFactors.mpr ⟨hr_prime, ?_, Nat.card_pos.ne'⟩
    exact (Nat.mem_primeFactors.mp hr).2.1.trans (Subgroup.card_dvd_of_le inf_le_right)
  have hrκ : r ∈ S14.kappa M := by
    rw [hP1.2]; exact ⟨hrπ, hrσ⟩
  -- A `κ`-element `c ∈ C` of order `r` (Cauchy in `↥C`).
  obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) r
    ((Nat.mem_primeFactors.mp hr).2.1)
  have hc_ne : (c : G) ≠ 1 := by
    intro hc1
    have h1 : orderOf c = 1 := by
      rw [show c = 1 from Subtype.ext hc1]; exact orderOf_one
    rw [hc_ord] at h1; exact hr_prime.ne_one h1
  -- `X := ⟨c⟩ ≤ M` is a `κ(M)`-group.
  have hcC : (c : G) ∈ C := c.2
  have hcC' : (c : G) ∈ Subgroup.centralizer (Q : Set G) ⊓ M := hCdef ▸ hcC
  have hcM : (c : G) ∈ M := (Subgroup.mem_inf.mp hcC').2
  set X : Subgroup G := Subgroup.zpowers (c : G) with hXdef
  have hXM : X ≤ M := by rw [hXdef]; exact Subgroup.zpowers_le.mpr hcM
  have hord_coe : orderOf (c : G) = r := by rw [Subgroup.orderOf_coe, hc_ord]
  have hXpi : Ch03.Subgroup.IsPiGroup (S14.kappa M) (X.subgroupOf M) := by
    intro s hs
    -- `|X.subgroupOf M| = |X| = orderOf c = r`, so its only prime factor is `r ∈ κ(M)`.
    have hcard : Nat.card ↥(X.subgroupOf M) = r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv, hXdef,
        Nat.card_zpowers, hord_coe]
    rw [hcard, hr_prime.primeFactors, Finset.mem_singleton] at hs
    rw [hs]; exact hrκ
  -- Conjugate `X` into `K`: `cʷ ∈ K`, `cʷ ≠ 1`.
  obtain ⟨w, hwM, hwle⟩ := exists_conj_smul_le_isHall_kappa hG hM hKM hK hXM hXpi
  set cw : G := w * (c : G) * w⁻¹ with hcwdef
  have hcw_mem_smul : cw ∈ MulAut.conj w • X := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
      hcwdef]
    rw [hXdef, show w⁻¹ * (w * (c : G) * w⁻¹) * w = (c : G) by group]
    exact Subgroup.mem_zpowers _
  have hcwK : cw ∈ K := hwle hcw_mem_smul
  have hcw_ne : cw ≠ 1 := by
    intro h
    apply hc_ne
    have hconj : w⁻¹ * cw * w = (c : G) := by rw [hcwdef]; group
    rw [h, mul_one, inv_mul_cancel] at hconj
    exact hconj.symm
  -- `Q ≤ C_{M_σ}(cʷ) = K*`: `cʷ` centralizes `Qʷ = Q`, and `Q ≤ M_σ`.
  have hc_cent : (c : G) ∈ Subgroup.centralizer (Q : Set G) := (Subgroup.mem_inf.mp hcC').1
  have hQcent : Q ≤ Subgroup.centralizer ({cw} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    rintro g hg
    rw [Set.mem_singleton_iff] at hg; subst hg
    -- `w⁻¹ y w ∈ Q` (`Q ⊴ M`, `w ∈ M`), and `c` centralizes it.
    have hwinvN : w⁻¹ ∈ Subgroup.normalizer (Q : Set G) := hMnormQ (M.inv_mem hwM)
    have hwinvyw : w⁻¹ * y * w ∈ Q := by
      have hmem : w⁻¹ * y * (w⁻¹)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hwinvN y).mp hy
      rwa [inv_inv] at hmem
    have hcyc : (w⁻¹ * y * w) * (c : G) = (c : G) * (w⁻¹ * y * w) :=
      Subgroup.mem_centralizer_iff.mp hc_cent (w⁻¹ * y * w) hwinvyw
    -- Translate back: `cw * y = y * cw`.
    rw [hcwdef]
    calc w * (c : G) * w⁻¹ * y
        = w * ((c : G) * (w⁻¹ * y * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * y * w) * (c : G)) * w⁻¹ := by rw [hcyc]
      _ = y * (w * (c : G) * w⁻¹) := by group
  have hQKstar : Q ≤ Kstar := by
    rw [← hprime cw hcwK hcw_ne]
    exact le_inf hQcent hQMσ
  exact hKstarneQ (le_antisymm hKstarQ hQKstar)

/-- **`D ⋊ K` is a Frobenius group from the prime-manner action** (BG Theorem 15.2, mmd L4196-4200,
BG Theorem 3.10(b)(c) input): for the `q'`-Hall complement `D` of `Q` in `M_σ` and the `κ`-Hall
complement `K`, the group `D ⊔ K` is Frobenius with kernel `D` and complement `K`.

The Frobenius (fixed-point-free) condition is exactly the prime-manner action: a `k ∈ K#` fixing
`n ∈ D#` would centralize it, so `n ∈ C_{M_σ}(k) = K* ⊆ Q` (`hprime`, `hKstarQ`; `D ≤ M_σ`), while
`n ∈ D` and `D ∩ Q = 1` (`hDQ`), forcing `n = 1`.  The remaining structure is bookkeeping:
`D ◁ D⊔K` (`K ≤ N_G(D)`, `hKnormD`), `D, K` complements (`D ∩ K = 1`, `hDK`), both nontrivial.

Discharges the `hfrob` hypothesis of `chiefFactor_card_and_commutator_of_inputs`. -/
theorem isFrobeniusGroup_DK_of_primeManner
    {M K D Kstar Q : Subgroup G}
    (hprime : ∀ x ∈ K, x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar)
    (hDMσ : D ≤ OddOrder.BG.Ch3.S10.Msigma M) (hKstarQ : Kstar ≤ Q) (hDQ : Disjoint D Q)
    (hKnormD : K ≤ Subgroup.normalizer (D : Set G)) (hDK : Disjoint D K)
    (hDne : D ≠ ⊥) (hKne : K ≠ ⊥) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(D ⊔ K)
      (D.subgroupOf (D ⊔ K)) (K.subgroupOf (D ⊔ K)) := by
  have hDL : D ≤ D ⊔ K := le_sup_left
  have hKL : K ≤ D ⊔ K := le_sup_right
  -- `D ◁ D⊔K` from `D ≤ N(D)` and `K ≤ N(D)`.
  have hDnormD : (D : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer
  haveI hDLnormal : (D.subgroupOf (D ⊔ K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mpr (sup_le hDnormD hKnormD)
  refine
    { isNormal := hDLnormal
      isComplement := ?_
      ne_bot_kernel := ?_
      ne_bot_complement := ?_
      conj_frobenius := ?_ }
  · -- `D` and `K` are complements in `D ⊔ K`.
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [Subgroup.disjoint_def]
      intro x hxD hxK
      rw [Subgroup.mem_subgroupOf] at hxD hxK
      exact Subtype.ext (Subgroup.disjoint_def.mp hDK hxD hxK)
    · have hsup : D.subgroupOf (D ⊔ K) ⊔ K.subgroupOf (D ⊔ K) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hDL hKL, Subgroup.subgroupOf_self]
      have := Subgroup.normal_mul (D.subgroupOf (D ⊔ K)) (K.subgroupOf (D ⊔ K))
      rw [hsup, Subgroup.coe_top] at this
      exact this.symm
  · -- kernel nontrivial.
    intro hbot
    exact hDne (by
      have := Subgroup.map_mono (f := (D ⊔ K).subtype) (le_of_eq hbot)
      rwa [Subgroup.map_subgroupOf_eq_of_le hDL, Subgroup.map_bot, le_bot_iff] at this)
  · -- complement nontrivial.
    intro hbot
    exact hKne (by
      have := Subgroup.map_mono (f := (D ⊔ K).subtype) (le_of_eq hbot)
      rwa [Subgroup.map_subgroupOf_eq_of_le hKL, Subgroup.map_bot, le_bot_iff] at this)
  · -- Frobenius condition = fixed-point-free = prime manner.
    rintro a ha ha1 n hn hn1 hfix
    rw [Subgroup.mem_subgroupOf] at ha hn
    have haK : (a : G) ∈ K := ha
    have ha1G : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hnG : (n : G) ≠ 1 := fun h => hn1 (Subtype.ext h)
    have hfixG : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := Subtype.ext_iff.mp hfix
    -- `n ∈ C_G(a)`: `a n a⁻¹ = n` ⟹ `a n = n a`.
    have han : (a : G) * (n : G) = (n : G) * (a : G) := by
      rw [mul_inv_eq_iff_eq_mul] at hfixG; exact hfixG
    have hnCent : (n : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro g hg
      rw [Set.mem_singleton_iff] at hg; subst hg
      exact han
    -- `n ∈ C_{M_σ}(a) = K* ⊆ Q`, while `n ∈ D` and `D ∩ Q = 1`.
    have hnMσ : (n : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := hDMσ hn
    have hnKstar : (n : G) ∈ Kstar := by
      rw [← hprime (a : G) haK ha1G]; exact Subgroup.mem_inf.mpr ⟨hnCent, hnMσ⟩
    have hnQ : (n : G) ∈ Q := hKstarQ hnKstar
    exact hnG (Subgroup.disjoint_def.mp hDQ hn hnQ)

/-- **BG Theorem 15.2 step 3-4, the chief-factor engine wiring** (mmd L4194-4196): given the
type-`P₁` data with `Q = O_q(M)`, the `K`-invariant complement `D` of `Q` in `M_σ`, and the
*output of `chiefFactor_Q0_normal_minimal_of_inputs`* (the normal `Q₀ = C_Q(D) ⊴ M`, `¬ K* ≤ Q₀`,
`Q₀ < Q`, and the lattice-minimality), it runs Theorem 3.10 on the Frobenius group `KD` and yields
the chief-factor index `[Q : Q₀] = q^{|K|}` with `|K|` prime, the commutator constraint
`D' ⊆ C_D(Q̄)`, and the elementary abelian section `Q̄ = Q/Q₀`.

Chains the chief-factor producers: `isElementaryAbelian_chiefFactor_of_minimalNormal`
(`hEA`/`hNT`), `card_centralizer_quotient_eq_of_kstar` (`hCfix`/`hCcard`),
`isFrobeniusGroup_DK_of_primeManner` (`hfrob`), `mem_centralizer_of_centralizes_quotient`
(`hFPF`), `actsPrimeManner_quotient_of_inputs` (`hcond3`), and the Theorem 3.10 engine
`chiefFactor_card_and_commutator_of_inputs`.  The coprimality `gcd(|D ⊔ K|, |Q|) = 1` uses
`|D ⊔ K| = |K|·|D|` (the Frobenius semidirect structure). -/
theorem chiefFactor_engine_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar Q D Q0 : Subgroup G} {q : ℕ} [Fact q.Prime]
    [(Q0.subgroupOf Q).Normal]
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hQ : Q = opiCoreInG ({q} : Set ℕ) M)
    (hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M) (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hKstarQ : Kstar ≤ Q) (hKne : K ≠ ⊥)
    (hKMσdisj : Disjoint K (OddOrder.BG.Ch3.S10.Msigma M))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)))
    (hDq' : q ∉ (Nat.card ↥D).primeFactors)
    (hDMσ : D ≤ OddOrder.BG.Ch3.S10.Msigma M) (hKnormD : K ≤ Subgroup.normalizer (D : Set G))
    (hQDdisj : Disjoint Q D) (hDne : D ≠ ⊥)
    (hQ0def : Q0 = Q ⊓ Subgroup.centralizer (D : Set G))
    (hMNQ0 : M ≤ Subgroup.normalizer (Q0 : Set G)) (hKstarNotQ0 : ¬ Kstar ≤ Q0)
    (hQ0ltQ : Q0 < Q)
    (hmin : ∀ H : Subgroup G, Q0 < H → H ≤ Q → (H.subgroupOf M).Normal → Q ≤ H) :
    (Nat.card ↥K).Prime ∧
      (Q0.subgroupOf Q).index = q ^ Nat.card ↥K ∧
      (∀ g ∈ ⁅D, D⁆, ∀ x ∈ Q, ⁅g, x⁆ ∈ Q0) ∧
      OddOrder.GroupTheory.IsElementaryAbelian q (↥Q ⧸ Q0.subgroupOf Q) := by
  classical
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hQM : Q ≤ M := hQMσ.trans hMσM
  have hDM : D ≤ M := hDMσ.trans hMσM
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hQpg : IsPGroup q ↥Q := by rw [hQ]; exact isPGroup_opiCoreInG_singleton M
  have hQ0Q : Q0 ≤ Q := hQ0ltQ.le
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := hKM.trans hMnormQ
  have hDNQ : D ≤ Subgroup.normalizer (Q : Set G) := hDM.trans hMnormQ
  have hQQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G) := hQM.trans hMNQ0
  have hKQ0 : K ≤ Subgroup.normalizer (Q0 : Set G) := hKM.trans hMNQ0
  have hDNQ0 : D ≤ Subgroup.normalizer (Q0 : Set G) := hDM.trans hMNQ0
  have hKstarN : Kstar ≤ Subgroup.normalizer (Q0 : Set G) := hKstarQ.trans hQQ0
  have hSolvQ : IsSolvable ↥Q := solvable_of_solvable_injective (Subgroup.inclusion_injective hQM)
  have hsolvDK : IsSolvable ↥(D ⊔ K) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective (sup_le hDM hKM))
  have hKstarP : (Nat.card ↥Kstar).Prime := kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar
  have hKstarEqQ : Nat.card ↥Kstar = q := by
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    have hdvd : Nat.card ↥Kstar ∣ Nat.card ↥Q := Subgroup.card_dvd_of_le hKstarQ
    rw [hn] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hKstarP Fact.out).mp (hKstarP.dvd_of_dvd_pow hdvd)
  have hqD : ¬ q ∣ Nat.card ↥D := fun hdvd =>
    hDq' (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)
  have hcopDQ : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    rw [hn]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simpa using Nat.coprime_one_right _
    · rw [Nat.coprime_pow_right_iff h0]
      exact ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hqD).symm
  have hcopKQ : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Q) :=
    hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hQMσ)
  have hDKdisj : Disjoint D K := hKMσdisj.symm.mono_left hDMσ
  have hcopDKQ : Nat.Coprime (Nat.card ↥(D ⊔ K)) (Nat.card ↥Q) := by
    have hcardsup : Nat.card ↥(D ⊔ K) = Nat.card ↥K * Nat.card ↥D := by
      rw [sup_comm]
      exact card_sup_eq_mul_of_le_normalizer_of_disjoint hKnormD (disjoint_iff.mp hDKdisj.symm)
    rw [hcardsup]; exact Nat.coprime_mul_iff_left.mpr ⟨hcopKQ, hcopDQ⟩
  have hprime := actsPrimeManner_of_typeP hG hM hP1.1 hKM hK hKstar
  obtain ⟨hEA, hNT⟩ :=
    isElementaryAbelian_chiefFactor_of_minimalNormal hQ0ltQ hQM hQpg hMnormQ hMNQ0 hmin
  obtain ⟨C, hQ0C, hCQ, hCfix, hCcard⟩ :=
    card_centralizer_quotient_eq_of_kstar hKstar hQMσ hKstarQ hKstarEqQ hQ0Q hKstarNotQ0 hKQ hQQ0
      hKQ0 hKstarN hcopKQ (Or.inr hSolvQ)
  have hfrob := isFrobeniusGroup_DK_of_primeManner (M := M) hprime hDMσ hKstarQ hQDdisj.symm hKnormD
    hDKdisj hDne hKne
  have hFPF : ∀ x ∈ Q, (∀ d ∈ D, ⁅d, x⁆ ∈ Q0) → x ∈ Q0 :=
    fun x hxQ hfix => mem_centralizer_of_centralizes_quotient hQ0def hDNQ hQQ0 hDNQ0 hcopDQ
      (Or.inr hSolvQ) hxQ hfix
  have hcond3 := actsPrimeManner_quotient_of_inputs hKstar hprime hQMσ hKstarQ hQ0Q hKQ hQQ0 hKQ0
    hcopKQ (Or.inr hSolvQ)
  obtain ⟨hKprime, hindex, hDcomm⟩ :=
    chiefFactor_card_and_commutator_of_inputs hQ0Q hQ0C hCQ hDne hEA hNT hDNQ hKQ hDNQ0 hKQ0 hQQ0
      hsolvDK hfrob hcopDKQ hFPF hcond3 hCfix hCcard
  exact ⟨hKprime, hindex, hDcomm, hEA⟩

/-- **Theorem 15.2(g) reverse inclusion, reduced to `C_M(Q) ⊆ M_σ`** (mmd L4196-4198): if the
centralizer `C_M(Q)` of the normal `q`-subgroup `Q` lies in `M_σ` (the genuinely BG-specific input,
from `σ`-uniqueness — it does *not* follow from local structure, cf. the ChatGPT-verified counter-
example `M = (C₇⋊C₃)×(C₃₁⋊C₅)`), then `C_M(Q) ⊆ F(M)`.  `C_M(Q)` is nilpotent
(`isNilpotent_of_centralizes_normal_of_quotient_isNilpotent`: it centralizes `Q ◁ M_σ` and
`M_σ/Q` is nilpotent) and normal in `M` (`M ≤ N_G(Q) ≤ N_G(C_G(Q))`), so a nilpotent normal
subgroup of `M` lands in `F(M)` (`nilpotent_normal_le_fitting`).  Discharges the `hcent` input of
`fittingInAmbient_eq_sup_centralizer_inf_of_inputs`. -/
theorem centralizer_inf_le_fittingInAmbient_of_le_Msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    [(Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal]
    [Group.IsNilpotent (↥(OddOrder.BG.Ch3.S10.Msigma M) ⧸
      Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))]
    (hCle : Subgroup.centralizer (Q : Set G) ⊓ M ≤ OddOrder.BG.Ch3.S10.Msigma M) :
    Subgroup.centralizer (Q : Set G) ⊓ M ≤ fittingInAmbient M := by
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- `C_M(Q)` is nilpotent (central extension over the nilpotent `M_σ/Q`).
  haveI : Group.IsNilpotent ↥(Subgroup.centralizer (Q : Set G) ⊓ M) :=
    isNilpotent_of_centralizes_normal_of_quotient_isNilpotent hCle inf_le_left
  -- `C_M(Q) ◁ M` (`M` normalizes `Q`, hence `C_G(Q)`, hence `C_G(Q) ⊓ M`).
  have hMnormC : M ≤ Subgroup.normalizer
      ((Subgroup.centralizer (Q : Set G) ⊓ M : Subgroup G) : Set G) :=
    le_normalizer_inf (hMnormQ.trans (normalizer_le_normalizer_centralizer Q)) Subgroup.le_normalizer
  haveI : ((Subgroup.centralizer (Q : Set G) ⊓ M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hMnormC
  haveI : Group.IsNilpotent ↥((Subgroup.centralizer (Q : Set G) ⊓ M).subgroupOf M) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      Subgroup.centralizer (Q : Set G) ⊓ M ≤ M)).symm
  -- Nilpotent normal subgroup of `M` lands in `F(M)`.
  calc Subgroup.centralizer (Q : Set G) ⊓ M
      = ((Subgroup.centralizer (Q : Set G) ⊓ M).subgroupOf M).map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le inf_le_right).symm
    _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype :=
        Subgroup.map_mono OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    _ = fittingInAmbient M := rfl

/-- **BG Theorem 15.2(g), assembled from the single `σ`-gap `C_M(Q) ⊆ M_σ`** (mmd L4196-4198):
chains the equality skeleton (`fittingInAmbient_eq_sup_centralizer_inf_of_inputs`) with the reduced
reverse inclusion (`centralizer_inf_le_fittingInAmbient_of_le_Msigma`).  For `Q = O_q(M)` with
`M_σ/Q` nilpotent, the conjunct `F(M) = Q ⊔ (C_G(Q) ⊓ M)` follows from `C_M(Q) ⊆ M_σ` alone.  This
is the wrapper-facing form: the only outstanding input is the BG-specific `C_M(Q) ⊆ M_σ` (a
`σ`-uniqueness fact to be supplied from the global analysis / forward input). -/
theorem fittingInAmbient_eq_sup_centralizer_inf_of_le_Msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : M ∈ maximalSubgroups G) (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hQ : Q = opiCoreInG ({q} : Set ℕ) M)
    [(Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal]
    [Group.IsNilpotent (↥(OddOrder.BG.Ch3.S10.Msigma M) ⧸
      Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))]
    (hCle : Subgroup.centralizer (Q : Set G) ⊓ M ≤ OddOrder.BG.Ch3.S10.Msigma M) :
    fittingInAmbient M = Q ⊔ (Subgroup.centralizer (Q : Set G) ⊓ M) :=
  fittingInAmbient_eq_sup_centralizer_inf_of_inputs hQ
    (centralizer_inf_le_fittingInAmbient_of_le_Msigma hG hM hMnormQ hCle)

/-- **`D = ⁅D, K⁆` from the Frobenius (fixed-point-free) action** (BG Theorem 15.2, mmd L4202,
BG Lemma 6.3(a) flavour but via the coprime decomposition): if `D ⊔ K` is a Frobenius group with
kernel `D` and complement `K` (so `K` acts fixed-point-freely on `D`), `K ≤ N_G(D)`, and the orders
of `K` and `D` are coprime with `D`/`K` one-sided solvable, then `⁅D, K⁆ = D`.

`Proposition 1.6(d)` (`subgroup_coprime_decomposition`) gives `D = C_D(K) ⊔ ⁅D, K⁆`; the Frobenius
condition forces `C_D(K) = C_G(K) ⊓ D = ⊥` (a nontrivial `d ∈ D` centralizing a nontrivial `k ∈ K`
would be fixed by conjugation, contradicting `conj_frobenius`), so the decomposition collapses to
`D = ⁅D, K⁆`. -/
theorem commutator_eq_self_of_frobenius_DK [Finite G] {D K : Subgroup G}
    (hKne : K ≠ ⊥)
    (hFrobFPF : ∀ a ∈ K, a ≠ 1 → ∀ n ∈ D, n ≠ 1 → a * n * a⁻¹ ≠ n)
    (hKnormD : K ≤ Subgroup.normalizer (D : Set G))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥D))
    (hSolv : IsSolvable ↥K ∨ IsSolvable ↥D) :
    ⁅D, K⁆ = D := by
  -- `C_G(K) ⊓ D = ⊥`: a nontrivial common element contradicts the Frobenius condition.
  have hCDK : (Subgroup.centralizer (K : Set G) ⊓ D : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro d hd
    rw [Subgroup.mem_inf] at hd
    obtain ⟨hdcent, hdD⟩ := hd
    by_contra hdne
    rw [Subgroup.mem_bot] at hdne
    -- Pick a nontrivial `k ∈ K`.
    haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
    obtain ⟨k, hkK, hkne⟩ := (Subgroup.nontrivial_iff_exists_ne_one K).mp inferInstance
    -- `k` and `d` commute (from `d ∈ C_G(K)`), so `k * d * k⁻¹ = d`, contradicting Frobenius.
    have hcomm : k * d = d * k := (Subgroup.mem_centralizer_iff.mp hdcent) k hkK
    have hfix : k * d * k⁻¹ = d := by rw [hcomm]; group
    exact hFrobFPF k hkK hkne d hdD hdne hfix
  -- Proposition 1.6(d): `D = (C_G(K) ⊓ D) ⊔ ⁅D, K⁆`.
  have hdecomp := OddOrder.BG.Ch3.S13.subgroup_coprime_decomposition hKnormD hcop hSolv
  rw [hCDK, bot_sup_eq] at hdecomp
  exact hdecomp.symm

-- The iterated quotient `(↥N ⧸ ψ.ker) ⧸ O_q(…)` makes the `Group`-instance synthesis for the
-- `mk' _ ⁅x, y⁆ = 1` step exceed the default `synthInstance` budget; raise it locally.
set_option synthInstance.maxHeartbeats 80000 in
/-- **Theorem 15.2 step 5 — `D` centralizes `Q` for narrow `Q`** (mmd L4202, BG Theorem 5.5(a)):
if `Q` is a narrow `q`-group (`q` odd), `D ⊔ K` is a Frobenius group with kernel `D` and complement
`K` acting in a prime manner, `D ⊔ K ≤ N_G(Q)`, `D` is a `q'`-group (`q ∤ |D|`), and the orders of
`K`, `D` are coprime, then `D ⊆ C_G(Q)`.

`N := N_G(Q)` is proper (`Q ≠ 1, G` in the simple `G`), hence solvable; the conjugation action
`ψ : N → MulAut Q` has kernel `C_G(Q) ⊓ N`.  Theorem 5.5(a) (`solvableAut_of_narrow`, applied to the
faithful action of `N/ker`) gives that `(N/ker)'` is a `q`-group.  By the Frobenius condition
`⁅D, K⁆ = D` (`commutator_eq_self_of_frobenius_DK`), so `D ⊆ ⁅N, N⁆ = N'`; the image of `D` in
`N/ker` therefore lies in `(N/ker)'` (a `q`-group) yet is a `q'`-group (`q ∤ |D|`), hence trivial.
Trivial image means `D ⊆ ker ψ = C_G(Q) ⊓ N`, i.e. `D ⊆ C_G(Q)`. -/
theorem D_centralizes_Q_of_narrow [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {Q D K : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hq_odd : Odd q) (hQpg : IsPGroup q ↥Q) (hQnarrow : OddOrder.GroupTheory.IsNarrow q ↥Q)
    (hQne : Q ≠ ⊥)
    (hKne : K ≠ ⊥)
    (hFrobFPF : ∀ a ∈ K, a ≠ 1 → ∀ n ∈ D, n ≠ 1 → a * n * a⁻¹ ≠ n)
    (hKnormD : K ≤ Subgroup.normalizer (D : Set G))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥D))
    (hKsolv : IsSolvable ↥K)
    (hDKN : D ⊔ K ≤ Subgroup.normalizer (Q : Set G))
    (hqD : ¬ q ∣ Nat.card ↥D) :
    D ≤ Subgroup.centralizer (Q : Set G) := by
  classical
  have hp_prime : q.Prime := Fact.out
  -- `N := N_G(Q)` is a proper (hence solvable) subgroup of the simple `G`.
  set N : Subgroup G := Subgroup.normalizer (Q : Set G) with hN_def
  have hNlt : N < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hQnorm : Q.Normal := by rw [← Subgroup.normalizer_eq_top_iff]; exact htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal Q hQnorm with h | h
    · exact hQne h
    · have hGpg : IsPGroup q G := (h ▸ hQpg : IsPGroup q ↥(⊤ : Subgroup G)).of_surjective
        (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom Subgroup.topEquiv.surjective
      haveI : Group.IsNilpotent G := hGpg.isNilpotent
      exact hG.notSolvable inferInstance
  haveI hNsolv : IsSolvable ↥N := hG.solvable_of_lt_top N hNlt
  -- The conjugation action `ψ : N → Aut Q` with kernel `C_G(Q) ∩ N`.
  set ψ : ↥N →* MulAut ↥Q := Q.normalizerMonoidHom with hψ_def
  have hψker : ψ.ker = (Subgroup.centralizer (Q : Set G)).subgroupOf N :=
    Q.normalizerMonoidHom_ker
  -- `A := N / ker ψ` acts faithfully, is solvable and odd.
  have hA_odd : Odd (Nat.card (↥N ⧸ ψ.ker)) := by
    refine hG.odd.of_dvd_nat (dvd_trans ?_ (Subgroup.card_subgroup_dvd_card N))
    simpa [Subgroup.index] using Subgroup.index_dvd_card ψ.ker
  -- Theorem 5.5(a): `(N / ker)'` is a `q`-group.
  obtain ⟨hcomm, -, -, -⟩ := Ch1.S05.solvableAut_of_narrow hq_odd hQpg hQnarrow
    (QuotientGroup.kerLift ψ) (QuotientGroup.kerLift_injective ψ) hA_odd
  have hA' : IsPGroup q (_root_.commutator (↥N ⧸ ψ.ker)) := by
    have hle : _root_.commutator (↥N ⧸ ψ.ker) ≤ Ch01.opCore q (↥N ⧸ ψ.ker) := by
      rw [_root_.commutator, Subgroup.commutator_le]
      intro x _ y _
      have h1 : QuotientGroup.mk' (Ch01.opCore q (↥N ⧸ ψ.ker)) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm _ _
      exact (QuotientGroup.eq_one_iff _).mp h1
    exact (Ch01.opCore_isPGroup q _).to_le hle
  -- `D ⊔ K ≤ N`, so `D ≤ N`; and `D = ⁅D, K⁆ ≤ N'`.
  have hDN : (D : Subgroup G) ≤ N := le_sup_left.trans hDKN
  have hDcommDK : ⁅D, K⁆ = D :=
    commutator_eq_self_of_frobenius_DK hKne hFrobFPF hKnormD hcop (Or.inl hKsolv)
  have hDcomm : (D : Subgroup G).subgroupOf N ≤ _root_.commutator ↥N := by
    have hDder : (D : Subgroup G) ≤ derivedInG N := by
      rw [← hDcommDK]
      calc ⁅D, K⁆ ≤ ⁅N, N⁆ := Subgroup.commutator_mono hDN (le_sup_right.trans hDKN)
        _ = derivedInG N := (Subgroup.map_subtype_commutator N).symm
    have key : ((_root_.commutator ↥N).map N.subtype).comap N.subtype = _root_.commutator ↥N :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective (_root_.commutator ↥N)
    calc (D : Subgroup G).subgroupOf N
        ≤ (derivedInG N).comap N.subtype := Subgroup.comap_mono hDder
      _ = _root_.commutator ↥N := key
  -- The image of `D` in `A` is `≤ (N/ker)'` (a `q`-group) and is a `q'`-group: hence trivial.
  set DA : Subgroup (↥N ⧸ ψ.ker) :=
    ((D : Subgroup G).subgroupOf N).map (QuotientGroup.mk' ψ.ker) with hDA_def
  have hDA_q : IsPGroup q ↥DA := by
    refine hA'.to_le ?_
    calc DA ≤ (_root_.commutator ↥N).map (QuotientGroup.mk' ψ.ker) := Subgroup.map_mono hDcomm
      _ ≤ _root_.commutator (↥N ⧸ ψ.ker) := by
          rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator]
          exact Subgroup.commutator_mono le_top le_top
  -- `q ∤ |DA|`: `|DA|` divides `|D|` (surjective images), and `q ∤ |D|`.
  have hDA_card_dvd : Nat.card ↥DA ∣ Nat.card ↥D := by
    have h1 : Nat.card ↥DA ∣ Nat.card ↥((D : Subgroup G).subgroupOf N) :=
      Subgroup.card_map_dvd (H := (D : Subgroup G).subgroupOf N) (QuotientGroup.mk' ψ.ker)
    have h2 : Nat.card ↥((D : Subgroup G).subgroupOf N) = Nat.card ↥D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv
    rw [h2] at h1; exact h1
  have hqDA : ¬ q ∣ Nat.card ↥DA := fun h => hqD (h.trans hDA_card_dvd)
  -- A `q`-group with `q ∤ |DA|` is trivial.
  have hDA_bot : DA = ⊥ := by
    obtain ⟨k, hk⟩ := hDA_q.exists_card_eq
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero] at hk; exact Subgroup.card_eq_one.mp hk
    · exact absurd (hk ▸ dvd_pow_self q hkpos.ne') hqDA
  -- Trivial image means `D ≤ ker ψ = C_G(Q) ∩ N`, hence `D ≤ C_G(Q)`.
  have hDker : (D : Subgroup G).subgroupOf N ≤ ψ.ker := by
    rw [hDA_def, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hDA_bot
    exact hDA_bot
  rw [hψker] at hDker
  intro x hx
  have hxN : x ∈ N := hDN hx
  have : (⟨x, hxN⟩ : ↥N) ∈ (Subgroup.centralizer (Q : Set G)).subgroupOf N :=
    hDker (by rw [Subgroup.mem_subgroupOf]; exact hx)
  rw [Subgroup.mem_subgroupOf] at this
  exact this

/-- **Theorem 15.2 step 5 — `D` centralizes `Q` from `q ∉ β(M)`** (mmd L4202): the `hDcent` input of
`mem_beta_of_inputs`, with the narrowness of `Q` discharged from `q ∉ β(M)`.

When `Q = O_q(M)` is (the image in `G` of) a Sylow `q`-subgroup `P` of `M` — which holds in the
type-P1 setting, since `M_σ/Q` is a `q'`-group, so the normal Sylow `q` of `M_σ` is a Sylow `q` of
`M` — narrowness of `↥Q ≅ ↥P` follows from `q ∉ β(M)` (`isNarrow_sylow_of_not_mem_beta`, BG Lemma
10.8 setup).  Chaining with `D_centralizes_Q_of_narrow` (the Theorem 5.5(a) gate) gives
`q ∉ β(M) → D ⊆ C_G(Q)`, exactly the `hDcent` hypothesis of `mem_beta_of_inputs`. -/
theorem D_centralizes_Q_of_not_mem_beta [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M Q D K : Subgroup G} {q : ℕ} [Fact q.Prime] (hM : M ∈ maximalSubgroups G)
    (hq_odd : Odd q) (hQpg : IsPGroup q ↥Q) (hQne : Q ≠ ⊥)
    (hqπ : q ∈ (Nat.card ↥M).primeFactors)
    (P : Sylow q ↥M) (hQP : Q = (P : Subgroup ↥M).map M.subtype)
    (hKne : K ≠ ⊥)
    (hFrobFPF : ∀ a ∈ K, a ≠ 1 → ∀ n ∈ D, n ≠ 1 → a * n * a⁻¹ ≠ n)
    (hKnormD : K ≤ Subgroup.normalizer (D : Set G))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥D))
    (hKsolv : IsSolvable ↥K)
    (hDKN : D ⊔ K ≤ Subgroup.normalizer (Q : Set G))
    (hqD : ¬ q ∣ Nat.card ↥D) :
    q ∉ OddOrder.BG.Ch3.S10.beta M → D ≤ Subgroup.centralizer (Q : Set G) := by
  intro hqβ
  -- Narrowness of the Sylow `P`, transferred along `↥Q ≅ ↥P`.
  have hPnarrow : OddOrder.GroupTheory.IsNarrow q ↥(P : Subgroup ↥M) :=
    OddOrder.BG.Ch3.S10.isNarrow_sylow_of_not_mem_beta hG hM hqπ hqβ P
  have eQP : ↥Q ≃* ↥(P : Subgroup ↥M) :=
    (MulEquiv.subgroupCongr hQP).trans
      (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).symm
  have hQnarrow : OddOrder.GroupTheory.IsNarrow q ↥Q :=
    OddOrder.GroupTheory.IsNarrow.of_mulEquiv eQP.symm hPnarrow
  exact D_centralizes_Q_of_narrow hG hq_odd hQpg hQnarrow hQne hKne hFrobFPF hKnormD hcop hKsolv
    hDKN hqD

/-- **Theorem 15.2 step 5 — `q ∈ β(M)`, gated-endpoint skeleton** (mmd L4202): "if `q ∉ β(M)`,
then Theorem 5.5(a) shows `(DK)' = D` centralizes `Q`, a contradiction".  The contradiction is
clean: `D` centralizing `Q` means `Q ≤ C_G(D)`, i.e. `C_Q(D) = Q`, against the established
`C_Q(D) = Q₀ ⊊ Q` (`M_σ` non-nilpotent).  Reduces `q ∈ β(M)` to the single Theorem-5.5 input
`hDcent` (`q ∉ β(M) → D ⊆ C_G(Q)`) and the proper-centralizer fact `hQ0` (`¬ Q ⊆ C_G(D)`). -/
theorem mem_beta_of_inputs {M Q D : Subgroup G} {q : ℕ}
    (hQ0 : ¬ Q ≤ Subgroup.centralizer (D : Set G))
    (hDcent : q ∉ OddOrder.BG.Ch3.S10.beta M → D ≤ Subgroup.centralizer (Q : Set G)) :
    q ∈ OddOrder.BG.Ch3.S10.beta M := by
  by_contra hq
  have hDQ := hDcent hq
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer] at hDQ
  exact hQ0 (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (by rwa [Subgroup.commutator_comm] at hDQ))

/-- **Theorem 15.2(f) — `M_F` non-cyclic, gated-endpoint skeleton** (mmd L4202): `M_F` is
non-cyclic because it contains the non-cyclic section `Q̄ = Q/Q₀` (the elementary abelian chief
factor of order `q^p`, `p ≥ 2`).  If `M_F` were cyclic, then so would be its subgroup `Q`
(`Subgroup.isCyclic_of_le`) and the quotient `Q/Q₀` (`isCyclic_of_surjective`), against `hQbar`.
Reduces `¬ IsCyclic M_F` to `Q ⊆ M_F` (Theorem 15.2(c)) and `¬ IsCyclic (Q/Q₀)` (from `|Q̄| = q^p`,
`p ≥ 2`). -/
theorem not_isCyclic_MF_of_inputs {M Q Q0 : Subgroup G} [(Q0.subgroupOf Q).Normal]
    (hQMF : Q ≤ MF M) (hQbar : ¬ IsCyclic (↥Q ⧸ Q0.subgroupOf Q)) :
    ¬ IsCyclic ↥(MF M) := by
  intro hcyc
  haveI := hcyc
  haveI : IsCyclic ↥Q := Subgroup.isCyclic_of_le hQMF
  exact hQbar (isCyclic_of_surjective (QuotientGroup.mk' (Q0.subgroupOf Q))
    (QuotientGroup.mk'_surjective _))

/-- A finite elementary-abelian `q`-group of order exceeding `q` is not cyclic (`§14`-independent,
reusable; generalises `not_isCyclic_of_card_prime_sq` to any order `> q`).  A cyclic group has
`Monoid.exponent = Nat.card`, while elementary-abelianness forces the exponent to divide `q`, so
`Nat.card ∣ q`. -/
theorem not_isCyclic_of_lt_card {q : ℕ} (hq : q.Prime) {Mod : Type*} [Group Mod] [Finite Mod]
    (h : OddOrder.GroupTheory.IsElementaryAbelian q Mod) (hlt : q < Nat.card Mod) :
    ¬ IsCyclic Mod := by
  intro hcyc
  have hExp_eq : Monoid.exponent Mod = Nat.card Mod := IsCyclic.exponent_eq_card
  have hExp_dvd : Monoid.exponent Mod ∣ q := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]; exact h.pow_eq_one
  rw [hExp_eq] at hExp_dvd
  exact (Nat.not_dvd_of_pos_of_lt hq.pos hlt) hExp_dvd

/-- **Theorem 15.2(f) conjunct `¬ IsCyclic M_F`, gated-endpoint skeleton** (mmd L4202): assembles
`not_isCyclic_MF_of_inputs` with the engine output `[Q : Q₀] = q^n` (`n = |K| ≥ 2`, since `|K|` is
the prime `p`).  The chief factor `Q̄ = Q/Q₀` (elementary abelian of order `q^n > q`) is non-cyclic
(`not_isCyclic_of_lt_card`), and `Q ⊆ M_F` (`hQMF`, Theorem 15.2(c)) lifts this to `M_F`. -/
theorem not_isCyclic_MF_of_chiefFactor_inputs [Finite G] {M Q Q0 : Subgroup G}
    [(Q0.subgroupOf Q).Normal] {q n : ℕ} (hq : q.Prime) (hn : 2 ≤ n)
    (hEA : OddOrder.GroupTheory.IsElementaryAbelian q (↥Q ⧸ Q0.subgroupOf Q))
    (hindex : (Q0.subgroupOf Q).index = q ^ n) (hQMF : Q ≤ MF M) :
    ¬ IsCyclic ↥(MF M) := by
  refine not_isCyclic_MF_of_inputs hQMF (not_isCyclic_of_lt_card hq hEA ?_)
  rw [← Subgroup.index_eq_card, hindex]
  calc q = q ^ 1 := (pow_one q).symm
    _ < q ^ n := pow_lt_pow_right₀ hq.one_lt (by omega)

/-- **Theorem 15.2(g) `F(M) ⊆ M_σ`** (mmd L4198), from the same `σ`-gap as the `(g)` equality:
`F(M) = Q ⊔ (C_G(Q) ⊓ M)` (`fittingInAmbient_eq_sup_centralizer_inf_of_le_Msigma`), with
`Q = O_q(M) ⊆ M_σ` (`opiCoreInG_singleton_le_Msigma_of_mem_sigma`, `q ∈ σ(M)`) and
`C_M(Q) ⊆ M_σ` (the forward input `hCle`).  So `F(M) ⊆ M_σ`. -/
theorem fittingInAmbient_le_Msigma_of_le_Msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : M ∈ maximalSubgroups G) (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hQ : Q = opiCoreInG ({q} : Set ℕ) M) (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M)
    [(Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal]
    [Group.IsNilpotent (↥(OddOrder.BG.Ch3.S10.Msigma M) ⧸
      Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))]
    (hCle : Subgroup.centralizer (Q : Set G) ⊓ M ≤ OddOrder.BG.Ch3.S10.Msigma M) :
    fittingInAmbient M ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  rw [fittingInAmbient_eq_sup_centralizer_inf_of_le_Msigma hG hM hMnormQ hQ hCle]
  refine sup_le ?_ hCle
  rw [hQ]
  exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ

open scoped commutatorElement in
/-- **Theorem 15.2 conjunct 3 — `M'' ⊆ F(M)`, gated-endpoint skeleton** (mmd L4198-4201): the
chain `M'' = M_σ' ⊆ Q D' ⊆ C_{M_σ}(Q̄) = F(M)`.

After identifying `M'' = M_σ'` (conjunct 2, `h2 : M_σ = M'`), the proof reduces `M_σ' ⊆ F(M)` to
three structural ingredients:
* `hsigmaprime : M_σ' ⊆ Q ⊔ ⁅D, D⁆` — the derived subgroup of the semidirect `M_σ = Q ⋊ D`
  (`Q ◁ M_σ`, complement `D`) lands in `Q · D'` (the `M_σ = QD` structure consequence);
* `hQab` / `hDcomm` — both `Q` and `D' = ⁅D, D⁆` *centralize the chief factor* `Q̄ = Q/Q₀`:
  `Q̄` is (elementary) abelian (`⁅Q, Q⁆ ⊆ Q₀`, `hQab`) and `D' ⊆ C_D(Q̄)` is the engine output
  `chiefFactor_card_and_commutator_of_inputs` (`∀ g ∈ ⁅D, D⁆, ∀ x ∈ Q, ⁅g, x⁆ ∈ Q₀`, mmd 15.2(g));
* `hsecFit : C_{M_σ}(Q̄) ⊆ F(M)` — the *section-centralizer* containment, the genuinely BG-specific
  forward input.  This is the mmd's "Proposition 1.5(d) yields `F(M) = Q C_M(Q) = C_{M_σ}(Q̄)`"
  (`D` nilpotent while `M_σ` is not), which bundles the `σ`-uniqueness gap `C_M(Q) ⊆ M_σ` (cf.
  `fittingInAmbient_eq_sup_centralizer_inf_of_le_Msigma`) with the Prop 1.5(d) section identity.
  Note `D'` only centralizes the *section* `Q̄`, not `Q` itself, so the full-centralizer helper
  `centralizer_inf_le_fittingInAmbient_of_le_Msigma` is too weak here; the section form is needed.

Both `Q` and `D'` therefore lie in `C_{M_σ}(Q̄)` (they centralize `Q̄` and sit inside `M_σ`), whence
in `F(M)` by `hsecFit`, so `M_σ' ⊆ Q ⊔ D' ⊆ F(M)`.  Once the step-4 core supplies `hsigmaprime`
(QD structure) and `hsecFit` (Prop 1.5(d) + `σ`-gap), conjunct 3 becomes unconditional. -/
theorem derivedDerived_le_fittingInAmbient_of_inputs [Finite G] {M Q Q0 D : Subgroup G}
    (h2 : OddOrder.BG.Ch3.S10.Msigma M = derivedInG M)
    (hsigmaprime : derivedInG (OddOrder.BG.Ch3.S10.Msigma M) ≤ Q ⊔ ⁅D, D⁆)
    (hQsig : Q ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hDsig : D ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Q0)
    (hDcomm : ∀ g ∈ ⁅D, D⁆, ∀ x ∈ Q, ⁅g, x⁆ ∈ Q0)
    (hsecFit : ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M,
      (∀ y ∈ Q, ⁅x, y⁆ ∈ Q0) → x ∈ fittingInAmbient M) :
    derivedInG (derivedInG M) ≤ fittingInAmbient M := by
  -- `M'' = M_σ'` (conjunct 2): rewrite the inner `derivedInG M` to `M_σ`.
  rw [← h2]
  -- `M_σ' ⊆ Q ⊔ D'`; show each of `Q`, `D'` lands in `F(M)` via the section-Fitting input.
  refine hsigmaprime.trans (sup_le ?_ ?_)
  · -- `Q ⊆ F(M)`: each `x ∈ Q` lies in `M_σ` and centralizes `Q̄` (`Q̄` abelian).
    intro x hx
    exact hsecFit x (hQsig hx) (fun y hy => hQab x hx y hy)
  · -- `D' ⊆ F(M)`: each `g ∈ ⁅D, D⁆` lies in `M_σ` and centralizes `Q̄` (engine output).
    have hDDsig : ⁅D, D⁆ ≤ OddOrder.BG.Ch3.S10.Msigma M := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hDsig ha) (hDsig hb)) (inv_mem (hDsig ha)))
        (inv_mem (hDsig hb))
    intro g hg
    exact hsecFit g (hDDsig hg) (fun x hx => hDcomm g hg x hx)

/-- **BG Corollary 15.5, "Lemma 1"**: `O_{σ(M)}(F(M)) = F(M_σ)` (`§14`-independent).
`≤`: `O_σ(F(M)) ≤ O_σ(M) = M_σ` (`opiCoreInG_fittingInG_le_opiCoreInG`); it is nilpotent (subgroup
of `F(M)`) and normal in `M` (characteristic in `F(M) ◁ M`), hence normal in `M_σ`, so a nilpotent
normal subgroup of `M_σ` lands in `F(M_σ)`.  `≥`: `F(M_σ)` is characteristic in `M_σ ◁ M` hence
normal in `M`, nilpotent, so `F(M_σ) ≤ F(M)` (`fittingInG_le_fittingInG_of_le_normalizer`); it is a
`σ`-group (`≤ M_σ`) and normal in `F(M)`, so `F(M_σ) ≤ O_σ(F(M))`. -/
theorem opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma [Finite G]
    {M : Subgroup G} :
    opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) (fittingInAmbient M) =
      fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) := by
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσ
  -- `M` normalizes both `M_σ` and `O_σ(F(M))`.
  have hM_norm_Mσ : M ≤ Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG σ M
  have hMσ_le_M : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  refine le_antisymm ?_ ?_
  · -- `O_σ(F(M)) ≤ F(M_σ)`.
    set N : Subgroup G := opiCoreInG σ (fittingInAmbient M) with hN
    -- `N ≤ M_σ`.
    have hN_Mσ : N ≤ OddOrder.BG.Ch3.S10.Msigma M := by
      have := OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_le_opiCoreInG σ M
      rwa [show opiCoreInG σ M = OddOrder.BG.Ch3.S10.Msigma M from rfl] at this
    -- `N ◁ M` (characteristic in `F(M)`), hence `N ◁ M_σ`.
    have hM_norm_N : M ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        ((OddOrder.GroupTheory.opiCoreInG_le σ (fittingInAmbient M)).trans
          (OddOrder.BG.Ch2.S08.fittingInG_le M))).mp
        (OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal σ M)
    have hNnorm_Mσ : (N.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN_Mσ).mpr (hMσ_le_M.trans hM_norm_N)
    -- `N` is nilpotent (subgroup of the nilpotent `F(M)`).
    haveI : Group.IsNilpotent ↥N := by
      haveI : Group.IsNilpotent ↥(fittingInAmbient M) := OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (OddOrder.GroupTheory.opiCoreInG_le σ (fittingInAmbient M)))
    -- Nilpotent normal subgroup of `M_σ` lands in `F(M_σ)`.
    haveI : Group.IsNilpotent ↥(N.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hN_Mσ).symm
    haveI := hNnorm_Mσ
    calc N = (N.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).map
              (OddOrder.BG.Ch3.S10.Msigma M).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hN_Mσ).symm
      _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥(OddOrder.BG.Ch3.S10.Msigma M)).map
              (OddOrder.BG.Ch3.S10.Msigma M).subtype :=
          Subgroup.map_mono OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
      _ = fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) := rfl
  · -- `F(M_σ) ≤ O_σ(F(M))`.
    -- `F(M_σ) ≤ F(M)` (`F(M_σ)` characteristic in `M_σ ◁ M`, nilpotent).
    have hFMσ_le_FM : fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ≤ fittingInAmbient M :=
      OddOrder.BG.Ch2.S08.fittingInG_le_fittingInG_of_le_normalizer hMσ_le_M hM_norm_Mσ
    -- `F(M_σ) ≤ M_σ`, a `σ`-group.
    have hFMσ_le_Mσ : fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ≤
        OddOrder.BG.Ch3.S10.Msigma M := OddOrder.BG.Ch2.S08.fittingInG_le _
    have hFMσ_pi : Subgroup.IsPiSubgroup σ (fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M)) :=
      fun r hr => OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hFMσ_le_Mσ) Nat.card_pos.ne' hr)
    -- `F(M_σ) ◁ F(M)` (since `M` normalizes `F(M_σ)` and `F(M) ≤ M`).
    have hM_norm_FMσ : M ≤ Subgroup.normalizer
        ((fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) : Subgroup G) : Set G) := fun x hx =>
      OddOrder.BG.Ch2.S08.mem_normalizer_fittingInG_of_mem_normalizer (hM_norm_Mσ hx)
    have hFMσ_norm_FM : ((fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M)).subgroupOf
        (fittingInAmbient M)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFMσ_le_FM).mpr
        ((OddOrder.BG.Ch2.S08.fittingInG_le M).trans hM_norm_FMσ)
    exact OddOrder.GroupTheory.le_opiCoreInG_of_normal_of_isPiSubgroup hFMσ_le_FM
      hFMσ_norm_FM hFMσ_pi

/-- Lattice absorption used in BG Corollary 15.5 (Case I): if `C = A ⊔ X` with `A ≤ B`, then
`C ⊔ B = X ⊔ B`.  Pure lattice fact (kept generic to avoid `whnf` on the underlying `Subgroup`
`set`-locals in the main proof). -/
theorem sup_eq_sup_of_eq_sup_of_le {α : Type*} [Lattice α] {C A X B : α}
    (hC : C = A ⊔ X) (hA : A ≤ B) : C ⊔ B = X ⊔ B := by
  subst hC
  rw [sup_right_comm, sup_eq_right.mpr hA, sup_comm]

/-- **Nilpotent normal subgroup lands in the ambient Fitting subgroup** (`§14`-independent,
reusable): if `N ≤ M`, `N.subgroupOf M ⊴ M`, and `N` is nilpotent, then `N ≤ F(M)`
(`fittingInAmbient M`).  The relative `N.subgroupOf M` is a nilpotent normal subgroup of `↥M`,
so it lies in `fitting ↥M` (`nilpotent_normal_le_fitting`); mapping back gives the claim. -/
theorem le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent [Finite G] {M N : Subgroup G}
    (hNM : N ≤ M) (hNnorm : (N.subgroupOf M).Normal) [Group.IsNilpotent ↥N] :
    N ≤ fittingInAmbient M := by
  haveI := hNnorm
  haveI : Group.IsNilpotent ↥(N.subgroupOf M) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNM).symm
  calc N = (N.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hNM).symm
    _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype :=
        Subgroup.map_mono OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    _ = fittingInAmbient M := rfl

/-- **BG Theorem 15.2** (mmd L4112): if `M_F` is strictly smaller than `M_sigma`,
then `M` is type `P1` and has the normal `q`-subgroup / minimal chief factor
structure described in the text. -/
theorem mf_ne_msigma_typeP1_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hne : MF M ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    S14.IsTypeP1 M ∧
      ∃ Q Q0 D : Subgroup G, ∃ p q : ℕ,
        p.Prime ∧ q.Prime ∧ Nat.card ↥K = p ∧ Nat.card ↥Kstar = q ∧
        q ∈ S14.piSet (MF M) ∧ q ∈ OddOrder.BG.Ch3.S10.beta M ∧
        Kstar ≤ MF M ∧
        Q ≤ MF M ∧ M ≤ Subgroup.normalizer (Q : Set G) ∧
        Subgroup.IsComplement' (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))
          (D.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) ∧
        Group.IsNilpotent ↥D ∧
        Q0 = Q ⊓ Subgroup.centralizer (D : Set G) ∧
        M ≤ Subgroup.normalizer (Q0 : Set G) ∧
        -- mmd 15.2(f): the chief factor `Q̄ = Q/Q0` is elementary abelian of order `q^p`
        -- (faithfulness fix, Lane G 2026-06-16: the previous scaffold wrote
        -- `Nat.card ↥(Q.subgroupOf (Q ⊔ Q0))`, which is `|Q|` since `Q0 = Q ⊓ C(D) ⊆ Q` forces
        -- `Q ⊔ Q0 = Q`; the intended `|Q̄| = |Q : Q0|` is `(Q0.subgroupOf Q).index`).
        (Q0.subgroupOf Q).index = q ^ p ∧
        OddOrder.BG.Ch3.S10.Msigma M = derivedInG M ∧
        derivedInG (derivedInG M) ≤ fittingInAmbient M ∧
        -- mmd 15.2(g) "F(M) ⊂ M_σ": the Fitting subgroup is contained in the σ-core.
        fittingInAmbient M ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
        -- mmd 15.2(g) "F(M) = Q C_M(Q)": the Fitting subgroup is the product of the normal
        -- `q`-subgroup `Q` and its `M`-centralizer (`Q` self-centralizing up to `C_M(Q)`).
        fittingInAmbient M = Q ⊔ (Subgroup.centralizer (Q : Set G) ⊓ M) ∧
        -- mmd 15.2(f): `M_F ⊇ Q̄`, an elementary abelian section of order `q^p` (rank `p ≥ 3`),
        -- so `M_F` is non-cyclic.  Breaks the 15.5↔15.6 circularity (Corollary 15.6's proof needs
        -- this without citing Corollary 15.5).
        ¬ IsCyclic ↥(MF M) := by
  classical
  -- **Setup.**  `p = |K|`, `q = |K*|`; `M` is type `P₁`, `q` prime, `M_σ = M'`.
  set q : ℕ := Nat.card ↥Kstar with hqdef
  have hP1 : S14.IsTypeP1 M := isTypeP1_of_mf_ne_msigma hG hM hne
  have hP : S14.IsTypeP M := hP1.1
  have hq_prime : q.Prime := kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar
  haveI : Fact q.Prime := ⟨hq_prime⟩
  have hMσderived : OddOrder.BG.Ch3.S10.Msigma M = derivedInG M :=
    typeP1_msigma_eq_derivedInG hG hM hP1 hKM hK hKstar
  obtain ⟨hcomplDer, _, _⟩ := S14.typeP_duality hG hM hP hKM hK hKstar
  have hcomplMσ : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      (K.subgroupOf M) := by rw [hMσderived]; exact hcomplDer
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hMσnotnil : ¬ Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hnil =>
    hne ((maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr hnil)
  have hKstarMσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := by rw [hKstar]; exact inf_le_left
  have hqMσ : q ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
    rw [hqdef]; exact Subgroup.card_dvd_of_le hKstarMσ
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
      (Nat.mem_primeFactors.mpr ⟨hq_prime, hqMσ, Nat.card_pos.ne'⟩)
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) M with hQdef
  have hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    rw [hQdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]; exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M
  have hQM : Q ≤ M := hQMσ.trans hMσM
  have hcop_sub : Nat.Coprime (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M))
      (Nat.card ↥(K.subgroupOf M)) := by
    have h := coprime_card_derived_kappaHall_of_isComplement' hK hcomplDer
    rwa [hMσderived]
  have hcond2 := actsPrimeManner_subgroupOf_of_typeP hG hM hP hKM hK hKstar
  have hqG : (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M
      ⊓ Subgroup.centralizer (K : Set G))).Prime := by rw [← hKstar]; exact hq_prime
  have hKstarQ : Kstar ≤ Q := by
    have h := kstar_le_opiCore_of_inputs hG hM hKM hcomplMσ hcop_sub.symm hcond2 hne hqG
    rw [← hKstar, ← hqdef, ← hQdef] at h; exact h
  have hcopKMσ : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) := by
    have e1 : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
    have e2 : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
        = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv
    rw [e1, e2] at hcop_sub; exact hcop_sub.symm
  have hKMσdisj : Disjoint K (OddOrder.BG.Ch3.S10.Msigma M) := by
    rw [disjoint_iff]
    exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcopKMσ
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  have hKne : K ≠ ⊥ := by
    intro hK0
    apply hMσnotnil
    have hKstareq : Kstar = OddOrder.BG.Ch3.S10.Msigma M := by
      rw [hKstar, hK0]
      have hc : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
        rw [Subgroup.coe_bot]; ext g; simp [Subgroup.mem_centralizer_iff]
      rw [hc, inf_top_eq]
    have hcardMσ : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) = q ^ 1 := by
      rw [pow_one, hqdef, hKstareq]
    exact (IsPGroup.of_card hcardMσ).isNilpotent
  have hQpg : IsPGroup q ↥Q := by rw [hQdef]; exact isPGroup_opiCoreInG_singleton M
  have hQneMσ : Q ≠ OddOrder.BG.Ch3.S10.Msigma M := by
    intro hQeq; exact hMσnotnil (hQeq ▸ hQpg.isNilpotent)
  -- **The `K`-invariant complement `D` of `Q` in `M_σ`.**
  obtain ⟨D, hDMσ, hKnormD, hQDdisj, hcomplD, hDnil, hDne, hDq'⟩ :=
    exists_kInvariant_qComplement hG hM hP hKM hK hKstar hQdef hQMσ hMnormQ hKstarQ hQneMσ hKne
      hKMσdisj hcopKMσ
  -- **The chief factor `Q₀ = C_Q(D) ⊴ M` and the Theorem 3.10 engine outputs.**
  obtain ⟨hMNQ0, hKstarNotQ0, hQ0ltQ, hmin⟩ :=
    chiefFactor_Q0_normal_minimal_of_inputs hG hM hP1 hKM hK hKstar hQdef hQMσ hMnormQ hKstarQ
      hQneMσ hKne hKMσdisj hcopKMσ hMσnotnil hDq' hDMσ hKnormD hQDdisj hcomplD hDnil hDne
  set Q0 : Subgroup G := Q ⊓ Subgroup.centralizer (D : Set G) with hQ0def
  have hQ0Q : Q0 ≤ Q := hQ0ltQ.le
  haveI hQ0nQ : (Q0.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0Q).mpr (hQM.trans hMNQ0)
  obtain ⟨hKprime, hindex, hDcomm, hEA⟩ :=
    chiefFactor_engine_of_inputs hG hM hP1 hKM hK hKstar hQdef hQMσ hMnormQ hKstarQ hKne hKMσdisj
      hcopKMσ hDq' hDMσ hKnormD hQDdisj hDne hQ0def hMNQ0 hKstarNotQ0 hQ0ltQ hmin
  -- **Fitting subgroup (Theorem 15.2(g)).**
  haveI hQnMσ : (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQMσ).mpr (hMσM.trans hMnormQ)
  haveI hNilMσQ : Group.IsNilpotent (↥(OddOrder.BG.Ch3.S10.Msigma M) ⧸
      Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) :=
    msigma_quotient_isNilpotent_of_inputs hG hM hP hKM hK hKstar hQMσ hMnormQ hKstarQ hQneMσ hKne
      hKMσdisj hcopKMσ
  have hprime := actsPrimeManner_of_typeP hG hM hP hKM hK hKstar
  have hQgtq : q < Nat.card ↥Q := by
    have h1 : (Q0.subgroupOf Q).index ≤ Nat.card ↥Q :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
    have h2 : q < q ^ Nat.card ↥K := by
      calc q = q ^ 1 := (pow_one q).symm
        _ < q ^ Nat.card ↥K := Nat.pow_lt_pow_right hq_prime.one_lt hKprime.two_le
    rw [hindex] at h1; exact lt_of_lt_of_le h2 h1
  have hKstarneQ : Kstar ≠ Q := by
    intro h
    have hqeq : q = Nat.card ↥Q := by rw [hqdef, h]
    rw [hqeq] at hQgtq; exact lt_irrefl _ hQgtq
  have hCle : Subgroup.centralizer (Q : Set G) ⊓ M ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    centralizer_le_Msigma_of_primeManner hG hM hP1 hKM hK hprime hQMσ hMnormQ hKstarQ hKstarneQ
  have cC17 : fittingInAmbient M ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    fittingInAmbient_le_Msigma_of_le_Msigma hG hM hMnormQ hQdef hqσ hCle
  have cC18 : fittingInAmbient M = Q ⊔ (Subgroup.centralizer (Q : Set G) ⊓ M) :=
    fittingInAmbient_eq_sup_centralizer_inf_of_le_Msigma hG hM hMnormQ hQdef hCle
  have hcopDQ : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    rw [hn]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simpa using Nat.coprime_one_right _
    · rw [Nat.coprime_pow_right_iff h0]
      exact ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr (fun hd =>
        hDq' (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩))).symm
  have hQab : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Q0 := by
    intro x hxQ y hyQ
    have hcomm := hEA.comm (QuotientGroup.mk (⟨x, hxQ⟩ : ↥Q))
      (QuotientGroup.mk (⟨y, hyQ⟩ : ↥Q))
    have h1 : QuotientGroup.mk (⁅(⟨x, hxQ⟩ : ↥Q), (⟨y, hyQ⟩ : ↥Q)⁆) =
        (1 : ↥Q ⧸ Q0.subgroupOf Q) := by
      rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    have h2 : ((⁅(⟨x, hxQ⟩ : ↥Q), (⟨y, hyQ⟩ : ↥Q)⁆ : ↥Q) : G) = ⁅x, y⁆ := by
      push_cast [commutatorElement_def]; rfl
    rwa [h2] at h1
  -- `M_σ' ⊆ Q ⊔ ⁅D, D⁆`: the derived subgroup of the semidirect `M_σ = Q ⋊ D` (`Q` normal,
  -- `D` complement).  `derivedInG_le_sup_of_normal` (S13) is exactly this normal-target argument:
  -- modulo the normal `Q` the quotient `M_σ/Q` is the image of `D`, so its derived subgroup is the
  -- image of `D' = ⁅D, D⁆`, and pulling back gives `M_σ' ⊆ Q ⊔ ⁅D, D⁆`.  (The `M_σ = QD`
  -- decomposition `Q ⊔ D = M_σ` is read off the complement `hcomplD.sup_eq_top`.)
  have hsigmaprime : derivedInG (OddOrder.BG.Ch3.S10.Msigma M) ≤ Q ⊔ ⁅D, D⁆ := by
    have hsup : Q ⊔ D = OddOrder.BG.Ch3.S10.Msigma M := by
      have h := congrArg (Subgroup.map (OddOrder.BG.Ch3.S10.Msigma M).subtype) hcomplD.sup_eq_top
      rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hQMσ, inf_eq_left.mpr hDMσ, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h
    have hle := OddOrder.BG.Ch3.S13.derivedInG_le_sup_of_normal hQMσ hDMσ hsup hQnMσ
    rwa [show derivedInG D = ⁅D, D⁆ from Subgroup.map_subtype_commutator D] at hle
  have hsecFit : ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M, (∀ y ∈ Q, ⁅x, y⁆ ∈ Q0) →
      x ∈ fittingInAmbient M :=
    centralizer_msigma_quotient_le_fittingInAmbient hG hM hQMσ hDMσ hQ0def hQ0Q hcomplD hMnormQ
      hMNQ0 hQpg hDnil hcopDQ hQab
  have cC16 : derivedInG (derivedInG M) ≤ fittingInAmbient M :=
    derivedDerived_le_fittingInAmbient_of_inputs hMσderived hsigmaprime hQMσ hDMσ hQab hDcomm hsecFit
  -- **`q ∈ β(M)` (conjunct 6).**
  have hQne : Q ≠ ⊥ := by
    intro h0
    have hKstar0 : Kstar = ⊥ := le_bot_iff.mp (h0 ▸ hKstarQ)
    have : q = 1 := by rw [hqdef, hKstar0, Subgroup.card_bot]
    exact hq_prime.ne_one this
  have hQ0notC : ¬ Q ≤ Subgroup.centralizer (D : Set G) := by
    intro hle
    exact (ne_of_lt hQ0ltQ) (le_antisymm hQ0Q (le_inf le_rfl hle))
  have hqπ : q ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq_prime, hqMσ.trans (Subgroup.card_dvd_of_le hMσM), Nat.card_pos.ne'⟩
  have hq_odd : Odd q := hG.odd.of_dvd_nat ((Nat.mem_primeFactors.mp hqπ).2.1.trans
    (Subgroup.card_subgroup_dvd_card M))
  have hcopKD : Nat.Coprime (Nat.card ↥K) (Nat.card ↥D) :=
    hcopKMσ.coprime_dvd_right (Subgroup.card_dvd_of_le hDMσ)
  have hDKN : D ⊔ K ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le (hDMσ.trans (hMσM.trans hMnormQ)) (hKM.trans hMnormQ)
  have hqD : ¬ q ∣ Nat.card ↥D := fun hd =>
    hDq' (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩)
  haveI hKsolv : IsSolvable ↥K :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hKM)
  have hqK : ¬ q ∣ Nat.card ↥K := fun hd =>
    hq_prime.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcopKMσ hd hqMσ)
  -- Sylow witness `P : Sylow q ↥M` with `Q = P.map M.subtype`.
  have hidx_M : ¬ q ∣ (Q.subgroupOf M).index := by
    have hMcard : Nat.card ↥M = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) * Nat.card ↥K := by
      have h := hcomplMσ.card_mul
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at h
      exact h.symm
    have hMσcard : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) = Nat.card ↥Q * Nat.card ↥D := by
      have h := hcomplD.card_mul
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQMσ).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDMσ).toEquiv] at h
      exact h.symm
    have hidxeq : (Q.subgroupOf M).index = Nat.card ↥D * Nat.card ↥K := by
      have hmul := Subgroup.card_mul_index (Q.subgroupOf M)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv, hMcard, hMσcard] at hmul
      refine Nat.eq_of_mul_eq_mul_left Nat.card_pos (?_ : Nat.card ↥Q * _ = Nat.card ↥Q * _)
      rw [hmul]; ring
    rw [hidxeq]
    exact fun hdvd => ((Nat.Prime.dvd_mul hq_prime).mp hdvd).elim hqD hqK
  obtain ⟨P, hQP⟩ := exists_sylow_eq_opiCore hQdef hQM hMnormQ hQpg hidx_M
  -- the `G`-level fixed-point-free condition, lifted from the `↥(D ⊔ K)`-Frobenius group.
  have hfrob := isFrobeniusGroup_DK_of_primeManner (M := M) hprime hDMσ hKstarQ hQDdisj.symm hKnormD
    (hKMσdisj.symm.mono_left hDMσ) hDne hKne
  have hFrobFPF : ∀ a ∈ K, a ≠ 1 → ∀ n ∈ D, n ≠ 1 → a * n * a⁻¹ ≠ n := by
    intro a haK ha1 n hnD hn1 heq
    have haDK : a ∈ D ⊔ K := (le_sup_right : K ≤ D ⊔ K) haK
    have hnDK : n ∈ D ⊔ K := (le_sup_left : D ≤ D ⊔ K) hnD
    refine hfrob.conj_frobenius ⟨a, haDK⟩ (Subgroup.mem_subgroupOf.mpr haK)
      (fun h => ha1 (congrArg Subtype.val h)) ⟨n, hnDK⟩ (Subgroup.mem_subgroupOf.mpr hnD)
      (fun h => hn1 (congrArg Subtype.val h)) (Subtype.ext ?_)
    show (a : G) * (n : G) * (a : G)⁻¹ = (n : G)
    exact heq
  have cC6 : q ∈ OddOrder.BG.Ch3.S10.beta M :=
    mem_beta_of_inputs hQ0notC (D_centralizes_Q_of_not_mem_beta hG hM hq_odd hQpg hQne hqπ P hQP
      hKne hFrobFPF hKnormD hcopKD hKsolv hDKN hqD)
  -- **`Q, K* ⊆ M_F` and `q ∈ π(M_F)` (conjuncts 5,7,8).**
  have hQhall : OddOrder.Isaacs.Ch03.IsHallSubgroup (Nat.card ↥Q).primeFactors
      (Q.subgroupOf M) := by
    have hpf : ((Nat.card ↥Q).primeFactors : Set ℕ) = ({q} : Set ℕ) := by
      obtain ⟨n, hn⟩ := hQpg.exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl; rw [pow_zero] at hn; rw [hn] at hQgtq
        have := hq_prime.two_le; omega
      rw [hn, Nat.primeFactors_prime_pow hn0 hq_prime, Finset.coe_singleton]
    rw [hpf]
    exact isHallSubgroup_subgroupOf_of_pgroup_of_not_dvd_index hQM hQpg hidx_M
  haveI hQnilM : Group.IsNilpotent ↥(Q.subgroupOf M) :=
    (hQpg.comap_subtype).isNilpotent
  have cC8 : Q ≤ MF M := le_maxNilpotentNormalHall hQM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMnormQ) hQnilM hQhall
  have cC7 : Kstar ≤ MF M := hKstarQ.trans cC8
  have cC5 : q ∈ S14.piSet (MF M) := by
    rw [S14.piSet, Set.mem_setOf_eq]
    refine Nat.mem_primeFactors.mpr ⟨hq_prime, ?_, Nat.card_pos.ne'⟩
    rw [hqdef]; exact Subgroup.card_dvd_of_le cC7
  -- **`¬ IsCyclic M_F` (conjunct 19).**
  have cC19 : ¬ IsCyclic ↥(MF M) :=
    not_isCyclic_MF_of_chiefFactor_inputs hq_prime hKprime.two_le hEA hindex cC8
  -- **Assemble.**
  exact ⟨hP1, Q, Q0, D, Nat.card ↥K, q, hKprime, hq_prime, rfl, hqdef.symm, cC5, cC6, cC7, cC8,
    hMnormQ, hcomplD, hDnil, hQ0def, hMNQ0, hindex, hMσderived, cC16, cC17, cC18, cC19⟩

/-- **BG Corollary 15.5** (mmd L4225): the decomposition `F(M) = F(M_σ) × Y` with
`Y = O_{σ(M)'}(F(M))` a cyclic `τ₂(M)`-subgroup, together with `F(M) = C_M(M_F)·M_F`,
`M'' ⊆ F(M)`, `M_F ⊆ M'`, and `K ≠ 1 → F(M) ⊆ M'`.  Direct products are encoded by the
commuting/trivial-intersection package.

Faithfulness fix (Lane G): the previous scaffold parametrized an arbitrary `H ≤ M_F` (mmd
fixes `H = M_F`) and used `M_F(M_σ)` where the textbook has the Fitting subgroup `F(M_σ)`
(`fittingInAmbient (Msigma M)`); the dropped conjuncts (a)/(b)/(d) are restored.  The `M'/M_F`
nilpotent clause of (c) is still deferred (quotient API).

`M_F` cyclic ⟹ `F(M)` cyclic exposure (Lane G 2026-06-15): the final conjunct records the
derived consequence that Corollary 15.6's proof cites ("if `M_F` is cyclic, then `F(M)` is
cyclic by Corollary 15.5").  It follows from (a)/(b): when `M_σ` is nilpotent, `F(M_σ) = M_σ =
M_F` (`fittingInAmbient_eq_self_of_isNilpotent`), so `F(M) = M_F × Y` is a product of coprime
cyclic factors (`isCyclic_prod_iff`); otherwise `M_F` is non-cyclic (Theorem 15.2) and the
implication is vacuous.  This supplies the `hFcyc` hypothesis of `typeP_kstar_in_mf_of_inputs`. -/
theorem fitting_decomposition [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∃ Y : Subgroup G,
      -- (a) `Y = O_{σ(M)'}(F(M))` is a cyclic `τ₂(M)`-subgroup of `F(M)`.
      IsCyclic ↥Y ∧ (↑(Nat.card ↥Y).primeFactors ⊆ tau2 M) ∧ Y ≤ fittingInAmbient M ∧
      -- (b) `M'' ⊆ F(M) = C_M(M_F)·M_F = F(M_σ) × Y`.
      derivedInG (derivedInG M) ≤ fittingInAmbient M ∧
      fittingInAmbient M = (Subgroup.centralizer (MF M : Set G) ⊓ M) ⊔ MF M ∧
      fittingInAmbient M = fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ⊔ Y ∧
      fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ⊓ Y = ⊥ ∧
      ⁅fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M), Y⁆ = ⊥ ∧
      -- (c) `M_F ⊆ M'` (the `M'/M_F` nilpotent part is deferred — quotient API).
      MF M ≤ derivedInG M ∧
      -- (d) if `K ≠ 1` (i.e. `M` is not of type `F`), then `F(M) ⊆ M'`.
      (¬ S14.IsTypeF M → fittingInAmbient M ≤ derivedInG M) ∧
      -- The derived consequence Corollary 15.6's proof cites ("`F(M)` is cyclic by Cor 15.5"):
      -- via the `F(M) = F(M_σ) × Y` decomposition (both factors cyclic, coprime orders when
      -- `M_σ` is nilpotent so `F(M_σ) = M_σ = M_F`; otherwise `M_F` is non-cyclic, vacuous).
      (IsCyclic ↥(MF M) → IsCyclic ↥(fittingInAmbient M)) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσ
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  set F := fittingInAmbient M with hF
  set FMσ := fittingInAmbient Mσ with hFMσ
  -- `Y := O_{σ'}(F(M))`, the `σ'`-Hall part of the Fitting subgroup.
  set Y : Subgroup G := opiCoreInG σᶜ F with hY
  haveI hFnil : Group.IsNilpotent ↥F := OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M
  -- ## Case-independent facts.
  -- Lemma 1: `O_σ(F(M)) = F(M_σ)`.
  have hL1 : opiCoreInG σ F = FMσ :=
    opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma
  -- Nilpotent Hall splitting `O_σ(F) ⊔ Y = F`.
  have hsplit : opiCoreInG σ F ⊔ Y = F := opiCoreInG_sup_compl_eq_of_isNilpotent σ
  -- Conjunct 3: `Y ≤ F`.
  have h3 : Y ≤ F := OddOrder.GroupTheory.opiCoreInG_le σᶜ F
  -- Conjunct 6: `F = F(M_σ) ⊔ Y`.
  have h6 : F = FMσ ⊔ Y := by rw [← hL1, hsplit]
  -- Conjunct 7: `F(M_σ) ⊓ Y = ⊥`.
  have h7 : FMσ ⊓ Y = ⊥ := by
    rw [← hL1, hY]
    exact OddOrder.GroupTheory.inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σ F)
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σᶜ F)
  -- Conjunct 8: `⁅F(M_σ), Y⁆ = ⊥`.
  have h8 : ⁅FMσ, Y⁆ = ⊥ := by
    rw [← hL1, hY]; exact OddOrder.BG.Ch2.S08.opiCoreInG_commutator_compl_eq_bot σ F
  -- Conjunct 9: `M_F ≤ M'`.
  have h9 : MF M ≤ derivedInG M := maxNilpotentNormalHall_le_derived hG hM
  -- `Y` is a `σ'`-group, `M_σ` is a `σ`-group, so they are coprime.
  have hYpi : Subgroup.IsPiSubgroup σᶜ Y := OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σᶜ F
  -- `M ≤ N_G(M_σ)` and `M ≤ N_G(Y)` (the latter since `Y` is characteristic in `F(M) ◁ M`).
  have hM_norm_Mσ : M ≤ Subgroup.normalizer (Mσ : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG σ M
  have hMσ_le_M : Mσ ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hM_norm_Y : M ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (h3.trans (OddOrder.BG.Ch2.S08.fittingInG_le M))).mp
      (by rw [hY]; exact OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal σᶜ M)
  -- ## Lemma 15.1 inputs (a `κ`-Hall `K` and a `(κ∪σ)ᶜ`-Hall `U`), via Hall's theorem in `↥M`.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hK
  have hKof : K.subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hKHall : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKof]; exact hK'
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M) ((S14.kappa M ∪ σ)ᶜ)
  set U : Subgroup G := U'.map M.subtype with hU
  have hUof : U.subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hUHall : Ch03.IsHallSubgroup ((S14.kappa M ∪ σ)ᶜ) (U.subgroupOf M) := by
    rw [hUof]; exact hU'
  -- Lemma 15.1 conclusion (with `Kstar := M_σ ⊓ C_M(K)`).
  obtain ⟨_, _, _, hMddσ, hKguard, _, _, _⟩ :=
    typeP_auxiliary_structure hG hM (hK ▸ Subgroup.map_subtype_le K')
      (hU ▸ Subgroup.map_subtype_le U') hKHall rfl hUHall
  -- Conjunct 4 / 10 helper: `M'' ≤ M_σ` (Lemma 15.1, unconditional).
  have hMdd_Mσ : derivedInG (derivedInG M) ≤ Mσ := hMddσ
  -- ## Case split on whether `M_σ` is nilpotent (`M_F = M_σ`).
  by_cases hcase : MF M = Mσ
  · -- ### Case I: `M_σ` nilpotent, `M_F = M_σ`, `F(M_σ) = M_σ`.
    haveI hMσnil : Group.IsNilpotent ↥Mσ :=
      (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mp hcase
    have hFMσ_eq : FMσ = Mσ := fittingInAmbient_eq_self_of_isNilpotent
    -- `M_σ ≤ F(M)` (nilpotent normal subgroup of `M`).
    have hMσ_le_F : Mσ ≤ F := by rw [← hFMσ_eq]; rw [h6]; exact le_sup_left
    -- `[M_σ, Y] = ⊥`, so `Y` centralizes `M_σ`; together with `Y ≤ M`, `Y ≤ C_G(M_σ) ⊓ M`.
    have hMσY : ⁅Mσ, Y⁆ = ⊥ := by rw [← hFMσ_eq]; exact h8
    have hY_cent : Y ≤ Subgroup.centralizer (Mσ : Set G) := by
      rw [Subgroup.commutator_comm] at hMσY
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMσY
    have hY_le_M : Y ≤ M := h3.trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
    -- Corollary 15.3(a) at `H := M_σ`: `C_M(M_σ) = (C_G(M_σ) ⊓ M_σ) ⊔ X`, `X` cyclic `τ₂`.
    -- Sorry-free via `mf_centralizer_msigma_decomp` (Prop 14.2(b1)(e) + Schur–Zassenhaus +
    -- Lemma 15.1(c)); this de-axiomatises the A(8) `FittingIsTI` chain (issue 8016).
    obtain ⟨X, hXcyc, hXτ₂, hCeq⟩ := mf_centralizer_msigma_decomp hG hM
    -- `C := C_G(M_σ) ⊓ M`, `A := C_G(M_σ) ⊓ M_σ`.
    set C : Subgroup G := Subgroup.centralizer (Mσ : Set G) ⊓ M with hCdef
    set A : Subgroup G := Subgroup.centralizer (Mσ : Set G) ⊓ Mσ with hAdef
    have hY_C : Y ≤ C := le_inf hY_cent hY_le_M
    have hA_C : A ≤ C := inf_le_inf_left _ hMσ_le_M
    have hX_C : X ≤ C := le_sup_right.trans hCeq.ge
    -- `A ⊴ C` (so we can form the cyclic quotient `C/A`).
    have hC_norm_A : C ≤ Subgroup.normalizer (A : Set G) := by
      have h1 : C ≤ Subgroup.normalizer (Subgroup.centralizer (Mσ : Set G)) :=
        inf_le_left.trans Subgroup.le_normalizer
      have h2 : C ≤ Subgroup.normalizer (Mσ : Set G) := inf_le_right.trans hM_norm_Mσ
      exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
    haveI hA_normal : (A.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer_inf).mpr
        (by rw [inf_eq_left.mpr hA_C]; exact hC_norm_A)
    -- `A ≤ M_σ` is a `σ`-group; `Y` is a `σ'`-group; hence `|A|` and `|Y|` are coprime.
    have hA_pi : ∀ r ∈ (Nat.card ↥A).primeFactors, r ∈ σ := fun r hr =>
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le (inf_le_right : A ≤ Mσ))
          Nat.card_pos.ne' hr)
    have hY_pi' : ∀ r ∈ (Nat.card ↥Y).primeFactors, r ∉ σ := fun r hr =>
      (Set.mem_compl_iff _ _).mp (hYpi r hr)
    -- `Y ⊓ A = ⊥` (coprime orders).
    have hY_inf_A : Y ⊓ A = ⊥ :=
      Subgroup.inf_eq_bot_of_coprime
        ((Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl Nat.card_pos.ne' Nat.card_pos.ne'
          hA_pi hY_pi').symm)
    -- Embed `Y` into the cyclic quotient `C/A` (`C/A` is a quotient image of the cyclic `X`).
    have haxtop : A.subgroupOf C ⊔ X.subgroupOf C = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hA_C hX_C, show A ⊔ X = C from hCeq.symm,
        Subgroup.subgroupOf_self]
    have hYc_inf_a : Y.subgroupOf C ⊓ A.subgroupOf C = ⊥ := by
      rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, hY_inf_A,
        MonoidHom.comap_bot]
      exact C.ker_subtype
    have hinj : Function.Injective
        ((QuotientGroup.mk' (A.subgroupOf C)).comp (Y.subgroupOf C).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hy
      have hmem : (Y.subgroupOf C).subtype y ∈ Y.subgroupOf C ⊓ A.subgroupOf C := ⟨y.2, hy⟩
      rw [hYc_inf_a, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]; exact Subtype.ext hmem
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
    -- Conjunct 1: `Y` is cyclic (`Y ≅ Y.subgroupOf C ↪ C/A` cyclic).
    haveI hYcyc' : IsCyclic ↥(Y.subgroupOf C) :=
      isCyclic_of_surjective _ (MonoidHom.ofInjective hinj).symm.surjective
    have hYcyc : IsCyclic ↥Y :=
      isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hY_C).surjective
    -- Conjunct 2: `π(Y) ⊆ τ₂` (`q ∣ |Y| ∣ [C:A] ∣ |X|`, `π(X) ⊆ τ₂`).
    have hYτ₂ : (↑(Nat.card ↥Y).primeFactors : Set ℕ) ⊆ tau2 M := by
      intro q hq
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hcardYc : Nat.card ↥(Y.subgroupOf C) = Nat.card ↥Y :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY_C).toEquiv
      have hdvd1 : Nat.card ↥Y ∣ (A.subgroupOf C).index := by
        rw [← hcardYc, Subgroup.index_eq_card]
        exact Subgroup.card_dvd_of_injective _ hinj
      have hdvd2 : (A.subgroupOf C).index ∣ Nat.card ↥X := by
        have hidx : (A.subgroupOf C).index = (A.subgroupOf C).relIndex (X.subgroupOf C) := by
          rw [← Subgroup.relIndex_top_right, ← haxtop, Subgroup.relIndex_sup_left]
        have hcardx : Nat.card ↥(X.subgroupOf C) = Nat.card ↥X :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_C).toEquiv
        rw [hidx, ← hcardx]
        exact Subgroup.relIndex_dvd_card (A.subgroupOf C) (X.subgroupOf C)
      have hqX : q ∈ (Nat.card ↥X).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqp,
          ((Nat.dvd_of_mem_primeFactors hq).trans hdvd1).trans hdvd2, Nat.card_pos.ne'⟩
      exact hXτ₂ hqX
    -- Conjunct 4: `M'' ⊆ F(M)` (`M'' ≤ M_σ ≤ F(M)`, `M_σ` nilpotent).
    have h4 : derivedInG (derivedInG M) ≤ F := hMdd_Mσ.trans hMσ_le_F
    -- Conjunct 5: `F(M) = (C_G(M_F) ⊓ M) ⊔ M_F = (C_G(M_σ) ⊓ M) ⊔ M_σ`.
    have h5 : F = (Subgroup.centralizer (MF M : Set G) ⊓ M) ⊔ MF M := by
      rw [hcase]
      -- `M ≤ N_G(C_G(M_σ))`: normalizing `M_σ` normalizes its centralizer.
      have hM_norm_CMσ : M ≤ Subgroup.normalizer (Subgroup.centralizer (Mσ : Set G)) :=
        hM_norm_Mσ.trans (normalizer_le_normalizer_centralizer Mσ)
      -- `C := C_G(M_σ) ⊓ M ⊴ M`.
      have hC_norm : M ≤ Subgroup.normalizer (C : Set G) :=
        (le_inf hM_norm_CMσ Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
      haveI hC_normal : (C.subgroupOf M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hC_norm
      refine le_antisymm ?_ ?_
      · -- `F ⊆ (C_G(M_σ) ⊓ M) ⊔ M_σ`: `F = M_σ ⊔ Y`, `M_σ ≤ M_σ`, `Y ≤ C`.
        rw [h6, hFMσ_eq]
        exact sup_le (le_sup_right) (hY_C.trans le_sup_left)
      · -- `(C_G(M_σ) ⊓ M) ⊔ M_σ ⊆ F`: `M_σ ≤ F`, and `C ⊔ M_σ` is nilpotent normal (`= X ⊔ M_σ`).
        refine sup_le ?_ hMσ_le_F
        -- `C ⊔ M_σ ⊴ M` and is nilpotent, hence `⊆ F(M)`.
        have hCMσ_le_M : C ⊔ Mσ ≤ M := sup_le inf_le_right hMσ_le_M
        have hCMσ_norm : ((C ⊔ Mσ).subgroupOf M).Normal := by
          rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCMσ_le_M]
          exact le_trans (le_inf hC_norm hM_norm_Mσ)
            (Subgroup.normalizer_inf_normalizer_le_normalizer_sup C Mσ)
        -- `C ⊔ M_σ = X ⊔ M_σ` (since `C = A ⊔ X` and `A ≤ M_σ`).
        have hA_le_Mσ : A ≤ Mσ := inf_le_right
        have hCMσ_eq : C ⊔ Mσ = X ⊔ Mσ := sup_eq_sup_of_eq_sup_of_le hCeq hA_le_Mσ
        -- `X ⊔ M_σ` nilpotent: `X` cyclic, `M_σ` nilpotent, `[X, M_σ] = ⊥` (`X ≤ C_G(M_σ)`).
        have hXcent : ⁅X, Mσ⁆ = ⊥ := by
          have hXle : X ≤ Subgroup.centralizer (Mσ : Set G) := hX_C.trans inf_le_left
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hXle
        haveI hXcyc' : IsCyclic ↥X := hXcyc
        letI : CommGroup ↥X := IsCyclic.commGroup
        haveI : Group.IsNilpotent ↥X := CommGroup.isNilpotent
        haveI hCMσ_nil : Group.IsNilpotent ↥(C ⊔ Mσ) := by
          rw [hCMσ_eq]; exact isNilpotent_sup_of_commutator_eq_bot hXcent
        haveI := hCMσ_norm
        have hCMσ_le_F : C ⊔ Mσ ≤ F :=
          le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent hCMσ_le_M hCMσ_norm
        exact le_sup_left.trans hCMσ_le_F
    -- Conjunct 10: `¬ TypeF → F(M) ⊆ M'`.  `M = K M'`, `M/M' ≅ K` (`κ`-group), `π(Y) ⊆ τ₂`,
    -- and `κ ∩ τ₂ = ∅`, so `Y ≤ M'`; with `M_σ ≤ M'` this gives `F ⊆ M'`.
    have h10 : ¬ S14.IsTypeF M → F ≤ derivedInG M := by
      intro hnotF
      have hP : S14.IsTypeP M := by
        rw [S14.isTypeF_iff_not_isTypeP] at hnotF; exact not_not.mp hnotF
      -- `K ≠ ⊥`: some `κ`-prime divides `|M|`, but a trivial `κ`-Hall would push it to the index.
      have hKne : K ≠ ⊥ := by
        obtain ⟨p, hpκ⟩ := hP
        obtain ⟨hpprime, -, P, hPmem, hPM, -⟩ := id hpκ
        haveI : Fact p.Prime := ⟨hpprime⟩
        -- `p ∣ |M|` (a rank-one elementary abelian `p`-subgroup `P ≤ M`).
        have hpcardP : Nat.card ↥P = p := by
          have := (OddOrder.GroupTheory.mem_elemAbelianOfRank.mp hPmem).2
          rwa [pow_one] at this
        have hpM : p ∈ (Nat.card ↥M).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hpprime,
            hpcardP ▸ Subgroup.card_dvd_of_le hPM, Nat.card_pos.ne'⟩
        intro hKbot
        -- `K = ⊥` ⟹ `(K.subgroupOf M).index = |↥M|`, so `p` divides the index of the `κ`-Hall.
        have hidx : (K.subgroupOf M).index = Nat.card ↥M := by
          rw [hKbot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
        have hpidx : p ∈ (K.subgroupOf M).index.primeFactors := by rw [hidx]; exact hpM
        exact hKHall.2 p hpidx hpκ
      obtain ⟨hMderiv, _, hcompl, _⟩ := hKguard hKne
      -- `Y ≤ M'`: image of the normal `τ₂`-subgroup `Y` in the abelian `M/M'` (order `|K|`, a
      -- `κ`-number) is trivial because `τ₂ ∩ κ = ∅`.
      have hY_le_deriv : Y ≤ derivedInG M := by
        have hYM : Y ≤ M := h3.trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
        set Hsub : Subgroup ↥M := Y.subgroupOf M with hHsub
        set D : Subgroup ↥M := (derivedInG M).subgroupOf M with hDdef
        have hDcomm : D = commutator ↥M :=
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)
        haveI hDnorm : D.Normal := by rw [hDcomm]; infer_instance
        -- `[M : M'] = |K|` (complement), a `κ`-number.
        have hDindex : D.index = Nat.card ↥(K.subgroupOf M) := hcompl.symm.index_eq_card
        -- `Coprime |Y| [M:M']` (`π(Y) ⊆ τ₂`, `π(K) ⊆ κ`, `τ₂ ∩ κ = ∅`).
        have hKpi : ∀ r ∈ (Nat.card ↥(K.subgroupOf M)).primeFactors, r ∈ S14.kappa M :=
          fun r hr => hKHall.1 r hr
        have hcop : Nat.Coprime (Nat.card ↥Hsub) D.index := by
          rw [hDindex]
          refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl Nat.card_pos.ne'
            Nat.card_pos.ne' (π := tau2 M) (fun r hr => ?_) (fun r hr => ?_)
          · -- `π(Y) ⊆ τ₂`.
            have : r ∈ (Nat.card ↥Y).primeFactors := by
              rwa [hHsub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv] at hr
            exact hYτ₂ this
          · -- `κ ∩ τ₂ = ∅`: a `κ`-prime has rank one, a `τ₂`-prime has rank two.
            intro hrτ₂
            have hrκ : r ∈ S14.kappa M := hKpi r hr
            have hr1 : pRank ↥M r = 1 := by
              rcases S14.kappa_subset_tau1_union_tau3 hrκ with h | h
              · exact ((mem_tau1_iff M r).mp h).2.2
              · exact ((mem_tau3_iff M r).mp h).2.2
            have hr2 : pRank ↥M r = 2 := ((mem_tau2_iff M r).mp hrτ₂).2
            rw [hr1] at hr2; exact absurd hr2 (by norm_num)
        -- `Y.subgroupOf M ≤ commutator ↥M`: image in the abelianization is trivial.
        haveI hHnorm : Hsub.Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr hM_norm_Y
        have hcard_img_dvd_Y : Nat.card ↥(Hsub.map (QuotientGroup.mk' D)) ∣ Nat.card ↥Hsub :=
          Subgroup.card_map_dvd Hsub (QuotientGroup.mk' D)
        have hcard_img_dvd_idx : Nat.card ↥(Hsub.map (QuotientGroup.mk' D)) ∣ D.index := by
          rw [Subgroup.index_eq_card]
          exact Subgroup.card_subgroup_dvd_card _
        have hcard_img_one : Nat.card ↥(Hsub.map (QuotientGroup.mk' D)) = 1 :=
          Nat.eq_one_of_dvd_coprimes hcop hcard_img_dvd_Y hcard_img_dvd_idx
        have himg_bot : Hsub.map (QuotientGroup.mk' D) = ⊥ :=
          Subgroup.card_eq_one.mp hcard_img_one
        have hHsub_le_D : Hsub ≤ D := by
          rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at himg_bot
          exact himg_bot
        -- Transport back to `G`: `Y ≤ M'`.
        calc Y = Hsub.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hYM).symm
          _ ≤ D.map M.subtype := Subgroup.map_mono hHsub_le_D
          _ = derivedInG M := Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le _)
      rw [h6, hFMσ_eq]
      exact sup_le ((OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM)) hY_le_deriv
    -- Conjunct 11: `M_F` cyclic → `F(M)` cyclic (`F = M_F × Y`, both cyclic coprime).
    have h11 : IsCyclic ↥(MF M) → IsCyclic ↥F := by
      intro hMFcyc
      haveI := hMFcyc
      haveI := hYcyc
      -- `F = M_F ⊔ Y` with `M_F ⊓ Y = ⊥`, `[M_F, Y] = ⊥`, coprime orders.
      have hMFY_inf : MF M ⊓ Y = ⊥ := by rw [hcase, ← hFMσ_eq]; exact h7
      have hMFY_comm : ⁅(MF M : Subgroup G), Y⁆ = ⊥ := by rw [hcase, ← hFMσ_eq]; exact h8
      have hFeq : F = MF M ⊔ Y := by rw [h6, hFMσ_eq, hcase]
      have hcop : Nat.Coprime (Nat.card ↥(MF M)) (Nat.card ↥Y) := by
        refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl Nat.card_pos.ne' Nat.card_pos.ne'
          (π := σ) (fun r hr => ?_) hY_pi'
        rw [hcase] at hr
        exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r hr
      -- Cyclic product (orderOf approach, mirroring `S06.isCyclic_sup`).
      obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := ↥(MF M))
      obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := ↥Y)
      have hMF_le : MF M ≤ MF M ⊔ Y := le_sup_left
      have hY_le : Y ≤ MF M ⊔ Y := le_sup_right
      have hoa : orderOf (Subgroup.inclusion hMF_le a) = Nat.card ↥(MF M) := by
        rw [orderOf_injective _ (Subgroup.inclusion_injective _) a,
          orderOf_eq_card_of_forall_mem_zpowers ha]
      have hob : orderOf (Subgroup.inclusion hY_le b) = Nat.card ↥Y := by
        rw [orderOf_injective _ (Subgroup.inclusion_injective _) b,
          orderOf_eq_card_of_forall_mem_zpowers hb]
      have hMFnorm_Y : MF M ≤ Subgroup.normalizer (Y : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMFY_comm).trans
          (OddOrder.Isaacs.Ch07.centralizer_le_normalizer Y)
      have hcardsup : Nat.card ↥(MF M ⊔ Y) = Nat.card ↥(MF M) * Nat.card ↥Y := by
        have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card (MF M) Y
        rw [hMFY_inf, Subgroup.card_bot, mul_one] at hprod
        rwa [show ((MF M : Set G) * (Y : Set G)) = ((MF M ⊔ Y : Subgroup G) : Set G) from
          (Subgroup.coe_mul_of_left_le_normalizer_right (MF M) Y hMFnorm_Y).symm] at hprod
      have hcomm : Commute (Subgroup.inclusion hMF_le a) (Subgroup.inclusion hY_le b) := by
        have hab : ((a : G)) * (b : G) = (b : G) * (a : G) :=
          (Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMFY_comm a.2) (b : G) b.2).symm
        exact Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]; exact hab)
      rw [hFeq]
      refine isCyclic_of_orderOf_eq_card
        (Subgroup.inclusion hMF_le a * Subgroup.inclusion hY_le b) ?_
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hoa, hob]; exact hcop),
        hoa, hob, hcardsup]
    exact ⟨Y, hYcyc, hYτ₂, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · -- ### Case II: `M_σ` not nilpotent, `M_F ≠ M_σ`, so `M` is type `P1` and `F(M) ⊆ M_σ`.
    obtain ⟨_hP1, Q, _Q0, _D, _p, _q, _, _, _, _, _, _, _, hQsubMF, _, _, _, _, _, _, hMσderiv,
        _, hFsubMσ, hFQ, hMFnc⟩ :=
      mf_ne_msigma_typeP1_structure hG hM hcase (Subgroup.map_subtype_le K') hKHall rfl
    -- In Case II: `F(M) ⊆ M_σ`, so `Y = O_{σ'}(F(M)) = ⊥` and `F(M) = F(M_σ)`.
    -- `Y = ⊥`: `F(M) ⊆ M_σ` is a `σ`-group, so its `σ'`-Hall core is trivial.
    have hYbot : Y = ⊥ := by
      rw [hY]
      refine OddOrder.GroupTheory.opiCoreInG_compl_eq_bot_of_isPiSubgroup ?_
      intro r hr
      exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hFsubMσ) Nat.card_pos.ne' hr)
    -- `F(M) = F(M_σ)`: `F(M) ◁ M` nilpotent `⊆ M_σ ⟹ ◁ M_σ ⟹ ⊆ F(M_σ)`; `F(M_σ) ⊆ F(M)` (Lemma 1).
    have hFMσ_eq : F = FMσ := by
      refine le_antisymm ?_ ?_
      · -- `F ⊆ M_σ`, `F ◁ M_σ` (since `F ◁ M`), `F` nilpotent ⟹ `F ⊆ F(M_σ)`.
        have hF_norm_Mσ : (F.subgroupOf Mσ).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hFsubMσ).mpr
            (hMσ_le_M.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
              (OddOrder.BG.Ch2.S08.fittingInG_le M)).mp
              (OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal M)))
        exact le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent hFsubMσ hF_norm_Mσ
      · -- `F(M_σ) ⊆ O_σ(F(M)) ⊆ F(M)`.
        rw [← hL1]; exact OddOrder.GroupTheory.opiCoreInG_le σ F
    -- Now assemble.  With `Y = ⊥`, conjuncts (a) and the `× Y` split collapse.
    have hYcyc : IsCyclic ↥Y := by rw [hYbot]; infer_instance
    have hYτ₂ : (↑(Nat.card ↥Y).primeFactors : Set ℕ) ⊆ tau2 M := by
      rw [hYbot, Subgroup.card_bot]; simp
    -- Conjunct 4: `M'' ⊆ F(M)`.
    have h4 : derivedInG (derivedInG M) ≤ F := by
      have hMdd_F : derivedInG (derivedInG M) ≤ fittingInAmbient M := ‹_›
      exact hMdd_F
    -- Conjunct 5 (Case II, `M_F ≠ M_σ`): `F(M) = (C_G(M_F) ⊓ M) ⊔ M_F` (mmd 15.2(g)
    -- "(b) `F(M) = C_M(H)H`" with `H = M_F`).
    have h5 : F = (Subgroup.centralizer (MF M : Set G) ⊓ M) ⊔ MF M := by
      have hMF_le_F : MF M ≤ F := maxNilpotentNormalHall_le_fittingInG M
      have hQ_le_MF : Q ≤ MF M := hQsubMF
      -- `C_M(M_F) ⊆ C_M(Q) ⊆ Q ⊔ C_M(Q) = F(M)` (Theorem 15.2(g) equality `hFQ`).
      have hCMF_le_F : Subgroup.centralizer (MF M : Set G) ⊓ M ≤ F := by
        have hsub : Subgroup.centralizer (MF M : Set G) ⊓ M ≤
            Subgroup.centralizer (Q : Set G) ⊓ M := by
          refine inf_le_inf_right _ ?_
          intro x hx
          rw [Subgroup.mem_centralizer_iff] at hx ⊢
          exact fun g hg => hx g (hQ_le_MF hg)
        rw [hF, hFQ]; exact hsub.trans le_sup_right
      refine le_antisymm ?_ (sup_le hCMF_le_F hMF_le_F)
      -- `⊆` (mmd 15.2(g)): the `σ'`-free, type-`P1` structural step `F(M) ⊆ C_M(M_F)·M_F`.
      -- Strategy (general, §14-independent): `M_F` is the full Hall `π(M_F)`-part of `F(M)`, so the
      -- nilpotent `F(M)` splits as `F(M) = M_F × O_{π(M_F)'}(F(M))`, and the second factor
      -- centralizes `M_F` (distinct Hall components of a nilpotent group commute).
      set π : Set ℕ := ↑(Nat.card ↥(MF M)).primeFactors with hπ
      -- `F ≤ M` and `M ≤ N_G(F)` (`F` is normal in `M`).
      have hF_le_M : F ≤ M := OddOrder.BG.Ch2.S08.fittingInG_le M
      have hM_norm_F : M ≤ Subgroup.normalizer (F : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch2.S08.fittingInG_le M)).mp
          (OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal M)
      -- `M_F ≤ O_π(F)`: `M_F ≤ F`, `(M_F).subgroupOf F ⊴ F` (as `F ≤ M ≤ N_G(M_F)`), `M_F` a `π`-group.
      have hMF_norm_F : (((MF M).subgroupOf F)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hMF_le_F).mpr
          (hF_le_M.trans (maxNilpotentNormalHall_le_normalizer M))
      have hMF_pi : Subgroup.IsPiSubgroup π (MF M) := fun p hp => by
        rw [hπ]; exact Finset.mem_coe.mpr hp
      have hMF_le_Oπ : MF M ≤ OddOrder.GroupTheory.opiCoreInG π F :=
        OddOrder.GroupTheory.le_opiCoreInG_of_normal_of_isPiSubgroup hMF_le_F hMF_norm_F hMF_pi
      -- `O_π(F) ≤ M_F`: `O_π(F)` is a normal `π`-subgroup of `↥M`, and `M_F` is `π`-Hall in `↥M`.
      have hOπ_le_F : OddOrder.GroupTheory.opiCoreInG π F ≤ F :=
        OddOrder.GroupTheory.opiCoreInG_le π F
      have hOπ_le_M : OddOrder.GroupTheory.opiCoreInG π F ≤ M := hOπ_le_F.trans hF_le_M
      haveI hObar_norm : ((OddOrder.GroupTheory.opiCoreInG π F).subgroupOf M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hOπ_le_M).mpr
          (OddOrder.GroupTheory.le_normalizer_opiCoreInG_of_le_normalizer π hM_norm_F)
      have hObar_pi : Ch03.Subgroup.IsPiGroup π ((OddOrder.GroupTheory.opiCoreInG π F).subgroupOf M) := by
        intro p hp
        have hcardO : Nat.card ↥((OddOrder.GroupTheory.opiCoreInG π F).subgroupOf M) =
            Nat.card ↥(OddOrder.GroupTheory.opiCoreInG π F) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOπ_le_M).toEquiv
        exact OddOrder.GroupTheory.isPiSubgroup_opiCoreInG π F p (by rwa [hcardO] at hp)
      have hObar_le_Hbar : (OddOrder.GroupTheory.opiCoreInG π F).subgroupOf M ≤ (MF M).subgroupOf M :=
        Ch03.Subgroup.IsPiGroup.normal_le_hall hObar_pi (maxNilpotentNormalHall_isHall M)
      have hMF_le_M : MF M ≤ M := maxNilpotentNormalHall_le M
      have hOπ_le_MF : OddOrder.GroupTheory.opiCoreInG π F ≤ MF M := by
        have := Subgroup.map_mono (f := M.subtype) hObar_le_Hbar
        rwa [Subgroup.map_subgroupOf_eq_of_le hOπ_le_M,
          Subgroup.map_subgroupOf_eq_of_le hMF_le_M] at this
      have hOπ_eq_MF : OddOrder.GroupTheory.opiCoreInG π F = MF M :=
        le_antisymm hOπ_le_MF hMF_le_Oπ
      -- `F = O_π(F) ⊔ O_{π'}(F) = M_F ⊔ O_{π'}(F)`.
      have hsplit : OddOrder.GroupTheory.opiCoreInG π F ⊔
          OddOrder.GroupTheory.opiCoreInG πᶜ F = F :=
        opiCoreInG_sup_compl_eq_of_isNilpotent π
      -- `O_{π'}(F)` centralizes `M_F = O_π(F)`, and lies in `M`, so `≤ C_G(M_F) ⊓ M`.
      have hcomm : ⁅OddOrder.GroupTheory.opiCoreInG π F,
          OddOrder.GroupTheory.opiCoreInG πᶜ F⁆ = ⊥ :=
        OddOrder.BG.Ch2.S08.opiCoreInG_commutator_compl_eq_bot π F
      have hOπ'_cent : OddOrder.GroupTheory.opiCoreInG πᶜ F ≤
          Subgroup.centralizer (MF M : Set G) := by
        have hcomm' : ⁅OddOrder.GroupTheory.opiCoreInG πᶜ F,
            OddOrder.GroupTheory.opiCoreInG π F⁆ = ⊥ := by
          rw [Subgroup.commutator_comm]; exact hcomm
        rw [← hOπ_eq_MF]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
      have hOπ'_le_M : OddOrder.GroupTheory.opiCoreInG πᶜ F ≤ M :=
        (OddOrder.GroupTheory.opiCoreInG_le πᶜ F).trans hF_le_M
      have hOπ'_le : OddOrder.GroupTheory.opiCoreInG πᶜ F ≤
          Subgroup.centralizer (MF M : Set G) ⊓ M := le_inf hOπ'_cent hOπ'_le_M
      -- Assemble: `F = M_F ⊔ O_{π'}(F) ≤ (C_G(M_F) ⊓ M) ⊔ M_F`.
      calc F = OddOrder.GroupTheory.opiCoreInG π F ⊔
                OddOrder.GroupTheory.opiCoreInG πᶜ F := hsplit.symm
        _ = MF M ⊔ OddOrder.GroupTheory.opiCoreInG πᶜ F := by rw [hOπ_eq_MF]
        _ ≤ MF M ⊔ (Subgroup.centralizer (MF M : Set G) ⊓ M) := sup_le_sup_left hOπ'_le _
        _ = (Subgroup.centralizer (MF M : Set G) ⊓ M) ⊔ MF M := sup_comm _ _
    -- Conjunct 10: `¬ TypeF → F(M) ⊆ M'`.  `F(M) ⊆ M_σ = M'` (Theorem 15.2).
    have h10 : ¬ S14.IsTypeF M → F ≤ derivedInG M := fun _ => hFsubMσ.trans hMσderiv.le
    -- Conjunct 11: `M_F` cyclic → `F(M)` cyclic.  Vacuous: `M_F` is non-cyclic (Theorem 15.2).
    have h11 : IsCyclic ↥(MF M) → IsCyclic ↥F := fun h => absurd h hMFnc
    exact ⟨Y, hYcyc, hYτ₂, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- **§14-independent assembly of BG Corollary 15.6** from its §14/§15 inputs taken as
hypotheses.  This packages the *logic* of Corollary 15.6 (mmd L4232) with no fragile citation of
the still-`sorry` §14 scaffold: once §14 lands, `typeP_kstar_in_mf` discharges each hypothesis by
a single citation and applies this skeleton.  Hypothesis provenance (mmd L4434 dependency table):

* `hKne` (`K* ≠ 1`) ← Proposition 14.2(c) (`typeP_structure`, conjunct `Kstar ≠ ⊥`);
* `hcyc` (`K K*` cyclic) ← Theorem 14.7(d) (`typeP_duality`, conjunct `IsCyclic (K ⊔ Kstar)`);
* `hKsubMF` (`K* ⊆ M_F`) ← Theorem 15.2(b)(c) (case-split on `M_F = M_σ`);
* `hcompl`/`hcop` (`M = K M'`, `K ∩ M' = 1`, coprime) ← Theorem 14.7(h) / Lemma 15.1's `K ≠ 1`
  clause;
* `hFcyc` (`M_F` cyclic ⟹ `F(M)` cyclic) ← Corollary 15.5 (the consequence its proof of 15.6
  cites).

The two nontrivial steps are unconditional: `K* ⊆ M''`
(`Msigma_inf_centralizer_le_derivedDerived_of_isComplement'`) and the `M_F`-not-cyclic
contradiction (`fittingInAmbient_cyclic_imp_derivedDerived_eq_bot`, giving `M'' = 1`, against
`K* ⊆ M''` and `K* ≠ 1`). -/
theorem typeP_kstar_in_mf_of_inputs [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hKne : Kstar ≠ ⊥) (hcyc : IsCyclic ↥(K ⊔ Kstar)) (hKsubMF : Kstar ≤ MF M)
    (hcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M))
    (hcop : Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M))
      (Nat.card ↥(K.subgroupOf M)))
    (hFcyc : IsCyclic ↥(MF M) → IsCyclic ↥(fittingInAmbient M)) :
    Kstar ≠ ⊥ ∧ IsCyclic ↥Kstar ∧ Kstar ≤ MF M ∧
      Kstar ≤ derivedInG (derivedInG M) ∧ ¬ IsCyclic ↥(MF M) := by
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  haveI := hcyc
  -- `K* ⊆ M''`:  the §14-independent conjunct-4 engine.
  have hKsubdd : Kstar ≤ derivedInG (derivedInG M) := by
    rw [hKstar]
    exact Msigma_inf_centralizer_le_derivedDerived_of_isComplement' hG hM hcompl hcop
  refine ⟨hKne, Subgroup.isCyclic_of_le (le_sup_right : Kstar ≤ K ⊔ Kstar), hKsubMF,
    hKsubdd, ?_⟩
  -- `M_F` not cyclic:  else `F(M)` cyclic ⟹ `M'' = 1`, but `K* ⊆ M''` and `K* ≠ 1`.
  intro hcycMF
  have hMdd : derivedInG (derivedInG M) = ⊥ :=
    fittingInAmbient_cyclic_imp_derivedDerived_eq_bot (hFcyc hcycMF)
  exact hKne (le_bot_iff.mp (hMdd ▸ hKsubdd))

/-- **BG Corollary 15.6** (mmd L4174): for a type-P maximal subgroup, `Kstar` is
nontrivial cyclic and lies in `M_F`, while `M_F` itself is not cyclic. -/
theorem typeP_kstar_in_mf [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M)
    (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Kstar ≠ ⊥ ∧ IsCyclic ↥Kstar ∧ Kstar ≤ MF M ∧
      Kstar ≤ derivedInG (derivedInG M) ∧ ¬ IsCyclic ↥(MF M) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- A Hall `(κ ∪ σ)ᶜ`-subgroup `U` of `M` exists by solvability (Hall's theorem); this is the
  -- `U`-factor of the type-`P` decomposition `M = K U M_σ` needed to invoke Proposition 14.2.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  -- `K* ≠ 1`:  Proposition 14.2(c) (`typeP_structure`).
  have hKne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  -- `K K*` cyclic and the `M = K M'` complement / coprime data:  Theorem 14.7(d),(h).
  obtain ⟨hcompl, hcop, _Mstar, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
    typeP_duality hG hM hP hKM hK hKstar
  -- `K* ⊆ M_F`:  Theorem 15.2 when `M_F ≠ M_σ`, else `K* ⊆ M_σ = M_F` directly.
  have hKsubMF : Kstar ≤ MF M := by
    by_cases hMF : MF M = OddOrder.BG.Ch3.S10.Msigma M
    · rw [hKstar, hMF]; exact inf_le_left
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hk, _⟩ :=
        mf_ne_msigma_typeP1_structure hG hM hMF hKM hK hKstar
      exact hk
  -- `M_F` cyclic ⟹ `F(M)` cyclic:  Corollary 15.5 (`fitting_decomposition`, last conjunct).
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hFcyc⟩ := fitting_decomposition hG hM
  exact typeP_kstar_in_mf_of_inputs hG hM hKstar hKne hcyc hKsubMF hcompl hcop hFcyc

end OddOrder.BG.Ch4.S15
