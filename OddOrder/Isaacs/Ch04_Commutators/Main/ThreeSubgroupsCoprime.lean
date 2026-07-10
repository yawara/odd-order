import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroups

/-!
# TAIL

Prefix-split from `OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroupsCoprime` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Isaacs.Ch04
open scoped commutatorElement

variable {G : Type*} [Group G]


section /- 4D: Coprime action — Fitting + Thompson PxQ + Baer (pp. 138-146) -/

/-! ### Isaacs §4C: 連鎖仮定下の A の構造 (Thm 4.22, Cor 4.23) -/

/-- **Bridge lemma** (semidirect product): `K ≤ φ.ker` iff `⁅K.map inr, inl(G).range⁆ = ⊥`
in `Γ = G ⋊[φ] A`. つまり `K ≤ A` が trivial action ↔ `inr(K)` と `inl(G)` が可換.

**証明**: `Subgroup.commutator_eq_bot_iff_le_centralizer` で commutator = ⊥ ↔ centralizer
包含, さらに semidirect product の `inl_aut` (`inl ((φ a) g) = inr a * inl g * inr a⁻¹`)
で `inr(k)` と `inl(g)` が可換 ↔ `(φ k) g = g`. -/
theorem _root_.SemidirectProduct.commutator_inr_inl_range_eq_bot_iff_le_ker
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G} (K : Subgroup A) :
    ⁅K.map (SemidirectProduct.inr : A →* G ⋊[φ] A),
      (SemidirectProduct.inl : G →* G ⋊[φ] A).range⁆ = ⊥ ↔ K ≤ φ.ker := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  constructor
  · -- K.map inr ≤ centralizer inl.range ⇒ K ≤ ker φ
    intro h k hk
    -- k ∈ K. Want φ k = 1, i.e., (φ k) g = g for all g.
    rw [MonoidHom.mem_ker]
    -- Use MulEquiv.ext for (φ k) = 1
    refine MulEquiv.ext fun g => ?_
    -- Goal: (φ k) g = (1 : MulAut G) g = g
    rw [MulAut.one_apply]
    have h_mem : (SemidirectProduct.inr k : G ⋊[φ] A) ∈
        K.map (SemidirectProduct.inr : A →* G ⋊[φ] A) := ⟨k, hk, rfl⟩
    have h_centr := h h_mem
    rw [Subgroup.mem_centralizer_iff] at h_centr
    have h_comm := h_centr (SemidirectProduct.inl g : G ⋊[φ] A) ⟨g, rfl⟩
    -- h_comm : inl g * inr k = inr k * inl g
    have h_aut : (SemidirectProduct.inr k : G ⋊[φ] A) * SemidirectProduct.inl g =
        (SemidirectProduct.inl ((φ k) g) : G ⋊[φ] A) * SemidirectProduct.inr k := by
      have hi := SemidirectProduct.inl_aut (φ := φ) k g
      have h_inv : (SemidirectProduct.inr k⁻¹ : G ⋊[φ] A) = (SemidirectProduct.inr k)⁻¹ :=
        map_inv SemidirectProduct.inr k
      rw [hi, h_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [h_aut] at h_comm
    -- h_comm : inl g * inr k = inl ((φ k) g) * inr k
    have h_eq : (SemidirectProduct.inl g : G ⋊[φ] A) = SemidirectProduct.inl ((φ k) g) :=
      mul_right_cancel h_comm
    exact (SemidirectProduct.inl_injective h_eq).symm
  · -- K ≤ ker φ ⇒ K.map inr ≤ centralizer inl.range
    intro h y hy
    rw [Subgroup.mem_centralizer_iff]
    obtain ⟨k, hk, rfl⟩ := hy
    have h_fix : φ k = 1 := h hk
    intro x hx
    obtain ⟨g, rfl⟩ := hx
    -- Goal: inl g * inr k = inr k * inl g
    have h_aut : (SemidirectProduct.inr k : G ⋊[φ] A) * SemidirectProduct.inl g =
        (SemidirectProduct.inl ((φ k) g) : G ⋊[φ] A) * SemidirectProduct.inr k := by
      have hi := SemidirectProduct.inl_aut (φ := φ) k g
      have h_inv : (SemidirectProduct.inr k⁻¹ : G ⋊[φ] A) = (SemidirectProduct.inr k)⁻¹ :=
        map_inv SemidirectProduct.inr k
      rw [hi, h_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [h_aut, h_fix, MulAut.one_apply]

/-- **Isaacs Corollary 4.23**: A が `G` に faithful 作用 + `[G, A, A] = 1`
(`actionCommutator φ ≤ fixedPointsOfMulAut φ`) ⇒ `commutator A ≤ φ.ker`.

**Faithful case**: φ injective ⇒ φ.ker = ⊥ ⇒ commutator A = ⊥ ⇒ A abelian.

**証明戦略** (Three-subgroups in Γ = G ⋊[φ] A, m = 2 specialization of Thm 4.22):
仮定 ⇒ `⁅⁅inl(G), inr(A)⁆, inr(A)⁆ = ⊥` (= `[G, A, A] = 1` in Γ). Three-subgroups で
`⁅⁅inr(A), inr(A)⁆, inl(G)⁆ = ⊥` (= `[A, A, G] = 1`). これは `inr(A')` と
`inl(G)` の交換子 = ⊥, つまり bridge lemma で `commutator A ≤ φ.ker`. -/
theorem commutator_le_ker_of_acts_trivially_on_actionCommutator
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G)
    (h_triv : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut φ) :
    _root_.commutator A ≤ φ.ker := by
  -- Setup in Γ = G ⋊[φ] A
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range with hXG
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range with hYA
  -- Hypothesis ⇒ ⁅⁅XG, YA⁆, YA⁆ = ⊥ in Γ
  -- (Same Step 1 as in Lem 4.25 / actionCommutator_commutator_eq_bot_of_acts_trivially)
  set H_Γ : Subgroup (G ⋊[φ] A) := ⁅XG, YA⁆
  have h_HΓ_eq : (actionCommutator φ).map SemidirectProduct.inl = H_Γ :=
    actionCommutator_map_inl φ
  have h_step1 : ⁅H_Γ, YA⁆ = ⊥ := by
    rw [← h_HΓ_eq, eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨k, hk, rfl⟩ _ ⟨a, rfl⟩
    rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
    have h_fix : (φ a) k = k := h_triv hk a
    rw [show (φ a) k⁻¹ = ((φ a) k)⁻¹ from map_inv (φ a) k, h_fix, mul_inv_cancel]
    exact map_one _
  -- Apply three-subgroups in Γ with H₁ = YA, H₂ = YA, H₃ = XG
  -- (this gives ⁅⁅YA, YA⁆, XG⁆ = ⊥)
  have h_three : ⁅⁅YA, YA⁆, XG⁆ = ⊥ := by
    -- We need: ⁅⁅YA, XG⁆, YA⁆ = ⊥ and ⁅⁅XG, YA⁆, YA⁆ = ⊥, then conclude ⁅⁅YA, YA⁆, XG⁆ = ⊥.
    have h_a : ⁅⁅YA, XG⁆, YA⁆ = ⊥ := by
      rw [Subgroup.commutator_comm YA XG]
      exact h_step1
    have h_b : ⁅⁅XG, YA⁆, YA⁆ = ⊥ := h_step1
    -- mathlib three-subgroups: ⁅⁅H₂, H₃⁆, H₁⁆ = ⊥ → ⁅⁅H₃, H₁⁆, H₂⁆ = ⊥ → ⁅⁅H₁, H₂⁆, H₃⁆ = ⊥
    -- With H₁ = YA, H₂ = YA, H₃ = XG: gives ⁅⁅YA, YA⁆, XG⁆ = ⊥ from h_a + h_b.
    exact Subgroup.commutator_commutator_eq_bot_of_rotate h_a h_b
  -- Now convert ⁅⁅YA, YA⁆, XG⁆ = ⊥ to ⁅(commutator A).map inr, inl(G).range⁆ = ⊥
  rw [← SemidirectProduct.commutator_inr_inl_range_eq_bot_iff_le_ker]
  -- Goal: ⁅(commutator A).map inr, inl(G).range⁆ = ⊥
  have h_eq : (_root_.commutator A).map (SemidirectProduct.inr : A →* G ⋊[φ] A) = ⁅YA, YA⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator]
    -- ⁅⊤, ⊤⁆.map inr = ⁅(⊤).map inr, (⊤).map inr⁆ = ⁅inr.range, inr.range⁆
    rw [show ((⊤ : Subgroup A).map (SemidirectProduct.inr : A →* G ⋊[φ] A)) = YA from
        (MonoidHom.range_eq_map SemidirectProduct.inr).symm]
  rw [h_eq]
  exact h_three

/-- **Isaacs Cor 4.23 (faithful)**: A が `G` に faithful 作用 + `[G, A, A] = 1`
⇒ A is abelian (`commutator A = ⊥`).

`commutator_le_ker_of_acts_trivially_on_actionCommutator` の faithful 特殊化. -/
theorem commutator_eq_bot_of_acts_trivially_on_actionCommutator_of_faithful
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G)
    (h_inj : Function.Injective φ)
    (h_triv : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut φ) :
    _root_.commutator A = ⊥ := by
  have h_ker : φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ).mpr h_inj
  have h_le : _root_.commutator A ≤ φ.ker :=
    commutator_le_ker_of_acts_trivially_on_actionCommutator φ h_triv
  rw [h_ker] at h_le
  exact le_bot_iff.mp h_le

/-! ### Isaacs §4C: Thm 4.22 (chain stabilization ⇒ A solvable) -/

/-- **Helper**: `iterCommutator (iterCommutator E X j) X k = iterCommutator E X (j + k)`.
-/
lemma iterCommutator_add (E X : Subgroup G) (j k : ℕ) :
    iterCommutator (iterCommutator E X j) X k = iterCommutator E X (j + k) := by
  induction k with
  | zero => simp [iterCommutator_zero]
  | succ k ih =>
    rw [iterCommutator_succ, ih]
    rw [show j + (k + 1) = (j + k) + 1 from by omega, iterCommutator_succ]

/-- **Abstract subgroup form of Isaacs Theorem 4.22**: For subgroups `E X` of an
ambient group `H` with `X ≤ E.normalizer` and `iterCommutator E X m = ⊥` for `m ≥ 1`,
the `(m-1)`-th derived series of `X` (viewed in `H`) commutes trivially with `E`.

**証明** (induction on `m`):
- Base `m = 1`: `iter E X 1 = ⁅E, X⁆ = ⊥`. `derivedSeries ↥X 0 = ⊤`, `.map subtype = X`.
  Goal: `⁅X, E⁆ = ⊥` = `⁅E, X⁆ = ⊥` ✓.
- Step `m = k + 1 ≥ 2`: Set `E' := ⁅E, X⁆`. `X ≤ E'.normalizer`
  (Lem 4.3: `⁅E, X⁆ ≤ E` ⇒ `⁅⁅E, X⁆, X⁆ ≤ ⁅E, X⁆`).
  `iter E' X k = iter E X (k+1) = ⊥` (helper). IH ⇒ `⁅D, E'⁆ = ⊥` where
  `D := (derivedSeries ↥X (k-1)).map subtype`.
  Three-subgroups with `H₁ = H₂ = D, H₃ = E`:
  * `⁅⁅D, E⁆, D⁆ ≤ ⁅⁅E, X⁆, D⁆ = ⁅D, ⁅E, X⁆⁆ = ⊥` (IH + comm)
  * `⁅⁅E, D⁆, D⁆ ≤ ⁅⁅E, X⁆, D⁆ = ⊥` (same)
  * ⇒ `⁅⁅D, D⁆, E⁆ = ⊥` (Three-subgroups).
  `⁅D, D⁆ = (⁅derivedSeries (k-1), derivedSeries (k-1)⁆).map subtype =
    (derivedSeries ↥X k).map subtype`. ✓ -/
theorem derivedSeries_subtype_commutator_eq_bot_of_iter_eq_bot
    {H : Type*} [Group H] {X : Subgroup H} (m : ℕ) (hm : 1 ≤ m) :
    ∀ {E : Subgroup H}, X ≤ Subgroup.normalizer E →
      iterCommutator E X m = ⊥ →
      ⁅((derivedSeries (↥X) (m - 1)).map X.subtype), E⁆ = ⊥ := by
  induction m with
  | zero => omega
  | succ k ih =>
    intro E h_norm h_iter
    rcases Nat.eq_zero_or_pos k with hk | hk
    · -- m = 1 base case (k = 0)
      subst hk
      -- derivedSeries (1-1) = derivedSeries 0 = ⊤, .map subtype = X
      have h_top : (⊤ : Subgroup ↥X).map X.subtype = X :=
        (MonoidHom.range_eq_map X.subtype).symm.trans X.range_subtype
      have h_idx : (0 + 1 : ℕ) - 1 = 0 := by omega
      rw [h_idx, derivedSeries_zero, h_top]
      -- Goal: ⁅X, E⁆ = ⊥. Hyp: iter E X 1 = ⁅E, X⁆ = ⊥.
      rw [Subgroup.commutator_comm]
      have h1 : iterCommutator E X (0 + 1) = ⁅E, X⁆ := by
        rw [iterCommutator_succ, iterCommutator_zero]
      rw [← h1]; exact h_iter
    · -- m = k + 1 ≥ 2 (k ≥ 1)
      have hk_le : 1 ≤ k := hk
      -- E' := ⁅E, X⁆
      set E' : Subgroup H := ⁅E, X⁆ with hE'_def
      -- X normalizes E'
      have h_norm_E' : X ≤ Subgroup.normalizer E' := by
        rw [← commutator_le_iff_le_normalizer]
        refine Subgroup.commutator_mono ?_ le_rfl
        exact commutator_le_iff_le_normalizer.mpr h_norm
      -- iter E' X k = iter E X (k+1) = ⊥
      have h_iter_E' : iterCommutator E' X k = ⊥ := by
        show iterCommutator (iterCommutator E X 1) X k = ⊥
        rw [iterCommutator_add]
        convert h_iter using 2
        omega
      -- IH applied
      have h_IH : ⁅(derivedSeries ↥X (k - 1)).map X.subtype, E'⁆ = ⊥ :=
        ih hk_le h_norm_E' h_iter_E'
      set D : Subgroup H := (derivedSeries ↥X (k - 1)).map X.subtype with hD_def
      -- D ≤ X
      have hD_le_X : D ≤ X := by
        rw [hD_def]
        exact (Subgroup.map_mono le_top).trans
          ((MonoidHom.range_eq_map X.subtype).symm.trans X.range_subtype).le
      -- ⁅D, ⁅E, X⁆⁆ = ⊥ from IH
      -- Three-subgroups in ambient H: H₁ = D, H₂ = D, H₃ = E
      have h_DE : ⁅⁅D, E⁆, D⁆ = ⊥ := by
        have h_le1 : ⁅D, E⁆ ≤ ⁅X, E⁆ := Subgroup.commutator_mono hD_le_X le_rfl
        have h_le2 : ⁅⁅D, E⁆, D⁆ ≤ ⁅⁅X, E⁆, D⁆ := Subgroup.commutator_mono h_le1 le_rfl
        have h_swap : ⁅⁅X, E⁆, D⁆ = ⁅D, ⁅E, X⁆⁆ := by
          rw [Subgroup.commutator_comm X E, Subgroup.commutator_comm ⁅E, X⁆ D]
        rw [h_swap] at h_le2
        exact le_bot_iff.mp (h_le2.trans h_IH.le)
      have h_ED : ⁅⁅E, D⁆, D⁆ = ⊥ := by
        rw [Subgroup.commutator_comm E D]
        exact h_DE
      -- Three-subgroups: gives ⁅⁅D, D⁆, E⁆ = ⊥
      have h_DDE : ⁅⁅D, D⁆, E⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate h_DE h_ED
      -- ⁅D, D⁆ = ((derivedSeries ↥X k)).map subtype
      have h_DD : (⁅D, D⁆ : Subgroup H) =
          (derivedSeries (↥X) k).map X.subtype := by
        rw [hD_def, ← Subgroup.map_commutator]
        congr 1
        rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk_le).symm,
            derivedSeries_succ]
        congr 2
      show ⁅(derivedSeries ↥X (k + 1 - 1)).map X.subtype, E⁆ = ⊥
      rw [show k + 1 - 1 = k from by omega]
      rw [← h_DD]
      exact h_DDE

/-- **Isaacs Theorem 4.22** ⭐: A 作用 + `[G, A, ..., A]_m = 1` ⇒
`derivedSeries A (m-1) ≤ φ.ker`. (faithful case: A is solvable with derived length ≤ m-1.)

Semidirect product `Γ = G ⋊[φ] A` 形で記述: iter (inl(G).range) (inr(A).range) m = ⊥
⇒ derivedSeries A (m-1) ≤ φ.ker. -/
theorem derivedSeries_le_ker_of_iter_inl_inr_eq_bot
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) (m : ℕ) (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
                             (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    derivedSeries A (m - 1) ≤ φ.ker := by
  -- Apply abstract form with X = inr(A).range, E = inl(G).range
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  haveI hXG_normal : XG.Normal := OddOrder.Isaacs.Ch03.inl_range_normal φ
  -- YA ≤ Subgroup.normalizer XG (XG normal ⇒ normalizer = ⊤)
  have h_norm : YA ≤ Subgroup.normalizer XG := by
    intro y _
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hXG_normal.conj_mem _ hz y, fun hz => ?_⟩
    have h1 := hXG_normal.conj_mem _ hz y⁻¹
    -- h1 : y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ ∈ XG, simplifies to z ∈ XG via group
    rwa [show y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z by group] at h1
  have h_abs := derivedSeries_subtype_commutator_eq_bot_of_iter_eq_bot
    (X := YA) m hm h_norm h_iter
  -- Bridge: ⁅(derivedSeries A (m-1)).map inr, XG⁆ = ⊥ ⇔ derivedSeries A (m-1) ≤ φ.ker
  rw [← SemidirectProduct.commutator_inr_inl_range_eq_bot_iff_le_ker]
  -- Transport: (derivedSeries A (m-1)).map inr = (derivedSeries ↥YA (m-1)).map YA.subtype
  have h_transport : ((derivedSeries A (m - 1)).map
      (SemidirectProduct.inr : A →* G ⋊[φ] A)) =
      (derivedSeries (↥YA) (m - 1)).map YA.subtype := by
    have h_factor : (SemidirectProduct.inr : A →* G ⋊[φ] A) =
        YA.subtype.comp (SemidirectProduct.inr (φ := φ)).rangeRestrict :=
      (MonoidHom.subtype_comp_rangeRestrict _).symm
    rw [h_factor, ← Subgroup.map_map]
    congr 1
    have h_surj : Function.Surjective (SemidirectProduct.inr (φ := φ)).rangeRestrict :=
      (SemidirectProduct.inr : A →* G ⋊[φ] A).rangeRestrict_surjective
    exact map_derivedSeries_eq h_surj (m - 1)
  rw [h_transport]
  exact h_abs

/-- **Isaacs Theorem 4.22 (faithful)**: A が `G` に faithful 作用 +
`iter (inl(G).range) (inr(A).range) m = ⊥` (= `[G, A, ..., A]_m = 1`)
⇒ A is solvable with derived length ≤ m - 1 (`derivedSeries A (m-1) = ⊥`). -/
theorem derivedSeries_eq_bot_of_iter_inl_inr_eq_bot_of_faithful
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G)
    (h_inj : Function.Injective φ) (m : ℕ) (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
                             (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    derivedSeries A (m - 1) = ⊥ := by
  have h_ker : φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ).mpr h_inj
  have h_le := derivedSeries_le_ker_of_iter_inl_inr_eq_bot φ m hm h_iter
  rw [h_ker] at h_le
  exact le_bot_iff.mp h_le

private lemma iterCommutator_eq_inl_range_of_actionCommutator_eq_top
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G)
    (h_top : actionCommutator φ = ⊤) :
    ∀ {m : ℕ}, 1 ≤ m →
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m =
      (SemidirectProduct.inl : G →* G ⋊[φ] A).range := by
  intro m hm
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  have h_one : iterCommutator XG YA 1 = XG := by
    change ⁅XG, YA⁆ = XG
    rw [← actionCommutator_map_inl (φ := φ), h_top]
    simpa [XG] using
      (MonoidHom.range_eq_map (SemidirectProduct.inl : G →* G ⋊[φ] A)).symm
  induction m with
  | zero => omega
  | succ n ih =>
      rcases n with _ | n
      · exact h_one
      · have hn : 1 ≤ n + 1 := by omega
        rw [iterCommutator_succ, ih hn]
        exact h_one

lemma actionCommutator_eq_bot_of_eq_top_iterCommutator_eq_bot
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G)
    {m : ℕ} (hm : 1 ≤ m)
    (h_top : actionCommutator φ = ⊤)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    actionCommutator φ = ⊥ := by
  have h_m :=
    iterCommutator_eq_inl_range_of_actionCommutator_eq_top φ h_top hm
  have hX_bot : (SemidirectProduct.inl : G →* G ⋊[φ] A).range = ⊥ := by
    rw [← h_m, h_iter]
  have h_map_bot : (actionCommutator φ).map
      (SemidirectProduct.inl : G →* G ⋊[φ] A) = ⊥ := by
    rw [actionCommutator_map_inl, hX_bot]
    simp
  exact (Subgroup.map_eq_bot_iff_of_injective
    (actionCommutator φ) SemidirectProduct.inl_injective).mp h_map_bot

/-! ### Isaacs §4D Lem 4.28 ⭐ (BG Prop 1.6(a)): G = C_G(A) · [G,A] for coprime + solvable -/

/-- **Isaacs Lemma 4.28** ⭐ (= BG Prop 1.6(a), **FT クリティカル**):
A acts on G via φ. Coprime (`|A|, |G|`) + one of A or G solvable ⇒
`fixedPointsOfMulAut φ ⊔ actionCommutator φ = ⊤` (= `G = C_G(A) · [G, A]`).

**証明** (Isaacs p.138, ~6 lines): Write `Ḡ = G / [G, A]`. By Cor 3.28 (coprime fixed points
come from G fixed points), `C_Ḡ(A) = image of C_G(A) under quotient`. But A acts trivially
on `Ḡ` (definition of `[G, A]` ⇒ `A` fixes every coset, so `C_Ḡ(A) = Ḡ`).
Hence `image of C_G(A) = Ḡ`, i.e., `C_G(A) ⊔ [G, A] = G`.

**Lean 化**: 各 `g ∈ G`, Cor 3.28 を `N = [G, A]` で適用 ⇒ ∃ `c ∈ C_G(A), c ∈ g · [G, A]`,
i.e., `c = g * n` for `n ∈ [G, A]`. Then `g = c * n⁻¹ ∈ C_G(A) * [G, A]`. -/
theorem fixedPoints_sup_actionCommutator_eq_top
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G) :
    Subgroup.fixedPointsOfMulAut φ ⊔ actionCommutator φ = ⊤ := by
  rw [eq_top_iff]
  intro g _
  -- Setup: N := actionCommutator φ, which is normal and A-invariant
  have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutator φ) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator φ
  -- For every a ∈ A, (φ a) g = g * n with n := g⁻¹ * (φ a) g ∈ actionCommutator
  -- (Lem 4.20 left form: actionCommutator ≤ actionCommutator gives this)
  have hg_fix : ∀ a : A, ∃ n ∈ actionCommutator φ, (φ a) g = g * n := by
    intro a
    refine ⟨g⁻¹ * (φ a) g, ?_, ?_⟩
    · exact (actionCommutator_le_iff_left φ (actionCommutator φ)).mp le_rfl a g
    · group
  -- Apply Cor 3.28: ∃ c ∈ C_G(A), c ∈ g · actionCommutator
  obtain ⟨c, hc_fix, ⟨n, hn_mem, hc_eq⟩⟩ :=
    coprime_fixedPoints_quotient hCop hSolv hN_inv hg_fix
  -- c ∈ fixedPointsOfMulAut, n⁻¹ ∈ actionCommutator
  have hc_mem : c ∈ Subgroup.fixedPointsOfMulAut φ := hc_fix
  -- g = c * n⁻¹: from hc_eq : c = g * n, so g = c * n⁻¹
  have hg_eq : g = c * n⁻¹ := by rw [hc_eq]; group
  -- g ∈ fixedPointsOfMulAut * actionCommutator ⊆ sup
  rw [hg_eq]
  exact Subgroup.mul_mem_sup hc_mem ((actionCommutator φ).inv_mem hn_mem)

/-! ### Isaacs §4D Lem 4.29 ⭐ (BG Prop 1.6(b)): [G, A, A] = [G, A] for coprime + solvable -/

/-- **Isaacs Lemma 4.29** (Γ form) ⭐: coprime + (A or G solvable) ⇒
`iterCommutator inl(G).range inr(A).range 2 = iterCommutator inl(G).range inr(A).range 1`
in Γ = G ⋊[φ] A. Equivalent (Isaacs notation): `[G, A, A] = [G, A]`.

**証明** (Isaacs p.139): Each generator `⁅inl g, inr a⁆` of [G, A]_Γ is in [G, A, A]_Γ.
By Lem 4.28: g = c * x with c ∈ C_G(A), x ∈ actionCommutator.
- `⁅inl c, inr a⁆ = 1` (c ∈ C_G(A) ⇒ inl c and inr a commute in Γ).
- Commutator identity: `⁅inl c · inl x, inr a⁆ = inl c · ⁅inl x, inr a⁆ · inl c⁻¹ · ⁅inl c, inr a⁆`
  `= inl c · ⁅inl x, inr a⁆ · inl c⁻¹`.
- Conjugate by inl c (= conjugate_commutatorElement): `= ⁅inl(cxc⁻¹), inr a⁆` (using
  inl c commutes with inr a).
- `cxc⁻¹ ∈ actionCommutator` (G-normal), so `inl(cxc⁻¹) ∈ inl(actionCommutator) = [G, A]_Γ`
  (`actionCommutator_map_inl`).
- Hence `⁅inl(cxc⁻¹), inr a⁆ ∈ ⁅[G, A]_Γ, inr(A).range⁆ = [G, A, A]_Γ`. -/
theorem iterCommutator_inl_inr_two_eq_one
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G) :
    iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
                   (SemidirectProduct.inr : A →* G ⋊[φ] A).range 2 =
    iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
                   (SemidirectProduct.inr : A →* G ⋊[φ] A).range 1 := by
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  -- I1 = ⁅XG, YA⁆ = [G, A]_Γ, I2 = ⁅I1, YA⁆ = [G, A, A]_Γ
  -- I1.Normal in Γ (Lem 4.1 系 via XG ⊔ YA = ⊤)
  haveI hI1_normal : (⁅XG, YA⁆).Normal :=
    commutator_normal_of_sup_eq_top SemidirectProduct.inl_range_sup_inr_range_eq_top
  refine le_antisymm ?_ ?_
  · -- I2 ≤ I1 (trivial: I1 normal in Γ, so ⁅I1, F⁆ ≤ I1)
    show iterCommutator XG YA 2 ≤ iterCommutator XG YA 1
    show ⁅iterCommutator XG YA 1, YA⁆ ≤ iterCommutator XG YA 1
    rw [show iterCommutator XG YA 1 = ⁅XG, YA⁆ from rfl]
    exact Subgroup.commutator_le_left _ _
  · -- I1 ≤ I2 (the substantive direction)
    show iterCommutator XG YA 1 ≤ iterCommutator XG YA 2
    show ⁅XG, YA⁆ ≤ ⁅iterCommutator XG YA 1, YA⁆
    rw [Subgroup.commutator_le]
    rintro _ ⟨g_0, rfl⟩ _ ⟨a, rfl⟩
    -- Goal: ⁅inl g_0, inr a⁆ ∈ ⁅iterCommutator XG YA 1, YA⁆
    -- By Lem 4.28: g_0 = c * x, c ∈ fixedPoints, x ∈ actionCommutator
    have h_top : g_0 ∈ Subgroup.fixedPointsOfMulAut φ ⊔ actionCommutator φ := by
      rw [fixedPoints_sup_actionCommutator_eq_top hCop hSolv]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_right] at h_top
    obtain ⟨c, hc_fix, x, hx_ac, h_eq⟩ := h_top
    -- h_eq : c * x = g_0
    have h_fix : (φ a) c = c := hc_fix a
    -- ⁅inl c, inr a⁆ = 1 (c ∈ fixedPoints ⇒ inl c commutes with inr a)
    have h_commute_ca : Commute (SemidirectProduct.inl c : G ⋊[φ] A)
        (SemidirectProduct.inr a) := by
      -- inl c · inr a = inr a · inl c iff (φ a) c = c (which holds by h_fix)
      show (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inr a =
          SemidirectProduct.inr a * SemidirectProduct.inl c
      -- inr a * inl c * inr a⁻¹ = inl((φ a) c) = inl c (by inl_aut + h_fix)
      have h_aut := SemidirectProduct.inl_aut (φ := φ) a c
      rw [h_fix] at h_aut
      -- h_aut : inl c = inr a * inl c * inr a⁻¹
      -- Want: inl c * inr a = inr a * inl c
      -- From h_aut: inl c * inr a = (inr a * inl c * inr a⁻¹) * inr a
      --           = inr a * inl c * (inr a⁻¹ * inr a) = inr a * inl c
      have h_inv_eq : (SemidirectProduct.inr a⁻¹ : G ⋊[φ] A) =
          (SemidirectProduct.inr a)⁻¹ := map_inv SemidirectProduct.inr a
      rw [h_inv_eq] at h_aut
      rw [show (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inr a =
            (SemidirectProduct.inr a * SemidirectProduct.inl c * (SemidirectProduct.inr a)⁻¹) *
              SemidirectProduct.inr a from by rw [← h_aut]]
      group
    have h_comm_ca_eq_one : ⁅(SemidirectProduct.inl c : G ⋊[φ] A),
        SemidirectProduct.inr a⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr h_commute_ca
    -- Goal: ⁅inl g_0, inr a⁆ ∈ ⁅⁅XG, YA⁆, YA⁆
    -- g_0 = c * x, so inl g_0 = inl c * inl x. Use commutator identity.
    rw [← h_eq, map_mul SemidirectProduct.inl]
    -- Goal: ⁅inl c * inl x, inr a⁆ ∈ ...
    -- Identity: ⁅cx, a⁆ = c · ⁅x, a⁆ · c⁻¹ · ⁅c, a⁆
    have h_id : ⁅(SemidirectProduct.inl c * SemidirectProduct.inl x : G ⋊[φ] A),
        (SemidirectProduct.inr a : G ⋊[φ] A)⁆ =
        (SemidirectProduct.inl c : G ⋊[φ] A) *
          ⁅(SemidirectProduct.inl x : G ⋊[φ] A), SemidirectProduct.inr a⁆ *
          (SemidirectProduct.inl c)⁻¹ *
          ⁅(SemidirectProduct.inl c : G ⋊[φ] A), SemidirectProduct.inr a⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h_id, h_comm_ca_eq_one, mul_one]
    -- Goal: inl c * ⁅inl x, inr a⁆ * (inl c)⁻¹ ∈ ⁅⁅XG, YA⁆, YA⁆
    -- = ⁅inl c · inl x · (inl c)⁻¹, inl c · inr a · (inl c)⁻¹⁆ (conjugate_commutatorElement)
    -- inl c · inr a · (inl c)⁻¹ = inr a (commute)
    rw [conjugate_commutatorElement]
    have h_conj_ca : (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inr a *
        (SemidirectProduct.inl c)⁻¹ = SemidirectProduct.inr a := by
      rw [show (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inr a =
          SemidirectProduct.inr a * SemidirectProduct.inl c from h_commute_ca]
      group
    rw [h_conj_ca]
    -- Goal: ⁅inl c * inl x * (inl c)⁻¹, inr a⁆ ∈ ⁅⁅XG, YA⁆, YA⁆
    -- inl c * inl x * (inl c)⁻¹ = inl(c * x * c⁻¹) ∈ inl(actionCommutator) = ⁅XG, YA⁆
    have h_lift : (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inl x *
        (SemidirectProduct.inl c)⁻¹ = SemidirectProduct.inl (c * x * c⁻¹) := by
      have h_inv : ((SemidirectProduct.inl c : G ⋊[φ] A))⁻¹ = SemidirectProduct.inl c⁻¹ :=
        (map_inv SemidirectProduct.inl c).symm
      rw [h_inv, ← map_mul, ← map_mul]
    rw [h_lift]
    -- c * x * c⁻¹ ∈ actionCommutator (G-normal)
    haveI : (actionCommutator φ).Normal := actionCommutator.normal φ
    have h_cxc_ac : c * x * c⁻¹ ∈ actionCommutator φ :=
      ‹(actionCommutator φ).Normal›.conj_mem _ hx_ac c
    -- inl(c * x * c⁻¹) ∈ (actionCommutator).map inl = ⁅XG, YA⁆ (= I1)
    have h_in_I1 : (SemidirectProduct.inl (c * x * c⁻¹) : G ⋊[φ] A) ∈ ⁅XG, YA⁆ := by
      have := actionCommutator_map_inl (φ := φ)
      rw [← this]
      exact ⟨c * x * c⁻¹, h_cxc_ac, rfl⟩
    exact Subgroup.commutator_mem_commutator h_in_I1 ⟨a, rfl⟩

private lemma iterCommutator_eq_one_of_two_eq_one
    {E F : Subgroup G}
    (h : iterCommutator E F 2 = iterCommutator E F 1) :
    ∀ {m : ℕ}, 1 ≤ m → iterCommutator E F m = iterCommutator E F 1 := by
  intro m hm
  induction m with
  | zero => omega
  | succ n ih =>
      rcases n with _ | n
      · rfl
      · have hn : 1 ≤ n + 1 := by omega
        rw [iterCommutator_succ, ih hn]
        simpa [iterCommutator_succ] using h

theorem iterCommutator_inl_inr_restrict_eq_bot
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    (P : Subgroup A) {m : ℕ}
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    let ψ : P →* MulAut G := φ.comp P.subtype
    iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
        (SemidirectProduct.inr : P →* G ⋊[ψ] P).range m = ⊥ := by
  dsimp
  let ψ : P →* MulAut G := φ.comp P.subtype
  let F : G ⋊[ψ] P →* G ⋊[φ] A :=
    SemidirectProduct.map (MonoidHom.id G) P.subtype (fun p => by
      ext g
      rfl)
  let XGP : Subgroup (G ⋊[ψ] P) := (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
  let YPP : Subgroup (G ⋊[ψ] P) := (SemidirectProduct.inr : P →* G ⋊[ψ] P).range
  let XGA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  let YAA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  have hF_inj : Function.Injective F := by
    intro x y hxy
    ext
    · simpa [F] using congrArg (fun z : G ⋊[φ] A => z.left) hxy
    · simpa [F] using congrArg (fun z : G ⋊[φ] A => z.right) hxy
  have h_map_X : XGP.map F = XGA := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, by simp [F]⟩
    · rintro ⟨g, rfl⟩
      refine ⟨(SemidirectProduct.inl : G →* G ⋊[ψ] P) g, ⟨g, rfl⟩, ?_⟩
      simp [F]
  have h_map_Y : YPP.map F ≤ YAA := by
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨p.1, by simp [F]⟩
  have h_map_iter_all :
      ∀ n : ℕ, (iterCommutator XGP YPP n).map F ≤ iterCommutator XGA YAA n := by
    intro n
    induction n with
    | zero =>
        simpa [iterCommutator_zero] using h_map_X.le
    | succ n ih =>
        rw [iterCommutator_succ, iterCommutator_succ, Subgroup.map_commutator]
        exact Subgroup.commutator_mono ih h_map_Y
  have h_map_bot : (iterCommutator XGP YPP m).map F = ⊥ := by
    refine le_antisymm ?_ bot_le
    exact (h_map_iter_all m).trans (le_of_eq h_iter)
  exact (Subgroup.map_eq_bot_iff_of_injective (iterCommutator XGP YPP m) hF_inj).mp h_map_bot

theorem iterCommutator_inl_inr_restrict_base_eq_bot
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) {m : ℕ}
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    let ψ : A →* MulAut H := OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH
    iterCommutator (SemidirectProduct.inl : H →* H ⋊[ψ] A).range
        (SemidirectProduct.inr : A →* H ⋊[ψ] A).range m = ⊥ := by
  dsimp
  let ψ : A →* MulAut H := OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH
  let F : H ⋊[ψ] A →* G ⋊[φ] A :=
    SemidirectProduct.map H.subtype (MonoidHom.id A) (fun a => by
      ext h
      rfl)
  let XH : Subgroup (H ⋊[ψ] A) := (SemidirectProduct.inl : H →* H ⋊[ψ] A).range
  let YA_H : Subgroup (H ⋊[ψ] A) := (SemidirectProduct.inr : A →* H ⋊[ψ] A).range
  let XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  let YA_G : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  have hF_inj : Function.Injective F := by
    intro x y hxy
    ext
    · simpa [F] using congrArg (fun z : G ⋊[φ] A => z.left) hxy
    · simpa [F] using congrArg (fun z : G ⋊[φ] A => z.right) hxy
  have h_map_X : XH.map F ≤ XG := by
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    exact ⟨h.1, by simp [F]⟩
  have h_map_Y : YA_H.map F ≤ YA_G := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, by simp [F]⟩
  have h_map_iter_all :
      ∀ n : ℕ, (iterCommutator XH YA_H n).map F ≤ iterCommutator XG YA_G n := by
    intro n
    induction n with
    | zero =>
        simpa [iterCommutator_zero] using h_map_X
    | succ n ih =>
        rw [iterCommutator_succ, iterCommutator_succ, Subgroup.map_commutator]
        exact Subgroup.commutator_mono ih h_map_Y
  have h_map_bot : (iterCommutator XH YA_H m).map F = ⊥ := by
    refine le_antisymm ?_ bot_le
    exact (h_map_iter_all m).trans (le_of_eq h_iter)
  exact (Subgroup.map_eq_bot_iff_of_injective (iterCommutator XH YA_H m) hF_inj).mp h_map_bot

/-- **Isaacs Corollary 4.30**:
Let `A` act faithfully on the finite group `G`. If an iterated commutator
`[G, A, ..., A]` is trivial, then every prime divisor of `|A|` divides `|G|`.

Proof: for a prime `p ∤ |G|`, restrict the action to a Sylow `p`-subgroup `P ≤ A`.
The restricted action is coprime, and the chain hypothesis restricts from `A` to `P`.
Lemma 4.29 collapses the restricted iterated commutator to `[G, P] = 1`, so `P`
acts trivially. Faithfulness forces `P = 1`, hence `p ∤ |A|`. -/
theorem prime_dvd_card_of_faithful_iterCommutator_eq_bot
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    (φ : A →* MulAut G) (h_inj : Function.Injective φ)
    {m : ℕ} (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥)
    {p : ℕ} (hp : p.Prime) (hpA : p ∣ Nat.card A) :
    p ∣ Nat.card G := by
  by_contra hpG
  haveI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p A := default
  let ψ : P →* MulAut G := φ.comp (P : Subgroup A).subtype
  have h_iter_P :
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
          (SemidirectProduct.inr : P →* G ⋊[ψ] P).range m = ⊥ := by
    simpa [ψ] using
      iterCommutator_inl_inr_restrict_eq_bot (φ := φ) (P : Subgroup A) h_iter
  have hCop_PG : Nat.Coprime (Nat.card P) (Nat.card G) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpG)
  have hSolv : IsSolvable P ∨ IsSolvable G := by
    left
    haveI : Group.IsNilpotent P := P.isPGroup'.isNilpotent
    infer_instance
  have h_two :
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
          (SemidirectProduct.inr : P →* G ⋊[ψ] P).range 2 =
        iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
          (SemidirectProduct.inr : P →* G ⋊[ψ] P).range 1 :=
    iterCommutator_inl_inr_two_eq_one (φ := ψ) hCop_PG hSolv
  have h_iter_one :
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
          (SemidirectProduct.inr : P →* G ⋊[ψ] P).range 1 = ⊥ := by
    have h_m := iterCommutator_eq_one_of_two_eq_one h_two hm
    rw [h_m] at h_iter_P
    exact h_iter_P
  have hP_le_ker : (⊤ : Subgroup P) ≤ ψ.ker := by
    rw [← SemidirectProduct.commutator_inr_inl_range_eq_bot_iff_le_ker]
    rw [show (⊤ : Subgroup P).map (SemidirectProduct.inr : P →* G ⋊[ψ] P) =
        (SemidirectProduct.inr : P →* G ⋊[ψ] P).range from
        (MonoidHom.range_eq_map _).symm]
    rw [Subgroup.commutator_comm]
    exact h_iter_one
  have hP_bot : (P : Subgroup A) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    let x : P := ⟨a, ha⟩
    have hx_ker : x ∈ ψ.ker := hP_le_ker (Subgroup.mem_top x)
    rw [MonoidHom.mem_ker] at hx_ker
    have hφa : φ a = 1 := by
      -- `ψ x = φ ((↑P).subtype ⟨a, ha⟩)` is definitionally `φ a`.
      exact hx_ker
    exact h_inj (by simpa using hφa)
  exact (P.ne_bot_of_dvd_card hpA) hP_bot

private theorem actionCommutator_isPGroup_of_iter_eq_bot_aux
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (hA : IsPGroup p A) :
    ∀ n : ℕ, ∀ {G : Type*} [Group G] [Finite G],
      (φ : A →* MulAut G) → ∀ {m : ℕ}, 1 ≤ m →
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥ →
      Nat.card G ≤ n → IsPGroup p (actionCommutator φ) := by
  intro n
  induction n with
  | zero =>
      intro G _ _ φ m hm h_iter h_le
      exfalso
      exact Nat.not_succ_le_zero _ (Nat.card_pos.trans_le h_le)
  | succ n ih =>
      intro G _ _ φ m hm h_iter h_le
      by_cases htop : actionCommutator φ = ⊤
      · have hbot :=
          actionCommutator_eq_bot_of_eq_top_iterCommutator_eq_bot φ hm htop h_iter
        rw [hbot]
        exact IsPGroup.of_bot
      set N : Subgroup G := actionCommutator φ with hN_def
      have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ N := by
        simpa [N, hN_def] using OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator φ
      let ψN : A →* MulAut N := OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hN_inv
      have h_iter_N :
          iterCommutator (SemidirectProduct.inl : N →* N ⋊[ψN] A).range
              (SemidirectProduct.inr : A →* N ⋊[ψN] A).range m = ⊥ := by
        simpa [ψN] using
          iterCommutator_inl_inr_restrict_base_eq_bot (φ := φ) hN_inv h_iter
      have hN_card_lt : Nat.card N < Nat.card G := by
        exact subgroup_card_lt_card_of_ne_top (G := G) (H := N) (by simpa [N, hN_def] using htop)
      have hNA_pgroup : IsPGroup p (actionCommutator ψN) :=
        ih ψN hm h_iter_N (Nat.le_of_lt_succ (hN_card_lt.trans_le h_le))
      set U : Subgroup N := OddOrder.Isaacs.Ch01.opCore p N with hU_def
      set U_G : Subgroup G := U.map N.subtype with hUG_def
      haveI hUG_normal : U_G.Normal := by
        dsimp [U_G]
        infer_instance
      have hU_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ U_G := by
        simpa [U_G, hUG_def, U, hU_def] using
          (OddOrder.Isaacs.Ch03.IsAInvariant.map_subtype_of_characteristic
            (φ := φ) hN_inv (K := U))
      let q : G →* G ⧸ U_G := QuotientGroup.mk' U_G
      let φbar : A →* MulAut (G ⧸ U_G) :=
        _root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hU_inv
      let Nbar : Subgroup (G ⧸ U_G) := N.map q
      have h_ac_bar : actionCommutator φbar = Nbar := by
        rw [actionCommutator_quotient_eq_map hU_inv]
      have hNA_le_U : actionCommutator ψN ≤ U := by
        haveI : (actionCommutator ψN).Normal := actionCommutator.normal ψN
        simpa [U, hU_def] using
          (OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore
            (N := actionCommutator ψN) hNA_pgroup)
      have hNbar_fixed : Nbar ≤ Subgroup.fixedPointsOfMulAut φbar := by
        rintro y ⟨g, hgN, rfl⟩ a
        change (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hU_inv a)
            (QuotientGroup.mk' U_G g) = QuotientGroup.mk' U_G g
        rw [_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
        change (((φ a) g : G) : G ⧸ U_G) = (g : G ⧸ U_G)
        rw [QuotientGroup.eq]
        have hdeltaN :
            (⟨g, hgN⟩ : N)⁻¹ * (ψN a) ⟨g, hgN⟩ ∈ U :=
          (actionCommutator_le_iff_left ψN U).mp hNA_le_U a ⟨g, hgN⟩
        have hdeltaG : g⁻¹ * (φ a) g ∈ U_G := by
          refine ⟨(⟨g, hgN⟩ : N)⁻¹ * (ψN a) ⟨g, hgN⟩, hdeltaN, ?_⟩
          simp [ψN]
        simpa [mul_inv_rev] using U_G.inv_mem hdeltaG
      have h_comm_Nbar : ⁅Nbar, Nbar⁆ = ⊥ := by
        rw [← h_ac_bar]
        exact actionCommutator_commutator_eq_bot_of_acts_trivially φbar
          (by simpa [h_ac_bar] using hNbar_fixed)
      have hNbar_comm : IsMulCommutative Nbar :=
        Subgroup.le_centralizer_iff_isMulCommutative.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h_comm_Nbar)
      let f : N →* G ⧸ U_G := q.comp N.subtype
      have hf_ker : f.ker = U := by
        ext x
        change ((x.1 : G) : G ⧸ U_G) = 1 ↔ x ∈ U
        rw [QuotientGroup.eq_one_iff]
        constructor
        · intro hx
          rcases hx with ⟨u, huU, hu_eq⟩
          have hux : u = x := Subtype.ext hu_eq
          simpa [hux] using huU
        · intro hx
          exact ⟨x, hx, rfl⟩
      have hf_range : f.range = Nbar := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨x.1, x.2, rfl⟩
        · rintro ⟨g, hgN, rfl⟩
          exact ⟨⟨g, hgN⟩, rfl⟩
      have hOpQ0 : OddOrder.Isaacs.Ch01.opCore p (N ⧸ U) = ⊥ := by
        simpa [U, hU_def] using opCore_quotient_opCore_eq_bot (G := N) p
      let e : (N ⧸ U) ≃* Nbar :=
        (QuotientGroup.quotientMulEquivOfEq hf_ker.symm).trans
          ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hf_range))
      have hOpNbar : OddOrder.Isaacs.Ch01.opCore p Nbar = ⊥ :=
        opCore_eq_bot_of_mulEquiv e hOpQ0
      have hNbar_pi_top :
          OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)}
            (⊤ : Subgroup Nbar) := by
        letI : IsMulCommutative Nbar := hNbar_comm
        exact isPiGroup_compl_top_of_isMulCommutative_opCore_eq_bot
          (G := Nbar) (p := p) hOpNbar
      have hNbar_pi :
          OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} Nbar := by
        intro r hr
        exact hNbar_pi_top r (by simpa using hr)
      have hA_pi_top :
          OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) (⊤ : Subgroup A) :=
        isPiGroup_singleton_of_isPGroup (G := A) (H := ⊤) (hA.to_subgroup _)
      have hA_pi_card : ∀ r ∈ (Nat.card A).primeFactors, r ∈ ({p} : Set ℕ) := by
        intro r hr
        exact hA_pi_top r (by simpa using hr)
      have hCop : Nat.Coprime (Nat.card A) (Nat.card Nbar) :=
        OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
          Nat.card_pos.ne' Nat.card_pos.ne' hA_pi_card hNbar_pi
      have hSolv : IsSolvable A ∨ IsSolvable Nbar := by
        left
        haveI : Group.IsNilpotent A := hA.isNilpotent
        exact IsNilpotent.to_isSolvable
      have hNbar_inv : OddOrder.Isaacs.Ch03.IsAInvariant φbar Nbar := by
        rw [← h_ac_bar]
        exact OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator φbar
      have hphi_bar_triv : ∀ a : A, ∀ g : G ⧸ U_G, (φbar a) g = g := by
        intro a g
        have hg_fix : ∀ b : A, ∃ n ∈ Nbar, (φbar b) g = g * n := by
          intro b
          refine ⟨g⁻¹ * (φbar b) g, ?_, by group⟩
          exact (actionCommutator_le_iff_left φbar Nbar).mp (le_of_eq h_ac_bar) b g
        obtain ⟨c, hc_fix, ⟨n0, hn0, hc_eq⟩⟩ :=
          coprime_fixedPoints_quotient_of_coprime_normal
            hCop hSolv hNbar_inv hg_fix
        have hn0_fix : (φbar a) n0 = n0 := hNbar_fixed hn0 a
        have hc_fix_a := hc_fix a
        rw [hc_eq, map_mul, hn0_fix] at hc_fix_a
        exact mul_right_cancel hc_fix_a
      have hbar_bot : actionCommutator φbar = ⊥ :=
        (actionCommutator_eq_bot_iff_acts_trivially φbar).mpr hphi_bar_triv
      have hNbar_bot : Nbar = ⊥ := by
        rw [← h_ac_bar, hbar_bot]
      have hN_le_U : N ≤ U_G := by
        have hmap_bot : N.map q = ⊥ := by
          simpa [Nbar] using hNbar_bot
        have hle_ker : N ≤ q.ker := (Subgroup.map_eq_bot_iff N).mp hmap_bot
        simpa [q, QuotientGroup.ker_mk', U_G, hUG_def] using hle_ker
      have hU_pgroup : IsPGroup p U_G := by
        simpa [U_G, hUG_def, U, hU_def] using
          (OddOrder.Isaacs.Ch01.opCore_isPGroup p N).map N.subtype
      have hN_pgroup : IsPGroup p N :=
        hU_pgroup.of_injective (Subgroup.inclusion hN_le_U)
          (Subgroup.inclusion_injective hN_le_U)
      simpa [N, hN_def] using hN_pgroup

/-- **Isaacs Theorem 4.26**: if a finite `p`-group `A` acts on finite `G` and
`[G, A, ..., A] = 1`, then `[G, A]` is a `p`-group. -/
theorem isaacs_thm_4_26
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {p : ℕ} [Fact p.Prime] (φ : A →* MulAut G) (hA : IsPGroup p A)
    {m : ℕ} (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    IsPGroup p (actionCommutator φ) :=
  actionCommutator_isPGroup_of_iter_eq_bot_aux hA (Nat.card G) φ hm h_iter le_rfl

private theorem actionCommutator_isNilpotent_of_iter_eq_bot_aux :
    ∀ n : ℕ, ∀ {A G : Type*} [Group A] [Finite A] [Group G] [Finite G],
      (φ : A →* MulAut G) → ∀ {m : ℕ}, 1 ≤ m →
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥ →
      Nat.card A ≤ n → Group.IsNilpotent (actionCommutator φ) := by
  intro n
  induction n with
  | zero =>
      intro A G _ _ _ _ φ m hm h_iter h_le
      exfalso
      exact Nat.not_succ_le_zero _ (Nat.card_pos.trans_le h_le)
  | succ n ih =>
      intro A G _ _ _ _ φ m hm h_iter h_le
      by_cases hA_nontriv : Nontrivial A
      swap
      · haveI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA_nontriv
        have hbot : actionCommutator φ = ⊥ := by
          rw [actionCommutator_eq_bot_iff_acts_trivially]
          intro a g
          have ha : a = 1 := Subsingleton.elim a 1
          simp [ha]
        rw [hbot]
        infer_instance
      by_cases hSylowTop :
          ∃ p0 : (Nat.card A).primeFactors, ∃ P : Sylow p0.val A, (P : Subgroup A) = ⊤
      · rcases hSylowTop with ⟨p0, P, hPtop⟩
        haveI hp0 : Fact p0.val.Prime := ⟨Nat.prime_of_mem_primeFactors p0.property⟩
        have hA_pgroup : IsPGroup p0.val A := by
          have hP_pgroup : IsPGroup p0.val (P : Subgroup A) := P.isPGroup'
          rw [hPtop] at hP_pgroup
          exact hP_pgroup.of_equiv Subgroup.topEquiv
        exact (isaacs_thm_4_26 (p := p0.val) φ hA_pgroup hm h_iter).isNilpotent
      · let F : Subgroup G := OddOrder.Isaacs.Ch01.fitting G
        have hF_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ F := by
          simpa [F] using OddOrder.Isaacs.Ch03.IsAInvariant.fittingSubgroup φ
        let φF : A →* MulAut (G ⧸ F) :=
          _root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hF_inv
        have hSylow_le_ker :
            ∀ p0 : (Nat.card A).primeFactors, ∀ P : Sylow p0.val A,
              (P : Subgroup A) ≤ φF.ker := by
          intro p0 P a haP
          haveI hp0 : Fact p0.val.Prime := ⟨Nat.prime_of_mem_primeFactors p0.property⟩
          have hP_ne_top : (P : Subgroup A) ≠ ⊤ := fun hPtop =>
            hSylowTop ⟨p0, P, hPtop⟩
          let ψP : P →* MulAut G := φ.comp (P : Subgroup A).subtype
          have h_iter_P :
              iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψP] P).range
                  (SemidirectProduct.inr : P →* G ⋊[ψP] P).range m = ⊥ := by
            simpa [ψP] using
              iterCommutator_inl_inr_restrict_eq_bot (φ := φ) (P : Subgroup A) h_iter
          have hP_card_lt : Nat.card P < Nat.card A :=
            subgroup_card_lt_card_of_ne_top (G := A) (H := (P : Subgroup A)) hP_ne_top
          have hNilpP : Group.IsNilpotent (actionCommutator ψP) :=
            ih ψP hm h_iter_P (Nat.le_of_lt_succ (hP_card_lt.trans_le h_le))
          have hP_comm_le_F : actionCommutator ψP ≤ F := by
            haveI : (actionCommutator ψP).Normal := actionCommutator.normal ψP
            haveI : Group.IsNilpotent (actionCommutator ψP) := hNilpP
            simpa [F] using
              (OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
                (G := G) (N := actionCommutator ψP))
          let x : P := ⟨a, haP⟩
          rw [MonoidHom.mem_ker]
          ext y
          refine QuotientGroup.induction_on y ?_
          intro g
          change (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hF_inv a)
              (QuotientGroup.mk' F g) = QuotientGroup.mk' F g
          rw [_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
          change (((φ a) g : G) : G ⧸ F) = (g : G ⧸ F)
          rw [QuotientGroup.eq]
          have hdelta : g⁻¹ * (φ a) g ∈ F := by
            have := (actionCommutator_le_iff_left ψP F).mp hP_comm_le_F x g
            simpa [ψP, x] using this
          simpa [mul_inv_rev] using F.inv_mem hdelta
        have hker_top : φF.ker = ⊤ := by
          apply eq_top_iff.mpr
          rw [← iSup_sylow_eq_top (M := A)]
          exact iSup_le (fun p0 => iSup_le (fun P => hSylow_le_ker p0 P))
        have hφF_triv : ∀ a : A, ∀ y : G ⧸ F, (φF a) y = y := by
          intro a y
          have ha : a ∈ φF.ker := by
            rw [hker_top]
            exact Subgroup.mem_top a
          rw [MonoidHom.mem_ker] at ha
          rw [ha]
          rfl
        have hφF_bot : actionCommutator φF = ⊥ :=
          (actionCommutator_eq_bot_iff_acts_trivially φF).mpr hφF_triv
        have hmap_bot : (actionCommutator φ).map (QuotientGroup.mk' F) = ⊥ := by
          rw [← actionCommutator_quotient_eq_map hF_inv, hφF_bot]
        have hAC_le_F : actionCommutator φ ≤ F := by
          have hle_ker : actionCommutator φ ≤ (QuotientGroup.mk' F).ker :=
            (Subgroup.map_eq_bot_iff (actionCommutator φ)).mp hmap_bot
          simpa [QuotientGroup.ker_mk'] using hle_ker
        have hAC_sub_nilp : Group.IsNilpotent ((actionCommutator φ).subgroupOf F) :=
          inferInstance
        exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAC_le_F)

/-- **Isaacs Theorem 4.27**: if finite `A` acts on finite `G` and
`[G, A, ..., A] = 1`, then `[G, A]` is nilpotent. -/
theorem isaacs_thm_4_27
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    (φ : A →* MulAut G) {m : ℕ} (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    Group.IsNilpotent (actionCommutator φ) :=
  actionCommutator_isNilpotent_of_iter_eq_bot_aux (Nat.card A) φ hm h_iter le_rfl

/-! ### Isaacs §4D Thm 4.34 ⭐ (Fitting, BG Prop 1.6(d)): G abelian + coprime ⇒
G = C_G(A) × [G, A] -/

/-- **Fitting product hom** `θ : G →* G` defined by `θ(g) = ∏ a : A, (φ a) g`.

Well-defined hom for abelian G (使用 Finset.prod_mul_distrib). 教科書 (Isaacs p.140) の
Thm 4.34 証明の核. -/
noncomputable def fittingProductHom {A G : Type*} [CommGroup G] [Group A] [Fintype A]
    (φ : A →* MulAut G) : G →* G where
  toFun g := ∏ a : A, (φ a) g
  map_one' := by simp
  map_mul' x y := by
    simp_rw [map_mul]
    exact Finset.prod_mul_distrib

/-- **`fittingProductHom` of A-fixed element**: c ∈ C_G(A) ⇒ θ c = c^|A|. -/
lemma fittingProductHom_apply_of_fixed {A G : Type*} [CommGroup G] [Group A] [Fintype A]
    {φ : A →* MulAut G} {c : G} (hc : ∀ a : A, (φ a) c = c) :
    fittingProductHom φ c = c ^ Nat.card A := by
  show ∏ a : A, (φ a) c = c ^ Nat.card A
  have h_eq : ∏ a : A, (φ a) c = ∏ _a : A, c :=
    Finset.prod_congr rfl (fun a _ => hc a)
  rw [h_eq, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- **`fittingProductHom` of action-image**: For g ∈ G, a ∈ A,
`θ ((φ a) g) = θ g` (using `b ↦ b * a` is a permutation of A). -/
lemma fittingProductHom_apply_of_smul {A G : Type*} [CommGroup G] [Group A] [Fintype A]
    {φ : A →* MulAut G} (g : G) (a : A) :
    fittingProductHom φ ((φ a) g) = fittingProductHom φ g := by
  show ∏ b : A, (φ b) ((φ a) g) = ∏ b : A, (φ b) g
  -- Rewrite (φ b) ∘ (φ a) = φ (b * a) using map_mul
  have h_compose : ∀ b : A, (φ b) ((φ a) g) = (φ (b * a)) g := fun b => by
    rw [← MulAut.mul_apply, ← map_mul]
  rw [Finset.prod_congr (rfl : (Finset.univ : Finset A) = Finset.univ)
        (fun b _ => h_compose b)]
  -- ∏ b : A, (φ (b * a)) g = ∏ b' : A, (φ b') g (b' = b * a is a bijection)
  exact Finset.prod_bijective (fun b => b * a) (Group.mulRight_bijective a)
    (fun b => by simp) (fun _ _ => rfl)

/-- **`actionCommutator` is in `ker (fittingProductHom)`** (G abelian).

For each generator `g * (φ a) g⁻¹` of `actionCommutator`: `θ (g * (φ a) g⁻¹) = θ g * θ ((φ a) g)⁻¹
= θ g * (θ g)⁻¹ = 1` (using θ hom + `fittingProductHom_apply_of_smul` + map_inv on φ a). -/
lemma actionCommutator_le_ker_fittingProductHom
    {A G : Type*} [CommGroup G] [Group A] [Fintype A] (φ : A →* MulAut G) :
    actionCommutator φ ≤ (fittingProductHom φ).ker := by
  rw [actionCommutator, Subgroup.closure_le]
  rintro _ ⟨g, a, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  -- Goal: θ (g * (φ a) g⁻¹) = 1
  -- (φ a) g⁻¹ = (φ a)(g⁻¹) = ((φ a) g)⁻¹
  have h_inv_eq : (φ a) g⁻¹ = ((φ a) g)⁻¹ := map_inv (φ a) g
  rw [h_inv_eq, map_mul, map_inv, fittingProductHom_apply_of_smul]
  exact mul_inv_cancel _

/-- **Isaacs Theorem 4.34** ⭐ (Fitting, = BG Prop 1.6(d)):
G abelian + A 作用 + coprime (|A|, |G|) ⇒
`fixedPointsOfMulAut φ ⊓ actionCommutator φ = ⊥` (intersection trivial,
combined with Lem 4.28 sup = ⊤ gives internal direct product `G = C_G(A) × [G, A]`).

**証明** (Isaacs p.140): θ : G →* G, `θ g = ∏ a : A, (φ a) g`.
- For c ∈ C_G(A): `θ c = c^|A|`.
- `actionCommutator ⊆ ker θ` (各生成元 `[g, a] ↦ 1`).
- So `c ∈ C_G(A) ∩ actionCommutator ⇒ θ c = c^|A| = 1`. Combined with `c^|G| = 1`
  (Lagrange) + coprime ⇒ `c = 1` (Bezout: ∃ s t, s|A| + t|G| = 1, c = c^1 = ...). -/
theorem fixedPoints_inf_actionCommutator_eq_bot_of_abelian
    {A G : Type*} [CommGroup G] [Group A] [Finite A] [Finite G]
    (φ : A →* MulAut G) (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    Subgroup.fixedPointsOfMulAut φ ⊓ actionCommutator φ = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  obtain ⟨hc_fix, hc_ac⟩ := Subgroup.mem_inf.mp hc
  -- c is A-fixed
  have hc_fixed : ∀ a : A, (φ a) c = c := hc_fix
  -- c ∈ ker θ via actionCommutator ⊆ ker θ
  haveI : Fintype A := Fintype.ofFinite A
  have hc_ker : fittingProductHom φ c = 1 :=
    actionCommutator_le_ker_fittingProductHom φ hc_ac
  -- θ c = c^|A| from hc_fixed
  have hc_pow_A : c ^ Nat.card A = 1 := by
    rw [← fittingProductHom_apply_of_fixed hc_fixed]; exact hc_ker
  -- c^|G| = 1 (Lagrange)
  have hc_pow_G : c ^ Nat.card G = 1 := pow_card_eq_one'
  -- Bezout: ∃ s t, s|A| + t|G| = 1 (coprime), then c = c^(s|A| + t|G|) = 1
  have h_one : c = 1 := by
    have h_gcd : Nat.gcd (Nat.card A) (Nat.card G) = 1 := hCop
    -- Use orderOf c ∣ Nat.card A and orderOf c ∣ Nat.card G ⇒ orderOf c ∣ gcd = 1 ⇒ c = 1
    have h_ord_A : orderOf c ∣ Nat.card A := orderOf_dvd_of_pow_eq_one hc_pow_A
    have h_ord_G : orderOf c ∣ Nat.card G := orderOf_dvd_of_pow_eq_one hc_pow_G
    have h_ord_gcd : orderOf c ∣ Nat.gcd (Nat.card A) (Nat.card G) :=
      Nat.dvd_gcd h_ord_A h_ord_G
    rw [h_gcd] at h_ord_gcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h_ord_gcd)
  exact h_one

/-! ### Isaacs §4D Cor 4.35 ⭐ (BG Prop 1.6(e)): abelian p-群 + p'-A fixes order-p ⇒
A trivial -/

/-- **Isaacs Corollary 4.35** ⭐ (= BG Prop 1.6(e), **FT クリティカル**):
G is abelian p-群, A is p'-group (i.e., p ∤ |A|), A acts on G via automorphisms.
If A fixes every element of order p (i.e., every g with `g^p = 1`), then
`actionCommutator φ = ⊥` (A acts trivially on G).

**証明** (Isaacs p.141):
- Coprime: p ∤ |A| + G p-group ⇒ |A| coprime |G|.
- G abelian + coprime ⇒ Thm 4.34: `fixedPoints ⊓ actionCommutator = ⊥`.
- Suppose [G, A] = actionCommutator ≠ ⊥. Then nontrivial subgroup of p-group G.
- Cauchy: ∃ g ∈ [G, A] with orderOf g = p. So `g^p = 1`, `g ≠ 1`.
- Hypothesis: A fixes g, i.e., g ∈ fixedPoints.
- So g ∈ fixedPoints ⊓ [G, A] = ⊥, contradicting g ≠ 1. -/
theorem actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p
    {A G : Type*} [Group A] [CommGroup G] [Finite A] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (φ : A →* MulAut G) (hG : IsPGroup p G)
    (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g) :
    actionCommutator φ = ⊥ := by
  -- Coprime |A|, |G|: G is p-group ⇒ |G| = p^n. p ∤ |A| ⇒ gcd = 1.
  have hCop : Nat.Coprime (Nat.card A) (Nat.card G) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
    rw [hn]
    exact (Nat.Coprime.pow_right n
      (Nat.coprime_comm.mp (Nat.Prime.coprime_iff_not_dvd hp.out |>.mpr hA_p')))
  -- Apply Thm 4.34: fixedPoints ⊓ actionCommutator = ⊥
  have h_inf_bot := fixedPoints_inf_actionCommutator_eq_bot_of_abelian φ hCop
  -- Suppose actionCommutator ≠ ⊥, get contradiction via Cauchy
  by_contra h_ne_bot
  -- ∃ g ∈ actionCommutator with g ≠ 1
  obtain ⟨g_elem, hg_in, hg_ne⟩ : ∃ g ∈ actionCommutator φ, g ≠ 1 := by
    by_contra h
    push Not at h
    apply h_ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    exact h
  -- actionCommutator is nontrivial subgroup of p-group ⇒ has order-p element
  haveI hG_AC : IsPGroup p (actionCommutator φ) := hG.to_subgroup _
  haveI : Nontrivial (actionCommutator φ) := ⟨⟨g_elem, hg_in⟩, 1, by
    intro h
    apply hg_ne
    exact (Subtype.ext_iff.mp h)⟩
  obtain ⟨n, hn_pos, hn_card⟩ := hG_AC.nontrivial_iff_card.mp inferInstance
  -- |actionCommutator| = p^n with n ≥ 1, so p ∣ |actionCommutator|
  have hp_dvd : p ∣ Nat.card (actionCommutator φ) := by
    rw [hn_card]; exact dvd_pow_self p hn_pos.ne'
  -- Cauchy: ∃ g ∈ actionCommutator with orderOf g = p
  obtain ⟨g, hg_ord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  -- Convert orderOf inside subgroup ⇒ orderOf in G via subtype is preserved
  have h_ord_eq : orderOf (g : G) = orderOf g := by
    exact (orderOf_injective (actionCommutator φ).subtype
      (Subgroup.subtype_injective _) g)
  have h_ord_g : orderOf (g : G) = p := h_ord_eq.trans hg_ord
  -- g^p = 1 in G
  have hg_pow : (g : G) ^ p = 1 := by
    rw [← h_ord_g]; exact pow_orderOf_eq_one _
  -- g is fixed by A (hypothesis)
  have hg_fixed : ∀ a : A, (φ a) (g : G) = g := h_fix g hg_pow
  -- So g ∈ fixedPointsOfMulAut ⊓ actionCommutator = ⊥
  have hg_in_inf : (g : G) ∈ Subgroup.fixedPointsOfMulAut φ ⊓ actionCommutator φ :=
    Subgroup.mem_inf.mpr ⟨hg_fixed, g.2⟩
  rw [h_inf_bot, Subgroup.mem_bot] at hg_in_inf
  -- hg_in_inf : (g : G) = 1, but orderOf g = p > 1, contradiction
  have : orderOf (g : G) = 1 := by rw [hg_in_inf, orderOf_one]
  rw [h_ord_g] at this
  exact hp.out.one_lt.ne' this

end
end OddOrder.Isaacs.Ch04

