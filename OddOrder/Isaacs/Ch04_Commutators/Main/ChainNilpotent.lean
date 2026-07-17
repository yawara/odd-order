import OddOrder.Isaacs.Ch04_Commutators.Main.BaerTrick

/-!
# Isaacs §4C Thm 4.24 — faithful chain action ⇒ A nilpotent

Split from the former monolithic `OddOrder.Isaacs.Ch04_Commutators.Main` (directory split, issue 0103).
-/
namespace OddOrder.Isaacs.Ch04
open scoped commutatorElement

variable {G : Type*} [Group G]


/-! ### Isaacs §4C Thm 4.24 ⭐: faithful chain action ⇒ A nilpotent

**ステートメント** (Isaacs p.139): `A`, `G` finite. `A` が `G` に faithful に作用 +
`[G, A, ..., A]_m = 1` ⇒ `A` is nilpotent.

**証明戦略**: `|G|`-induction で **`A^∞` acts trivially on `G`** (non-faithful generalized
form) を示す. faithful 仮定下では `A^∞ ⊆ C_A(G) = ⊥` から `A` nilpotent.

**Phase 1 (本ファイル)**: `lowerCentralSeriesInfty A := lcs A (Nat.card A)` の infra と
stability lemma. Phase 2/3 (three-subgroups helpers + main theorem) は後続. -/

section /- §4C (続): Theorem 4.24 — faithful chain action ⇒ `A` nilpotent (infra) -/

variable {A : Type*} [Group A]

/-- 真部分群は真に小さい濃度を持つ (`Set.Finite.card_lt_card` の Subgroup 版). -/
private lemma nat_card_lt_of_subgroup_lt {G : Type*} [Group G] [Finite G]
    {H₁ H₂ : Subgroup G} (h : H₁ < H₂) :
    Nat.card H₁ < Nat.card H₂ := by
  exact Set.Finite.card_lt_card (Set.toFinite _) (SetLike.coe_ssubset_coe.mpr h)

/-- 鳩の巣論法: 有限群の lcs は `Nat.card A` step 以内に必ず stabilize する.
    具体的には `lcs A (Nat.card A) = lcs A (Nat.card A + 1)`. -/
private lemma lowerCentralSeries_card_eq_succ_card [Finite A] :
    (⊤ : Subgroup A).lowerCentralSeries (Nat.card A)
      = (⊤ : Subgroup A).lowerCentralSeries (Nat.card A + 1) := by
  -- antitone を使って ≤ は trivial. < は矛盾を導く.
  refine le_antisymm ?_ ((⊤ : Subgroup A).lowerCentralSeries_antitone (Nat.le_succ _))
  -- by contradiction: もし lcs (N+1) < lcs N なら、それまで全 step も strict
  -- かもしれない. しかしそうとは限らないので、別ルートで.
  -- Claim: ∃ k ≤ Nat.card A, lcs k = lcs (k+1). これを取れば stability propagation.
  suffices h : ∃ k ≤ Nat.card A, (⊤ : Subgroup A).lowerCentralSeries k
      = (⊤ : Subgroup A).lowerCentralSeries (k + 1) by
    obtain ⟨k, hk_le, hk_eq⟩ := h
    -- propagate: lcs k = lcs (k+1) ⇒ lcs (k+j) = lcs k for all j
    have h_prop : ∀ j, (⊤ : Subgroup A).lowerCentralSeries (k + j)
        = (⊤ : Subgroup A).lowerCentralSeries k := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
          have h1 : (⊤ : Subgroup A).lowerCentralSeries (k + (j + 1)) =
              ⁅(⊤ : Subgroup A).lowerCentralSeries (k + j), ⊤⁆ := rfl
          rw [h1, ih]
          have h2 : (⊤ : Subgroup A).lowerCentralSeries (k + 1) =
              ⁅(⊤ : Subgroup A).lowerCentralSeries k, ⊤⁆ := rfl
          rw [← h2, hk_eq]
    -- want: lcs (Nat.card A) ≤ lcs (Nat.card A + 1)
    -- show both = lcs k
    have h_LHS : (⊤ : Subgroup A).lowerCentralSeries (Nat.card A)
        = (⊤ : Subgroup A).lowerCentralSeries k := by
      have hN : Nat.card A = k + (Nat.card A - k) := by omega
      rw [hN]; exact h_prop _
    have h_RHS : (⊤ : Subgroup A).lowerCentralSeries (Nat.card A + 1)
        = (⊤ : Subgroup A).lowerCentralSeries k := by
      have hN : Nat.card A + 1 = k + (Nat.card A - k + 1) := by omega
      rw [hN]; exact h_prop _
    rw [h_LHS, h_RHS]
  -- prove existence: by contradiction (pigeonhole)
  by_contra h_no_stable
  push Not at h_no_stable
  -- h_no_stable : ∀ k ≤ Nat.card A, lcs k ≠ lcs (k+1)
  -- antitone + ≠ ⇒ strict at every step ≤ Nat.card A
  have h_strict : ∀ k ≤ Nat.card A,
      (⊤ : Subgroup A).lowerCentralSeries (k + 1)
        < (⊤ : Subgroup A).lowerCentralSeries k := fun k hk =>
    lt_of_le_of_ne ((⊤ : Subgroup A).lowerCentralSeries_antitone (Nat.le_succ k))
      (fun heq => h_no_stable k hk heq.symm)
  -- card bound: Nat.card (lcs k) ≤ Nat.card A - k for k ≤ Nat.card A + 1
  have h_card_bound : ∀ k ≤ Nat.card A + 1,
      Nat.card ((⊤ : Subgroup A).lowerCentralSeries k) + k ≤ Nat.card A + 1 := by
    intro k hk
    induction k with
    | zero =>
        simp only [Nat.add_zero]
        have h_top : (⊤ : Subgroup A).lowerCentralSeries 0 = ⊤ := rfl
        rw [h_top]
        have h_top_card : Nat.card (⊤ : Subgroup A) = Nat.card A :=
          Nat.card_congr Subgroup.topEquiv.toEquiv
        omega
    | succ n ih =>
        have hn : n ≤ Nat.card A := by omega
        have hn_le : n ≤ Nat.card A + 1 := Nat.le_succ_of_le hn
        have ih' : Nat.card ((⊤ : Subgroup A).lowerCentralSeries n) + n
            ≤ Nat.card A + 1 := ih hn_le
        have h_strict_n := h_strict n hn
        have h_card_lt := nat_card_lt_of_subgroup_lt h_strict_n
        omega
  -- Apply at k = Nat.card A + 1
  have h_final := h_card_bound (Nat.card A + 1) le_rfl
  have h_ge_one : 1 ≤ Nat.card ((⊤ : Subgroup A).lowerCentralSeries (Nat.card A + 1)) :=
    Nat.card_pos
  omega

/-- The "infinity term" of the lower central series for a finite group `A`:
`A^∞ := lowerCentralSeries A (Nat.card A)`. For a finite group this is the eventual
stable value of the lower central series. -/
noncomputable def lowerCentralSeriesInfty (A : Type*) [Group A] [Finite A] : Subgroup A :=
  (⊤ : Subgroup A).lowerCentralSeries (Nat.card A)

/-- `A^∞ = ⁅A^∞, ⊤⁆` (lcs の stable 性質の右作用形). -/
lemma lowerCentralSeriesInfty_commutator_top [Finite A] :
    ⁅lowerCentralSeriesInfty A, (⊤ : Subgroup A)⁆ = lowerCentralSeriesInfty A := by
  unfold lowerCentralSeriesInfty
  exact (lowerCentralSeries_card_eq_succ_card (A := A)).symm

/-- `A^∞ = ⁅⊤, A^∞⁆` (lcs の stable 性質の左作用形, `commutator_comm` 経由). -/
lemma commutator_top_lowerCentralSeriesInfty [Finite A] :
    ⁅(⊤ : Subgroup A), lowerCentralSeriesInfty A⁆ = lowerCentralSeriesInfty A := by
  rw [Subgroup.commutator_comm]
  exact lowerCentralSeriesInfty_commutator_top

end /- §4C (続) -/

/-! ### §4C Thm 4.24 Phase 2: helpers for the main theorem -/

section /- §4C (続 II): Thm 4.24 main theorem -/

variable {A : Type*} [Group A]

/-! #### iterated commutators with `A^∞` and the chain hypothesis -/

/-- **Subgroup-valued iterated right commutator with a fixed subgroup**:
`iterRightCommutator K m = ⁅...⁅K, F⁆, F⁆...⁆`. Specialisation of `iterCommutator`
where we vary the left operand but keep the right operand fixed, used in the
"sequence terminating at 1" step of Thm 4.24.

This is definitionally `iterCommutator K F m`, but the explicit name aids
readability around `Nat.find` of "last nontrivial in chain". -/
private noncomputable def iterRightCommutator
    (K F : Subgroup G) (m : ℕ) : Subgroup G :=
  iterCommutator K F m

private lemma iterRightCommutator_zero (K F : Subgroup G) :
    iterRightCommutator K F 0 = K := rfl

private lemma iterRightCommutator_succ (K F : Subgroup G) (m : ℕ) :
    iterRightCommutator K F (m + 1) = ⁅iterRightCommutator K F m, F⁆ := rfl

/-- **Monotonicity in the left operand**: if `K ≤ K'`, then `iterRightCommutator K F m ≤ iterRightCommutator K' F m`. -/
private lemma iterRightCommutator_mono_left
    {K K' F : Subgroup G} (h : K ≤ K') (m : ℕ) :
    iterRightCommutator K F m ≤ iterRightCommutator K' F m := by
  induction m with
  | zero => simpa [iterRightCommutator_zero] using h
  | succ m ih =>
      rw [iterRightCommutator_succ, iterRightCommutator_succ]
      exact Subgroup.commutator_mono ih le_rfl

/-- **iterRightCommutator with shifted base**: `iterRightCommutator (iter K F j) F k = iter K F (j + k)`. -/
private lemma iterRightCommutator_add (K F : Subgroup G) (j k : ℕ) :
    iterRightCommutator (iterRightCommutator K F j) F k = iterRightCommutator K F (j + k) := by
  induction k with
  | zero => simp [iterRightCommutator_zero]
  | succ k ih =>
      rw [iterRightCommutator_succ, ih]
      rw [show j + (k + 1) = (j + k) + 1 from by omega, iterRightCommutator_succ]

/-! #### Restriction of the action to `A^∞ ≤ A` -/

/-- The composed hom `lowerCentralSeriesInfty A →* MulAut G` obtained by restricting `φ`. -/
private noncomputable def phiInfty {A G : Type*} [Group A] [Group G] [Finite A]
    (φ : A →* MulAut G) :
    (lowerCentralSeriesInfty A) →* MulAut G :=
  φ.comp (lowerCentralSeriesInfty A).subtype

/-- **A^∞ の作用 commutator** = `⁅G, A^∞⁆` (内部記法). Subgroup-typed. -/
private noncomputable def actionCommutatorInfty {A G : Type*} [Group A] [Group G] [Finite A]
    (φ : A →* MulAut G) : Subgroup G :=
  actionCommutator (phiInfty φ)

/-- `[G, A^∞] ≤ [G, A]` (作用 commutator は acting group の制限で縮む). -/
private lemma actionCommutatorInfty_le_actionCommutator
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G) :
    actionCommutatorInfty φ ≤ actionCommutator φ :=
  actionCommutator_comp_le φ _

/-- `[G, A^∞]` is normal in G (inherited from `actionCommutator.normal`). -/
private instance actionCommutatorInfty_normal
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G) :
    (actionCommutatorInfty φ).Normal :=
  actionCommutator.normal (phiInfty φ)

/-- `[G, A^∞]` is A-invariant (it is the image of an action commutator restricted to A^∞,
which is itself characteristic in A, but more importantly, `(φ a) g * g⁻¹` for `a ∈ A^∞`
is permuted under the broader A-action). -/
private lemma actionCommutatorInfty_isAInvariant
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutatorInfty φ) := by
  -- Strategy: actionCommutatorInfty φ = ⁅⊤, lowerCentralSeriesInfty⁆ "viewed in G" via the action.
  -- Use the fact that the generating set
  -- {g * (φ a) g⁻¹ : g ∈ G, a ∈ A^∞}
  -- is invariant under φ b for b ∈ A: (φ b) (g * (φ a) g⁻¹) = (φ b) g * (φ (b * a * b⁻¹)) ((φ b) g)⁻¹,
  -- and b * a * b⁻¹ ∈ A^∞ because A^∞ is characteristic (hence normal) in A.
  apply OddOrder.Isaacs.Ch03.IsAInvariant.closure_of_invariant_set
  intro b
  -- Generator: x = g * (phiInfty φ) ⟨a, ha⟩ g⁻¹ with ⟨a, ha⟩ : A^∞. Equivalently g * (φ a) g⁻¹.
  have h_norm : (lowerCentralSeriesInfty A).Normal := by
    unfold lowerCentralSeriesInfty
    exact ((⊤ : Subgroup A).lowerCentralSeries (Nat.card A)).normal_of_characteristic
  have key : ∀ g : G, ∀ a : lowerCentralSeriesInfty A,
      (φ b) (g * (phiInfty φ) a g⁻¹) =
        (φ b) g * (phiInfty φ) ⟨b * a.val * b⁻¹, h_norm.conj_mem _ a.property _⟩
          ((φ b) g)⁻¹ := by
    intro g a
    change (φ b) (g * (φ a.val) g⁻¹) = (φ b) g * (φ (b * a.val * b⁻¹)) ((φ b) g)⁻¹
    rw [map_mul (φ b)]
    congr 1
    rw [show ((φ b) g)⁻¹ = (φ b) g⁻¹ from (map_inv (φ b) g).symm,
        show φ (b * a.val * b⁻¹) = (φ b) * (φ a.val) * (φ b)⁻¹ from by
          rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    refine ⟨(φ b) g, ⟨b * a.val * b⁻¹, h_norm.conj_mem _ a.property _⟩, ?_⟩
    exact key g a
  · rintro ⟨g, a, rfl⟩
    refine ⟨(φ b)⁻¹ g * (phiInfty φ)
        ⟨b⁻¹ * a.val * b, by
          have := h_norm.conj_mem _ a.property b⁻¹
          simpa [mul_assoc] using this⟩
        ((φ b)⁻¹ g)⁻¹,
      ⟨(φ b)⁻¹ g, _, rfl⟩, ?_⟩
    change (φ b) ((φ b)⁻¹ g * (φ (b⁻¹ * a.val * b)) ((φ b)⁻¹ g)⁻¹) =
        g * (φ a.val) g⁻¹
    rw [map_mul (φ b)]
    congr 1
    · exact MulAut.apply_inv_self (M := G) (φ b) g
    rw [show ((φ b)⁻¹ g)⁻¹ = (φ b)⁻¹ g⁻¹ from (map_inv ((φ b)⁻¹) g).symm,
        show φ (b⁻¹ * a.val * b) = (φ b)⁻¹ * (φ a.val) * (φ b) from by
          rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self,
        MulAut.apply_inv_self]

/-- **Chain hypothesis descends to `A^∞`**: if `iterCommutator inl(G).range inr(A).range m = ⊥`
then `iterCommutator inl(G).range inr(A^∞).range m = ⊥` (acting via `phiInfty`).

Proof: `lowerCentralSeriesInfty A ≤ A` (as subgroup), and the chain hypothesis restricts. -/
private lemma iterCommutator_inl_inr_lowerCentralSeriesInfty_eq_bot
    {A G : Type*} [Group A] [Group G] [Finite A] {φ : A →* MulAut G} {m : ℕ}
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    iterCommutator
        (SemidirectProduct.inl : G →* G ⋊[phiInfty φ] (lowerCentralSeriesInfty A)).range
        (SemidirectProduct.inr : (lowerCentralSeriesInfty A) →*
            G ⋊[phiInfty φ] (lowerCentralSeriesInfty A)).range m = ⊥ :=
  iterCommutator_inl_inr_restrict_eq_bot (φ := φ) (lowerCentralSeriesInfty A) h_iter

/-! #### Fixed-point subgroup `C := [G, A^∞] ∩ C_G(A)` and its properties -/

/-- **Fixed-point subgroup**: `C := actionCommutatorInfty φ ⊓ fixedPointsOfMulAut φ`.

This is the subgroup of `[G, A^∞]` consisting of elements fixed by the entire `A`-action.
Used in the inductive step of Thm 4.24 as the kernel we factor out. -/
private noncomputable def actionCommutatorInfty_fix
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G) : Subgroup G :=
  actionCommutatorInfty φ ⊓ Subgroup.fixedPointsOfMulAut φ

/-- `C` is A-invariant. (Intersection of two A-invariant subgroups.) -/
private lemma actionCommutatorInfty_fix_isAInvariant
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutatorInfty_fix φ) := by
  refine OddOrder.Isaacs.Ch03.IsAInvariant.inf (actionCommutatorInfty_isAInvariant φ) ?_
  -- fixedPointsOfMulAut φ is A-invariant: it is a characteristic-like subgroup w.r.t. A
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro b g hg
  rw [Subgroup.mem_fixedPointsOfMulAut] at hg ⊢
  intro a
  -- Goal: (φ a) ((φ b) g) = (φ b) g.
  -- Use: (φ a) ((φ b) g) = (φ (a * b)) g = (φ b) ((φ (b⁻¹ * a * b)) g) by composing,
  -- and (φ (b⁻¹ * a * b)) g = g since g is fixed by every element of A.
  have h_eq : (φ a) ((φ b) g) = (φ b) ((φ (b⁻¹ * a * b)) g) := by
    rw [show φ (b⁻¹ * a * b) = (φ b)⁻¹ * (φ a) * (φ b) from by
        rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
  rw [h_eq, hg (b⁻¹ * a * b)]

/-! #### Lemma: `K = [G, A^∞]` centralizes `[G, A]` (three-subgroups in Γ)

Given the hypothesis that `A^∞` acts trivially on `[G, A]` (= IH applied to `[G, A]`),
we derive that `[G, A^∞]` centralizes `[G, A]`, using a three-subgroups argument in Γ. -/

/-- The hypothesis "A^∞ acts trivially on `[G, A]`" translated into a Γ-side commutator
identity: `⁅inl([G, A]), inr(A^∞)⁆ = ⊥` in Γ. -/
private lemma commutator_inl_GA_inr_Ainf_eq_bot_of_centralized
    {A G : Type*} [Group A] [Group G] [Finite A] {φ : A →* MulAut G}
    (h : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ)) :
    ⁅(actionCommutator φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A),
      (lowerCentralSeriesInfty A).map (SemidirectProduct.inr : A →* G ⋊[φ] A)⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  rintro _ ⟨k, hk, rfl⟩ _ ⟨a, ha, rfl⟩
  -- Goal: ⁅inl k, inr a⁆ ∈ ⊥
  rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
  -- Need: k * (φ a) k⁻¹ = 1 (i.e., (φ a) k = k).
  have h_fix : (φ a) k = k := by
    have hk_fix := h hk
    -- hk_fix : k ∈ fixedPointsOfMulAut (phiInfty φ), i.e., ∀ b : A^∞, (phiInfty φ b) k = k.
    -- phiInfty φ ⟨a, ha⟩ k = (φ a) k by definition. Apply to b := ⟨a, ha⟩.
    have := hk_fix ⟨a, ha⟩
    exact this
  rw [show (φ a) k⁻¹ = ((φ a) k)⁻¹ from map_inv (φ a) k, h_fix, mul_inv_cancel]
  exact map_one _

/-- **K = [G, A^∞] centralizes [G, A]**: given hypothesis (d) "A^∞ acts trivially on [G, A]",
`⁅[G, A^∞], [G, A]⁆ = ⊥` in G.

**Proof**: Three-subgroups in Γ = G ⋊[φ] A with H_1 = inr(A^∞) (lowerCentralSeriesInfty A
mapped via inr), H_2 = inl(G).range, H_3 = inl([G, A]) = ⁅XG, YA⁆ (= GA_inl):
- `⁅H_2, H_3, H_1⁆ ≤ ⁅H_3, H_1⁆ = ⁅GA_inl, H_1⁆ = ⊥` (hypothesis (d) via Γ-form).
  Wait: `⁅H_3, H_1⁆ = ⁅GA_inl, inr(A^∞)⁆` and we have hypothesis as
  `⁅GA_inl, inr(A^∞)⁆ = ⊥`, hence `⁅H_2, H_3, H_1⁆ ≤ ⁅⊤, ⊥⁆ = ⊥`... no, that's wrong.
- Actually, `⁅H_2, H_3, H_1⁆ = ⁅⁅H_2, H_3⁆, H_1⁆`. We need to bound `⁅H_2, H_3⁆`.
  Since `GA_inl ⊴ Γ` (using inl ⊔ inr = ⊤), `⁅XG, GA_inl⁆ ≤ GA_inl`.
  So `⁅H_2, H_3⁆ ≤ GA_inl`, hence `⁅⁅H_2, H_3⁆, H_1⁆ ≤ ⁅GA_inl, inr(A^∞)⁆ = ⊥` (hypothesis (d)).
- `⁅H_3, H_1, H_2⁆ = ⁅⁅GA_inl, inr(A^∞)⁆, XG⁆ = ⁅⊥, XG⁆ = ⊥` (hypothesis (d)).
- Three-subgroups (rotate): `⁅⁅H_1, H_2⁆, H_3⁆ = ⊥`.
- `⁅H_1, H_2⁆ = ⁅inr(A^∞), inl(G)⁆ = (commutator_comm) = ⁅inl(G), inr(A^∞)⁆
  = inl([G, A^∞]) = inl(K)`.
- So `⁅inl(K), GA_inl⁆ = ⁅inl(K), inl([G, A])⁆ = inl(⁅K, [G, A]⁆) = ⊥`.
- By inl_injective, `⁅K, [G, A]⁆ = ⊥` in G. -/
private theorem commutator_actionCommutatorInfty_actionCommutator_eq_bot
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G)
    (h : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ)) :
    ⁅actionCommutatorInfty φ, actionCommutator φ⁆ = ⊥ := by
  -- Set up
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YinfA : Subgroup (G ⋊[φ] A) :=
    (lowerCentralSeriesInfty A).map (SemidirectProduct.inr : A →* G ⋊[φ] A)
  set GA_inl : Subgroup (G ⋊[φ] A) :=
    (actionCommutator φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A) with hGA_inl
  -- GA_inl = ⁅XG, inr(A).range⁆ (from actionCommutator_map_inl)
  have hGA_inl_eq : GA_inl = ⁅XG, (SemidirectProduct.inr : A →* G ⋊[φ] A).range⁆ :=
    actionCommutator_map_inl φ
  -- Hypothesis (d): ⁅GA_inl, YinfA⁆ = ⊥
  have hd_gamma : ⁅GA_inl, YinfA⁆ = ⊥ :=
    commutator_inl_GA_inr_Ainf_eq_bot_of_centralized h
  -- GA_inl is normal in Γ (it = ⁅XG, YA⁆ with XG ⊔ inr(A) = ⊤).
  haveI hGA_norm : GA_inl.Normal := by
    rw [hGA_inl_eq]
    exact commutator_normal_of_sup_eq_top
      SemidirectProduct.inl_range_sup_inr_range_eq_top
  -- ⁅XG, GA_inl⁆ ≤ GA_inl (left commutator inclusion since GA_inl normal)
  have h_inner : ⁅XG, GA_inl⁆ ≤ GA_inl := Subgroup.commutator_le_right XG GA_inl
  -- ⁅⁅XG, GA_inl⁆, YinfA⁆ ≤ ⁅GA_inl, YinfA⁆ = ⊥
  have h_three_b : ⁅⁅XG, GA_inl⁆, YinfA⁆ = ⊥ :=
    le_bot_iff.mp <| le_trans (Subgroup.commutator_mono h_inner le_rfl) hd_gamma.le
  -- ⁅⁅GA_inl, YinfA⁆, XG⁆ = ⊥ from hd_gamma
  have h_three_a : ⁅⁅GA_inl, YinfA⁆, XG⁆ = ⊥ := by
    rw [hd_gamma, Subgroup.commutator_bot_left]
  -- Apply Subgroup.commutator_commutator_eq_bot_of_rotate
  -- with H_1 := YinfA, H_2 := XG, H_3 := GA_inl:
  -- - input1: ⁅⁅H_2, H_3⁆, H_1⁆ = ⁅⁅XG, GA_inl⁆, YinfA⁆ = h_three_b
  -- - input2: ⁅⁅H_3, H_1⁆, H_2⁆ = ⁅⁅GA_inl, YinfA⁆, XG⁆ = h_three_a
  -- - output: ⁅⁅H_1, H_2⁆, H_3⁆ = ⁅⁅YinfA, XG⁆, GA_inl⁆ = ⊥
  have h_three : ⁅⁅YinfA, XG⁆, GA_inl⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h_three_b h_three_a
  -- ⁅YinfA, XG⁆ = (actionCommutatorInfty φ).map inl
  have h_YinfA_XG_eq : ⁅YinfA, XG⁆ =
      (actionCommutatorInfty φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A) := by
    -- ⁅YinfA, XG⁆ = ⁅XG, YinfA⁆ (commutator_comm).
    -- ⁅XG, YinfA⁆ = ⁅XG, inr(A^∞ via subtype).range⁆ via image of range.
    -- And this equals (actionCommutator (φ.comp subtype)).map inl
    -- = actionCommutatorInfty.map inl (by definition).
    have h_eq_range : YinfA =
        ((SemidirectProduct.inr : A →* G ⋊[φ] A).comp
          (lowerCentralSeriesInfty A).subtype).range := by
      rw [MonoidHom.range_comp]
      change (lowerCentralSeriesInfty A).map (SemidirectProduct.inr : A →* G ⋊[φ] A) =
        ((lowerCentralSeriesInfty A).subtype.range).map _
      rw [Subgroup.range_subtype]
    rw [Subgroup.commutator_comm, h_eq_range]
    have := actionCommutator_map_inl_comp φ (lowerCentralSeriesInfty A).subtype
    -- this : (actionCommutator (φ.comp ((lowerCentralSeriesInfty A).subtype))).map inl =
    --        ⁅XG, ((SemidirectProduct.inr).comp (lowerCentralSeriesInfty A).subtype).range⁆
    -- We want LHS = (actionCommutatorInfty φ).map inl, which is the same since
    -- actionCommutatorInfty φ := actionCommutator (phiInfty φ) := actionCommutator (φ.comp subtype).
    exact this.symm
  rw [h_YinfA_XG_eq, hGA_inl, ← Subgroup.map_commutator] at h_three
  exact (Subgroup.map_eq_bot_iff_of_injective _ SemidirectProduct.inl_injective).mp h_three

/-- **`[K, [G, A]] = ⊥` ⇒ `[[G, A], C] = ⊥`** (since C ≤ K). Just commutator monotonicity. -/
private lemma commutator_actionCommutator_actionCommutatorInfty_fix_eq_bot
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G)
    (h : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ)) :
    ⁅actionCommutator φ, actionCommutatorInfty_fix φ⁆ = ⊥ := by
  have h_main := commutator_actionCommutatorInfty_actionCommutator_eq_bot φ h
  have h_C_le : actionCommutatorInfty_fix φ ≤ actionCommutatorInfty φ := inf_le_left
  -- Goal: ⁅actionCommutator φ, actionCommutatorInfty_fix φ⁆ = ⊥
  rw [Subgroup.commutator_comm]
  exact le_bot_iff.mp <|
    le_trans (Subgroup.commutator_mono h_C_le le_rfl) h_main.le

/-! #### C ⊴ G (Step 6 of Isaacs Thm 4.24)

We now show `actionCommutatorInfty_fix φ` is normal in G via:
(I) `[C, G] ≤ [G, A^∞]` (since C ≤ K and K is normal in G).
(II) `[C, G] ≤ fixedPointsOfMulAut φ` (three-subgroups in Γ with H_1 = inl(G), H_2 = inr(A),
H_3 = inl(C)). -/

/-- **A centralizes [C, G] (in Γ-form): `⁅⁅XG, inl(C)⁆, inr(A)⁆ = ⊥`**.

**Proof**: Three-subgroups in Γ with H_1 = XG, H_2 = inr(A), H_3 = inl(C):
- `⁅H_1, H_2, H_3⁆ = ⁅⁅XG, inr(A)⁆, inl(C)⁆ = ⁅GA_inl, inl(C)⁆ = inl(⁅[G, A], C⁆) = ⊥`
  (from `commutator_actionCommutator_actionCommutatorInfty_fix_eq_bot`).
- `⁅H_2, H_3, H_1⁆ = ⁅⁅inr(A), inl(C)⁆, XG⁆ = ⁅⊥, XG⁆ = ⊥` (A centralizes C ⇒ ⁅inr(A), inl(C)⁆ = ⊥).
- Three-subgroups rotate: `⁅⁅H_3, H_1⁆, H_2⁆ = ⁅⁅inl(C), XG⁆, inr(A)⁆ = ⊥`. -/
private theorem commutator_inl_C_XG_inr_A_eq_bot_of_centralized
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G)
    (h : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ)) :
    ⁅⁅(actionCommutatorInfty_fix φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A),
        (SemidirectProduct.inl : G →* G ⋊[φ] A).range⁆,
      (SemidirectProduct.inr : A →* G ⋊[φ] A).range⁆ = ⊥ := by
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  set Cinl : Subgroup (G ⋊[φ] A) :=
    (actionCommutatorInfty_fix φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A)
  -- Part A: ⁅YA, Cinl⁆ = ⊥ (A centralizes C in G)
  have h_AC_bot : ⁅YA, Cinl⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨a, rfl⟩ _ ⟨c, hc, rfl⟩
    obtain ⟨_, hc_fix⟩ := Subgroup.mem_inf.mp hc
    have h_fix : (φ a) c = c := hc_fix a
    -- Goal: ⁅inr a, inl c⁆ ∈ ⊥
    rw [Subgroup.mem_bot]
    -- Compute ⁅inr a, inl c⁆ = (inr a) * (inl c) * (inr a)⁻¹ * (inl c)⁻¹
    -- = inl ((φ a) c) * inr a * (inr a)⁻¹ * (inl c)⁻¹  (by inl_aut)
    -- = inl c * (inl c)⁻¹ = 1
    have hi := SemidirectProduct.inl_aut (φ := φ) a c
    -- hi : inl ((φ a) c) = inr a * inl c * inr a⁻¹
    change (SemidirectProduct.inr a : G ⋊[φ] A) * SemidirectProduct.inl c *
        (SemidirectProduct.inr a)⁻¹ * (SemidirectProduct.inl c)⁻¹ = 1
    rw [show ((SemidirectProduct.inr a : G ⋊[φ] A))⁻¹ = SemidirectProduct.inr a⁻¹ from
        (map_inv _ _).symm, ← hi, h_fix]
    group
  -- Part B: ⁅⁅XG, YA⁆, Cinl⁆ = ⊥
  -- Use commutator_actionCommutator_actionCommutatorInfty_fix_eq_bot and bridge.
  have h_actY_eq : ⁅XG, YA⁆ = (actionCommutator φ).map SemidirectProduct.inl :=
    (actionCommutator_map_inl φ).symm
  have h_C_actCom : ⁅(actionCommutator φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A),
      Cinl⁆ = ⊥ := by
    -- = (⁅actionCommutator φ, actionCommutatorInfty_fix φ⁆).map inl = ⊥.map inl
    rw [← Subgroup.map_commutator,
        commutator_actionCommutator_actionCommutatorInfty_fix_eq_bot φ h]
    simp
  have h_XY_C_bot : ⁅⁅XG, YA⁆, Cinl⁆ = ⊥ := by
    rw [h_actY_eq]; exact h_C_actCom
  -- Apply three-subgroups (rotate) with H_1 = XG, H_2 = YA, H_3 = Cinl:
  -- - input1: ⁅⁅H_2, H_3⁆, H_1⁆ = ⁅⁅YA, Cinl⁆, XG⁆ = ⁅⊥, XG⁆ = ⊥
  -- - input2: ⁅⁅H_3, H_1⁆, H_2⁆ = ⁅⁅Cinl, XG⁆, YA⁆ — wait, this is what we want.
  -- We need to swap. Three-subgroups: given ⁅⁅H_2, H_3⁆, H_1⁆ + ⁅⁅H_3, H_1⁆, H_2⁆ ⇒
  -- ⁅⁅H_1, H_2⁆, H_3⁆.
  -- We have ⁅⁅XG, YA⁆, Cinl⁆ = ⊥ which is ⁅⁅H_1, H_2⁆, H_3⁆. (output of rotate)
  -- And ⁅⁅YA, Cinl⁆, XG⁆ = ⊥ which is ⁅⁅H_2, H_3⁆, H_1⁆. (input1)
  -- We want ⁅⁅Cinl, XG⁆, YA⁆ = ⁅⁅H_3, H_1⁆, H_2⁆. (input2)
  -- Three-subgroups can derive any one from the other two.
  have h_input1 : ⁅⁅YA, Cinl⁆, XG⁆ = ⊥ := by
    rw [h_AC_bot, Subgroup.commutator_bot_left]
  -- The rotate lemma gives ⁅⁅H_1, H_2⁆, H_3⁆ from ⁅⁅H_2, H_3⁆, H_1⁆ + ⁅⁅H_3, H_1⁆, H_2⁆.
  -- Apply with H_1' = YA, H_2' = Cinl, H_3' = XG:
  -- gives ⁅⁅YA, Cinl⁆, XG⁆ from ⁅⁅Cinl, XG⁆, YA⁆ + ⁅⁅XG, YA⁆, Cinl⁆.
  -- We want the inverse direction. Let's use:
  -- H_1' = Cinl, H_2' = XG, H_3' = YA:
  -- ⁅⁅H_2', H_3'⁆, H_1'⁆ = ⁅⁅XG, YA⁆, Cinl⁆ = ⊥ (h_XY_C_bot)
  -- ⁅⁅H_3', H_1'⁆, H_2'⁆ = ⁅⁅YA, Cinl⁆, XG⁆ = ⊥ (h_input1)
  -- ⇒ ⁅⁅H_1', H_2'⁆, H_3'⁆ = ⁅⁅Cinl, XG⁆, YA⁆ = ⊥.
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h_XY_C_bot h_input1

/-- **[C, G] ⊆ fixedPointsOfMulAut φ**: from the three-subgroups conclusion above. -/
private lemma commutator_actionCommutatorInfty_fix_top_le_fixedPoints
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G)
    (h : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ)) :
    ⁅actionCommutatorInfty_fix φ, (⊤ : Subgroup G)⁆ ≤ Subgroup.fixedPointsOfMulAut φ := by
  have h_three := commutator_inl_C_XG_inr_A_eq_bot_of_centralized φ h
  -- We want: ∀ x ∈ ⁅C, ⊤⁆, ∀ a, (φ a) x = x.
  intro x hx
  rw [Subgroup.mem_fixedPointsOfMulAut]
  intro a'
  -- Use h_three: ⁅⁅inl(C), XG⁆, inr(A).range⁆ = ⊥, so for x ∈ ⁅C, ⊤⁆ (mapped under inl)
  -- and any a', ⁅inl x, inr a'⁆ = 1 in Γ.
  -- inl(⁅C, ⊤⁆) = ⁅inl(C), inl(⊤)⁆ = ⁅inl(C), XG⁆.
  have h_x_inl_mem : (SemidirectProduct.inl x : G ⋊[φ] A) ∈
      ⁅(actionCommutatorInfty_fix φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A),
        (SemidirectProduct.inl : G →* G ⋊[φ] A).range⁆ := by
    have h_map : ⁅(actionCommutatorInfty_fix φ).map
          (SemidirectProduct.inl : G →* G ⋊[φ] A),
        (SemidirectProduct.inl : G →* G ⋊[φ] A).range⁆ =
        ⁅actionCommutatorInfty_fix φ, (⊤ : Subgroup G)⁆.map SemidirectProduct.inl := by
      rw [MonoidHom.range_eq_map (SemidirectProduct.inl : G →* G ⋊[φ] A),
          ← Subgroup.map_commutator]
    rw [h_map]
    exact ⟨x, hx, rfl⟩
  -- Now ⁅inl x, inr a'⁆ ∈ ⁅⁅inl(C), XG⁆, inr(A).range⁆ = ⊥
  have h_x_a_bot : ⁅(SemidirectProduct.inl x : G ⋊[φ] A),
      (SemidirectProduct.inr a' : G ⋊[φ] A)⁆ = (1 : G ⋊[φ] A) := by
    have h_mem : ⁅(SemidirectProduct.inl x : G ⋊[φ] A),
        (SemidirectProduct.inr a' : G ⋊[φ] A)⁆ ∈
        (⊥ : Subgroup (G ⋊[φ] A)) := by
      rw [← h_three]
      exact Subgroup.commutator_mem_commutator h_x_inl_mem ⟨a', rfl⟩
    exact Subgroup.mem_bot.mp h_mem
  -- ⁅inl x, inr a'⁆ = inl(x * (φ a') x⁻¹). So inl(x * (φ a') x⁻¹) = 1, hence x * (φ a') x⁻¹ = 1.
  rw [SemidirectProduct.commutator_inl_inr] at h_x_a_bot
  have h_in_G : x * (φ a') x⁻¹ = 1 :=
    SemidirectProduct.inl_injective (by rw [h_x_a_bot]; exact (map_one _).symm)
  -- x * (φ a') x⁻¹ = 1 ⇒ (φ a') x⁻¹ = x⁻¹ ⇒ ((φ a') x)⁻¹ = x⁻¹ ⇒ (φ a') x = x.
  have h_aux : (φ a') x⁻¹ = x⁻¹ := by
    have := h_in_G
    have := mul_left_cancel (a := x) (b := (φ a') x⁻¹) (c := x⁻¹)
      (by rw [this, mul_inv_cancel])
    exact this
  rw [map_inv] at h_aux
  exact (inv_injective h_aux)

/-! #### Normality and nontriviality of C in G -/

/-- **`C ⊴ G`** (Step 6 conclusion of Isaacs Thm 4.24):
combining `⁅C, ⊤⁆ ≤ [G, A^∞]` (since `C ≤ [G, A^∞]` and `[G, A^∞]` is G-normal) with
`⁅C, ⊤⁆ ≤ fixedPointsOfMulAut φ` (from
`commutator_actionCommutatorInfty_fix_top_le_fixedPoints`) yields `⁅C, ⊤⁆ ≤ C`, hence
`C` is normal in `G` by `Subgroup.commutator_top_right_le_iff`. -/
private lemma actionCommutatorInfty_fix_normal_of_centralized
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G)
    (h : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ)) :
    (actionCommutatorInfty_fix φ).Normal := by
  rw [← Subgroup.commutator_top_right_le_iff]
  refine le_inf ?_ (commutator_actionCommutatorInfty_fix_top_le_fixedPoints φ h)
  haveI : (actionCommutatorInfty φ).Normal := actionCommutatorInfty_normal φ
  calc ⁅actionCommutatorInfty_fix φ, (⊤ : Subgroup G)⁆
      ≤ ⁅actionCommutatorInfty φ, (⊤ : Subgroup G)⁆ :=
        Subgroup.commutator_mono inf_le_left le_rfl
    _ ≤ actionCommutatorInfty φ :=
        Subgroup.commutator_le_left _ _

/-! #### Phase 2D-2: nontriviality of C -/

/-- **`iterCommutator` monotonicity in the left operand**: if `K₁ ≤ K₂`, then
`iter K₁ F m ≤ iter K₂ F m`. -/
private lemma iterCommutator_mono_left {G : Type*} [Group G]
    {K₁ K₂ F : Subgroup G} (h : K₁ ≤ K₂) (m : ℕ) :
    iterCommutator K₁ F m ≤ iterCommutator K₂ F m := by
  induction m with
  | zero => simpa [iterCommutator_zero] using h
  | succ m ih =>
      rw [iterCommutator_succ, iterCommutator_succ]
      exact Subgroup.commutator_mono ih le_rfl

/-- **`C ≠ ⊥` when `[G, A^∞] ≠ ⊥`**: if `actionCommutatorInfty φ ≠ ⊥`, then there is a
nontrivial `A`-fixed subgroup of `G` contained in `[G, A^∞]`.

**Strategy** (in Γ = G ⋊[φ] A): set `K_inl := (actionCommutatorInfty φ).map inl ≠ ⊥`
(injectivity of `inl`). Consider the chain `f k := iterCommutator K_inl inr(A).range k`.
- `f 0 = K_inl ≠ ⊥`.
- `f m = ⊥` because `K_inl ≤ inl(G).range = iter inl(G).range inr(A).range 0`, hence
  `f k ≤ iter inl(G).range inr(A).range k`, and the chain hypothesis gives `f m = ⊥`.
- Let `k₀ := Nat.find` of the smallest `k` with `f k = ⊥`. Then `k₀ ≥ 1` and `f (k₀ - 1) ≠ ⊥`
  but `⁅f (k₀ - 1), inr(A).range⁆ = f k₀ = ⊥`.
- `f (k₀ - 1) ≤ inl(G).range` (induction: `K_inl ≤ inl(G).range`, and `inl(G).range` is normal
  in Γ since `actionCommutator_map_inl φ` shows `⁅inl(G).range, inr(A).range⁆ ≤ inl(G).range`
  — actually `inl(G).range` is normal in Γ by `commutator_normal_of_sup_eq_top` applied to
  `⁅inl(G).range, inl(G).range⁆` is trivially in `inl(G).range`; here we use that
  `inl(G).range ⊴ Γ` via `SemidirectProduct.inl_range_normal`).
- Pull `f (k₀ - 1)` back to `L ≤ G` via `inl` (= preimage), so `inl(L) = f (k₀ - 1)`.
- `⁅L, ⊤⁆ = ⊥` and every `l ∈ L` is `A`-fixed (from `f k₀ = ⊥` element-wise).
- `L ≤ actionCommutatorInfty φ` (induction: `f j ≤ K_inl`, but actually we need
  `f j ≤ K_inl` — `f` is decreasing because `K_inl ≤ ?`. Let me use `f (k₀ - 1) ≤ K_inl`
  directly via `iterCommutator_succ_le_self`-style.) -/
private lemma actionCommutatorInfty_fix_ne_bot_of_ne_bot
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G] {φ : A →* MulAut G}
    {m : ℕ}
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥)
    (hK : actionCommutatorInfty φ ≠ ⊥) :
    actionCommutatorInfty_fix φ ≠ ⊥ := by
  classical
  -- Setup in Γ
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range with hXG_def
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range with hYA_def
  set K_inl : Subgroup (G ⋊[φ] A) :=
    (actionCommutatorInfty φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A) with hK_inl_def
  -- f k := iter K_inl YA k
  set f : ℕ → Subgroup (G ⋊[φ] A) := fun k => iterCommutator K_inl YA k with hf_def
  -- K_inl ≠ ⊥
  have hK_inl_ne : K_inl ≠ ⊥ := by
    intro h
    apply hK
    exact (Subgroup.map_eq_bot_iff_of_injective (actionCommutatorInfty φ)
      SemidirectProduct.inl_injective).mp h
  -- K_inl ≤ XG
  have hK_inl_le_XG : K_inl ≤ XG := by
    rintro _ ⟨g, _, rfl⟩
    exact ⟨g, rfl⟩
  -- f k ≤ iter XG YA k for all k
  have hf_le_iter : ∀ k, f k ≤ iterCommutator XG YA k := fun k =>
    iterCommutator_mono_left hK_inl_le_XG k
  -- f m = ⊥
  have hfm_bot : f m = ⊥ := by
    have h := hf_le_iter m
    rw [h_iter] at h
    exact le_bot_iff.mp h
  -- ∃ k, f k = ⊥
  have h_exists : ∃ k, f k = ⊥ := ⟨m, hfm_bot⟩
  -- k₀ := Nat.find
  let k₀ := Nat.find h_exists
  have hk₀_spec : f k₀ = ⊥ := Nat.find_spec h_exists
  have hk₀_min : ∀ j < k₀, f j ≠ ⊥ := fun j hj => Nat.find_min h_exists hj
  -- f 0 = K_inl ≠ ⊥, so k₀ ≥ 1
  have hf0 : f 0 = K_inl := by simp [hf_def, iterCommutator_zero]
  have hk₀_pos : 1 ≤ k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with hzero | hpos
    · exfalso
      have := hk₀_spec
      rw [hzero, hf0] at this
      exact hK_inl_ne this
    · exact hpos
  -- Let k := k₀ - 1
  set k := k₀ - 1 with hk_def
  have hk_succ : k + 1 = k₀ := by omega
  -- f k ≠ ⊥
  have hfk_ne : f k ≠ ⊥ := hk₀_min k (by omega)
  -- f (k+1) = ⊥
  have hfk1_bot : f (k + 1) = ⊥ := by rw [hk_succ]; exact hk₀_spec
  -- ⁅f k, YA⁆ = f (k+1) = ⊥
  have h_comm_fk_YA : ⁅f k, YA⁆ = ⊥ := by
    have : f (k + 1) = ⁅f k, YA⁆ := iterCommutator_succ _ _ _
    rw [← this]
    exact hfk1_bot
  -- f k ≤ XG (induction). XG is normal in Γ, so iter preserves XG-containment.
  haveI hXG_normal : XG.Normal := by
    simp only [hXG_def]
    infer_instance
  have hXG_comm_YA_le : ⁅XG, YA⁆ ≤ XG := Subgroup.commutator_le_left XG YA
  have hfk_le_XG : ∀ j, f j ≤ XG := by
    intro j
    induction j with
    | zero =>
        simp only [hf_def, iterCommutator_zero]
        exact hK_inl_le_XG
    | succ j ih =>
        have ih' : iterCommutator K_inl YA j ≤ XG := by
          simpa [hf_def] using ih
        change iterCommutator K_inl YA (j + 1) ≤ XG
        rw [iterCommutator_succ]
        exact (Subgroup.commutator_mono ih' le_rfl).trans hXG_comm_YA_le
  have hfk_le_XG_now : f k ≤ XG := hfk_le_XG k
  -- f k ≤ K_inl (induction using iter_succ_le for normal K_inl-style)
  -- Actually K_inl may not be normal in Γ. We use a different strategy: extract L ≤ G
  -- with inl L = f k via the fact that f k ≤ XG = inl.range.
  -- Define L : Subgroup G as the preimage of f k under inl.
  let L : Subgroup G := (f k).comap (SemidirectProduct.inl : G →* G ⋊[φ] A)
  have hL_map : L.map (SemidirectProduct.inl : G →* G ⋊[φ] A) = f k := by
    -- map ∘ comap = inf with range; range = XG; f k ≤ XG
    rw [Subgroup.map_comap_eq, hXG_def.symm]
    show XG ⊓ f k = f k
    exact inf_eq_right.mpr hfk_le_XG_now
  have hL_ne_bot : L ≠ ⊥ := by
    intro hL
    apply hfk_ne
    rw [← hL_map, hL, Subgroup.map_bot]
  -- L ≤ actionCommutatorInfty φ: use that f j ≤ K_inl for all j (since K_inl is "stable
  -- enough" — iter K_inl YA j ≤ K_inl needs K_inl to be Normal in Γ. K_inl might not be normal,
  -- but iter K_inl YA j ≤ K_inl.subgroupClosure... Use the fact that
  -- iter K_inl YA j ⊆ (closure (K_inl ∪ YA)) — no, that's not what we want.
  --
  -- Alternative: K_inl is normal in XG (since XG ≅ G via inl, and actionCommutatorInfty φ
  -- is normal in G). So XG-conjugation preserves K_inl. But YA conjugation might not.
  -- However, the iter chain is built by commutators with YA. We claim:
  -- iter K_inl YA j ⊆ K_inl (within XG). Proof: induction. iter K_inl YA (j+1) =
  -- ⁅iter K_inl YA j, YA⁆. iter K_inl YA j ⊆ K_inl ⊆ XG (by IH and inl-image normality).
  -- ⁅K_inl, YA⁆ = ?. Compute generators: ⁅inl k, inr a⁆ = inl(k * (φ a) k⁻¹). k ∈ acInfty
  -- which is A-invariant via phiInfty, so (φ a) k... wait we need this for general a ∈ A,
  -- not just a ∈ A^∞. But acInfty is A-invariant (Phase 2A `actionCommutatorInfty_isAInvariant`)!
  -- So (φ a) k ∈ acInfty, so k * (φ a) k⁻¹ ∈ acInfty (closed under product/inv).
  -- Therefore ⁅K_inl, YA⁆ ⊆ K_inl.
  have hKinl_YA_le_Kinl : ⁅K_inl, YA⁆ ≤ K_inl := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨g, hg, rfl⟩ _ ⟨a, rfl⟩
    -- Goal: ⁅inl g, inr a⁆ ∈ K_inl. ⁅inl g, inr a⁆ = inl (g * (φ a) g⁻¹).
    rw [SemidirectProduct.commutator_inl_inr]
    -- Need: g * (φ a) g⁻¹ ∈ actionCommutatorInfty φ.
    have h_inv := OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem.mp
      (actionCommutatorInfty_isAInvariant φ)
    -- (φ a) g ∈ actionCommutatorInfty φ
    have h_phi_g : (φ a) g ∈ actionCommutatorInfty φ := h_inv a g hg
    -- g * (φ a) g⁻¹ ∈ actionCommutatorInfty φ
    have h_phi_g_inv : (φ a) g⁻¹ = ((φ a) g)⁻¹ := map_inv (φ a) g
    rw [h_phi_g_inv]
    exact ⟨g * ((φ a) g)⁻¹,
      (actionCommutatorInfty φ).mul_mem hg ((actionCommutatorInfty φ).inv_mem h_phi_g),
      rfl⟩
  have hfk_le_Kinl : ∀ j, f j ≤ K_inl := by
    intro j
    induction j with
    | zero => simp [hf_def, iterCommutator_zero]
    | succ j ih =>
        have ih' : iterCommutator K_inl YA j ≤ K_inl := by
          simpa [hf_def] using ih
        change iterCommutator K_inl YA (j + 1) ≤ K_inl
        rw [iterCommutator_succ]
        exact (Subgroup.commutator_mono ih' le_rfl).trans hKinl_YA_le_Kinl
  -- L ≤ actionCommutatorInfty φ: take l ∈ L, then inl l ∈ f k ≤ K_inl = inl(acInfty),
  -- so by inl_injective, l ∈ acInfty.
  have hL_le_acInfty : L ≤ actionCommutatorInfty φ := by
    intro l hl
    have hinl : (SemidirectProduct.inl l : G ⋊[φ] A) ∈ f k := hl
    have hinl_Kinl : (SemidirectProduct.inl l : G ⋊[φ] A) ∈ K_inl := hfk_le_Kinl k hinl
    obtain ⟨l', hl', heq⟩ := hinl_Kinl
    have : l = l' := SemidirectProduct.inl_injective heq.symm
    rw [this]
    exact hl'
  -- L ≤ fixedPointsOfMulAut φ: from ⁅f k, YA⁆ = ⊥, take l ∈ L, then for any a,
  -- ⁅inl l, inr a⁆ = 1. Since ⁅inl l, inr a⁆ = inl(l * (φ a) l⁻¹), inl_injective
  -- gives l * (φ a) l⁻¹ = 1, hence (φ a) l = l.
  have hL_le_fix : L ≤ Subgroup.fixedPointsOfMulAut φ := by
    intro l hl
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    -- inl l ∈ f k
    have hinl : (SemidirectProduct.inl l : G ⋊[φ] A) ∈ f k := hl
    -- ⁅inl l, inr a⁆ ∈ ⁅f k, YA⁆ = ⊥
    have h_comm_mem : ⁅(SemidirectProduct.inl l : G ⋊[φ] A),
        (SemidirectProduct.inr a : G ⋊[φ] A)⁆ ∈ (⁅f k, YA⁆ : Subgroup (G ⋊[φ] A)) :=
      Subgroup.commutator_mem_commutator hinl ⟨a, rfl⟩
    rw [h_comm_fk_YA, Subgroup.mem_bot] at h_comm_mem
    -- ⁅inl l, inr a⁆ = inl (l * (φ a) l⁻¹) = 1
    rw [SemidirectProduct.commutator_inl_inr] at h_comm_mem
    -- l * (φ a) l⁻¹ = 1 in G
    have h_one_G : l * (φ a) l⁻¹ = 1 := by
      have := h_comm_mem
      have h_inl_one : (SemidirectProduct.inl (1 : G) : G ⋊[φ] A) = 1 := map_one _
      have := this.trans h_inl_one.symm
      exact SemidirectProduct.inl_injective this
    -- (φ a) l⁻¹ = l⁻¹, so (φ a) l = l
    have h_aux : (φ a) l⁻¹ = l⁻¹ :=
      mul_left_cancel (a := l) (b := (φ a) l⁻¹) (c := l⁻¹)
        (by rw [h_one_G, mul_inv_cancel])
    rw [map_inv] at h_aux
    exact inv_injective h_aux
  -- L ≤ actionCommutatorInfty_fix φ = actionCommutatorInfty φ ⊓ fixedPointsOfMulAut φ
  have hL_le_C : L ≤ actionCommutatorInfty_fix φ := le_inf hL_le_acInfty hL_le_fix
  -- L ≠ ⊥, hence C ≠ ⊥
  intro hC_bot
  apply hL_ne_bot
  exact le_bot_iff.mp (hL_le_C.trans hC_bot.le)

/-! #### Phase 3: quotient induction and the main nilpotence theorem -/

/-- **Quotient descent for the chain hypothesis**:
if `[G,A,...,A]_m = 1`, then the same iterated commutator is trivial for the
induced action on `G/N`, provided `N` is normal and `A`-invariant. -/
private theorem iterCommutator_inl_inr_quotient_eq_bot
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) {m : ℕ}
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    let φbar : A →* MulAut (G ⧸ N) :=
      _root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN
    iterCommutator (SemidirectProduct.inl : G ⧸ N →* (G ⧸ N) ⋊[φbar] A).range
        (SemidirectProduct.inr : A →* (G ⧸ N) ⋊[φbar] A).range m = ⊥ := by
  dsimp
  let φbar : A →* MulAut (G ⧸ N) :=
    _root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN
  let F : G ⋊[φ] A →* (G ⧸ N) ⋊[φbar] A :=
    SemidirectProduct.map (QuotientGroup.mk' N) (MonoidHom.id A) (fun a => by
      ext g
      rfl)
  let XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  let YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  let Xbar : Subgroup ((G ⧸ N) ⋊[φbar] A) :=
    (SemidirectProduct.inl : G ⧸ N →* (G ⧸ N) ⋊[φbar] A).range
  let YAbar : Subgroup ((G ⧸ N) ⋊[φbar] A) :=
    (SemidirectProduct.inr : A →* (G ⧸ N) ⋊[φbar] A).range
  have h_map_X : XG.map F = Xbar := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk' N g, by simp [F]⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      refine ⟨(SemidirectProduct.inl : G →* G ⋊[φ] A) g, ⟨g, rfl⟩, ?_⟩
      simp [F]
  have h_map_Y : YA.map F = YAbar := by
    ext x
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, by simp [F]⟩
    · rintro ⟨a, rfl⟩
      refine ⟨(SemidirectProduct.inr : A →* G ⋊[φ] A) a, ⟨a, rfl⟩, ?_⟩
      simp [F]
  have h_map_iter :
      ∀ n : ℕ, (iterCommutator XG YA n).map F = iterCommutator Xbar YAbar n := by
    intro n
    induction n with
    | zero =>
        simpa [iterCommutator_zero] using h_map_X
    | succ n ih =>
        rw [iterCommutator_succ, iterCommutator_succ, Subgroup.map_commutator, ih, h_map_Y]
  have h_map_bot : (iterCommutator XG YA m).map F = ⊥ := by
    rw [h_iter, Subgroup.map_bot]
  rwa [h_map_iter m] at h_map_bot

/-- If `N` is `A`-invariant, then it is also invariant for the restricted `A^∞`-action. -/
private lemma isAInvariant_phiInfty_of_isAInvariant
    {A G : Type*} [Group A] [Group G] [Finite A] {φ : A →* MulAut G}
    {N : Subgroup G} (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) :
    OddOrder.Isaacs.Ch03.IsAInvariant (phiInfty φ) N := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a g hg
  exact hN.smul_mem a.val hg

/-- **`[G/N, A^∞]` is the image of `[G, A^∞]`** for an `A`-invariant normal subgroup `N`. -/
private lemma actionCommutatorInfty_quotient_eq_map
    {A G : Type*} [Group A] [Group G] [Finite A] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) :
    actionCommutatorInfty
        (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) =
      (actionCommutatorInfty φ).map (QuotientGroup.mk' N) := by
  change actionCommutator
        (phiInfty (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN)) =
      (actionCommutator (phiInfty φ)).map (QuotientGroup.mk' N)
  rw [actionCommutator, actionCommutator, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨q, a, rfl⟩
    refine QuotientGroup.induction_on q ?_
    intro g
    refine ⟨g * (phiInfty φ a) g⁻¹, ⟨g, a, rfl⟩, ?_⟩
    simp [map_mul, phiInfty]
  · rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk' N g, a, by simp [map_mul, phiInfty]⟩

/-- Γ-side form of "`A` centralizes `[G,A^∞]`". -/
private lemma commutator_inl_GAinf_inr_A_eq_bot_of_fixed
    {A G : Type*} [Group A] [Group G] [Finite A] {φ : A →* MulAut G}
    (h : actionCommutatorInfty φ ≤ Subgroup.fixedPointsOfMulAut φ) :
    ⁅(actionCommutatorInfty φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A),
      (SemidirectProduct.inr : A →* G ⋊[φ] A).range⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  rintro _ ⟨k, hk, rfl⟩ _ ⟨a, rfl⟩
  rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
  have h_fix : (φ a) k = k := h hk a
  rw [show (φ a) k⁻¹ = ((φ a) k)⁻¹ from map_inv (φ a) k, h_fix, mul_inv_cancel]
  exact map_one _

/-- Γ-side bridge: `⁅inl(G), inr(A^∞)⁆ = inl([G,A^∞])`. -/
private lemma commutator_inl_range_inr_lowerCentralSeriesInfty_eq_actionCommutatorInfty_map
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G) :
    ⁅(SemidirectProduct.inl : G →* G ⋊[φ] A).range,
      (lowerCentralSeriesInfty A).map (SemidirectProduct.inr : A →* G ⋊[φ] A)⁆ =
        (actionCommutatorInfty φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A) := by
  have h_eq_range :
      (lowerCentralSeriesInfty A).map (SemidirectProduct.inr : A →* G ⋊[φ] A) =
        ((SemidirectProduct.inr : A →* G ⋊[φ] A).comp
          (lowerCentralSeriesInfty A).subtype).range := by
    rw [MonoidHom.range_comp]
    rw [Subgroup.range_subtype]
  rw [h_eq_range]
  exact (actionCommutator_map_inl_comp φ (lowerCentralSeriesInfty A).subtype).symm

/-- If `A^∞` centralizes `[G,A]` and `A` centralizes `[G,A^∞]`, then `A^∞` acts
trivially on `G`. This is the final three-subgroups step in Isaacs Thm 4.24. -/
private theorem actionCommutatorInfty_eq_bot_of_centralized_and_fixed
    {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* MulAut G)
    (hGA : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ))
    (hKA : actionCommutatorInfty φ ≤ Subgroup.fixedPointsOfMulAut φ) :
    actionCommutatorInfty φ = ⊥ := by
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  set YinfA : Subgroup (G ⋊[φ] A) :=
    (lowerCentralSeriesInfty A).map (SemidirectProduct.inr : A →* G ⋊[φ] A)
  have h_XG_YA_Yinf : ⁅⁅XG, YA⁆, YinfA⁆ = ⊥ := by
    have h := commutator_inl_GA_inr_Ainf_eq_bot_of_centralized (φ := φ) hGA
    simpa [XG, YA, YinfA, actionCommutator_map_inl (φ := φ)] using h
  have h_YA_XG_Yinf : ⁅⁅YA, XG⁆, YinfA⁆ = ⊥ := by
    rw [Subgroup.commutator_comm YA XG]
    exact h_XG_YA_Yinf
  have h_XG_Yinf_eq :
      ⁅XG, YinfA⁆ =
        (actionCommutatorInfty φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A) := by
    simpa [XG, YinfA] using
      commutator_inl_range_inr_lowerCentralSeriesInfty_eq_actionCommutatorInfty_map φ
  have h_XG_Yinf_YA : ⁅⁅XG, YinfA⁆, YA⁆ = ⊥ := by
    have h := commutator_inl_GAinf_inr_A_eq_bot_of_fixed (φ := φ) hKA
    simpa [YA, h_XG_Yinf_eq] using h
  have h_three : ⁅⁅YinfA, YA⁆, XG⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h_YA_XG_Yinf h_XG_Yinf_YA
  have h_Yinf_YA : ⁅YinfA, YA⁆ = YinfA := by
    simp only [YinfA, YA]
    rw [MonoidHom.range_eq_map (SemidirectProduct.inr : A →* G ⋊[φ] A),
      ← Subgroup.map_commutator, lowerCentralSeriesInfty_commutator_top]
  rw [h_Yinf_YA, Subgroup.commutator_comm YinfA XG, h_XG_Yinf_eq] at h_three
  exact (Subgroup.map_eq_bot_iff_of_injective _ SemidirectProduct.inl_injective).mp h_three

/-- **General form of Isaacs Thm 4.24**: under the chain hypothesis, the stable lower
central term `A^∞` acts trivially on `G` (no faithfulness assumption). -/
private theorem actionCommutatorInfty_eq_bot_of_iter_eq_bot_aux :
    ∀ n : ℕ, ∀ {A G : Type*} [Group A] [Finite A] [Group G] [Finite G],
      (φ : A →* MulAut G) → ∀ {m : ℕ}, 1 ≤ m →
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥ →
      Nat.card G ≤ n → actionCommutatorInfty φ = ⊥ := by
  intro n
  induction n with
  | zero =>
      intro A G _ _ _ _ φ m hm h_iter h_le
      exact False.elim (Nat.not_succ_le_zero _ (Nat.card_pos.trans_le h_le))
  | succ n ih =>
      intro A G _ _ _ _ φ m hm h_iter h_le
      by_cases hG_nontriv : Nontrivial G
      swap
      · haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG_nontriv
        change actionCommutator (phiInfty φ) = ⊥
        rw [actionCommutator_eq_bot_iff_acts_trivially]
        intro a g
        exact Subsingleton.elim _ _
      haveI : Nontrivial G := hG_nontriv
      set H : Subgroup G := actionCommutator φ with hH_def
      have hH_ne_top : H ≠ ⊤ := by
        intro htop
        have hH_bot : H = ⊥ := by
          simpa [H, hH_def] using
            actionCommutator_eq_bot_of_eq_top_iterCommutator_eq_bot φ hm
              (by simpa [H, hH_def] using htop) h_iter
        have htop_bot : (⊤ : Subgroup G) = ⊥ := by
          rw [← htop, hH_bot]
        exact (top_ne_bot : (⊤ : Subgroup G) ≠ ⊥) htop_bot
      have hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H := by
        simpa [H, hH_def] using OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator φ
      let ψH : A →* MulAut H := OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH_inv
      have h_iter_H :
          iterCommutator (SemidirectProduct.inl : H →* H ⋊[ψH] A).range
              (SemidirectProduct.inr : A →* H ⋊[ψH] A).range m = ⊥ := by
        simpa [ψH] using iterCommutator_inl_inr_restrict_base_eq_bot
          (φ := φ) (H := H) hH_inv h_iter
      have hH_card_lt : Nat.card H < Nat.card G :=
        subgroup_card_lt_of_ne_top hH_ne_top
      have hH_card_le_n : Nat.card H ≤ n :=
        Nat.le_of_lt_succ (hH_card_lt.trans_le h_le)
      have hIH_H : actionCommutatorInfty ψH = ⊥ :=
        ih ψH hm h_iter_H hH_card_le_n
      have hGA_fixed_by_Ainf : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut (phiInfty φ) := by
        intro g hg
        rw [Subgroup.mem_fixedPointsOfMulAut]
        intro a
        have htriv := (actionCommutator_eq_bot_iff_acts_trivially (phiInfty ψH)).mp
          hIH_H a ⟨g, by simpa [H, hH_def] using hg⟩
        have hval := congrArg Subtype.val htriv
        simpa [ψH, phiInfty] using hval
      by_cases hK_bot : actionCommutatorInfty φ = ⊥
      · exact hK_bot
      let C : Subgroup G := actionCommutatorInfty_fix φ
      have hC_normal : C.Normal := by
        simpa [C] using actionCommutatorInfty_fix_normal_of_centralized φ hGA_fixed_by_Ainf
      haveI : C.Normal := hC_normal
      have hC_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ C := by
        simpa [C] using actionCommutatorInfty_fix_isAInvariant φ
      have hC_ne_bot : C ≠ ⊥ := by
        simpa [C] using actionCommutatorInfty_fix_ne_bot_of_ne_bot
          (φ := φ) (m := m) h_iter hK_bot
      let φbar : A →* MulAut (G ⧸ C) :=
        _root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hC_inv
      have h_iter_bar :
          iterCommutator (SemidirectProduct.inl : G ⧸ C →* (G ⧸ C) ⋊[φbar] A).range
              (SemidirectProduct.inr : A →* (G ⧸ C) ⋊[φbar] A).range m = ⊥ := by
        simpa [φbar] using iterCommutator_inl_inr_quotient_eq_bot
          (φ := φ) (N := C) hC_inv h_iter
      have hC_card_gt_one : 1 < Nat.card C := by
        have hC_card_ne_one : Nat.card C ≠ 1 := fun hcard =>
          hC_ne_bot (Subgroup.card_eq_one.mp hcard)
        have hpos : 0 < Nat.card C := Nat.card_pos
        omega
      have hquot_lt : Nat.card (G ⧸ C) < Nat.card G := by
        have hcard_eq : Nat.card G = Nat.card (G ⧸ C) * Nat.card C :=
          C.card_eq_card_quotient_mul_card_subgroup
        have hq_pos : 0 < Nat.card (G ⧸ C) := Nat.card_pos
        rw [hcard_eq]
        simpa [mul_comm] using
          Nat.mul_lt_mul_of_pos_right hC_card_gt_one hq_pos
      have hquot_le_n : Nat.card (G ⧸ C) ≤ n :=
        Nat.le_of_lt_succ (hquot_lt.trans_le h_le)
      have hIH_bar : actionCommutatorInfty φbar = ⊥ :=
        ih φbar hm h_iter_bar hquot_le_n
      have hK_le_C : actionCommutatorInfty φ ≤ C := by
        have hmap_bot : (actionCommutatorInfty φ).map (QuotientGroup.mk' C) = ⊥ := by
          rw [← actionCommutatorInfty_quotient_eq_map (φ := φ) (N := C) hC_inv,
            hIH_bar]
        have hle_ker : actionCommutatorInfty φ ≤ (QuotientGroup.mk' C).ker :=
          (Subgroup.map_eq_bot_iff (actionCommutatorInfty φ)).mp hmap_bot
        simpa [QuotientGroup.ker_mk'] using hle_ker
      have hK_fixed_by_A : actionCommutatorInfty φ ≤ Subgroup.fixedPointsOfMulAut φ :=
        hK_le_C.trans (by simp [C, actionCommutatorInfty_fix])
      exact actionCommutatorInfty_eq_bot_of_centralized_and_fixed φ
        hGA_fixed_by_Ainf hK_fixed_by_A

/-- **Isaacs Thm 4.24, non-faithful form**:
under the iterated-commutator chain hypothesis, `A^∞` lies in the kernel of the action. -/
theorem lowerCentralSeriesInfty_le_ker_of_iter_inl_inr_eq_bot
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    (φ : A →* MulAut G) {m : ℕ} (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    lowerCentralSeriesInfty A ≤ φ.ker := by
  have hbot : actionCommutatorInfty φ = ⊥ :=
    actionCommutatorInfty_eq_bot_of_iter_eq_bot_aux (Nat.card G) φ hm h_iter le_rfl
  change actionCommutator (phiInfty φ) = ⊥ at hbot
  rw [actionCommutator_eq_bot_iff_acts_trivially] at hbot
  intro a ha
  rw [MonoidHom.mem_ker]
  ext g
  exact hbot ⟨a, ha⟩ g

/-- **Isaacs Theorem 4.24**: if finite `A` acts faithfully on finite `G` and
`[G,A,...,A]=1`, then `A` is nilpotent. -/
theorem isaacs_thm_4_24
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    (φ : A →* MulAut G) (hfaithful : Function.Injective φ)
    {m : ℕ} (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    Group.IsNilpotent A := by
  have hAinf_le_ker := lowerCentralSeriesInfty_le_ker_of_iter_inl_inr_eq_bot
    (φ := φ) hm h_iter
  have hAinf_bot : lowerCentralSeriesInfty A = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have hker : φ a = 1 := by
      simpa [MonoidHom.mem_ker] using hAinf_le_ker ha
    have ha_one : a = 1 := hfaithful (by rw [hker, map_one])
    simp [ha_one]
  rw [Subgroup.nilpotent_iff_lowerCentralSeries]
  exact ⟨Nat.card A, by simpa [lowerCentralSeriesInfty] using hAinf_bot⟩

end /- §4C (続 II) -/

end OddOrder.Isaacs.Ch04

