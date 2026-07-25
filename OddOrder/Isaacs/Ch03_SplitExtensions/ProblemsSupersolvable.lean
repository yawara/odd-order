/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Problems3B

/-!
# Isaacs Chapter 3 — Problems §3B: 超可解群 (supersolvable groups)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) の章末演習 3B.7 (書籍 p. 85) が導入する
**超可解群** の定義と 3B.7 (a)(b) の解答。3B.9 / 3B.10 も同じ定義を使う。

超可解列は「`G` で**正規**な部分群の増大列で各因子が巡回」。Lean では「因子 `Nᵢ₊₁/Nᵢ` が巡回」を
**`Nᵢ₊₁ = Nᵢ ⊔ ⟨x⟩` なる `x ∈ Nᵢ₊₁` の存在**として表す (商群の `Normal` instance を仮説の中で
作らずに済み, `Nᵢ ≤ Nᵢ₊₁` も自動的に従う)。
-/

namespace OddOrder.Isaacs.Ch03

open scoped commutatorElement

universe u

section /- Problems 3B: supersolvable groups (p. 85) -/

/-- **超可解群** (Isaacs Problem 3B.7 の定義, 書籍 p. 85): `G` で正規な部分群の列
`1 = N₀ ⊆ N₁ ⊆ ⋯ ⊆ N_r = G` で各因子 `Nᵢ₊₁ / Nᵢ` が巡回なものが存在する.

因子の巡回性は `Nᵢ₊₁ = Nᵢ ⊔ ⟨x⟩` (`x ∈ Nᵢ₊₁`) の形で表す. -/
def IsSupersolvable (G : Type*) [Group G] : Prop :=
  ∃ (r : ℕ) (N : ℕ → Subgroup G), (∀ i, (N i).Normal) ∧ N 0 = ⊥ ∧ N r = ⊤ ∧
    ∀ i < r, ∃ x ∈ N (i + 1), N (i + 1) = N i ⊔ Subgroup.zpowers x

/-- `B = A ⊔ ⟨x⟩` で `A ⊴ G` なら `⁅B, B⁆ ≤ A` (商 `B/A` は巡回, 特に abelian). -/
theorem commutator_le_of_eq_sup_zpowers {G : Type*} [Group G] {A B : Subgroup G} [A.Normal]
    {x : G} (hB : B = A ⊔ Subgroup.zpowers x) : ⁅B, B⁆ ≤ A := by
  have hmap : B.map (QuotientGroup.mk' A) = Subgroup.zpowers ((QuotientGroup.mk' A) x) := by
    rw [hB, Subgroup.map_sup, MonoidHom.map_zpowers, QuotientGroup.map_mk'_self, bot_sup_eq]
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have ha' : (QuotientGroup.mk' A) a ∈ Subgroup.zpowers ((QuotientGroup.mk' A) x) := by
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ ha
  have hb' : (QuotientGroup.mk' A) b ∈ Subgroup.zpowers ((QuotientGroup.mk' A) x) := by
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ hb
  obtain ⟨i, hi⟩ := ha'
  obtain ⟨j, hj⟩ := hb'
  have hcomm : ((QuotientGroup.mk' A) a) * ((QuotientGroup.mk' A) b)
      = ((QuotientGroup.mk' A) b) * ((QuotientGroup.mk' A) a) := by
    rw [← hi, ← hj, zpow_mul_comm]
  have hone : (QuotientGroup.mk' A) ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  exact (QuotientGroup.eq_one_iff _).mp hone

/-- 超可解 ⟹ 可解 (各因子は巡回, 特に abelian なので Problem 3B.2 が使える). -/
theorem IsSupersolvable.isSolvable {G : Type*} [Group G] (h : IsSupersolvable G) :
    IsSolvable G := by
  obtain ⟨r, N, hnorm, h0, hr, hstep⟩ := h
  refine isSolvable_of_commutator_series N h0 hr fun i hi => ?_
  obtain ⟨x, -, hx⟩ := hstep i hi
  haveI := hnorm i
  exact commutator_le_of_eq_sup_zpowers hx

/-- 超可解群の商群も超可解. -/
theorem IsSupersolvable.quotient {G : Type*} [Group G] (h : IsSupersolvable G) (K : Subgroup G)
    [K.Normal] : IsSupersolvable (G ⧸ K) := by
  obtain ⟨r, N, hnorm, h0, hr, hstep⟩ := h
  refine ⟨r, fun i => (N i).map (QuotientGroup.mk' K), fun i => ?_, ?_, ?_, fun i hi => ?_⟩
  · exact (hnorm i).map _ (QuotientGroup.mk'_surjective K)
  · simp only [h0, Subgroup.map_bot]
  · simp only [hr, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
  · obtain ⟨x, hxmem, hx⟩ := hstep i hi
    refine ⟨(QuotientGroup.mk' K) x, Subgroup.mem_map_of_mem _ hxmem, ?_⟩
    simp only
    rw [hx, Subgroup.map_sup, MonoidHom.map_zpowers]

/-- **Isaacs Problem 3B.7(a)** (書籍 p. 85): 有限**超可解**群の極小正規部分群の位数は**素数**.

超可解列 `1 = N₀ ⊆ ⋯ ⊆ N_r = G` に対し `M ⊓ Nⱼ ≠ 1` となる最小の `j = i+1` を取ると,
極小性から `M ≤ Nᵢ₊₁` かつ `M ⊓ Nᵢ = 1`. よって `M` は `G ⧸ Nᵢ` の巡回部分群 `⟨x Nᵢ⟩` へ
単射的に写り `M` は巡回. 一方 Thm 3.11 で `M` は elementary abelian `p`-群なので
生成元の位数は `p`, すなわち `|M| = p`. -/
theorem card_prime_of_isMinimalNormal_of_isSupersolvable {G : Type u} [Group G] [Finite G]
    (hG : IsSupersolvable G) {M : Subgroup G} (hM : Ch02.IsMinimalNormal M) :
    (Nat.card ↥M).Prime := by
  classical
  haveI hMnormal : M.Normal := hM.1
  haveI : IsSolvable G := hG.isSolvable
  obtain ⟨r, N, hnorm, h0, hr, hstep⟩ := hG
  -- `M ⊓ N j ≠ ⊥` となる最小の `j`.
  have hexr : M ⊓ N r ≠ ⊥ := by rw [hr, inf_top_eq]; exact hM.2.1
  have hex : ∃ j, M ⊓ N j ≠ ⊥ := ⟨r, hexr⟩
  have hjspec : M ⊓ N (Nat.find hex) ≠ ⊥ := Nat.find_spec hex
  have hjle : Nat.find hex ≤ r := Nat.find_le hexr
  have hj0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, h0, inf_bot_eq] at hjspec
    exact hjspec rfl
  obtain ⟨i, hij⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hilt : i < r := by omega
  have hMi : M ⊓ N i = ⊥ :=
    not_not.mp (Nat.find_min hex (show i < Nat.find hex by omega))
  rw [hij] at hjspec
  -- `M ⊓ N (i+1)` は正規で `≤ M`, 極小性から `= M`.
  haveI : (N (i + 1)).Normal := hnorm (i + 1)
  haveI : (N i).Normal := hnorm i
  have hMle : M ≤ N (i + 1) := by
    rcases hM.2.2 (M ⊓ N (i + 1)) inferInstance inf_le_left with hbot | heq
    · exact absurd hbot hjspec
    · rw [← heq]; exact inf_le_right
  obtain ⟨x, -, hx⟩ := hstep i hilt
  -- `φ : M →* G ⧸ Nᵢ` は単射で, 像は巡回部分群 `⟨φ x⟩` に含まれる.
  set φ : G →* G ⧸ N i := QuotientGroup.mk' (N i) with hφ_def
  set ψ : ↥M →* G ⧸ N i := φ.comp M.subtype with hψ_def
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have h1 : (y : G) ∈ N i := by
      have h2 : φ (y : G) = 1 := MonoidHom.mem_ker.mp hy
      exact (QuotientGroup.eq_one_iff _).mp h2
    have h3 : (y : G) ∈ (M ⊓ N i : Subgroup G) := ⟨y.2, h1⟩
    rw [hMi, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hrange : ψ.range ≤ Subgroup.zpowers (φ x) := by
    rintro _ ⟨y, rfl⟩
    have hy : (y : G) ∈ N (i + 1) := hMle y.2
    rw [hx] at hy
    have hmapped : φ (y : G) ∈ (N i ⊔ Subgroup.zpowers x).map φ := Subgroup.mem_map_of_mem _ hy
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers, hφ_def, QuotientGroup.map_mk'_self,
      bot_sup_eq] at hmapped
  -- 巡回性を `M` に移す.
  haveI : IsCyclic ↥(ψ.range.subgroupOf (Subgroup.zpowers (φ x))) := inferInstance
  haveI : IsCyclic ↥ψ.range :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hrange).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hrange).surjective
  haveI : IsCyclic ↥M :=
    isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm.toMonoidHom
      (MonoidHom.ofInjective hinj).symm.surjective
  -- Thm 3.11: `M` は elementary abelian `p`-群. 巡回なので `|M| = p`.
  obtain ⟨p, hp, hEA⟩ := solvable_minimal_normal_isElementaryAbelian hM
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥M)
  have hord : orderOf g = Nat.card ↥M := orderOf_eq_card_of_forall_mem_zpowers hg
  have hdvd : Nat.card ↥M ∣ p := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one (hEA.pow_eq_one g)
  haveI : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM.2.1
  have hne1 : Nat.card ↥M ≠ 1 := (Finite.one_lt_card (α := ↥M)).ne'
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpeq
  · exact absurd h1 hne1
  · rw [hpeq]; exact hp

/-- **Isaacs Problem 3B.7(b)** (書籍 p. 85): 有限**超可解**群の極大部分群の指数は**素数**.

3B.1 と同じ骨格 (`|G|` の強帰納法 + 極小正規部分群) だが, (a) により極小正規部分群の位数が
素数 `p` なので, `N ≰ M` の場合の `|G : M| ∣ |N| = p` が直ちに素数を与える. -/
theorem index_prime_of_isCoatom_of_isSupersolvable_aux (n : ℕ) :
    ∀ {G : Type u} [Group G] [Finite G] (M : Subgroup G),
      IsSupersolvable G → Nat.card G ≤ n → IsCoatom M → M.index.Prime := by
  induction n with
  | zero =>
    intro G _ _ M _ hcard _
    have := Nat.card_pos (α := G)
    omega
  | succ n ih =>
    intro G _ _ M hG hcard hM
    haveI hnt : Nontrivial G := by
      rcases subsingleton_or_nontrivial G with hs | hn
      · exact absurd (by ext x; simp [Subsingleton.elim x (1 : G)] : M = ⊤) hM.1
      · exact hn
    have hMone : M.index ≠ 1 := fun h => hM.1 (Subgroup.index_eq_one.mp h)
    obtain ⟨N, hNmin, -⟩ :=
      Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
    haveI hNnormal : N.Normal := hNmin.1
    have hNprime : (Nat.card ↥N).Prime := card_prime_of_isMinimalNormal_of_isSupersolvable hG hNmin
    by_cases hNM : N ≤ M
    · -- `G ⧸ N` に落として帰納法 (指数は不変).
      have hindex : (M.map (QuotientGroup.mk' N)).index = M.index :=
        Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective N)
          (by rw [QuotientGroup.ker_mk']; exact hNM)
      haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNmin.2.1
      have hNcard : 1 < Nat.card ↥N := Finite.one_lt_card
      have hprod : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
      have hquot : Nat.card (G ⧸ N) ≤ n := by
        have h2 : 2 * N.index ≤ Nat.card ↥N * N.index := Nat.mul_le_mul_right _ hNcard
        rw [← Subgroup.index_eq_card]
        omega
      rw [← hindex]
      exact ih _ (hG.quotient N) hquot (isCoatom_map_mk'_of_isCoatom hNM hM)
    · -- `M ⊔ N = ⊤` なので `|G : M| ∣ |N| = p`, かつ `≠ 1` なので `= p`.
      have hsup : N ⊔ M = ⊤ := by
        rw [sup_comm]
        refine hM.2 _ (lt_of_le_of_ne le_sup_left fun h => hNM ?_)
        exact h ▸ le_sup_right
      have hdvd : M.index ∣ Nat.card ↥N :=
        ⟨_, (Ch02.index_mul_card_inf_eq_card_of_sup_eq_top hsup).symm⟩
      rcases (Nat.dvd_prime hNprime).mp hdvd with h1 | heq
      · exact absurd h1 hMone
      · rw [heq]; exact hNprime

/-- **Isaacs Problem 3B.7(b)** (書籍 p. 85): 有限**超可解**群の極大部分群の指数は**素数**. -/
theorem index_prime_of_isCoatom_of_isSupersolvable {G : Type u} [Group G] [Finite G]
    (hG : IsSupersolvable G) {M : Subgroup G} (hM : IsCoatom M) : M.index.Prime :=
  index_prime_of_isCoatom_of_isSupersolvable_aux (Nat.card G) M hG le_rfl hM

end

end OddOrder.Isaacs.Ch03
