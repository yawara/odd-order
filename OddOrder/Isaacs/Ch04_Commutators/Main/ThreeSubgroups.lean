import OddOrder.Isaacs.Ch04_Commutators.Main.CommutatorBasics

/-!
# ThreeSubgroups

Prefix-split from `OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroupsCoprime` (2000-line limit,
issue 0103 第 2 パス).
-/

/-!
# Isaacs §4B-§4D 前半 — three subgroups, Mann, coprime action, [G,A] (pp. 122-141)

Split from the former monolithic `OddOrder.Isaacs.Ch04_Commutators.Main` (directory split, issue
0103).
-/
namespace OddOrder.Isaacs.Ch04
open scoped commutatorElement

variable {G : Type*} [Group G]


section /- 4B: Three-subgroups + lcs additivity + Mann (pp. 122-131) -/

/-! ### Isaacs §4B (Three-subgroups + lower central series)

- **Lemma 4.9 Three-subgroups**: mathlib `Subgroup.commutator_commutator_eq_bot_of_rotate`
  で完全カバー (前提 `⁅⁅H₂,H₃⁆, H₁⁆ = ⊥ ∧ ⁅⁅H₃,H₁⁆, H₂⁆ = ⊥ ⇒ ⁅⁅H₁,H₂⁆, H₃⁆ = ⊥`).
  no-wrapper. -/

/-- **Isaacs Cor 4.10** (Three-subgroups mod `N`):
`N ⊴ G` を含む形での 4.9 — `⁅⁅H₂, H₃⁆, H₁⁆ ≤ N ∧ ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N
⇒ ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N`.

商写像 `G → G/N` で push し, image 上で mathlib `commutator_commutator_eq_bot_of_rotate`
を適用. -/
theorem commutator_commutator_le_of_rotate {H₁ H₂ H₃ N : Subgroup G} [N.Normal]
    (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) :
    ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  -- Use `≤ N ↔ map (mk' N) = ⊥` (since ker (mk' N) = N).
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have to_quot : ∀ {K : Subgroup G}, K ≤ N ↔ K.map π = ⊥ := by
    intro K
    rw [eq_bot_iff, Subgroup.map_le_iff_le_comap]
    constructor
    · intro h x hx
      rw [Subgroup.mem_comap, hπ, Subgroup.mem_bot, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
      exact h hx
    · intro h x hx
      have := h hx
      rw [Subgroup.mem_comap, hπ, Subgroup.mem_bot, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at this
      exact this
  rw [to_quot]
  rw [to_quot] at h1 h2
  -- Map distributes over commutator.
  simp only [Subgroup.map_commutator] at h1 h2 ⊢
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

/-- **Isaacs Thm 4.11** (lcs 加法性) ⭐: `⁅γᵢ(G), γⱼ(G)⁆ ≤ γᵢ₊ⱼ(G)`.

mathlib indexing (`lcs 0 = ⊤ = G^1`, `lcs n = G^{n+1}`) では Isaacs `⁅G^i, G^j⁆ ≤ G^{i+j}`
は `⁅lcs (i-1), lcs (j-1)⁆ ≤ lcs (i+j-1)`, つまり `⁅lcs a, lcs b⁆ ≤ lcs (a + b + 1)`
(`a = i-1, b = j-1`).

**証明** (Isaacs p.123-124): `j` についての induction (`i` 自由).
* base `j = 0`: `⁅lcs i, ⊤⁆ = lcs (i+1)` (mathlib `lowerCentralSeries` 定義式).
* step: Cor 4.10 (Three-subgroups mod `N`) を `H₁ = lcs j, H₂ = ⊤, H₃ = lcs i,
  N = lcs (i+j+2)` で適用. `lcs n` は characteristic ⇒ normal なので `[N.Normal]` 成立.
  - h1 (`⁅⁅⊤, lcs i⁆, lcs j⁆ ≤ N`): `⁅⊤, lcs i⁆ = ⁅lcs i, ⊤⁆ = lcs (i+1)`
    (`commutator_comm` + 定義) 経由で IH at `(i+1, j)`.
  - h2 (`⁅⁅lcs i, lcs j⁆, ⊤⁆ ≤ N`): IH at `(i, j)` + `commutator_mono`
    + `lcs (i+j+1)+1 = lcs (i+j+2)` (定義).
  - 結論 `⁅⁅lcs j, ⊤⁆, lcs i⁆ ≤ N`, つまり `⁅lcs (j+1), lcs i⁆ ≤ lcs (i+j+2)`.
  - `commutator_comm` で `⁅lcs i, lcs (j+1)⁆ ≤ lcs (i+j+2)` を得る.

**下流**: Cor 4.12 (weight n commutator ⊆ G^n), Cor 4.13 (derived ⊆ lcs),
Ch.2 §2D Lucchini K = ⊥ aux の解消経路. -/
theorem commutator_lowerCentralSeries_le (i j : ℕ) :
    ⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G).lowerCentralSeries j⁆ ≤
      (⊤ : Subgroup G).lowerCentralSeries (i + j + 1) := by
  induction j generalizing i with
  | zero =>
    -- ⁅lcs i, lcs 0⁆ = ⁅lcs i, ⊤⁆ = lcs (i+1) by `lowerCentralSeries` def.
    change ⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G)⁆ ≤
      (⊤ : Subgroup G).lowerCentralSeries (i + 1)
    exact le_refl _
  | succ j ih =>
    -- Goal: ⁅lcs i, lcs (j+1)⁆ ≤ lcs (i + (j+1) + 1) = lcs (i + j + 2).
    -- Step A: prove the rotated form via Cor 4.10.
    have key : ⁅⁅(⊤ : Subgroup G).lowerCentralSeries j, (⊤ : Subgroup G)⁆,
        (⊤ : Subgroup G).lowerCentralSeries i⁆ ≤
        (⊤ : Subgroup G).lowerCentralSeries (i + j + 2) := by
      refine commutator_commutator_le_of_rotate ?_ ?_
      · -- h1: ⁅⁅⊤, lcs i⁆, lcs j⁆ ≤ lcs (i + j + 2).
        have h_top : (⁅(⊤ : Subgroup G), (⊤ : Subgroup G).lowerCentralSeries i⁆ : Subgroup G) =
            (⊤ : Subgroup G).lowerCentralSeries (i + 1) := by
          rw [Subgroup.commutator_comm]; rfl
        rw [h_top]
        have hIH := ih (i + 1)
        have heq : (i + 1) + j + 1 = i + j + 2 := by omega
        rwa [heq] at hIH
      · -- h2: ⁅⁅lcs i, lcs j⁆, ⊤⁆ ≤ lcs (i + j + 2).
        -- By IH at i + `commutator_mono` + `lcs (i+j+1)+1 = lcs (i+j+2)` def.
        exact Subgroup.commutator_mono (ih i) le_rfl
    -- Step B: rewrite goal into rotated form via `commutator_comm` + `lowerCentralSeries` def.
    have hidx : i + (j + 1) + 1 = i + j + 2 := by omega
    rw [hidx]
    -- Goal: ⁅lcs i, lcs (j+1)⁆ ≤ lcs (i + j + 2).
    -- lcs (j+1) = ⁅lcs j, ⊤⁆ definitionally; commute and conclude.
    rw [Subgroup.commutator_comm]
    exact key

/-- **左結合 n-重交換子**: `iterLeftCommutator g [g₁, g₂, ..., gₙ] = ⁅...⁅⁅g, g₁⁆, g₂⁆..., gₙ⁆`.
`gs.length = n` のとき重み `n+1`. -/
def iterLeftCommutator (head : G) (tail : List G) : G :=
  tail.foldl (fun acc g => ⁅acc, g⁆) head

/-- **`iterLeftCommutator` 汎用補題**: accumulator が `lcs n` 内なら, 長さ `m` の
リストでの fold は `lcs (n + m)` に収まる. -/
theorem iterLeftCommutator_mem_lowerCentralSeries_add (n : ℕ) (acc : G)
    (hacc : acc ∈ (⊤ : Subgroup G).lowerCentralSeries n) (gs : List G) :
    iterLeftCommutator acc gs ∈ (⊤ : Subgroup G).lowerCentralSeries (n + gs.length) := by
  induction gs generalizing n acc with
  | nil =>
    simpa [iterLeftCommutator] using hacc
  | cons g rest ih =>
    -- iterLeftCommutator acc (g :: rest) = iterLeftCommutator ⁅acc, g⁆ rest.
    have step : ⁅acc, g⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (n + 1) := by
      change ⁅acc, g⁆ ∈ ⁅(⊤ : Subgroup G).lowerCentralSeries n, (⊤ : Subgroup G)⁆
      exact Subgroup.commutator_mem_commutator hacc (Subgroup.mem_top g)
    have hRec := ih (n + 1) ⁅acc, g⁆ step
    -- hRec : iterLeftCommutator ⁅acc, g⁆ rest ∈ lcs ((n+1) + rest.length)
    have hidx : n + (g :: rest).length = (n + 1) + rest.length := by
      simp [List.length_cons]; omega
    rw [hidx]
    -- Convert goal: iterLeftCommutator acc (g :: rest) = iterLeftCommutator ⁅acc, g⁆ rest (rfl).
    change iterLeftCommutator ⁅acc, g⁆ rest ∈ _
    exact hRec

/-- **Isaacs Cor 4.12** (weight n commutator ⊆ G^n): 重み `n+1` の左結合交換子は
`lcs G n` に含まれる. mathlib indexing で Isaacs `G^{n+1}` = mathlib `lcs G n`.

**証明**: 汎用補題 `iterLeftCommutator_mem_lowerCentralSeries_add` を `n = 0`,
`acc = g ∈ ⊤ = lcs 0` で specialize. -/
theorem iterLeftCommutator_mem_lowerCentralSeries (g : G) (gs : List G) :
    iterLeftCommutator g gs ∈ (⊤ : Subgroup G).lowerCentralSeries gs.length := by
  simpa using iterLeftCommutator_mem_lowerCentralSeries_add 0 g
    (by simp : g ∈ (⊤ : Subgroup G)) gs

/-- **Isaacs Cor 4.13** (derived ⊆ lcs with exponential index):
`derivedSeries G r ≤ lowerCentralSeries G (2^r - 1)`.

mathlib 既存の `derived_le_lower_central` (`derived r ≤ lcs r`) より strictly stronger
(`r ≥ 2` で lcs が antitone のため): Isaacs notation `G^{(r)} ⊆ G^{2^r}` (`G^k = lcs (k-1)`,
`G^{(r)} = derivedSeries r`) に対応.

**証明** (Isaacs p.124): `r`-induction.
* base `r = 0`: `derivedSeries 0 = ⊤ = lcs 0 = lcs (2^0 - 1)` (rfl).
* step: `derivedSeries (r+1) = ⁅derivedSeries r, derivedSeries r⁆`
  - IH + `commutator_mono`: ≤ `⁅lcs (2^r-1), lcs (2^r-1)⁆`.
  - **Thm 4.11** (`commutator_lowerCentralSeries_le`): ≤ `lcs ((2^r-1) + (2^r-1) + 1)`.
  - 算術: `(2^r-1) + (2^r-1) + 1 = 2·2^r - 1 = 2^(r+1) - 1` (`1 ≤ 2^r` 経由).

**系** (Isaacs Cor 4.13 文): `G` nilpotent class `m` (`lcs m = ⊥`) ⇒ derived length
`≤ 1 + ⌈log₂ m⌉`. 本リポでは boolean form のみ実装, log₂ 操作は別途. -/
theorem derivedSeries_le_lowerCentralSeries_two_pow_sub_one (r : ℕ) :
    derivedSeries G r ≤ (⊤ : Subgroup G).lowerCentralSeries (2 ^ r - 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [derivedSeries_succ]
    calc ⁅derivedSeries G r, derivedSeries G r⁆
        ≤ ⁅(⊤ : Subgroup G).lowerCentralSeries (2 ^ r - 1),
            (⊤ : Subgroup G).lowerCentralSeries (2 ^ r - 1)⁆ :=
          Subgroup.commutator_mono ih ih
      _ ≤ (⊤ : Subgroup G).lowerCentralSeries ((2 ^ r - 1) + (2 ^ r - 1) + 1) :=
          commutator_lowerCentralSeries_le _ _
      _ = (⊤ : Subgroup G).lowerCentralSeries (2 ^ (r + 1) - 1) := by
          congr 1
          have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
          rw [pow_succ]
          omega

/-- **Cor 4.13 系** (G nilpotent ⇒ derived series 量的境界):
`lowerCentralSeries G m = ⊥` ⇒ `derivedSeries G (Nat.log 2 m + 1) = ⊥`.

形式的には `lcs m = ⊥ ⇒ derived (⌊log₂ m⌋ + 1) = ⊥`. mathlib 既存 `IsNilpotent → IsSolvable`
は qualitative only (具体的 derived length 不明), 本補題は **Cor 4.13** から得られる
**explicit upper bound** を与える.

**証明**: `m < 2^(Nat.log 2 m + 1)` (`Nat.lt_pow_succ_log_self`) ⇒ `2^(...)-1 ≥ m`
⇒ lcs antitone で `lcs (2^(...)-1) ≤ lcs m = ⊥`. **Cor 4.13** で `derived (Nat.log 2 m + 1)
≤ lcs (2^(Nat.log 2 m + 1) - 1) = ⊥`. -/
theorem derivedSeries_eq_bot_of_lowerCentralSeries_eq_bot
    {m : ℕ} (h : (⊤ : Subgroup G).lowerCentralSeries m = ⊥) :
    derivedSeries G (Nat.log 2 m + 1) = ⊥ := by
  have h2pow : m < 2 ^ (Nat.log 2 m + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num : (1:ℕ) < 2) m
  have hidx : m ≤ 2 ^ (Nat.log 2 m + 1) - 1 := by omega
  rw [eq_bot_iff]
  calc derivedSeries G (Nat.log 2 m + 1)
      ≤ (⊤ : Subgroup G).lowerCentralSeries (2 ^ (Nat.log 2 m + 1) - 1) :=
        derivedSeries_le_lowerCentralSeries_two_pow_sub_one _
    _ ≤ (⊤ : Subgroup G).lowerCentralSeries m :=
        (⊤ : Subgroup G).lowerCentralSeries_antitone hidx
    _ = ⊥ := h

/-! ### iterCommutator + Z(F(G)) absorbs G-minimal 補題群

`iterCommutator E F n = ⁅...⁅E, F⁆, F⁆..., F⁆` の infrastructure と
`le_centralizer_of_isMinimalNormal` (Z(F(G)) absorbs G-minimal in F(G)) 系は
**`OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh02.lean`** に移動 (2026-05-24).

理由: Lucchini K=⊥ aux 解消 (issue #0001) で同じ補助補題群を使うが,
ForwardFromCh02 → Main.lean の direct import は循環依存になる
(Main → Ch3 → ForwardFromCh02 → Main). ForwardFromCh02 に置くことで Main.lean
からは Ch3 経由で transitive にアクセス可能 (namespace `OddOrder.Isaacs.Ch04` を共有).

Main.lean 側で `iterCommutator` を使う §4C `iterCommutator_add` / §4D
`iterCommutator_inl_inr_two_eq_one` は ForwardFromCh02 の declarations を直接参照. -/

/-! **Mann 4.14-4.19**: M(G), self-centralizing normal abelian 系. Isaacs 独自集約で
**BG/Peterfalvi 直接被引用 0**. ⇒ **Phase 1 内では skip 可** (audit 確認). -/

end -- 4B

section /- 4C: A acts on G via automorphisms (pp. 131-138) -/

/-! ### Isaacs §4C (A 作用 + [G,A])

`A ⊆ Aut(G)` の作用下で `[G, A]` (= smallest A-invariant N with A trivial on G/N) の構造論.

- **Lemma 4.20**: `⁅G, A⁆` は `A` が trivial 作用する最小 A-invariant 正規部分群.
- **Cor 4.21**: TFAE: (a) 右剰余類すべて A-inv, (b) 左剰余類すべて A-inv, (c) `⁅G,A⁆ ⊆ H`.
- **Thm 4.22**: A faithful + `⁅G, A, ..., A⁆_m = 1` ⇒ A solvable, derived length ≤ m-1.
- **Cor 4.23**: m=2 版.
- **Thm 4.24**: A faithful + chain ⇒ A nilpotent.
- **Lemma 4.25**: `⁅G,A,A⁆ = 1` ⇒ `⁅G,A⁆` abelian.
- **Thm 4.26**: A p-群 + chain ⇒ `⁅G,A⁆` は p-群.
- **Thm 4.27**: A 有限 + chain ⇒ `⁅G,A⁆` nilpotent.

全 stub. `[G, A]` の Lean 形式化 (semidirect product `G ⋊ A` 経由 vs `MulAut` 経由)
の設計判断が要る. ~500-800 行 LOC 推定. -/

end -- 4C

section /- 4D: Coprime action — Fitting + Thompson PxQ + Baer (pp. 138-146) -/

/-! ### Isaacs §4D (Coprime action) ⭐ FT クリティカル

BG Prop 1.6(a)(b)(c)(d)(e) クラスタ + BG Thm 1.11 がこの section を占める.

- **Lemma 4.28** ⭐ BG Prop 1.6(a): `(|G|,|A|) = 1` + (A or G solvable)
  ⇒ `G = C_G(A) · ⁅G, A⁆`.
- **Lemma 4.29** ⭐ BG Prop 1.6(b): coprime ⇒ `⁅G, A, A⁆ = ⁅G, A⁆`.
- **Cor 4.30**: A faithful + chain ⇒ `|A|` の素因子 ⊆ `|G|` の素因子.
- **Thm 4.31 Thompson P×Q** ⭐: `A = P × Q` (P p-群, Q p'-群) acts on p-群 G,
  Q fixes every P-fixed element ⇒ Q trivial on G.
- **Lemma 4.32**: P p-群, G 非自明 p-群: `⁅G, P⁆ < G` かつ `C_G(P) > 1`.
- **Thm 4.33**: G p-solvable ⇒ 全 p-local H で `O_{p'}(H) ≤ O_{p'}(G)`. **Hall-Higman 1.2.3
  (Ch.3 Lem 3.21) 経由**.
- **Thm 4.34 Fitting** ⭐ BG Prop 1.6(d): G abelian + coprime ⇒ `G = C_G(A) × ⁅G, A⁆`.
- **Cor 4.35** ⭐ BG Prop 1.6(e): G abelian p-群 + A p'-群 fixes order-p elements
  ⇒ A trivial.
- **Thm 4.36** ⭐ BG Thm 1.11: p > 2, G p-群 + A p'-群 fixes order-p elements
  ⇒ A trivial. **Ch.5 Cor 5.30 経由で normal p-comp 5.26 へ**.
- **Lemma 4.37 Baer trick**: G odd order + class ≤ 2 ⇒ `x +' y := xy√⁅y,x⁆` で加法群.
- **Thm 4.38**: p > 2, P p-群 + Q ⊴ A p'-群, Q fixes P-fixed elements ⇒ Q trivial
  (4.31 強化, P 正規不要).

**実装スケジュール推定**: 4.28 + 4.29 + 4.30 (~200 行 / 1 週), 4.34 + 4.35 + 4.36
(~250 行 / 1-2 週), 4.31 + 4.32 + 4.38 (~150 行 / 1 週), 4.33 + 4.37 (~150 行 / 1 週).

合計 ~750 行 LOC / 4-5 週. Phase 1 残予算と要相談. -/

/-- A finite `p`-group is a `{p}`-group in the π-group sense. -/
theorem isPiGroup_singleton_of_isPGroup {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} (hH : IsPGroup p H) :
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) H := by
  intro q hq
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := H)).mp hH
  rw [hn] at hq
  by_cases hn0 : n = 0
  · simp [hn0] at hq
  · rw [Nat.primeFactors_prime_pow hn0 Fact.out] at hq
    simpa using hq

/-- A finite `{p}`-group in the π-group sense is a `p`-group. -/
theorem isPGroup_of_isPiGroup_singleton {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) H) :
    IsPGroup p H := by
  rw [IsPGroup.iff_card]
  exact ⟨(Nat.card H).primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun {q} hq_prime hq_dvd => by
      have hq_pf : q ∈ (Nat.card H).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd, Nat.card_pos.ne'⟩
      simpa using hH q hq_pf)⟩

/-- Singleton π-core agrees with the usual `p`-core. -/
theorem oPiCore_singleton_eq_opCore {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] :
    OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G =
      OddOrder.Isaacs.Ch01.opCore p G := by
  apply le_antisymm
  · exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore
      (isPGroup_of_isPiGroup_singleton (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup ({p} : Set ℕ)))
  · exact OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore
      (isPiGroup_singleton_of_isPGroup (OddOrder.Isaacs.Ch01.opCore_isPGroup p G))

theorem opCore_eq_bot_of_mulEquiv
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (e : G ≃* H)
    (hG : OddOrder.Isaacs.Ch01.opCore p G = ⊥) :
    OddOrder.Isaacs.Ch01.opCore p H = ⊥ := by
  rw [← oPiCore_singleton_eq_opCore (G := H) p,
    ← OddOrder.Isaacs.Ch03.oPiCore.map_eq_of_mulEquiv ({p} : Set ℕ) e,
    oPiCore_singleton_eq_opCore (G := G) p, hG, Subgroup.map_bot]

/-- In a finite abelian group with trivial `O_p`, every prime divisor is different from `p`. -/
theorem isPiGroup_compl_top_of_isMulCommutative_opCore_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [IsMulCommutative G]
    (hOp : OddOrder.Isaacs.Ch01.opCore p G = ⊥) :
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} (⊤ : Subgroup G) := by
  intro q hq hq_mem
  have hq_eq : q = p := by simpa using hq_mem
  subst q
  have hp_dvd_top : p ∣ Nat.card ↥(⊤ : Subgroup G) :=
    Nat.dvd_of_mem_primeFactors hq
  have hp_dvd : p ∣ Nat.card G := by simpa using hp_dvd_top
  let P : Sylow p G := default
  -- rc2: `CommGroup.ofIsMulCommutative` removed; build CommGroup from the IsMulCommutative.
  letI : CommGroup G :=
    { (inferInstance : Group G) with mul_comm := ‹IsMulCommutative G›.is_comm.comm }
  haveI : (P : Subgroup G).Normal := Subgroup.normal_of_isMulCommutative _
  have hP_le : (P : Subgroup G) ≤ OddOrder.Isaacs.Ch01.opCore p G :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore P.isPGroup'
  have hP_bot : (P : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    simpa [hOp] using hP_le
  exact (P.ne_bot_of_dvd_card hp_dvd) hP_bot

lemma opCore_quotient_opCore_eq_bot {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] :
    OddOrder.Isaacs.Ch01.opCore p (G ⧸ OddOrder.Isaacs.Ch01.opCore p G) = ⊥ := by
  set N : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hN_def
  set f : G →* G ⧸ N := QuotientGroup.mk' N with hf_def
  have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective N
  have hf_ker : f.ker = N := QuotientGroup.ker_mk' N
  set Kbar : Subgroup (G ⧸ N) := OddOrder.Isaacs.Ch01.opCore p (G ⧸ N) with hKbar_def
  set K : Subgroup G := Kbar.comap f with hK_def
  haveI hK_normal : K.Normal := Kbar.normal_comap f
  have hKbar_pgroup : IsPGroup p Kbar := OddOrder.Isaacs.Ch01.opCore_isPGroup p (G ⧸ N)
  have hN_pgroup : IsPGroup p N := OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  have hN_le_K : N ≤ K := by
    intro x hx
    have hfx : f x = 1 := by
      have : x ∈ f.ker := by rw [hf_ker]; exact hx
      exact this
    rw [hK_def, Subgroup.mem_comap, hfx]
    exact Subgroup.one_mem _
  have hK_map : K.map f = Kbar := by
    rw [hK_def]
    exact Subgroup.map_comap_eq_self_of_surjective hf_surj Kbar
  have hK_pgroup : IsPGroup p K := by
    have h_quot_card : Nat.card (↥K ⧸ N.subgroupOf K) = Nat.card Kbar := by
      let g : ↥K →* G ⧸ N := f.comp K.subtype
      have hg_range : g.range = K.map f := by
        simp [g, MonoidHom.range_comp, Subgroup.range_subtype]
      have hg_ker : g.ker = N.subgroupOf K := by
        ext x
        constructor
        · intro hx
          have : f (x : G) = 1 := hx
          have hxN : (x : G) ∈ N := by rw [← hf_ker]; exact this
          exact hxN
        · intro hx
          have hxN : (x : G) ∈ N := hx
          have : (x : G) ∈ f.ker := by rw [hf_ker]; exact hxN
          exact this
      have h_iso : (↥K) ⧸ g.ker ≃* ↥g.range :=
        QuotientGroup.quotientKerEquivRange g
      have h_card_eq : Nat.card ((↥K) ⧸ g.ker) = Nat.card ↥g.range :=
        Nat.card_congr h_iso.toEquiv
      rw [hg_ker] at h_card_eq
      rw [h_card_eq, hg_range, hK_map]
    have h_sub_card : Nat.card (N.subgroupOf K) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_le_K).toEquiv
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hKbar_pgroup
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hN_pgroup
    have hK_card : Nat.card K = p ^ (a + b) := by
      have h_mul : Nat.card K = Nat.card (↥K ⧸ N.subgroupOf K) *
          Nat.card (N.subgroupOf K) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup]
      rw [h_mul, h_quot_card, ha, h_sub_card, hb, pow_add]
    exact IsPGroup.of_card hK_card
  have hK_le_N : K ≤ N := by
    have := OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore (N := K) hK_pgroup
    rw [hN_def]
    exact this
  have hK_eq_N : K = N := le_antisymm hK_le_N hN_le_K
  rw [← hK_map, hK_eq_N]
  apply le_bot_iff.mp
  intro y hy
  rcases hy with ⟨z, hz, hzy⟩
  rw [Subgroup.mem_bot, ← hzy]
  have : z ∈ f.ker := by rw [hf_ker]; exact hz
  exact this

lemma subgroup_card_lt_card_of_ne_top
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} (h_ne : H ≠ ⊤) :
    Nat.card ↥H < Nat.card G := by
  have h_dvd : Nat.card ↥H ∣ Nat.card G :=
    ⟨H.index, by rw [mul_comm, H.index_mul_card]⟩
  have h_le' : Nat.card ↥H ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos h_dvd
  have h_ne' : Nat.card ↥H ≠ Nat.card G := fun heq =>
    h_ne (Subgroup.eq_top_of_card_eq _ heq)
  exact Nat.lt_of_le_of_ne h_le' h_ne'

/-- A finite group is generated by all of its Sylow subgroups. -/
lemma iSup_sylow_eq_top {M : Type*} [Group M] [Finite M] :
    (⨆ p : (Nat.card M).primeFactors, ⨆ P : Sylow p.val M, (P : Subgroup M)) = ⊤ := by
  classical
  set sup := ⨆ p : (Nat.card M).primeFactors, ⨆ P : Sylow p.val M, (P : Subgroup M) with hsup_def
  have h_sup_dvd : Nat.card sup ∣ Nat.card M := Subgroup.card_subgroup_dvd_card sup
  have h_pow_dvd : ∀ p ∈ (Nat.card M).primeFactors,
      p ^ (Nat.card M).factorization p ∣ Nat.card sup := by
    intro p hp
    haveI hp_prime : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    have hP_le : ((default : Sylow p M) : Subgroup M) ≤ sup := by
      rw [hsup_def]
      refine le_trans ?_ (le_iSup (fun q : (Nat.card M).primeFactors =>
        ⨆ Q : Sylow q.val M, (Q : Subgroup M)) ⟨p, hp⟩)
      exact le_iSup (fun Q : Sylow p M => (Q : Subgroup M)) default
    have h_dvd := Subgroup.card_dvd_of_le hP_le
    rwa [Sylow.card_eq_multiplicity] at h_dvd
  have h_factorization_le : ∀ p, (Nat.card M).factorization p ≤ (Nat.card sup).factorization p := by
    intro p
    rcases Nat.eq_zero_or_pos ((Nat.card M).factorization p) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hp_in : p ∈ (Nat.card M).primeFactors := by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr (by omega)
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
      exact (hp_prime.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp (h_pow_dvd p hp_in)
  have h_factorization_le' : ∀ p, (Nat.card sup).factorization p ≤ (Nat.card M).factorization p :=
    fun p => (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr h_sup_dvd p
  have h_eq : Nat.card sup = Nat.card M := by
    apply Nat.eq_of_factorization_eq Nat.card_pos.ne' Nat.card_pos.ne'
    intro p
    exact le_antisymm (h_factorization_le' p) (h_factorization_le p)
  exact Subgroup.eq_top_of_card_eq sup h_eq

/-- Hall-Higman 1.2.3 specialized from `O_π` to the usual `p`-core. -/
theorem hall_higman_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hπ' : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥) :
    Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) ≤
      OddOrder.Isaacs.Ch01.opCore p G := by
  rw [← oPiCore_singleton_eq_opCore (G := G) p]
  exact OddOrder.Isaacs.Ch03.hall_higman_1_2_3 ({p} : Set ℕ) hπ'

/-- Normal `p`-subgroups commute with normal `p'`-subgroups in a finite group. -/
theorem commute_of_normal_isPGroup_of_normal_isPiCompl
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P Q : Subgroup G} [P.Normal] [Q.Normal]
    (hP : IsPGroup p P)
    (hQ : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} Q) :
    ∀ x y : G, x ∈ P → y ∈ Q → Commute x y := by
  have hPpi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) P :=
    isPiGroup_singleton_of_isPGroup hP
  have hcop : Nat.Coprime (Nat.card P) (Nat.card Q) :=
    OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne' hPpi hQ
  have hdis : Disjoint P Q := Subgroup.disjoint_of_coprime_natCard hcop
  intro x y hx hy
  exact Subgroup.commute_of_normal_of_disjoint P Q inferInstance inferInstance hdis x y hx hy

/-- centralizer ⊆ normalizer (mathlib v4.29.1 に直接の lemma 無し). -/
theorem centralizer_le_normalizer_subgroup {G : Type*} [Group G] (H : Subgroup G) :
    Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer H := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hcomm : ∀ z ∈ H, z * x = x * z := Subgroup.mem_centralizer_iff.mp hx
  have hx_inv_mem : x⁻¹ ∈ Subgroup.centralizer (H : Set G) :=
    Subgroup.inv_mem _ hx
  have hcomm_inv : ∀ z ∈ H, z * x⁻¹ = x⁻¹ * z :=
    Subgroup.mem_centralizer_iff.mp hx_inv_mem
  refine ⟨fun hy => ?_, fun hxyx => ?_⟩
  · have hxy : x * y = y * x := (hcomm y hy).symm
    have : x * y * x⁻¹ = y := by rw [hxy]; group
    rw [this]; exact hy
  · have hcomm_z : (x * y * x⁻¹) * x⁻¹ = x⁻¹ * (x * y * x⁻¹) :=
      hcomm_inv (x * y * x⁻¹) hxyx
    have h_eq : y * x⁻¹ = (x * y * x⁻¹) * x⁻¹ := by
      rw [hcomm_z]; group
    have hy_eq : y = x * y * x⁻¹ := mul_right_cancel h_eq
    rw [hy_eq]; exact hxyx

/-- **作用交換子部分群** `[G, A]_φ` := 集合 `{g * (φ a) g⁻¹ : g ∈ G, a ∈ A}` の生成部分群.

これは Γ = G ⋊[φ] A 内で `⁅inl(G), inr(A)⁆` を `inl : G →* Γ` 経由で pull back した
ものに対応する. 具体的計算: `[inl(g), inr(a)] = inl(g * (φ a) g⁻¹)` (`inl_aut` 経由).

下流 Isaacs §4D 4.28-4.30 の `[G, A]` 記号の自然な実装. -/
def actionCommutator {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) : Subgroup G :=
  Subgroup.closure {x : G | ∃ g : G, ∃ a : A, x = g * (φ a) g⁻¹}

/-- 自明作用 (φ = 1) の場合, `actionCommutator = ⊥` (各 generator = g * g⁻¹ = 1). -/
@[simp]
theorem actionCommutator_one_eq_bot {A G : Type*} [Group A] [Group G] :
    actionCommutator (1 : A →* MulAut G) = ⊥ := by
  rw [actionCommutator, Subgroup.closure_eq_bot_iff]
  rintro _ ⟨g, a, rfl⟩
  change g * (1 : MulAut G) g⁻¹ = 1
  simp

/-- **`actionCommutator φ` は φ 作用下で A-不変**.

`(φ b) (g * (φ a) g⁻¹) = (φ b) g * (φ (b * a * b⁻¹)) ((φ b) g)⁻¹` (generator → generator 写像)
が両方向で成り立つので生成集合自体が `(φ b)`-stable. `closure_of_invariant_set` で結論. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutator φ) := by
  apply OddOrder.Isaacs.Ch03.IsAInvariant.closure_of_invariant_set
  intro b
  -- generator g * (φ a) g⁻¹ → (φ b) g * (φ (b·a·b⁻¹)) ((φ b) g)⁻¹ (= 別の generator).
  have key : ∀ g : G, ∀ a : A,
      (φ b) (g * (φ a) g⁻¹) = (φ b) g * (φ (b * a * b⁻¹)) ((φ b) g)⁻¹ := by
    intro g a
    rw [map_mul (φ b)]
    congr 1
    -- (φ b) ((φ a) g⁻¹) = (φ (b·a·b⁻¹)) ((φ b) g)⁻¹
    rw [show ((φ b) g)⁻¹ = (φ b) g⁻¹ from (map_inv (φ b) g).symm,
        show φ (b * a * b⁻¹) = (φ b) * (φ a) * (φ b)⁻¹ from by rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  ext x
  refine ⟨?_, ?_⟩
  · -- (φ b) '' S ⊆ S
    rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    exact ⟨(φ b) g, b * a * b⁻¹, key g a⟩
  · -- S ⊆ (φ b) '' S: take preimage via (φ b)⁻¹
    rintro ⟨g, a, rfl⟩
    refine ⟨(φ b)⁻¹ g * (φ (b⁻¹ * a * b)) ((φ b)⁻¹ g)⁻¹,
      ⟨(φ b)⁻¹ g, b⁻¹ * a * b, rfl⟩, ?_⟩
    rw [map_mul (φ b)]
    congr 1
    · exact MulAut.apply_inv_self (M := G) (φ b) g
    -- (φ b) ((φ (b⁻¹·a·b)) ((φ b)⁻¹ g)⁻¹) = (φ a) g⁻¹
    rw [show ((φ b)⁻¹ g)⁻¹ = (φ b)⁻¹ g⁻¹ from (map_inv ((φ b)⁻¹) g).symm,
        show φ (b⁻¹ * a * b) = (φ b)⁻¹ * (φ a) * (φ b) from by rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.apply_inv_self]

/-- **`(actionCommutator φ).map inl = ⁅inl.range, inr.range⁆`** (Γ = G ⋊[φ] A 内).

Γ 経由で `actionCommutator` を Γ 内 commutator subgroup と同一視. `inl` 経由 push が
Γ 内 commutator `⁅inl.range, inr.range⁆` に一致. これと Lem 4.1 (`⁅H, K⁆ ⊴ ⟨H, K⟩`)
を組合せて `(actionCommutator φ).Normal` (G 内) を導出する経路の主補題.

**証明**: 両側 `Subgroup.closure` 形に展開し集合等式. 生成元の対応は
`⁅inl g, inr a⁆ = inl (g * (φ a) g⁻¹)` (`SemidirectProduct.commutator_inl_inr`). -/
theorem actionCommutator_map_inl
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) :
    (actionCommutator φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A) =
      ⁅(SemidirectProduct.inl : G →* G ⋊[φ] A).range,
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range⁆ := by
  rw [actionCommutator, MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    refine ⟨SemidirectProduct.inl g, ⟨g, rfl⟩, SemidirectProduct.inr a, ⟨a, rfl⟩, ?_⟩
    exact SemidirectProduct.commutator_inl_inr (φ := φ) g a
  · rintro ⟨_, ⟨g, rfl⟩, _, ⟨a, rfl⟩, rfl⟩
    refine ⟨g * (φ a) g⁻¹, ⟨g, a, rfl⟩, ?_⟩
    exact (SemidirectProduct.commutator_inl_inr (φ := φ) g a).symm

/-- Restricted-action version of `actionCommutator_map_inl`.

If `B` acts on `G` through `i : B →* A` and `φ : A →* MulAut G`, then the
`B`-action commutator maps into the same semidirect product `G ⋊[φ] A` as the
commutator of `inl(G)` with the image of `B` inside `inr(A)`. -/
theorem actionCommutator_map_inl_comp
    {A B G : Type*} [Group A] [Group B] [Group G]
    (φ : A →* MulAut G) (i : B →* A) :
    (actionCommutator (φ.comp i)).map (SemidirectProduct.inl : G →* G ⋊[φ] A) =
      ⁅(SemidirectProduct.inl : G →* G ⋊[φ] A).range,
        ((SemidirectProduct.inr : A →* G ⋊[φ] A).comp i).range⁆ := by
  rw [actionCommutator, MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨g, b, rfl⟩, rfl⟩
    refine ⟨SemidirectProduct.inl g, ⟨g, rfl⟩,
      SemidirectProduct.inr (i b), ⟨b, rfl⟩, ?_⟩
    exact SemidirectProduct.commutator_inl_inr (φ := φ) g (i b)
  · rintro ⟨_, ⟨g, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    refine ⟨g * (φ (i b)) g⁻¹, ⟨g, b, rfl⟩, ?_⟩
    exact (SemidirectProduct.commutator_inl_inr (φ := φ) g (i b)).symm

/-- Restricting the acting group can only shrink the action commutator. -/
theorem actionCommutator_comp_le
    {A B G : Type*} [Group A] [Group B] [Group G]
    (φ : A →* MulAut G) (i : B →* A) :
    actionCommutator (φ.comp i) ≤ actionCommutator φ := by
  rw [actionCommutator, Subgroup.closure_le]
  rintro _ ⟨g, b, rfl⟩
  exact Subgroup.subset_closure ⟨g, i b, rfl⟩

/-- Push-forward of the conjugation-action commutator: for `K ≤ N_Γ(P)`, the
`actionCommutator` of the conjugation action of `K` on `P` realizes the ambient subgroup
commutator `⁅P, K⁆`. -/
theorem actionCommutator_conj_map_subtype {Γ : Type*} [Group Γ] {P K : Subgroup Γ}
    (hKP : K ≤ Subgroup.normalizer (P : Set Γ)) :
    (actionCommutator ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP))).map
      P.subtype = ⁅P, K⁆ := by
  rw [actionCommutator, MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    refine ⟨(g : Γ), g.2, (a : Γ), a.2, ?_⟩
    rw [commutatorElement_def]
    have hcoe : (P.subtype
          (g * ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP)) a g⁻¹) : Γ)
        = (g : Γ) * ((a : Γ) * (g : Γ)⁻¹ * (a : Γ)⁻¹) := rfl
    rw [hcoe]
    group
  · rintro ⟨g, hg, a, ha, rfl⟩
    refine ⟨(⟨g, hg⟩ : P) *
      ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP)) ⟨a, ha⟩ ⟨g, hg⟩⁻¹,
      ⟨⟨g, hg⟩, ⟨a, ha⟩, rfl⟩, ?_⟩
    rw [commutatorElement_def]
    have hcoe : (P.subtype
          ((⟨g, hg⟩ : P) *
            ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP)) ⟨a, ha⟩
              (⟨g, hg⟩ : P)⁻¹) : Γ)
        = g * (a * g⁻¹ * a⁻¹) := rfl
    rw [hcoe]
    group

/-- Push-forward of the conjugation-action fixed points: fixed points of the conjugation
action of `K` on `P` map to `C_Γ(K) ⊓ P`. -/
theorem fixedPointsOfMulAut_conj_map_subtype {Γ : Type*} [Group Γ] {P K : Subgroup Γ}
    (hKP : K ≤ Subgroup.normalizer (P : Set Γ)) :
    (Subgroup.fixedPointsOfMulAut
        ((Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKP))).map P.subtype =
      Subgroup.centralizer (K : Set Γ) ⊓ P := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun k hk => ?_, x.2⟩
    have hfix := Subgroup.mem_fixedPointsOfMulAut.mp hx ⟨k, hk⟩
    have hcoe : k * (x : Γ) * k⁻¹ = (x : Γ) := congrArg Subtype.val hfix
    calc k * (x : Γ) = (k * x * k⁻¹) * k := by group
    _ = (x : Γ) * k := by rw [hcoe]
  · rintro ⟨hy, hyP⟩
    refine ⟨⟨y, hyP⟩, Subgroup.mem_fixedPointsOfMulAut.mpr fun a => Subtype.ext ?_, rfl⟩
    change (a : Γ) * y * (a : Γ)⁻¹ = y
    rw [hy (a : Γ) a.2]
    group

/-- **`actionCommutator φ` は G で normal subgroup**.

経路: `actionCommutator_map_inl` で `(actionCommutator φ).map inl = ⁅inl.range, inr.range⁆`,
Γ 内で `inl.range ⊔ inr.range = ⊤` (`SemidirectProduct.inl_range_sup_inr_range_eq_top`) より
Lem 4.1 系 `commutator_normal_of_sup_eq_top` で `⁅inl.range, inr.range⁆.Normal`. `inl`
injectivity で pull back (`Subgroup.Normal.of_map_injective`).

Isaacs §4C 冒頭注 (Lem 4.1 を Γ で適用) を直接実装. -/
instance actionCommutator.normal {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) :
    (actionCommutator φ).Normal := by
  refine Subgroup.Normal.of_map_injective
    (φ := (SemidirectProduct.inl : G →* G ⋊[φ] A)) SemidirectProduct.inl_injective ?_
  rw [actionCommutator_map_inl]
  exact commutator_normal_of_sup_eq_top SemidirectProduct.inl_range_sup_inr_range_eq_top

/-! ### Isaacs §4C: [G,A] の universal property (Lem 4.20, Cor 4.21) -/

/-- **Isaacs Lemma 4.20** (element form, right): `actionCommutator φ ≤ N` iff
`∀ a g, (φ a) g * g⁻¹ ∈ N`. つまり `actionCommutator φ` は
`{(φ a) g * g⁻¹ : a g}` で生成される最小の部分群.

**意味**: `N ⊴ G` が `A`-不変なら `actionCommutator ≤ N ↔ A acts trivially on G/N`
(右剰余類 `Nx` が A 不変 ↔ `(φ a) x ∈ Nx`).

**証明**: `actionCommutator` は `g * (φ a) g⁻¹ = ((φ a) g * g⁻¹)⁻¹` で生成されるので
`(φ a) g * g⁻¹` の集合と同じ subgroup を生成する. -/
theorem actionCommutator_le_iff {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) (N : Subgroup G) :
    actionCommutator φ ≤ N ↔ ∀ a : A, ∀ g : G, (φ a) g * g⁻¹ ∈ N := by
  constructor
  · intro h a g
    have h_gen : g * (φ a) g⁻¹ ∈ actionCommutator φ :=
      Subgroup.subset_closure ⟨g, a, rfl⟩
    have h_inv : (φ a) g * g⁻¹ = (g * (φ a) g⁻¹)⁻¹ := by
      rw [show (φ a) g⁻¹ = ((φ a) g)⁻¹ from map_inv (φ a) g]
      group
    rw [h_inv]
    exact Subgroup.inv_mem _ (h h_gen)
  · intro h
    rw [actionCommutator, Subgroup.closure_le]
    rintro _ ⟨g, a, rfl⟩
    have h_form : g * (φ a) g⁻¹ = ((φ a) g * g⁻¹)⁻¹ := by
      rw [show (φ a) g⁻¹ = ((φ a) g)⁻¹ from map_inv (φ a) g]
      group
    rw [h_form]
    exact Subgroup.inv_mem _ (h a g)

/-- **Isaacs Lemma 4.20** (element form, left): `actionCommutator φ ≤ N` iff
`∀ a g, g⁻¹ * (φ a) g ∈ N`. 左剰余類 `xN` 形.

**意味**: 左剰余類 `xN` が `A` 不変 ↔ `(φ a) x ∈ xN` ↔ `x⁻¹ * (φ a) x ∈ N`. -/
theorem actionCommutator_le_iff_left {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) (N : Subgroup G) :
    actionCommutator φ ≤ N ↔ ∀ a : A, ∀ g : G, g⁻¹ * (φ a) g ∈ N := by
  rw [actionCommutator_le_iff]
  -- ∀ a g, (φ a) g * g⁻¹ ∈ N ↔ ∀ a g, g⁻¹ * (φ a) g ∈ N
  constructor
  · intro h a x
    have h' := h a x⁻¹
    rw [show (φ a) x⁻¹ = ((φ a) x)⁻¹ from map_inv (φ a) x] at h'
    -- h' : ((φ a) x)⁻¹ * x⁻¹⁻¹ ∈ N
    have h_eq : ((φ a) x)⁻¹ * x⁻¹⁻¹ = (x⁻¹ * (φ a) x)⁻¹ := by group
    rw [h_eq] at h'
    simpa using Subgroup.inv_mem _ h'
  · intro h a x
    have h' := h a x⁻¹
    rw [show (φ a) x⁻¹ = ((φ a) x)⁻¹ from map_inv (φ a) x] at h'
    have h_eq : x⁻¹⁻¹ * ((φ a) x)⁻¹ = ((φ a) x * x⁻¹)⁻¹ := by group
    rw [h_eq] at h'
    simpa using Subgroup.inv_mem _ h'

/-- `actionCommutator φ = ⊥` iff `A` acts trivially on `G` (`∀ a g, (φ a) g = g`).

Lem 4.20 left form を `N = ⊥` で特殊化. BaerMul wrapper への翻訳に基本. -/
theorem actionCommutator_eq_bot_iff_acts_trivially {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) :
    actionCommutator φ = ⊥ ↔ ∀ a : A, ∀ g : G, (φ a) g = g := by
  rw [eq_bot_iff, actionCommutator_le_iff_left]
  refine ⟨fun h a g => ?_, fun h a g => ?_⟩
  · have hg := h a g
    rw [Subgroup.mem_bot, inv_mul_eq_one] at hg
    exact hg.symm
  · rw [Subgroup.mem_bot, h a g, inv_mul_cancel]

/-- **A-不変部分群への作用制限**: `φ : A →* MulAut G` + `IsAInvariant φ H` から
`A →* MulAut ↥H` を構成. 関数本体は `(φ a)` を `H` に制限したもの.

Thm 4.36 induction で IH を `[G, A] < G` 等の subgroup に適用するために必要. -/
def OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom {A G : Type*} [Group A] [Group G]
    {φ : A →* MulAut G} {H : Subgroup G}
    (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) : A →* MulAut H where
  toFun a := {
    toFun := fun h => ⟨(φ a) h.val, hH.smul_mem a h.property⟩
    invFun := fun h => ⟨(φ a)⁻¹ h.val, hH.inv_smul_mem a h.property⟩
    left_inv := fun h => Subtype.ext (by
      change (φ a)⁻¹ ((φ a) h.val) = h.val
      simp)
    right_inv := fun h => Subtype.ext (by
      change (φ a) ((φ a)⁻¹ h.val) = h.val
      simp)
    map_mul' := fun x y => Subtype.ext (map_mul (φ a) x.val y.val)
  }
  map_one' := by
    ext h
    change ((φ 1 : MulAut G) h.val) = h.val
    simp
  map_mul' a b := by
    ext h
    change ((φ (a * b) : MulAut G) h.val) = ((φ a) ((φ b) h.val))
    rw [map_mul]; rfl

@[simp] lemma OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom_apply_val
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) (a : A) (h : H) :
    ((OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH a) h).val =
      (φ a) h.val := rfl

/-- If `H` is A-invariant and `K` is characteristic in `H`, then the image of `K`
inside `G` is A-invariant. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.map_subtype_of_characteristic
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H)
    {K : Subgroup H} [K.Characteristic] :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (K.map H.subtype) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a x hx
  rcases hx with ⟨k, hk, rfl⟩
  let ψ : A →* MulAut H := OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH
  have hK_map : K.map (ψ a).toMonoidHom = K :=
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) (ψ a)
  have hk' : (ψ a) k ∈ K := by
    have : (ψ a) k ∈ K.map (ψ a).toMonoidHom := ⟨k, hk, rfl⟩
    rwa [hK_map] at this
  exact ⟨(ψ a) k, hk', rfl⟩

/-- **A-不変正規部分群で割った商群への誘導作用**.

`N` が `φ` で不変なら, 各 `φ a` は `G/N` の自己同型を誘導する. -/
noncomputable def _root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) : A →* MulAut (G ⧸ N) where
  toFun a := QuotientGroup.congr N N (φ a) (by
    change N.map (φ a).toMonoidHom = N
    exact hN a)
  map_one' := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro g
    simp
  map_mul' a b := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro g
    simp [map_mul]

@[simp] lemma _root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk'
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) (a : A) (g : G) :
    (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN a)
        (QuotientGroup.mk' N g) =
      QuotientGroup.mk' N ((φ a) g) := rfl

@[simp] lemma _root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) (a : A) (g : G) :
    (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN a) (g : G ⧸ N) =
      ((φ a) g : G ⧸ N) := rfl

/- Note (issue 0106): `quotientMulAutHom` and its two `simp` lemmas were originally declared with
a qualified head *inside* `namespace OddOrder.Isaacs.Ch04`, yielding the doubled real name
`OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.…`.  They now live at the intended single namespace
(`_root_.` head above).  No deprecated aliases are kept: alias constants under the doubled name
would make every qualified reference ambiguous in files that `open OddOrder.Isaacs.Ch04`
file-wide.  Downstream consumers of the old doubled name: drop the `OddOrder.Isaacs.Ch04.`
prefix. -/

/-- **Isaacs Corollary 3.28 / BG Proposition 1.5(d), subgroup form**: for a coprime
action `φ : A → MulAut G` and an `A`-invariant normal subgroup `N`, the fixed points of
the induced action on `G/N` are exactly the image of the fixed points in `G`. -/
theorem fixedPointsOfMulAut_quotientMulAutHom_eq_map
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) (hSolv : IsSolvable A ∨ IsSolvable G)
    {N : Subgroup G} [N.Normal] (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) :
    Subgroup.fixedPointsOfMulAut (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) =
      (Subgroup.fixedPointsOfMulAut φ).map (QuotientGroup.mk' N) := by
  refine le_antisymm ?_ ?_
  · intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [Subgroup.mem_fixedPointsOfMulAut] at hq
    have hg_fix : ∀ a : A, ∃ n ∈ N, (φ a) g = g * n := by
      intro a
      have hga := hq a
      rw [_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk',
        QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hga
      exact ⟨g⁻¹ * (φ a) g, by simpa using N.inv_mem hga, by group⟩
    obtain ⟨c, hc_fix, n, hn, hcn⟩ := coprime_fixedPoints_quotient hCop hSolv hN hg_fix
    refine Subgroup.mem_map.mpr ⟨c, Subgroup.mem_fixedPointsOfMulAut.mpr hc_fix, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hcn]
    simpa using N.inv_mem hn
  · rw [Subgroup.map_le_iff_le_comap]
    intro c hc
    rw [Subgroup.mem_fixedPointsOfMulAut] at hc
    rw [Subgroup.mem_comap, Subgroup.mem_fixedPointsOfMulAut]
    intro a
    rw [_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk', hc a]

/-- An `A`-invariant subgroup maps to an invariant subgroup in an
`A`-invariant quotient. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.map_quotient
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N)
    {H : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) :
    OddOrder.Isaacs.Ch03.IsAInvariant
      (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN)
      (H.map (QuotientGroup.mk' N)) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a q hq
  rw [Subgroup.mem_map] at hq ⊢
  obtain ⟨g, hg, rfl⟩ := hq
  exact ⟨(φ a) g, hH.smul_mem a hg, by
    rw [_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']⟩

/-- The preimage of an invariant subgroup of an `A`-invariant quotient is
invariant in the original group. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.comap_quotient
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N)
    {Y : Subgroup (G ⧸ N)}
    (hY : OddOrder.Isaacs.Ch03.IsAInvariant
      (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) Y) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (Y.comap (QuotientGroup.mk' N)) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a g hg
  rw [Subgroup.mem_comap] at hg ⊢
  rw [← _root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
  exact hY.smul_mem a hg

/-- Pull back a quotient Hall subgroup containing the image of `K`.

The preimage is invariant, contains `K`, and has `π`-free index. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.exists_comap_quotient_hall
    {G A : Type*} [Group G] [Finite G] [Group A] {φ : A →* MulAut G}
    {π : Set ℕ} {K M : Subgroup G} [M.Normal]
    (hM : OddOrder.Isaacs.Ch03.IsAInvariant φ M)
    {Hbar : Subgroup (G ⧸ M)}
    (hHbar_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup π Hbar)
    (hHbar_inv : OddOrder.Isaacs.Ch03.IsAInvariant
      (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hM) Hbar)
    (hK_image_le : K.map (QuotientGroup.mk' M) ≤ Hbar) :
    ∃ H : Subgroup G,
      OddOrder.Isaacs.Ch03.IsAInvariant φ H ∧ K ≤ H ∧
        (∀ p ∈ H.index.primeFactors, p ∉ π) ∧
        H = Hbar.comap (QuotientGroup.mk' M) := by
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let H : Subgroup G := Hbar.comap q
  refine ⟨H, ?_, ?_, ?_, rfl⟩
  · exact OddOrder.Isaacs.Ch03.IsAInvariant.comap_quotient hM hHbar_inv
  · intro k hk
    change q k ∈ Hbar
    exact hK_image_le (by
      rw [Subgroup.mem_map]
      exact ⟨k, hk, rfl⟩)
  · have hindex : H.index = Hbar.index :=
      Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective (N := M))
    rw [hindex]
    exact hHbar_hall.2

/-- The action commutator descends to quotients as the image of the action commutator. -/
theorem actionCommutator_quotient_eq_map
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) :
    actionCommutator (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) =
      (actionCommutator φ).map (QuotientGroup.mk' N) := by
  rw [actionCommutator, actionCommutator, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨q, a, rfl⟩
    refine QuotientGroup.induction_on q ?_
    intro g
    refine ⟨g * (φ a) g⁻¹, ⟨g, a, rfl⟩, ?_⟩
    simp [map_mul]
  · rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk' N g, a, by simp [map_mul]⟩

/-- If `[G,A] ≤ N`, then the induced action on `G/N` is trivial. -/
theorem actionCommutator_quotient_eq_bot_of_le
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N)
    (h_le : actionCommutator φ ≤ N) :
    actionCommutator (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) = ⊥ := by
  rw [actionCommutator_eq_bot_iff_acts_trivially]
  intro a q
  refine QuotientGroup.induction_on q ?_
  intro g
  rw [_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply]
  rw [QuotientGroup.eq]
  simpa [mul_inv_rev] using
    N.inv_mem ((actionCommutator_le_iff_left φ N).mp h_le a g)

/-- If `R` normalizes `K` and `⁅K, R⁆ ≤ F(K)`, then the conjugation action of `R`
on `K/F(K)` fixes every quotient element. -/
theorem fixedPoints_quotient_eq_top_of_commutator_le_fitting
    {G : Type*} [Group G] [Finite G] {K R : Subgroup G} [K.Normal]
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hcomm : ⁅K, R⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype) :
    Subgroup.fixedPointsOfMulAut
      (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom
        (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic
          (H := OddOrder.Isaacs.Ch01.fitting ↥K)
          ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK)))) = ⊤ := by
  set φ : R →* MulAut K := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK)
    with hφ
  have hFinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (OddOrder.Isaacs.Ch01.fitting ↥K) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
  have hac_le : actionCommutator φ ≤ OddOrder.Isaacs.Ch01.fitting ↥K := by
    have h := actionCommutator_conj_map_subtype hRK
    rw [← h] at hcomm
    exact Subgroup.map_le_map_iff_of_injective K.subtype_injective |>.mp hcomm
  have hbot : actionCommutator (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hFinv) =
      ⊥ := by
    rw [actionCommutator_quotient_eq_map, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hac_le
  rw [Subgroup.eq_top_iff']
  intro g
  rw [Subgroup.mem_fixedPointsOfMulAut]
  intro a
  exact (actionCommutator_eq_bot_iff_acts_trivially _).mp hbot a g

/-- **Isaacs Corollary 4.21**: For `H ≤ G`, the following are equivalent:
(a) `∀ a x, (φ a) x ∈ Hx` (right coset is A-invariant in element form);
(b) `∀ a x, (φ a) x ∈ xH` (left coset is A-invariant in element form);
(c) `actionCommutator φ ≤ H`.

Element-level: (a) = `∀ a x, (φ a) x * x⁻¹ ∈ H`, (b) = `∀ a x, x⁻¹ * (φ a) x ∈ H`. -/
theorem actionCommutator_le_iff_TFAE {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) (H : Subgroup G) :
    List.TFAE [
      actionCommutator φ ≤ H,
      ∀ a : A, ∀ x : G, (φ a) x * x⁻¹ ∈ H,
      ∀ a : A, ∀ x : G, x⁻¹ * (φ a) x ∈ H] := by
  tfae_have 1 ↔ 2 := actionCommutator_le_iff φ H
  tfae_have 1 ↔ 3 := actionCommutator_le_iff_left φ H
  tfae_finish

/-- **Isaacs Cor 4.21 corollary**: If `actionCommutator φ ≤ H`, then `H` is `A`-invariant.
(Because `(φ a) h = ((φ a) h * h⁻¹) * h` and the first factor is in `H` by Lem 4.20.) -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.of_actionCommutator_le
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {H : Subgroup G} (h_le : actionCommutator φ ≤ H) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ H := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a h hh
  -- (φ a) h ∈ H. Use: (φ a) h = ((φ a) h * h⁻¹) * h, both factors ∈ H.
  have h1 : (φ a) h * h⁻¹ ∈ H := (actionCommutator_le_iff φ H).mp h_le a h
  have h_eq : (φ a) h = ((φ a) h * h⁻¹) * h := by group
  rw [h_eq]
  exact H.mul_mem h1 hh

/-- **Isaacs Lemma 4.25** ⭐: If `A` acts trivially on `actionCommutator φ` (i.e.,
`[G, A, A] = 1`), then `actionCommutator φ` is abelian.

**証明戦略** (Isaacs p.135): Γ = G ⋊[φ] A 内で Three-subgroups lemma を適用.
- `H_Γ := ⁅inl(G).range, inr(A).range⁆` (Γ-内 commutator) `= inl(actionCommutator)`
  (`actionCommutator_map_inl`).
- 仮説 ⇒ Γ で `⁅H_Γ, inr(A).range⁆ = ⊥` (各生成元 `⁅inl k, inr a⁆ = inl(k * (φ a) k⁻¹)`
  で `(φ a) k = k` から `= inl 1 = 1`).
- `H_Γ.Normal` (Lem 4.1 系) ⇒ `⁅H_Γ, inl(G).range⁆ ≤ H_Γ` ⇒ 二重交換子も `⊥`.
- Three-subgroups で `⁅⁅inl(G).range, inr(A).range⁆, H_Γ⁆ = ⁅H_Γ, H_Γ⁆ = ⊥`.
- `inl` 単射で pull back. -/
theorem actionCommutator_commutator_eq_bot_of_acts_trivially
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G)
    (h_triv : actionCommutator φ ≤ Subgroup.fixedPointsOfMulAut φ) :
    ⁅actionCommutator φ, actionCommutator φ⁆ = ⊥ := by
  -- Setup: work in Γ = G ⋊[φ] A
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  set H_Γ : Subgroup (G ⋊[φ] A) := ⁅XG, YA⁆ with hHΓ_def
  -- H_Γ = inl(actionCommutator)
  have h_HΓ_eq : (actionCommutator φ).map SemidirectProduct.inl = H_Γ :=
    actionCommutator_map_inl φ
  -- H_Γ is Normal in Γ (Lem 4.1 系 via inl ⊔ inr = ⊤)
  haveI h_HΓ_normal : H_Γ.Normal := commutator_normal_of_sup_eq_top
    SemidirectProduct.inl_range_sup_inr_range_eq_top
  -- Step 1: ⁅H_Γ, YA⁆ = ⊥ in Γ (from hypothesis, via generator computation)
  have h_step1 : ⁅H_Γ, YA⁆ = ⊥ := by
    rw [← h_HΓ_eq, eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨k, hk, rfl⟩ _ ⟨a, rfl⟩
    -- Goal: ⁅inl k, inr a⁆ ∈ ⊥
    rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
    -- Goal: inl (k * (φ a) k⁻¹) = 1
    have h_fix : (φ a) k = k := h_triv hk a
    rw [show (φ a) k⁻¹ = ((φ a) k)⁻¹ from map_inv (φ a) k, h_fix, mul_inv_cancel]
    exact map_one _
  -- Step 2: ⁅⁅H_Γ, XG⁆, YA⁆ = ⊥ (via H_Γ.Normal ⇒ ⁅H_Γ, XG⁆ ≤ H_Γ, then Step 1)
  have h_step2 : ⁅⁅H_Γ, XG⁆, YA⁆ = ⊥ := by
    have h_inner_le : ⁅H_Γ, XG⁆ ≤ H_Γ := Subgroup.commutator_le_left H_Γ XG
    exact le_bot_iff.mp <|
      le_trans (Subgroup.commutator_mono h_inner_le le_rfl) h_step1.le
  -- Step 3: Three-subgroups in Γ
  -- With H₁ = XG, H₂ = YA, H₃ = H_Γ:
  -- ⁅⁅H₂, H₃⁆, H₁⁆ = ⁅⁅YA, H_Γ⁆, XG⁆ = ⁅⊥, XG⁆ = ⊥ (step 1 + commutator_comm)
  -- ⁅⁅H₃, H₁⁆, H₂⁆ = ⁅⁅H_Γ, XG⁆, YA⁆ = ⊥ (step 2)
  -- Conclude: ⁅⁅H₁, H₂⁆, H₃⁆ = ⁅⁅XG, YA⁆, H_Γ⁆ = ⁅H_Γ, H_Γ⁆ = ⊥
  have h_step3 : ⁅H_Γ, H_Γ⁆ = ⊥ := by
    have h_a : ⁅⁅YA, H_Γ⁆, XG⁆ = ⊥ := by
      rw [Subgroup.commutator_comm YA H_Γ, h_step1, Subgroup.commutator_bot_left]
    have h_b : ⁅⁅H_Γ, XG⁆, YA⁆ = ⊥ := h_step2
    have h_three := Subgroup.commutator_commutator_eq_bot_of_rotate h_a h_b
    -- h_three : ⁅⁅XG, YA⁆, H_Γ⁆ = ⊥
    rwa [← hHΓ_def] at h_three
  -- Step 4: Pull back ⁅H_Γ, H_Γ⁆ = ⊥ via inl injectivity to actionCommutator
  have h_inl_comm : (⁅actionCommutator φ, actionCommutator φ⁆).map
      SemidirectProduct.inl = ⁅H_Γ, H_Γ⁆ := by
    rw [Subgroup.map_commutator, h_HΓ_eq]
  have h_map_bot : (⁅actionCommutator φ, actionCommutator φ⁆).map
      SemidirectProduct.inl = ⊥ := h_inl_comm.trans h_step3
  exact (Subgroup.map_eq_bot_iff_of_injective ⁅actionCommutator φ, actionCommutator φ⁆
        SemidirectProduct.inl_injective).mp h_map_bot

end

/-! ### Isaacs Cor 4.12, 一般括弧形 (weight-n commutator words, p. 124)

既存の left-associated 元交換子形 (`iterLeftCommutator_mem_lowerCentralSeries_add`) に
対し, 書籍の Cor 4.12 本来の形 = **任意括弧付けの部分群交換子** `[[G,G],[G,[G,G]]]` 等が
`γₙ(G)` に含まれることを, 交換子語の二分木で定式化する. -/

/-- **重み付き交換子語** (Isaacs p.124): `G` のコピーの任意括弧付け交換子を表す二分木.
`leaf` = `G` 自身 (weight 1), `node l r` = `⁅l, r⁆`. -/
inductive CommutatorWord : Type
  | leaf : CommutatorWord
  | node : CommutatorWord → CommutatorWord → CommutatorWord

namespace CommutatorWord

/-- 語の重み = 葉 (`G` のコピー) の数. -/
def weight : CommutatorWord → ℕ
  | leaf => 1
  | node l r => l.weight + r.weight

/-- 語の群 `G` での評価: 葉は `⊤`, 節は部分群交換子. -/
def eval (G : Type*) [Group G] : CommutatorWord → Subgroup G
  | leaf => ⊤
  | node l r => ⁅l.eval G, r.eval G⁆

theorem one_le_weight : ∀ w : CommutatorWord, 1 ≤ w.weight
  | leaf => le_refl 1
  | node l _ => le_trans (one_le_weight l) (Nat.le_add_right _ _)

/-- **Isaacs Cor 4.12 (一般括弧形)**: 任意の weight-`n` 交換子語の `G` での評価は
`γₙ(G)` (mathlib 添字では `(⊤ : Subgroup G).lowerCentralSeries (n-1)`) に含まれる.
帰納法 + Thm 4.11 (`commutator_lowerCentralSeries_le`) そのまま (書籍 p.124). -/
theorem eval_le_lowerCentralSeries (G : Type*) [Group G] :
    ∀ w : CommutatorWord, w.eval G ≤ (⊤ : Subgroup G).lowerCentralSeries (w.weight - 1)
  | leaf => le_of_eq rfl
  | node l r => by
    calc (node l r).eval G = ⁅l.eval G, r.eval G⁆ := rfl
      _ ≤ ⁅(⊤ : Subgroup G).lowerCentralSeries (l.weight - 1),
            (⊤ : Subgroup G).lowerCentralSeries (r.weight - 1)⁆ :=
          Subgroup.commutator_mono (eval_le_lowerCentralSeries G l)
            (eval_le_lowerCentralSeries G r)
      _ ≤ (⊤ : Subgroup G).lowerCentralSeries ((l.weight - 1) + (r.weight - 1) + 1) :=
          commutator_lowerCentralSeries_le _ _
      _ = (⊤ : Subgroup G).lowerCentralSeries ((node l r).weight - 1) := by
          have h1 := one_le_weight l
          have h2 := one_le_weight r
          congr 1
          change l.weight - 1 + (r.weight - 1) + 1 = l.weight + r.weight - 1
          omega

end CommutatorWord

end OddOrder.Isaacs.Ch04
