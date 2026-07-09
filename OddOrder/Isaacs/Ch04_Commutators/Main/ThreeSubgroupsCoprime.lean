import OddOrder.Isaacs.Ch04_Commutators.Main.CommutatorBasics

/-!
# Isaacs §4B-§4D 前半 — three subgroups, Mann, coprime action, [G,A] (pp. 122-141)

Split from the former monolithic `OddOrder.Isaacs.Ch04_Commutators.Main` (directory split, issue 0103).
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

private theorem opCore_eq_bot_of_mulEquiv
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (e : G ≃* H)
    (hG : OddOrder.Isaacs.Ch01.opCore p G = ⊥) :
    OddOrder.Isaacs.Ch01.opCore p H = ⊥ := by
  rw [← oPiCore_singleton_eq_opCore (G := H) p,
    ← OddOrder.Isaacs.Ch03.oPiCore.map_eq_of_mulEquiv ({p} : Set ℕ) e,
    oPiCore_singleton_eq_opCore (G := G) p, hG, Subgroup.map_bot]

/-- In a finite abelian group with trivial `O_p`, every prime divisor is different from `p`. -/
private theorem isPiGroup_compl_top_of_isMulCommutative_opCore_eq_bot
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

private lemma opCore_quotient_opCore_eq_bot {G : Type*} [Group G] [Finite G]
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

private lemma subgroup_card_lt_card_of_ne_top
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} (h_ne : H ≠ ⊤) :
    Nat.card ↥H < Nat.card G := by
  have h_dvd : Nat.card ↥H ∣ Nat.card G :=
    ⟨H.index, by rw [mul_comm, H.index_mul_card]⟩
  have h_le' : Nat.card ↥H ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos h_dvd
  have h_ne' : Nat.card ↥H ≠ Nat.card G := fun heq =>
    h_ne (Subgroup.eq_top_of_card_eq _ heq)
  exact Nat.lt_of_le_of_ne h_le' h_ne'

/-- A finite group is generated by all of its Sylow subgroups. -/
private lemma iSup_sylow_eq_top {M : Type*} [Group M] [Finite M] :
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
  show g * (1 : MulAut G) g⁻¹ = 1
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
      show (φ a)⁻¹ ((φ a) h.val) = h.val
      simp)
    right_inv := fun h => Subtype.ext (by
      show (φ a) ((φ a)⁻¹ h.val) = h.val
      simp)
    map_mul' := fun x y => Subtype.ext (map_mul (φ a) x.val y.val)
  }
  map_one' := by
    ext h
    show ((φ 1 : MulAut G) h.val) = h.val
    simp
  map_mul' a b := by
    ext h
    show ((φ (a * b) : MulAut G) h.val) = ((φ a) ((φ b) h.val))
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
noncomputable def OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom
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

@[simp] lemma OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk'
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) (a : A) (g : G) :
    (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN a)
        (QuotientGroup.mk' N g) =
      QuotientGroup.mk' N ((φ a) g) := rfl

@[simp] lemma OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) (a : A) (g : G) :
    (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN a) (g : G ⧸ N) =
      ((φ a) g : G ⧸ N) := rfl

/-- **Isaacs Corollary 3.28 / BG Proposition 1.5(d), subgroup form**: for a coprime
action `φ : A → MulAut G` and an `A`-invariant normal subgroup `N`, the fixed points of
the induced action on `G/N` are exactly the image of the fixed points in `G`. -/
theorem fixedPointsOfMulAut_quotientMulAutHom_eq_map
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) (hSolv : IsSolvable A ∨ IsSolvable G)
    {N : Subgroup G} [N.Normal] (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) :
    Subgroup.fixedPointsOfMulAut (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) =
      (Subgroup.fixedPointsOfMulAut φ).map (QuotientGroup.mk' N) := by
  refine le_antisymm ?_ ?_
  · intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [Subgroup.mem_fixedPointsOfMulAut] at hq
    have hg_fix : ∀ a : A, ∃ n ∈ N, (φ a) g = g * n := by
      intro a
      have hga := hq a
      rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk',
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
    rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk', hc a]

/-- An `A`-invariant subgroup maps to an invariant subgroup in an
`A`-invariant quotient. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.map_quotient
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N)
    {H : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) :
    OddOrder.Isaacs.Ch03.IsAInvariant
      (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN)
      (H.map (QuotientGroup.mk' N)) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a q hq
  rw [Subgroup.mem_map] at hq ⊢
  obtain ⟨g, hg, rfl⟩ := hq
  exact ⟨(φ a) g, hH.smul_mem a hg, by
    rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']⟩

/-- The preimage of an invariant subgroup of an `A`-invariant quotient is
invariant in the original group. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.comap_quotient
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N)
    {Y : Subgroup (G ⧸ N)}
    (hY : OddOrder.Isaacs.Ch03.IsAInvariant
      (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) Y) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (Y.comap (QuotientGroup.mk' N)) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a g hg
  rw [Subgroup.mem_comap] at hg ⊢
  rw [← OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
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
      (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hM) Hbar)
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
    actionCommutator (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) =
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
    actionCommutator (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) = ⊥ := by
  rw [actionCommutator_eq_bot_iff_acts_trivially]
  intro a q
  refine QuotientGroup.induction_on q ?_
  intro g
  rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply]
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
      (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom
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
  have hbot : actionCommutator (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hFinv) =
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
private lemma iterCommutator_add (E X : Subgroup G) (j k : ℕ) :
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
        OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hU_inv
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
        change (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hU_inv a)
            (QuotientGroup.mk' U_G g) = QuotientGroup.mk' U_G g
        rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
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
          OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hF_inv
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
          change (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hF_inv a)
              (QuotientGroup.mk' F g) = QuotientGroup.mk' F g
          rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
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
