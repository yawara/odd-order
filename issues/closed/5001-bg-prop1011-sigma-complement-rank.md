---
id: 5001
slug: bg-prop1011-sigma-complement-rank
title: "BG Prop 10.11 sigma_complement_rank_le_one (a)(b)(c) (forward-conditional)"
created: 2026-06-10
---

# BG Prop 10.11 sigma_complement_rank_le_one (a)(b)(c) (forward-conditional)

## 背景

`OddOrder/BG/Ch3_MaximalSubgroups/S10_LocalLemmas.lean:451` (`sigma_complement_rank_le_one`) =
§10 で残る sorry (Lemma 10.13 を除く D-lane 対象)。**(b) は Prop 10.10 (`normalizer_factorization`,
commit `de75651e` で完成) を使う** ので依存解消済 → 着手可能。

mmd 出典: `references/bg/local-analysis.mmd` L2856-2880 (Prop 10.11 statement + proof)。

## statement (既存・変更不要)

`M ∈ ℳ`, `K` を `M` の `σ(M)'`-部分群 (`Subgroup.IsPiSubgroup (sigma M)ᶜ K`, `K ≤ M`) とすると:
- (a) `K ∉ 𝒰` (`¬ IsUniquelyMaximal K`)
- (b) `r(C_K(M_σ)) ≤ 1` (`rank ↥(C_G(M_σ) ⊓ K) ≤ 1`)
- (c) `C_K(M_σ) ∩ M'` は cyclic で `M` に normal
  (`IsCyclic ↥(C_G(M_σ) ⊓ K ⊓ M') ∧ M ≤ N_G(C_G(M_σ) ⊓ K ⊓ M')`)

原典 (d) は別 theorem `sigma_complement_commutator_cyclic_normal` に分離済 (本 issue 対象外)。

## BG 証明 (mmd L2860-2880)

- **(a)**: `E` を `K` を含む Hall `σ(M)'`-subgroup of `M`。`p` = `|E|` の最大素因子。
  `α(M) ⊆ σ(M)` ゆえ `r(E) ≤ 2`。**Theorem 4.20** で `P = O_p(E)` が `E` の (ゆえ `M` の)
  Sylow `p`。`p ∉ σ(M)` ⟹ `N_G(P) ⊄ M`。よって `K ⊆ E ⊆ M ∩ N_G(P)` から `K ∉ 𝒰`。
- **(b)**: `r_p(C_K(M_σ)) ≥ 2` なる `p` を仮定 (背理法)。`A ∈ ℰ_p²(C_K(M_σ))`, `q ∈ σ(M)`,
  `Q` = Sylow q of `M_σ`。すると `Q ∈ ℋ_G*(A;q)`, `q ∈ π(C_G(A))`, `N_G(Q) ⊆ M`。
  (a) で `A ∉ 𝒰` ⟹ **Uniqueness Theorem** で `r(C_G(A)) ≤ 2` かつ `A ∈ ℰ_p*(G)`。
  `M_α ⊆ M_σ ⊆ C_G(A)` ⟹ `M_α = 1`。**Theorem 10.2** で `M'/M_α` nilpotent ⟹ `M'` nilpotent。
  **Proposition 10.10** ✅ で ある Sylow p `P` が `N_G(Q)' ⊆ M'` に入る ⟹ `P = O_p(M') ⊴ M`,
  `M = N_G(P)`, `p ∈ σ(M)`。しかし `p ∈ σ(K) ⊆ σ(M)'`。矛盾。
- **(c)**: (b) を `Z = O_{σ(M)'}(F(M))` に適用 (`[Z,M_σ] ⊆ Z ∩ M_σ = 1`) ⟹ `Z` cyclic。
  `M' ⊆ C_M(Z)` かつ `C_K(M_σ) ∩ M' ⊆ C_M(M_σ Z) ⊆ C_M(F(M)) ⊆ F(M)`。

## やること / 依存の現状

- [x] **(a)**: **Theorem 4.20** (「`E` 可解, `r(E)≤2`, `p` 最大素因子 ⟹ `O_p(E)` が Sylow p」)
      の正確な Lean 形を同定。`S04g_Thm418.lean` に 4.20(c) machinery はあるが capstone 形を要確認。
      `α(M) ⊆ σ(M)` (`alpha_subset_sigma`) で `r(E) ≤ 2`。`N_G(P) ⊄ M` は `p ∉ σ(M)` から。
- [x] **(b)**: **Uniqueness Theorem** の必要方向 = 「`A ∉ 𝒰` ⟹ `r(C_G(A)) ≤ 2` ∧ `A ∈ ℰ_p*(G)`」。
      S09 capstone は対偶 (`r ≥ 3 ⟹ 𝒰`)。`isUniquelyMaximal_of_three_le_rank_of_lt_top` の対偶 +
      `A ∈ ℰ_p*` の導出を要確認。**Thm 10.2 の M_α 形**: 現状 `derivedQuotientMbeta_isNilpotent`
      は M'/M_β。M_α=1 のケースでは M_β=M_α=1 で M' nilpotent が出るか要確認 (or M_α 版を別途)。
      Prop 10.10 適用部は `normalizer_factorization` (✅) を直接呼ぶ。
- [x] **(c)**: `Z = O_{σ(M)'}(F(M))`, `[Z, M_σ] ⊆ Z ⊓ M_σ = 1`, Fitting/centralizer 包含チェーン。
- [x] forward-axiom island (Prop 10.10 / Cor 10.7 経由) を AxiomsCheck に登録 (同 keystone island)。

## 完了条件

`sigma_complement_rank_le_one` の sorry が消え、leaf + full build green、`#print axioms` =
standard 3 + `pLengthOne_commutator_of_zgroupCentralizer` +
`exists_prime_orderOf_zgroupCentralizer_of_complement` ちょうど。

## 参照

- Prop 10.10 完成: commit `de75651e`, `notes/bg/s10_spine_blockers.md` 2026-06-10 更新節。
- §10 残 sorry: 本 Prop 10.11 + Lemma 10.13 (`nonabelian_pSubgroup_rankTwo_elemAbelian_structure`,
  `S10_LocalLemmas.lean:1063`, group-level Additive diamond で D 対象外)。

## 実装ブループリント (2026-06-10 調査, 全依存 exact-lemma 確定)

Prop 10.11 は (a)(b)(c) 束ねた大型定理 (Prop 10.10 同等規模)。全依存を exact lemma 名まで同定済み。
実装は純粋 assembly。**(a)→(b)→(c) の順** (内部依存)。part (a) は独立 lemma
`sigma_complement_not_isUniquelyMaximal` に切り出すのが良い ((b) でも使う)。

### 確定した依存 (すべて実在・検証済)

| 用途 | lemma | 場所 |
|---|---|---|
| Hall σ'-subgroup ⊇ K (φ=1 trivial action) | `OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall` | S01_Solvable:1404 |
| Thm 4.20(c) char Sylow series | `Ch1.S05.exists_characteristicSylowSeriesPackage_of_rank_fitting_le_two` | S05:1741付近 |
| 正規 Sylow 抽出 | `Ch1.S04.CharacteristicSylowSeriesPackage.exists_terminal_normal_sylow` | S04g:1863 |
| Thm 4.20(a) `M'⊆F(M)` (M_α=1⟹M' nilpotent) | `Ch1.S05.derived_le_fitting_of_rank_fitting_le_two` | S05:3826 |
| E≤N_G(R) (E内正規Sylowの像) | `Isaacs.Ch07...map_le_normalizer_map_of_normal` (φ:=E.subtype, P:=⊤, L:=Q) | S7A2:196 |
| K⊆2極大⟹¬𝒰 | `Ch2.S09.not_isUniquelyMaximal_of_le_inf_distinct_maximals` | S09_Theorem91:399 |
| pRank>0⟹p∈π | `Ch2.S09.mem_primeFactors_card_of_pos_pRank` | S09_Theorem91:589 |
| R≤M を Sylow q ↥M に lift | `sylow_subgroupOf_of_le` (本ファイル private:30) | S10_LocalLemmas:30 |
| α(M)⊆σ(M) | `alpha_subset_sigma` | S10_HallStructure |
| Msigma ne_bot / M_α≤M_σ≤M' | `Msigma_ne_bot`, `Malpha_le_Msigma`, `Msigma_le_derived` | S10 |

**⚠ repo の Thm 10.2 (`isHall_Msigma_Malpha`) は「M'/M_α nilpotent」を含まない** (docstring「追加予定」)。
part (b) は M_α=1 のケースなので **Thm 4.20(a)** (`derived_le_fitting_of_rank_fitting_le_two`,
M_α=1⟹rank M≤2⟹M' ⊆ F(M) nilpotent) で代替する。

**🔨 要新規 sub-lemma**: `¬ IsUniquelyMaximal (⊥ : Subgroup G)` (E=⊥ ⟺ K=⊥ ⟺ M が σ(M)-群 のケース)。
「unique maximal ⟹ G cyclic ⟹ solvable, hG.notSolvable と矛盾」(~20 行)。または下流で K≠⊥ が
保証されるなら回避可 (要確認)。

### part (a) コードスケッチ (検証済の前半 ~50 行; 後半は Sylow lift + 𝒰)

```lean
theorem sigma_complement_not_isUniquelyMaximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {K : Subgroup G} (hKM : K ≤ M)
    (hKpi : Subgroup.IsPiSubgroup (sigma M)ᶜ K) : ¬ IsUniquelyMaximal K := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- (K=⊥ なら ¬𝒰⊥ で別処理。以下 K≠⊥ ⟹ E≠⊥)
  -- Step 1: Hall σ'-subgroup E ⊇ K (φ=1).
  have hKsubMpi : Ch03.Subgroup.IsPiGroup (sigma M)ᶜ (K.subgroupOf M) := fun p hp => by
    have hpK : p ∈ (Nat.card ↥K).primeFactors := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp
    exact hKpi p hpK
  let φ : Unit →* MulAut ↥M := 1
  have hKinv : Ch03.IsAInvariant φ (K.subgroupOf M) := by
    rw [Ch03.isAInvariant_iff_smul_mem]; intro _ x hx; simpa [φ] using hx
  obtain ⟨H, hHhall, _, hKH⟩ := OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
    (by simp : Nat.Coprime (Nat.card Unit) (Nat.card ↥M)) hKsubMpi hKinv
  set E : Subgroup G := H.map M.subtype with hEdef
  have hEM : E ≤ M := Subgroup.map_subtype_le H
  have hKE : K ≤ E := fun x hx => by
    rw [hEdef, Subgroup.mem_map]; exact ⟨⟨x, hKM hx⟩, hKH (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  haveI : IsSolvable ↥E := solvable_of_solvable_injective (Subgroup.inclusion_injective hEM)
  have hEpi : ∀ p ∈ (Nat.card ↥E).primeFactors, p ∈ (sigma M)ᶜ := fun p hp => by
    rw [Subgroup.card_map_of_injective M.subtype_injective H] at hp; exact hHhall.1 p hp
  -- Step 2: r(E)≤2 (α⊆σ, π(E)⊆σ').
  have hErank : rank ↥E ≤ 2 := by
    rw [rank_le_iff]; intro p hp; haveI : Fact p.Prime := ⟨hp⟩; by_contra hcon
    have h3E : 3 ≤ pRank ↥E p := by omega
    have h3M : 3 ≤ pRank ↥M p := le_trans h3E (pRank_le_of_injective (Subgroup.inclusion_injective hEM))
    exact hEpi p (Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega))
      (alpha_subset_sigma hG hM ((mem_alpha_iff M p).mpr
        ⟨Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega), h3M⟩))
  -- Step 3: Thm 4.20(c) char series ⟹ 正規 Sylow q (q∈π(E)⊆σ').  [要 Nontrivial ↥E ← K≠⊥]
  have hEodd : Odd (Nat.card ↥E) := hG.odd.of_dvd_nat
    ((Subgroup.card_subgroup_dvd_card E).trans (Subgroup.card_subgroup_dvd_card M))  -- ≪ trans 注意
  have hErankF : rank ↥(Ch01.fitting ↥E) ≤ 2 :=
    le_trans (rank_le_of_injective (Subgroup.inclusion_injective (Ch01.fitting_le ↥E))) hErank
  obtain ⟨pkg⟩ := Ch1.S05.exists_characteristicSylowSeriesPackage_of_rank_fitting_le_two hEodd hErankF
  obtain ⟨i, _, hqE, Q, hQnorm⟩ := Ch1.S04.CharacteristicSylowSeriesPackage.exists_terminal_normal_sylow pkg
  set q : ℕ := (pkg.series.step i).q; haveI : Fact q.Prime := (pkg.series.step i).q_prime
  set R : Subgroup G := (Q : Subgroup ↥E).map E.subtype with hRdef
  have hRE : R ≤ E := Subgroup.map_subtype_le _
  have hRpg : IsPGroup q ↥R := Q.isPGroup'.map E.subtype
  -- Step 4 (TODO): R は M の Sylow q (E Hall σ', q∈σ' ⟹ |E|_q=|M|_q):
  --   q∤[M:E] (Hall) ∧ q∤[E:R] (R Sylow E) ⟹ q∤[M:R] ⟹ R.subgroupOf M は Sylow q (toSylow).
  -- Step 5: q∉σ(M) (hEpi: π(E)⊆σ'), q∈π(M) ⟹ mem_sigma_iff の ∀ で N_G(R)⊄M.
  -- Step 6: haveI : (Q:Subgroup ↥E).Normal := hQnorm;
  --   E≤N_G(R) via map_le_normalizer_map_of_normal (φ:=E.subtype, P:=⊤, L:=Q) + (⊤).map=E.
  -- Step 7: N_G(R)<⊤ (R≠⊥, simple) ⟹ 極大 L⊇N_G(R), L≠M (N_G(R)⊄M);
  --   K⊆E⊆N_G(R)⊆L, K⊆M ⟹ not_isUniquelyMaximal_of_le_inf_distinct_maximals.
```

### part (b) 要点
M_α=1 を背理法で得る前段で Prop 10.10 (✅ `normalizer_factorization`) を直接適用。
**要確認**: 「`A∉𝒰` ⟹ `r(C_G(A))≤2` ∧ `A∈ℰ_p*(G)`」(Uniqueness Theorem の必要方向)。
S09 capstone は対偶 (`isUniquelyMaximal_of_three_le_rank_of_lt_top`)。その contrapositive +
`A∈ℰ_p*` の導出を要組立。

### part (c) 要点
`Z := Fsigma' M = O_{σ'}(F(M))`。`[Z,M_σ]⊆Z⊓M_σ=1` で (b) を Z に適用 ⟹ Z cyclic。
`C_K(M_σ)∩M' ⊆ C_M(M_σ·Z) ⊆ C_M(F(M)) ⊆ F(M)` の Fitting 包含チェーン。

## 完了記録 (2026-06-10)

**COMPLETE**。`sigma_complement_rank_le_one` (a)(b)(c) capstone 実装、sorry 解消。

- **(a)** は独立 theorem `sigma_complement_not_isUniquelyMaximal` に切り出し
  (+ helper `not_isUniquelyMaximal_bot`)。**unconditional・axiom-clean** (standard 3 のみ;
  `#assert_only_allowed_axioms` 登録)。Hall σ'-overgroup (`aInvariant_piSubgroup_le_aInvariant_hall`,
  φ=1) + Thm 4.20(c) char Sylow series 終端正規 Sylow + relIndex 乗法で M-Sylow 化 +
  `q ∉ σ(M)` で N_G(R) ⊄ M + `not_isUniquelyMaximal_of_le_inf_distinct_maximals`。
- **(b)** = `rank_centralizer_Msigma_inf_le_one`。blueprint どおり: Uniqueness Thm は
  `isUniquelyMaximal_of_mem_e2_not_maximal` (⟹ A∈ℰ_p*) と `uniquenessTheorem` (⟹ r(C_G(A))≤2)
  の対偶 2 本。α(M)=∅ は「r∈α なら r³-elem-abelian ≤ M_σ ≤ C_G(A) で rank 矛盾」(M_α 経由不要)。
  M' nilpotent は Thm 4.20(a) `derived_le_fitting_of_rank_fitting_le_two`。Prop 10.10 の
  P ≤ N_G(S)' ⊆ M' から `Sylow.smul_eq_iff_mem_normalizer` + nilpotent M' の正規 Sylow 一意性で
  M = N_G(P)、p ∈ σ(M) 矛盾。
- **(c)**: Z = O_{σ'}(F(M))。`normal_subgroupOf_iff_le_normalizer` で Z,M_σ ⊴ M 化 →
  `commutator_le_inf` + π-coprime で Z ≤ C(M_σ) → (b) を Z に適用 → rank ≤ 1 →
  nilpotent + `IsZGroup` (mathlib instance) で Z cyclic → M' ≤ C(Z) は
  ψ : M →* MulAut Z (`normalizerMonoidHom`) + `IsCyclic.mulAutMulEquiv` 可換性で commutator 消滅 →
  X = C_K(M_σ)⊓M' ≤ C(F(M))⊓M ≤ F(M) (nilpotent π-分解 `top_le_oPiCore_sup_compl_of_isNilpotent`
  + `centralizer_fittingInG_inf_le_fittingInG`) → X ≤ O_σ'(F)=Z
  (`isPiGroup_le_of_normal_isHallSubgroup`、S10_HallStructure で public 化) →
  cyclic uniqueness (`cyclic_subgroup_eq_of_card_eq`、capstone 前へ移動) で M ≤ N(X)。

`#print axioms`: (a) = standard 3 ちょうど; (b)/capstone/(d) = standard 3 + keystone island 2
ちょうど (完了条件どおり)。AxiomsCheck 4 エントリ登録 (S10_LocalLemmas import 追加)。
full build 3613 green。§10 の D-lane 残 sorry は Lemma 10.13 のみ (対象外、c-bg-s10 委任)。
