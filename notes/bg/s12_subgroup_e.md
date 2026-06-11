# BG §12: 部分群 E — 大規模節の形式化ロードマップ

## ✅ 2026-06-11 (Lane F session 3, Fable 5): **Lemma 12.3 COMPLETE — cascade 根の解除**

**新 leaf `S12_ExceptionalBridge.lean`** (imports S10_LocalLemmasCore + S11_MsigmaANormal +
S12_Lemma1218)。全結果 **unconditional・axiom-clean** (standard 3 のみ)、AxiomsCheck 6 本登録。

- **⚠ scaffold 訂正**: 旧 `elemAb_centralizes_meet` (S12_E) は **unfaithful** だった
  (場合分け仮定 `p∉σ(M)` / `p∈σ(M)−α(M)` と `M*≠M` を欠き、両結論を無条件連言で主張 —
  `M*=M` で偽になりうる)。faithful な 2 定理に分割して置換:
  `elemAb_centralizes_Msigma_meet` (12.3(a)) / `elemAb_centralizes_Malpha_meet` (12.3(b))。
- **`S11.Hypothesis111.of_normalizer_le`** (§11 入口 constructor, 初の Hyp111 producer):
  `p∉σ(M)`, `A₀∈ℰ_p¹`, `N_G(A₀)≤M`, `A₀≤A∈ℰ_p²(M)` → `∃P, Hypothesis111 M p A₀ A P`。
  `r_p(M)=2` = Lem 10.5 (`pRank_eq_two_of_normalizer_le`); `A∈ℰ_p*(G)` は
  `F ⊇ A elem-ab ⟹ F ≤ C(A) ≤ C(A₀) ≤ N(A₀) ≤ M` + rank-2; `N_G(P)⊄M` は σ の定義から
  (witness Sylow `PM` がそのまま `mem_sigma_iff` の witness)。**12.4/12.5 もこれを使う**。
- **`not_conj_of_mem_sigma_of_normalizer_le`** (12.2(b) σ-case): Thm 10.1(b)
  (`fusion_control_of_mem_sigma .2.1`) の transitivity を `(g₁,g₂):=(h,1)` で呼び、
  `c ∈ C(X) ⊆ M*` が `M*` を固定 ⟹ `M*=M`。τ₁∪τ₃-case は消費者出現時に追加。
- **`normalizer_Malpha_sup_sylow_of_mem_sigma`** (Thm 10.2(d) Sylow closure): `p∈σ(M)`,
  `SM : Sylow p ↥M` ⟹ `M ≤ N_G(M_α ⊔ S̄)`。実装 = quotient `M/M_α` で
  `Sylow.mapSurjective` (mk' surjective; **card 計算不要・p∈α 場合分け不要**) →
  `S̄ ≤ F(M/M_α)` (`Msigma_quotient_Malpha_le_fitting`) → nilpotent 内 Sylow normal
  (`isNilpotent_of_finite_tfae.out 0 3`) → char → AppB transport → `comap_map_eq` で
  `SM ⊔ N` ⊴ ↥M → `le_normalizer_map_subtype_of_normal` (新汎用 helper) で G へ。
- **engine `commutator_le_inf_Msigma_of_normalizer_le`** (mmd L3107-3111): `A`-不変
  `p'`-部分群 `K ≤ M*` ⟹ `⁅A,K⁆ ≤ K ⊓ M*_σ`。`M*_σ⊔A` の正規性を
  `p∈σ(M*)` (sup 吸収) / `p∉σ(M*)` (constructor + **Thm 11.7**) で統一し、
  **`le_of_le_sup_of_coprime_card`** (新汎用: `P ≤ N_G(N)`, `H ≤ N⊔P`, `(|H|,|P|)=1` ⟹
  `H ≤ N`; 商 `L/N` = `P` の像で `|H像| ∣ gcd=1`) で `K⊓(M*_σ⊔A) ≤ M*_σ` に落とす。
- **12.3(a)**: `p∈σ(M*)` 枝 = 非共役 (sigma_conj 移送) → 10.12(a) `M*_α⊓M_σ=⊥` +
  Sylow closure `T=M*_α⊔S` 経由で `⁅A,K⁆ ≤ K⊓T ≤ M*_α`; `p∉σ(M*)` 枝 = engine +
  **Cor 11.4** (`eq_of_Msigma_meet_Hsigma`) で `M_σ⊓M*_σ≠⊥ ⟹ M*=M` 矛盾。
  **12.3(b)**: 12.2(b)σ (X:=A₀) → 10.12(a) `M_α⊓M*_σ=⊥` + engine で即。
- de-private 2 件: `S10.sigma_conj` (S10_HallStructure)、`le_normalizer_inf` (S12_Lemma1218)。
- build 地雷: `Subgroup.card_map_dvd _ π` (H explicit); `map_eq_bot_iff.mp` は定数解決失敗
  → `rw [← map_eq_bot_iff]`; `M.subtype x` 適用形には coe-simp 不発 → `map_mul/map_inv` で;
  `subgroupOf` への `map_le_iff_le_comap` rw はパターン不一致 → element-wise が安全。

### ✅ session 3 cont.: **Prop 12.4 (a)(b) COMPLETE** (同 leaf, unconditional・axiom-clean)

- **(b) = worker `mem_sigma_and_Malpha_eq_bot_of_forall_normalizer_ne`**: (b)-仮定下で
  `p∈σ(M) ∧ M_α=⊥ ∧ M_σ nilpotent ∧ C_G(A)≤M` を一括証明 (mmd L3131-3157 通り)。
  **(a) `centralizer_le_of_elemAb_rank_two`** = by_cases: (b)-仮定 → worker.2.2.2 /
  否定 → `ℳ(N(A₀))={M}` 直接枝 (`eq_top_or_exists_le_coatom` で nonempty → singleton)。
- 部品 (全部 leaf 内、再利用可): rank 境界 = `uniquenessTheorem` (S12_E:622 パターン移植);
  生成 = `le_centralizer_of_forall_line` (private; **Prop 1.16(2)
  `cocyclicFixedByClosure_eq_top_of_not_isCyclic`** + 12.19 の φ-template; cocyclic `Y` を
  `card ∈ {1,p,p²}` で trichotomy [`Nat.dvd_prime_pow` + `interval_cases`]: 1=cyclic 矛盾 /
  p=ℰ¹ 供給 (hsupply に 12.3(a)/(b) を差す) / p²=⊤ 直接); 矛盾 = `rank_centralizer_Msigma_inf_le_one`
  (K:=A, inf_eq_right で rank A=2 と衝突); `Z=Ω₁(Z(P))` = `omega1CenterInG` (centrality は
  `mem_omega1OfAbelian`+`mem_center_iff` 手出し, `Z≠⊥` は `center_nontrivial`+
  `pow_dvd_card_omega1OfAbelian_of_pos_le_pRank`); **`Z≤A` = A⊔Z elem-ab** (新汎用
  `isElementaryAbelian_sup_of_le_centralizer`: closure_union + 可換 closure_induction;
  supporting `inf_centralizer_le_centralizer_sup` / `le_centralizer_swap` /
  `le_centralizer_self_of_isElementaryAbelian`) + card ≤ p² (le_pRank) + `eq_of_le_of_card_ge`;
  `p∉α` = Sylow p ↥M を `⟨Pg.subgroupOf M, _, hmax⟩` で手組み (12.18:1146 template) +
  `pRank_sylow_eq` 鎖; `M_α=⊥` = α の素数 q の Sylow が `M_α ≤ C_M(A)` 内で rank≥3 矛盾;
  nilpotent = BB4 + `Msigma_le_derived` + `nilpotent_of_mulEquiv`; 末尾 = PW normal-in-nilpotent
  (tfae 0 3) → char → AppB transport → `normalizer_le_normalizer_omega1CenterInG` → `N_G(Z)=M`。
- 地雷: `cocyclicFixedByClosure_eq_top` は `[IsMulCommutative A]` instance 要 (`⟨⟨hA.1.comm⟩⟩`);
  `IsCyclic` field の goal は zpowers が ∃-unfold された形 → rw 不可、defeq exact で;
  `isHall_Msigma_Malpha` の Malpha-Hall は `.2.1` (右は 4 連言)。

### ✅ session 3 cont.²: **Thm 12.5 COMPLETE** (新 leaf `S12_Theorem125.lean`, 一発 green)

- `Msigma_nilpotent_of_tau2` 全 6 結論 unconditional・axiom-clean。**§11 中継完了 — 以後
  §11 直接参照は不要** (BG L3177)。入口 = 12.4(b) 対偶 (`∃A₀, ℳ(N(A₀))={M}` →
  `normalizer_le_of_maximalSubgroupsContaining_eq_singleton` [新 helper] → `N(A₀)≤M`) →
  `Hypothesis111.of_normalizer_le`。(a)=11.3, (b)=11.5 + Hyp111 fields (P_sylow は引数順
  reshape + .symm), (c)=11.7, (d)=Cor 11.6(b) (inf_comm), (f)=Cor 11.6(c)
  `exists_distinct_conj_lines` の第1成分。
- **(e) の二分** (mmd L3171-3176): `∃A₀', N(A₀')≤M*` → 12.3(a) + (d) /
  otherwise → 12.4(b) を **M\* に適用** (`p∈σ(M*) ∧ M*_α=⊥`) →
  `normalizer_Malpha_sup_sylow_of_mem_sigma` が `M*_α=⊥` で **`S ⊴ M*` に退化**
  (`rw [hMα', bot_sup_eq]`) → `⁅A,K⁆ ≤ K⊓S = ⊥` (p'∩p) → `K ≤ C(A)` → (d)。
  原文の `A ⊆ O_p(M*)` 経路は O_p 機構不要のこの形で代替。

### ✅ session 3 cont.³: **Cor 12.6 前提 2 点 landed** (12.2(b) τ₁∪τ₃-case + 12.5(b) Ω₁ 条項)

- **`not_conj_of_mem_tau1_union_tau3_of_normalizer_le`** (bridge): 12.2(b) τ₁∪τ₃-case
  完成 — **σ/τ の共役移送一切不要**の contrapositive 実装: `M*=M^g` なら
  `X' := conj g⁻¹ • X ≤ M` かつ `N_G(X') ≤ M` ⟹ 12.2(a) を **(M, X', M*:=M)** で呼ぶと
  `p ∈ σ(M)∪τ₂(M)` — τ₁/τ₃ の `pRank=1` と `∉σ` に矛盾。private 複製 2 本
  (`mulAut_smul_eq_map`/`normalizer_conj_smul`) のみ。12.2(b) は**これで全 case 完成**。
- **`omega1_eq_of_tau2`** (S12_Theorem125): 12.5(b) の deferred Ω₁ 条項 —
  `A ⊆ P ∈ Syl_p(M)` なる**任意の** P で `A = Ω₁(P)` ∧ `N_G(P)⊄M`。entry を
  `exists_line_normalizer_le_of_notMem_sigma` に抽出 (12.5 本体もリファクタ) +
  `Hypothesis111.of_sylow` + Cor 11.6(a)。

### ✅✅ session 3 cont.⁴: **Cor 12.6 COMPLETE** (新 leaf `S12_Corollary126.lean`, 全 6 結論)

下のレシピ通りに実装、ほぼ一発 (修正 = beta-unreduced `one_mul` は defeq `exact` /
`Commute.zpow_left` 向き / `hr r` binder)。全 unconditional・axiom-clean、AxiomsCheck 6 本。
部分定理: `sup_Msigma_inf_E_eq_of_le` (Dedekind) / `E_le_normalizer_of_tau2` /
`line_le_of_le_E_of_tau2` / `centralizer_le_E_of_tau2` /
`maximalContaining_centralizer_line_eq_singleton` /
`Msigma_inf_centralizer_eq_bot_of_le_centralizer` ((d)(e) 共通 core, **素数位数 reduce +
12.2(b)τ₁τ₃ + 12.5(e)**; §13 で再利用可能) / `centralizer_zpowers_eq_singleton` /
assembly `elemAb_normal_in_E_of_tau2` (S12_E から移動)。**S12_E 実 sorry 10**。

### ✅✅✅ session 4-5: **Theorem 12.7 COMPLETE — 全 (a)(b)(c)(d)(e) + assembly, unconditional・axiom-clean**

**(d) + assembly は session 5 で着地** (新 leaf `S12_Theorem127d.lean`, 578 行,
root/AxiomsCheck 登録済, full build 緑)。レシピ通り一発 (数学的逸脱なし, ビルド修正
4 ラウンドのみ)。S12_E から 12.7 scaffold 削除 → **S12_E 実 sorry 9**
(12.4(a)系 ×3 + 12.8〜12.13 系 ×6)。AxiomsCheck に 12.7 全 6 結果登録
(standard 3 axioms のみ確認済)。

**(d) 実装メモ** (`exists_complement_of_canonical_line`):
- **step 1-2**: `E₂` は Sylow-p of E (`card_E2_eq_pow`: Hall τ₂ + (a) 素数限定 ⟹
  card = p^{ν_p(E)}) → `A ≤ E₂` (`elemAb_le_E2_of_prime_eq`: A ⊴ E + Sylow 共役) →
  `E₂` abelian (`E2_isMulCommutative_of_prime_eq`: ν_p(E)=ν_p(M) + 12.5(b))。
- **step 3**: S' ⊇ E₂ Sylow-of-G nonab → 10.13(b) (A₀ ≠ Ω₁(Z(S')) は
  C(A₀) ≤ M [12.6(c) 復元] vs S' ⊄ M) → C_{S'}(A) = A₀⊔Z'、
  **C_{S'}(A) = E₂ は `map_sylow_E_maximal_in_M` 一発** (E₂ ≤ C(A)⊓S' ≤ E の p-群)。
  **℧¹(E₂) ≤ Z' は商を取らず `Subgroup.pow_index_mem`**: [E₂:Z'] = p (card 勘定)
  ⟹ x^p ∈ Z' ∀x。⟹ A₀ ⊓ ℧¹-image = ⊥。
- **step 4**: Maschke は S12_E:298 の compHom テンプレそのまま
  (φ : ↥E₁ →* MulAut ↥E₂, E₁ ≤ N(E₂) = `E2_normal_in_E12`)。S := Agemo ↥E₂ p 1
  (characteristic ⟹ Normal instance 自動 + `IsAInvariant.of_characteristic`)。
  W₀ := A₀.subgroupOf E₂ の不変性は hMnorm (= 12.7(b) M ≤ N(A₀)) 経由。
  商は exp p ⟹ Ω₁(quot) = ⊤ ⟹ X̄'⊔Ā₀ = ⊤; E₂-level 復元は
  `Subgroup.comap_map_eq` + `QuotientGroup.ker_mk'` (ker = Agemo ≤ X')。
- **step 5**: E₀ := E₁ ⊔ (X ⊔ E₃)。card 連鎖 5 本
  (`card_sup_eq_mul_of_le_normalizer_of_disjoint` + 素因子 disjoint→coprime→inf ⊥
  ×4) ⟹ |E| = p·|E₀| ⟹ A₀⊓E₀ = ⊥ (∣p + =p なら E=E₀ 矛盾)。
- **新設汎用 helper** (leaf 内 public, 12.8+ 再利用可):
  `le_centralizer_of_le_of_le` (可換包絡), `le_normalizer_sup`,
  (private) `coprime_of_forall_prime_not_dvd`。
- ⚠ 技法: rw リストに証明項 (`(....).mpr ?_`) を入れない — refine で分離。
  `E₂.subtype x` vs `(↑x : G)` の混在は `show` で defeq 切替してから rw。
- assembly **(a)-conjunct は素数限定形** `∀ q, q.Prime → q ∈ tau2 M → q = p`
  (docstring に deviation 明記済; 旧 scaffold の `tau2 M = {p}` から変更)。

▶ **次 = Lemma 12.8** (S abelian 側; S12_E:443 scaffold)。

### 🟢 session 5 続き: **Lemma 12.8 (a)(b)(c) COMPLETE** (新 leaf `S12_Lemma128.lean`, 777 行)

mmd L3253-3298 (証明全文 L3260-3284 取得済)。**部品構成** (全 unconditional・axiom-clean,
AxiomsCheck 5 本登録):
- `sylow_le_derivedInG_normalizer` = **Cor 10.7(a) complement-free 形** (S ≤ N_G(S)')。
  `S10.sylow_structure …`.1 + `S10.exists_sylow_complement_normalizer` (**de-private 化**
  @ S10_BetaRadical:648 — SZ complement producer)。
- `sylow_isMulCommutative_of_tau2_of_abelian`: S abelian ⟹ **∀ q ∈ τ₂ ∀ Sylow-q-of-G abelian**
  (12.7(a) 対偶 + Sylow 共役)。`exists_sylow_le_E_of_tau2`: B_q ∈ ℰ_q²(E) ⊆ S_q ≤ C(B_q) ≤ E
  [12.6(b)]。`factorization_card_E_eq_of_tau2`: ν_q(E) = ν_q(G)。
- `derivedInG_normalizer_elemAb_le_fittingInG` = **chain core** N_G(B)' ≤ F(E):
  F(N) ≤ C_G(B) は **O_q × O_q' 分解** (新 helper `oPiCore_sup_compl_eq_top`:
  nilpotent K で O_π ⊔ O_πᶜ = ⊤, Hall card ×2 + coprime-⊥); O_q-part は abelian q-群 ⊇ B、
  O_q'-part は coprime normal commutator ⊥。F(N) ≤ F(E) は nilpotent-normal transport。
  N' ≤ F(N) = **Thm 4.20(a)** (`Ch1.S05.derived_le_fitting_of_rank_fitting_le_two`;
  rank transport = `rank_le_of_injective` ×2, r(E) ≤ 2 = `h.rank_le_two`)。
- `sylow_eq_opiCore_fittingInG_of_tau2`: **S_q = O_q(F(E))** ∧ E ≤ N(S_q) ∧ F(E) ≤ C(S_q)。
  q-群 ≤ O_q(F(E)) は `S10.isPiGroup_le_of_normal_isHallSubgroup` (oPiCore = normal Hall)
  + card ⟹ eq。汎用 `pGroup_le_opiCoreInG_fittingInG` / π 版 `piGroup_le_…`。
- **(a)(b)** `E2_abelian_normal_hall_of_abelianSylow`: **E₂ = O_{τ₂}(F(E))**
  (W := O_{τ₂}(F(E)) が E の normal Hall τ₂ [ν_r(W) = ν_r(E) ∀r∈τ₂-prime ⟸ S_r ≤ W] ⟹
  E₂ ≤ W 吸収 + card ⟹ =)。abelian は per-prime: Sylow-r(E₂) = O_r(F(E)) ≤ C(E₂)
  (F(E) ≤ C(S_r) + swap) + `le_of_sylow_le_of_nilpotent`。Hall-of-G は ν_r 連鎖。
- **(c)** `sylow_chain_of_abelianSylow`: S ≤ N(S)' ≤ F(E) ≤ C(S) ≤ E (部品合成のみ)。
- 他 de-private: `coprime_of_forall_prime_not_dvd` (127d)。新 helper:
  `isMulCommutative_of_le` / `isMulCommutative_of_le_centralizer` / `derivedInG_le_derivedInG`。

### ✅✅✅ session 5 完結: **Lemma 12.8 全 6 結論 + assembly COMPLETE** (leaf ×2, unconditional・axiom-clean)

**(d)(e)(f) + assembly = 新 leaf `S12_Lemma128d.lean` (930 行)**, S12_E scaffold 削除
(**実 sorry 8**: 12.4(a) 系 ×3 + 12.9〜12.13 系 ×5)。AxiomsCheck 計 9 本登録。
- **(d)** `normalizer_chain_of_abelianSylow`: char-chain 一周。部品 = `S = O_p(E₂)` /
  `E₂ = O_{τ₂}(K)` / `K := E₂E₃ = O_{τ₂∪τ₃}(F(E))` (汎用 `piGroup_le_opiCoreInG_of_nilpotent`
  + `card_opiCoreInG_dvd_of_nilpotent` で card 同定) + transport
  `le_normalizer_opiCoreInG_of_le_normalizer`; 一周の鍵 **N(A) ≤ N(F(E))** は
  **F(N)=F(C)=F(E)** (C := C_G(A) ⊴ N [conj transport]; F(N) ≤ C は chain-core 拡張結論
  [`derivedInG_normalizer_elemAb_le_fittingInG` を 3 連言化]; F(C) ⊴ N は
  `AppB.normalizer_le_normalizer_map_of_characteristic` + `Ch01.fitting.characteristic`)。
- **(e)** `central_line_of_abelianSylow`: K abelian (`centralizer_sup_eq` 新 helper +
  ⁅E₂,E₃⁆ ≤ ⊓ = ⊥)、F(E) ≤ C(K) (`fittingInG_le_centralizer_opiCoreInG` 新汎用 +
  E₃ = O_{τ₃}(F(E)) 同定)、⁅K,X⁆ ⊴ N(S) ((f) 機構 mirror) → **10.11(d)**
  (`S10.sigma_complement_commutator_cyclic_normal`) → N(⁅K,X⁆) = M → N(S) ≤ M ✗。
- **(f)** `relative_normality_of_abelianSylow`: H := C_G(S)⊔X ⊴ N(S)
  (`Ch06.normal_of_commutator_le`)、C_S(X) = S⊓C(H)、⁅S,H⁆ = ⁅S,X⁆
  (normal_mul 分解 + c-conj 固定)、conj-invariance (map_inf injective / map_commutator)。
- ⚠ 技法: element commutator は `open scoped commutatorElement` 必須 (Bracket G G)。
  subst h : r = p は **p 側 (binder) を消す** — 以降 r 表記。`set K` の fold ずれは
  `show` で正規化してから omega。

### ✅ session 6: **Corollary 12.9 COMPLETE** (新 leaf `S12_Corollary129.lean`, unconditional・axiom-clean)

mmd L3286-3292。`commutator_decomp_of_tau1_action` (S12_E scaffold を移設・充足、
**S12_E 実 sorry 8→7**)。AxiomsCheck 登録済 (standard 3 のみ)。

- **(a)**: 10.11(d) (`S10.sigma_complement_commutator_cyclic_normal`, **K := A, P := Q** —
  A の q'-性は p ≠ q [pRank 2≠1] から) で `[A,Q] ≤ C(M_σ)`・cyclic・`M ≤ N([A,Q])`。
  `Isaacs.Ch05.fitting_coprime_abelian_decomp (P := A, K := Q)` (Q ≤ N(A) は 12.6(a)
  `elemAb_normal_in_E_of_tau2` 第1連言経由) で `A = (A⊓C(Q)) ⊔ [A,Q]` disjoint。
  card 三分 (`Nat.dvd_prime_pow` + `interval_cases`): 1 = hAQ 矛盾 / p² = `A ≤ C(M_σ)` で
  **rank-clash engine** (10.11(b) `rank_centralizer_Msigma_inf_le_one` + `inf_eq_right` +
  `two_le_rank_of_mem_elemAbelianOfRank_two` + omega; bridge:953 パターン) ⟹ card A₀ = p。
  `A₀ = A ⊓ C(M_σ)` も同じ三分で。`|A| = |A₁|·|A₀|`
  (`card_sup_eq_mul_of_le_normalizer_of_disjoint`) ⟹ card A₁ = p。
- **(b)**: `A₁ = A₀^g` と仮定 → swap で `Q^{g⁻¹} ≤ C(A₀)`。`N(A₀) = M`
  (`normalizer_lt_top_of_le_of_ne_bot` + coatom)、`C(A₀)` は M-conj 不変
  (`centralizer_conj_smul` + `conj_smul_eq_self_of_mem_normalizer`)。
  **cyclic Sylow q 論法**: ↥M 内 Sylow `S₁ ⊇ Q.subgroupOf M`
  (`comap_subtype.exists_le_sylow (G := M)`) へ `Q'.subgroupOf M` を共役で押し込み
  (`exists_conj_le_sylow_of_isPGroup` = S09 private の再掲)、G レベル化
  `SylG := map M.subtype S₁` は cyclic (`pRank_le_of_injective` ≤ r_q(M) = 1 [τ₁] +
  `S10.isCyclic_of_pRank_le_one`; Odd q は `hG.odd.of_dvd_nat`) ⟹
  `S10.cyclic_subgroup_eq_of_card_eq` で `Q = (Q')^m` ⟹ `Q ≤ C(A₀)` ⟹ `A₀ ≤ A₁` ⟹
  直和性で `A₀ = ⊥`、card p に矛盾。
- **(c)**: `C(A₁) ⊄ M` は by_cases: nonabelian Sylow p ⟹ **12.7 assembly**
  `tau2_singleton_of_nonabelianSylow` の (c)-連言に `X := A₁ ≠ A₀ = A⊓C(M_σ)` を
  食わせるだけ; abelian ⟹ `Q` を Hall-τ₁ へ
  (`Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall` **trivial 作用 A := Unit, φ := 1** +
  `Ch1.S06.exists_conj_eq_of_isHall_subgroupOf` で `X := Q^w ≤ E₁`, `w ∈ E`) →
  **12.8(e)** `central_line_of_abelianSylow` ⟹ `E ≤ C(X)` ⟹ `[A,X] = ⊥` ⟹
  (`A` は w-不変 = 12.6(a)) `[A,Q] = ⊥` 矛盾でこの枝は不発。
- ⚠ 技法: `rw [hQ_eq]` は `⁅A,Q⁆` 内の Q も巻き込む → **`conv_lhs => rw [hQ_eq]`**。
  `rw [← hsup]` も同罪 (card 等式は sup 側で作って `rw [hsup] at` で潰す)。
  `Subgroup.card_map_of_injective` は injective 1 引数 (subgroup 暗黙)。
  `(conj g)⁻¹` vs `conj g⁻¹` の不一致は `smul_smul + ← map_mul + inv_mul_cancel +
  map_one + one_smul` で正規化。trivial Hall 作用の Coprime は `Nat.card_unique` で整形。
  `push_neg` は deprecated → `push Not`。
- leaf 内 private helper: `card_conj_smul` (S10 系 private の 3 例目重複 — hoist は hub 仕事)、
  `conj_smul_mono`、`map_subtype_conj_smul` (↥M-conj と G-conj の subtype 交換)、
  `exists_conj_le_sylow_of_isPGroup` (S09 private 再掲)。

▶ **次 = Corollary 12.10** (S12_E:446 scaffold `nilpotent_sigmaComplement_abelian`;
mmd L3293〜; 消費 = 12.5(b)/12.7(a)/12.8(a) [依存表 L778])。

### (履歴) 残 = 12.8 (d)(e)(f) + assembly — 設計メモ (session 5)

- **(d)** N(A)=N(S)=N(E₂)=N(E₂E₃)=N(F(E)): **char-chain 一周** N(F(E)) ≤ N(E₂E₃) ≤ N(E₂)
  ≤ N(S) ≤ N(A) ≤ N(F(E))。部品: S = opiCoreInG {p} E₂ / E₂ = O_{τ₂}(E₂⊔E₃) /
  E₂⊔E₃ = O_{τ₂∪τ₃}(F(E)) (各 piGroup_le + card; ν_r(F(E)) = ν_r(E₃) ∀r∈τ₃ は
  E₃ ≤ F(E) [E₃ cyclic→ab→nilp ⊴ E] + E₃_hall)、transport = `le_normalizer_opiCoreInG_of_le_normalizer`。
  **最後の N(A) ≤ N(F(E)) は F(N)=F(C)=F(E)** (C := C_G(A) ⊴ N [centralizer_conj_smul +
  conj_smul_eq_self]; F(N) ≤ C [chain core 内既証 — 再導出] ⟹ F(N) ⊴-in-C ⟹ ≤ F(C);
  F(C) char C ⊴ N ⟹ ≤ F(N); F(C) = F(E) 同型: C ⊴ E + F(E) ≤ C [F(E)≤C(S)≤C(A)])。
- **(f)** X ≤ N(S) ⟹ C_S(X), ⁅S,X⁆ ⊴ N(S): H := C_G(S) ⊔ X ⊴ N(S)
  (`Ch06.normal_of_commutator_le`: N(S)' ≤ F(E)∩… ≤ C(S) ≤ H)。
  C_S(X) = S ⊓ C_G(H) (**centralizer_sup helper 要**: C(H⊔K) = C(H)⊓C(K),
  sup_eq_closure + closure_induction ~15 行; c ∈ S ⟹ c ∈ C(C_G(S)) swap)。
  正規性 = conj-invariance (conj_smul_eq_self + centralizer_conj_smul + map_inf injective)。
  ⁅S,H⁆ = ⁅S,X⁆: h = c·x (`Subgroup.mul_normal`: C(S) ⊴ N(S)) ⟹ [s,cx] = [s,x]。
- **(e)** X ∈ ℰ_q¹, X ≤ E₁, C_{M_σ}(X) = ⊥ ⟹ X ≤ E ∧ E ≤ C(X): K := E₂⊔E₃ abelian
  (E₃ cyclic + ⁅E₂,E₃⁆ ≤ ⊓ = ⊥ + centralizer_sup ⟹ K ≤ C(K))。F(E) ≤ C(K)
  (oPiCore_sup_compl π:=τ₂ で C(E₂)、τ₃ 版で C(E₃))。⁅K,X⁆ ⊴ N(S) ((f) 機構 mirror) ⟹
  N(S) ≤ N(⁅K,X⁆)。**10.11(d)** = `S10.sigma_complement_commutator_cyclic_normal`
  (K abelian ✓, hKp' : {q}ᶜ-群 [q∈τ₁ vs τ₂∪τ₃], hPN : X ≤ N(K)⊓M, hCP ✓) ⟹ M ≤ N(⁅K,X⁆)。
  ⁅K,X⁆ ≠ ⊥ なら N(⁅K,X⁆) = M (maximal + normalizer_lt_top) ⟹ N(S) ≤ M ✗
  (`normalizer_sylow_le_normalizer_elemAb`.2) ⟹ ⁅K,X⁆ = ⊥ ⟹ K ≤ C(X)。
  E = E₁ ⊔ K (eq_sup + sup_assoc) + E₁ cyclic (`h.E1_isCyclic`) ⟹ E ≤ C(X)。
- **assembly**: scaffold `E2_abelian_of_abelianSylow` (S12_E:443) を素直に束ねて移植・削除。
  ⚠ scaffold (c) の `derivedInG (normalizer …)` 表記と (f) の `S ⊓ C(X)` 形は部品と一致確認。

### 🟢 session 4 進捗 (履歴): **12.7 = (a)(b)(c)+A₀+habs+(e) 完了、残 = (d)+assembly のみ**

leaf `S12_Theorem127.lean` (root/AxiomsCheck 登録済)。commits: `bec4e194` (prep:
一般 line-engine `le_of_forall_line_inf_centralizer_le` + conj transports public 化) /
`0cf44a9c` ((a) `tau2_prime_eq_of_nonabelianSylow` — **⚠ faithful 化: tau2 は素数性を
含まないため素数限定形** + helpers `card_Msigma_mul_card_E` /
`factorization_card_eq_of_notMem_sigma` / `map_sylow_E_maximal_in_M` /
`exists_elemAb_rank_two_le_E_of_tau2`) / `a3d2631e` ((c)+A₀ =
`exists_canonical_line_of_nonabelianSylow`: A₀ = A⊓C(M_σ) card p, M_σ ≤ C(A₀),
(c) 二分律 [Z₀-枝 = S ≤ C / 10.13(c)-枝 = n∈N_S(A)−M 共役 + ℳ-移送]) /
`83003c06` (habs: **∀ W ⊴-by-M p-群 → W ≤ A₀** を同定理の結論に追加 — W ≤ P Sylow 共役
+ W ≤ C(M_σ) + C_P(M_σ) ≤ A₀ [10.13(b) の Z, Z⊓C(M_σ) = ⊥]) / `72f3ecf7` ((b) =
`fitting_eq_sup_of_canonical_line`: M ≤ N(A₀) [M_σ⊔E 分解 sup_le 一発] +
F(M) = M_σ⊔A₀ [card-divisibility: Fq = {q}-core per prime → M_σ/A₀] + M_σ⊓A₀ = ⊥;
`normalizer_le_normalizer_centralizer` de-private; helper
`eq_pow_factorization_of_forall_eq`) / `c7d48549` (**(e) parametrized**
`primeFactors_centralizer_le_tau1_of_disjoint`: E₀ ≤ E, A₀⊓E₀=⊥ の任意候補に対し
π(C_{E₀}(x)) ⊆ τ₁ — Cauchy は `exists_prime_orderOf_dvd_card'` [Nat.card 版・要 prime]、
normal-Hall 吸収は `S10.isPiGroup_le_of_normal_isHallSubgroup hHall hPi` [Hall が第1引数、
π-側は `Ch03.Subgroup.IsPiGroup`])。全部 unconditional・axiom-clean。

### ▶ 残 = (d) 補群 E₀ + assembly — **精密レシピ (session 4 設計済; (e) は landed 済で assembly が呼ぶだけ)**

**(d)** `∃ E₀ ≤ E, A₀⊓E₀ = ⊥ ∧ A₀⊔E₀ = E`: E₀ := E₁ ⊔ X ⊔ E₃ (X = Maschke 補空間 ≤ E₂):
1. **A ≤ E₂**: A ⊴ E p-群 (12.6(a)) → A.subgroupOf E ≤ Sylow T_A of ↥E; E₂.subgroupOf E
   も Sylow (card: |E₂| = p^{ν_p(E)} — Hall τ₂ の素因子 ⊆ τ₂∩primes = {p} [(a)!] +
   index 互いに素; `Sylow.ofCard`); conj e ∈ E で A = A^e ≤ E₂ (確立済 hsmul_eq パターン)。
2. **E₂ abelian + Sylow-of-M**: ν_p(E₂) = ν_p(E) = ν_p(M) → `Sylow.ofCard` in ↥M →
   12.5(b) → 移送 (= `map_sylow_E_isMulCommutative` の E₂ 版; E₂ は map 形でないので
   subgroupOfEquivOfLe 直)。
3. **A₀⊓Agemo(↥E₂)-image = ⊥**: S' ⊇ E₂ Sylow-of-G (nonab 移送); 10.13(b) (A, A₀, S') →
   C_{S'}(A) = A₀⊔Z' cyclic; **C_{S'}(A) = E₂** (E₂ ≤ C(A)⊓S' [abelian ⊇ A] ≤ E-p-群
   [12.6(b)] ⊇ E₂-Sylow-of-E ⟹ = E₂ 最大性 — hP_eq パターン); Agemo ≤ Z'
   (`Subgroup.closure_le`: 生成元 y^p = (az)^p = z^p ∈ Z' [abelian, a^p=1]) ⟹
   A₀⊓Agemo ≤ A₀⊓Z' = ⊥。
4. **Maschke**: `Ch1_Preliminary.exists_aInvariant_complement_in_omega1_quotient`
   (R := ↥E₂, φ : ↥E₁ →* MulAut ↥E₂ [E₁ ≤ N(E₂) = 12.1(e) `h.E2_normal_in_E12`;
   compHom テンプレ], S := Agemo ↥E₂ p 1 [`Agemo.characteristic` +
   `IsAInvariant.of_characteristic`], coprime |E₁| |E₂| [τ₁ vs p], p ∣ |E₂| [A₀ ≤],
   hQab = quotient-comm [E₂ abelian induction], W₀ := A₀.subgroupOf E₂
   [`isAInvariant_subgroupOf_restrict` 群: OperatorMaschke:94-138 の plumbing helpers],
   hWΩ: 全像 ≤ Ω₁ [exp p: x̄^p = (x^p)-class = 1, x^p ∈ Agemo `subset_closure ⟨x, rfl⟩`])
   → X' : Subgroup ↥E₂, Agemo ≤ X', E₁-不変, X̄'⊓Ā₀ = ⊥, X̄'⊔Ā₀ = Ω₁(quot) **= ⊤**
   (quot exp p)。E₂-level: X := X'.map E₂.subtype: A₀⊓X = ⊥ (x̄ ∈ ⊥ → x ∈ ker = Agemo →
   A₀⊓Agemo = ⊥ [step 3]); A₀⊔X = E₂ (π-sup = ⊤ + ker ≤ X')。
5. **E₀ 組立**: E₀ := E₁ ⊔ (X ⊔ E₃)。card 連鎖 (全て
   `card_sup_eq_mul_of_le_normalizer_of_disjoint` + 素因子-coprime-inf-⊥ パターン):
   |X⊔E₃| = |X||E₃| (X ≤ E ≤ N(E₃), p vs τ₃); |E₀| = |E₁||X||E₃| (E₁ ≤ N(X) [Maschke
   不変性 → G-level: mem_normalizer 移送] ∧ N(E₃) → N(X⊔E₃) [conj smul_sup helper 要
   ~10 行 or `Subgroup.smul_sup`]; E₁⊓(X⊔E₃) = ⊥ [τ₁ vs {p}∪τ₃]); |E₂| = p|X|
   (A₀⊔X = E₂, X ≤ N(A₀) [A₀ ⊴ M], A₀⊓X = ⊥); |E| = |E₁||E₂||E₃|
   (|E₁₂| = |E₁||E₂| [E₁ ≤ N(E₂), τ₁ vs τ₂-primes={p}]; |E| = |E₁₂||E₃| [eq_sup +
   E₁₂⊓E₃ = ⊥]) ⟹ |E₀| = |E|/p。**A₀⊔E₀ = E** (lattice: ⊇ E₁,E₃,E₂=A₀⊔X);
   **A₀⊓E₀ = ⊥**: A₀ ≤ E₀ なら E₀ = A₀⊔E₀ = E だが |E₀| = |E|/p < |E| ✗;
   |A₀⊓E₀| ∣ p ⟹ ⊥。
**(e)** `∀ x ∈ M_σ#, ∀ r ∈ π(C_{E₀}(x)), r ∈ τ₁`: y ∈ C_{E₀}(x) order r (Cauchy
`exists_prime_orderOf_dvd_card` in ↥(E₀⊓C({x})) → coe); r ∈ τ₁∪τ₂∪τ₃
(`h.mem_tau_union_of_mem_primeFactors`; r ∣ |E|); **r∈τ₃ 枝**: ⟨y⟩ τ₃... y ∈ E₃
(`S10.isPiGroup_le_of_normal_isHallSubgroup` in ↥E: zpowers y ≤ E₃) → 12.6(d)
(`elemAb_normal_in_E_of_tau2 .2.2.2.1`-shape か standalone 部分定理) で C_{M_σ}(y) = ⊥
だが x ∈ それ ✗; **r=p 枝** ((a) で τ₂∩primes={p}): X_y := zpowers(y の p-order-power —
y 自体 order p なので zpowers y) ∈ ℰ_p¹(E), C_{M_σ}(X_y) ∋ x ≠ ⊥ ⟹ (c) 対偶で
X_y = A₀ ⟹ A₀ ≤ ⟨y⟩ ≤ E₀ ✗ (A₀⊓E₀ = ⊥); ⟹ r ∈ τ₁ ✓。
**assembly** `tau2_singleton_of_nonabelianSylow`: scaffold を S12_E から削除して移植。
**⚠ (a)-conjunct は素数限定形に変更** (`∀ q, q.Prime → q ∈ tau2 M → q = p`) —
docstring に deviation 明記。残りの conjunct は部分定理を束ねるだけ。
AxiomsCheck 登録 (tau2_prime_eq / exists_canonical_line / fitting_eq_sup / assembly)。

## 🔵 session 4: **Thm 12.7 設計 (recon 完了, 全依存 EXISTS 確認済)** — mmd L3201-3251

leaf `S12_Theorem127.lean` (import S12_Corollary126)。3 commit 構成。**確認済 API**:

- **Lem 10.13** = `S10.nonabelian_pSubgroup_rankTwoElemAbelian_structure` (S10_LocalLemmas:976):
  入力 (p∈π(G), A∈ℰ_p², `IsMaximalElementaryAbelian` [= `isMaximalElementaryAbelian_of_mem_tau2`
  S12_ECore:490], P nonab p-群, A≤P, A₀∈`elemAbelianOfRankIn p 1 A`, A₀≠`omega1CenterInG P p`) →
  (a) Z₀∈ℰ¹(A); (b) ∃Z≤P cyclic, Z₀≤Z, A₀⊓Z=⊥, C(A)⊓P=A₀⊔Z; (c) ∀X,Y∈ℰ¹(A)∖{Z₀}:
  ∃n∈N(A)⊓P, conj n•X=Y。
- **Prop 10.10(c)** = `S10.normalizer_factorization` (S10_BetaRadical:2815): 入力 (p≠q,
  A∈ℰ_p²∩ℰ*, **Q∈`hInvariantStar ⊤ A {q}`**, q∈π(C_G(A))) → ∃P∈Syl_p(G), A≤P, …,
  (Q cyclic ∨ ∃B:Subgroup ↥Q, card=q²∧max-elem-ab) → P ≤ C_G(Q)。
  Q 構成 = `exists_le_hInvariantStar` (AInvariantPiSubgroups:255, public)。
- **(d) Maschke** = `Ch1_Preliminary.exists_aInvariant_complement_in_omega1_quotient`
  (OperatorMaschke:159): R:=P abelian, φ:E₁-action, S:=Y:=`Agemo ↥P p 1`-image
  (characteristic ✓), W₀:=A₀ → E₁-不変 X, Y≤X, X̄⊓Ā₀=⊥, X̄⊔Ā₀=Ω₁(P/Y)=⊤ (P/Y exp p)。
  E₀ := E₁⊔X⊔E₃ (E₁ norm X+E₃ ✓), card = |E|/p (`card_sup_eq_mul_of_le_normalizer_of_disjoint`
  連鎖: X⊓E₃=⊥ coprime, E₁⊓XE₃=⊥) ⟹ A₀⊓E₀=⊥ (A₀⊆E₀ なら ⊔=E₀≠E ✗)。
- fittingInG API (S08_FittingOfMaximal): `fittingInG_isNilpotent`,
  `le_fittingInG_of_normal_isPiSubgroup_singleton`, `fittingInG_le` 等。
- partition: `h.mem_tau_union_of_mem_primeFactors` (S12_ECore:295)。
- π-群≤normal Hall: `S10.isPiGroup_le_of_normal_isHallSubgroup` (S10:232)。
- ℰ_q² 存在 = `exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic` (S04_PGroupsSmallRank:947)。

**証明スケッチ (BG faithful)**: P := Sylow p of E (= Sylow of M: ν_p(|M|)=ν_p(|E|),
|M|=|M_σ||E|); S ⊇ P Sylow of G (nonab 移送); C_S(A)=P⊂S (P abelian [12.5(b)] +
C_G(A)≤E [12.6(b)] ⟹ C_S(A)≤E p-群 ⊇P Sylow-of-E ⟹ =P)。
(a): q∈τ₂∖{p} → B∈ℰ_q²(E) (pRank=2 → Sylow-q of ↥M 内 elem-ab card q² →conj into E)
→ B ⊴ E [12.6(a)-q] → A 中心化 B (⁅A,B⁆≤A⊓B=⊥ 双方正規+coprime) → Q := hInvStar ⊇ B
(B∈ℰ*(G) [12.1(g)] ⟹ B.subgroupOf Q ∈ℰ²(Q)∩ℰ*(Q) 移送) → 10.10(c): Syl_p(G) P'≤C(Q)≤C(B)≤E
[12.6(b)-q] → |P'|=|S|>|P|=p-part(|E|) ✗。
(c): A₀ 存在 = 一般 line-engine 対偶 (M_σ≠⊥ [isHall_Msigma_Malpha .2.2.2.2?? — 要素確認] +
∀line C=⊥ ⟹ M_σ=⊥); ℳ(C(A₀))={M} [12.6(c)]; S⊄M (S≤M⟹|S|≤|P| ✗); A₀≠Z₀ (A₀≤Z₀⟹S≤C(A₀)≤M ✗);
X=Z₀ 枝: S≤C(Z₀) ⟹ C(X)⊄M ⟹ C_{M_σ}(X)=⊥ [12.6(c) 対偶]; X≠Z₀ 枝: 10.13(c) (X,A₀) →
n∈N(A)⊓S, A₀^n=X; n∉P (P abelian: A₀^n=A₀≠X); S⊓M=P (P Sylow-of-M card-max) ⟹ n∉M;
ℳ(C(X))={M^n} (conj 移送) ⟹ C_{M_σ}(X)=⊥ ∧ C(X)⊄M (どちらも M=M^n⟹n∈N_G(M)=M ✗)。
M_σ=C_{M_σ}(A₀): line-engine T:=C(A₀)。A₀=A⊓C(M_σ): ⊇ swap; ⊊ なら A⊆C(M_σ) ⟹ 第2の line も
C_{M_σ}≠⊥ ✗ (c)。
(b): A₀⊴M (m=se 分解: A₀^e=A₀ [A⊴E+C(M_σ) e-不変], A₀^s=A₀ [s∈M_σ⊆C(A₀)]); F(M)⊇M_σ⊔A₀
(nilpotent normal ≤ F ×2); ⊆: q∈π(F): O_q(F)⊴M → 12.2(a) (M*:=M) → q∈σ∪{p};
O_p(F)=:W⊴M p-群 → W≤全 Sylow ⟹ W≤P → W≤C(M_σ) (⁅W,M_σ⁆≤W⊓M_σ=⊥) → W≤C_P(M_σ)=A₀
(P=A₀×Z [10.13(b)], C_Z(M_σ)=⊥ [(c): Z の line ≠A₀], C_P(M_σ)=A₀×C_Z=A₀); σ-part ≤ M_σ。
(e): r∈π(C_{E₀}(x)) → y order r (Cauchy in ↥C_{E₀}(x)) → r∈τ₁∪τ₂∪τ₃ [partition];
r∈τ₃ ⟹ y∈E₃ [normal Hall 吸収] ⟹ 12.6(d) ✗; r=p ⟹ line X_y≤⟨y⟩: C_{M_σ}(X_y)∋x≠1 ⟹
(c) X_y=A₀ ⟹ A₀≤E₀ ✗; ⟹ r∈τ₁。
**prep (commit 1)**: 一般 engine `le_of_forall_line_inf_centralizer_le` (bridge へ;
旧 `le_centralizer_of_forall_line` をそれ経由に refactor) + bridge の conj privates を
public 化 (mulAut_smul_eq_map/normalizer_conj_smul) + `centralizer_conj_smul`/
`isCoatom_conj_smul` 追加 + B-存在 helper + P-Sylow-of-M-from-E helper。

— (12.6 の) **完全レシピ (session 3 recon 済, 履歴用)**:

新 leaf `S12_Corollary126.lean` (import S12_Theorem125) 推奨。mmd L3179-3196。
前提整理: `h : SubgroupESetup M E E₁ E₂ E₃`, `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)` (`hAE : A ≤ E`)。
12.5 を `hAM := hAE.trans h.E_le` で呼んで全成果を取得しておく。

1. **(a)-1 `E ≤ N(A)`**: Thm 12.5(c) `M ≤ N(M_σ⊔A)` + **Dedekind**: `e ∈ E ⊆ M`:
   `A^e ≤ (M_σ⊔A)^e = M_σ⊔A` ∧ `A^e ≤ E` ⟹ `A^e ≤ (M_σ⊔A)⊓E = A`。
   `(M_σ⊔A)⊓E = A` は ↥M 内で分解: `(Msigma M).subgroupOf M` Normal ⟹
   `x ∈ M_σ⊔A` を `x = s·a` に分解 (mathlib `Subgroup.mul_normal`/`normal_mul` 系で
   `↑(N ⊔ H) = ↑N * ↑H`; ↥M 内 or G 内どちらでも — G 内なら A ≤ N_G(M_σ) で
   `Subgroup.sup_eq_range...` 不可なので **↥M 内が安全**)、`s = x·a⁻¹ ∈ M_σ⊓E = ⊥`
   (h.isComplement'_subgroupOf.disjoint)。card 同値 conj: `A^e` と `A` の card 一致 +
   `≤` ⟹ `eq_of_le_of_card_ge` で = (normalizer 化は mem_normalizer_iff 両向き)。
2. **(a)-2 `X ≤ E ↔ X ≤ A` (X ∈ ℰ_p¹)**: ←は `hAE.trans` 自明。→: `X⊔A` は p-群
   (`A ⊴ E` ⟹ X normalizes A, card_sup or IsPGroup of sup via ↥E-quotient…
   実装は「X⊔A ≤ E p-部分群」: mathlib `IsPGroup.sup` 不在なら
   `card_sup_eq_mul_of_le_normalizer_of_disjoint` 不要 — X·A ≤ Sylow まで行かず:
   `(hX.isPGroup ⊔-route)` 詰まったら: X⊔A の代わりに **X ≤ Sylow P_X of M with A ≤ P_X**:
   `A ⊴ E` でなく直接: X p-群 ≤ M ⟹ ∃ Sylow PM ⊇ (X⊔A).subgroupOf?? — X⊔A p-群の証明:
   φ-quotient 不要、`Subgroup.sup_eq_mul`-card: |X⊔A| = |X·A| ∣ |X||A| (X norm A:
   `card_sup_eq...disjoint` は disjoint 版なので不可) → 安全策 = `(X⊔A).subgroupOf E` 内
   で O_p… **最簡**: X, A ≤ E、A ⊴ E: X⊔A ≤ E は p-群: mathlib
   `IsPGroup.to_sup_of_normal_right (hX) (hA) [A.Normal]`?? — ↥E 内で
   `(X.subgroupOf E) ⊔ (A.subgroupOf E)` に `IsPGroup.to_sup_of_normal_right`
   (mathlib 存在: normal 側仮定で sup p-群 ✓) を適用し map で戻す。
   そのあと Sylow PM of ↥M ⊇ (X⊔A).subgroupOf M、P' := map、`omega1_eq_of_tau2` の
   P'-data (hPsyl は constructor 内のパターン) ⟹ `A = Ω₁(P')`;
   x ∈ X: x^p = 1 (ℰ¹ elem-ab) ∧ x ∈ P' ⟹ `⟨x,_⟩ ∈ Omega ↥P' p 1`
   (`Subgroup.subset_closure`, pow_one 注意: p^1) ⟹ x ∈ A ✓。
3. **(b)**: `N_M(A) = E`: ⊇ は (a)-1 + h.E_le; ⊆: `N_M(A) = (N_M(A)⊓M_σ)·E` (Dedekind,
   E ≤ N_M(A)) で `N_{M_σ}(A) = C_{M_σ}(A)` (s ∈ M_σ⊓N(A): `⁅A,s⁆ ≤ A⊓M_σ = ⊥`
   [A ≤ E, M_σ⊓E=⊥] ⟹ centralize) `= ⊥` (12.5(d))。`C_G(A) ≤ E`:
   12.4(a) `centralizer_le_of_elemAb_rank_two` ⟹ C_G(A) ≤ M ⟹ ≤ N_M(A) = E。
   `N_G(A) ⊄ M`: A = Ω₁(P) char P (omega1_eq_of_tau2 + char 転送は
   `normalizer_le_normalizer_omega1CenterInG` でなく Omega-char:
   `N_G(P) ≤ N_G(Ω₁(P).map)` — AppB.normalizer_le_normalizer_map_of_characteristic
   (W := Omega ↥P p 1, Characteristic instance 要 — OmegaSubgroup に instance あるはず)
   + `¬N_G(P) ≤ M` (omega1_eq_of_tau2 .2)。
4. **(c)**: X ∈ ℰ¹(A), C_{M_σ}(X) ≠ ⊥ ⟹ ℳ(C_G(X)) = {M}: M* ∈ ℳ(C_G(X)):
   `A ≤ C(X)` (le_centralizer_self + centralizer_le) `≤ M*` ⟹ M* ∈ ℳ(A);
   M* ≠ M なら 12.5(e) ⟹ `C_{M_σ}(X) ≤ M_σ⊓M* = ⊥` 矛盾 ⟹ 全員 = M;
   nonempty: `C_G(X) < ⊤` (X ≠ ⊥ central なら X ⊴ G 矛盾 — C(X) = ⊤ ⟹ X ≤ center:
   simple 群の center = ⊥ route か normalizer_lt_top 流用 C ≤ N) + coatom 存在。
   = {M} は `Set.eq_singleton_iff_unique_mem`。
5. **(d)(e)**: WLOG x prime order r (y := x^(orderOf x / r), C_{M_σ}(x) ≤ C_{M_σ}(y));
   **(d)**: r ∈ π(E₃) ⊆ τ₃ (`h.E₃...` isPiGroup field); **`⁅A,E₃⁆ ≤ A⊓E₃ = ⊥`**
   (A ⊴ E [(a)], E₃ ⊴ E [12.1(d), S12_ECore に landed], 双方 normal ⟹ commutator ≤ inf;
   A⊓E₃ = ⊥ は p ∈ τ₂ vs π(E₃) ⊆ τ₃ の card 互いに素) ⟹ A ≤ C(x) ≤ N(⟨x⟩);
   M* ∈ ℳ(N(⟨x⟩)) (coatom 存在; N < ⊤): `not_conj_of_mem_tau1_union_tau3_of_normalizer_le`
   (Or.inr, X := ⟨x⟩ zpowers) ⟹ M* ≁ M ⟹ M* ≠ M (conj-refl: ⟨1, one_smul⟩);
   A ≤ M* ⟹ 12.5(e) ⟹ C_{M_σ}(x) ≤ M_σ⊓M* = ⊥ (C(x) ≤ N(⟨x⟩) ≤ M*:
   centralizer {x} vs zpowers: `centralizer_zpowers_eq_singleton`-ish S11:862 private —
   C({x}) = C(⟨x⟩) 同値補題を自前 5 行)。**(e)**: x ∈ C_{E₁}(A)#: r ∈ π(E₁) ⊆ τ₁;
   A ≤ C(x) は x ∈ C(A) の swap (`le_centralizer_swap` 単元版) — 残り同型。
6. **(f)**: `S10.disjoint_of_not_conj hG hM hM* hnc |>.2 (12.5(a))` 直接 (10.12(b))。

⚠ (d)(e) の「x prime order に reduce」: `orderOf` の素因数 r、y := x^(orderOf x / r):
orderOf y = r (`orderOf_pow` + div); y ∈ E₃ (subgroup pow-closed); y ≠ 1;
C_{M_σ}(x) ≤ C_{M_σ}(y) (centralizer {x} ⊆ centralizer {y}: y ∈ zpowers x)。
π(E₃) ⊆ τ₃: SubgroupESetup の field 名要確認 (E₃_hall から isPiGroup 経由?
`h.isPiGroup_tau3`?? — S12_ECore の SubgroupESetup projection 群を grep)。

12.4 実装メモ (recon 済): worker = (b)-仮定 (`∀A₀∈ℰ¹(A), ℳ(N_G(A₀))≠{M}`) 下で
`p∈σ ∧ M_α=⊥ ∧ M_σ nilpotent ∧ C_G(A)≤M` 一括証明 → (a) は by_cases で direct 枝
(`ℳ(N(A₀))={M}` ⟹ `C(A)≤C(A₀)≤N(A₀)≤M`)。部品: r(C_M(X))≤2 = uniquenessTheorem
(S12_E `rank_centralizer_Malpha_le_one_of_not_uniqueMaximal` パターン); 生成 = Prop 1.16(2)
`cocyclicFixedByClosure_eq_top_of_not_isCyclic` (cocyclic Y を card ∈ {1,p,p²} で分類:
1=⊥ は noncyclic 矛盾, p = ℰ¹ → 12.3(a)/(b), p² = ⊤ 直接) + 12.19 の φ-setup テンプレ
(S12_E:307-315); 矛盾 = Prop 10.11(b) `rank_centralizer_Msigma_inf_le_one` (K:=A);
`Z=Ω₁(Z(P))` は **`S10.omega1CenterInG`** (S10:128, `normalizer_le_normalizer_omega1CenterInG`
あり); `M_σ` nilpotent = BB4 + `Msigma_le_derived` + `nilpotent_of_mulEquiv`;
`ℳ(N(Y))≠{M} ⟹ ∃M*∈ℳ(N(Y))−{M}` は nonemptiness 要 (`eq_top_or_exists_le_coatom` 経由,
MaximalSubgroup.lean:155 参照)。

## ✅✅✅ 2026-06-11 (Lane F session 2, Fable 5): **Lemma 12.18 COMPLETE — unconditional・axiom-clean**

**`tau1_Malpha_interaction` (a)(b) 全結論 sorry-free** (leaf `S12_Lemma1218.lean`, 1,180 行,
commits `9854236d` [(a) 第2連言] + 本 commit [(b)+assemble+AxiomsCheck])。
session 1 スケルトン通りに組立、数学的逸脱なし。**`#print axioms` = standard 3 のみ**:
(b) の Cor 10.9(a)(2) 消費は de-axiom 済 (ce49f862) ゆえ **island 化せず** (session 1 の
「keystone island 見込み」は解消済)。AxiomsCheck に BB4/第2連言/capstone の 3 本登録。

### 実装プロファイル ((a) 第2連言 = hard core ~420 行 + helpers ~250 行)

- **cyclic 同位数一意** `eq_of_card_eq_of_le_of_isCyclic` (素数位数版): 両部分群を
  `zpowers (g^(|C|/r))` に同定。**mathlib に直接形は無い** (leansearch/moogle 共にダウンで
  自作; `IsCyclic.card_powMonoidHom_ker` は CommGroup 要件で不採用)。部品 =
  `orderOf_pow` + `Nat.gcd_eq_right` + `Nat.div_div_self` + `Subgroup.eq_of_le_of_card_ge`。
- **(12.7) カード評価** `card_eq_prime_of_le_exponent_prime`: `S ≤ C` cyclic ∧ `S ≤ R₁`
  (exp r) ∧ `S ≠ ⊥` ⟹ `|S| = r`。`C_{R₁}(P)`/`R₀ = C_{R₁}(Q)` の両方に適用。
- **Ω₁ bookkeeping は z 経由の card 比較のみで完結**: `⟨z⟩ = C_{R₁}(P)` (一意性) ⟹ `z ∈ R₁`
  ⟹ `⟨z⟩ ≤ R₀` ⟹ `R₀ = ⟨z⟩` (eq_of_le_of_card_ge)。原文の Ω₁ 演算子は不要。
- **FPF-decomp ≤ 版** `inf_centralizer_sup_le_inf_of_le_normalizer`: `C_{Q⊔N}(P) ≤ C_N(P)`
  (S12_E の eq_bot 版の第2成分保持変種; quotient FP の witness を `R₀` へ落とす要)。
- **normalizer 移送 3 点** `le_normalizer_inf` / `normalizer_le_normalizer_centralizer` /
  `normalizer_le_normalizer_normalizer` (mathlib 不在、element 計算 ~15 行ずつ)。
- **Thm 3.7 矛盾 step** `inf_centralizer_ne_bot_of_not_le_centralizer`: 第1連言の
  1034-1113 を R₁ 任意で抽出 (Q⊔R₁ 非冪零 + FPF ⟹ C_{R₁}(P)≠1)。第1連言は無改変。
- **quotient 形 Thm 3.7**: ambient `Hgrp := (Q⊔N)⊔P`、`R₀.subgroupOf Hgrp` Normal、
  `N' := π(Y)`, `R' := π(P)` に form-2 適用。**FPF/可換性の引き戻しは
  `Ch04.coprime_fixedPoints_quotient` (coset-fixed 形) で element-wise** — quotient 内
  centralizer subgroup を扱わない。card: `card_map_dvd` (H explicit!) + `range_comp` 経由。
- **(b) reduction**: `Q ≤ M'` = `Ch04.fixedPoints_sup_actionCommutator_eq_top`
  (Isaacs Lem 4.28) + S06 conjugation bridges (`fixedPointsOfMulAut_conj_map_subtype` で
  C_Q(P)=⊥ → fixedPoints=⊥、`actionCommutator_conj_map_subtype` で AC=⊤ → Q=⁅Q,P⁆)
  + `Subgroup.map_subtype_commutator`。`M'` 非冪零 = nilpotent なら Sylow q
  (`isNilpotent_of_finite_tfae.out 0 3`) が normal→char (`Sylow.characteristic_of_normal`)
  → `AppB.normalizer_le_normalizer_map_of_characteristic` で `M ≤ N_G(Q)` ⟹ `N_G(Q)=M`
  ⟹ `ℳ(N_G(Q))={M}` 矛盾。`q∉α` = Uniqueness 9.6 (`rank Q ≥ 3` は Sylow.mk +
  `pRank_sylow_eq`)。`α=β` = `beta_complement_centralizes` (p:=r∈α−β) .2 で
  `C_M(Q)∈𝒰` → S12_E:627-648 の uniquely-maximal 矛盾パターン。

### build 地雷録 (このセッションで踏んだ分)

- **combining tilde 識別子は不正**: `x̃`(x+U+0303) は Lean 識別子にならない (`ñ` 単一 CP は
  可)。expected token エラー位置で発覚。ASCII 化 (`xt`/`nt`/`mt`) が安全。
- **`orderOf_injective f hf x` は必ず明示引数 + 必要なら `.symm`**: `_` だと
  `orderOf (f ?) = orderOf ?` の unification が `↑x` 表示と合わず失敗。第1連言の
  「`(orderOf_injective ... ⟨x, hx⟩).symm`」パターンに統一。
- **element membership の sup は `Subgroup.mem_sup_left/right`** (`le_sup_left h` は
  ≤ proof ゆえ関数適用不可)。
- **`Subgroup.map_eq_bot_iff` 系は H が explicit variable** → dot notation
  `(H.map_eq_bot_iff_of_injective hf).mp`。`Subgroup.card_map_dvd` も同様 H explicit。
- **`rintro rfl` が theorem binder を subst する**: `L = M` で M (binder) 側が消され
  後続の `M` が unknown に。`intro h; rw [h]` で回避。
- **TFAE `.out 0 3` は have で分離**: 適用を直結すると auto-param が metavariable のまま
  「Function expected」化 (Frattini.lean:60 と同パターンに)。
- `simp only [Subgroup.coe_mul, InvMemClass.coe_inv]` 後の `congr 1` は rfl-proof
  (`hφ_coe`) 側を defeq で閉じる — 後続 `exact` を置くと「No goals」。

### ▶ §12 残 = cascade 14 件 (S12_E) — 全解禁済・次セッションから回収

根 = **Lemma 12.3** `elemAb_centralizes_meet` (Thm 11.7 = `S11.MsigmaA_normal` landed 済) →
12.4 → 12.5 → τ₂ cascade (12.6-12.12) + σ-side (12.13-12.16)。12.15/12.16 が §13-14 の gate。
モデルは Opus 4.8 で可 (LAUNCH.md)。大物 (12.5/12.12/12.13) は専用 leaf を切ること
(S12_E は 1,126 行で上限接近)。

## 🔵 2026-06-11 (Lane F session 1, Opus): scope 確定 + 12.18 (a) 第2連言 完全 recon → Fable 5 へ昇格

**Lane F 初回。10.13 解禁後の §12 回収を担う想定だったが、scope を精査して以下を確定:**

### scope 確定 (再 triage 不要)

- **§12 cascade 13 結果 (12.3→12.4→12.5→τ₂ cascade 12.6-12.12 + σ-side 12.13-12.16) は全て
  Thm 11.7 でブロック中**。11.5/11.6 は landed (merge 25f27343/9581665d) だが、cascade の根
  **Lemma 12.3** (`elemAb_centralizes_meet`@S12_E:132) が証明本体で **Thm 11.7 を直接使用**
  (mmd L3107「it follows from Theorem 11.7 that M*_σA ⊴ M*」を原文確認)。12.4(a) も
  12.3(a)(b) 経由 (mmd L3135/L3147 確認)。**Thm 11.7 (`MsigmaA_normal`@S11:1202, S11 唯一の残
  sorry L1205) = Lane E 担当・未完了** ⟹ F は cascade に着手不可。
- **着手可能な §11 非依存 sorry は `tau1_Malpha_interaction` (Lemma 12.18, S12_E:1107) のみ**。
  building blocks 5 件 + (a) 第1連言 `tau1_Malpha_centralizer_P_ne_bot` (S12_E:914) は landed。

### 決定: 12.18 (a) 第2連言 hard core は **Fable 5 (1M) へ昇格** (ユーザー裁可, LAUNCH.md 方針)

12.18 は §12 最厚クラス。Opus session で **全証明スケルトンを詰めて** Fable 5 に引き継ぐ。
**全ステップが既存 API にマップ済み (下記)。新規ボトルネックは無く、組立 + 小 API hunt のみ。**

### 🎯 12.18 残タスク (3 件) と推奨ファイル構造

**専用 leaf `S12_Lemma1218.lean`** を新設 (S12_E を import; building blocks 再利用)。
`tau1_Malpha_interaction` を S12_E から **移動** (S12_E の sorry −1, 新 leaf に sorry-free 版)。
`OddOrder.lean` に import 追加。S13 は将来この leaf を import (現状 §13 は未使用、grep 確認済)。
※ S12_E は現在 1123 行。12.18 残 (~350 行) を足すと 1500 超 ⟹ 新 leaf 必須。

1. **BB4 helper** `isNilpotent_derived_of_Malpha_eq_bot` [~30 行, 低リスク, 最初に land 推奨]:
   `M_α = ⊥ ⇒ IsNilpotent ↥(M')`。`S10.derived_quotient_Malpha_le_fitting`
   (S10_HallStructure:1490, 無条件: `(M/M_α)' ≤ F(M/M_α)`) を `M_α=⊥` で quotient-by-⊥ transport
   ⟹ `M' ≤ F(M)` nilpotent。part (b) の M_α≠⊥ 用 (Thm 10.2(d) 代替)。

2. **(a) 第2連言** `tau1_Malpha_centralizer_PQ_eq_bot` [hard core, ~250 行]:
   `… → S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥`。**完全スケルトン↓**。

3. **assemble** `tau1_Malpha_interaction` [~40 行]: (a) = ⟨第1連言, 第2連言⟩; (b) reduction↓。

---

### 📐 (a) 第2連言の完全証明スケルトン (Opus が詰めた; mmd L3502-3506)

**背理法**: `hcon : C_{M_α}(PQ) ≠ ⊥` を仮定し ⊥ を導く (背理で False)。

**Step B — r, R の選択** (mmd「we can choose r and R such that C_R(PQ)≠1」):
- `C := S10.Malpha M ⊓ C(P⊔Q)` (= `C_{M_α}(PQ)`). hcon: C ≠ ⊥。
- prime `r ∣ |C|` を取る ⟹ `r ∈ α(M)` (C ≤ M_α は α-群; `S10.Malpha_isPiGroup`)。
- `z ∈ C`, `orderOf z = r` (Cauchy: `exists_prime_orderOf_dvd_card` 等)。`⟨z⟩ = zpowers z` は
  **PQ-invariant な r-部分群 of M_α** (z は P⊔Q に中心化される ⟹ P,Q が ⟨z⟩ を正規化)。
- **R⊇⟨z⟩ rank-3 helper** で `R ≤ M_α`, `IsPGroup r R`, `P⊔Q ≤ N_G(R)`, `rank R ≥ 3`,
  **`zpowers z ≤ R`** を得る。⟹ `z ∈ C_R(PQ)` ⟹ `C_R(PQ) ≠ 1`。
  - この helper = **BB3 (`exists_invariant_sylow_Malpha_rank_three`@S12_E:759) を `P₀=zpowers z`
    開始に一般化**。BB3 は内部で `aInvariant_pSubgroup_le_aInvariant_sylow`
    (ForwardFromCh03:554, 結論に `P ≤ S` を含む) を `P:=⊥` で呼ぶだけ ⟹ `P:=zpowers z` に替え、
    `IsAInvariant φ (zpowers z)` を供給 (z が PQ 中心化ゆえ). rank≥3 導出 (S12_E:809-825) は不変
    (R が M_α の Sylow r ⟹ `pRank M r ≤ pRank R r`、`((mem_alpha_iff).mp hrα).2` で `3 ≤ pRank M r`)。
    BB3 を直接編集 (param 追加) か新 helper として複製、どちらでも可。

**Step (12.7) 機構** (第1連言 S12_E:946-1101 とほぼ同一; この r,R で再構築):
- `C_R(P)`, `C_R(Q)` は **cyclic** (r-群, rank ≤ 1): `C_R(P) ≤ C(P)⊓M_α` (R≤M_α) で
  `rank ≤ 1` (= 12.6/12.5 = `rank_centralizer_Malpha_le_one_of_not_uniqueMaximal`)、
  `pRank ≤ rank` (`pRank_le_rank`@PRank:601) ⟹ `S10.isCyclic_of_pRank_le_one`
  (S10_LocalCriteria:57)。**C_R(P) cyclic ∧ C_R(Q) cyclic が Ω₁ bookkeeping の前提**。
- Thompson R₁ (char in R, exp r, Q 非中心化) = `exists_charSubgroup_exponent_not_centralized`
  (BB2@S12_E:674)。R₀ := `C_{R₁}(Q)` (= `R₁ ⊓ C(Q)`)、N := `N_{R₁}(R₀)` (normalizer in R₁).
- **C_{R₁}(P) 位数 r** (= 第1連言と同じ; (12.7) の前半): `C_{R₁}(P) ≠ 1` (FPF-decomp
  `inf_centralizer_sup_eq_bot_of_le_normalizer`@S12_E:880 + Thm 3.7 で QR₁ 矛盾)。
  `C_{R₁}(P) = R₁ ⊓ C(P) ⊆ C_R(P)` cyclic, exp r ⟹ 位数 ∣ r、≠1 ⟹ **位数 r**。

**Step Ω₁ bookkeeping** (mmd「C_{R₁}(P)=Ω₁(C_R(Q))=C_{R₁}(Q)=R₀」; 一般 Ω₁ 演算子は不要、
**cyclic 群の「位数 r の部分群は一意」で回避**):
- `z ∈ C_R(PQ) ⊆ C_R(P)`, `orderOf z = r` ⟹ `zpowers z` は cyclic `C_R(P)` の位数 r 部分群。
- `C_{R₁}(P)` も `C_R(P)` の位数 r 部分群 ⟹ **`zpowers z = C_{R₁}(P)`** (cyclic の同位数部分群一意)。
  ⟹ **`z ∈ R₁`**。
- `z ∈ C_R(Q) ∩ R₁ = C_{R₁}(Q) = R₀` ⟹ `zpowers z ⊆ R₀`、位数 ≥ r。`R₀ = C_{R₁}(Q) ⊆ C_R(Q)`
  cyclic exp r ⟹ 位数 ≤ r ⟹ **`R₀ = zpowers z = C_{R₁}(P)`** (位数 r)。
- ⟹ **`C_{R₁}(P) = R₀` かつ `R₀` は P-不変 (= C_{R₁}(P), P 中心化) ∧ Q-不変 (= C_{R₁}(Q))**。
- ⚠ **要 API**: 「finite cyclic 群で同位数の 2 部分群は等しい」。候補 = `zpowers z` と `C_{R₁}(P)`
  を共に `{x ∈ C_R(P) | x^r = 1}` (= r-torsion, 位数 gcd(r,|C_R(P)|)=r) に等号 (両者 ⊆, 同位数,
  `Subgroup.eq_of_le_of_card_ge`)。mathlib hunt (`IsCyclic`/`card_nthRoots`/r-torsion subgroup)。
  **これが唯一の小 API gap**。

**Step QN/R₀ 非 nilpotent** (mmd「neither is QN/R₀」を一行で済ますが要論証 — Opus が詰めた):
- `R₀ ⊊ R₁`: Q 非中心化 R₁ ⟹ `C_{R₁}(Q) = R₀ ≠ R₁`。
- `N = N_{R₁}(R₀) ⊋ R₀`: R₁ は r-群 (nilpotent), proper subgroup の normalizer は真に大きい =
  **`S08.lt_inf_normalizer_of_isPGroup_lt`** (S09_Theorem91:851 で使用例) または
  `Isaacs.Ch01.lt_normalizer_of_isNilpotent_of_lt_top` (Main:410)。⟹ `N/R₀ ≠ 1`。
- `C_{N/R₀}(Q) = 1`: coprime quotient fixed points = `C_N(Q)/R₀`、`C_N(Q) = C_{R₁}(Q) ⊓ N =
  R₀ ⊓ N = R₀` (R₀ ⊆ N) ⟹ `C_{N/R₀}(Q) = R₀/R₀ = 1` (`coprime_fixedPoints_quotient`
  ForwardFromCh03:808)。
- QN/R₀ nilpotent と仮定 ⟹ Q が N/R₀ を中心化 (coprime: nilpotent ⟹ commute,
  `commute_of_coprime_orderOf_of_isNilpotent`@S10_LocalLemmas) ⟹ `C_{N/R₀}(Q) = N/R₀ ≠ 1`、
  上と矛盾 ⟹ **QN/R₀ 非 nilpotent**。

**Step 最終矛盾** (quotient 形 Thm 3.7):
- `C_{QN/R₀}(P) = 1`: `C_{R₁}(P) = R₀` ⟹ `C_N(P) = C_{R₁}(P) ⊓ N = R₀` ⟹ `C_{N/R₀}(P)=1`
  (同 coprime quotient FP); `C_Q(P) = 1` (hCQP)。両者で `C_{QN/R₀}(P)=1`。
- **quotient 形 Thm 3.7 なし** ⟹ ambient `(Q ⊔ N ⊔ P)/R₀` で適用 (R₀ ⊴ ambient: P,Q,N が R₀ 正規化):
  `N' := (Q ⊔ N).map (QuotientGroup.mk' R₀sub)`, `R' := P.map (...)`、
  `isNilpotent_of_normalizing_primeOrder_fixedPointFree` (S03c:676, form-2) を
  `(N:=N', R:=R')` で。FPF = `C_{QN/R₀}(P)=1` を element-wise に。⟹ QN/R₀ nilpotent。
- 上の「QN/R₀ 非 nilpotent」と矛盾 ⟹ False。∎

---

### 📐 part (b) reduction (mmd L3508; (a) を消費)

`(∀ T ≤ M, q-group, Q≤T → Q=T)` (Q Sylow q) 仮定下:
- `Q ⊆ M'`: `C_Q(P)=1` (hCQP) ⟹ coprime FPF action で `Q = [Q,P] ⊆ M'`
  (`[Q,P] ⊆ M'` は P,Q ⊆ M)。
- `Q ⋪ M`: `ℳ(N_G(Q))≠{M}` (hMNQ) ⟹ Q 非正規 (正規なら M ⊆ N_G(Q) ⟹ ℳ={M})。
- `M' 非 nilpotent`: Q ⊆ M', Q ⋪ M ⟹ M' に非正規 Sylow ⟹ 非 nilpotent (nilpotent ⟹ 全 Sylow 正規)。
- `M_α ≠ ⊥`: **BB4** (M_α=⊥ ⟹ M' nilpotent の対偶)。
- `q ∉ α(M)`: Uniqueness 9.6 (`S09.uniquenessTheorem`)。q∈α ⟹ r_q≥3 ⟹ N_G(Q) uniquely maximal
  ⟹ ℳ(N_G(Q))={M} 矛盾。
- `α = β`: `∃ r ∈ α−β` ⟹ Cor 10.9(a)(2) (`S10.beta_complement_centralizes` 第2連言) で
  `C_M(Q) ∈ 𝒰`、偽 ⟹ α−β=∅ ⟹ (α⊆... で) α=β。
- 以上で (a) の仮定 (M_α≠⊥, q∉α) が成立 ⟹ (a) 適用で 4 結論 + α=β を束ねる。
- ⚠ **keystone island**: (b) は Cor 10.9(a)(2) 消費。**ただし 2026-06-11 に Cor 10.9 は de-axiom
  済 (Lem 10.4(b) 実証明化 ce49f862) ⟹ (a)(b) とも unconditional の可能性大**。要 `#print axioms`
  確認 (Cor 10.9 経路が standard 3 axioms のみなら island 登録不要)。

---

### 📋 API 所在 (Opus 確認済; Fable 5 は再 probe 不要)

**EXISTS (そのまま使える)**:
- BB4 入力: `S10.derived_quotient_Malpha_le_fitting` (S10_HallStructure:1490, 無条件)
- rank→cyclic: `pRank_le_rank` (PRank:601), `S10.isCyclic_of_pRank_le_one` (S10_LocalCriteria:57)
- R⊇P₀ Sylow: `aInvariant_pSubgroup_le_aInvariant_sylow` (ForwardFromCh03:554, 結論 `P ≤ S` 含む)
- Thm 3.7 form-2: `isNilpotent_of_normalizing_primeOrder_fixedPointFree` (S03c:676) — 署名 =
  `{N R}(R≤N(N))(Disjoint N R)(N≠⊥)(R≠⊥)(∃p prime,|R|=p)(∀r∈R,r≠1,∀n∈N,n≠1,r*n*r⁻¹≠n):IsNilpotent N`
- coprime quotient FP: `coprime_fixedPoints_quotient` (ForwardFromCh03:808)
- normalizer 増大 (p-群): `S08.lt_inf_normalizer_of_isPGroup_lt` / `Ch01.lt_normalizer_of_isNilpotent_of_lt_top`
- nilpotent⟹commute: `S10.commute_of_coprime_orderOf_of_isNilpotent`
- 12.18 building blocks (全 S12_E): `rank_centralizer_Malpha_le_one_of_not_uniqueMaximal` (622),
  `maximalSubgroupsContaining_normalizer_ne_singleton_of_mem_tau1` (Helper A, 655),
  `exists_charSubgroup_exponent_not_centralized` (BB2, 674),
  `exists_invariant_sylow_Malpha_rank_three` (BB3, 759),
  `inf_centralizer_sup_eq_bot_of_le_normalizer` (FPF-decomp, 880),
  `card_sup_eq_mul_of_le_normalizer_of_disjoint` (card, 868),
  `tau1_Malpha_centralizer_P_ne_bot` ((a)第1連言, 914)
- (b) 用: `S09.uniquenessTheorem`, `S10.beta_complement_centralizes` (Cor10.9(a))

**NEEDS BUILDING (3 件)**:
- R⊇⟨z⟩ rank-3 helper (BB3 を P₀ 開始に一般化/複製; mechanical)
- **cyclic 同位数部分群一意** (唯一の小 API gap; r-torsion `{x|x^r=1}` 経由 + `eq_of_le_of_card_ge`)
- quotient 形 Thm 3.7 の ambient `(Q⊔N⊔P)/R₀` 組立 (mechanical だが慎重に; `QuotientGroup.mk'`)

### Fable 5 の着手順 (推奨)
1. `S12_Lemma1218.lean` 新設 + BB4 land (緑確認) + `tau1_Malpha_interaction` を S12_E から移動 (sorry 版)。
2. cyclic 同位数一意 の小 helper を先に潰す (Ω₁ bookkeeping の心臓)。
3. R⊇⟨z⟩ helper → 第2連言を上記スケルトン通り組立。
4. quotient Thm 3.7 → 最終矛盾。assemble + (b) + BB4 配線。`#print axioms` で island 判定。

## ✅ 2026-06-10 Lemma 12.1 COMPLETE (issue 5002 closed)

**`subgroupE_basic` (a)-(g) 全 conjunct sorry-free、unconditional・axiom-clean**
(standard 3 のみ; keystone forward-axiom にすら非依存)。AxiomsCheck
`#assert_only_allowed_axioms` 登録、full build 3613 green。commits 9f1d22c4 → 0107bdf2。

下記レシピからの実装上の差分 (handoff 用):
- **(b)(f) は Frattini でなく Burnside 再編で実装**: `W = N_E(P)`、SZ-補群 `K`、
  mathlib **`Sylow.commutator_eq_bot_or_commutator_eq_self`** (cyclic Sylow の
  ⁅K,P⁆ = ⊥ ∨ P dichotomy — Prop 1.6(d) + 鎖論法のパッケージ!) で分岐し、
  ⊥ 枝は `W ≤ C_E(P)` → Burnside normal p-complement ⊇ E' が `p ∣ |E'|`
  (`dvd_card_derived_of_mem_tau3`) と矛盾。P 枝が `P = ⁅K,P⁆ ≤ E'`。
  (f) は P 枝で Prop 1.6(d) (`fixedPoints_isComplement_actionCommutator_of_abelian`) +
  **conjugation bridges** (`actionCommutator_conj_map_subtype` = ⁅P,K⁆,
  `fixedPointsOfMulAut_conj_map_subtype` = C(K)⊓P) で `C_P(K) = ⊥`。
- **E∩M' ≤ E'** (`inf_derivedInG_le_derivedInG`): mk' M_σ 商へ写し complement が
  derived を運ぶ (`Subgroup.map_commutator` + ker 差吸収)。`p∈τ₃ ⟹ p∣|E'|` は
  `M' ≤ M_σ(E⊓M')` 分解 (IsComplement'.existsUnique) + p∤|M_σ|。
- **(e) E₂⊴E₁₂** は新 field `E₁₂_hall` 経由: commutator ↥(E₁⊔E₂) の素因子は
  (τ₁∪τ₂)∩(τ₂∪τ₃) = τ₂ ⟹ Hall τ₂ = E₂ に `normal_le_hall` で吸収 ⟹
  `normal_of_commutator_le`。E₂ の Hall-in-J 化は `relIndex_mul_relIndex` tower。
- **(e) E=E₁E₂E₃**: join の subgroupOf index が τ-分割の各 Hall index を割る ⟹ 1。
- **E₃ ⊴ E**: E₃ = `opiCoreInG τ₃ E'` (nilpotent E' の `oPiCore_isHall_of_isNilpotent` +
  Hall card 同定) → `le_normalizer_opiCoreInG_of_le_normalizer`。
- 技法メモ: ⁅g,x⁆ element bracket をソースに直接書くと `Bracket Γ Γ` 不能
  (scoped notation)。`Subgroup.commutator_mem_commutator` + `commutatorElement_def` rw で回避。
  `(... : Subgroup _)` の型穴は normalizer 系で解決不能 → private abbrev
  (`sylowNormalizerE`/`sylowSelfE`) で明示。`set W := ...` を rcases 後の枝でやると
  既存変数を分裂させる (S09 の罠と同根) → obtain/rcases の前に固定。
- 再利用資産: `one_le_pRank_of_mem_primeFactors` (Cauchy→pRank≥1)、
  `isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one`、conjugation bridges、
  τ-partition 基本層、`isPiGroup_tau23_derived`。public 化:
  `S10.isCyclic_of_pRank_le_one`、`S10.le_of_coprime_card_index`。

**▶ 次 frontier** (着手可能残): **12.2(a)** (Lem 10.5 のみ・軽)、**12.19** (Cor 10.9(a)
のみ・軽)、**12.17** (Lem 6.3(a) 第 2 結論 `C_H(K)≤H'` の §6 補完が必要)、**12.18** (大物:
Thm 1.13 + Thm 3.7 + 式 (12.5)-(12.7))。残り 14 件は 10.13 ブロック (下記 triage)。

## ✅ 2026-06-10 (session 2): 12.2(a) + 6.3(a).2 + 12.17 COMPLETE

着手可能 leaf のうち 3 件を unconditional・axiom-clean で完成 (commits 240809c6 / 6cca7ee2 /
76f5fcbf)。全 full build 3613 green、AxiomsCheck 登録済。

- **12.2(a)** `prime_mem_sigma_or_tau2` (240809c6): 非自明 p-部分群 `X`, `M*∈ℳ(N_G(X))` ⇒
  `p∈σ(M*)∪τ₂(M*)`。BG は「by Lemma 10.5」と書くが Lem 10.5 は `X∈ℰ_p¹` 専用ゆえ直接不可。
  その内部の **cyclic-Sylow 論法** (`pRank_eq_two_of_normalizer_le` step(i) と同型) を一般
  p-部分群へ適応: `p∉σ(M*)` ⇒ `r_p(M*)≤2`; `r_p=1` なら Sylow p cyclic で `X` characteristic
  ⇒ `N_G(P)≤N_G(X)≤M*` ⇒ `p∈σ(M*)` 矛盾。Lem 10.5 自体は不使用。
  支持: `Isaacs.Ch04.characteristic_of_subgroup_of_isCyclic` を public 化。
  ⚠ 署名の `M/hM/hXM` は part (b) (τ₁∪τ₃ 非共役) 用に保持 (a では未使用、linter warning 容認)。
- **6.3(a) 第2結論** `centralizer_inf_le_derivedInG_of_isComplement'` (6cca7ee2, S06_Additional):
  `G` 可解, `H⊴G` 補群 `K`, `H⊆G'`, `(|H|,|K|)=1` ⇒ `C_H(K)⊆H'`。S06 docstring の「§10 critical
  path 外で TODO」を充足。証明 = `Ḡ=G/H'` で `H̄` 可換・`K̄` coprime 共役作用、action commutator
  `⁅H̄,K̄⁆=H̄` (第1結論) で全体 ⇒ Prop 1.6(d) で fixed points `C_Ḡ(K̄)⊓H̄=⊥` ⇒ `C_H(K)⊆ker=H'`。
  **リファクタ**: 汎用共役 bridge `actionCommutator_conj_map_subtype` /
  `fixedPointsOfMulAut_conj_map_subtype` を S12_E → S06_Additional へ上流移動 (S12 は selective
  open で従来どおり 12.1(f) 使用)。
- **12.17** `Msigma_E_relations` (76f5fcbf): `C_{M_σ}(E)⊆M_σ'` ∧ `⁅M_σ,E⁆=M_σ`。両結論とも
  Lem 6.3(a) を ↥M 内で適用 (M_σ normal Hall, 補群 E, M_σ⊆M') し `M.subtype` で G へ transport。
  transport 技法: `⁅A,B⁆.map=⁅A.map,B.map⁆` + `map_subgroupOf_eq_of_le`; centralizer は元ごと
  に ↥M へ持ち上げ。prereq: `Msigma_subgroupOf` (正規), `Msigma_le_derived`+`comap_map_eq_self`
  (`M_σ⊆M'`), `Msigma_subgroupOf_isHall.coprime_index`+`IsComplement'.index_eq_card` (coprime)。
  原典 (12.17) の `M_σ∩M^g` cyclic 評価は docstring 通り後続。

### ✅ 12.19 COMPLETE (keystone island, commit da142ebf)

- **12.19** `derivedE_centralizes_betaComplement` COMPLETE。⚠ **keystone island** (Cor 10.9(a)
  `beta_complement_centralizes` 消費ゆえ Prop 10.11(b)(c)(d) と同じ 2 軸に属す; unconditional
  ではない)。`#assert_axioms_island` 登録、full build 3613 green。実装した具体経路:
  - **抽象 Key Lemma** `exists_hall_actsTrivially_of_forall_sylow` (private, 再利用可能): A が
    可解 N に coprime 作用し各 Sylow が Hall π を固定 ⟹ A が Hall π を固定。witness = A-invariant
    Hall H₀ (`exists_aInvariant_hall`); 各 Sylow D は共役 c•H_D=H₀ (c は D-fixed,
    `aInvariant_hall_conj`) を固定 ⟹ D が H₀ 固定; 固定元は部分群で全 Sylow を含む ⟹ ⊤
    (index の各素因子 p で Sylow_p ≤ K ⟹ p∤index)。
  - **Helper** `exists_hall_subgroupOf_of_full_factorization` (private): C≤Nsub が full π-part を
    持てば C の Hall π は Nsub の Hall π (factorization 比較)。
  - **供給**: 各 prime Sylow D_q (image X_G ≤ M' q-group) は Cor 10.9 を r∈β'∩π(M_σ) ごと集めて
    C_{M_σ}(X_G) が full β'-part ⟹ Helper で Hall β' を中心化。φ:↥E'→*MulAut↥M_σ は
    `MulDistribMulAction.compHom`+`toMulAut` (S10_LocalLemmas テンプレ)。X_G=⊥ 枝は C=M_σ で
    Cor 10.9 不要 (∀ prime q を供給する必要があるため)。
  - 技法メモ: subgroup の MulAut smul は `toMonoidEnd` で展開されるので `show ... = c*h'*c⁻¹` で
    conj 形に戻す。`Subtype.ext` は `.val` 形を出し `.subtype` 形の hφ_coe と不一致 → `subtype_injective`
    を使う。`map_subtype_commutator` は bare だと unfold 形を rw 探索 → `have h:derivedInG=⁅,⁆` 経由。

### ▶ 残り着手可能 leaf (D-lane §12 next frontier)

- **12.18** `tau1_Malpha_interaction`: 大物 (Thm 1.13 + Thm 3.7(両 landed) + Uniqueness +
  Cor 10.9(a)(2) + 式 (12.5)-(12.7))。§11 非依存だが本文最厚クラス。Cor 10.9(a)(2) 消費なら
  keystone island になる見込み。S12_E 実 sorry は 12.19 完了で 15。

## ✅ 2026-06-10 (session 3): 12.18 building blocks 3 件 landed + 精密 assembly recipe

12.18 (`tau1_Malpha_interaction`, mmd L3484-3508, 本文最厚) を精密 recon し、**hard かつ
再利用可能な infrastructure 3 件**を sorry-free・unconditional・axiom-clean で land
(commits f111961f, b113206c)。assembly の全依存署名を確定 (全 dep 存在確認済)。

### landed building blocks (S12_E.lean, 全 axiom-clean)
- `maximalSubgroupsContaining_normalizer_ne_singleton_of_mem_tau1` (Helper A): `p∈τ₁ ∧ P≤M ∧
  P≠⊥ ∧ IsPGroup p P ⇒ ℳ(N_G(P))≠{M}`。Lemma 12.2(a) 背理。⟹ (12.6) の入力。
- `exists_charSubgroup_exponent_not_centralized` (BG Thm 1.13 機構): q-群 Q が r-群 R 正規化・
  非中心化 (奇位数) ⇒ ∃ R₁≤R char-in-R, exp r, Q 非中心化。`thompson_critical_omega` の
  `autCentralizer` r-群性 + φ:↥Q→*MulAut↥R で orderOf(φx) r-冪∧q-冪⟹1。**pure group theory・§13+ 再利用可**。
- `exists_invariant_sylow_Malpha_rank_three` (BB3): r∈α, α'-subgroup X≤M ⇒ ∃ R≤M_α X-不変 Sylow r,
  rank≥3。Lemma 10.3 テンプレ (`aInvariant_pSubgroup_le_aInvariant_sylow` を ⊥ から)。**X:=P⊔Q で使う**。

### 残 = (a) assembly + (b) reduction (issue 5003 に手順詳細・全 dep 名)
- **2 つの infra ギャップ判明**: (1) **Thm 10.2(d)** (M'非nilpotent⇒M_α≠1) 未形式化 →
  `derived_quotient_Malpha_le_fitting` (S10:1490) + quotient-by-⊥ で BB4 として要構築 (part b の M_α≠⊥);
  (2) **quotient 形 Thm 3.7 なし** → (a) hard core の QN/R₀ は ambient (Q⊔N⊔P)/R₀ 商で form-2 適用。
- (a) は **2 conjunct 別 land 推奨**: 第1 `C_{M_α}(P)≠⊥` [reachable ~150 行, 全 dep 確認] /
  第2 `C_{M_α}(PQ)=⊥` [hard core, Ω₁ cyclic bookkeeping + QN/R₀ quotient]。
- 確認済 assembly dep: `rank_centralizer_Malpha_le_one_of_not_uniqueMaximal` (12.5/12.6),
  `normalizer_le_normalizer_map_of_characteristic` (AppB:232, char⟹normalizer),
  `coprime_fixedPoints_quotient` (ForwardFromCh03:808, C_{QR₁}(P)≤R₁),
  `isNilpotent_of_normalizing_primeOrder_fixedPointFree` (Thm 3.7 form-2), `mem_elemAbelianOfRank` (|P|=p)。
  nilpotent⟹commute は S10_LocalLemmas:1080 が private ゆえ 2 行再証 (coprime orderOf)。

### session 3 cont.: assembly helpers 2 件 + (a) 第1連言 COMPLETE (計 6 commit)

- **H2** `inf_centralizer_sup_eq_bot_of_le_normalizer` + **card helper** `card_sup_eq_mul_of_le_normalizer_of_disjoint`
  (commit b6935baa) + `commute_of_coprime_orderOf_of_isNilpotent` de-privatize (S10_LocalLemmas)。
- **✅✅ (a) 第1連言 `tau1_Malpha_centralizer_P_ne_bot` COMPLETE** (commit fc769550,
  **unconditional・axiom-clean**) — `C_{M_α}(P)≠⊥`。building blocks 5 件が実合流。
  **(12.7) order-count 不要** (C_{R₁}(P)≠1 ⟹ C_{M_α}(P)⊇C_{R₁}(P)≠1)。FPF は H2 → element-wise
  (⟨a⟩=P via `eq_of_le_of_card_ge`) → Thm 3.7 form-2。
- **残 = (a) 第2連言 `C_{M_α}(PQ)=⊥`** [hard core: Ω₁ cyclic bookkeeping + QN/R₀ ambient-quotient
  Thm 3.7] + **part(b) reduction** (BB4 Thm10.2(d) + Uniqueness + Cor10.9(a)(2)) + assemble。
  全 building block は再利用可ゆえ第2連言/(b) は setup 共有可。詳細手順 = issue 5003。
- build 地雷録 (issue 5003 にも): `Nat.Coprime.mul` 不在 (Coprime=Eq, dot 不可) → `coprime_comm`+`Nat.Coprime.mul_right`;
  `orderOf_coe`/`orderOf_mk` 不在 → `orderOf_injective`; `rank_bot` 不在 → R≠⊥ は C(⊥)=⊤ 経由;
  `Subgroup.orderOf_dvd_natCard P haP` (subgroup 明示)。

## 2026-06-10 D-lane triage (issue 5002): §11 依存 vs 着手可能の定理単位分類

mmd L3023-3483 全 19 結果の証明を精読して依存を確定 (再 triage 不要)。
**ブロッカーの根 = Thm 11.7 / Lem 10.13 (どちらも Lemma 10.13 = c-bg-s10 委任領域)**。

### 着手可能 (§11 非依存) — 5 件

| 結果 | Lean name | 依存 (mmd 確認済) |
|---|---|---|
| **Lem 12.1** | `subgroupE_basic` | Thm 10.2 (`isHall_Msigma_Malpha`), Lem 4.5(a) (`exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic` の対偶), Prop 1.6(d) (`fixedPoints_isComplement_actionCommutator_of_abelian`), Lem 10.4(c) (`alpha_criterion`.2) |
| **Lem 12.2(a)** | `prime_mem_sigma_or_tau2` | Lem 10.5 のみ ((b) 非共役 clause が Thm 10.1(b) — Lean surface は (a) のみ) |
| **Lem 12.17** | `Msigma_E_relations` | Lem 6.3(a) のみ。`[M_σ,E]=M_σ` は landed (`commutator_eq_self_of_isComplement'_le_commutator`); `C_{M_σ}(E)⊆M_σ'` は Lem 6.3(a) **第 2 結論** (未 landed、§6 で証明可能・keystone 非依存) |
| **Lem 12.19** | `derivedE_centralizes_betaComplement` | Cor 10.9(a) (✅ landed) + 互いに素 |
| **Lem 12.18** | `tau1_Malpha_interaction` | Lem 12.2(a) + Thm 1.13 + Thm 3.7 (✅ landed) + Thm 10.2(d) + Uniqueness + Cor 10.9(a)(2) + 式 (12.5)-(12.7)。§11 非依存だが大物 |

### ブロック (Thm 11.7 = Lem 10.13 経由) — 14 件

- **Lem 12.3** (`elemAb_centralizes_meet`): 証明が **Thm 11.7 を直接使用** ("it follows from
  Theorem 11.7 that M*_σA ⊴ M*") + Cor 11.4 + Lem 10.12(a) + Lem 12.2(b)。
- **Prop 12.4** ← 12.3。 **Thm 12.5** ← 12.4 + **Thm 11.3/11.5/11.7 + Cor 11.6 直接**。
- τ₂-case cascade: **Cor 12.6** ← 12.5; **Thm 12.7** ← 12.5/12.6 + **Lem 10.13(b)(c) 直接**;
  **Lem 12.8** ← 12.7(a); **Cor 12.9** ← 12.8(e)/12.7(c); **Cor 12.10** ← 12.5(b)/12.7(a)/12.8(a);
  **Lem 12.11** ← 12.6/12.5/12.10(c)/12.7(d); **Thm 12.12** ← 12.7/12.8/12.6(c)/12.5(f)/12.11(c)。
- σ-side: **Thm 12.13** ← 12.10(a)(d)/12.4 + Cor 10.7(b); **Cor 12.14** ← 12.13;
  **Prop 12.15** ← 12.10(d)/12.2/12.5(e)/12.6; **Cor 12.16** ← 12.15/12.5(e)/12.6(f)。

⟹ forward-axiom 化はしない (LAUNCH.md の方針どおり §11 ブロック分は素通し)。10.13 が
解ければ §11 (11.5/11.6/11.7) → 12.3 → cascade が一斉に開く。

### ⚠ scaffold statement 訂正 (2026-06-10): 12.1(e) `E₂ ⊴ E₁⊔E₂` は旧 setup で偽

原文は **`E₁₂` を Hall τ₁∪τ₂-subgroup として固定し、`E₁`,`E₂` をその内部の Hall** に取る
(mmd L3029)。旧 `SubgroupESetup` は E₁/E₂ を E の独立な Hall とし `E12 := E₁ ⊔ E₂` と
再定義していたため、E₁ だけ共役でずらすと `E₂ ⋪ E₁⊔E₂` の反例が組める
(例: E = (C₃₁⋊C₁₅)×C₅, τ₁={3}, τ₂={5}, τ₃={31}; E₁ = ⟨a y a⁻¹⟩ (a∈C₃₁) に対し
⁅E₁,E₂⁆ が C₃₁ 成分を持ち E₁⊔E₂ = E ⊉ normalizer E₂)。
**修正 = `SubgroupESetup` に field `E₁₂_hall : IsHallSubgroup (tau1 M ∪ tau2 M)
((E₁ ⊔ E₂).subgroupOf E)` を追加** (原文 faithful 化)。producer 義務は §13 活用時に
12.1(e) と同じ論法 (E₁₂' ≤ O_{τ₂}(E₁₂) ≤ E₂ ⟹ E₂ ⊴ E₁₂ ⟹ |E₁E₂|=|E₁₂|) で果たせる
(非 vacuous)。S12/S13 に constructor 使用なし ⟹ 波及ゼロ。

### Lem 12.1 実装レシピ (確定)

- **(a) E' nilpotent**: 原文の Thm 10.2「M'/M_σ nilpotent」は repo 未収載 (docstring「追加予定」)。
  **Thm 4.20(a) `derived_le_fitting_of_rank_fitting_le_two` で代替** (issue 5001(b) と同じ手):
  E は σ'-群 (M_σ Hall σ の補群) ⟹ π(E)∩α=∅ ⟹ rank E ≤ 2 ⟹ E' ≤ F(E) nilpotent。
  rank≤2 論法は issue 5001 part(a) Step 2 のコードがテンプレート。
- **(d) E₁ cyclic**: E₁∩M' = ⊥ (π(E₁)⊆τ₁, π(M') 排反, card 論法) ⟹ E₁' = ⊥ abelian;
  各 Sylow cyclic (Lem 4.5(a) 対偶 + r_p(M)=1); abelian + 全 Sylow cyclic ⟹ cyclic
  (nilpotent π-分解 or `IsZGroup`)。E₃ cyclic は (b) E₃ ⊆ E' nilpotent + Sylow cyclic で同様。
- **(b)(f)**: p∈τ₃ ごと P = Sylow p of E。E' nilpotent ⟹ O_p(E')⊴E は P に入り
  O_{p'}(E')⊴E ⟹ **N⊔P_G ⊇ E' ⟹ N⊔P_G ⊴ E** (N = O_{p'}(E); quotient 回避、derived を含む
  部分群は normal)。Frattini (`Sylow.normalizer_sup_eq_top`) ⟹ E = N·N_E(P)。SZ で
  K = complement of P in N_E(P)。[P,K]=1 と仮定 ⟹ E' ≤ N⊔K' (commutator calculus,
  P abelian) ⟹ E' ≤ NK p'-群 ⟹ P∩E'=⊥、p∈π(E') に矛盾 ⟹ [P,K]≠1。
  Prop 1.6(d) (`fixedPoints_isComplement_actionCommutator_of_abelian`, φ = conj action) ⟹
  P = C_P(K) × [P,K]、P cyclic p-群の部分群束は鎖 ⟹ C_P(K)=⊥ ∧ [P,K]=P ⊆ E'。
  (f) は C_{E₃}(E) の p-part ⊆ C_P(K) = ⊥。
- **(e)**: π(E') ⊆ τ₂∪τ₃ (E'≤M'∩E, τ₁∩π(M')=∅) ⟹ E' ≤ E₂⊔E₃
  (`Subgroup.IsPiGroup.normal_le_hall`; E₂⊔E₃ = E₂E₃ Hall τ₂∪τ₃, card = |E₂||E₃| via E₃⊴E)
  ⟹ E₂⊔E₃ ⊴ E (⊇ derived)。E = E₁⊔(E₂⊔E₃) は card。E₂ ⊴ E₁₂ は新 field `E₁₂_hall` 経由で
  E₁₂'( ≤ E'∩E₁₂ τ₂-群 normal) ≤ O_{τ₂}(E₁₂) ≤ E₂。
- **(c)**: E ≠ ⊥ (M_σ ≤ M' ⊊ M, solvable nontrivial M ⟹ E ≅ M/M_σ ≠ 1)。E₂=E₁=⊥ なら
  (e) で E = E₃ ⊆ E' ⟹ perfect ⟹ E 可解と矛盾。
- **(g)**: `alpha_criterion`.2 直接 (p.Prime は `mem_primeFactors_card_of_pos_pRank` 経由)。

## 2026-06-02 B7 foundation checkpoint

Lean file: `OddOrder/BG/Ch3_MaximalSubgroups/S12_E.lean`.

Concrete surfaces now present:
- Definitions: `tau1`, `tau2`, `tau3`, and `SubgroupESetup` for `E` complement data and Hall `E₁/E₂/E₃`.
- New API: membership rewrites for `tau1`/`tau2`/`tau3`, `tau_i ⊆ sigma(M)'` projections, rank/derived-prime projections for `tau_i`, disjointness helpers between `tau1` and `tau3`, named joins `E12`, `E23`, `E123`, and `SubgroupESetup` projection lemmas (`E_complement`, `E1_le_M`, `E2_le_M`, `E3_le_M`, `E12_le_E/M`, `E23_le_E/M`, `E123_le_E`).

Current Lean inventory: 19 theorem-level `sorry`s remain in §12, matching the 19-result scaffold.

Main proof blockers: §10 Hall/fusion/beta results, §11 exceptional maximal endpoints, BG Lemma 4.5/Thm 4.20, Proposition 1.6(d), Theorem 1.13, Theorem 3.7, and the Uniqueness Theorem. The `SubgroupESetup` fields intentionally do not include any of these hard conclusions.

**スコープ**: BG §12 (pp.83–96), mmd L3023-3483, **19 結果** (そのうち主要 15 個).  
形式化先 (予定): `OddOrder/BG/Ch3_MaximalSubgroups/S12_SubgroupE.lean` (2 ファイル分割の可能性大)  
ROADMAP 上の位置: Phase 2a 第 4 波 (§10-§11 完成必須)  
役割: 部分群 E の構造定理と共役性、§13 Prime Action の前提  
難度: **★★★★★** (本文最大級、460 行で 15 主要結果、局所解析特有概念)

---

## TL;DR: §12 は単独で小章相当の大規模構造理論

§12 は **最大部分群 M の補集合 E (≅ M/M_σ) の精密構造** を 460 行かけて確立する本文最大級の節. 典型的には小規模な lemma chain だが、ここでは:

1. **E の基本構造** (12.1): E' nilpotent, r(E) ≤ 2, すべての Sylow 部分群 abelian
2. **τ₂(M) ≠ ∅ の場合** (12.5–12.12): 最も複雑な subsection (8 主要結果群)
3. **σ(M) 側の埋め込み** (12.13–12.19): nonabelian p-subgroup の一意性と M_σ の埋め込み制御

形式化では **2000+ 行の Lean 予想**. 単一ファイルは避けるべき. むしろ conceptual chunks に分割:
- `S12A_Structure.lean`: 12.1–12.4 (基本構造)
- `S12B_Tau2.lean`: 12.5–12.12 (τ₂ case 中心)
- `S12C_Sigma.lean`: 12.13–12.19 (σ(M) / embedding)

---

## §12 全 19 結果の精密リスト

| No. | 名前 | 型 | L範囲 | 概要 | 主キーワード |
|-----|------|-----|------|------|-------------|
| 1 | **Lemma 12.1** | Lemma | 3035–3060 | E' nilpotent, E₁ cyclic, E₃ ◁ E, C_{E₃}(E)=1 | Structure of E, cyclic radicals, kernel relations |
| 2 | **Lemma 12.2** | Lemma | 3062–3069 | p-subgroup X の normalizer の maximal subgroup 分類 | Maximal containment, τ-notation |
| 3 | **Lemma 12.3** | Lemma | 3071–3093 | A ∈ E_p²(M ∩ M*) が M_σ ∩ M* を centralize | Coprime action on p'-subgroups |
| 4 | **Prop 12.4** | Proposition | 3095–3126 | A ∈ E_p²(M) ⟹ C_G(A) ⊆ M (かつ condition on hypothesis 11.1) | Exceptional maximal existence |
| 5 | **Thm 12.5** | Theorem | 3129–3148 | τ₂(M) ≠ ∅ ⟹ M_σ nilpotent, abelian Sylow p, M_σA ◁ M | Main τ₂ case, nilpotent control |
| 6 | **Cor 12.6** | Corollary | 3150–3169 | τ₂(M) ≠ ∅, A ∈ E_p²(E) ⟹ A ◁ E, C_G(A) ⊆ E | Normality in E, centralizer bounds |
| 7 | **Thm 12.7** | Theorem | 3171–3220 | Nonabelian Sylow p, τ₂(M) ≠ ∅ ⟹ τ₂(M) singleton, A₀ ∈ E^1(A), E₀ complement | Abelian vs. nonabelian Sylow split |
| 8 | **Lemma 12.8** | Lemma | 3223–3259 | Abelian Sylow p, τ₂(M) ≠ ∅ ⟹ E₂ abelian Hall τ₂-subgroup | Abelian case structure, exponent preservation |
| 9 | **Cor 12.9** | Corollary | 3260–3269 | [A,Q] ≠ 1 (A ∈ E_p², Q ∈ E_q¹) ⟹ decomposition A = A₀ × A₁ | Conjugacy non-isomorphism |
| 10 | **Cor 12.10** | Corollary | 3270–3283 | (a) nilpotent σ(M)'-subgroup abelian, (b) E₂, E' abelian | Nilpotency & abelianity summary |
| 11 | **Lemma 12.11** | Lemma | 3284–3305 | M* ∈ M(N_G(A)) ⟹ τ₂(M) ⊆ σ(M*) - β(M*) | τ₂ transfer to other maximal |
| 12 | **Thm 12.12** | Theorem | 3306–3344 | C_{M_σ}(e)=1 ∀(τ₁∪τ₃)-element e ⟹ A₀ abelian normal, E₀ Frobenius complement | Frobenius structure existence |
| 13 | **Thm 12.13** | Theorem | 3347–3368 | Nonabelian p-subgroup ⟹ p ∈ U (一意性集合) | Nonabelian p-group uniqueness |
| 14 | **Cor 12.14** | Corollary | 3369–3384 | p ∈ σ(M), X ∈ E_p¹(M), p ∈ β(M) or X ⊆ M_σ' ⟹ M(C_G(X)) = {M} | σ(M) side maximal uniqueness |
| 15 | **Prop 12.15** | Proposition | 3385–3422 | q ∈ σ(M), X nonid q-subgroup ⟹ conditions on M* ∈ M(N_G(X)) | σ(M) containment in other maximal |
| 16 | **Cor 12.16** | Corollary | 3423–3447 | σ(M)-subgroup Y ⟹ Y conjugate to M_σ subgroup | σ(M)-subgroup conjugacy |
| 17 | **Lemma 12.17** | Lemma | 3448–3453 | C_{M_σ}(E) ⊆ M_σ', [M_σ,E] = M_σ, M_σ ∩ M^g cyclic β(M)'-group | Embedding M_σ in G via E action |
| 18 | **Lemma 12.18** | Lemma | 3454–3479 | p ∈ τ₁(M), P ∈ E_p¹, Q P-inv q-subgroup, C_Q(P)=1, M(N_G(Q)) ≠ {M} ⟹ control of M_α | τ₁ & σ interaction |
| 19 | **Lemma 12.19** | Lemma | 3480–3482 | E' centralizes Hall β(M)'-subgroup of M_σ | Derivedrator & β partition |

**集計**: 3 Theorem + 5 Corollary + 11 Lemma + 1 Proposition = **19 結果**.  
**主要度**: 12.1–12.4 (基礎), 12.5–12.11 (τ₂ case の中核, 8 結과), 12.13–12.19 (σ(M) uniqueness & embedding)

---

## E の精密定義

### E の導入と記法 (L3023–3032)

**Hypothesis**: M は maximal subgroup of G. **E は M_σ の M 内での complement** = $E \cong M/M_σ$ with $M = E \ltimes M_σ$ (semidirect product, 単なる product ではない).

**π(E) = τ₁(M) ∪ τ₂(M) ∪ τ₃(M)** に分割:

- **τ₁(M)** = {p ∈ σ(M)' | p ∉ π(M'), r_p(M) = 1}
  - p は σ(M) に属さず、M' に出現せず、rank 1
  - r_p(E) = 1 でもあり
  
- **τ₂(M)** = {p ∈ σ(M)' | r_p(M) = 2}
  - σ(M) に属さず、rank 2
  - **最も複雑な case** (12.5–12.12 の中核)
  
- **τ₃(M)** = {p ∈ σ(M)' | p ∈ π(M'), r_p(M) = 1}
  - σ(M) に属さず、M' に出現、rank 1

### Hall subgroup decomposition

E_{12}, E_1, E_2, E_3 は対応する Hall subgroups of E or E_{12}:

- **E_{12}** = Hall (τ₁ ∪ τ₂)-subgroup of E
- **E_1** = Hall τ₁-subgroup of E_{12}
- **E_2** = Hall τ₂-subgroup of E_{12}
- **E_3** = Hall τ₃-subgroup of E

重要な関係:
- **E = E₁E₂E₃** (coprime order product)
- **E₁₂ = E₁E₂**
- **E₂E₃ ◁ E** (Lemma 12.1(e))
- **E₂ ◁ E₁₂** (Lemma 12.1(e))

---

## 15 結果のグループ化と依存構造

### Group A: E の基本構造 (結果 1–4, 12.1–12.4, L3023–3126)

**概要**: E の抽象的構造定理. τ notation 導入, Hypothesis 11.1 への bridge.

**主要定理**:
- **12.1**: E' is nilpotent, E₁ & E₃ cyclic, E₃ ◁ E, C_{E₃}(E)=1
- **12.2**: p-subgroup X の normalizer での maximal subgroup の τ 分類
- **12.3**: A-centralization lemma (preparation for 12.4)
- **12.4**: A ∈ E_p²(M) ⟹ C_G(A) ⊆ M + exceptional maximal existence condition

**数学的流れ**:
1. Thm 10.2 (M'/M_σ nilpotent) ⟹ E' nilpotent (12.1(a))
2. Frattini argument & rank argument ⟹ E₁, E₃ cyclic (12.1(d))
3. τ partition の閉性確認 (12.2 via rank calculation)
4. C_G(A) ⊆ M の基本的なことが従う (12.4(a), Thm 11.1 hypothesis setup)

**形式化予想**: 150–200 行 (per-result 15–25 行, proof のみ).

**依存**: §10 (τ notation 定義), §11 (Hypothesis 11.1), Lemma 4.5 (cyclic p-group rank 1), Frattini argument (Proposition 1.6(d)), Thm 10.2.

---

### Group B: τ₂(M) ≠ ∅ の詳細構造 (結果 5–12, 12.5–12.12, L3127–3344)

**概要**: τ₂(M) が非空のとき (= rank 2 prime case) の最複雑な局所解析. **最も厚い subsection** (218 行, 8 主要結果).

**文脈**: §11 Hypothesis 11.1 がここで activate される.

**主要定理**:

1. **Thm 12.5**: τ₂(M) ≠ ∅ ⟹
   - M_σ is nilpotent
   - Sylow p-subgroups of M abelian, Ω₁(P) = A (= M_σA ◁ M)
   - C_{M_σ}(A) = 1
   - M_σ ∩ M* = 1 for M* ∈ M(A) - {M}

   **Thm 11.5, 11.7 の直接的応用**, ただし A は E 側 (not M_σ 側).

2. **Cor 12.6**: τ₂(M) ≠ ∅, A ∈ E_p²(E) ⟹
   - A ◁ E (because M_σA ◁ M by 12.5(c) + M = M_σE)
   - C_G(A) ⊆ N_M(A) = E
   - M(C_G(X)) = {M} for certain X ∈ E_p¹(E)

   **Key implication**: τ₂ prime の元素的abelian 2-group A は E 内で normal + centralizer bound.

3. **Thm 12.7**: Sylow p-subgroup nonabelian case ⟹
   - τ₂(M) = {p} (singleton)
   - A₀ = C_A(M_σ) has order p, F(M) = M_σ × A₀
   - E₀ = complement to A₀ in E

   **Technical peak**: Sylow p-subgroup が nonabelian の場合の最精密な factorization.

4. **Lemma 12.8**: Sylow p-subgroup abelian case ⟹
   - E₂ abelian ◁ E
   - E₂ Hall τ₂(M)-subgroup of G
   - S ⊆ N_G(S)' ⊆ F(E) ⊆ C_G(S) ⊆ E
   - N_G(A) = N_G(S) = N_G(E₂) = ... (many equalities)

   **Abelian Sylow case での simplification**.

5. **Cor 12.9**: [A,Q] ≠ 1 (A ∈ E_p², Q ∈ E_q¹, q ∈ τ₁(M)) ⟹
   - A = A₀ × A₁ (decomposition)
   - A₀ = [A,Q] ∈ E¹(A) with N_G(A₀) = M
   - A₁ conjugate と non-isomorphic in G
   - C_G(A₁) ⊄ M

   **Interaction between τ₂ & τ₁**.

6. **Cor 12.10**: Summary corollaries:
   - (a) Nilpotent σ(M)'-subgroup abelian
   - (b) E₂, E' abelian
   - (c) E₂E₃ ⊆ C_E(A) ◁ E, π(E/C_E(A)) ⊆ τ₁(M)
   - (d) Noncyclic p-subgroup P ∈ σ(M) ⟹ N_G(P) ⊆ M
   - (e) x ∈ E with π(⟨x⟩) ⊆ τ₂(M), C_{M_σ}(x) ≠ 1 ⟹ M(C_G(x)) = {M}

   **Corollary anthology**, §13 で多用.

7. **Lemma 12.11**: M* ∈ M(N_G(A)), τ₂(M) ≠ ∅, A ∈ E_p²(E) ⟹
   - τ₂(M) ⊆ σ(M*) - β(M*)
   - π(E/C_E(A)) ⊆ τ₁(M*) ∪ τ₂(M*)
   - Condition on q ∈ π(E/C_E(A)) ∩ π(C_E(A))

   **τ₂ from M transfer to other maximal**.

8. **Thm 12.12**: "Frobenius condition" (C_{M_σ}(e)=1 for all (τ₁∪τ₃)-elements e) ⟹
   - ∃ abelian normal A₀ with C_E(x) ⊆ A₀ ∀ x ∈ M_σ#
   - ∃ E₀ of same exponent as E, E₀M_σ is Frobenius group kernel M_σ

   **Richest structural theorem**: 12.12 は 5 page proof (L3306–3344) で case splitting on C_E(S) ⊆ E か否か.

**数学的highlight**: 12.5–12.8 で τ₂ case の abelian vs. nonabelian Sylow split を完全に解決. 12.9–12.12 では other maximal への transfer と Frobenius factorization.

**形式化予想**: 600–800 行 (per-result 50–80 行, proofs が thick).

**依存**: §11 (Hypothesis 11.1 + Thm 11.3, 11.5, 11.7), §10 (Corollary 10.9, Lemma 10.10, 10.12, 10.13), Prop 1.5, 1.6 (A-invariant, Frattini), Lemma 4.5 (cyclic), Maschke (1.5).

---

### Group C: σ(M) の埋め込みと一意性 (結果 13–19, 12.13–12.19, L3345–3482)

**概要**: nonabelian p-group と σ(M) の側面. M_σ の G への埋め込み制御, τ₁ との相互作用.

**主要定理**:

1. **Thm 12.13**: Nonabelian p-subgroup ⟹ p ∈ U (unique maximal set)

   **最も簡潔な一意性定理**. Corollary 12.10(d) + cyclic vs. nonabelian Sylow split.

2. **Cor 12.14**: p ∈ σ(M), X ∈ E_p¹(M), p ∈ β(M) or X ⊆ M_σ' ⟹
   - M(C_G(X)) = {M}

   **σ(M) side での C_G(X) uniqueness**.

3. **Prop 12.15**: q ∈ σ(M), X nonid, M* ∈ M(N_G(X)) - {M} ⟹
   - M* ≄ M
   - N_G(S) ⊆ M (S = Sylow q-subgroup of M ∩ M*)
   - Case split on q ∈ σ(M*): (d) q ∈ σ(M*) + (e) q ∉ σ(M*)

   **Most general σ(M) interaction**, Corollary 12.6(f) の σ disjointness 確立.

4. **Cor 12.16**: σ(M)-subgroup Y ⟹
   - Y conjugate to subgroup of M_σ
   - For p ∈ π(E) ∩ β(G)', H ∈ M(Y) not conjugate to M: r_p(N_H(Y)) ≤ 1, etc.

   **σ(M)-subgroup の conjugacy class**.

5. **Lemma 12.17**: Embedding relations
   - C_{M_σ}(E) ⊆ M_σ'
   - [M_σ, E] = M_σ
   - M_σ ∩ M^g cyclic β(M)'-group (g ∈ G - M)

   **Intersection structure** across conjugates.

6. **Lemma 12.18**: τ₁ & M_α interaction
   - p ∈ τ₁(M), P ∈ E_p¹(M), Q P-inv q-subgroup, C_Q(P)=1, M(N_G(Q)) ≠ {M}
   - ⟹ (a) M_α ≠ 1 & q ∉ α(M) ⟹ C_{M_α}(P) ≠ 1 & C_{M_α}(PQ) = 1
   - ⟹ (b) Q Sylow ⟹ α(M) = β(M) (key: β = α characterization)

   **Delicate τ₁ argument**, 引用頻度が高い (§13 の 3 spots).

7. **Lemma 12.19**: E' centralizer
   - E' centralizes Hall β(M)'-subgroup of M_σ

   **Coprime order product** (E' と M_σ が互いに素).

**数学的highlight**: Group C は Group B (τ₂ case) の completion. 12.13 で nonabelian p-group の一意性を secured. 12.15–12.17 で σ(M) の family across conjugates の structure. 12.18–12.19 は more specialized interactions.

**形式化予想**: 300–400 行 (per-result 30–50 行).

**依存**: Thm 12.13 (nonabelian uniqueness), Corollary 12.10 summary, Group A & B prior results, Lemma 10.12 (β-related), §9 Uniqueness Theorem (maximal comparison).

---

## 下流での引用と接続

### §13 Prime Action での §12 利用

§13 (L3484–3739) は "Prime Action" = derived series with Thompson-style actions. **§12 の 13 spots から引用**:

- **Thm 13.1–13.9**: §12 から Cor 12.6(d), Lemma 12.18 (a), Thm 12.7, Thm 12.13 などを multi-step composition で利用
- **Key dependency**: 12.18 は 13 で 3+ spots で引用 (τ₁ & M_α の interaction)
- **Frobenius factorization**: Thm 12.12 が Lemma 14.1 で引用 (§14 での type-P maximal の Frobenius family への応用)

### §14–§15 への cascade

- **Prop 14.2**: Thm 12.5(a) (M_σ nilpotent) を前提に counting argument 展開
- **Thm 14.3–14.6**: Cor 12.6, 12.10 summary に依存して maximal family counting
- **Thm 15.2**: Lemma 12.19 (E' ∩ Hall β(M)') を使用

---

## Peterfalvi との関係

**BG App.C "Final Contradiction" との重複**: App.C は Peterfalvi 1984 paper の改訂版. その論文は **Peterfalvi 本体 §9 (04.9_*.mmd)** と論理的に同一.

**§12 と Peterfalvi §9 の接続**:
- Peterfalvi §9 は **type-I group (non-existence) の証明** で global counting / Frobenius family argument を展開
- BG §12 の **Thm 12.12 (Frobenius structure)** + Thm 12.13 (nonabelian uniqueness) が Peterfalvi §9 の local prerequisites
- Phase 2b で Peterfalvi §9 を形式化するとき、§12 の Thm 12.12–12.13 + Cor 12.10 は **既に mathlib に integrated** な状態が理想

**BG独自性**: BG §12 の Group A (12.1–12.4) は Peterfalvi には explicit に出現せず. これは **BG の local setup の汎用性** を示す (complement definition, τ notation などが Peterfalvi 以外の contexts でも出現).

---

## mathlib カバレッジ

### 既存 (high)
- **Solvable**: Group theory, solvable series, derived series API
- **Sylow**: Sylow subgroup existence, conjugacy
- **Nilpotent**: Fitting subgroup (Phase 1 で実装予定)
- **Coprime action**: Basic `CoprimeAction` API (mathlib 既存)
- **Frattini argument**: (mathlib にはないが §1 で BG が定義, Phase 2a で実装)

### 一部 / 新規 (mid)
- **A-invariant Hall theory**: Basic Hall は mathlib にあるが、coprime action 下の A-invariant completion は **新規** (§1 Prop 1.5)
- **p-group rank**: Basic rank function は mathlib にあるが、Blackburn rank ≤ 2 decomposition は新規
- **Cyclic p-group characterization**: Lemma 4.5 (rank 1) — 新規

### 完全新規 (low)
- **τ₁, τ₂, τ₃ notation & partition**: §12 独自の fine partition. mathlib には無い
- **E の定義**: complement of M_σ in M — 新規 structure (group extension theory で後に generalize 可)
- **Thm 11.1 Hypothesis**: Exceptional maximal の machinery — §11 で新規
- **Group A–C の 19 結果全て**: 新規証明体系

### Phase 2a での実装ボリューム

- **§12 alone**: 2000+ 行 Lean 予想
  - Lemma 12.1 proof: 100+ 行 (Frattini, rank calculation multi-case)
  - Thm 12.5 proof: 150+ 行 (Thm 11.5, 11.7 composition)
  - Thm 12.7 proof: 200+ 行 (Sylow abelian vs. nonabelian split, exponent preservation)
  - Thm 12.12 proof: 250+ 行 (case C_E(S) ⊆ E, regular action on M_σ)
  - Thm 12.13 proof: 100+ 行 (generator-relation argument, focal subgroup)
  - Remaining (12.2, 12.3, 12.4, 12.6, 12.8–12.11, 12.14–12.19): 800–1000 行

- **合計 mathlib additions**: §12 dedicated + §10–§11 adjacent = **5000+ 行 Lean code** (cf. §12 mmd 460 行)

---

## 形式化規模と 2 ファイル分割の検討

### なぜ分割が必要か

単一の `S12_SubgroupE.lean` では:
- **2000+ 行 threshold**: IDE navigation, compilation time の悪化
- **Conceptual boundary**: Group A (structure), Group B (τ₂ case), Group C (σ & uniqueness) は論理的に distinct
- **Reusability**: Group A だけ import する downstream module があり得る (§13 では主に Group C 引用)

### 提案分割スキーム

**Option 1: 3 ファイル分割 (推奨)**

```
OddOrder/BG/Ch3_MaximalSubgroups/
  └─ S12_SubgroupE/
     ├── A_Structure.lean          (12.1–12.4, ~200 行)
     ├── B_Tau2Case.lean           (12.5–12.12, ~800 行)
     └── C_Sigma_Embedding.lean    (12.13–12.19, ~300 行)
  └─ S12_SubgroupE.lean            (aggregate, ~50 行 = imports + docstring)
```

**利点**:
- Group A は independent-ish (12.1–12.3 は pure structure, 12.4 は Hypothesis 11.1 bridge のみ)
- Group B は heaviest, most intricate (sub-section として隔離価値大)
- Group C は Group A だけに depend, Group B には weak dependency

**欠点**: Lean 4 では subdirectory の import convention が要注意 (relative imports, module hierarchy).

**Option 2: 2 ファイル分割**

```
OddOrder/BG/Ch3_MaximalSubgroups/
  ├── S12A_Structure.lean       (12.1–12.4, ~200 行)
  └── S12B_MainTheorems.lean    (12.5–12.19, ~1200 行)
```

**利点**: Module hierarchy が simpler.  
**欠点**: S12B が重過ぎる (1200 行は IDE 限界手前).

### 推奨: Option 1 (subdirectory 分割)

Lean 4 module convention にて:

```lean
namespace OddOrder.BG.Ch3.S12

-- In A_Structure.lean
theorem lemma_12_1 : ... := ...
theorem prop_12_4 : ... := ...

-- In B_Tau2Case.lean
import .A_Structure
theorem thm_12_5 : ... := ...
theorem thm_12_12 : ... := ...

-- In C_Sigma_Embedding.lean
import .A_Structure
theorem thm_12_13 : ... := ...
theorem lemma_12_19 : ... := ...

-- In S12_SubgroupE.lean (aggregate)
import .A_Structure
import .B_Tau2Case
import .C_Sigma_Embedding
```

---

## Phase 2a 形式化着手順

### Timeline (estimate)

**Phase 2a 第 4 波** = §10–§13 parallel completion

1. **§10 M_α/M_σ** (2 week, 1500 行): prerequisite
2. **§11 Exceptional** (1 week, 500 行): prerequisite
3. **§12 Subgroup E** (4 week, 2000 行, **this section**)
   - Week 1: Group A (structure, 200 行)
   - Week 2: Group B (τ₂ case, 800 行) ← **heaviest**
   - Week 3: Group B continued (proofs refinement, type-checking)
   - Week 4: Group C (σ & embedding, 300 行)
4. **§13 Prime Action** (2 week, 800 行): depends on §12, parallel possible

### Intermediate milestones

- **After Group A**: Can export structure definitions (E₁, E₂, E₃, τ-partition) for downstream
- **After Thm 12.5**: Core τ₂ machinery ready. Thm 12.13 starts becoming provable
- **After Thm 12.12**: Frobenius structure availability, early §14 lemmas can start

### Dependency verification checklist

- [ ] §10 (M_α, M_σ) fully formalized
- [ ] §11 (Exceptional) fully formalized
- [ ] Hypothesis 11.1 Lean definition + characterization
- [ ] Prop 1.5 (A-invariant Hall) available in §1
- [ ] Prop 1.6(d) (Frattini + coprime) available in §1
- [ ] Lemma 4.5 (cyclic p-group) available in §4
- [ ] Maschke / Schur-Zassenhaus available (mathlib)
- [ ] Thm 10.2, Corollary 10.7, Lemma 10.12, 10.13 ready (§10)
- [ ] Thm 11.3, 11.5, 11.7 ready (§11)

---

## 未解決 / TODO

### 数学的な精査

1. **Thm 12.7 vs. 12.8 の completeness**: nonabelian vs. abelian Sylow p の split が complete か確認. 原文 L3217 "By (a)" の implicit case coverage を explicit に.

2. **Thm 12.12 の case analysis**: `C_E(S) = E` vs. `C_E(S) ≠ E` の分岐が exhaustive か. Proof では Q/Q₀ acting regularly on S の condition が critical だが、逆方向 (not regular) の処理が clear か.

3. **Cor 12.9 の非同型性**: "A₀ is not conjugate to A₁ in G" (12.9(b)) の証明が rank argument だが、nonabelian p-subgroup の existence が guaranteed される context を確認.

4. **τ₁ & τ₃ の interaction**: Lemma 12.18 は τ₁(M) に限定. τ₃(M) ≠ ∅ の場合の similar statement はあるか? L3454 では τ₁ only.

### Formalization-specific

1. **Naming convention**: τ₁, τ₂, τ₃ を Lean identifier に (e.g., `tau₁ M`, `Tau2_set M`). mmd での `\tau_{i}(M)` notation を Lean に上げる方法.

2. **Group A–C の import graph**: Subdirectory 分割の際、A_Structure → B_Tau2Case → C_Sigma の dependency が **linear chain か DAG か** を確認. DAG の場合 B & C の parallel formalization 可.

3. **Proof automation**: Lemma 12.1, 12.2 は rank calculation が repetitive. `omega` or `decide` で partial automation 可か.

4. **LTE との比較**: Lean Feit-Thompson project (2012–) での この section に対応部分があるか, notation/approach の参照価値.

### 下流への影響

1. **§13 前提の early validation**: Cor 12.10 (summary) が 13 で heavily used. 12.10 の formalization 後 early sanity check で §13 の first lemma を try-formalize.

2. **Thm 12.12 & §14 の timing**: Thm 12.12 (Frobenius) は Lemma 14.1 で引用. 14 の formalization 開始前に 12.12 の completeness check.

3. **App.C との sync**: Phase 2b Peterfalvi 開始時に, §12 の Thm 12.12–12.13 と App.C の correspondence を docstring で明文化.

---

## 統計サマリー

| 項目 | 数値 |
|------|------|
| mmd 行数 | 460 |
| 主要結果数 | 15 (+ 4 sub-corollaries = 19 total) |
| 群分け | A (4), B (8), C (7) |
| 予想 Lean 行数 | 2000–2200 |
| 平均 per-result | 100–140 行 |
| 推定 formalization 期間 | 4 week (1 person) |
| mathlib 新実装 | τ-partition, E definition, Thm 11.1 machinery |
| 下流引用 spots | §13 (13+), §14 (5+), §15 (2+) |
| ファイル数 (推奨) | 4 (3 modules + aggregate) |

---

## まとめ

BG §12 "The Subgroup E" は **局所解析の中核** で、M の complement E の精密構造を 460 行で確立する本文最大級の定理群. τ₂ case (12.5–12.12) が最重要で、そこで abelian vs. nonabelian Sylow p の split、M_σ の nilpotency、maximal subgroup の family structure などが secured される.

形式化では **2000+ 行 Lean** が予想され、3 ファイル分割 (A_Structure, B_Tau2Case, C_Sigma_Embedding) で conceptual clarity と module reusability を両立. Phase 2a 第 4 波の center piece として §10–§11 の直後に着手し、§13 と部分的に並列化可.

数学的には §12 単独で **局所解析教科書の 1 章相当** の深さを持つ. 形式化者は proof の key idea (Frattini, rank calculation, coprime action の clever use) を理解した上での implementation が critical.

---

*作成日: 2026-05-22*  
*出典: BG local-analysis.mmd L3023–3483, PDF pp.83–96*  
*参考: BG §10 (M_α, M_σ), §11 (Exceptional), §13 (Prime Action), App.C (Peterfalvi)*

