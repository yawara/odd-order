# BG §13: Prime Action — per-section 調査ノート

## 2026-06-12 Lane G session 1: STATEMENT AUDIT — 🛑→✅ 解消済 (2026-07-02: issue 8000 closed、§13 全証明済 — 以下履歴)

**結論: §13 は現状の §12 surface では着工不能。根の Lemma 13.1 が BG Cor 12.16(a)(b) を要し、
その statement が repo に存在しない。** LAUNCH.md 手順 3 (着工前必須 audit) の所見。

### 環境
- `git merge --ff-only main` 成功 (`aa5231be`→`f1408227`; S10 分割 4 ファイル取り込み)。
- `lake build …S13_PrimeAction` 緑 (3067 jobs, scaffold 実 sorry 11)。
- mmd 実行番号は notes 旧記載とズレ: §13 = **L3526-3739** (Lem 13.1 = L3528, notes 旧 L3498 は古い抽出)。
  §12 cited: Thm 12.13=L3377, Cor 12.14=L3399, Prop 12.15=L3417, Cor 12.16=L3453, Lem 12.17=L3478,
  Lem 12.18=L3484, Lem 12.19=L3510。

### audit 結果 (4 指定 statement + 周辺)
| BG | Lean (S12) | faithful? | 備考 |
|---|---|---|---|
| Thm 12.13 | `nonabelian_pgroup_isUniquelyMaximal` (S12_E:49) | ✅ | 完全一致 |
| Cor 12.14 | `maximalContaining_centralizer_eq_singleton` (S12_E:57) | ⚠ 不完全 | `ℳ(C_G(X))={M}` のみ。原典 `ℳ(P)={M}` (P=Sylow p of M_σ) を**脱落**。Lemma 13.6 が `ℳ(S)` に要する → 13.6 着工時に要対応 |
| Prop 12.15 | `sigma_subgroup_maximal_interaction` (S12_E:458) | ✅ | (a)-(e) 全 faithful。`complement` は `M*_σ⊓(M⊓M*)=⊥ ∧ ⊔=M*` |
| **Cor 12.16(a)(b)** | **存在しない** | 🛑 | `sigma_subgroup_conj_into_Msigma` (S12_E:64) は docstring が「12.16(a)」だが**実体は前置節「Y conj into M_σ」のみ**。rank bound `r_p(N_H(Y))≤1` (a) と π-bound `p∈τ₁⟹p∉π(N_H(Y)')` (b) **未述**。S12_E:29 も「12.16(b) deferred」と自認 |

### なぜ全 §13 が gate されるか
- §13 は **Lemma 13.1 を根とする DAG**: Cor 13.2 は「follows directly from Lemma 13.1」(mmd L3554)、
  以降 13.3/13.4/…/13.11 は全て 13.2 か 13.4 経由。独立に着工できる §13 結果は無い。
- Lemma 13.1 (3 結論) の証明は **3 つとも Cor 12.16(a) を要する**:
  - (b) `p∉τ₂(M*)`: `r_p(N_{M*}(Y))=2` (12.1(g)) vs `≤1` (12.16(a)) の矛盾 (mmd L3538)。
  - (c) `p∈τ₁(M)⟹p∈β(G)`: 12.16(b) の対偶 (mmd L3540)。
  - (a) centralization: `p∈σ(M*)∪τ₃(M*)` (= (b) で τ₂ 除外) 経由で Sylow `S⊆M*'` を取るので (b) 依存。

### 在庫 OK な §12/§10 依存 (cite 可)
12.1(d) E₁/E₃ cyclic (S12_ECore:835,910) ✅ / 12.1(g) `isMaximalElementaryAbelian_of_mem_tau2`
(S12_ECore:490; ただし `¬idealPrime`=「p∉β(G)」部分のみ直接, 「r_p(N_{M*}(Y))=2」は別途要導出) /
12.2(a) (S12_ECore:1218) ✅ / 12.5 (S12_Theorem125:94) ✅ / 12.6(a)(b)(c) (S12_Corollary126) ✅ /
12.13/12.15/12.18(a) (S12_Lemma1218) ✅ / 12.17 (S12_E:74, **実証明済**) ✅ /
10.8 (S10_BetaRadicalCore) ✅ / 10.12(a) `disjoint_of_not_conj` (S10_LocalLemmasCore:1200) ✅。
未再確認 (13.6/13.7/13.9 着工時に): 12.5(d), 12.6(d), 12.6(f)。

### 解消パス (要 hub/ユーザー裁可 — session 1 末で提示)
1. **(推奨) hub/Lane F が S12_E へ Cor 12.16(a)(b) の sorry'd statement を追加** → G が cite。
   architecture 最善 (statement は §12 に属す)。issue 8000 に drop-in 署名あり。G は短時間待機。
2. ユーザー承認のもと G が §13 helper で 12.16(a)(b) を **forward axiom** 宣言 → 即着工、後で de-axiom。
3. G が 12.16(a)(b) を §13 側で **実証明** (sorry 無し, sorry'd Prop 12.15 引用) → idle/axiom 無しだが
   §12 仕事を G レーンで抱える + 合流時 relocate (~150-250 行, 非推奨)。

→ 詳細・署名は **issue 8000** (`issues/8000-s13-blocked-cor1216ab.md`)。

### session 1 進捗 (forward axiom path 採択後)

- **forward axiom インフラ確立** (commit `c8080f87`): 新 leaf `S13_Lemma131.lean` に
  `cor1216_pRank_normalizer_le_one` (a) / `cor1216_not_mem_primeFactors_derived_of_tau1` (b)
  を provisional axiom 宣言、root 配線、full build 3792 緑。
- **Lemma 13.1 step 1 着地** (sorry-free): `Msigma_commutator_M_le` (`⁅M_σ,M⁆≤M_σ`, 再利用可) +
  `exists_sigma_prime_dvd_derived_Mstar` (mmd L3534: `⁅M_σ∩M*,M∩M*⁆≠1` ⟹ `∃q∈σ(M)∩π(M*')`)。

### Lemma 13.1 残 step plan (mmd L3534-3546; scaffold `pSubgroup_centralizes_of_interaction` は
S13_PrimeAction に sorry'd で残置、全 step 着地で migrate)

- **step 2 (Frattini) ✅ COMPLETE (2026-06-12 session 1, commit `a93636c5`)**:
  `exists_sylow_frattini_decomp` (sorry-free) = `q∉β(M*) ∧ q∣|M*'| ⟹ ∃ Y, Y≠⊥ ∧ IsPGroup q Y ∧
  Y≤M*' ∧ Mstar = O_{β(M*)∪{q}}(M*') ⊔ (Mstar ⊓ N_G(Y))`。核 `M*_β Q ◁ D` =
  `S10.normal_sup_sylow_of_quotient_nilpotent` (D/M*_β nilpotent) → O_{β∪q}(D) に押込 (char in D⊴M*
  ⟹ K⊴M*)、Frattini = `Sylow.ofCard`+`Sylow.normalizer_sup_eq_top`+subtype transport (S10 Cor 10.9
  機構縮約)。~100 行・4 build iteration で着地。helper `Mbeta_le_derived` も land。
  🔑 **M*_β でなく K=O_{β∪q}(M*') を使うのが鍵** (K は M*' に characteristic ⟹ K⊴M* が無料)。
- **step 3 = (b) `p∉τ₂(M*)` ✅ COMPLETE (2026-06-12 session 2, axiom 初使用)**:
  `not_mem_tau2_of_interaction` (sorry-free; `#print axioms` = `[propext, Classical.choice,
  Quot.sound, cor1216_pRank_normalizer_le_one]` — forward axiom のみ, sorryAx 無し)。
  p∈τ₂(M*) 仮定→矛盾。実装の要:
  - q∉β(M*): `(S10.disjoint_of_not_conj hG hMstar h.mem_maximal hnc').1.2`
    (= `alpha Mstar ∩ sigma M = ∅`, hnc' = conjugacy 対称化を inline 2 行) + β⊆α。
  - **r_p(N_{M*}(Y))=2 は τ₂ witness 不要**: 直接 `tau2_pRank_eq_two hpτ2` (=pRank M*=2) を
    新 helper `pRank_le_of_factorization_card_eq` (N≤H ∧ v_p|H|=v_p|N| ⟹ pRank H≤pRank N;
    N の Sylow p を `Sylow.ofCard` で H の Sylow p と同定 → `pRank_sylow_eq`) で N へ transfer。
    v_p|M*|=v_p|N| は積公式を **↥M* 内**で (`card_HK_mul_card_inf_eq_card_mul_card` +
    `Subgroup.normal_mul` (KM⊴⟹↑KM·↑NM=↑(KM⊔NM)) + `SetLike.coe_sort_coe`+`Subgroup.card_top`,
    subgroupOf cards は `subgroupOfEquivOfLe`) → `|M*|·|K⊓N|=|K|·|N|`, 両辺 factorization_p:
    v_p|K|=v_p|K⊓N|=0 (`p∤|K|`) ⟹ v_p|M*|=v_p|N|。p∤|K| = K {β∪q}-group ∧ p∉β(M*)
    (τ₂⟹p∉σ⊇β) ∧ p≠q (`h.not_mem_sigma_of_mem_primeFactors` で p∉σ(M), q∈σ(M))。
  - **r_p(N_{M*}(Y))≤1**: `cor1216_pRank_normalizer_le_one hG h hYne hYpi hpE hpβG hHY hnc`。
    hpβG=`(isMaximalElementaryAbelian_of_mem_tau2 ... hpτ2 hAM hA).2` (witness A は
    `exists_mem_elemAbelianOfRank_two_le_of_tau2`, S12_Lemma1211 を新規 import)。
    hYpi: Y は q-group + q∈σ(M)。hHY: `mem_maximalSubgroupsContaining.mpr ⟨IsCoatom, Y≤M*⟩`。
    `rw [← hNdef] at hle1` で N に fold して omega。
  - 🔑 **import 知見**: S12_E の closure は S12_ECore のみ (S12_E は branch-A leaf)。proven §12
    結果は別 leaf: `exists_mem_elemAbelianOfRank_two_le_of_tau2`=S12_Lemma1211 (branch B, 要 import),
    `not_conj_symm`=S12_ExceptionalBridge (branch A, inline で回避),
    `not_mem_sigma_of_mem_primeFactors`=S12_ECore の **`SubgroupESetup` namespace 内**
    (dot 記法 `h.not_mem_sigma_of_mem_primeFactors hG hpE`)。§13 後続も同様に leaf を選んで import。
  - 🔑 **新 helper 2 個** (axiom-clean, 再利用可, S13_Lemma131 冒頭): `pRank_eq_of_mulEquiv`
    (≃* 不変), `pRank_le_of_factorization_card_eq` (上記)。step 4/5 でも使える見込み。
  - **AxiomsCheck island assert は step 6 (assembly) で**: 現状 AxiomsCheck は S13_Lemma131 を
    import せず (per-name `#assert_only_allowed_axioms` のみ) ⟹ full build 緑・gate pass。
- **step 4 = (c) `p∈τ₁(M)⟹p∈β(G)` ✅ COMPLETE (2026-06-12 session 2)**:
  `mem_idealPrime_of_tau1_of_interaction` (sorry-free; `#print axioms` = forward axiom
  `cor1216_not_mem_primeFactors_derived_of_tau1` のみ + 標準, sorryAx 無し)。
  🔑 **当初の心配 (Burnside Sylow⊆M*') は不要だった** — injection 論法は `p∈π(M*')` (full
  Sylow でなく p∣|M*'|) だけでよい。再利用 helper 4 個 (全 axiom-clean):
  - `derivedInG_le_sup_of_normal` (M*=K⊔N, K⊴M* ⟹ M*'≤K⊔N'; ↥M* 内 quotient `φ=mk' KM` で
    `map φ commutator(↥M*)=map φ ⁅NM,NM⁆` → `comap_map_eq` → 下降 `map_subtype_commutator`)。
  - `card_normal_sup_mul_card_inf` ((b) の積公式を一般 sup へ; |K⊔L|·|K⊓L|=|K|·|L|)。
  - `mem_primeFactors_derived_of_not_tau1_tau2` (`p∈π(M*)∖τ₁∖τ₂ ⟹ p∈π(M*')`: σ は
    Sylow⊆M_σ⊆M*' [`sigma_subgroup_le_Msigma_of_isHall`+`Msigma_le_derived`]、p∉σ は rank≤2
    [`mem_alpha_iff`]∧≠2[τ₂]⟹=1∧p∉τ₁⟹p∈π(M*'); `one_le_pRank_of_mem_primeFactors` で rank≥1)。
  - `pRank_eq_of_mulEquiv` / `pRank_le_of_factorization_card_eq` (step 3 由来)。
  証明: by_contra ¬idealPrime → p∉β(M*) (β⟹idealPrime) → setup 再利用 (p∤|K|) →
  hpMstarDeriv (p∈π M*') → hpNderiv (p∈π N': M*'≤K⊔N', |M*'|∣|K|·|N'|, p∤|K| で Euclid) →
  axiom `cor1216(b)` の `p∉π(N')` と矛盾。⚠ setup ~30 行が (b) と重複 (将来 factor 候補)。
- **step 5 = (a) centralization ✅ COMPLETE (2026-06-12 session 2)**:
  `pSubgroup_centralizes_Msigma_inf` (**完全 axiom-clean** — forward axiom 不使用,
  `#print axioms` = 標準3つのみ)。論法 (mmd L3542): `K_a=O_{α(M*)∪{p}}(M*')⊴M*` (uniform char),
  `P⊆K_a` → `⁅M_σ∩M*,P⁆⊆M_σ⊓K_a=⊥`。新 helper:
  - `derivedQuotientMalpha_isNilpotent` (keystone): M*'/M*_α = (M*'/M*_β)⧸(M*_α/M*_β) =
    nilpotent M*'/M*_β の商 ⟹ nilpotent (`quotientQuotientEquivQuotient` + `nilpotent_of_surjective`;
    `map_surjective_of_surjective` は friction で回避)。Malpha' Normal は instance 引数。
  - `exists_sylow_le_derivedInG_of_not_tau1_tau2`: ∃ Sylow p of M* ⊆ M*' (σ=M_σ経由,
    **τ₃=de-private `sylow_le_derived_of_mem_tau3` 経由** E*'⊆M*' + |E*|_p=|M*|_p)。
  - `sylow_le_opiCoreInG_alpha_p`: S⊆K_a (p∈α は S⊆M*_α⊆K_a [`isPiGroup_le_of_normal_isHallSubgroup`],
    p∉α は M*_α⊔S⊴M*' [keystone+`normal_sup_sylow`] ⊆K_a)。
  - `commutator_le_of_subgroupOf_normal`: ⁅K,H⁆≤K (Msigma_commutator_M_le 一般化)。
  - **P⊆K_a は full Sylow⊆M*' でなく cardinality で**: |K_a|_p=|M*|_p (S⊆K_a) ⟹ p∤[M*:K_a] ⟹
    P の ↥M*/K_a 像が coprime位数 p-group ⟹ 自明 ⟹ P⊆K_a (Hall 性証明を回避)。
  - M_σ⊓K_a=⊥: `inf_eq_bot_of_coprime` (`coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl`;
    α(M*)∩σ(M)=∅ via `disjoint_of_not_conj` swapped, p∉σ(M) via `not_mem_sigma_of_mem_primeFactors`)。
- **step 6 = assembly ✅ COMPLETE (2026-06-12 session 2)**:
  `pSubgroup_centralizes_of_interaction` (S13_PrimeAction scaffold) を (a)(b)(c) で組立、
  sorry 除去 (S13_PrimeAction 実 sorry 11→10)。S13_PrimeAction が S13_Lemma131 を import。
  `#print axioms` = [propext, cor1216_pRank_normalizer_le_one,
  cor1216_not_mem_primeFactors_derived_of_tau1]。**AxiomsCheck island 4件 PASS** (full build
  3645 jobs): (a)=allowed, (b)(c)/full=island。S13_PrimeAction を AxiomsCheck import 追加済。
  ⟹ **🎉 BG Lemma 13.1 完全証明 (forward axiom conditional)**。次 = **Cor 13.2** (mmd L3548;
  「follows directly from Lemma 13.1」+ Lemma 12.2(a))。

### 2026-06-13 Lane G session 3: Cor 13.2 ✅ COMPLETE (新 leaf `S13_Corollary132.lean`)

**`tau13_pSubgroup_centralizes` 完全証明** (sorry-free, axiom = 2 forward `cor1216_*` のみ;
新規 axiom 0)。S13_PrimeAction scaffold stub を leaf へ移動 (実 sorry 10→9)、S13_PrimeAction が
leaf を import し再 export。root + AxiomsCheck (island PASS, full build 3793/3646 jobs) に配線。

証明構造 (3 結論を共通 setup 後 `by_cases ⁅M_σ∩M*, M∩M*⁆ = ⊥` で分岐):
- **非共役** `hnc` = `not_conj_of_mem_tau1_union_tau3_of_normalizer_le` (BG Lem 12.2(b), 既存) を
  X:=P で適用 — **無料** (conj-invariance/disjointness 自作不要)。
- **=⊥ 枝**: `commutator_eq_bot_iff_le_centralizer` で M∩M* がそのまま中心化 (向き =
  `⁅H,K⁆=⊥ ↔ H≤C(K)`、hcomm を `commutator_comm` で swap)。(a)(b) trivial、(c) vacuous。
- **≠⊥ 枝**: `not_mem_tau2_of_interaction` (13.1b) で `p∉τ₂(M*)`、`prime_mem_sigma_or_tau2`
  (12.2a) と合わせ `p∈σ(M*)`、`tau1_subset_sigma_compl` で `p∉τ₁(M*)`。
  - (a) = `pSubgroup_centralizes_Msigma_inf` (13.1a) 直接。
  - (b) = 新 reusable helper **`le_centralizer_of_forall_prime_isPGroup`**(有限群は素冪部分群で
    生成 — orderOf の素冪分解 z=y^m / w=y^{r^a} + Bézout `gcd_eq_gcd_ab` で y=w^A·z^B、
    `Nat.strong_induction_on orderOf`)を K:=Q に適用、各素冪部分群 R に (a) を per-prime 適用
    (`r∈π(Q)⟹r∉τ₁(M*)` via `IsPiSubgroup`、`r∈π(E)/π(M*)` via `mem_primeFactors_of_isPGroup_le`)。
  - (c) `p∈β(M*)` = `mem_idealPrime_of_tau1_of_interaction` (13.1c, `idealPrime`) +
    `p∈α(M*)`: `pRank M* p = pRank G p` via 新 helper **`pRank_eq_of_mem_sigma`**
    (`isSylow_sylowMap_of_mem_sigma` + `pRank_sylow_eq` + `equivMapOfInjective`)、`idealPrime` の
    `r_p(G)≥3` を移送。
- 新 helper 4 (再利用可): `le_centralizer_of_forall_prime_isPGroup` /
  `mem_primeFactors_of_isPGroup_le` / `mem_primeFactors_E_of_mem_M_of_not_sigma`
  (|M|=|M_σ||E| + `Msigma_isPiGroup`) / `pRank_eq_of_mem_sigma`。
- **次 = Cor 13.3** (`cyclicSylow_actsPrime`; mmd L3556): Cor 13.2(a)(b) + `ActsPrimeOn` 定義
  (S13_PrimeAction 内)。leaf は ActsPrimeOn を要するので S13_PrimeAction を import
  ⟹ S13_PrimeAction は 13.3 leaf を import 不可 (cycle)、13.3 stub は leaf へ移し root 直 import。

  **⚠ 13.3 は terse corollary に見えて real proof（mmd「this proves (a)」が coprime-action 論法を省略）**:
  - `ActsPrimeOn` 定義 = element 形 `∀g∈P#, C_{M_σ}(g)=C_{M_σ}(P)`。cyclic P では
    `ℰ¹(P)={Ω₁(P)}` ゆえ **`C_{M_σ}(Ω₁P) ⊆ C_{M_σ}(P)` に帰着**(両形同値、mmd L3490)。
  - これは `D:=C_{M_σ}(Ω₁P)` に P を coprime 作用 (p∤|M_σ|) ⟹ `D=C_D(P)·[D,P]`,
    `C_D(P)=C_{M_σ}(P)`。**crux = `[D,P]=1`**(P-FPF on [D,P])。
  - Cor 13.2(a) は「N_E(P) の p-部分群が C_{M_σ}(P)=M_σ∩M* を中心化」を与える
    (C_G(P)⊆N_G(P)⊆M* ゆえ C_{M_σ}(P)⊆M_σ∩M*) が、これだけでは `[D,P]=1`(D は Ω₁P の
    centralizer で C_{M_σ}(P) より大) に直結しない。P が **E の Sylow** であること + [D,P] の
    Sylow への Frattini/局所論法が要る。**未解決の path; 次セッションの第一課題**。
  - coprime 分解 infra: `OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top`
    (抽象 action 形、subgroup 設定への適応要)。
  - (b) E₃ は mmd 明快: E₃⊆E'⊆M*', π(E₃)⊆π(M*')⊆(τ₁M*)' ⟹ Cor 13.2(b) 直接
    ((a) より易、先に landing 可)。

### 2026-06-13 Lane G: main 同期 + **de-axiom 完了** (issue 8000 closed)

main 取り込み (merge, 102 commits)。Lane F が issue 0065 で **S12_E に Cor 12.16(a)(b) faithful
sorry'd statement** を露出済 (`sigma_subgroup_pRank_normalizer_le_one` /
`sigma_subgroup_not_mem_primeFactors_derived_of_tau1`, commit `e876f29b`, 私の forward axiom と
**byte-identical drop-in 署名**) と判明 → handshake step 2 実行:
- S13_Lemma131 の forward axiom 2 本 (`cor1216_*`) を**削除**、cite 先を S12_E の 2 定理へ差し替え
  (use site 2 箇所、引数 list 不変ゆえ機械的)。
- AxiomsCheck: cor1216 island 3 本 + Cor 13.2 island を削除。13.1(a)
  `pSubgroup_centralizes_Msigma_inf` は S12_E Cor 12.16 非依存 (`[propext, Classical.choice,
  Quot.sound]` clean) ゆえ `#assert_only_allowed_axioms` 維持。
- footprint: Lemma 13.1(b)(c)/full・Cor 13.2 = `[propext, sorryAx, Classical.choice, Quot.sound]`
  (sorryAx = S12_E Cor 12.16 由来 = repo 標準 scaffold-sorry)。**新規 axiom 0**。
- full build 3796 + AxiomsCheck 3782 green。**HOLD 解消** (G の forward axiom 消滅 ⟹ merge ブロッカー無し)。
- 残: F が S12_E の 2 sorry を §12 cascade で埋めれば §13 全体が自動 unconditional 化 (issue 0065)。

### 2026-06-13 Lane G: Thm 13.4 着手 (proof plan; loop)

**13.4 = §13 の "main step" (unblocked: Cor 13.2 ✅ + Lem 12.18 + Thm 12.13)。13.3 の
prime-action criterion とは独立**(13.5 が両者を要するが、13.4←13.3 ではない)。

statement (scaffold `S13_PrimeAction.centralizer_le_centralizer_of_tau1`):
`p∈τ₁(M), P∈ℰ_p¹(E), r∈π(E), R∈ℰ_r¹(C_E(P)) ⟹ C_{M_σ}(P) ⊆ C_{M_σ}(R)`
(`M_σ⊓C(P) ≤ M_σ⊓C(R)`)。

mmd 証明 (L3580-3597) の構造:
- **outer**: C_{M_σ}(P)⊆C_{M_σ}(R) ⟺ R が C_{M_σ}(P) を中心化。C_{M_σ}(P) は σ(M)-群ゆえ
  PR-不変 Sylow q (q∈σ(M)) で生成 (PR=P×R abelian, R≤C_E(P))。各 σ-Sylow S を R が中心化
  すれば従う。**要 coprime-action invariant-Sylow generation** (infra: `AInvariantPiSubgroups`
  の `hInvariantStar`)。
- **per-q (核)**: S = PR-不変 Sylow q of C_{M_σ}(P)。`[S,R]=1` を示す。仮定 Q:=[S,R]≠1:
  1. M*∈ℳ(N_G(P))。`1⊂Q=[S,R]⊆[M_σ∩M*,R]` ⟹ **Cor 13.2** で `p∈β(M*)`, `r∈τ₁(M*)`。
  2. `1⊂P⊆C_{M_α(M*)}(RQ)`、`S=C_S(R)×Q` (S abelian by **Thm 12.13**)。
  3. **Lem 12.18(a)** (`tau1_Malpha_interaction`, S12_Lemma1218:1029) を (r,R,M*)↦(p,P,M) で適用 →
     `C_{M_α}(P)⊆C_{M_α}(R)`; r∈τ₁(M) で逆向き ⟹ `C_{M_α}(P)=C_{M_α}(R)`。
     (注: ここ M_α は M_α(M*)? mmd 表記曖昧、要精読 L3585-3592。)
  4. C_{M_α}(P)=C_{M_α}(R) は S で正規化 (S⊆C_M(P)) ⟹ Q=[S,R] で中心化 ⟹ `C_{M_α}(R)=C_{M_α}(RQ)`。
  5. ℳ(N_G(Q))≠{M} ⟹ **Lem 12.18(a)** が `C_{M_α}(R)≠C_{M_α}(RQ)` (= C_{M_α}⊓C(R)≠⊥ かつ
     C_{M_α}⊓C(R⊔Q)=⊥) ⟹ 矛盾。

deps 確認済: Lem 12.18 = `tau1_Malpha_interaction` (a 結論 = `M_α⊓C(P)≠⊥ ∧ M_α⊓C(P⊔Q)=⊥`,
hyp: q≠p, p∈τ₁(M), P∈ℰ_p¹, P-inv q-grp Q, C_Q(P)=⊥, ℳ(N_G(Q))≠{M}, M_α≠⊥, q∉α(M))。
Thm 12.13 = M_σ の Sylow abelian (要 exact 名特定; S12_Lemma128 `sylow_isMulCommutative_*` 周辺)。

### 2026-06-13 Lane G (loop): Thm 13.4 — **outer reduction COMPLETE**, per-q core 着手

**✅ 進捗 (4 commit)**: reusable infra 3 + outer reduction:
- `eq_of_le_of_forall_full_prime_pow` (4c3e2bdb): order 論法 (各素数の full Sylow⊆C ⟹ C=H)。
- `exists_aInvariant_sylow_subgroup` (b2ddd441): coprime A-不変 Sylow 存在 (subgroup 形, φ-action
  boilerplate を `Isaacs.Ch04.exists_aInvariant_sylow` で encapsulate)。
- `msigma_centralizer_le_of_invariant_sylow_centralized` (6e6d7f92): **outer reduction** —
  R が C_{M_σ}(P) の全 (P⊔R)-不変 Sylow を中心化 ⟹ C_{M_σ}(P)⊆C_{M_σ}(R)。⟹ **13.4 を per-q core
  に還元**。coprimality は P⊔R≤E (σ' 群; 当初の commuting-subgroup 補題は不要と判明)。
  hAN は `le_normalizer_inf`+`normalizer_le_normalizer_centralizer` (S12_Lemma1218)。

**残: per-q core** (`hcore` の中身): q∈σ(M), S=(P⊔R)-不変 Sylow q of C_{M_σ}(P) で **[S,R]=1**。
mmd L3576-3597 精読で確定した構造 (Q:=[S,R]≠1 と仮定して矛盾):
1. M*∈ℳ(N_G(P)) (M*≠M; p∈τ₁(M) ゆえ非共役)。`1⊂Q=[S,R]⊆[M_σ∩M*,R]`。
   - R≤E∩M* (R≤E, R≤C(P)⊆N_G(P)⊆M*)。
2. **Cor 13.2(b)** で `r∈τ₁(M*)`: もし r∉τ₁(M*) なら R は τ₁(M*)'-部分群 ⟹ 13.2(b) で R が
   M_σ∩M* を中心化 ⟹ [M_σ∩M*,R]=1 ⟹ Q=1 矛盾。∴ r∈τ₁(M*)。
3. **Cor 13.2(c)** で `p∈β(M*)`: [M_σ∩M*,M∩M*]⊇[M_σ∩M*,R]⊇Q≠1 (R⊆M∩M*) ⟹ 13.2(c) +
   p∈τ₁(M) ⟹ p∈β(M*)。
4. `1⊂P⊆ M∩M*_σ` (P が C_{M*_σ}(RQ) に; ⚠ mmd は `M_{\tilde p}` = Nougat 誤抽出、**M*_σ と推定**、
   要 PDF 確認)。S=C_S(R)×Q (S abelian by **Thm 12.13** + R coprime 作用)。
5. **Lem 12.18(a)** を (r,R,M*)↦(p,P,M) role-swap で適用 → `ℳ(N_G(Q))={M*}`。
6. **Prop 12.15** (`sigma_subgroup_maximal_interaction`, S12_E:484, sorry'd scaffold・cite 可) を
   X=Q, M* で: (e) は `1⊂P⊆M∩M*_σ` で排除 (P⊆M*_σ⊓(M∩M*)=⊥ 矛盾) ⟹ **Lem 10.12(a) で q∈σ(M*)**;
   (d) で `M_α≠1` かつ `r∈π(E)∩τ₁(M*)⊆τ₁(M)` (τ₁(M*)⊆τ₁(M)∪α(M), r∈π(E)⟹r∉α(M))。
7. `[S,R]≠1 ⟹ q∉α(M)`、よって Lem 12.18(a) を 2 回 (p,P と r,R) →
   `C_{M_α}(P)⊆C_{M_α}(R)` と `C_{M_α}(R)⊆C_{M_α}(P)` ⟹ `C_{M_α}(P)=C_{M_α}(R)`。
8. これは S で正規化 (S⊆C_M(P)) ⟹ Q=[S,R] で中心化 → `C_{M_α}(R)=C_{M_α}(RQ)`。
9. **矛盾**: ℳ(N_G(Q))≠{M} ⟹ Lem 12.18(a) が `C_{M_α}(R)≠C_{M_α}(RQ)` (C_{M_α}⊓C(R)≠⊥ かつ
   C_{M_α}⊓C(R⊔Q)=⊥)。∎

cite 先 (一部 sorry'd scaffold ゆえ §13 は sorryAx 経由・repo 標準): Cor 13.2 ✅,
Prop 12.15 `sigma_subgroup_maximal_interaction` (sorry'd), Lem 12.18 `tau1_Malpha_interaction` ✅,
Lem 10.12(a) `S10.disjoint_of_not_conj` 系, Thm 12.13 (要特定)。
**次 iteration: per-q core skeleton を WIP leaf に (step 1-3 = Cor 13.2 は concrete に proof,
step 4-9 = Prop 12.15/Lem 12.18 部は sorry で構造化) → 順次充足。**

### 2026-06-13 Lane G (loop): per-q core skeleton 着地 (WIP) + **PDF 精読で proof 確定**

**WIP leaf S13_Theorem134**: per_q_centralizes (setup + step 2-3 proven, step 4-9 sorry) +
centralizer_le_centralizer_of_tau1 (outer reduction + per_q で proof)。build 緑 (sorry 1)。
- step 2 (r∈τ₁M*) = Cor 13.2(b) 対偶 (R が τ₁M*'-部分群なら M_σ∩M* 中心化 → [S,R]=1 矛盾)。✅ proven。
- step 3 (p∈β(M*)) = Cor 13.2(c) ([M_σ∩M*,M∩M*]⊇[S,R]≠1)。✅ proven。
- M* = `eq_top_or_exists_le_coatom` (N_G(P)≠⊤ via P 非正規)。setup ✅。

**📖 PDF 精読 (book p.94-99 = PDF 107-112; offset +13) — Prop 12.15 / Lem 12.18 / Thm 13.4 exact**:
- **M_p̃ = M*_σ** 確定: `1⊂P⊆C_{M*_σ}(RQ)`。
- **Prop 12.15** (book p.94, `sigma_subgroup_maximal_interaction` S12_E:484, sorry'd): X=Q, M* で
  (e) 排除 (P⊆M∩M*_σ) → (Lem 10.12(a)) q∈σ(M*) → (d) M_α≠1, τ₁(M*)⊆τ₁(M)∪α(M)。
- **Lem 12.18** (book p.96, `tau1_Malpha_interaction`): (a) M_α≠1∧q∉α(M) ⟹ C_{M_α}(P)≠1∧C_{M_α}(PQ)=1。
- **⚠ 2 つの BG proof 省略 (OCR でなく原文の "we can conclude"/"to get")**:
  1. **`ℳ(N_G(Q))={M*}`**: 原文「apply Lem 12.18(a) ... to get ℳ(N_G(Q))={M*}」だが **Lem 12.18(a)
     の結論は C_{M_α} であって ℳ ではない** → 原文の shorthand。実質要るのは **N_G(Q)⊆M***
     (⟹ M*∈ℳ(N_G(Q))-{M} で Prop 12.15 適用可、かつ ℳ(N_G(Q))≠{M} で step 9 の Lem 12.18 可)。
     導出は §12 の σ-uniqueness 系を要する見込み (Q=[S,R]⊆M*_σ, q∈σ(M*))。**要 §12 study**。
  2. **`C_{M_α}(P)⊆C_{M_α}(R)` と逆**: 原文「Since [S,R]≠1 yields q∉α(M), we can conclude」。
     q∉α(M) で Lem 12.18(a) (C_{M_α}(P)≠1, C_{M_α}(PQ)=1; rank≤1 cyclic) は出るが、**包含 itself は
     さらに rank-1/cyclic + FPF 論法を要する** (原文 elide)。**要 derivation**。
- step 8: C_{M_α}(P)=C_{M_α}(R) は S で正規化 (S⊆C_M(P)) + Q=[S,R] で中心化 (three-subgroups:
  [A,R]=1 [A=C_{M_α}(R)⊆C(R)], [A,S]⊆A [S 正規化], ⟹ [Q,A]=[[S,R],A]=1) → C_{M_α}(R)=C_{M_α}(RQ)。
- step 9: Lem 12.18(a) (r,R 版) で C_{M_α}(R)≠1, C_{M_α}(RQ)=M_α⊓C(R⊔Q)=1 ⟹ ≠ → 矛盾。
**評価**: per-q core は ~100-150 行・2 つの BG 省略 (ℳ(N_G(Q))={M*} の N_G(Q)⊆M* / C_{M_α} 包含) の
derivation を要する深い部分。outer reduction まで完成・committed ゆえ、ここは focused task。
**次: N_G(Q)⊆M* の導出 (§12 σ-uniqueness) を最初に攻める。**

### 2026-06-13 Lane G (loop): ℳ(N_G(Q))={M*} 省略を解明 + per-q core 深度評価

**ℳ(N_G(Q))={M*} の正体 = Lem 12.18(a) の入れ子 contradiction** (原文「to get」の真意):
ℳ(N_G(Q))≠{M*} と仮定 → Lem 12.18(a) を (r,R,M*) role-swap で適用 → C_{M*_α}(RQ)=1。
だが p∈β(M*)⊆α(M*) ゆえ P⊆M*_α、かつ `1⊂P⊆C_{M*_σ}(RQ)` から P⊆C_{M*_α}(RQ)≠1 → P=1 矛盾。
∴ ℳ(N_G(Q))={M*}。**要 sub-facts: M*_α≠1, q∉α(M*), P⊆M*_α, C_Q(R)=1**(各々 §12 依存)。

**per-q core 深度評価 (重要)**: steps 4-9 は **~150-200 行の入れ子 contradiction**で、各 sub-step が
それ自体 §12 の深い導出:
- **S abelian** = Thm 12.13 (`S12_E:48`「非可換 p-群 ⟹ 𝒰」, sorry'd) の 𝒰-machinery 経由 (S∈𝒰 排除)。
- **C_Q(R)=1** = abelian S への R coprime 作用の FPF (`[S,R]⊓C_S(R)=⊥`; repo に既製無し→要構築)。
- **ℳ(N_G(Q))={M*}** = 上記 Lem 12.18 入れ子 contradiction (~40-60 行)。
- **Prop 12.15** 適用 (X=Q, M*) → q∈σ(M*) → (d)。
- **C_{M_α}(P)⊆C_{M_α}(R)** 包含 = Lem 12.18(a) (C_{M_α}(P)≠1, C_{M_α}(PQ)=1) + rank-1/cyclic 論法。
- step 8 three-subgroups, step 9 Lem 12.18 (r,R 版) 矛盾。
⟹ Lem 12.18 を **3 回** (M*-role で ℳ 導出, M-role で包含 ×2)、Prop 12.15・Thm 12.13・three-subgroups。
**outer reduction まで committed; per-q core は focused task (多数の §12 sorry'd scaffold cite + 新 FPF 補題)。**

surface map (Explore 2026-06-12): `commutator_mono`/`commutator_le_left` (mathlib),
`S10.Msigma_isPiGroup`/`Msigma_le_derived`, `Sylow.normalizer_sup_eq_top'`, `pRank_mono_of_le`,
`isHall_Mbeta` (full bundle: Hall + nilpotent quotient + normal p-complement),
`tau2 M={p∉σ ∧ pRank=2}`/`tau2_pRank_eq_two`, `S10.disjoint_of_not_conj` (10.12)。

### 2026-06-13 Lane G (loop): Thm 13.4 per-q **step 5 COMPLETE** (`ℳ(N_G(Q))={M*}`)

**✅ step 5 着地** (`S13_Theorem134.per_q_centralizes`, build 緑 3082 / axiom = sorryAx+標準のみ,
残 sorry 1 = steps 6-9)。step 4b (FPF `hCQR`) の上に structural prep + 入れ子 contradiction:
- `hQS:⁅S,R⁆≤S` (`Ch04.commutator_le_of_le_normalizer hRS_norm`), `hQq` (`hSpg.to_le hQS`),
  `hRNQ:R≤N(Q)` (`Ch04.le_normalizer_of_commutator_le (commutator_mono hQS le_rfl)`),
  `hPcRQ:P≤C(R⊔Q)` (R⊔Q≤C(P) を sup_le + commutator_comm 対称化)。
- **q∉α(M*)** = `S10.disjoint_of_not_conj hG hMstarMax h.mem_maximal hnc'` の `.1.2` (alpha M*∩sigma M=∅)
  + q∈σ(M)。idiom は S13_Lemma131:333-339 と同一 (hnc' は conj 対称性 inline)。
- **P≤M*_α** = `S10.alpha_subgroup_le_Malpha_of_isHall (Malpha_isHall …) hPMstar hPα`
  (p∈β(M*)⊆α(M*)); ⟹ `M*_α≠⊥` (P≠⊥ ⊆ M*_α)。
- **step 5 本体**: `ℳ(N_G(Q))≠{M*}` 仮定 → `tau1_Malpha_interaction` を (r,R,M*)↦(p,P,M) で適用
  (hqp=hrq.symm) → `.1 hMαstar_ne hqαstar` の第2成分 `M*_α⊓C(R⊔Q)=⊥`; だが P≤M*_α⊓C(R⊔Q), P≠⊥ → 矛盾。

**🔑 重要な設計発見 (次 iteration の step 7 を unblock)**: BG「[S,R]≠1 yields q∉α(M)」は shorthand。
**q∉α(M) も q∉α(M*) と同じ disjointness (10.12(a))** で出る — ただし向きが逆:
- q∉α(M*) = `alpha M* ∩ sigma M = ∅` (q∈σ(M) は既知)。【step 5, DONE】
- q∉α(M) = `alpha M ∩ sigma M* = ∅` (**q∈σ(M*) が要る** = step 6 が Prop 12.15 で供給)。【step 7】
⟹ step 7 の q∉α(M) は新たな hard work 不要、step 6 の後に `disjoint_of_not_conj hG h.mem_maximal hMstarMax hnc` の `.1.2` で即出る。

**残 steps 6-9 (frontier)**:
- **step 6** = Prop 12.15 (`sigma_subgroup_maximal_interaction`, X=Q): Sylow S'⊇Q of M⊓M* 構成 +
  case (e) 排除 (`1⊂P⊆M⊓M*_σ`, P≤M*_σ は p∈σ(M*) [β⊆σ] 経由) → q∈σ(M*) + (d) τ₁(M*)⊆τ₁(M)∪α(M)。
- **step 7** = q∉α(M) [上記 disjointness] → Lem 12.18(a) ×2 で C_{M_α}(P)=C_{M_α}(R)。
  ⚠ **2nd BG gap (genuine)**: Lem 12.18(a) は C_{M_α}(P)≠1∧C_{M_α}(PQ)=1 を出すが、**包含 C_{M_α}(P)⊆C_{M_α}(R)
  itself は rank-1/cyclic 論法を要する** (BG elide; 要 derivation)。
- **step 8** three-subgroups (`commutator_commutator_eq_bot_of_le_of_commutator_bot` 済) → C_{M_α}(R)=C_{M_α}(RQ)。
- **step 9** Lem 12.18(a) (on M) → C_{M_α}(R)≠C_{M_α}(RQ) 矛盾 (要 `ℳ(N_G(Q))≠{M}` = hMNQstar+M*≠M)。

### 2026-06-13 Lane G (loop): Thm 13.4 per-q **steps 6 + 8-9 COMPLETE → 単一 sorry に還元**

**✅ 大躍進**: per_q_centralizes の 9-step 矛盾が **step 7 の単一等式に還元** (build 緑, 残 sorry 1)。
- **step 6** (前 commit `bab4d04b`): Prop 12.15 (X=Q) → q∈σ(M*), τ₁(M*)⊆τ₁(M)∪α(M), M_α≠⊥, q∉α(M)。
  新 helper `exists_maximal_pSubgroup_le_of_le` (Q≤H を H の極大 q-部分群へ; axiom-clean)。
- **steps 8-9** (本 commit): 矛盾を実装・閉じた。
  - r∈τ₁(M) = hτ1sub + r∉α(M) (h.not_mem_sigma_of_mem_primeFactors)。
  - Lem 12.18(a) on (r,R,q,Q) [C_Q(R)=1=hCQR ✓] → C_{M_α}(R)≠1 (hCR_ne), C_{M_α}(RQ)=1 (hCRQ_bot)。
  - **A:=M_α⊓C(P)**: S-不変 (S⊆C(P)⊆N(C(P)) [le_normalizer] + M_α⊴M [le_normalizer_opiCoreInG] → le_normalizer_inf),
    A⊆C(R) (=hCeq), 三部分群 (`commutator_commutator_eq_bot_of_le_of_commutator_bot`) → A⊆C(Q)。
  - A⊆M_α⊓C(R⊔Q)=⊥ (R⊔Q≤C(A) を sup_le+対称化, centralizer_sup_eq 不要) だが A=M_α⊓C(R)≠⊥ → 矛盾。

**🎯 唯一の残 sorry = step 7**: `hCeq : M_α⊓C(P) = M_α⊓C(R)` (S13_Theorem134.lean per_q 内)。
これは BG が "we can conclude" で省略する rank-≤1/cyclic 論法 (2nd BG gap)。**次 iteration の単一標的**。
- **入手済ツール**: `rank_centralizer_Malpha_le_one_of_not_uniqueMaximal` (S12_E:510, P が α' かつ ℳ(N_G(P))≠{M} で
  rank(C(P)⊓M_α)≤1)、`eq_of_card_eq_of_le_of_isCyclic` (S12_Lemma1218:77, 巡回内 同位数 prime 部分群 = 一意)。
- **P 側 rank≤1 適用可**: p∈τ₁⟹p∉α (P が α'); M*≠M∈ℳ(N_G(P)) ⟹ ℳ(N_G(P))≠{M}。⟹ C_{M_α}(P) 巡回。
- **R 側**: Lem 12.18(a) on (r,R) で C_{M_α}(R)≠1, C_{M_α}(RQ)=1 (Q が C_{M_α}(R) に FPF 作用)。
- **要 derivation**: 両 cyclic + FPF/coprime で等式。BG 原文 Lem 12.18 証明 (Thm 1.13/3.7/12.5-12.7) が範型。
  ⚠ 包含の正確な機序は未確定 — 次 iteration で BG Lem 12.18 証明を精読し移植 or rank+card 経路を構築。

### 2026-06-13 Lane G (loop): step 7 root-cause 精査 — **genuine hard sub-lemma と確定**

**結論**: step 7 `C_{M_α}(P)=C_{M_α}(R)` は BG が "we can conclude" で省く実質的サブ補題で、
**既存 lemma の系ではない**。loop-quick-win でなく集中的な BG-12.18 流の証明を要する (要判断)。

**確定した事実 (この iteration)**:
- 両辺 cyclic (rank≤1) は出る: P 側 (p∈τ₁⟹α', `maximalSubgroupsContaining_normalizer_ne_singleton_of_mem_tau1`
  S12_E で ℳ(N_G(P))≠{M}) と R 側 (r∈τ₁(M)⟹同様) の両方に `rank_centralizer_Malpha_le_one_of_not_uniqueMaximal` 適用可。
- steps 8-9 矛盾は等式を仮定すれば airtight (実装済・compile)。**S が C(R) を正規化しない** (S∤N(R), [S,R]=Q≠1 と
  q≠r から S⊄N(R)) ため S-不変な C_{M_α}(P) 形が必須 ⟹ 等式は迂回不能。

**棄却した経路 (この iteration の精査)**:
- **Lem 12.18(a) 直接**: 包含を出さない (C_{M_α}(P)≠1 / C_{M_α}(PQ)=1 のみ)。かつ (p,P) 適用は
  C_Q(P)=Q≠1 (Q⊆S⊆C(P)) で**仮定 C_Q(P)=1 が破れ不可**。
- **Cor 13.2(b) / 13.3(b) 流**: 「τ₁(M*)'-部分群が C_{M_α}(P) を中心化」型だが、P も R も **τ₁** (τ₁' でない) ゆえ不適合。
- **three-subgroups [Z_P,R,S] / [Z_R,P,Q]**: いずれも「S が Z_P=C_{M_α}(P) を中心化 (⁅S,Z_P⁆=1)」or
  「Q が Z_R を正規化」等の未証明前提に bottom-out。C_{M_σ}(P) の nilpotency があれば S が q'-part Z_P を中心化するが、
  C_{M_σ}(P) nilpotent は未確認。
- **elemAb_centralizes_Malpha_meet (Lem 12.3)**: σ-part・rank-2 A 用で τ₁ 中心化包含には非適合。

**推奨アプローチ (次の集中セッション)**: BG Lemma 12.18(a) の repo 証明
(`tau1_Malpha_centralizer_PQ_eq_bot` + `inf_centralizer_ne_bot_of_not_le_centralizer`, S12_Lemma1218:304-560,
Thompson critical `exists_charSubgroup_exponent_not_centralized` + Thm 3.7
`isNilpotent_of_normalizing_primeOrder_fixedPointFree` 使用) を範型に、cyclic 分解 Z_P=C_{Z_P}(R)×[Z_P,R] の
[Z_P,R]=1 を FPF/Thm 3.7 で示す独立 lemma `centralizer_Malpha_eq_of_commuting_tau1` を切り出して証明。
~hundreds 行規模の見込み。**step 7 以外の per_q は完成済 (4 commits: steps 4b,5,6,8-9)。**

### 2026-06-13 Lane G (loop): step 7 = **original derivation と判明** (scope 上方修正)

repo の Lem 12.18(a) 証明 (`tau1_Malpha_centralizer_PQ_eq_bot`) の技法を精読した結果、step 7 の
scope が当初見積りより重いと判明 (要再判断):
- **cyclic は Sylow level でのみ**: repo は M_α 全体の cyclic でなく、α(M) の素数 ℓ の M_α の
  Sylow R_ℓ (rank≥3, `exists_invariant_sylow_Malpha_rank_three`) を取り、`isCyclic_of_pRank_le_one`
  (p-群は pRank≤1⟹cyclic、nilpotent 不要) で R_ℓ⊓C(P) を cyclic 化。**M_α 自体は nilpotent でない**
  (repo は M'/M_α 商の nilpotency `derivedQuotientMalpha_isNilpotent` のみ; M_α は Hall α で非 nilpotent)。
- ⟹ 「M_α=M_β nilpotent ⟹ C_{M_α}(P) cyclic ⟹ Aut-abelian で Q が trivial」近道は **前提崩壊で不可**。
- **P-side は Lem 12.18(a) 適用不能**: 包含に必要な C_{M_α}(P)≠1 は Lem 12.18(a) から出ない
  (C_Q(P)=Q≠1 で仮定破れ; R を Q 役にしても C_R(P)=R≠1 で破れ)。
- **🔴 決定的**: BG は包含 itself を "we can conclude" で**完全に省略** ⟹ step 7 は BG proof の port でなく
  **original derivation** (rank≥3 Sylow + Thompson + Thm 3.7 の機構を未記述 config に再構築)。
  ~数百行 + 数学的 design が必要で、loop の quick-iteration には不向き。

**現況**: per_q は step 7 単一 sorry に還元済 (steps 4b/5/6/8-9 完成・build緑・axiom-clean)。
Cor 13.3 (cyclic Sylow & E₃ prime action) は **unblocked** (13.2 済) で productive。
⟹ ユーザー再判断: step 7 続行 vs Cor 13.3 へ pivot (step 7 は後日 dedicated)。

### 2026-06-13 Lane G (loop): **step 7 hard-stop → Cor 13.3 へ pivot** (ユーザー裁可)

ユーザー裁可で step 7 は documented sorry で温存 (rank framework `5f36ecdb` まで landed;
hCeq の Thompson/Thm 3.7 climax = BG-elided original derivation で dedicated session 行き)。
loop は **Cor 13.3** へ pivot。

**Cor 13.3(a) 証明確定** (clean, tractable — scaffold `cyclicSylow_actsPrime` in S13_PrimeAction):
P = E の cyclic Sylow p (p∉τ₂)。g∈P# について C_{M_σ}(g)=C_{M_σ}(P) を示す:
- ⊇ は自明 (g∈P ⟹ C(P)⊆C(g))。
- ⊆: M*∈ℳ(N_G(⟨g⟩)) を取る。P abelian ∋ g ⟹ P⊆C(g)⊆N(⟨g⟩)⊆M* ⟹ P≤M⊓M*。
  **Cor 13.2(a)** (tau13_pSubgroup_centralizes.1, ⟨g⟩ & M*) で P が M_σ⊓M* を中心化。
  C(g)⊆M* ⟹ C_{M_σ}(g)=M_σ⊓C(g)⊆M_σ⊓M* ⟹ P が C_{M_σ}(g) を中心化 ⟹ C_{M_σ}(g)⊆C(P);
  かつ ⊆M_σ ⟹ ⊆C_{M_σ}(P)。∎
- **要 sub-fact**: `p∈τ₁∪τ₃` (Cor 13.2 の仮定)。`mem_tau_union_of_mem_primeFactors` (S12_ECore:295)
  で p∈τ₁∪τ₂∪τ₃; τ₂ 排除は cyclic Sylow (rank1) vs τ₂⟹pRank_M=2 (`tau2_pRank_eq_two`)。
  ⚠ **要: Sylow-p-of-E が pRank_M(p) を捕捉** (p∈σ' ⟹ Sylow_p E = Sylow_p M) — 次 iteration で確認/構築。

**Cor 13.3(b)** (E₃ prime): Cor 13.2(b) + E₃⊆E'⊆M*' ⟹ π(E₃)⊆τ₁(M*)' (Lemma 12.1: E₃ cyclic normal ⊆E')。
→ Cor 13.2(b) で E₃ が C_{M_σ}(P) 中心化。**次 iteration**。

### 2026-06-13 Lane G (loop): Cor 13.3(a) core landed (`7ae72709`) + τ₂-exclusion 標的確定

**✅ core landed**: `actsPrimeOn_Msigma_of_mem_tau13` (abelian p-部分群 P≤M, p∈τ₁∪τ₃ ⟹ M_σ prime 作用,
sorry-free body, S13_PrimeAction)。再利用可 (Cor 13.3(a) / Thm 13.5 / Lemma 13.7)。

**🎯 τ₂-exclusion 標的確定** (τ def 精読): `tau1∪tau3 = {p∉σ(M) ∧ pRank ↥M p = 1}`
(τ₁=∉π(M'), τ₃=∈π(M'); τ₂=pRank=2)。⟹ cyclicSylow_actsPrime(a) の配線 = **`pRank ↥M p = 1` を示す**
(P cyclic Sylow of E, p∈π(P))。p∉σ は `h.not_mem_sigma_of_mem_primeFactors` ✅; pRank≥1 は Cauchy;
**残 = pRank ↥M p ≤ 1** (τ₂ 排除)。
- **route** (~40 行, 次 iteration): P max-p in E ⟹ P.subgroupOf E は Sylow p ↥E (maximality) ⟹ |P|=|E|_p;
  `card_Msigma_mul_card_E` + p∤|M_σ| (p∈σ') ⟹ |E|_p=|M|_p ⟹ |P|=|M|_p ⟹ P.subgroupOf M は Sylow p ↥M;
  `pRank_sylow_eq` + IsCyclic ⟹ pRank ↥M p = pRank ↥P ≤ 1。`pRank_M_le_two` (≤2) は既存だが不足、=1 が要る。
  ⚠ `pRank ↥M p = pRank ↥E p` は repo に無し ⟹ Sylow-E-M card chain を直接構築。subtype Sylow 注意。
- IsCyclic→IsMulCommutative は `IsCyclic.commGroup` instance + `⟨⟨mul_comm⟩⟩`。
- **(b) E₃**: 別途 (multi-prime, core 直接適用不可; Cor 13.2(b) + E₃⊆E' 経路)。

### 2026-06-13 Lane G (loop): Cor 13.3(a) COMPLETE (`6c0b15ca`) + (b) plan 確定

**✅ Cor 13.3(a) 完了**: `cyclicSylow_actsPrime`(a) 配線済 (helper `mem_tau1_union_tau3_of_isCyclic_sylow_E`
[`8263023c`] + core + IsCyclic.commGroup)。残 sorry = (b) のみ。

**🎯 Cor 13.3(b) plan 確定** (E₃ prime on M_σ; intricate ~80 行, 2 sub-lemma + assembly):
ActsPrimeOn def は **per-element** (∀g∈E₃#, C_{M_σ}(g)=C_{M_σ}(E₃))。core 直接適用不可 (E₃ multi-prime)。
- **B1** `C_{M_σ}(Sylow_p(E₃)) = C_{M_σ}(E₃)` (各 p∈π(E₃)):
  P:=Sylow_p(E₃) は E-normal (cyclic E₃ ◁ E [`E3_normal`] の char 部分群) ⟹ E⊆N_G(P)⊆M* (M*∈ℳ(N_G(P)))。
  E₃⊆E'=derivedInG E [`E3_le_derived hG`] ⊆ M*' (E⊆M* ゆえ) ⟹ π(E₃)⊆π(M*')⊆τ₁(M*)ᶜ (τ₁ def: ∉π(M*'))
  ⟹ `IsPiSubgroup (τ₁ M* )ᶜ E₃`。E₃⊆E⊓M*。**Cor 13.2(b)** (`tau13_pSubgroup_centralizes …).2.1`)
  ⟹ E₃ が M_σ⊓M* 中心化。C_{M_σ}(P)⊆M_σ⊓M* (C(P)⊆N(P)⊆M*) ⟹ E₃ が C_{M_σ}(P) 中心化
  ⟹ C_{M_σ}(P)⊆C_{M_σ}(E₃); 逆は P≤E₃ で自明。
- **B2** cyclic 分解 `C_{M_σ}(g) = ⊓_{p|ord g} C_{M_σ}(g_p)` (g_p = p-part): 一般 cyclic fact (mathlib CRT/zpowers)。
- **assembly**: g∈E₃#, g_p∈Sylow_p(E₃)# ⟹ (a) で C_{M_σ}(g_p)=C_{M_σ}(Sylow_p)=C_{M_σ}(E₃) [B1]
  ⟹ C_{M_σ}(g)=⊓_p C_{M_σ}(E₃)=C_{M_σ}(E₃) [B2]。
- **⚠ landscape**: (b) 後、§13 残 (13.5/13.6/13.7/…) は **Thm 13.4 (step 7) gate** ゆえ lane は step-7 壁に再到達。
  (b) が最後の cleanly-unblocked §13 結果。

### 2026-06-13 Lane G (loop): Cor 13.3(b) **clean route 確定** (B1/B2 不要、単一証明 ~60行)

**🎯 改良 plan** (B1+B2 より大幅 simple、全 lemma 特定済): per-element ∀g∈E₃#, C_{M_σ}(g)=C_{M_σ}(E₃):
- ⊇ 自明 (`fixedBy_le_fixedByElement`)。
- ⊆: p := order(g) の素因数, **x := g^(orderOf g / p)** (order p, x∈⟨g⟩⊆E₃, x≠1)。
  **P:=⟨x⟩=zpowers x** は E-normal: ⟨x⟩.subgroupOf E₃ は ↥E₃ cyclic (`E3_isCyclic`) の部分群ゆえ
  **characteristic** (`characteristic_of_subgroup_of_isCyclic`, Isaacs/Ch04/ForwardFromCh02:403, public);
  E⊆N_G(E₃) (E₃◁E, `E3_normal`) + char lift bridge (`mem_normalizer_map_subtype_of_characteristic`,
  S03f_Prelim:366) ⟹ E⊆N_G(⟨x⟩)。
  M*∈ℳ(N_G(⟨x⟩)) (N_G(⟨x⟩)≠⊤)。E⊆N_G(⟨x⟩)⊆M*。E₃⊆E'=derivedInG E (`E3_le_derived hG`) ⊆M*'
  (E⊆M* ゆえ derivedInG_mono) ⟹ π(E₃)⊆π(M*') ⟹ q∉τ₁(M*) (τ₁ def ∉π(M*')) ⟹ `IsPiSubgroup (τ₁ M*)ᶜ E₃`。
  E₃⊆E⊓M*。**Cor 13.2(b)** (`tau13_pSubgroup_centralizes hG h (Or.inr hpτ3) hxM hxne hxp hMstar |>.2.1 E₃ … `)
  ⟹ E₃⊆C(M_σ⊓M*)。C_{M_σ}(x)⊆M_σ⊓M* (C({x})⊆N(⟨x⟩)⊆M*)。⟹ E₃ が C_{M_σ}(x) 中心化
  ⟹ C_{M_σ}(x)⊆C_{M_σ}(E₃)。C_{M_σ}(g)⊆C_{M_σ}(x) (x∈⟨g⟩, C(g)⊆C(x)) ⟹ C_{M_σ}(g)⊆C_{M_σ}(E₃)。
- p∈τ₃(M): x order p, p∈π(E₃) (x∈E₃), E₃ は τ₃-π-group (`isPiGroup_tau3`) ⟹ p∈τ₃。
- **次 iteration で build** (全 lemma teed up; fiddly = order 算術 x + char-normalizer bridge subtype)。

### 2026-06-13 Lane G (dedicated session): step 7 (hCeq) **深掘り調査** — math 機序を精密化、shortcut 棄却、real path 確定 (ユーザー裁可で head-on)

Cor 13.3 完了後、ユーザー裁可で step 7 (`hCeq : C_{M_α}(P)=C_{M_α}(R)`, S13_Theorem134:262-291 の唯一 sorry) に正面着手。
BG 13.4 原文 (mmd L3568-3598)・Lemma 12.18 (L3484-3508)・repo の 600 行 `tau1_Malpha_centralizer_PQ_eq_bot`
(S12_Lemma1218:410-1029) を精読。**結論: genuine な BG-elided original derivation で確定。以下は次セッションの正本。**

**① 矛盾構造の精密化 (steps 8-9 が hCeq から消費するもの)**:
per_q の最終矛盾は、`A := C_{M_α}(P)` について **(I) inclusion 1 `A ⊆ C(R)`** + **(II) `A ≠ ⊥`** に縮約できる
(hCeq 等式まるごとは不要)。実際 steps 8-9 (実装済) は:
S が A を正規化 (`hSNA`, S⊆C(P)) + (I) `A⊆C(R)` ⟹ three-subgroups で `[A,Q]=1` (`hAcQ`) ⟹
`A ⊆ M_α⊓C(R⊔Q) = C_{M_α}(RQ) = ⊥` (`hCRQ_bot`) ⟹ `A=⊥`。これと (II) `A≠⊥` で矛盾。
- BG は (II) を **inclusion 2 `C_{M_α}(R) ⊆ A`** から得る (`A ⊇ C_{M_α}(R) ≠ ⊥`, `hCR_ne`)。⟹ 結局 **両 inclusion = 等式**が要。
- **🔑 three-subgroups が S-正規化を要するため迂回不能**: `[C_{M_α}(R), Q]=1` を直接 three-subgroups で出そうとすると
  `[[S,R], C_{M_α}(R)]=[Q,C_{M_α}(R)]` に bottom-out して循環。S は `C_{M_α}(R)` を正規化しない (S⊄N(R))。
  BG は等式で `C_{M_α}(R)` を **S-不変な `C_{M_α}(P)` に swap** してこれを回避する。∴ inclusion 1 は本質的。

**② cyclic Aut-abelian shortcut — 着想と棄却 (再調査不要)**:
「もし `A=C_{M_α}(P)` が cyclic なら、S,R が A を正規化 (⊆C(P)) ∧ Aut(cyclic)=abelian ⟹ `Q=[S,R]` が A を中心化
(φ([s,r])=[φ(s),φ(r)]=1 in Aut(A))」という clean な insight を得た。これは正しく、`hAcQ` の three-subgroups を不要化する。
さらにこれから `C_{M_α}(PR) = A∩C(R) ⊆ C(Q)∩C(R)∩M_α = C_{M_α}(RQ) = ⊥` も従う。
**🛑 しかし棄却**: A が cyclic と示せない。`isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one` (S12_ECore:461) は
**`[Group.IsNilpotent H]` を要求**。`M_α = opiCoreInG (alpha M) M` は **Hall α-subgroup で非 nilpotent**
(notes 既出; M'/M_α のみ nilpotent = `derivedQuotientMalpha_isNilpotent`)。⟹ `rank A ≤ 1` は **A = Z-群** (Sylow 巡回)
を与えるのみで cyclic でない ⟹ Aut(A) 非可換 ⟹ shortcut 適用不能。**repo PQ_eq_bot も per-Sylow** (C_{R'}(P) は
R'=Sylow⟹p-群⟹巡回) で処理しており、A 全体の cyclic 性は使っていない。

**③ real path = per-Sylow Theorem 3.7 reconstruction (~数百行, PQ_eq_bot 範型)**:
各 `r'∈α(M)` と PRS-不変 Sylow r' `R'` of M_α (`exists_invariant_sylow_Malpha_rank_three`) で、
`C_{R'}(P)/C_{R'}(R)` 巡回 (`isCyclic_of_pRank_le_one`)、Thompson `R'_1` (`exists_charSubgroup_exponent_not_centralized`)
+ Thm 3.7 (`isNilpotent_of_normalizing_primeOrder_fixedPointFree`) + 巡回内一意性
(`card_eq_prime_of_le_exponent_prime` / `eq_of_card_eq_of_le_of_isCyclic`) で per-Sylow に R-中心化を出し、
**非 nilpotent M_α 上で assemble** する。これが hard part 2 つ:
  (a) **inclusion の正確な Thm-3.7 config が未確定**: BG は inclusion 自体を完全省略 ("we can conclude", L3588-3594)。
      12.18(a) の結論は `C_{M_α}(RQ)=⊥` であって inclusion でない ⟹ inclusion は 12.18(a) の instance でない。
      BG §12-13 に standalone な「commuting τ₁-元の C_{M_α} 包含」補題も無い (grep 確認済)。
      ∴ Thompson 配置を**未記述 config に再構成**する必要 (PQ_eq_bot とは別 statement)。
  (b) **非 nilpotent M_α の assembly**: per-Sylow の R-中心化を全 M_α へ束ねる (C_{M_α}(P) は Sylow の積で書けない)。

**④ 評価と推奨**: notes 既出「original derivation, ~数百行」を**精密に裏付け**た。math 機序 (BG が "we can conclude" で
飛ばす inclusion の正確な論法) が未確定なまま Lean を書くのは coding-into-void ゆえ不可 (難所回避でなく root-cause 未解決)。
**残る本質ギャップ = inclusion `C_{M_α}(P)⊆C(R)` の正確な coprime rank-1 論法**。これは恐らく Thompson 1966 / Gorenstein
の coprime-action「rank-1 centralizer coincidence」型補題を要する (BG が周知として省略)。
- **推奨次手**: (A) Thompson 1966 / Gorenstein のソースで inclusion の正確な論法を pin → per-Sylow + assembly で formalize
  (real multi-session 投資), または (B) step 7 は documented sorry で温存し §13 構造 (13.5→13.10) を sorry'd 13.4 引用で積む
  (scaffold-cite, structural progress; step 7 完成で自動 unconditional 化)。**この session は ④ の調査で head-on を遂行**;
  build/sorry 不変 (notes-only)。

### 2026-06-13 Lane G (dedicated session 続き): ソース読解 (head-on 継続) → **per-Sylow cyclic trick で step 7 を大幅構造化** (正本)

ユーザー裁可で BG Ch3 coprime 構造定理 (Thm 3.6/3.7/3.8/3.9/3.10) + Gorenstein を読解。直接の inclusion 補題は
無いが、**BG Theorem 1.11 (Ω₁-rigidity, repo formalize 済 `S01c_Omega1Rigidity.lean`) が p-群限定**である点が鍵で、
**per-Sylow では C_{R'}(P) が cyclic** ((非 nilpotent M_α 全体では失敗した) cyclic Aut-abelian trick が復活)。
これで step 7 の attack が一変。**以下が新しい正本。前項④の「shortcut 棄却」は per-Sylow で覆る。**

**🔑 per-Sylow cyclic Aut-abelian trick (rigorous・Lean-able)**:
各 `r'∈α(M)` で **PRS-不変 Sylow r' `R'` of M_α** を取る (存在: `SPR = S⋊PR` は {p,q,r}-群で M_α [α-群] と
coprime [p,q,r∉α] ⟹ coprime-action で SPR-不変 Sylow 存在; PR が S を正規化 [`hSinv`] ゆえ SPR が群)。
`C_{R'}(P)` は **cyclic** (`isCyclic_of_pRank_le_one`: R' は r'-群 ∧ rank≤1 ∧ r' odd)。S,R は R' と P を正規化
⟹ `C_{R'}(P)≤C(P)∩R'` を正規化、Aut(cyclic)=abelian ⟹ **`Q=[S,R]` が `C_{R'}(P)` を中心化**。

**この trick から導かれる rigorous facts (全て Lean 構成可)**:
- **(A) Q が `C_{M_α}(P)` を中心化** (= Lean の `hAcQ`, **hCeq 不要で直接導出可**): `C_{M_α}(P)` は自身の Sylow
  `C_{R'}(P)` で生成 (有限群 = ⟨Sylows⟩; coprime-action で C_{M_α}(P) の Sylow r' = C_{R'}(P))、各を Q が中心化 ⟹ 全体中心化。
- **(B) `C_{M_α}(PR)=⊥`** (= R が `C_{M_α}(P)` に FPF, かつ P が `C_{M_α}(R)` に FPF): (A) で `C_{M_α}(P)⊆C(Q)` ⟹
  `C_{M_α}(P)∩C(R) ⊆ M_α∩C(R)∩C(Q) = C_{M_α}(RQ) = ⊥` (`hCRQ_bot`)。
- **(C) `C_{M_α}(R)` は cyclic**: (B) で P が `C_{M_α}(R)≠⊥` に FPF ⟹ Thm 3.7 (`isNilpotent_of_normalizing_primeOrder_fixedPointFree`)
  で nilpotent ⟹ rank≤1 ∧ odd ⟹ cyclic。

**🛑 残る hard core (closure) = inclusion 自体は (A)(B) と「両立して FALSE」**: (A)(B) は **R が C_{M_α}(P) に FPF /
P が C_{M_α}(R) に FPF** を与え、これは BG の inclusion (`C_{M_α}(P)⊆C(R)` 等) と逆 ⟹ BG の inclusion/等式は
偽仮定 Q≠1 下の「偽の派生」。**genuine な closure は S-非対称性で阻まれる**: 「Q が C_{M_α}(P) 中心化」(A) を
C_{M_α}(R) へ移送するには S が C_{M_α}(R)=M_α∩C(R) を正規化する必要があるが **S⊄N(R)** (S は P 経由で定義され R 用の
対称物が無い)。BG は等式でこれを回避。
- **closure の見立て (次の hard core)**: C_{M_α}(R)≠⊥ cyclic の素因子 r''∈α(M) で Sylow R'' (rank≥3) を取り、
  P が C_{R''}(R)≠⊥ (cyclic) に FPF + rank≥3 構造から **Thompson R''_1 (`exists_charSubgroup_exponent_not_centralized`)
  + Thm 3.7** で矛盾を出す (PQ_eq_bot 範型の ~hard core)。これが BG「we can conclude」の実体と推定。
- **⟹ step 7 の改訂 attack (4 step)**: (1) per-Sylow cyclic trick → fact (A)(B) [Lean-able, ~中規模] →
  (2) fact (C) cyclic [Thm 3.7] → (3) **Thompson closure on rank-≥3 R''** [hard core, ~PQ_eq_bot scale] →
  (4) 矛盾。**(1)(2)(4) は機械的、(3) が唯一の真の難所**。

**ツール確定** (全 repo 在): Thm 1.11 `actsTrivially_of_fixes_omega1_centralizer`/`...` (S01c_Omega1Rigidity),
`isCyclic_of_pRank_le_one` (S10_LocalCriteria), Thm 3.7 `isNilpotent_of_normalizing_primeOrder_fixedPointFree`
(S03c), `exists_charSubgroup_exponent_not_centralized` (Thompson 1.13), `exists_invariant_sylow_Malpha_rank_three`
(S12_E), `card_eq_prime_of_le_exponent_prime`/`eq_of_card_eq_of_le_of_isCyclic` (S12_Lemma1218)。
**評価**: 「totally elided」から「(A)(B)(C) rigorous + 単一 Thompson closure」へ前進。次セッションは (1)(2) を land
(fact A=hAcQ を hCeq 非依存で証明し既存 step 8-9 を一部組換え) → (3) Thompson closure に集中。**この session は head-on で
math を大幅前進** (build/sorry 不変, notes-only)。

### 2026-06-13 Lane G (同 session, closure 精密検証): 🛑 **(3) Thompson closure は遮断 — 上の楽観評価を訂正** (definitive)

fact (A) 着工前に closure (step 3) が通るか精査 → **遮断と確定**。上の「(3) Thompson closure on R''」は誤りで、
genuine な impasse。理由 (全て検証済):
- **新 Thm 3.7 矛盾が構成不能**: PQ_eq_bot 型の矛盾は「prime-order 群が非 nilpotent な `Q·R''_1` 等に FPF 作用
  ⟹ Thm 3.7 で nilpotent ⟹ 矛盾」。ここで使える FPF は (i) **P-FPF**: `C_Q(P)=Q≠1` (P が Q を中心化) ゆえ
  `C_{Q·R''_1}(P)=1` が**破れ Thm 3.7 適用不可** / (ii) **R-FPF**: `C_Q(R)=1` ✓ だが**既に (r,R) の 12.18(a)
  適用で消費済** (= `C_{M_α}(RQ)=⊥` を産出) ⟹ 新たな矛盾源にならない。⟹ **新 Thompson 矛盾の起点が無い**。
- **cyclic trick も R 側は不可 (S-非対称性が絶対)**: `C_{M_α}(R)` (cyclic) を正規化する群は `P` / `R` / `C_S(R)` のみで、
  これら**相互の commutator は全て 1** (`[P,R]=1`, `[P,C_S(R)]=1` [P が S 中心化], `[R,C_S(R)]=1`) ⟹ `Q=[S,R]` を
  commutator として産めない。S 全体は `C(R)` を正規化しない (`Q⊄N(C(R))`)。
- **facts (A)(B)(C) は self-consistent** (P が `C_{M_α}(R)≠⊥` cyclic に FPF 作用は矛盾でない) ⟹ **単体で False を産まない**。
  ⟹ hCeq (`C_{M_α}(P)=C_{M_α}(R)`) は **(B) `C_{M_α}(PR)=⊥` + `hCR_ne` の下で False に同値**ゆえ、closure (=False 導出)
  と equi-difficulty (hCeq は doomed でなく closure と同値; 現 Lean 構造は維持で可だが closure を要す)。

**🔴 definitive 所見**: step 7 closure = BG が "we can conclude" で省く inclusion で、**標準 coprime-action machinery
(BG Ch3 全 + Gorenstein + 在 repo 機構) では構成不能**な genuine gap。BG 固有の省略論法は本 session 精査の範囲
(Thm 1.13/3.6/3.7/3.8/3.9/3.10, Prop 1.10/1.16, Thm 1.8/1.11) に**現れず**、original derivation (恐らく未記述 config への
Thompson/Thm 3.7 の非自明再構成、または P-Q 中心化を回避する別経路) を要する。**~数 session 規模の research-level task。**
- **landed 資産**: facts (A)(B)(C) の rigorous な math 確立 (再利用可技法 = per-Sylow cyclic trick) + hCeq=closure 同値性
  + 遮断構造の完全 map。**未 land** (Lean): fact (A) の formalize は ~200 行で closure を閉じない (技法検証のみ) ゆえ保留。
- **推奨**: step 7 は documented sorry で温存 → **§13 構造 (Thm 13.5/Lemma 13.6/13.7…) を sorry'd 13.4 引用で積む**
  (option B; build-green structural progress, step 7 完成で自動 unconditional 化)。step 7 は dedicated research session 行き。

### 2026-06-13 Lane G (同 session): pivot → **Theorem 13.5 の証明設計確定** (次ターン実装; ready-to-build)

step 7 impasse 確定を受け option B へ pivot。**Theorem 13.5 (E₁≠1 ⟹ E₁ acts prime on M_σ)** の clean 証明を設計
(mmd L3600 「E₁ cyclic ⟹ Cor 13.3 + Thm 13.4」)。新 leaf `S13_Theorem135.lean` 予定 (import: S13_PrimeAction
[ActsPrimeOn/cyclicSylow_actsPrime] + S13_Theorem134 [centralizer_le_centralizer_of_tau1])。

**設計 (K := fixedBy (M_σ) E₁ を universal target に)**: `ActsPrimeOn (M_σ) E₁` = ∀g∈E₁#, fixedByElement g = K。
⊇ は `fixedBy_le_fixedByElement` で free。⊆ は `M_σ⊓C(g) ≤ C(E₁)` を示す:
1. **cross-prime 補題 (crux)**: ∀ 素数 p,p' ∈ π(E₁), `fixedBy (M_σ) P_p = fixedBy (M_σ) P_{p'}` (P_p=Sylow p of E₁
   =Sylow p of E [E₂E₃ coprime])。導出 = Cor 13.3(a) で `fixedBy P_p = fixedByElement (Ω₁P_p の生成元)`
   (prime action) + **Thm 13.4** を (Ω₁P_p ∈ ℰ_p¹(E), Ω₁P_{p'} ∈ ℰ_{p'}¹(C_E(Ω₁P_p)) [E₁ abelian]) で適用 ⟹
   `C_{M_σ}(Ω₁P_p) ⊆ C_{M_σ}(Ω₁P_{p'})`、両 prime ∈ τ₁ ゆえ対称で =。
2. `fixedBy E₁ = ⋂_{p'} fixedBy P_{p'} = K` (E₁=∏ Sylows, C(E₁)=⋂C(P_{p'}); 全 fixedBy P_{p'} 相等)。
3. g∈E₁#: ⟨g⟩=∏_{p|ord g}⟨g_p⟩ ⟹ `fixedByElement g = ⋂_{p|ord g} fixedByElement g_p = ⋂ fixedBy P_p = K`
   (Cor 13.3(a) で各 g_p∈P_p#)。

**実装注意**: fiddly = (a) E₁ の Sylow p を取り cyclic/maximal-in-E を示し cyclicSylow_actsPrime 適用、(b) Ω₁(P_p) ∈
elemAbelianOfRank G p 1 (= ℰ_p¹) 構成、(c) ⟨g⟩=∏⟨g_p⟩ CRT と C(∏)=⋂C。~200-300 行・all-or-nothing (sorry 不可)。
**この session は step 7 を exhaustive head-on (facts A/B/C rigorous + 遮断完全 map, commit a43dbc1e/9b924c31/54c2b33f)、
13.5 は設計まで。次ターン = 13.5 実装。**

### 2026-06-13 Lane G (main 取込後の再調査): step 7 に **新 lead = `C_{M_α}(P) ⊆ M*` 埋め込み**

main 取込 (§12 Cor 12.16(a)(b) proof + 12.13/12.15 proven, build-fix `2d11cc56`) 後、step 7 closure を再調査。
- **① σ-disjointness 角度は dead end**: `disjoint_of_not_conj` (10.12) の `sigma M ∩ sigma H = ∅` は **part (b) M_σ
  nilpotent 要求** (S10_LocalLemmasCore:1204)。per_q は M_α≠⊥ ⟹ M_σ 非 nilpotent ゆえ step 6 の `q∈σ(M)∩σ(M*)` は
  矛盾にならない (無条件版 = Thm 13.9 = 13.4 downstream で循環)。`mem_sigma_inter_sigma_imp.2` は逆に「M_σ 非 nilpotent」を
  与えるのみ (既知 = M_α≠⊥ と整合)。
- **② 🆕 新 lead `C_{M_α}(P) ⊆ M*`** (従来解析は M_α(M) 内に閉じ M* 未使用): `C(P)⊆N_G(P)⊆M*` (`hNP`) ⟹
  **`C_{M_α}(P) = M_α(M)⊓C(P) ⊆ M_α(M)⊓M*`**。`α(M)∩σ(M*)=∅` (10.12a) ⟹ `C_{M_α}(P)` は **σ(M*)'-部分群**
  (`⊓M*_σ=⊥`)。かつ fact (A) で **Q≤M*_σ が中心化**。⟹ hard-core 対象が M* 構造に埋込まれ「σ(M*)'-群 ∧ M*_σ の Q に
  中心化」の強制約下。**BG「since q∉α(M), we can conclude」の "q∉α(M)" はこの α(M)∩σ(M*)=∅ disjointness (M* 埋込) の
  発動と推定** — inclusion 再構成の鍵候補。Cor 12.14 (`ℳ(C_G(σ-subgrp))={M*}`)/Lem 12.17/Cor 12.16 (now proven) と接続可能性。
- **⚠ 非対称**: `C_{M_α}(R) ⊄ M*` (M*∈ℳ(N_G(R)) でない) — inclusion の向き/S-非対称性の根源、M* 埋込は P 側のみ。
- **評価**: 新 lead は genuine だが closure には未到達 (M* 側構造定理との接続を要精査)。次の step-7 attack は「②の M* 埋込
  + Cor 12.14/12.16 (proven) で C_{M_α}(P) の制約を締める」方向。impasse の core は残るが attack surface が一つ増えた。

### 2026-06-14 Lane G (M* 埋込の深掘り): 🔴 **closure 未到達を確定、impasse は robust と再確認**

ユーザー指示で M* 埋込 lead を最後まで深掘り。**新たな structural fact を多数得たが closure には至らず**、impasse が
robust であることを精密に確定:
- **Cor 12.14** (`maximalContaining_centralizer_eq_singleton`, S12_E:53; X∈ℰ_p¹(M), p∈σ(M), p∈β(M)∨X≤M_σ' ⟹
  ℳ(C_G(X))={M}) も `C_{M_α}(P)⊆M*` を裏付ける (X≤Q order-q ⟹ C_G(Q)⊆M*) が**新制約ゼロ** (既知の埋込再確認)。
- **R'' (M_α の rank≥3 Sylow) は非可換** (`exists_invariant_sylow_Malpha_rank_three` は abelian 非保証) ⟹ PR-module
  表現論分解は clean 適用不可。
- **🔑 circular 構造を確定**: fact (B) `C_{M_α}(PR)=⊥` の下で **inclusion 1 (`C_{M_α}(P)⊆C(R)`) ⟺ `C_{M_α}(P)=⊥`**
  (R が C_{M_α}(P) に FPF), かつ **inclusion 2 (`C_{M_α}(R)⊆C(P)`) ⟺ `C_{M_α}(R)=⊥` ⟺ 矛盾そのもの** (Ω₁-rigidity
  [Thm 1.11 per-Sylow] で「P が C_{M_α}(R) 中心化 ⟺ P が各 z_{r''}=Ω₁(C_{R''}(R)) 固定」に還元、だが fact (B) で
  `z_{r''}∈C(P)⟹z_{r''}∈C_{R''}(PR)=⊥` ⟹ P は z_{r''} を**動かす** ⟹ inclusion 2 は B の下で FALSE)。
  ⟹ **inclusion を独立に導出する = 矛盾を導出する**で循環。BG の「since q∉α(M)/r∈τ₁(M), we can conclude」は
  偽仮定 Q≠1 下でのみ valid な step で、**標準機構での独立再構成路が存在しない**ことを確定。
- **全 attack 封鎖の根本原因 (3 点)**: (i) Thompson/Thm 3.7 は **P が Q を中心化** (`C_Q(P)=Q≠1`) で全 FPF operator
  (P/R/S) 封じ [R は (r,R) 12.18(a) で消費済・C_{R''_1}(R)≠⊥ で再利用不可]; (ii) M* 埋込は **α(M)-素数が σ(M*)-制約
  (Cor 12.14/12.16) と直交** (α(M)∩π(E)=∅ ゆえ Cor 12.16 の π(E)-rank bound が効かない); (iii) cyclic/Ω₁ 還元は循環。
- **🟥 最終評価**: step 7 = **標準 coprime/local 機構 (BG Ch1-3 + §10-12 proven + Gorenstein) で到達不能な genuine
  research gap**。残る理論的可能性 = R'' (非可換 rank≥3) 上の PR 作用の非自明な表現論/Hall-Higman 型議論、または BG が
  別途持つ未特定 lemma。**dedicated な数学研究を要し、loop/通常実装では不可**と確定。productive 前進は §13 構造 (13.5+)。

### 2026-06-14 Lane G: 🎉🎉🎉 **step 7 GAP SOLVED — ChatGPT の「一様排除」洞察で reconstruction gap が埋まった**

ユーザーが ChatGPT に gap を尋ね、回答を `notes/bg/bg_theorem13_4_gap_verification.md` に配置。**全ステップ検証 → 正しい**。
私の「impasse」は誤り (新しい議論を探していたが、実際は **BG 自身の前半議論の再適用**だった)。

**🔑 核心 = 一様排除補題 (UniformExclusion)**: BG の 13.4 前半 (`[S,R]≠1 ⟹ q∉α(M)` を M* 経由で導く部分) は
**素数 q について一様**。すなわち:
> `a∈τ₁(M), A₀∈ℰ_a¹(E), b∈π(E), B₀∈ℰ_b¹(C_E(A₀)), s∈σ(M)`、T を A₀B₀-不変 Sylow s of C_{M_σ}(A₀) とすると、
> **`[T,B₀]≠1 ⟹ s∉α(M)`**。

証明 = **私の per_q steps 1-6 を (P,R,q,S)→(A₀,B₀,s,T) に一般化したもの** (s が特定 q であることを一切使わない事を全 step 検証)。

**包含の証明 (alpha_fixed_le_fixed)**: `C_{M_α}(A₀)` の各素因子 ℓ は **ℓ∈α(M)** (M_α が α-群)。ℓ-Sylow B_ℓ は A₀B₀-不変
Sylow ℓ of C_{M_σ}(A₀) (ℓ∈α ⟹ C_{M_σ}(A₀) の ℓ-部分は M_α 内 ⟹ B_ℓ∈Syl_ℓ(C_{M_σ}(A₀)))。UniformExclusion の対偶
(ℓ∈α(M) ⟹ `[B_ℓ,B₀]=1`) を各 ℓ に適用 → B₀ が全 Sylow を中心化 → ⟨Sylows⟩=C_{M_α}(A₀) ⟹ **`C_{M_α}(A₀)⊆C_{M_α}(B₀)`**。

**per_q への適用**: hCeq = `le_antisymm (alpha_fixed_le_fixed P R) (alpha_fixed_le_fixed R P)` (対称包含、後者は r∈τ₁(M)
[hrτ1M 既存] + P∈ℰ_p¹(C_E(R)))。⟹ **hCeq の sorry 除去、steps 8-9 (既存) で閉じ、step 7 完全解決**。

**なぜ見落としたか**: 私の fact (A)(B)(C) は正しく (ChatGPT も確認)、`C_{M_α}(P)∩C_{M_α}(R)=⊥` も真。だが inclusion を
**新議論**で示そうとして詰まった。実際は inclusion ⟺「各 α-Sylow が R-中心化」⟺「BG の一様排除を各 α-Sylow に適用」。

**形式化プラン**: (1) `uniform_exclusion` (= per_q steps 1-6 を一般化, 結論 `s∉α(M)`); (2) `alpha_fixed_le_fixed`
(各 α-Sylow に (1) 適用 + Sylow 生成 assembly); (3) per_q の hCeq を (2) で埋める。S13_Theorem134.lean に追加 (~250 行)。
正本 = `notes/bg/bg_theorem13_4_gap_verification.md` (ChatGPT 回答 + 私の検証)。

### 2026-06-14 Lane G: ✅✅✅ **step 7 IMPLEMENTED — Theorem 13.4 完全証明 (sorry-free)**

上記プランを実装完了 (S13_Theorem134.lean):
- **`uniform_exclusion`** (新 top-level, ~120 行): per_q steps 1-6 を `(a,A₀,b,B₀,s,T)` に一般化、`⁅T,B₀⁆≠⊥ → s∉α(M)`。
  first-try build green (steps 1-6 の転記が一発で通った)。
- **`alpha_fixed_le_fixed`** (新 top-level, ~55 行): outer reduction `msigma_centralizer_le_of_invariant_sylow_centralized`
  を範型に M_α 版。`eq_of_le_of_forall_full_prime_pow` + `exists_aInvariant_sylow_subgroup` で各 ℓ の B₀-不変 full Sylow
  に `uniform_exclusion` 対偶 (ℓ∈α(M) ⟹ `[S,B₀]=⊥`) を適用 → `C_{M_α}(A₀)⊆C_{M_α}(B₀)`。first-try build green。
- **per_q hCeq** = `le_antisymm (alpha_fixed_le_fixed hG h hp hP hPE hr hR hRC) (alpha_fixed_le_fixed hG h hrτ1M hR hRE hpE hP (le_inf hPE hPCR))`
  (逆向きは `hpE : p∈π(E)` [`mem_primeFactors_of_isPGroup_le`] + `hPCR : P≤C(R)` [commutator 対称])。**sorry 除去**。Thompson 用 rank bounds は不要化で削除。
- **`#print axioms centralizer_le_centralizer_of_tau1` = `[propext, sorryAx, Classical.choice, Quot.sound]`** —
  sorryAx は §12 scaffold (Cor 12.16 / Prop 12.15 / Thm 12.13 の S12_E sorry'd statement) 由来のみ、**新規 axiom 0**。
  ⟹ **Theorem 13.4 は §12-conditional で完全証明** (他の G 結果と同列、Lane F の §12 完成で自動 unconditional 化)。
- docstring 3 箇所 (WIP / per_q / centralizer_le_centralizer_of_tau1) を ✅COMPLETE に更新。leaf build 3087 green、実 sorry 0。
- **🎯 §13 frontier 解放**: Thm 13.4 完成で **Thm 13.5 / Lem 13.6 / 13.7 / … の step-7 gate が消滅** — 以降 §13 結果は
  proof レベルで unblocked (§12 scaffold-cite のみ)。次 = Theorem 13.5 (設計済 [上記] + 13.4 完成で完全に積める)。

### 2026-06-14 Lane G: ✅✅✅ Theorem 13.5 COMPLETE — E₁ prime action (sorry-free, **完全 axiom-clean**)

`E1_actsPrime` を S13_PrimeAction に in-place 実装 (実 sorry 7→6)。**`#print axioms` = [propext,
Classical.choice, Quot.sound] — sorryAx 0**。⟹ main 取込で **Lane F の §12 が完全 PROVEN 化**
(Prop 12.15 / Thm 12.13 / Cor 12.16 すべて sorry-free) されたため、推移的に **Thm 13.4 / Cor 13.3 /
Cor 13.2 / Lemma 13.1 もすべて axiom-clean** = §13 (13.1–13.5) は完全 unconditional。AxiomsCheck に
clean `#assert_only_allowed_axioms` 登録、full build 3788 jobs green (36s)。

**証明構造** (設計どおり、Sylow 分解 API 不要):
- helper `key` (cross-prime core): order-`p` 元 `x ∈ E₁` で `C_{M_σ}(x) = C_{M_σ}(E₁)`。⊇ free、
  ⊆ は `le_centralizer_of_forall_prime_isPGroup` (K=E₁) で「各素冪部分群 `R ≤ E₁` が `C_{M_σ}(x)` を
  中心化」へ還元 → R≠⊥ で order-`r` 元 `y∈R` 取り、**Thm 13.4** (`⟨x⟩∈ℰ_p¹(E)`,
  `⟨y⟩∈ℰ_r¹(C_E⟨x⟩)`; E₁ abelian で `x,y` 可換) → `C_{M_σ}(x) ⊆ C_{M_σ}(y) = C_{M_σ}(R)`
  (後者 = R の prime action = `actsPrimeOn_Msigma_of_mem_tau13`, Cor 13.3(a) core)。
- Main: `g∈E₁#` を素因子 `p` の `x=g^{ord g/p}` (order p) に落とし `C(g)⊆C(x)` + `key`。
- 補助 helper (theorem 内 have): `hcent_zpowers` (`C({z})=C(⟨z⟩)`), `hE1comm` (E₁ abelian),
  `hzp_mem` (order-prime 元 → `⟨z⟩∈ℰ¹`, `Subgroup.IsElementaryAbelian.of_card_prime`)。
- 🔑 **r=p ケースも Thm 13.4 が許容** (`{p r}` 独立, r≠p 制約なし)。`le_centralizer_of_forall_prime_isPGroup`
  が prime-power induction で「E₁=⊔Sylow」を暗黙に carry ⟹ cyclic→Sylow 明示分解の自作不要。
- **配置**: S13_PrimeAction 内 in-place (Cor 13.3 と同所)。新 leaf にしない理由 = 下流 stub
  (13.6/13.7) が 13.5 に依存し leaf 化すると import cycle。AxiomsCheck は既に S13_PrimeAction を
  import ゆえ配線追加不要。

**次 = Lemma 13.6** (mmd L3574, stub `maximalContaining_eq_singleton_of_E1`): `1⊂P⊆E₁`, `q∈σ(M)`,
`X∈ℰ_q¹(C_{M_σ}(P))`, `S` を `M_σ` の Sylow `q` とすると `ℳ(C_G(X))=ℳ(S)={M}`。deps = Thm 13.5 ✅ /
Cor 12.6 / Lem 12.17 / Thm 13.4 ✅。⚠ session-1 audit 既知: Cor 12.14 が `ℳ(S)` (S=Sylow) に要する
形を `maximalContaining_centralizer_eq_singleton` が脱落 → 13.6 着工時に要確認。

---

## 2026-06-02 B7 foundation checkpoint

Lean file: `OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeAction.lean`.

Concrete surfaces now present:
- Definitions: `fixedBy` (`C_N(X)`), `fixedByElement` (`C_N(g)`), `ActsPrimeOn`, and `ActsRegularlyOn`.
- Basic API: definitional rewrites for the centralizer predicates, `fixedBy_le_fixedByElement`, `ActsRegularlyOn.toActsPrimeOn`, monotonicity in the acted-on subgroup for both regular and prime action, and bottom-subgroup constructors.

Current Lean inventory: 11 theorem-level `sorry`s remain in §13. The two action predicates and their basic API are sorry-free.

Main proof blockers: BG Lemma 10.8, Corollary 12.16(a), Lemma 12.18/12.19, §10 beta-complement/normalizer gates, and the remaining §12 tau/E structural results. These remain explicit theorem dependencies rather than fields on `ActsPrimeOn`.

**スコープ**: BG §13 (pp.97-104 in PDF), mmd L3484-3739, **7 主要結果**.
**形式化先 (予定)**: `OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeAction.lean`
**ROADMAP 上の位置**: Phase 2a 第 4 波 (§12 完成必須)
**役割**: prime action 構造定理. E の derived series に基づく Thompson 風の作用理論. §14 (Type 𝒫 Counting) と §15 (M_F structure) への橋渡し.
**難度**: ★★★★☆ (§12 より軽いが，Thompson 作用による高度な局所制御が必要)

---

## TL;DR: Prime Action = 素数別作用制御の精密構造

§13 は **maximal subgroup M 内で，complement E が M_σ に対して特定素数 p に対してのみ作用する** という prime action の概念を導入・確立. 

**核心結果**:
1. **Lemma 13.1**: 異なるmaximal M* との prime 相互作用 → p-centralizer の制御
2. **Corollary 13.3**: cyclic Sylow, E₃ は prime action (定義確認)
3. **Theorem 13.4**: τ₁(M) の element と他素数 element との derived series 制御 (most intricate)
4. **Theorem 13.5**: E₁ は prime action (cyclic Sylow consequence)
5. **Lemma 13.6**: E₁ の作用下での M_σ の maximal family 一意性
6. **Lemma 13.7**: E₁E₃ 同時作用の prime 性 (conditional)
7. **Lemma 13.8–13.10**: 相互作用制約と §14 への transition

形式化では **800-1200 行** Lean 予想（proof density は §12 より低い）.

---

## §13 全 7 結果（精密リスト）

| # | 名前 | 型 | 行範囲 | 概要 | 証明長 | 依存 |
|----|------|-----|--------|------|--------|------|
| 1 | **Lemma 13.1** | Lemma | 3498-3516 | 異 maximal M* との p 相互作用 → p-centralization | 19行 | §12 (Cor12.16), §10 (Thm10.2) |
| 2 | **Corollary 13.2** | Corollary | 3518-3524 | τ₁∪τ₃ の element: p-centralizer, τ₁' 作用 | 7行 | Lemma 13.1 |
| 3 | **Corollary 13.3** | Corollary | 3526-3534 | cyclic Sylow p-subgroup & E₃ は prime on M_σ | 9行 | Cor 13.2 |
| 4 | **Theorem 13.4** | Theorem | 3536-3568 | **τ₁ element P & other R: C_{M_σ}(P) ⊆ C_{M_σ}(R)** | 33行 | Cor 13.2, §12 (Lemma 12.18) |
| 5 | **Theorem 13.5** | Theorem | 3570-3572 | E₁ は prime on M_σ | 3行 | Cor 13.3, Thm 13.4 |
| 6 | **Lemma 13.6** | Lemma | 3574-3595 | E₁ 作用下 M_σ Sylow の maximal family 一意性 | 22行 | Thm 13.5, §12 (Cor 12.6, Lemma 12.17), Thm 13.4 |
| 7 | **Lemma 13.7** | Lemma | 3596-3628 | E₁E₃ 同時作用が prime (E₁ が E₃ を非正則作用でない場合) | 33行 | Thm 13.5, Cor 13.3, Thm 13.4, Lemma 13.6, Cor 12.6 |
| * | **Lemma 13.8–13.10** | Auxiliary | 3630-3695 | 相互maximal の禁止configuration + Theorem 13.10 (Conclusion) | 66行計 | Lemma 13.6, 13.8, §12全般 |

**計**: 主結果 7 個, 補助 3 個 (Lemma 13.8, 13.9 = Thm実質, Cor 13.11 etc.)
**合計 mmd**: 256 行 (§12 の 460 行より compact)
**主要証明**: Thm 13.4 (33行, Thompson 風)，Lemma 13.7 (33行, mutual action), Lemma 13.8 (32行, contradiction)

---

## Prime Action の定義と由来

### 素数 p ∈ σ(M) に対する prime action

X ⊆ G (nonidentity p-subgroup, p 素数) が **M_σ に対して prime に作用する** ⟺

**定義1 (original)**:
$$C_{M_\sigma}(g) = C_{M_\sigma}(X) \text{ for all } g \in X^\#$$

**定義2 (elementary part版)**:
$$C_{M_\sigma}(P) \subseteq C_{M_\sigma}(X) \text{ for all } P \in \mathcal{E}^1(X)$$

**補注**: この定義は **1 つの素数 p のみに relative**. X が multiple primes を contain すれば，その product への "prime" status は定義されず，むしろ **各素因子ごとに separately** prime か否かを判定.

### Regular action との対比

- **regular**: C_{M_σ}(g) = 1 for all g ∈ X^# (最も制限的)
- **prime**: C_{M_σ}(g) = C_{M_σ}(X) for all g ∈ X^# (中程度制限)
- **general**: no constraint

§13 の主戦場は **regular と prime の中間** に落ちる coprime-action scenarios.

---

## 7 結果の構造と証明梗概

### Group I: 初等的 prime action (結果 1-5, Lemma 13.1 – Theorem 13.5)

#### **Lemma 13.1** (L3498-3516)

**主張**:
- M* ∈ ℳ, p ∈ π(E) ∩ π(M*), p ∉ τ₁(M*), [M_σ ∩ M*, M ∩ M*] ≠ 1, M* ≄ M に対して:
  1. Every p-subgroup of M ∩ M* centralizes M_σ ∩ M*
  2. p ∉ τ₂(M*)
  3. (if p ∈ τ₁(M)) then p ∈ β(G)

**数学的意味**:
- 異なるmaximal M, M* 間の p-相互作用で，**p-subgroup は M* 側を stabilize するのに十分に大きい** ことが imply される.
- この補題は "maximal family の disjointness" 方向への第一歩で，§12 の Proposition 12.15 (σ(M) disjointness) を踏台にして，**complement E の側面** から p の exclusivity を示す.

**証明スケッチ** (L3505-3516):
1. [M_σ ∩ M*, M ∩ M*] ≠ 1 から，∃q ∈ σ(M) ∩ π(M*').
2. Y = Sylow q-subgroup of M*'. Lemma 10.8 (M_β' structure) + Frattini で M* = N_{M*}(Y)M_β.
3. If p ∈ τ₂(M*): then r_p(N_{M*}(Y)) = 2 (Lemma 12.1(g)) ⟹ p ∉ β(G) (Cor 12.16(a) contradiction) ⟹ p ∉ τ₂(M*).
4. p ∈ σ(M*) ∪ τ₃(M*) なので，M* の Sylow p ⊆ M*'. P を M ∩ M* の p-subgroup とすると，P ⊆ M*_α S (S = Sylow p of M*).
5. M*_α S は σ(M)'-group ⟹ [M_σ ∩ M*, P] = 1.

**キーテクニック**: Frattini argument + lemma 10.8 (β-radical nilpotency) の合成.

**形式化見積**: 80-120 行.

---

#### **Corollary 13.2** (L3518-3524)

**主張**:
- p ∈ τ₁(M) ∪ τ₃(M), P = nonidentity p-subgroup of M, M* ∈ ℳ(N_G(P)) に対して:
  1. Every p-subgroup of M ∩ M* centralizes M_σ ∩ M*
  2. Every τ₁(M*)'-subgroup of E ∩ M* centralizes M_σ ∩ M*
  3. (if [M_σ ∩ M*, M ∩ M*] ≠ 1) then p ∈ σ(M*), and (if p ∈ τ₁(M)) p ∈ β(M*)

**証明**: Lemma 13.1 を p ∈ τ₁(M) ∪ τ₃(M) の場合に apply. Lemma 12.2(a) で p ∈ σ(M*) ∪ τ₂(M*) を ensure.

**役割**: Lemma 13.1 の **τ₁(M), τ₃(M) specialization**. 以下の Corollary 13.3 の土台.

**形式化見積**: 40-60 行.

---

#### **Corollary 13.3** (L3526-3534)

**主張**:
1. Every nontrivial cyclic Sylow p-subgroup of E acts **prime** on M_σ.
2. The group E₃ acts **prime** on M_σ.

**数学的意味**: 
- E₁ は cyclic (Lemma 12.1(d)), τ₁(M) に属す → Corollary 13.3(a) で cyclic Sylow は prime.
- E₃ は cyclic normal (Lemma 12.1(d)), τ₃(M) に属す → Corollary 13.3(b) で prime.
- **これが Theorem 13.5 (E₁ is prime) の first step**.

**証明** (L3530-3534):
1. (a): P = cyclic Sylow p of E, p ∈ τ₁(M) ∪ τ₃(M). Take M* ∈ ℳ(N_G(P)).
   - Cor 13.2(a): Every p-subgroup of N_E(P) centralizes C_{M_σ}(P) ⟹ P prime on M_σ.
2. (b): E₃ cyclic normal in E, Lemma 12.1(d) ⟹ E₃ ⊆ E'. So E ⊆ N_G(Q) (Q Sylow 3 of E₃), E₃ ⊆ E' ⊆ M*.
   - Cor 13.2(b) で E₃ 는 centralizer.

**形式化見積**: 50-70 行.

---

#### **Theorem 13.4** (L3536-3568) — Main Theorem

**主張** (L3538):
- p ∈ τ₁(M), P ∈ ℰ_p¹(E), r ∈ π(E), R ∈ ℰ_r¹(C_E(P)) に対して:
$$C_{M_\sigma}(P) \subseteq C_{M_\sigma}(R)$$

**数学的意味**:
- τ₁(M) の element P と，それを centralize する他素数 element R の interaction.
- **Derived series との緊密な coupling**: τ₁(M) は p ∉ π(M'), rank 1 → rank small.
- R が C_E(P) 内の元素的 r-subgroup なら，R の M_σ への作用は P より「弱い」.
- これは **Thompson の作用論** の中核: "小さい element が大きい element の centralizer に dominant".

**証明** (L3540-3568, 28 行):

1. **仮定**: [S, R] ≠ 1 (where S = PR-inv Sylow q-subgroup of C_{M_σ}(P), q ∈ σ(M)).
   
2. **Step 1** (L3544-3550): Take M* ∈ ℳ(N_G(P)).
   - [S, R] ⊆ [M_σ ∩ M*, R] (by construction).
   - Cor 13.2 ⟹ p ∈ β(M*), r ∈ τ₁(M*).

3. **Step 2** (L3552-3556): 
   - S = C_S(R) × Q (Q = [S, R], S abelian by Thm 12.13).
   - Lemma 12.18(a) (with r, R, M* in place of p, P, M) ⟹ ℳ(N_G(Q)) = {M*}.
   - Cannot have Prop 12.15(e) because P ⊆ M ∩ M*_σ ⟹ q ∈ σ(M*).
   - Prop 12.15(d) ⟹ M_α ≠ 1, r ∈ π(E) ∩ τ₁(M*) ⊆ τ₁(M).

4. **Step 3** (L3558-3567):
   - From [S, R] ≠ 1 and Lemma 12.18: C_{M_α}(P) ⊆ C_{M_α}(R) and C_{M_α}(R) ⊆ C_{M_α}(P).
   - So C_{M_α}(P) = C_{M_α}(R).
   - But ℳ(N_G(Q)) ≠ {M} ⟹ Lemma 12.18(a) yields C_{M_α}(R) ≠ C_{M_α}(RQ).
   - **Contradiction** ⟹ [S, R] = 1 ⟹ R centralizes S ⟹ C_{M_σ}(P) ⊆ C_{M_σ}(R).

**キーテクニック**: 
- **Maximal family の一意性 (Lemma 12.18)** と **derived series の abelian structure (Thm 12.13)** の合成.
- Proposion 12.15 の case analysis (5 cases: (a)-(e)) で，4 cases を eliminate し，1 case (d) に絞る.
- **最後の矛盾**: C_{M_α}(RQ) の identity vs. non-identity の対比.

**数学的インサイト**: 
- Theorem 13.4 は「τ₁ element P のみ作用を制限すれば，他素数 R の作用は P に dominated される」という **prime action の証明の心臓部**. 
- これは Thompson 1966 論文の "fixed point theorem" の local incarnation.

**形式化見積**: 200-300 行 (proof が multi-case).

---

#### **Theorem 13.5** (L3570-3572)

**主張**: E₁ ≠ 1 ⟹ E₁ acts prime on M_σ.

**証明** (L3572, 1 行!): 
- E₁ cyclic (Lemma 12.1(d)) ⟹ Cor 13.3(a) + Thm 13.4 で E₁ prime.

**簡潔性の理由**: Corollary 13.3 + Theorem 13.4 が all work; no additional case analysis needed.

**形式化見積**: 20-30 行.

---

### Group II: Prime Action の extended analysis (結果 6-7, Lemma 13.6–13.7)

#### **Lemma 13.6** (L3574-3595) — Maximal Uniqueness

**主張** (L3574-3576):
- 1 ⊂ P ⊆ E₁, q ∈ σ(M), X ∈ ℰ_q¹(C_{M_σ}(P)), S = Sylow q-subgroup of M_σ に対して:
$$\mathscr{M}(C_G(X)) = \mathscr{M}(S) = \{M\}$$

**数学的意味**:
- E₁ の nontrivial subgroup P に対して，C_{M_σ}(P) の元素的 q-part は **G 全体において M にのみ maximal に contain される**.
- **M の一意性の再確認**: E₁ acting via derived series → maximal family の整合性.

**証明** (L3578-3594, 17 行):

1. **仮定の簡略化** (L3578-3582):
   - Cor 12.14 ⟹ q ∉ β(M), X ⊄ M_σ' と仮定可（否，M(C_G(X)) = {M} 自動).
   - Thm 13.5 ⟹ C_{M_σ}(P) = C_{M_σ}(E₁) (P ⊆ E₁ なので).

2. **Hall structure** (L3584-3586):
   - Thm 12.13: q ∉ β(M) ⟹ E' centralizes some Sylow q of M_σ.
   - Prop 1.5 (A-invariant Hall): E normalizes S, assume X ⊆ S ⊆ C_{M_σ}(E').

3. **E₂ ≠ 1 確認** (L3588):
   - Lemma 12.17 ⟹ C_{M_σ}(E) ⊆ M_σ'.
   - X ⊄ C_{M_σ}(E) ⟹ E₁E' ≠ E ⟹ E₂ ≠ 1 (E = E₁E₂E₃).

4. **τ₂ case の推論** (L3590-3594):
   - Take p ∈ τ₂(M), Q ∈ ℰ_p²(E).
   - A = Q ⊲ E (Cor 12.6(a)), C_{M_σ}(A) = 1 (Thm 12.5(d)).
   - Thm 13.4: A₀ = C_A(E₁) ⊆ A centralizes X (by 13.4).
   - A = A₀ × [A, E₁] ⟹ A centralizes X, contradiction to C_{M_σ}(A) = 1.

**キーテクニック**: 
- **Thm 12.5(d)** (τ₂ case で C_{M_σ}(A) = 1) と **Thm 13.4** (C_{M_σ}(P) ⊆ C_{M_σ}(A)) の矛盾から，maximal family を force.

**形式化見積**: 120-150 行.

---

#### **Lemma 13.7** (L3596-3628) — Simultaneous E₁E₃ Action

**主張** (L3596):
- E₁ ≠ 1, E₁ does not act regularly on E₃ に対して:
$$E_1 E_3 \text{ acts prime on } M_\sigma$$

**数学的意味**:
- E₁ と E₃ は coprime order (τ₁ ⊥ τ₃), 両者ともcyclic, normal relations あり.
- "E₁ が E₃ に**非正則** (not regularly)" = ∃ P ∈ ℰ_p¹(E₁), R ∈ ℰ_r¹(E₃) with P centralizes R.
- ⟹ E₁E₃ (their product) は prime on M_σ.
- **物理的意味**: 2 つの cyclic-coprime actions が "anti-regular" なら，product も prime 性を保つ.

**証明** (L3598-3628, 31 行):

1. **Initial reduction** (L3598-3604):
   - P ∈ ℰ_p¹(E₁) centralizes R ∈ ℰ_r¹(E₃) (non-regular assumption).
   - Thm 13.4: C_{M_σ}(P) ⊆ C_{M_σ}(R).
   - Thm 13.5, Cor 13.3(b): E₁, E₃ prime on M_σ, coprime order.
   - If C_{M_σ}(P) = C_{M_σ}(R) ⟹ E₁E₃ prime (by abelian formula on coprime actions).

2. **Main case: C_{M_σ}(P) ⊂ C_{M_σ}(R)** (L3608-3628):
   - Assume strict inequality (otherwise done).

3. **Step 1** (L3614-3616):
   - C_{M_σ}(R) ≠ 1 ⟹ Cor 12.6(d): τ₂(M) = ∅.
   - So E = E₁E₃ (no E₂).

4. **Step 2** (L3618-3627):
   - R ⊲ E (E₃ normal cyclic), take M* ∈ ℳ(N_G(R)).
   - E ⊆ M*, E₃ ⊆ M* ⟹ 1 ⊂ P ⊆ C_{E₁}(M_σ ∩ M*) (from L3620).
   - By Cor 13.2(b): E₁ ⊆ Hall τ₁(M*), apply Thm 13.5 to M*: E₁* prime on M*_σ.
   - Thus E₁* centralizes R.

5. **Step 3** (L3622-3628):
   - So E₁ centralizes R ⟹ R ⊆ Z(E) (by properties of E₃, Lemma 12.1(d)).
   - But Lemma 12.1(d): C_{E₃}(E) = 1 ⟹ **contradiction**.

**キーテクニック**: 
- **Thm 13.5 の iteration** (M* で apply) + **Lemma 12.1 の normalization**: E₃ ⊲ E, but Z(E₃) small.
- **Maximal family の uniqueness (Lemma 13.6)** を暗黙的に使用 (M* ∈ ℳ(N_G(R)) の selection).

**数学的インサイト**: 
- Lemma 13.7 は "prime action は 2 つ-coprime factors の product で preserve される" というabelian factorization 的な stability. これが §14 での "type P maximal の全体 family" の consistency を guarantee.

**形式化見積**: 200-250 行.

---

### Group III: 相互制約と Transition (補助 Lemma 13.8–13.10)

#### **Lemma 13.8** (L3630-3660) — Forbidden Configuration

**主張** (L3630-3636):
**不可能な configuration** の 5 条件:
1. M* ∈ ℳ, M* ≄ M
2. p ∈ τ₁(M) ∩ τ₁(M*), P ∈ ℰ_p¹(M ∩ M*)
3. Q, Q* = P-invariant Sylow subgroups (possibly distinct primes)
4. C_Q(P) = 1, C_{Q*}(P) = 1
5. N_G(Q) ⊆ M*, N_G(Q*) ⊆ M

⟹ **Contradiction** (no such config exists).

**数学的意味**:
- τ₁ element P が 2 つの異なる Sylow に対して "regular に作用" すれば，その両者の normalizers が定義上異なるmaximal に belong → contradiction.
- **Maximal の一意性の deeper incarnation**: Proposition 12.15 等での σ disjointness に続く強化版.

**証明** (L3638-3660, 23 行):
- Assume config exists. By (3)-(5), Q = nonidentity Sylow of M for prime q ∉ α(M).
- M = N_M(Q)M_α (Frattini + Thm 10.2 hierarchy).
- Lemma 12.18 ⟹ C_{M_β}(P) ≠ 1, C_{M_β}(PQ) = 1, etc.
- Hall construction (H = Hall β(M) ∪ β(M*) subgroup of C_G(P)) and Prop 10.14(d)
  (`S10.normalizer_le_of_nontrivial_beta_subgroup`) ⟹ M = M^g ⊇ H.
- Then r ∈ β(M*) ∩ π(H) ⟹ R ⊆ N_M(Q), so R ⊆ N_G(Q) ⊆ M*.
- Thm 13.4 ⟹ C_{M_σ}(P) ⊆ C_{M_σ}(R), but then [X, Q] = 1 for X ∈ C_{M_σ}(P).
- **最終矛盾**: [X, Q] ⊆ M_α by careful subgroup analysis, but X ⊆ C_{M_α}(PQ) = 1 (Lemma 12.18) ⟹ contradiction.

**形式化見積**: 150-200 行.

---

#### **Theorem 13.9** (L3662-3670) — σ Disjointness for non-conjugate Maximal

**主張**:
- M* ∈ ℳ, M* ≄ M ⟹ σ(M) ∩ σ(M*) = ∅

**簡潔性**: これは **Corollary 12.6(f)** の再確認; §12 で既に established.

**証明**: Lemma 13.6 (maximal uniqueness) + Lemma 13.8 (forbidden config) を合成. Assume q ∈ σ(M) ∩ σ(M*). Thm 13.5 で E₁ prime ⟹ C_S(P) = 1 (where S = E-inv Sylow q of M_σ). Lemma 13.1(a) ⟹ p ∈ τ₁(M*). Then Lemma 13.8 (Q = Q* = S) ⟹ contradiction.

**役割**: Corollary 12.6(f) のprime action 視点からの confirmation. §14–§15 への transfer continuity.

**形式化見積**: 80-100 行.

---

#### **Theorem 13.10** (L3672-3695) — E₁ Action on E₃

**主張**:
- Some P ∈ ℰ_p¹(E₁) does not centralize E₃ ⟹
  1. (a) E₁ does not act regularly on E₃ (contrapositive of regularity).
  2. (b) C_{M_σ}(E₃) = 1 (unless other cases).
  3. (c) ∃ P ⊆ E₁, C_{M_σ}(P) ≠ 1, C_{M_σ}(PQ) = 1 for Sylow Q of E₃.

**数学的意味**:
- E₁ が E₃ に作用するときの "regularity vs. centraization" tradeoff.
- (a) → Lemma 13.7 の条件を satisfy → E₁E₃ prime.
- (c) → Lemma 13.6 の maximal uniqueness via Lemma 12.18.

**証明** (L3674-3695, 22 行):
- P acts regularly on Sylow Q of E₃ (by non-centralization assumption) ⟹ Q = [Q, P] ⊆ E'.
- Take M* ∈ ℳ(N_G(Q)). Lemma 12.2(b) ⟹ M* ≄ M.
- Lemma 12.18 ⟹ C_{M_α}(P) ≠ 1, C_{M_α}(PQ) = 1 ⟹ (c).
- (a) follows from non-regularity. (b): If C_{M_σ}(E₃) ≠ 1, then by (c) and Lemma 13.6, M(C_G(Q*)) ≠ {M}; Prop 10.14(d) handles the `q*∈β(M)` branch, while the other branch is the definition of σ(M). This contradiction gives (b).

**形式化見積**: 100-120 行.

---

#### **Corollary 13.11** (L3696-3698) — E₃ Action Summary

**主張**:
- E₃ ≠ 1, E₃ does not act regularly on M_σ ⟹
  1. (a) τ₂(M) = ∅
  2. (b) τ₁(M) ≠ ∅, τ₃(M) ≠ ∅
  3. (c) E₁E₃ prime on M_σ
  4. (d) E₁ centralizes E₃

**役割**: Theorem 13.10 + Lemma 13.7 のcorollary. §14 への "type P maximal" の setup.

**形式化見積**: 50-70 行.

---

## Prime Action の Thompson 背景

### Thompson 1966 "Nonsolvable Finite Groups" との接続

Thompson のこの論文は **p-局所群の derived series に基づく action theory** を開発. その中核は:

- **p-element への作用が，derived series階層で層別化される**.
- **Prime action**: 単一素数 p での制限的作用 (Thompson の"standard form").
- **Counting arguments**: prime action の family に基づく global constraints.

§13 は **solvable G における Thompson 風作用** の local realization:
- E₁, E₃ (cyclic, coprime) の prime action.
- Lemma 13.4 (τ₁-element の centralizer制御) = Thompson fixed-point idea の local version.
- Lemma 13.7 (simultaneous action) = Thompson の "prime action は products で preserve" の再現.

### Feit-Thompson 本文での位置づけ

§13 は **BG 内では standalone** だが，**Feit-Thompson Theorem の "final steps"** に属する:
- §14 (Type P Counting) は prime action family の cardinality を count.
- §15 (M_F Structure) は prime action に基づく maximal subgroup factorization.
- App.C (Final Contradiction) は global contradiction を prime action inconsistency から derive.

---

## §12 からの継承と explicit dependency

### §12 結果の direct quotations

| §13 Lemma/Thm | 引用 §12 結果 | 役割 |
|---|---|---|
| Lemma 13.1 (a) | Cor 12.16(a) | p ∉ τ₂(M*) の保証 |
| Cor 13.2 | Lemma 13.1, Lemma 12.2(a) | τ-specialization |
| Cor 13.3 | Lemma 12.1(d) | E₁, E₃ cyclicity |
| Thm 13.4 | Lemma 12.18(a), Prop 12.15 | τ₁-centralizer control |
| Lemma 13.6 | Thm 12.5(d), Cor 12.6(a), Lemma 12.17, Thm 13.4 | maximal uniqueness |
| Lemma 13.7 | Thm 13.5, Cor 13.3(b), Lemma 12.1(d), Cor 12.6(d) | E₁E₃ simultaneous |
| Lemma 13.8 | Lemma 12.18, Prop 10.14(d), Thm 13.4 | forbidden config |
| Thm 13.9 | Cor 12.6(f), Lemma 13.6, Lemma 13.8 | σ disjointness |
| Thm 13.10, Cor 13.11 | Lemma 12.2(b), Lemma 12.18, Lemma 13.6, Lemma 13.7 | E₁E₃ interaction |

**計**: §13 全 7 結果中，**13 spots** で §12 を引用. §12 の 19 結果のうち，**8–9 個** が §13 で essential.

### §10 β/σ-prime gate audit (2026-06-02)

**Direct §13 gates**:
- `S10.normalizer_le_of_nontrivial_beta_subgroup` = Prop 10.14(d). Used explicitly in
  Lemma 13.8 and Theorem 13.10 where β-subgroup normalizers must be forced back into the
  corresponding maximal subgroup.
- `S10.disjoint_of_not_conj` = Lemma 10.12. Used in Lemma 13.8 for the final
  `M_α ∩ M*_α = 1` contradiction.
- `S10.isHall_Msigma_Malpha` = Theorem 10.2 surface. Lemma 13.8 still needs the deferred
  quotient nilpotence tail `M'/M_α` from the original theorem; do not replace that by a
  new §13 hypothesis.

**§12-mediated §10 gates now visible in Lean**:
- `S10.beta_complement_normalizer_derived_contains_sylow` = Cor 10.9(a)(3). This is the
  derived-normalizer Sylow containment needed for β-complement Frattini/fusion steps.
- `S10.beta_factorization_of_sylow_normalizer_in_intersection` = Cor 10.9(b). This feeds
  the §12 maximal-interaction branch used before Theorem 13.4 / Lemma 13.8.
- `S10.sigma_complement_commutator_cyclic_normal` = Prop 10.11(d). This is used earlier
  in the §11/§12 exceptional and τ₂ machinery consumed by §13; keep it as an upstream
  proof gate rather than a field of `SubgroupESetup`.

---

## 形式化の dependency graph

```
§10 (M_α, M_σ)
  ↓
§11 (Exceptional, Hypothesis 11.1)
  ↓
§12 (Subgroup E)
  │ ├─ Lemma 12.1 (E structure)
  │ ├─ Thm 12.5 (τ₂ nilpotency)
  │ ├─ Cor 12.6 (A normality in E)
  │ ├─ Thm 12.7 (nonabelian Sylow)
  │ ├─ Cor 12.10 (summary)
  │ ├─ Lemma 12.18 (τ₁ & M_α)
  │ └─ Lemma 12.17, 12.19 (embedding)
  ↓
★ §13 (Prime Action) ← THIS SECTION
  ├─ Lemma 13.1–13.3 (초등적)
  ├─ Thm 13.4–13.5 (Thompson-style)
  ├─ Lemma 13.6–13.7 (extended)
  └─ Lemma 13.8–13.10 (transition)
  ↓
§14 (Type P Counting)
  │ ├─ Prop 14.2: uses Thm 13.5, Thm 13.9
  │ └─ Thm 14.3–14.6: uses Cor 13.3, Lemma 13.6
  ↓
§15 (M_F Structure)
  │ └─ Thm 15.2: uses Lemma 13.6, Thm 13.9
  ↓
App.C (Final Contradiction)
```

---

## §14–§15 への橋渡し役割

### §14 (Type P Counting) への interface

**Proposition 14.2** (mmd 추정 L3745~):
- τ₂(M) ≠ ∅ (exceptional prime p) に対して，M_σ nilpotent (Thm 12.5(a)) + E₁ prime (Thm 13.5) ⟹ prime action family에 based한 maximal counting.

**Theorem 14.3–14.6**:
- Cor 13.3 (E₃ prime), Lemma 13.6 (maximal uniqueness) ⟹ family の full cardinality.

### §15 (M_F Structure) への connection

**Theorem 15.2**:
- Lemma 13.6 + Thm 13.9 (σ disjointness) ⟹ M_F의 maximal family over M_σ.

---

## mathlib カバレッジ

| 概念 | mathlib status | 新規実装 | 引用箇所 |
|------|---|---|---|
| Prime action (정의) | ✗ (새로운 개념) | O | 전체 |
| Derived series, cyclic p-groups | ◐ | § 12 참조 | Cor 13.3, Thm 13.4 |
| Coprime action with normalization | ◐ (basic) | ● (A-invariant) | Lemma 13.6–13.7 |
| Sylow transfer, Focal subgroup | ◐ | ● (§10 via Lemma 13.6) | Lemma 13.6, 13.8 |
| Frattini argument | ◐ | ● (§1 Prop 1.6) | Lemma 13.1 proof |
| Maximal subgroup uniqueness (𝒰) | ◐ (§9) | ● | Lemma 13.6, 13.8, 13.9 |

**新規 정의**:
- `PrimeAction M_σ X` (X acts prime on M_σ)
- `RegularAction M_σ X` (X acts regularly)
- Helper lemmas for cyclic Sylow / E₁, E₂, E₃ interactions.

---

## Phase 2a 형식화 計画

### 예상 일정

**§13 단독** (in parallel with §12 completion):
- Week 1: Lemma 13.1–13.3, Thm 13.5 (elementary, 150 행)
- Week 2: Thm 13.4 (main, 250 행, proof intricate)
- Week 3: Lemma 13.6–13.7 (extended analysis, 250 행)
- Week 4: Lemma 13.8–13.10, Thm 13.9 (transition, 150 행)

**합계**: 3-4 주 (1 person), **800–1100 행 Lean 예상**.

### Dependency 체크리스트

- [ ] §10 (M_α, M_σ, Thm 10.2, Lemma 10.8–10.12) ✓
- [ ] §11 (Hypothesis 11.1, Thm 11.3, 11.5, 11.7) ✓
- [ ] §12 (Lemma 12.1, Thm 12.5, Cor 12.6, Lemma 12.18) ✓
- [ ] Prop 1.5 (A-invariant Hall), Prop 1.6(d) (Frattini + coprime)
- [ ] Thm 12.13 (nonabelian Sylow uniqueness)
- [ ] Prop 12.15 (σ(M) case analysis in other maximal)
- [ ] Lemma 12.17 (C_{M_σ}(E) structure)
- [ ] Thm 9.6 (Uniqueness Theorem for 𝒰)

---

## 미해결 / TODO

### 수학적 정정사항

1. **Theorem 13.4 의 symmetry**: τ₁(M) 내 P와 다른 소수 R 간의 asymmetry. 만약 R도 τ₁이면 대칭적인가? (현재 정리 statement는 r ∈ π(E) 일반적, 하지만 τ₁에 제한되지 않음.) 이 generality가 §14 counting에 필수인지 확인 필요.

2. **Lemma 13.7 의 "non-regular" 가정**: "E₁ does not act regularly on E₃" ⟺ ∃ P ∈ ℰ_p¹(E₁), R ∈ ℰ_r¹(E₃) with C_R(P) ≠ 1. 역방향도 성립하는가? (현재 정리는 forward only로 보임.)

3. **Lemma 13.8 의 completeness**: 5 조건 (1)–(5)에서 (1)–(4)만 주면 (5)는 derived되는가? 아니면 (5)는 독립적 가정인가? mmd L3633-3636 의 원문 다시 읽기.

4. **Cor 13.11 (c) "E₁E₃ prime"**: Lemma 13.7의 contrapositive인가? 아니면 별도의 statement인가? Corollary와 Lemma의 statement 정확성 차이 재확인.

### 형식화 시 주의사항

1. **τ notation의 Lean 표현**: τ₁(M), τ₂(M), τ₃(M)을 record type vs. function vs. set으로 정의할지. Lean 4에서의 관례에 맞게.

2. **Prime action의 unfolding**: 정의 1 (centralizer equality) vs. 정의 2 (elementary part)의 equivalence를 early lemma로 증명.

3. **Proof automation**: Lemma 13.1, 13.2 의 Frattini+rank 계산은 어느 정도 `omega`, `decide` 등으로 자동화 가능한가.

4. **LTE reference**: Lean Feit-Thompson project의 "local analysis" 부분 (수학적으로 비슷한 부분이 있을 수 있음)과 notation 일치성 확인.

---

## 참고문헌 (섹션 내부)

- **Lemma 12.1**: E의 기본 구조 (cyclic E₁, E₃; nilpotent E')
- **Theorem 12.5**: τ₂ 경우의 M_σ nilpotency
- **Corollary 12.6**: τ₂ 시 A ⊲ E, C_G(A) ⊆ E
- **Lemma 12.18**: τ₁ & M_α interaction
- **Theorem 12.13**: Nonabelian p-subgroup의 uniqueness
- **Proposition 12.15**: σ(M)의 다른 maximal에서의 작용
- **Corollary 12.10**: τ-summary
- **Theorem 13.4**: 핵심 Thompson-style 정리 (τ₁ centralizer control)
- **Lemma 13.6**: Maximal family uniqueness
- **Lemma 13.7**: E₁E₃ simultaneous prime action

---

## 현재 상태 (2026-05-22)

**형식화 준비 상태**: Ready for Phase 2a 제 4 파 (§12 complete 후)

**전제 완성**:
- ✓ §1–§9 foundational theory
- ✓ §10 (M_α, M_σ)
- ✓ §11 (Exceptional)
- ✓ §12 (Subgroup E) — currently completing
- ⏳ §13 (Prime Action) — **PENDING**
- ⏳ §14–§15 (Counting & M_F)

**주요 insight 정리됨**:
1. Prime action = 단일 소수 p에 대한 제한적 작용 (정의 embedded in mmd L3486-3492)
2. Theorem 13.4 = 핵심, Thompson 방식의 derived series 제어
3. Lemma 13.6–13.7 = "prime action은 family 전체에서 consistent" 확인
4. Transition (13.8–13.10) = §14 으로의 smoothing

---

## 완성 예상

**형식화 착수**: §12 완성 직후 (est. Week 4 of Phase 2a)  
**형식화 기간**: 3–4 주 (1 person, ~1000 행 Lean)  
**병렬화 가능**: §14–§15 와 partially parallel (§13 early results 후)  
**§14–§15 시작**: Lemma 13.6, Thm 13.5 완성 후

---

*작성: 2026-05-22*  
*출처: BG local-analysis.mmd L3484–3739 (256 행), PDF pp.97-104*  
*참고: §12 부분군 E, §14 Type 𝒫 Counting, §15 M_F Structure, App.C Final Contradiction*  
*Peterfalvi 1984 "Non-solvable finite groups" (Thompson 작용론 기반)*
