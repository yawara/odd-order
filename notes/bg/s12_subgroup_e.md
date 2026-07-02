# BG §12: 部分群 E — 大規模節の形式化ロードマップ

> ✅ **§12 COMPLETE (2026-07-02)** — Prop 12.15 d.2/e.2 も landed
> (`S12_*.lean` 全ファイル実 sorry 0)。以下のセッション記録は履歴。

## 🟢🟢 2026-06-13 (Lane F session 20, Opus 4.8): **Prop 12.15 = 9/11 — E⊇S infra COMPLETE + e.3b landed; 残 d.2/e.2**

session 19 の E⊇S gap を **infra で解消**し e.3b 着地。**build 緑、実 sorry = d.2 / e.2 の 2 個**(9/11)。

**新規 infra (S12_Proposition1215 内, sorry-free)**:
- `subgroupESetup_of_complement (hM)(hE_le)(hcompl_inf)(hcompl_sup) : ∃E₁E₂E₃, SubgroupESetup M E …`
  — `exists_subgroupESetup` の Hall-pieces 組立を「与えられた補群 E」でパラメタ化(複製)。
- `exists_subgroupESetup_with_le (hM)(hAM:A≤M)(hA_pi:A は σ(M)'-群) : ∃E…, setup ∧ A≤E`
  — `Ch03.hall_D` で σ'-Hall H⊇A.subgroupOf M 取得 → 補群 props(hcompl_inf=coprime,
  hcompl_sup=`|H|=N.index` を σ/σ' index-part の coprime + dvd-antisymm で)→ `subgroupESetup_of_complement`。
  ⚠ 教訓: **一般群の部分群束は modular でない**(`IsModularLattice (Subgroup C)` は **CommGroup 限定**)
  → Dedekind は **正規部分群版を手で**(M_σ⊴ 経由, S12_Corollary126 と同型)。helper 2 (`pRank_eq_of_mulEquiv`
  / `exists_mem_elemAbelianOfRank_two_le_of_two_le_pRank`) も追加。S10 `normalizer_sylow_map_le_of_mem_sigma` de-private 済。
- **e.3b** (`M*_σ⊔(M∩M*)=M*`): A∈ℰ²(S) に with_le で E*⊇A → E*≤N_G(A)⊆M (12.6(a)`elemAb_normal_in_E_of_tau2`.1.1
  + 12.10(d)) → M∩M*=E* (正規 Dedekind + hMsM) → `E_compl_sup`。e.3a/hMsM/setup は refine 前に hoist 済。

**残 2 (各 BG sub-argument が不明瞭・要精読)**:
- **e.2** (`π(M)∩σ(M*)⊆β(M*)`): Cor 10.9(a)(1) (`beta_complement_centralizes`, S10_BetaRadical:241) の対偶で
  Fact1「A は Syl_r(M*_σ) 非中心化」⟹ r>q は **clear**。だが Fact2「no Syl_r(M) centralizes Syl_q(M_σ)」⟹ q>r
  が "C_G(A) `r'`-group" からどう出るか不明瞭(in-file コメントに詳細)。
- **d.2** (`τ₁(M*)⊆τ₁(M)∪α(M)`): factorization M=(M∩M*)M_α / M*=(M∩M*)M*_α は有(h109_M/h109_star)。
  τ₁=`{r∉σ ∧ r∉π(M') ∧ pRank=1}`。`r∉σ(M)` の sub-step が defs から非自明(session 19 参照)。
▶ 次: e.2 Fact2 / d.2 r∉σ(M) の BG 精読。WIP 未 commit(S10 de-private + S12_E relocation + 新 leaf)。

## 🟢🚧 2026-06-13 (Lane F session 19, Opus 4.8): **Prop 12.15 = 8/11 parts COMPLETE; e.2/e.3b に E⊇S 構造 gap**

session 18 から進展: **(d.1)(d.3a)(d.3b)(e.3a) 追加 landed** (計 8/11: a,b,c,e.1,d.1,d.3a,d.3b,e.3a)。
build 緑、実 sorry = **d.2 / e.2 / e.3b の 3 個**。leaf WIP 未 commit (root/AxiomsCheck 未配線 — 完成まで)。

**新 landed の手法**:
- (d.1/d.3a/d.3b): `S` を `Sylow q G` term 化 (`S.subgroupOf Mstar`→`exists_le_sylow`→`isSylow_sylowMap_of_mem_sigma`→(c) で同定) → Cor 10.9(b) (`beta_factorization_of_sylow_normalizer_in_intersection`) ×2 + `Malpha_ne_bot_of_sylow_normalizer_le` 再利用 + `simp [Malpha,Mbeta,hab]` bridge。
- (e.3a): A∈ℰ²(S) を構成 (`S`を`Sylow q ↥M*`化[(c) maximality]→`pRank_sylow_eq`+`tau2_pRank_eq_two`で pRank=2→新 helper `exists_mem_elemAbelianOfRank_two_le_of_two_le_pRank`) → `Msigma_nilpotent_of_tau2` conjunct-5 (N=M∈ℳ(A))。新 helper 2 個 + S10 `normalizer_sylow_map_le_of_mem_sigma` **de-private**。

**🚧 e.2/e.3b の BLOCKER (要判断)**: Cor 12.6(a)(b) (`elemAb_normal_in_E_of_tau2`/`centralizer_le_E_of_tau2`)
は全て **`A ≤ E`** (E = setup の M*_σ-補群) を要求。だが e.2/e.3b の A は **`A ≤ M` も同時に**要る
(`N_G(A)⊆M` を Cor 12.10(d)+`q∈σ(M)` で出すため)。`exists_subgroupESetup` は **`E ⊇ S` を保証せず**、
A を E に conj 押込 (S12_Lemma1211:370 idiom, `w∈M*`) すると `A ≤ M` が壊れる。
⟹ **新 infra 必要**: `SubgroupESetup M* E …` with `E ⊇ S` (param. setup 構成、または setup の
conj-stability + 補群の Hall 共役性)。~50-100 行の sub-project。**12.16 は 12.15(e) 依存ゆえ最終的に要**。
**推奨**: (i) まず d.2 (τ₁ transfer、E-setup 非依存・独立) を landing → 9/11; (ii) その後 E⊇S infra を
別 leaf で形式化 → e.2/e.3b。または user に「E⊇S infra を作る価値があるか / 既知 shortcut あるか」確認。

## 🟢 2026-06-13 (Lane F session 18, Opus 4.8): **Prop 12.15 実装中 — (a)(b)(c)(e.1) COMPLETE, (d)/(e.2-3) 残**

新 leaf `S12_Proposition1215.lean` (downstream, S12_E より下流; S12_E の 12.15 は削除済 = 移動)。
**build 緑, 実 sorry = (d) + (e.2) + (e.3a) + (e.3b) の 4 個** (a/b/c/e.1 landed)。
WIP 未 commit (12.15 完成時に S10 de-private + S12_E relocation と束ねて 1 commit)。

**landed**:
- (a) `not_conj_of_mem_sigma_of_normalizer_le` (Lemma 12.2(b)) 一発。
- (b) N_G(S)⊆M: noncyclic = Cor 12.10(d) (`exists_subgroupESetup hG hM` → `nilpotent_sigmaComplement_abelian` `.2.2.2.1`); cyclic = X char S (新 helper `cyclic_subgroup_eq_of_card_eq` [S10_BetaRadicalGlobal から複製] + `AppB.normalizer_le_normalizer_map_of_characteristic`) で N_G(S)⊆N_G(X)⊆M*、+ T=Syl_q(M)⊇S → p-group normalizer 条件 (新 helper `eq_of_isPGroup_of_normalizer_inf_eq` = `normalizerCondition_of_isNilpotent`+`subgroupOf_normalizer_eq`+`inf_subgroupOf_left`) で S=T → **de-private した `S10.normalizer_sylow_map_le_of_mem_sigma`** で N_G(S)⊆M。
- (c): (b) と同じ helper `eq_of_isPGroup_of_normalizer_inf_eq` 再利用。
- (e.1) q∈τ₂(M*): `prime_mem_sigma_or_tau2` (12.2a) `.resolve_left hqns`。

**残 (d)/(e.2-3) construction path (pin 済)**:
- **(d) q∈σ(M*)** [L3443-51]: 要 `S : Sylow q G`。MY S = Syl_q(M∩M*)=Syl_q(M*); q∈σ(M*) ⟹ image=Syl_q(G) (`isSylow_sylowMap_of_mem_sigma` S10_HallStructureCore:1213; `S.subgroupOf Mstar`→`Sylow q ↥M*` を (c) maximality で)。N_G(S)⊆M⊓M* (b + q∈σ(M*)⟹⊆M*) → `Malpha_ne_bot_of_sylow_normalizer_le` (S12_Theorem1213 再利用)=d.3b、`beta_factorization_of_sylow_normalizer_in_intersection` (10.9b) ×2 = d.1 + d.3a (`simp only [S10.Malpha,S10.Mbeta,hab]`)。d.2 (τ₁ transfer) は別。
- **(e.2/e.3)** [L3429-41]: `exists_subgroupESetup hG hMstar` で E*、A∈ℰ²(S)、Thm 12.5(e)+Cor 12.6(a) (M*_σ∩M=1・A⊴E*)、Cor 12.10(d) (E*⊆N_G(A)⊆M ⟹ M∩M*=E*=e.3)、Cor 10.9(a) (p>q∧q>p 矛盾=e.2)。
- ⚠ **cross-lane flag 健在**: 12.16×2 を S13 (Lane G) が cite ⟹ 12.16 着地時 S13 re-point 要。12.15 完成後に判断を仰ぐ。

## ✅✅✅✅ 2026-06-13 (Lane F session 17, Opus 4.8): **Thm 12.13 完全 COMPLETE — sorry-free・axiom-clean (σ-side keystone 確定)**

**piece 5 (`maximalContaining_normalizer_center_ne_of_two_maximals`) 内の唯一の sorry
= `hK : C_{M_α}(Z)⊆M⋆` の per-generator 12.4(a) ステップを充足 → 12.13 全体が sorry-free に。**
commit `5e9087f3`。`#print axioms nonabelian_pgroup_isUniquelyMaximal`
= `[propext, Classical.choice, Quot.sound]` (sorryAx 無し)。AxiomsCheck 登録済 (assert 2→3)。
leaf 914 行 (<1500)。full build 緑 + assert 通過。

**A-frame (cocyclic 閉包還元) の generator core の決着手順** (session 16 の skeleton を完成):
- 生成元 g (∀y∈Y, φ y g=g, (Q/Z)/Y cyclic) に対し `A_Y := (Y.comap mk').map Q.subtype`
  (Y の ↥Q 内 preimage, Z≤A_Y)。`↑g ∈ C_G(A_Y)`: 各 x∈A_Y を `mk' yb` 経由で取り
  `hfix` を `mk'_apply→lift_mk'` で展開、`hψ_coe`+`mul_inv_eq_iff_eq_mul` で ↑g·x=x·↑g。
- `Y≠⊥` (else Q/Z cyclic 矛盾, **`isCyclic_iff_exists_zpowers_eq_top.mpr ⟨a,hYa⟩`**):
  `Nontrivial ↥Y` (`nontrivial_iff_ne_bot`) + `exists_ne (1:↥Y)` で a'∈A_Y∖Z を抽出。
- `A := ⟨a'⟩⊔Z ∈ ℰ²(Q)` (再利用 helper **`zpowers_sup_center_mem_elemAbelianOfRank_two`**
  = card 議論を共有化), `A≤Q≤M⋆`, `↑g∈C_G(A_Y)≤C_G(A)` ⟹ 12.4(a)
  `centralizer_le_of_elemAb_rank_two` で ↑g∈M⋆。
- **API 地雷**: `lift` 展開は `mk'_apply` を先に (`mk' yb`≠`mk yb` syntactically);
  `exists_mem_ne_one_of_ne_bot` は mathlib に無い→`nontrivial_iff_ne_bot`+`exists_ne`;
  `zpowers a=⊤⟹IsCyclic` は `rw` でなく `isCyclic_iff_exists_zpowers_eq_top.mpr`。

**§12 残 sorry = 5 (全て S12_E、12.13 経路外)**: 12.14 (`maximalContaining_centralizer_eq_singleton`) /
12.16(a) ×2 (`sigma_subgroup_conj_into_Msigma` + `sigma_subgroup_pRank_normalizer_le_one`) /
12.16(b) (`sigma_subgroup_not_mem_primeFactors_derived_of_tau1`) / 12.15
(`sigma_subgroup_maximal_interaction`)。**12.15/12.16 は §13-14 gate (Lane G が scaffold 引用)**。
▶ 次 = 12.14 or 12.15/12.16 (優先度高: G unconditional 化に直結)。BG mmd L3369-3479 recon 要。

## 🔎 2026-06-13 (Lane F session 17 cont., Opus 4.8): **12.15→12.16 recon — placement 確定 + ⚠ cross-lane flag**

12.13 完了後、Lane-G gate (12.15/12.16) の着手 recon。**結論: 12.15 から (12.16 は 12.15 依存)。**

### 🧩 import DAG の事実 (placement 決定打)
- **S13_Lemma131 が cite する S12_E sorry = ちょうど 2 個**: `sigma_subgroup_pRank_normalizer_le_one`
  (12.16(a) pt2) + `sigma_subgroup_not_mem_primeFactors_derived_of_tau1` (12.16(b))。
  `maximalContaining_centralizer_eq_singleton` (12.14) / `sigma_subgroup_conj_into_Msigma`
  (12.16a pt1) / `sigma_subgroup_maximal_interaction` (12.15) は **どこからも未使用**。
- **dep-leaves (S12_Theorem125 / Corollary126 / Corollary1210 / ExceptionalBridge) はすべて
  S12_E より DOWNSTREAM**: 連鎖 `S12_ExceptionalBridge → S12_Lemma1218 → S12_E`。
  ⟹ 12.15/12.16 (12.5(e)/12.6/12.10(d)/12.2(b) を要する) は **S12_E 内 in-place 証明不可**。
  **downstream leaf 必須** (12.13 と同型)。S12_E は「base + forward-decl(sorry)」ファイル。

### ⚠⚠ CROSS-LANE FLAG (要ユーザー/hub 判断 — 12.16 着地時に顕在化)
S12_E の sorry'd 12.16×2 は S13 (Lane G) が cite。downstream leaf で証明 → S12_E から **削除** →
S13 の import を leaf に **re-point** が必要 (同名・同 namespace だが S13 は S12_E しか import せず、
leaf は S12_E より downstream ゆえ S12_E 経由で透過解決できない)。これは **Lane G の S13 編集**。
plan のデフォルト「S12_E の sorry を in-place 証明で discharge → G 自動 unconditional」は **本ケースで
破綻** (downstream dep)。**選択肢**: (1) F が downstream leaf で証明 + S13 import を直接編集
(1 行追加・低衝突), (2) F は証明のみ + hub が merge 時に S13 re-point + S12_E 削除,
(3) leaf を distinct 名で証明し S12_E/S13 不変 (G は条件付きのまま; 後で hub が名前 swap)。
→ **12.15 はこの判断と独立に必要** (12.16 の前提) ゆえ先行。12.16 着地前にユーザー裁可を仰ぐ。

### ▶ 12.15 (`sigma_subgroup_maximal_interaction`) 実装プラン
- **新 leaf `S12_Proposition1215.lean`** (downstream; import = S12_Theorem125 / S12_Corollary126 /
  S12_Corollary1210 / S12_ExceptionalBridge — これらが S12_ECore+S10 を推移取込)。
  statement = S12_E:469-488 と **byte-identical** (将来の swap 用)。証明後 S12_E の 12.15 を削除
  (未使用ゆえ clean)。root `OddOrder.lean` + AxiomsCheck 両 import 必須。
- **証明構造 (BG mmd L3417-3451 精読済)**, 5 結論:
  - **(b) N_G(S)⊆M**: T=Syl_q(M)⊇S。S 非巡回 ⟹ Cor 12.10(d) で N_G(S)⊆M。
    S 巡回 ⟹ N_G(S)⊆N_G(X)⊆M*、S⊆N_T(S)⊆M∩M*、S=N_T(S)⟹S=T、q∈σ(M) で N_G(S)⊆M。
  - **(a) M* 非共役**: Lemma 12.2(b) = `not_conj_of_mem_sigma_of_normalizer_le` (S12_ExceptionalBridge:238)。
  - **(c)**: (b) から (S は M∩M* の Sylow q かつ N_G(S)⊆M ⟹ M* の Sylow q)。
  - **(e) q∉σ(M*)**: Lemma 12.2(a) `prime_mem_sigma_or_tau2` (S12_ECore) で q∈σ(M*)∪τ₂(M*)、
    N_G(S)⊄M* ⟹ q∈τ₂(M*)。A∈ℰ²(S), E*=M*_σ の補群⊇A。Thm 12.5(e)+Cor 12.6(a): M*_σ∩M=1, A◁E*。
    Cor 12.10(d): E*⊆N_G(A)⊆M ⟹ M∩M*=E* (補群)。π(M)∩σ(M*)⊆β(M*): p∈π(M)∩σ(M*)−β(M*) と仮定 →
    C_G(A)⊆E* (Cor 12.6(b)) は p'-group → A は M*_σ の Syl_p を中心化せず → Cor 10.9(a) で p>q∧q>p 矛盾。
  - **(d) q∈σ(M*)**: N_G(S)⊆M*、S は G の Sylow q。Cor 10.9(b)
    (`beta_factorization_of_sylow_normalizer_in_intersection`, S10_BetaRadical:697):
    M=(M∩M*)M_α, α(M)=β(M)、M* も同様 ⟹ M_α,M*_α≠1。τ₁(M*)⊆τ₁(M)∪α(M):
    r∈τ₁(M*), R=Syl_r(M∩M*) は M*=(M∩M*)M*_α の Sylow r で normal complement を持つ ⟹ r∉α(M) なら M も同様。
- **dep 名 (確定分)**: 12.2b=`not_conj_of_mem_sigma_of_normalizer_le`+`not_conj_symm`,
  12.2a=`prime_mem_sigma_or_tau2`(ECore), 12.1g=ECore:487, 10.9b=
  `beta_factorization_of_sylow_normalizer_in_intersection`(S10_BetaRadical:697)。
  **次 iter で pin 要**: 12.10(d) 非巡回 N_G(S)⊆M の正確名 (S12_Corollary1210), 12.5(e), 12.6(a)(b)(f), 10.9(a)。

## ✅✅✅ 2026-06-13 (Lane F session 16, Opus 4.8): **Thm 12.13 主定理 wire COMPLETE — piece 5 のみ残**

**`nonabelian_pgroup_isUniquelyMaximal` (12.13 本体) を全 ingredient から組立完了** (S12_Theorem1213, 660 行)。
主定理は sorry-free に assemble され、唯一の sorry = piece-5 sub-lemma
`maximalContaining_normalizer_center_ne_of_two_maximals` (`ℳ(N_G(Z))≠{M}`) のみ
(`#print axioms nonabelian_pgroup_isUniquelyMaximal` = propext/sorryAx/choice/Quot ⟹ sorry 依存は piece-5 経由のみ)。
**全 logical wiring 検証済 = 12 ingredient が正しく合成することを確認**。leaf 実 sorry=1 (piece-5 本体)。

**12.13 ingredient (全 axiom-clean, sessions 15-16, 12 commits)**:
reduction (`exists_expPExtraspecial_le_of_two_maximals`: P→Sylow G→r≤2→Q extraspecial, S・rank 露出) /
`Malpha_ne_bot_of_sylow_normalizer_le` (M_α≠1, Cor10.9b) / `notMem_alpha_of_rank_sylow_le_two` (p∉α) /
`exists_elemAbelianOfRank_two_le_of_expPExtraspecial` (A∈ℰ²(Q)) /
`center_map_le_of_mem_elemAbelianOfRank_two_le_expPExtraspecial` (Z≤A) /
`exists_line_maximalContaining_eq_of_Malpha_ne_bot` (12.4b 対偶) /
`exists_conj_smul_zpowers_eq_of_expPExtraspecial`(型) + `..._le`(G-element) + `exists_conj_smul_eq_of_lines_of_expPExtraspecial`(G-subgroup) (line-共役 3 段) /
`eq_of_conj_of_maximalContaining_normalizer_eq_singleton` (ℳ-矛盾エンジン)。

**残 = piece 5 内の唯一 sorry = `hK : C_{M_α}(Z)⊆M⋆`** (A の cocyclic core; C+B は実証済)。
C (ℳ-矛盾) + B (Lem6.5b: N_M(Z)⊆M⋆ from hK; ↥M 内 normalizer_eq_centralizerK_mul_normalizerU +
Cor10.9b で hKU + p∉α で coprime) は **DONE** (commit d4cf9fc5 / f7f1d384)。

### ▶ A = hK (C_{M_α}(Z)⊆M⋆) 実装レシピ (cocyclic quotient-action, ~120 行 all-or-nothing, 最難)
template = `S12_ExceptionalBridge.le_of_forall_line_inf_centralizer_le` (769-851; 部分群 A 版・
**quotient でないので直接流用不可**: rank-1 line で Y=Z 問題。Q/Z の line のみ A_Y rank-2 で 12.4a 可)。
- K := centralizer Z ⊓ M_α。**(1) Q≤N_G(K)**: Q normalize Z (Z=Z(Q) の像) ⟹ normalize centralizer Z;
  Q≤M, M_α⊴M ⟹ normalize M_α ⟹ K。**(2) Z centralize K** (K=C_{M_α}(Z) は定義上 Z 中心化)。
- **φ 構成**: `act : MulDistribMulAction ↥Q ↥K := MulDistribMulAction.compHom (M:=↥(N_G K)) ↥K (inclusion hQK)`;
  `ψ := MulDistribMulAction.toMulAut ↥Q ↥K : ↥Q→*MulAut↥K`; `center↥Q ≤ ψ.ker` ((2) より z conj 自明);
  `φ := QuotientGroup.lift (center↥Q) ψ hker : (↥Q⧸center↥Q)→*MulAut↥K`。
- coprime `|Q/Z|=p²` vs `p∤|K|` (K≤M_α, p∉α 済); noncyclic Q/Z ((ℤ/p)², extraspecial commutator=center)。
  ⟹ `cocyclicFixedByClosure φ = ⊤` (Prop 1.16)。
- `closure_le` で各 generator g (∀y∈Y, φ y g=g, (Q/Z)/Y cyclic) → ↑g が preimage A_Y (= Y の ↥Q 内 preimage
  を map; Z≤A_Y) を中心化 → **A_Y∈ℰ²(Q)** (Y line ⟹ |A_Y|=p²; Y=⊤ ⟹ A_Y=Q⊇rank2) → 12.4a
  (`centralizer_le_of_elemAb_rank_two` を M⋆ に) で ↑g∈M⋆ ⟹ K⊆M⋆。
- **✅ template + API 確定 (session 17 study)**: φ-construction template = **`S10_LocalCriteria:161-209`**
  (`MulDistribMulAction.compHom (M:=↥(N_G(Malpha M))) ↥(Malpha M) (inclusion hX_norm_Ma)` +
  `toMulAut` + `hφ_coe`/`hφ_inv_coe`; X が M_α に conj 作用)。これを K=C_{M_α}(Z) 版に + `QuotientGroup.lift`。
  cocyclic template = **`le_of_forall_line_inf_centralizer_le:785-846`** (closure_le + 各 line case)。
  確定 API: `le_normalizer_map_subtype_of_normal` (Q≤N_G(Z) from center↥Q normal),
  `le_normalizer_opiCoreInG (alpha M) M` (M≤N_G(M_α)), `centralizer_conj_smul` +
  `mem_normalizer_of_conj_smul_eq_self` + `Subgroup.smul_inf` (hQK idiom = S12_Corollary1210:309-312),
  `QuotientGroup.lift N φ HN`, `commGroupOfCyclicCenterQuotient`/`cyclic_center_quotient_of_card_eq_prime_sq`
  (PGroup.lean:358-371; Q/Z noncyclic via Q nonabelian), `Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl`
  (coprime, S10_LocalCriteria:158)。**A-frame は ~80 行 all-or-(1-sorry): clean prefix は commit 不可
  (全中間結果が最終 sorry に feed) ゆえ generator→M⋆ (12.4a) のみ sorry 化した full A-frame を一括で書く。**
- **incremental commit 可**: φ+cocyclic+closure-reduction を frame とし generator→M⋆ (12.4a 部) を sorry 化
  → net sorry=1 維持で A-frame 先行 commit、その後 generator core。
**crux = quotient-action φ 構成 + line↔rank-2 A_Y 対応。multi-iteration 見込み。**

## 🟢 2026-06-13 (Lane F session 15, Opus 4.8): **Thm 12.13 hard-core 着手 — 還元補題・extraspecial 共役・ℳ-矛盾エンジン**

Thm 12.13 `nonabelian_pgroup_isUniquelyMaximal` (leaf `S12_Theorem1213.lean`) の hard core は
背理法 + 非共役矛盾。これまでに landed (build 緑・axiom-clean):
- `mem_sigma_normalizer_le_of_two_maximals` (還元: Cor 12.10(a)(d) → `p∈σ(M)` ∧ `N_G(P)≤M`)。
- `exists_conj_eq_center_mul_of_expPExtraspecial` (共役の半分: a₀∉Z, z∈Z ⟹ ∃q, q a₀ q⁻¹ = z·a₀。
  φ:q↦⁅q,a₀⁆ が Z への全射準同型)。
- **NEW** `eq_of_conj_of_maximalContaining_normalizer_eq_singleton` (**ℳ-矛盾エンジン** = 最終矛盾の後半):
  `A₀⋆ = g•A₀` (g∈M), `ℳ(N_G(A₀))={M}`, `ℳ(N_G(A₀⋆))={M⋆}` ⟹ `M=M⋆`。
  共役は `N_G(·)` と可換 (`normalizer_conj_smul`)・coatom 保存 (`isCoatom_conj_smul`)・g∈M で M 固定
  (`conj_smul_eq_self_of_mem_normalizer`)。すべて既存 helper (S12_ExceptionalBridge / S12_Corollary129 /
  AInvariantPiSubgroups) で組める ⟹ 新 import 不要。

### ▶ 12.13 hard core 残り decomposition (この順, BG mmd L3379–3397 精読済)

**証明骨格** (背理法 `P` が distinct maximal `M,M⋆` に): WLOG `P` = Sylow p of `M∩M⋆` (⟹ Sylow p of G);
Uniqueness で `r(P)=2`; Cor 10.7(b) `sylow_structure` で extraspecial `Q⊆P` (|Q|=p³, exp p),
`Z=Z(Q)=Q'` 位数 p; Q/Z が `K=C_{M_α}(Z)` に作用, Prop 1.16 + Prop 12.4(a) で `K⊆M⋆`;
Cor 10.9(b) `M=(M∩M⋆)M_α` + Lem 6.5(b) で `N_M(Z)⊆M⋆`, よって `ℳ(N_G(Z))≠{M}` ∧ `M_α≠1`
(M_α=1 なら M=M∩M⋆⟹M⊆M⋆⟹M=M⋆ 矛盾)。最後に 12.4(b) **対偶** (M_α≠1) を M, M⋆ 両方に適用し
`A₀,A₀⋆∈ℰ¹(A)−{Z}` (`ℳ(N_G(A₀))={M}`, `ℳ(N_G(A₀⋆))={M⋆}`) を取る。`A₀,A₀⋆` は Q 内非中心 line で
**Q-共役** ⟹ エンジンで `M=M⋆` 矛盾。

**残ピース (leaf に追加予定)**:
1. ~~**line-共役** `exists_conj_smul_zpowers_eq_of_expPExtraspecial`~~ **✅ DONE (session 15)** —
   type-level, sorry-free・axiom-clean。`b∈⟨a⟩⊔Z`(`mem_sup_of_normal_right` で `b=aⁱ·z`)⟹
   `∃q, q•⟨a⟩=⟨b⟩`。ZMod p 体で `j:=i⁻¹.val`, center 位数 p で `z^p=1`, `exists_conj_eq_center_mul`
   を `z^j∈Z` に適用→`(z^j a)ⁱ=z·aⁱ=b∈q•⟨a⟩`→両辺位数 p で等号。
   **デバッグ知見** (再利用): `Nat.card (φ•H)` は `(φ•H : Subgroup Q)` 型注釈必須 (Nat.card が Type 期待で
   `•` が誤 elaborate); `Subgroup.equivMapOfInjective` は `≃*` ゆえ `Nat.card_congr` には `.toEquiv`;
   `Subgroup.eq_of_le_of_card_ge` (not `_le`; `[Finite K]` (hle:H≤K) (Nat.card K≤Nat.card H):H=K);
   `Commute z a` は `(mem_center_iff.mp hz a).symm` を中間 `have` に (Eq 経由 dot は `Eq.zpow_left` 解決失敗);
   `zpow_mem hz j` (root, K 暗黙; `Subgroup.zpow_mem` は引数順違い)。
2. ~~**還元チェーン**~~ **✅ DONE (session 15)** — 2 補題で landed (sorry-free・axiom-clean):
   - `exists_sylow_eq_map_of_normalizer_le` (R-a): `Sylow p of K (≤G)` で `N_G(P̄)≤K` ⟹ `P̄` は G の Sylow p。
     S10.isSylow_sylowMap_of_mem_sigma の非 σ 一般化 (同証明; private `lt_inf_normalizer_of_lt_of_isPGroup`
     を leaf に複製)。
   - `exists_expPExtraspecial_le_of_two_maximals` (還元本体): 非可換 P が distinct max M≠M⋆ に
     ⟹ `∃Q≤M∩M⋆, IsExpPExtraspecial p Q ∧ |Q|=p³`。P を M∩M⋆ の Sylow に拡大→R-a で G-Sylow→
     **r(S)≤2** (by_contra r≥3 ⟹ `Ch2.S09.uniquenessTheorem hG hSlt (by omega) (Or.inl ⟨3≤r⟩)` で
     IsUniquelyMaximal S, `huniq.2.unique` で M=M⋆ 矛盾) → S 非可換で `S10.sylow_structure …2.1 hrank2`
     の abelian 枝を排し extraspecial Q。
   **🔑 flagged gap 解消**: Uniqueness の hr3 は「P Sylow rank2」でなく **by_contra (r≥3) 分岐内で Or.inl** で供給
   (BG「Uniqueness で r(P)≤2」は対偶。`uniquenessTheorem` 署名はそのまま使える)。
3. ~~**M_α≠1**~~ **✅ DONE (session 15)** `Malpha_ne_bot_of_sylow_normalizer_le`: Sylow p of G で
   `N_G(S)≤M∩M⋆` ⟹ M_α≠1。Cor 10.9(b) = `S10.beta_factorization_of_sylow_normalizer_in_intersection`
   (`M=(M⋆∩M)⊔M_β ∧ α=β`) で M_α=M_β; M_β=⊥ なら M=M∩M⋆≤M⋆=M⋆ 矛盾。
4. ~~**coprimality `p∉α(M)`**~~ **✅ DONE (session 15)** `notMem_alpha_of_rank_sylow_le_two`:
   `rank(S)≤2` ⟹ `p∉α(M)` (∵ `pRank_p(M)≤pRank_p(G)=pRank_p(S)≤rank(S)≤2<3`)。
   ⟹ `p∉β(M)` ⟹ `p∤|M_α|` (Lem 6.5(b) の coprime)。**coprimality gap 解消**。
5. **🔶 残 hard piece = K⊆M⋆**: K=C_{M_α}(Z)。Prop 1.16 (`cocyclicFixedByClosure_eq_top_of_not_isCyclic`,
   Q/Z noncyclic rank2 が K に coprime 作用 [coprime は p∉α で OK]) で K=⟨C_K(Ā)|Ā∈ℰ¹(Q/Z)⟩、
   各 `C_K(A/Z)=C_K(A)⊆M⋆` を 12.4(a) (`centralizer_le_of_elemAb_rank_two` を M⋆ に, A∈ℰ²(Q)⊆ℰ²_p(M⋆))。
   ⟹ K⊆M⋆。次に Lem 6.5(b) (`normalizer_eq_centralizerK_mul_normalizerU`, M=(M∩M⋆)⊔M_α, M_α⊴M,
   Z≤M∩M⋆, coprime) で `N_M(Z)=C_{M_α}(Z)·N_{M∩M⋆}(Z)⊆M⋆` ⟹ **ℳ(N_G(Z))≠{M}** (∵ N_M(Z)⊆M⋆≠M)。
   **⚠ 最難所**: Prop 1.16 の `cocyclicFixedByClosure` を K=C_{M_α}(Z) 上の Q/Z 作用に instantiate +
   `C_K(A/Z)=C_K(A)` (Z 中心化ゆえ quotient fixed = ambient fixed) + ℰ¹(Q/Z)↔ℰ²(Q) の対応。
6. **12.4(b) 対偶 ✅ DONE (session 15)** `exists_line_maximalContaining_eq_of_Malpha_ne_bot`:
   A∈ℰ²(M), A≤M, M_α≠⊥ ⟹ ∃A₀∈ℰ¹(A), A₀≤A, ℳ(N_G(A₀))={M} (push_neg + 12.4(b))。
   組立: A₀≠Z は ℳ(N_G(Z))≠{M} (piece 5) から。M⋆ 側も同様 → line-共役 + engine で M=M⋆ 矛盾。

**⚠ 注意点 (session 15 末)**: ✅ piece 2 (reduction)・3 (M_α≠1)・4 (coprimality)・6前半 (12.4b 対偶);
✅ back-end (line-conj+engine)。**残 hard = piece 5 (K⊆M⋆)** + 主定理組立。
- **piece 5 = K⊆M⋆ assessment (最難所, multi-iter 見込み)**: `le_centralizer_of_forall_line` (12.4b の
  Prop 1.16 engine) は **「W≤C(A) (centralizer)」結論で 12.13 の「K≤M⋆ (maximal 包含)」には流用不可**。
  raw `cocyclicFixedByClosure_eq_top_of_not_isCyclic` を **A':=Q/Z (=↥Q⧸Z), G':=↥K** で instantiate 要:
  (1) **作用 `φ:(↥Q⧸Z) →* MulAut ↥K` の構成 = crux** (Q は K=C_{M_α}(Z) を正規化 [Q≤M, M_α⊴M, Z normalize];
  Z は K を中心化ゆえ作用は Q/Z を経由)。(2) coprime (`p∤|K|`, p∉α 済) + noncyclic (Q/Z≅(ℤ/p)²)。
  (3) `cocyclicFixedByClosure=⊤` ⟹ K=⟨C_K(Y)|Y≤Q/Z,(Q/Z)/Y cyclic⟩。(4) 各 `C_K(Y)⊆C_G(A_Y)⊆M⋆`
  (A_Y=Y の Q 内 preimage ∈ℰ²(Q), 12.4(a)=`centralizer_le_of_elemAb_rank_two` を M⋆ に; Y=Q/Z は
  C_K(Q)⊆C_K(line))。⟹ K⊆M⋆ → Lem 6.5(b) で N_M(Z)⊆M⋆ → ℳ(N_G(Z))≠{M}。**(1) の quotient-action
  MonoidHom 構成が型重く 1-2 iter。**
- **主定理組立 (piece 5 後 or piece5-sorry で先行可)**: 
  - ✅ **richer reduction DONE (session 15)**: `exists_expPExtraspecial_le_of_two_maximals` を拡張し
    `∃ (S:Sylow p G)(Q), N_G(S)≤M∩M⋆ ∧ rank(S)≤2 ∧ Q≤M∩M⋆ ∧ IsExpPExtraspecial p Q ∧ |Q|=p³` を返す
    (Malpha_ne_bot/notMem_alpha に S・rank2 を供給可)。
  - ✅ **A∈ℰ²(Q) 存在 DONE (session 15)** `exists_elemAbelianOfRank_two_le_of_expPExtraspecial`:
    **🔑訂正: `A∈elemAbelianOfRank G p 2` は `IsElementaryAbelian p A ∧ |A|=p²` のみ (maximality 不要!)**
    (`IsMaximalElementaryAbelian` は別物=`ℰ*`/idealPrime 用)。`mem_elemAbelianOfRank.mpr ⟨elem, card⟩`。
    Q 非可換⟹非cyclic⟹`exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic` (Ch1.S04, odd 要) で
    p²-elem-ab E≤↥Q→`E.map Q.subtype`。**pRank≤2 不要だった** (over-engineering 撤回)。
  - **残: Z(Q)≤A** (assembly の line-共役で `a₀*∈⟨a₀⟩⊔Z`⟹`A=⟨a₀⟩⊔Z` に要)。
    self-centralizing 経由: `|Q|=p³`, `|A|=p²` ⟹ `C_Q(A)` (=centralizer A⊓Q) の位数∈{p²,p³};
    =p³ なら C_Q(A)=Q⟹A≤Z(Q) (|A|≤p 矛盾)⟹=p²=|A|⟹C_Q(A)=A⟹Z(Q)⊆C_Q(A)=A。~20 行・次 iter。
  - **line-共役の ↥Q↔G transport**: A₀,A₀⋆ (12.4b より ∈ℰ¹(A), ≤A≤Q) を ↥Q 内の zpowers に持ち上げ
    `exists_conj_smul_zpowers_eq_of_expPExtraspecial` 適用→ q∈↥Q→ G で conj、engine へ。
  推奨: 次 iter で A∈ℰ²(Q) 構成 → piece5 を sorry'd sub-lemma 化 → 主定理を完全 wire (net sorry 0 維持)
  で合成検証 + piece5 隔離、その後 piece5 本体。

## ✅✅✅ 2026-06-13 (Lane F session 14, Opus 4.8): **Thm 12.12 COMPLETE — sorry-free・axiom-clean**

**BG Theorem 12.12 (Frobenius 因子分解) を完全形式化**(`frobenius_factorization_of_regular`,
S12_Theorem1212c, 全 capstone axiom-clean)。3 ケース (τ₂=∅ / 非可換 Sylow / 可換 Sylow) 全実証。
新 leaf `S12_Theorem1212c.lean` (9 theorem, sorry-free) の構成 (commits 0e0ca590→5fe05044):

1. **3-case glue** `frobenius_factorization_of_regular` (0e0ca590): selector = 「|E| を割る τ₂-素数で
   非可換 Sylow をもつか」。Case 1 (`frobFact_of_regular_all` + hregAll 導出), Case 2
   (`frobFact_of_nonabelianSylow`) 即決。素数性は `primeFactors` ケース分けで無料。
2. **per-prime Z_p** `exists_regular_cyclic_of_mem_tau2` (6d2f3845): wiring。
3. **part (a)** `frobFact_partA_of_abelianSylow` + 汎用 `isPiSubgroup_le_of_normal_isHall` (f5728ec9):
   A₀=E₂ + `C_E(x)⊆E₂`。
4. **piece B 直積** `card_finsetSup_eq_prod` + `mem_Z_of_orderOf_prime_mem` + `le_normalizer_finsetSup`
   (a89342ad): 「⨆Z_p の素数位数 r 元 ∈ Z_r」。
5. **τ₂-積バンドル** `exists_tau2_product` (e6ebf144): ZZ=∏Z_p [≤E, ≠⊥, E≤N, IsPiGroup τ₂, 全域 regular,
   τ₂-exp realize]。`choose!` で族構成。
6. **Case 3 最終 glue** `frobFact_of_abelianSylow` (5fe05044): K=Hall τ₂'(`hall_E_exists`),
   E₀=ZZ⊔K, regularity (τ₂→a∈ZZ via E₀/ZZ τ₂' quotient; τ₁∪τ₃→hreg), exp (τ₂→ZZ exp-元;
   τ₂'→K⊇Sylow_r exp-元), Frobenius (`isFrobeniusGroup_of_regular`)。

**§12 残 sorry = 6** (全て S12_E, 12.12 経路外): 12.13 `nonabelian_pgroup_isUniquelyMaximal` /
12.14 `maximalContaining_centralizer_eq_singleton` / 12.15 `sigma_subgroup_maximal_interaction` /
12.16(a) `sigma_subgroup_conj_into_Msigma` + `sigma_subgroup_pRank_normalizer_le_one`[issue 0065 deferred] /
12.16(b) `sigma_subgroup_not_mem_primeFactors_derived_of_tau1`[issue 0065 deferred]。
**次 = 12.13/12.14/12.15/12.16(a)pt1 の独立 hard 定理群** (issue 0065 の 12.16 ×2 は proof-deferred scaffold)。
12.15/12.16 は §13-14 gate (Lane G 引用中)。再利用知見: `Subgroup.orderOf_coe` は `orderOf ↑x` 形のみ rw 可
→ 直接 `H.orderOf_dvd_natCard hx`; `Finset.induction with | empty | insert` の empty 失敗は insert を
誤吞 (case 消失に注意); 集合 normalizer の bot は `mem_normalizer_fintype`。

## 🟢 2026-06-13 (Lane F session 13, Opus 4.8): **Thm 12.12 三ケース組立 — Case 1/2 完了・Case 3 隔離**

新 leaf `S12_Theorem1212c.lean` を切り、`frobenius_factorization_of_regular` (12.12 本体) を
**S12_E scaffold から移植・3 ケースに分解して証明**。`frobenius_factorization_of_regular` の結論型は
`FrobFactConclusion M E` (= S12_E の inline 連言と defeq)。ケース選択子 = 「`|E|` を割る `τ₂`-素数で
**非可換 Sylow** をもつものが存在するか」(`by_cases hnonab : ∃ p ∈ (Nat.card ↥E).primeFactors, p ∈ τ₂ ∧ ∃ S:Sylow p G, ¬可換`):

- **Case 2** (非可換 Sylow): `frobFact_of_nonabelianSylow` (既存) に直結。**完了**。
- **Case 1** (`τ₂ ∩ π(E) = ∅`): `frobFact_of_regular_all` (既存) に `hregAll` を供給。導出 =
  `e∈E#` の各素因数 `r ∈ primeFactors(ord e) ⊆ π(E)` を `mem_tau_union_of_mem_primeFactors` で
  `τ₁∪τ₂∪τ₃` に入れ、`r∉τ₂` (Case 1 仮定) から `τ₁∪τ₃` を結論。`E≠⊥` は `h.E_ne_bot hG`。**完了**。
- **Case 3** (可換 Sylow, `τ₂≠∅`): 新 sorried `frobFact_of_abelianSylow` に隔離 (= **残務**)。

**🔑 素数性の自動化**: ケース分けを「`p ∈ (Nat.card ↥E).primeFactors`」で行うことで `Nat.prime_of_mem_primeFactors`
が `Fact p.Prime` を無料供給 (τ₂-素数は `p∉σ⟹p∤|M_σ|` + `pRank=2⟹p∣|M|` で必ず `|E|` を割る)。
**🔑 `orderOf e ∣ |E|`** = `E.orderOf_dvd_natCard heE` (subtype 不要)。

S12_E:475 の sorried `frobenius_factorization_of_regular` は除去 → pointer comment。net 0 sorry
(S12_E 7→6 real + 新 leaf +1)。full build 3795 緑・AxiomsCheck OK。

### ▶ 残務: `frobFact_of_abelianSylow` (S12_Theorem1212c.lean:51, τ₂-集約)

`A₀ = E₂` (Lemma 12.8(a): abelian normal Hall τ₂); `E₀ = E₁E₃·∏_{p∈τ₂}Z_p`。各 `p∈τ₂`:
`A_p∈ℰ²_p(E)` (`exists_elemAb_rank_two_le_E_of_tau2`) → `S_p:=A_p` を含む Sylow p of G → **可換 (habel)**
→ Lemma 12.8(c) 鎖 `S ⊆ N_G(S)' ⊆ F(E) ⊆ C_G(S) ⊆ E` で **`S_p ≤ E` (hSM 自動)** →
per-prime capstone `exists_cyclic_Enormal_regular_of_abelianSylow` で **`Z_p ≤ S_p ≤ E`** cyclic,
`E ≤ N_G(Z_p)`, `exp(Z_p)=exp(S_p)`, regular。
- **exp(E₀)=exp(E)**: `exponent_eq_of_forall_factorization_le` (S12_Theorem1212:90) で素数別に realize
  (`exists_factorization_le_at_prime`/`factorization_exponent_le_of_sylow` を流用; r∈τ₁→E₁, r∈τ₃→E₃,
  r∈τ₂→Z_r)。
- **E₀ regular**: `inf_centralizer_eq_bot_of_forall_prime_order` (S12_Theorem1212b:1215) で prime-order に還元。
  order `r∈τ₁∪τ₃` → `hreg` 直接; **order `r∈τ₂` → `a∈Z_r`** が要 (⚠ **未解決の核心**: `E₀∩(Sylow_r)=Z_r`
  すなわち `E₁⊔E₃` が `τ₂'` であることが要る。Schur-Zassenhaus 補群 / E₂⊴E の Hall 構造で詰める)。
- **τ₂ 上の有限 product**: `T := (Nat.card ↥E).primeFactors.filter (·∈τ₂ M)` 上の `Finset.sup` + per-p
  選択 (Classical.choose)。`Z_p ≤ E₂` (τ₂-Hall) ゆえ ∏ は E₂ 内 abelian 直積。

## 🟢 2026-06-12 (Lane F session 12, Opus 4.8): **Thm 12.12 Case 3 per-prime Z-construction COMPLETE**

Case 3 の per-prime Z-construction を**両枝とも完全実装**(front-half `353c9d9d`, agemo
`bda45cbe`, C_E(S)=E `debde8a5`, 統合 `0cc8d6de`)。capstone =
**`exists_cyclic_Enormal_regular_of_abelianSylow`** (S12_Theorem1212b.lean): abelianSylow regime +
正則仮定 ⟹ ∃ cyclic Z≤S, exp(Z)=exp(S), E≤N_G(Z), regular。C_E(S)=E で場合分け統合。
全 axiom-clean、full build 3775。**Case 3 の数学的核心が完結。**

### ▶ 残り = τ₂ 集約 → frobFact_of_abelianSylow → 3-case (12.12 完成まで)
- **frobFact_of_abelianSylow**: A₀=E₂ で (a)。(b) E₀=E₁⊔E₃⊔(⊔_{p∈τ₂}Z_p)。各 p∈τ₂ で
  A_p∈ℰ_p²(E)(Cor 12.6(a))+S_p abelian(Thm 12.7(a))から
  `exists_cyclic_Enormal_regular_of_abelianSylow`。exp(E₀)=exp(E)。
  M_σE₀ Frobenius = `isFrobeniusGroup_of_regular`(既存)に E₀ regular を渡す。
  **E₀ regular の鍵 = 「prime-order 元 FPF ⟹ 全非単位元 FPF」**(a∈E₀#, prime power a^m で
  C_{M_σ}(a)⊆C_{M_σ}(a^m); r∈τ₂ なら Z_r 共役[M_σ⊴M], r∈τ₁∪τ₃ なら hreg)。
  **⚠ Frobenius-complement 理論 ~150 行 = 最難 wiring。**
- **3-case**(frobenius_factorization_of_regular scaffold S12_E:438): τ₂=∅→Case1;
  else ∃nonab Syl→Case2 / else→frobFact_of_abelianSylow。

### ▶ 残 sorry (§12 完遂): 12.12(上記)/ 12.13 / 12.14 / 12.16(a)(b)。独立 hard 定理群。

## 🟢 2026-06-12 (Lane F session 10, Opus 4.8): **Thm 12.12 Case 3 front-half — 開問 c (r_q=2) 解決**

front-half (C_E(S)≠E 枝, X 存在) の **真のボトルネック「Lemma 12.11(c) yields r_q(N_G(S))=2」
(session 9 で開問 c=未解決) を完全解決・コミット** (commit `443dd824`)。全 unconditional・
axiom-clean、AxiomsCheck 4 本、full build 3775。新規 4 結果は `S12_Theorem1212b.lean`:

- **`pRank_normalizer_eq_two_of_index_card`** (開問 c, 核心): abelianSylow regime で
  `q ∈ π[E:C_E(A)]` (hqi) かつ `q ∈ π|C_E(A)|` (hqc) ⟹ **`pRank(N_G(S)) q = 2`**。
  **🔑 鍵の発見**: 12.11(c) (`tau2_transfer_to_maximal …2.2 q hqi hqc`) は `q∈τ₂(M*)` ∧
  `∃P:Sylow p G, M*≤N_G(P)` を与える (M*∈ℳ(N_G(A)))。session 9 が詰まった「M* の
  abelian Syl_q が N_G(S) 内に来る根拠」は **不要**だった。正しい論法 = **S=P ⟹ M*=N_G(S)**:
  `S ≤ N_G(S) =(12.8(d)) N_G(A) ≤ M* ≤ N_G(P)` で S,P 両 Sylow p ⟹ `sylow_eq_of_le_normalizer`
  で S=P ⟹ M*≤N_G(S)、N_G(S)≤M* と合わせ M*=N_G(S) ⟹ `pRank(N_G(S))q = pRank M* q = 2`
  (`tau2_pRank_eq_two`)。「abelian Syl_q」条項は rank には不要 (τ₂ 定義が pRank=2 を直接供給)。
- **`sylow_eq_of_le_normalizer`** (汎用): S≤N_G(P), 両 Sylow p ⟹ S=P (P は N_G(P) の正規=
  一意 Sylow, `Sylow.unique_of_normal`+`Subgroup.normal_in_normalizer`+subtype/subgroupOf 往復)。
- **`centralizer_le_of_omega1_le_centralizer`** (BG Prop 1.6(e)): abelian p-群 S で coprime Q が
  Ω₁(S) 中心化 ⟹ S 全体中心化 (`fitting_coprime_abelian_decomp`、[S,Q]≠1 の order-p 元 ∈
  Ω₁⊆C_S(Q) が C_S(Q)⊓[S,Q]=⊥ に矛盾)。対偶で開問 b の Q₁⊄C_E(A) を出す。
- **`prime_dvd_index_of_sylow_not_le_of_normal`** (汎用): H⊴K で Sylow q P⊄H ⟹ q∣[K:H]
  (P の K⧸H 像が非自明 q-群)。開問 b の hqi 供給 (C_E(A)⊴E が normality を供給, Cor 12.10(c))。

### ▶ front-half 残り (= 次セッション、precise plan)

**(1) 開問 b = setup lemma** (hqi/hqc + q∈τ₁ + Q₁ cyclic + C_S(Q₁)⊊S を供給):
- `A = Ω₁(S)` = `(omega1_eq_of_tau2 hG h.mem_maximal hp hA (hAE.trans h.E_le) S.isPGroup' hAS
  hSM (sylow_maximal_in_M_of_le hSM)).1` → A=(Omega ↥S p 1).map S.subtype。
- **q 選択**: hCES (`C(S)⊓E≠E`) で `(C(S)⊓E).subgroupOf E ≠ ⊤` (subgroupOf_eq_top↔E≤C(S)⊓E↔
  E≤C(S)) → index≠1 → `Nat.exists_prime_and_dvd` で q + `Q₁':Sylow q ↥E`、
  `sylow_not_le_of_prime_dvd_index Q₁' (q∣index)` ⟹ Q₁'⊄(C(S)⊓E).subgroupOf E ⟹
  Q₁:=Q₁'.map E.subtype ⊄ C(S) ⟹ **C_S(Q₁)⊊S** (¬(S≤C(Q₁)))。
- **q≠p**: q=p なら Q₁=Syl_p(E)=S (|E|_p=|G|_p ∵ p∉σ, S⊆E)、C_S(S)=S 矛盾。
- **hqi**: C_S(Q₁)⊊S =¬(S≤C(Q₁)) →(Prop1.6(e)対偶)¬(A≤C(Q₁)) →(`le_centralizer_swap`)
  ¬(Q₁≤C(A)) ⟹ ¬(Q₁'≤(E⊓C(A)).subgroupOf E) ⟹ (C_E(A)⊴E via Cor12.10(c)第2連言
  `E≤N((E⊓C(A)))` → `prime_dvd_index_of_sylow_not_le_of_normal`) q∣((E⊓C(A)).subgroupOf E).index
  → hqi。
- **q∈τ₁(M)**: `(nilpotent_sigmaComplement_abelian hG h).2.2.1 p _ hp A hA hAE).2.2 q hqi`。
- **Q₁ cyclic**: q∈τ₁ ⟹ pRank Q₁ q≤pRank M q=1 (`tau1_pRank_eq_one`+`pRank_le_of_injective`)
  → `S10.isCyclic_of_pRank_le_one`。
- **hqc** (🔑 Q₁ と decouple): 別 line `X':=Ω₁(Syl_q(E₁))` を使う (E₁=τ₁-Hall ⟹ q∈τ₁ で
  Syl_q(E₁)=Syl_q(E) cyclic、Ω₁ order q、X'≤E₁)。M_σ⊓C(X')=⊥ (X' は τ₁-元、hreg)。
  `central_line_of_abelianSylow X' ⟨q,_,hX'∈ℰ¹⟩ hX'≤E₁ hCX'` ⟹ E≤C(X') ⟹ X'≤E⊓C(A)=C_E(A)
  (X'≤E、A≤E≤C(X')⟹X'≤C(A)) ⟹ q=|X'|∣|C_E(A)| → hqc。

**(2) assembly** (`exists_partial_centralizer_of_abelianSylow`): 目標 = back-half consumer
`exists_invariant_cyclic_sameExponent_regular` が要する `∃X:Subgroup G, X≤N_G(S) ∧
Coprime(|S|,|X|) ∧ S⊓C(X)≠⊥ ∧ S⊓C(X)≠S`。
- **型設計**: Q:=`(Q':Sylow q ↥(N_G(S))).map subtype : Subgroup G` (⊇Q₁ を選ぶ:
  Q₁'≤N_G(S) を `IsPGroup.exists_le_sylow` で ↥(N_G(S)) 内 Sylow に延長)。Q≤N_G(S),
  IsPGroup q ↥Q, `pRank ↥Q q = pRank ↥Q' q = pRank ↥(N_G(S)) q` (`pRank_sylow_eq` Q' + map-iso
  `pRank_le_of_injective` 両向き)。
- **by_contra** (¬goal): `push_neg` → ∀X≤N_G(S), ¬(Coprime∧S⊓C(X)≠⊥∧≠S)。x∈Q∖C_G(S) に
  X=⟨x⟩ 適用 (Coprime は q-群/p-群、S⊓C(⟨x⟩)=S⊓C({x})、≠S ∵ x∉C_G(S)) ⟹
  S⊓C({x})=⊥ ⟹ **regular** (φ̄ wrapper hfpf)。
- φ̄ `isCyclic_quotient_of_conjugation_fpf` ⟹ IsCyclic(↥Q⧸(conjActionHom hQN).ker)。
- step6 `pRank_le_one_of_cyclic_quotient` (Q:=↥Q, Q₀:=ker=`conjActionHom_ker`=C_G(S).subgroupOf Q,
  Q₁:=Q₁(Sylow q of E).subgroupOf Q [cyclic], Q₀<Q₁ ∵ C_Q(S)⊊Q₁ [Q₁⊄C_G(S) ∵ C_S(Q₁)⊊S])
  ⟹ pRank ↥Q q ≤ 1。
- rank=2 lemma `pRank_normalizer_eq_two_of_index_card` + pRank_sylow_eq ⟹ pRank ↥Q q = 2。矛盾。
- **⚠ 注意点**: Q₀=C_Q(S)⊊Q₁ の証明 (Q₁⊄C_G(S): C_S(Q₁)⊊S ⟹ ∃ 非中心化 ∴ Q₁⊄C_G(S));
  Q₁≤Q の subgroupOf 化; X (back-half へ) は by_contra で得る存在子。
- 完成後 → `frobFact_of_abelianSylow` で C_E(S)=E 枝 (generic rank-2 分解 S=Y×Z) と統合 →
  Z_p 集約 E₀=E₁E₃·∏Z_p → 3 ケース統合で S12_E scaffold `frobenius_factorization_of_regular`。

## 🟢 2026-06-12 (Lane F session 11, Opus 4.8): **Thm 12.12 Case 3 front-half COMPLETE + C_E(S)=E plan**

front-half (C_E(S)≠E 枝) を**完全実装・コミット** (`353c9d9d`): `exists_sylow_tau1_cyclic_notCentralizing`
(開問 b) + `exists_partial_centralizer_of_abelianSylow` (assembly)。これで C_E(S)≠E 枝が
back-half に X を供給し完結。AxiomsCheck 全登録、full build 3775。**残 = C_E(S)=E 枝 +
τ₂ 集約 + 3-case 統合**(全て 12.12 内)。

### ▶ C_E(S)=E 枝の **streamlined 構成** (Y×Z 分解を回避する recon 進展)

BG は S=Y×Z (rank-2 cyclic 分解) を使うが、**agemo ℧^{a-1}(S) 経由で Y×Z を回避できる**:
目標 = `∃ Z cyclic ≤S, exp(Z)=exp(S), E≤N_G(Z), ∀z∈Z#, M_σ⊓C(z)=⊥`。
- `Monoid.exists_orderOf_eq_exponent` で max-order s₀∈↥S (ord=exp(S)=p^a)。
- ℧ := (Agemo ↥S p (a-1)).map S.subtype。**agemo helpers landed** (`mem_agemo_iff_of_comm`:
  abelian で x∈℧⟺∃y,x=y^(p^n); `agemo_eq_range_powMonoidHom`)。℧⊆Ω₁(S)=A (∵(x^{p^{a-1}})^p=1)、
  ℧≠⊥ (s₀^{p^{a-1}}≠1)、℧ char in ↥S → N_G(S)-不変 (AppB.normalizer_le_normalizer_map_of_characteristic)。
- **good line L** (C_{M_σ}(L)=1) を ℧ 内に取る (dichotomy `rcases eq_or_lt (℧≤A)`):
  - ℧=A (rank 2, homocyclic): **12.5(f)** (`exists_distinct_conj_lines` 系, S12_Theorem125:202)
    で A₁⊆A=℧ good。
  - ℧⊊A: ℧ は line (proper nontrivial ≤ rank-2 elem-ab A) → char → 不変 → **key fact**
    (`inf_centralizer_line_eq_bot_of_invariant`) で C_{M_σ}(℧)=1。L=℧。
- gen w of L ⊆℧ → `mem_agemo_iff_of_comm` で w=s^{p^{a-1}} (↥S 内), ord(s)=p^a (s^{p^{a-1}}=w≠1)。
  Z=⟨↑s⟩。exp(Z)=ord(↑s)=p^a=exp(S)。Ω₁(Z)=⟨↑s^{p^{a-1}}⟩=⟨w⟩=L。
  regular: z∈Z# → Ω₁(Z)=L≤⟨z⟩ → C_{M_σ}(z)≤C_{M_σ}(L)=1。E≤N_G(Z): hCES (E≤C(S)) で E が ↑s 中心化。
- **要 sub-facts**: `IsPGroup⟹exp=p^a` (exp∣card=p^n, `Nat.dvd_prime_pow`); a≥1 (S≠⊥);
  rank-2 elem-ab の proper nontrivial 部分群 = line (order p); Ω₁(⟨s⟩)=⟨s^{ord/p}⟩。

### ▶ τ₂ 集約 (C_E(S)=E/≠E 統合後) → `frobFact_of_abelianSylow` → 3-case

各 p∈τ₂ で per-p Z_p (上記 2 枝統合 `exists_cyclic_Enormal_regular_of_abelianSylow`)。
E₀ = E₁⊔E₃⊔(⊔_{p∈τ₂} Z_p)。**集約は finite τ₂ 上の product** — exp(E₀)=exp(E) と
M_σE₀ Frobenius (各 Z_p regular ⟹ E₀ regular on M_σ; `isFrobeniusGroup_of_regular` 既存)。
A₀=E₂ で (a)。3-case (`frobenius_factorization_of_regular` scaffold S12_E:438):
τ₂=∅ → Case1 (`frobFact_of_regular_all`); nonab Syl → Case2 (`frobFact_of_nonabelianSylow`);
ab Syl → Case3 (`frobFact_of_abelianSylow`)。**いずれも S12_Theorem1212.lean に Case1/2 完成済**。

### ▶ 残 sorry (S12_E, §12 完遂に必要)

1. **12.12** `frobenius_factorization_of_regular` (上記 Case3 残で完成)。
2. **12.13** `nonabelian_pgroup_isUniquelyMaximal` (非可換 p-部分群 ∈ 𝒰)。
3. **12.14** `maximalContaining_centralizer_eq_singleton` (σ-case 一意性, Prop 12.4 経由)。
4. **12.16(a)** `sigma_subgroup_conj_into_Msigma`; **12.16(b)**。
これらは独立な hard 定理群 (各 ~100-300 行)。**§12 完遂は multi-session 規模**。

## 🟢 2026-06-12 (Lane F session 10, Opus 4.8): **Thm 12.12 Case 3 front-half — 開問 c (r_q=2) 解決**

新 leaf `S12_Theorem1212.lean` (~510 行)。Thm 12.12 (Frobenius 因子分解、大物) を 3 ケースに分解。
**Case 1 (τ₂=∅) + Case 2 (Sylow p 非可換) 完成**、共通インフラ + exponent 機構も完成。
**全 unconditional・axiom-clean、AxiomsCheck 10 本登録**。S12_E の 12.12 scaffold は**未充足のまま**
(`frobenius_factorization_of_regular` の assembly は Case 3 完成後 — 実 sorry 5 不変)。

### ✅✅ session 8 cont. (commit fd2ee0bd): **Case 2 (nonabelian Sylow) COMPLETE**

capstone `frobFact_of_nonabelianSylow` (axiom-clean)。12.7 サブ定理 (canonical line +
補群) を組み立て `FrobFactConclusion M E` を返す。新規部品 (全 public・再利用可):
- **`eq_sup_inf_of_le_normalizer`** (Dedekind): `E₀≤N(A₀)`, `A₀≤H≤A₀⊔E₀` ⟹ `H = A₀⊔(H⊓E₀)`。
  `Subgroup.coe_mul_of_left_le_normalizer_right` で集合積に落とし element-wise (card 不要)。
- **`inf_centralizer_bot_symm`** (bridge): `(∀x∈N#,K⊓C(x)=⊥) → (∀a∈K#,N⊓C(a)=⊥)`。
- **`factorization_exponent_le_of_sylow`** (fact A): Sylow p が exp の p-part を担う
  (max-p-order 元を `Sylow` 共役 `MulAction.exists_smul_eq` で E₂ へ移送、`Subgroup.orderOf_mk`)。
- **`exists_orderOf_eq_rpow_in_complement`** (r≠p): `IsComplement'.QuotientMulEquiv` で
  max-r-order 元を E₀ へ (核 `⟨g⟩⊓A₀.subgroupOf E=⊥` は `inf_eq_bot_of_coprime`、位数保存は
  `orderOf_map_dvd`+`ker_mk'`)。**set でなく `QuotientGroup.mk'` を明示** (set は rw で zeta 展開
  暴走 → motive 不正)。
- **`exists_factorization_le_at_prime`** (r=p): 可換 `E₂ = A₀ × C` (C=E₂⊓E₀) で
  `exp E₂ ∣ lcm(exp A₀,exp C)` (`Monoid.exponent_dvd` の ∀g 形 + `Commute.orderOf_mul_dvd_lcm`;
  **`MonoidHom.noncommCoprod` は import 外**ゆえ hom でなく直接)、`ν_p(exp A₀)≤1≤ν_p(exp C)`
  (C nontrivial p-群) + fact A で C≤E₀ の exp 元が p-part 実現。
- assembly: (a) `E⊓C(x)=A₀` = Dedekind + `E₀⊓C(x)=⊥` (`primeFactors_centralizer_le_tau1`
  12.7(e) + Cauchy + hreg)。(b) bridge → `isFrobeniusGroup_of_regular`。
- 地雷: `MulEquiv.orderOf_eq` 連鎖は rw でなく `.trans` (subgroupOf 依存型で motive 不正);
  `Fact.out` は複数 Fact 在で `(Fact.out : p.Prime)` 明示要; `orderOf_coe`/`orderOf_mk` は
  `Subgroup.` 名前空間; `exists_prime_orderOf_dvd_card'` (primed=Nat.card)。

### ✅ landed (この session)

1. **`FrobFactConclusion M E`** (def): 12.12 二部結論の共通ゴール。各ケース helper がこれを返し、
   assembly 時に scaffold へ defeq で流す設計。
2. **Prop 3.9 `isCyclic_of_coprime_fpf_pgroup_action`**: finite p-群 R (p odd) が nontrivial
   finite H に coprime FPF 作用 ⟹ IsCyclic R。非 cyclic なら elem-ab p² 部分群 B 経由で
   **Isaacs 6.21** (`S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'`) から
   ⟨C_H(b)⟩=⊤、FPF (`actionFixedBy φ a = ⊥`) で `nontrivialActionFixedByClosure_le_iff` → ⊥ と矛盾。
   **一発で通過**。Case 3 の Q/Q₀ ↷ S 適用で使う (作用の組み方 = recon v 未済)。
3. **`isFrobeniusGroup_of_regular`** (packaging, 全ケース共通): regular な E₀≤E (∀a∈E₀#,
   M_σ⊓C(a)=⊥) で E₀≠⊥ なら M_σ E₀ が kernel M_σ の Frobenius 群。M_σ⊴M⊇M_σE₀ で正規性
   (`Msigma_subgroupOf`+`normal_subgroupOf_iff_le_normalizer`)、M_σ⊓E₀=⊥ (setup)、M_σ≠⊥
   (`S10.Msigma_ne_bot` = Thm 10.2(e))、conj_frobenius は `subgroupOf_eq_bot↔Disjoint` +
   `mul_inv_eq_iff_eq_mul` で regularity に帰着。
4. **Case 1 `frobFact_of_regular_all`** (E=E₁E₃ = τ₂∅): regularity が E 全体に及ぶケース。
   A₀=⊥ (IsMulCommutative=`IsMulCommutative.of_comm (Subsingleton.elim)`、E≤N(⊥)=S07:2045 の
   `mem_normalizer_iff` パターン、(a)-conjunct は 1≠e∈E⊓C(x) が x∈M_σ⊓C(e)=⊥ を強制)、E₀=E
   (exponent rfl、packaging)。**`E≠⊥` を要求** (E=⊥ なら part (b) Frobenius は偽 — BG も非自明
   補群前提; faithful な追加仮定)。Cases 2/3 は τ₂≠∅⟹E₂≠⊥⟹E≠⊥ で自動。
5. **`exponent_eq_of_forall_factorization_le`** (汎用, Cases 2/3 共通): E₀≤E で ∀素数 r に
   ∃g₀∈E₀, v_r(exp E)≤v_r(ord g₀) なら exp(E₀)=exp(E)。exp(E₀)∣exp(E)=`exponent_dvd_of_monoidHom`、
   逆は `Nat.factorization_le_iff_dvd`+`Finsupp.le_def` で素数ごと。**鍵 mathlib 補題**=
   `Nat.Prime.exists_orderOf_eq_pow_factorization_exponent` (exp の r-part を達成する元の存在)。

### ▶ Case 2 (nonabelian Sylow p) — **完全戦略 recon 済**、未実装

discriminant: τ₂≠∅ で p∈τ₂ を固定、A∈ℰ_p²(E) を取り (`exists_elemAb_rank_two_le_E_of_tau2`?)、
`by_cases ∃ S:Sylow p G, ¬IsMulCommutative S`。nonabelian 枝 = Case 2。

**12.7 サブ定理の直接呼び出し** (assembly `tau2_singleton_of_nonabelianSylow` でなく):
- `tau2_prime_eq_of_nonabelianSylow` → `hprime_eq : ∀q prime, q∈τ₂ M→q=p` (12.7(a))。
- `exists_canonical_line_of_nonabelianSylow hG h hp hA hAE hnonab` →
  `A₀ = A⊓C(M_σ)`, `|A₀|=p`, `A₀≤A`, `M_σ≤C(A₀)`, line 条件 `hc` (∀X∈ℰ¹,X≤E,X≠A₀ →
  M_σ⊓C(X)=⊥ ∧ ¬C(X)≤M), `habs`。
- `fitting_eq_sup_of_canonical_line …` 第1連言 → `M ≤ N(A₀)` (= hMnorm)。
- `exists_complement_of_canonical_line hG h hp hA hAE hnonab hprime_eq hA₀A hA₀card hMσC hMnorm`
  → `∃E₀, E₀≤E ∧ A₀⊓E₀=⊥ ∧ A₀⊔E₀=E`。

**(a)-conjunct `E⊓C(x) ≤ A₀`** (x∈M_σ#): A₀≤C_E(x) (A₀≤E、M_σ≤C(A₀)⟹x∈M_σ⟹A₀≤C(x)) +
C_E(x)⊓E₀=⊥ (≤E₀⊓C(x)=⊥) + [E:E₀]=p (=|A₀|、A₀⊴E disjoint) ⟹ |C_E(x)| ∣ p ⟹ C_E(x)=A₀ (card)。
**要 helper**: 「H⊓K=⊥, A₀≤H, A₀⊴E, A₀⊔K=E ⟹ |H| ∣ p」or 直接 C_E(x)=A₀。

**(b) regularity**: (e) `primeFactors_centralizer_le_tau1_of_disjoint hG h hp hA hAE hprime_eq hc
hE₀E hA₀E₀ hx hx1` → π(C_{E₀}(x))⊆τ₁ ⟹ C_{E₀}(x)=⊥ (∃y order r∈τ₁⊆τ₁∪τ₃ → hreg → x∈M_σ⊓C(y)=⊥ ✗)
⟹ `∀x∈M_σ#, E₀⊓C(x)=⊥`。**要 bridge `inf_centralizer_symm`** (∀x∈M_σ#,E₀⊓C(x)=⊥) ⟺
(∀a∈E₀#,M_σ⊓C(a)=⊥) [comm 対称、~12 行] → packaging。

**(b) exponent `exp(E₀)=exp(E)`** = `exponent_eq_of_forall_factorization_le` の hattain を discharge:
- **r≠p** (🔑 **Sylow 共役を回避する clean path 発見**): max-r-order 元 g:↥E
  (`exists_orderOf_eq_pow_factorization_exponent`, ord g = r^k, k=v_r(exp E)) を **complement iso**
  `Subgroup.IsComplement'.QuotientMulEquiv [K.Normal] (h:H.IsComplement' K) : G⧸K ≃* H` で E₀ へ。
  K:=A₀.subgroupOf E (normal, A₀⊴E), H:=E₀.subgroupOf E (complement)。`mk g : ↥E⧸K` の位数 = r^k
  (核 A₀ は |A₀|=p で r と互いに素: g^{ord(mk g)}∈K ⟹ ord g ∣ ord(mk g)·p、coprime で r^k∣ord(mk g);
  逆は hom で ord(mk g)∣ord g)。iso で g₀:=e(mk g)∈↥E₀sub 同位数 → subgroupOfEquivOfLe で ↥E₀ の
  r^k 位数元。**Sylow 機構不要・複素 iso のみ** (~40 行)。
- **r=p**: E₂=Sylow p of E は abelian (`E2_isMulCommutative_of_prime_eq`)、|E₂|≥p² (r_p(M)=2)。
  Dedekind (A₀≤E₂): E₂=A₀⊔(E₂⊓E₀) disjoint ⟹ (abelian) E₂=A₀×(E₂⊓E₀)。|E₂⊓E₀|=|E₂|/p≥p ⟹
  C:=E₂⊓E₀ nontrivial p-群、exp(E₂)=lcm(p,exp C)=exp C (p∣exp C)。exp(E₂)=p^{v_p(exp E)}
  (E₂=Sylow p ⟹ p-part 一致)。abelian C は `Monoid.exists_orderOf_eq_exponent` で
  ord=exp C=p^{v_p(exp E)} の g₀∈E₀ を供給。

### ▶ Case 3 (abelian Sylow, 12.8 regime) — **最難、recon 部分的**

A₀=E₂ (12.8(a))。(a) C_E(x)≤E₂。(b) 各 p∈τ₂ で cyclic Z_p⊴E (exp=exp(S_p)、C_{M_σ}(Ω₁(Z_p))=1)
構成 → E₀=E₁E₃·∏Z_p。**N_G(S)-不変 cyclic Z≠⊥ ⟹ C_{M_σ}(Ω₁(Z))=1 自動** (12.6(c)+N_G(S)⊄M)。
- **C_E(S)=E 枝**: S abelian rank2 ⟹ **S=Y×Z cyclic×cyclic** (= **recon (i) 未済**: mathlib に
  rank-2 abelian p-群の cyclic 分解の直接形が要調査; `Monoid.exists_orderOf_eq_exponent` で
  Z=⟨exp 元⟩ cyclic、Y=補空間を取る手組みが有力)。|Y|<|Z|: Ω₁(Z) char S。|Y|=|Z|: Ω₁(Z)=任意
  A₁∈ℰ¹(A)、**12.5(f)** (`Msigma_nilpotent_of_tau2 ….2.2.2.2.2`) で C_{M_σ}(A₁)=1。
- **C_E(S)≠E 枝**: q∈π(E/C_E(S))、Q=Syl_q(N_G(S))⊇Q₁=Syl_q(E)。Prop 1.6(e)⟹Q₁⊄C_E(A)⟹
  12.10(c)⟹q∈τ₁,Q₁ cyclic。Q₀=C_Q(S)⊂Q₁。**Q/Q₀ regular on S ⟹ Prop 3.9 で cyclic** (← 作り方
  = recon v: `MulAut.conjNormal`/`QuotientGroup.lift` で φ̄:Q/Q₀→MulAut S) ⟹ r_q(N_G(S))=1、
  但し **12.8(e)** (`central_line_of_abelianSylow`, sig 確認済) で Ω₁(Q₁) が A 中心化 + **12.11(c)**
  で r_q=2 矛盾。⟹ ∃X≤Q, 1⊂C_S(X)⊂S。S₀=C_S(X),S₁=[S,X] cyclic (S=S₀×S₁) + **12.8(f)**
  (`relative_normality_of_abelianSylow`, sig 確認済) で両方⊴N_G(S) ⟹ regular。Z=大きい方。

### ✅ Case 2 実装完了 (上記 session 8 cont.)。exponent (ii)/(iii) も landed。

### ▶▶ Case 3 = **次セッションの frontier** (BG L3344-3373 全文取得済、recon 大幅進展)

**BG proof 構造** (A₀=E₂ で (a)、(b) のみ): 各 p∈τ₂ で **cyclic N_G(S)-不変 Z≤S、exp(Z)=exp(S)**
を構成 → E₀ = E₁E₃·∏Z_p。**key fact** = 「N_G(S)-不変 cyclic Z≠⊥ ⟹ C_{M_σ}(Ω₁(Z))=1」自動
(p∉σ⟹N_G(S)⊄M、否定なら Cor 12.6(c) で N_G(S)⊆N_G(Ω₁(Z))⊆M 矛盾)。2 枝:
- **C_E(S)=E 枝**: S abelian rank2 = Y×Z cyclic。|Y|<|Z|: Ω₁(Z) char S。|Y|=|Z|: Ω₁(Z)=任意
  A₁∈ℰ¹(A)、12.5(f) で C_{M_σ}(A₁)=1 な A₁ 存在。
- **C_E(S)≠E 枝** (主): q∈π(E/C_E(S))、Q=Syl_q(N_G(S))⊇Q₁=Syl_q(E)。Prop1.6(e)⟹Q₁⊄C_E(A)
  ⟹12.10(c)⟹q∈τ₁,Q₁ cyclic。Q₀=C_Q(S)⊂Q₁。Q/Q₀ regular on S なら Prop3.9⟹cyclic⟹
  r_q(N_G(S))=1、但し 12.8(e)で Ω₁(Q₁)中心化A + 12.11(c)で r_q=2 矛盾。⟹∃X≤Q,1⊂C_S(X)⊂S。
  S₀=C_S(X),S₁=[S,X] (S=S₀×S₁) + 12.8(f)で両⊴N_G(S) ⟹ regular。Z=大きい方。

**🔑 recon 更新 (session 8 cont.²、API 大幅判明 — Case 3 は当初想定より tractable)**:
- ✅ **coprime 分解 `S=C_S(X)×[S,X]`** = `Isaacs.Ch05.fitting_coprime_abelian_decomp`
  (`(P:=S)(K:=X) (hX≤N(S)) hcop` → `⟨hinf, hsup⟩` = inf=⊥ ∧ C_S(X)⊔[S,X]=S; **使用例
  S12_Corollary129:154**)。⟹ C_E(S)≠E 枝の S₀×S₁ は組める。
- ✅ **rank1⟹cyclic** = `S10.isCyclic_of_pRank_le_one hpg hodd hr1` (S10_LocalLemmasCore:561/779)。
  S₀,S₁ は rank 加法性 (r(S₀)+r(S₁)=r(S)=2, 両≥1) で各 rank1 ⟹ cyclic。
- ✅ 12.8(e) `central_line_of_abelianSylow` (S12_Lemma128d:583)、12.8(f)
  `relative_normality_of_abelianSylow` (:405) — sig 確認済 (`hG h hp hA hAE hAS hSab`)。
- ✅ Cor12.6(c) = `maximalContaining_centralizer_line_eq_singleton` /
  `centralizer_zpowers_eq_singleton` (S12_Corollary126:257/241) — key fact に使用。
- ✅ Prop 3.9 = `isCyclic_of_coprime_fpf_pgroup_action` (S12_Theorem1212:55、landed)。
- ⚠ **残ギャップ 2 点**:
  - **(i) generic rank-2 abelian `S=Y×Z`** (C_E(S)=E 枝のみ): mathlib 直接形なし。有限 abelian
    構造定理 (`Additive`+`AddCommGroup` の不変因子分解) 経由か、rank2 専用補題の手組みが要る
    (それ自体が小サブプロジェクト)。**C_E(S)≠E 枝は coprime 分解で回避できるので、まず主枝を実装**。
  - **(v) quotient 作用 φ̄:Q/Q₀→MulAut S** (Prop3.9 適用): Q→MulAut S (共役、Q≤N_G(S)) の核
    =C_Q(S)=Q₀、`QuotientGroup.lift` で injective 化。要構成 (~20 行)。
- **着手順**: (1) ✅ **key fact COMPLETE** (commit 5359320d、新 leaf `S12_Theorem1212b.lean`):
  `inf_centralizer_line_eq_bot_of_invariant` (N_G(S)-不変 line L≤S ⟹ C_{M_σ}(L)=1) +
  `sylow_maximal_in_M_of_le` (G の Syl-p ⊆ M は M の Syl-p)。**Omega bridge 不要** — `Omega`
  を直接使用 (`omega1_eq_of_tau2` の `A=(Omega ↥S p 1).map S.subtype` + `Omega.mem_of_pow_eq_one`;
  `IsElementaryAbelian.pow_eq_one` で line 元の `g^p=1`; `p^1` は simp)。N_G(S)⊄M =
  `normalizer_sylow_le_normalizer_elemAb ….2`。**この lemma が両枝共通の payoff 接続点。**
  → (2) ✅ **cyclic-Z 正則性 bridge COMPLETE** (commit b84f8ffc): `line_le_zpowers_in_cyclic`
  (cyclic p-群で order-p 部分群は一意最小 L≤⟨a⟩; generator+`orderOf_pow` gcd+Bézout
  [`Int.gcd_eq_gcd_ab`/`zpow_eq_zpow_iff_modEq`/`Int.modEq_iff_dvd`]; mathlib に cyclic 包含直接形
  なし→自前) + `inf_centralizer_eq_bot_of_line_le_cyclic` (`N⊓C(L)=⊥`→`∀a∈Z#,N⊓C(a)=⊥`;
  `centralizer_zpowers_eq_singleton`+`centralizer_le`; ↥Z→G transport=`map_subgroupOf_eq_of_le`+
  `MonoidHom.map_zpowers`)。**key fact↔per-element 正則性の接続完成。S12_Theorem1212b に 4 補題。**
  → (3) ✅ **φ̄ quotient 作用 wrapper COMPLETE** (commit 5783a7d4, session 9): S12_Theorem1212b に
  3 部品 — `conjActionHom` (共役 hom ↥Q→*MulAut↥S = normalizerMonoidHom S を inclusion で comp) +
  `conjActionHom_ker` (kernel=C_Q(S)=C_G(S)⊓Q, normalizerMonoidHom_ker 経由) +
  `isCyclic_quotient_of_conjugation_fpf` (FPF ∀x∈Q∖C_G(S),S⊓C_G(x)=⊥ ⟹ IsCyclic(↥Q⧸ker);
  lifted φ̄=`QuotientGroup.kerLift`, `actionFixedBy φ̄ (mk a)=C_S(a)`, Prop 3.9 適用; coprime=q^m⊥p^n
  via `coprime_primes`+`Coprime.pow m n`; `(φ̄ a s).val=a·s·a⁻¹` は defeq で `congrArg Subtype.val`)。
  axiom-clean, AxiomsCheck 2 本。

**▶▶ C_E(S)≠E 主枝の残り (= 次の frontier、BG L3358-3373 完訳済)**。論理は 2 半:

- **front half = X 存在 (rank 矛盾, BG L3363-3370)**: q∈π(E/C_E(S)), Q=Syl_q(N_G(S))⊇Q₁=Syl_q(E)。
  C_S(Q₁)⊊S ⟹ Prop1.6(e) ⟹ Q₁⊄C_E(A) ⟹ Cor12.10(c) ⟹ q∈τ₁(M), Q₁ cyclic。C_G(S)⊆E ⟹
  Q₀=C_Q(S)⊊Q₁。**by_contra: Q/Q₀ が S に regular (FPF)** ⟹ φ̄ wrapper で IsCyclic(Q/Q₀) ⟹
  Ω₁(Q/Q₀)⊆Q₁/Q₀ ⟹ Ω₁(Q)⊆Q₁ ⟹ r_q(N_G(S))=r(Q)=1 (Q₁ cyclic)。一方 12.8(e) で Ω₁(Q₁) が A
  中心化 ⟹ 12.11(c) で r_q(N_G(S))=2。矛盾 ⟹ ∃X≤Q, 1⊊C_S(X)⊊S。**⚠ この rank 部分が hard**:
  Ω₁(Q)/Ω₁(Q/Q₀) の rank 連動 + 12.11(c) の r_q=2 抽出 (12.11(c) は「q∈τ₂(M*), Syl_p⊴M*,
  abelian Syl_q」止まりで「r_q=2」は派生 — sig 精査要)。
- **back half = Z 構成 (BG L3371-3373)**: X から S₀=C_S(X), S₁=[S,X], **coprime 分解
  `fitting_coprime_abelian_decomp`** (X≤N_G(S), coprime(|S|,|X|)) で S₀⊓S₁=⊥ ∧ S₀⊔S₁=S。
  両 nontrivial (S₀≠1 from 1⊊C_S(X); S₁=[S,X]≠1 from C_S(X)⊊S)。**両 cyclic**: `isCyclic_of_pRank_le_one`
  に pRank S₀≤1 / pRank S₁≤1 要。**🔑 pRank 加法性は mathlib/repo に無い** → 代替ルート確定:
  pRank S₀≥2 なら B₀(elem-ab,p²)⊆S₀ + y(order p)∈S₁ で **B₀⊔⟨y⟩ が elem-ab order p³**
  (`isElementaryAbelian_sup_of_le_centralizer` [S12_ExceptionalBridge:717, S abelian で中心化条件自明] +
  disjoint card |B₀⊔⟨y⟩|=p³) ⟹ `le_pRank` で pRank S≥3 vs pRank S=2 矛盾 ⟹ pRank S₀≤1。同 S₁。
  **✅ friction 解消 (disjoint card)**: `OddOrder.BG.Ch1.S01.card_sup_eq_card_mul_card_of_disjoint_normal`
  (`X⊓T=⊥ ⟹ |X⊔T|=|X|·|T|`, 片方 normal 要 — abelian S 内で自明)。**🔑 完全 template =
  `S04f_Blackburn.lean:1924-1937`** (T:order p², X:order p, disjoint → |T⊔X|=p³ →
  `isElementaryAbelian_sup_of_le_centralizer` で elem-ab → 用済; これを ↥S 型内で S₀,S₁ にミラー)。
  ⚠ 型注意: `le_pRank (A:Subgroup ↥S)` は `pRank ↥S p`、`isCyclic_of_pRank_le_one` は `pRank ↥S₀ p`
  — Subgroup G / ↥S / ↥S₀ 境界の cast が実装の主作業。
  **✅✅ back-half 抽象 primitive 2 件 DONE (session 9, commits e872900c / bd01dfe8, 両 axiom-clean)**:
  - `isCyclic_of_inf_eq_bot_of_pRank_le_two` (T:CommGroup 有限 p-群, pRank T≤2, T₀⊓T₁=⊥, T₁≠⊥ ⟹
    IsCyclic ↥T₀): elem-ab order p³ ルートを抽象化。S₀,S₁ 両方に適用 (T:=↥S, T₀/T₁ swap)。
  - `exponent_eq_of_sup_eq_top_of_exponent_dvd` (T₀⊔T₁=⊤, exp T₁∣exp T₀ ⟹ exp T=exp T₀):
    Z=大きい方で exp(Z)=exp(S)。card 大 ⟹ exp 大 (cyclic p-群) ⟹ exp(小)∣exp(大) を供給。
  - **✅ `inf_centralizer_eq_bot_of_invariant_cyclic` (3rd primitive, commit ba168e91)**: N_G(S)-不変
    nonidentity cyclic Z≤S ⟹ ∀z∈Z#, Mσ⊓C_G(z)=1。L=Ω₁(Z)=`(Omega ↥Z p 1).map Z.subtype` を
    line 化 (|Ω₁|=p via `Omega.exponent_eq_of_class_le_two`+`IsCyclic.exponent_eq_card`; 不変性
    via `AppB.normalizer_le_normalizer_map_of_characteristic` [Ω₁ char]) → key fact + bridge。
    Odd p = `hG.odd.of_dvd_nat`。**Z-regular payoff 完成。**
  **✅✅✅ Z 構成 assembly COMPLETE (session 9, commit 8ff6b506) — Case 3 back-half 完結**:
  `exists_invariant_cyclic_sameExponent_regular` (abelianSylow regime で X≤N_G(S) coprime +
  1⊊C_S(X)⊊S ⟹ ∃ cyclic N_G(S)-不変 Z≤S, exp(Z)=exp(S), regular)。`fitting_coprime_abelian_decomp`
  (P:=↑S,K:=X) で S₀=C(X)⊓↑S/S₁=⁅↑S,X⁆ → both-cyclic ×2 (cast wrapper
  `isCyclic_of_le_of_inf_eq_bot_of_pRank_le_two`) + 12.8(f) で ⊴N_G(S) → Z=大 (card) → exp
  (cast `exponent_eq_of_le_of_sup_eq_of_exponent_dvd`) + Z-regular。**🔑 知見: `open scoped
  IsMulCommutative` で `[IsMulCommutative ↥S]`→`CommGroup ↥S` 自動; pRank ↥S≤2 =
  `pRank_le_of_injective (inclusion hSM)` + tau2_pRank_eq_two; decomp(C⊓↑S) vs 12.8(f)(↑S⊓C) は
  inf_comm; card 大⟹exp 大 = IsCyclic.exponent_eq_card + pow_dvd_pow。** assembly は namespace
  修正のみで一発通過。
## ▶▶ front-half (X 存在 rank 矛盾) 実装プラン (session 9 末, 精密 recon 済 — BG L3358-3370)

**目標**: abelianSylow regime + C_E(S)≠E ⟹ ∃ X≤Q, 1⊊C_S(X)⊊S。これが back-half
`exists_invariant_cyclic_sameExponent_regular` に X を供給し C_E(S)≠E 枝完成。

**BG 引数 (L3358-3370) の formalization map**:
1. q∈π(E/C_E(S)) を取る (C_E(S)≠E ⟹ [E:C_E(S)]>1 ⟹ ∃ prime; mechanical)。
2. Q=Syl_q(N_G(S)), Q₁=Syl_q(E)⊆Q。**✅ 開問 (a) 解決 (session 9, commit c5b04ed7)**:
   `E_le_normalizer_sylow_of_abelianSylow` で **E≤N_G(S)** (sylow_chain で S≤F(E) → S=Syl_p(nilpotent
   F(E)) char → E normalizes F(E) ⟹ E≤N_G(F(E))≤N_G(S))。ゆえ Q₁=Syl_q(E)⊆E⊆N_G(S)。
3. C_S(Q₁)⊊S ⟹ Prop1.6(e) ⟹ Q₁⊄C_E(A) ⟹ **Cor12.10(c)** ⟹ q∈τ₁(M), Q₁ cyclic。
   **🔶 開問 (b) 部分解決**: repo の `nilpotent_sigmaComplement_abelian` (S12_Corollary1210:158) の
   (c) 連言 = 「π(E/C_E(A))⊆τ₁(M)」。Q₁⊄C_E(A)⟹q∈π(E/C_E(A))⟹q∈τ₁、q∈τ₁⟹Syl_q cyclic (rank1)。
   threading (Prop1.6(e) + (c)連言 + τ₁⟹cyclic) は要実装だが pieces 揃った。
4. C_G(S)⊆E ⟹ Q₀=C_Q(S)⊊Q₁ (Q₀⊆Q₁ は C_Q(S)≤Q₁=Syl_q(E)、⊊ は Q₁⊄C_E(A)⟹Q₁⊄C_G(S))。
5. **by_contra: Q/Q₀ regular on S** (∀x∈Q∖C_G(S), S⊓C_G(x)=⊥) ⟹ **φ̄ wrapper
   `isCyclic_quotient_of_conjugation_fpf` ✅** ⟹ IsCyclic(Q⧸C_Q(S))。
6. **r(Q)=1 側 (= 新規 abstract lemma 推奨, 自己完結)**: IsCyclic(Q⧸Q₀) ∧ Q₀⊊Q₁≤Q (q-群) ⟹
   Ω₁(Q)⊆Q₁ ⟹ (Q₁ cyclic) pRank Q q≤1。**証明**: Ω₁(Q/Q₀)⊆Q₁/Q₀ (Q₁/Q₀ は cyclic Q/Q₀ の
   nontrivial 部分群 ⟹ unique min 含む, `line_le_zpowers_in_cyclic` 系) → g∈Ω₁(Q) は ḡ^q=1 ⟹
   ḡ∈Ω₁(Q/Q₀)⊆Q₁/Q₀ ⟹ g∈Q₁·Q₀=Q₁ → elem-ab⊆Ω₁(Q)⊆Q₁ で pRank Q=pRank Ω₁(Q)≤pRank Q₁≤1。
   ~50 行、Omega quotient + preimage 機構。**← 最初の committable 一手 (abstract, BG 非依存)。**
7. **r_q=2 側 (= hard core, BG 依存)**: 12.8(e) で Ω₁(Q₁) が A 中心化 ⟹ q∈π(E/C_E(A))∩π(C_E(A))
   ⟹ **`tau2_transfer_to_maximal` (=12.11(a-c), 第3連言)** で q∈τ₂(M*), M* に abelian Syl_q(G)。
   q∈τ₂(M*)⟹r_q(M*)=2。**⚠ 開問 (c) = 真の hard core: r_q(M*)=2 ⟹ r_q(N_G(S))=2 の接続** —
   M* の abelian Syl_q(G) が N_G(S) 内に来る根拠が要 (BG は「Lemma 12.11(c) yields
   r_q(N_G(S))=2」と圧縮)。`pRank_eq_two_of_normalizer_le` [S10] は maximal 用で N_G(S) 直結せず。
   12.8(e) の repo 形 `central_line_of_abelianSylow` は「X∈ℰ¹+regular⟹X≤E∧E中心化X」で
   「Ω₁(Q₁)中心化A」とは別命題 — 12.8(e) の正しい形を S12_Lemma128d で要再特定。
8. 6 と 7 で pRank Q q ≤1 vs =2 矛盾 ⟹ X 存在。

**推奨 build 順**: **✅ (6) Ω₁-rank abstract lemma 着地 (session 9, commit 8672fd5c)** —
`omega_le_of_ne_bot_in_cyclic` + `pRank_le_one_of_cyclic_quotient` (IsCyclic(Q⧸Q₀)∧Q₀⊊Q₁⟹
pRank Q≤1; Ω₁(Q)≤Q₁ を `Subgroup.comap_map_eq_self`+omega-helper で、elem-ab≤Ω₁ は
`IsElementaryAbelian.pow_eq_one`+`Omega.mem_of_pow_eq_one`、|B|≤q は cyclic exponent)。一発に
近く通過 (修正 2: `h0lt1.ne`+`le_antisymm` / `≤` 型付け)。→ 次 = (a)(b) 開問解決
(E/N_G(S), Cor12.10(c) 特定) で setup → (c) hard core (12.8(e) 正形 + r_q=2 接続) を BG 精読で
攻略 → 統合 (r(Q)=1 [✅] + φ̄ wrapper [✅] + r_q=2 [c] で by_contra)。**(c) が front-half の真の
ボトルネック (BG 圧縮された rank 接続)。**

**残 (front-half 後)**: C_E(S)=E 枝 (generic rank-2 分解 S=Y×Z — mathlib
`AddCommGroup.equiv_directSum_zmod_of_finite` 在だが rank2→2 cyclic 部分群への翻訳は別 sub;
|Y|=|Z| case は Ω₁(Z)=任意 A₁ の制御要) → Z_p 集約 E₀=E₁E₃·∏Z_p → `frobFact_of_abelianSylow`
→ 3 ケース統合で S12_E scaffold `frobenius_factorization_of_regular` 充足。
**⚠ Case 3 残りは hard core 複数 (front-half (c) + =E generic decomp) — multi-session 見込み。**

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

### ✅ session 6 cont.: **Corollary 12.10 COMPLETE — 全 5 結論** (新 leaf `S12_Corollary1210.lean`, unconditional・axiom-clean)

mmd L3294-3316。`nilpotent_sigmaComplement_abelian` (S12_E scaffold 移設・充足、
**S12_E 実 sorry 7→6**)。AxiomsCheck 3 本登録 (standard 3 のみ)。

- **⚠ scaffold faithful 化**: (c) 連言に `p.Prime →` を追加 (BG の τ₂ は素数集合だが repo
  `tau2` は pRank 条件のみで合成数を排除しない — 12.3 の unfaithful 訂正と同類)。
- **鍵部品 ×2** (public, 12.11+ 再利用可):
  `sylow_isMulCommutative_of_sigma_compl` (r ∉ σ(M), r ∣ |M| ⟹ M の Sylow r abelian;
  τ-分割 `SubgroupESetup.mem_tau_union_of_mem_primeFactors` → τ₁/τ₃ = rank-1 cyclic
  [`pRank_sylow_eq` + `S10.isCyclic_of_pRank_le_one`], τ₂ = **12.5(b) 第 2 連言が直接**
  [`Msigma_nilpotent_of_tau2 ….2.1.1`]) と
  `isMulCommutative_of_isNilpotent_of_forall_sylow` (汎用: nilpotent + 全 Sylow abelian ⟹
  abelian; **`isNilpotent_of_finite_tfae .out 0 4`** の Sylow 直積 equiv + 2 重 funext)。
- **(a)**: Sylow-of-N → G-level map → ↥M の Sylow へ `exists_le_sylow (G := M)` → 鍵部品。
  S = ⊥ 枝は Subsingleton で comm。
- **(b)**: E₂ = by_cases ∃τ₂-素数 (空なら card 1 で trivial) → by_cases nonabelian Sylow:
  12.7(a)文脈 `E2_isMulCommutative_of_prime_eq` / 12.8(a) `E2_abelian_normal_hall_of_abelianSylow .1.1`。
  E' = 12.1(a) `h.derived_isNilpotent` + (a)。
- **(c)**: `A ≤ E₂` = **`IsPiGroup.normal_le_hall`** (A ⊴ E は 12.6(a)、Normal instance =
  `normal_subgroupOf_iff_le_normalizer`); E₂ ≤ C(A) = `le_centralizer_of_le_of_le`;
  E₃ ≤ C(A) = ⁅E₃,A⁆ ≤ E₃⊓A = ⊥ (commutator_le 元計算 + coprime [τ₃ vs p∈τ₂ pRank 衝突]);
  正規性 = `mem_normalizer_of_conj_smul_eq_self` + **`Subgroup.smul_inf`** + `centralizer_conj_smul`;
  index 素因子 = **`relIndex_mul_relIndex` (hHK/hKL named — H K L が explicit variable)** で
  `index_{C⊆E} ∣ index_{E₂⊆E}` → Hall .2 で τ₂/τ₃ 排除。
- **(d)**: `exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic` (↥P 内) → map →
  **12.4(a) `centralizer_le_of_elemAb_rank_two` は σ/σ' 不問で適用可** (bridge 版に hpσ 引数なし) →
  10.1(c) = `S10.fusion_control_of_mem_sigma ….2.2.1` の N(P) 元分解 n = a·c。
- **(e)**: E₂ は M の Hall τ₂ でもある (relIndex 連鎖 + `E.relIndex M = |M_σ|` card 消去) →
  trivial-action Hall 押し込み + `exists_conj_eq_of_isHall_subgroupOf` で y := x^w ∈ E₂ →
  A ≤ C(y) (E₂ abelian) → coatom M* ⊇ C(y) は **12.5(e) (`.2.2.2.2.1`)** で = M
  (C_{M_σ}(y) ≠ ⊥ と M_σ⊓M* = ⊥ の衝突) → C(y) ≠ ⊤ (center = ⊥) で ≤ M →
  conj 引き戻し (private `centralizer_singleton_conj_smul` + `isCoatom_conj_smul`)。
- ⚠ 技法: **`rintro rfl` が theorem binder `M` を consume して識別子 `M` が消える**
  (ext 変数 Mstar = M の subst が M 側を選ぶ) → `intro hMs; rw [hMs]` で回避。
  `subst hu` (hu : u = x, x = binder) も同罪 → `rw [hu]`。
  `Subgroup.relIndex_mul_relIndex` は H K L explicit → named (hHK :=)/(hKL :=) で渡す。
  `(MulAut.conj g).toMonoidHom z = g*z*g⁻¹` は rfl で潰す (conj_apply simp は coe 形に不発)。
  `Dvd.intro_left` でなく `dvd_of_mul_left_eq`。mem_center/centralizer の comm 向きは `.symm` 要確認。
- conj_smul_mono (S12_Corollary129) を public 化 (12.10 (e) が使用)。

### ✅✅✅ session 7: **Lemma 12.11 COMPLETE — (a)(b)(c) + assembly** (新 leaf `S12_Lemma1211.lean`, unconditional・axiom-clean)

mmd L3318-3334。**S12_E 実 sorry 6→5** (scaffold `tau2_transfer_to_maximal` を leaf に
移設・充足; (a)-連言は素数限定形に faithful 化 — 12.3/12.7(a)/12.10(c) と同型)。
AxiomsCheck 計 8 本 (sessions 6-7 で leaf 分全登録)。

- **前段 (session 7 開始時に commit 済)**: `exists_subgroupESetup` (§12 冒頭の setup 存在
  — SZ 補群 + Hall-in-Hall `isHallSubgroup_of_isHallSubgroup_of_le` で `E₁⊔E₂` を `K₀` に
  同定) / (a) `tau2_prime_mem_sigma_diff_beta` (`p` 自身 = 12.2(a)
  `prime_mem_sigma_or_tau2` + τ₂-枝は 12.6(b) `N(A^w)⊄M*` 衝突; `q ≠ p` は押し込み
  `A_q ≤ E₂` + coprime normal 可換 + **12.5(d)** rank-clash; β = 12.1(g)) /
  (b) `index_primeFactors_subset_tau1_union_tau2` (σ∪τ₃ に落ちると `Q ≤ M*'` →
  Lem 10.8(c) normal `p`-補群 → `⁅A,Q⁆ = ⊥` → `q ∤ [E:C_E(A)]` 矛盾) / 汎用押し込み
  `exists_conj_smul_le_hallPiece` + `hallPiece_isHall_in_M`。
- **(c) = `tau2_normalSylow_abelianSylow_of_mem_index_card`** (本セッション):
  - **line パッケージ** (private `exists_line_package`): `C_G(A) ≤ E` (12.6(b)) の Sylow
    `q`-部分群 `Q₁` (cyclic — `q ∈ τ₁(M)` = **12.10(c)**) とその唯一の位数 `q` 部分群
    `Q₀ = Ω₁(Q₁)`、`Q₁` を含む `E` の Sylow `q` の像 `Q` (cyclic, `q² ≤ |Q|` ⟸
    `q ∣ |C_E(A)|` × `q ∣ [E:C_E(A)]`)、**Frattini 性** (∀T: `C_G(A) ≤ T` ∧
    `N_G(Q₀) ≤ T` ⟹ `N_G(A) ≤ T`) を bundle。Frattini = mathlib
    `Sylow.normalizer_sup_eq_top` (ambient `↥N_G(A)`, normal `C.subgroupOf N`
    [`normal_subgroupOf_iff_le_normalizer` + `normalizer_le_normalizer_centralizer`]) +
    `Subgroup.mul_normal` 分解 + `map_subtype_conj_smul` で G-level 化 + cyclic 一意性
    (`le_of_ne_bot_of_le_cyclic` + `eq_of_le_of_card_ge`) で `N(Q₁)` 元が `Q₀` も正規化。
  - **M\*\* 構成と同定**: `M** ∈ ℳ(N_G(Q₀))` → `A ≤ C(Q₀) ≤ M**` → **12.4(a)** で
    `C_G(A) ≤ M**` → Frattini 性で `N_G(A) ≤ M**` ⟹ `M** ∈ ℳ(N_G(A))` → (b)@M** +
    **12.2(a)** (X := Q₀) で `q ∈ τ₂(M**)` → (a)@両方で `p ∈ σ(M*) ∩ σ(M**)` →
    **12.6(f)** (M** 基準, A_q は押し込み構成) で共役 → **Thm 10.1(b)** transitivity
    (`(g₁,g₂) := (g,1)`, `c ∈ C_G(A) ≤ M*` 固定) で `M* = M**` (subst でなく
    `rw [← hMeq] at hs hqτ₂ss` — binder-consume 回避)。
  - **結論 2** (Sylow `p` ⊴ M*): **12.5(a)** (A_q ≤ M*) で `M*_σ` nilpotent →
    `S10.exists_sylow_le_normalizer_le_of_mem_sigma` の `S ≤ M*` を
    `sigma_subgroup_le_Msigma_of_isHall` で `M*_σ` へ → `S.subtype` + nilpotent tfae 0 3
    → `Sylow.characteristic_of_normal` → AppB transport + `le_normalizer_opiCoreInG`
    (`Sylow.coe_subtype` + `subgroupOf_map_subtype` + `inf_of_le_left` で写像同定)。
  - **結論 3** (abelian Sylow `q` ≤ M*): Syl ⊇ A_q を by_cases。abelian = **12.8(c)**
    chain `S ≤ N(S)' ≤ F(E*) ≤ C(S) ≤ E* ≤ M*` で即。nonabelian = **12.7 assembly**
    (A₀ card q, (c)-清掃条項, 補群 E₀) → `Q` を `E₂*` へ押し込み (`Q₀^w ≤ Q^w` 保持) →
    `⊥ ≠ A^w ≤ M*_σ ⊓ C(Q₀^w)` で 12.7(c) 対偶から `Q₀^w = A₀` → `K' := E₀ ⊔ M*_σ`
    (`|K'|·q = |M*|` [card_sup ×2 + `card_Msigma_mul_card_E`], `A₀ ⊓ K' = ⊥` [card 勘定])
    → **`no_complement_of_lt_cyclic`** (`[Q^w : Q^w⊓K'] ≤ [M*:K'] = q` vs `q² ≤ |Q^w|`)
    で False。
- ⚠ 技法 (新規): **`rw [← hs.E_compl_sup]` は RHS の `S10.Msigma Mstar` 内の `Mstar` も
  巻き込み** → モンスター型が heartbeats を食い尽くし**後続 tactic に timeout が連鎖**
  (エラー行 ≠ 原因行; 12.9 の conv_lhs 罠の正規化版)。**sup/inf の片側だけ展開する rw は
  `conv_lhs => rw [...]` を既定にする**。`le_normalizer_inf` は「N(A)⊓N(B) ≤ N(A⊓B)」
  でなく 2 つの bound (hA : H ≤ N(A)) (hB : H ≤ N(B)) を直接取る。
  `card_sup_eq_mul_of_le_normalizer_of_disjoint` は S12_E に public 既存 (重複宣言注意)。
- leaf 内 private 再掲 (hoist は hub 仕事): `card_conj_smul` / `map_subtype_conj_smul` /
  `le_of_ne_bot_of_le_cyclic` (cyclic q-群の最小部分群一意性; 新規) /
  `no_complement_of_lt_cyclic` (新規; relIndex 論法)。

▶ **次 = Theorem 12.12** (S12_E:449 scaffold `frobenius_factorization_of_regular`;
mmd L3336-3383 — **大物** (Frobenius 因子分解))。残 S12_E sorry 5 = 12.4(a) 系 ×3
(`nonabelian_pgroup_isUniquelyMaximal` / `maximalContaining_centralizer_eq_singleton` /
`sigma_subgroup_conj_into_Msigma`) + 12.12 + 12.15。12.13 は S12_E に scaffold 無し
(リスト上は次の大物)。

### ▶ Thm 12.12 実装レシピ (session 7 末 recon 済 — 再調査不要)

**scaffold**: `frobenius_factorization_of_regular` (S12_E:449)。hreg =
「∀ e ∈ E#, π(ord e) ⊆ τ₁∪τ₃ → M_σ ⊓ C_G({e}) = ⊥」。新 leaf `S12_Theorem1212.lean`。

**3 大ケース** (mmd L3340-3383):
1. **τ₂(M) = ∅** (E = E₁E₃): A₀ := ⊥, E₀ := E。(a) = ∀e∈E#, π(ord e)⊆τ₁∪τ₃ (τ-分割
   `mem_tau_union_of_mem_primeFactors` + E₂ trivial) → hreg → C_E(x) = ⊥。
   (b) Frobenius = hreg 直。exponent = rfl。
2. **nonabelian Sylow p** (p∈τ₂): **12.7 部分定理を直接呼ぶ** (assembly でなく):
   `exists_canonical_line_of_nonabelianSylow` (A₀, card p, habs) →
   `fitting_eq_sup_of_canonical_line` **第1連言 = M ≤ N(A₀)** (E-正規性) →
   `exists_complement_of_canonical_line` (E₀) + (e) `primeFactors_centralizer_le_tau1_of_disjoint`
   + hreg → C_{E₀}(x) = ⊥。(a) の C_E(x) ≤ A₀: A₀ ≤ C_E(x) (hMσC swap) +
   C_E(x)⊓E₀ = ⊥ + [E:E₀] = p で card ≤ p。**exponent**: E₀ の Sylow p ≅ P/A₀ ≅ Z cyclic
   (P = A₀ × Z, 10.13(b)) — per-prime exponent 勘定 (下記 4)。
3. **abelian Sylow** (12.8 regime): (a): A₀ := E₂ (12.8(a))、C_E(x) ≤ E₂ =
   「C_E(x) は τ₂-群 (e = e₁e₂ 素数分解で τ₁τ₃-部分は hreg で死ぬ; e_r ∈ ⟨e⟩ ⟹
   C(e) ≤ C(e_r)) + `IsPiGroup.normal_le_hall`」。(b): 各 p∈τ₂ に cyclic Z_p ⊴ E,
   exp(Z_p) = exp(S_p), C_{M_σ}(Ω₁(Z_p)) = ⊥ を構成 → E₀ := E₁ ⊔ (⊔_p Z_p) ⊔ E₃:
   - **N_G(S)-不変 cyclic Z ≠ ⊥ は自動的に C_{M_σ}(Ω₁(Z)) = ⊥** (mmd L3345): さもなくば
     12.6(c) `maximalContaining_centralizer_line_eq_singleton`-経由で N_G(S) ≤ N_G(Ω₁(Z)) ≤ M
     — 12.5(b) `N_G(S) ⊄ M` に矛盾。Ω₁(Z) char Z ⊴ N_G(S) の transport。
   - **case C_E(S) = E**: S = Y × Z cyclic ×2 (**abelian rank-2 の cyclic 分解 — 要 recon**:
     mathlib に直接形が無ければ S ≅ Z/p^a × Z/p^b を `IsPGroup.commutative...` 経由で?
     12.7(d) の Maschke 流 or `Subgroup.pow_index_mem` 流で手組みも可)。|Y|<|Z| なら
     Ω₁(Z) char S (= Ω₁(℧^{k}(S)) 形) → N_G(S)-不変。|Y|=|Z| なら任意の
     A₁ ∈ ℰ¹(A) を Ω₁(Z) に取れる + **12.5(f)** (`Msigma_nilpotent_of_tau2 ….2.2.2.2.2`:
     ∃A₁, C_{M_σ}(A₁) = ⊥)。⚠ この枝は「Z ⊴ E」を C_E(S) = E (E が S を中心化) から得る。
   - **case C_E(S) ≠ E**: q ∈ π(E/C_E(S)), Q := Sylow q of N_G(S) ⊇ Q₁ := Sylow q of E
     (E ≤ N_G(S) = 12.8 `sylow_eq_opiCore_fittingInG_of_tau2` 第2連言)。
     Q₁ ⊄ C_E(A) = **Prop 1.6(e)** (新 helper ~15 行: (d) `fitting_coprime_abelian_decomp` +
     「Ω₁([S,Q₁]) ≤ C⊓[S,Q₁] = ⊥ ⟹ [S,Q₁] = ⊥」+ **A = Ω₁(S)** = `omega1_eq_of_tau2`) →
     12.10(c) で q ∈ τ₁(M), Q₁ cyclic。Q₀ := C_Q(S) ⊂ Q₁ (C_G(S) ≤ E [12.8(c)] ⟹
     Q₀ ≤ Q⊓E = Q₁ [Sylow 極大性])。
     **regular 仮定の反駁**: (i) r_q(N_G(S)) = 2: Ω₁(Q₁) は A を中心化 (12.8(e)
     `central_line_of_abelianSylow` … 要シグネチャ確認) → **12.11(c)** (q ∈ π(index)∩π(card)
     ✓) で q ∈ τ₂(M*) ∧ P ⊴ M* → **S = P** (S, P とも abelian Sylow-p-of-G ∋ A ⟹
     ≤ C_G(A) ≤ M*; P ⊴ M* は唯一 Sylow ⟹ S ≤ P ⟹ S = P) ⟹ **N_G(S) = M*** (maximal)
     ⟹ r_q(N_G(S)) = pRank M* q = 2。(ii) regular ⟹ **Prop 3.9** で Q/Q₀ cyclic ⟹
     Ω₁(Q) ≤ Q₁ (Q₀ ≤ Q₁ + quotient Ω₁ 持ち上げ) ⟹ r(Q) ≤ 1 (elem-ab B ≤ Ω₁(Q) ≤
     cyclic) — (i) と omega 矛盾。
     **non-regular 出口**: ∃x ∈ Q−Q₀, C_S(x) ≠ ⊥ → S₀ := C_S(⟨x⟩), S₁ := [S,⟨x⟩]:
     S = S₀ × S₁ (1.6(d)), 両方 cyclic (rank-2 の直積因子, 両方 ≠ ⊥... S₁ = ⊥ なら
     x ∈ C(S) = Q₀ ✗), **12.8(f)** `relative_normality_of_abelianSylow` で両方 ⊴ N_G(S)
     → 上の自動 regularity → Z := |S₀|≥|S₁| ? S₀ : S₁ (exp(Z) = exp(S) = max)。
4. **Prop 3.9 (新規形式化, leaf 内 public — BG は G 5.3.14 引用だが repo 流の短証明)**:
   `R` p-群 (p odd) が `H ≠ 1` に coprime FPF 作用 (φ : R →* MulAut H) ⟹ IsCyclic R。
   証明 = `S10.isCyclic_of_pRank_le_one` + by_contra で rank ≥ 2 → B ≤ R elem-ab p²
   (`exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank` + `exists_subgroup_card_prime_sq`)
   → **Isaacs 6.21** `nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'`
   (S01b_Prop116; φ' := φ.comp B.subtype, ¬cyclic = elem-ab p² rank2) → 各 C_H(b) = ⊥
   (FPF) → H = ⊥ ✗。**12.12 での適用は quotient 作用 Q/Q₀ ↷ S**: φ̄ を
   `QuotientGroup.lift`-form で組む (ker ⊇ Q₀ = C_Q(S)); regular 仮定がちょうど FPF。
5. **Frobenius 判定**: `Ch06.IsFrobeniusGroup` fields = isNormal/isComplement'/ne_bot ×2/
   conj_frobenius (∀a∈A#, ∀n∈N#, ana⁻¹ ≠ n)。M_σ ⊴ M_σ⊔E₀ = `normal_subgroupOf_…`,
   IsComplement' = disjoint + card (`Subgroup.isComplement'_…` 要 recon)、
   conj_frobenius ⟺ C_{M_σ}(a) = ⊥ (元計算)。
6. **E₀ 全体の regularity** (∀e∈E₀#, C_{M_σ}(e) = ⊥): e の素数部分 e_r ∈ ⟨e⟩ (∃k, e_r = e^k)
   ⟹ C(e) ≤ C(e_r); r ∈ τ₁∪τ₃ → hreg; r ∈ τ₂ → e_r ∈ Sylow-r(E₀) = Z_r
   (|E₀|_r = |Z_r| ∧ Z_r ⊴ E₀ ⟹ 唯一 Sylow) → ⟨e_r⟩ ⊇ Ω₁(Z_r)-条項。
   **exponent**: exp = lcm-of-Sylow-exponents の per-prime 勘定
   (**mathlib `Monoid.exponent` API 要 recon**: `Monoid.exponent_eq_iSup_orderOf` 系 +
   Sylow ごとの分解; E₀ の Sylow: r∈τ₁τ₃ は E₁/E₃ 全体が入るので E と同一, r∈τ₂ は
   Z_r で exp(Z_r) = exp(S_r) を構成時に確保)。

**未 recon (session 8 冒頭で)**: (i) abelian p-群 rank-2 の cyclic×cyclic 分解の mathlib 形,
(ii) `Monoid.exponent` × Sylow API, (iii) `IsComplement'` 構成 lemma 名,
(iv) 12.8(e)/(f) の正確なシグネチャ, (v) quotient 作用 φ̄ の組み方
(`MulAut.conjNormal`? `QuotientGroup.lift`)。

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

---

## session 21 (2026-06-13, Lane F): Prop 12.15 COMPLETE + d.2 の素数限定決定

**✅✅✅ BG Prop 12.15 (`sigma_subgroup_maximal_interaction`) 完全証明** — sorry-free・axiom-clean
(AxiomsCheck 登録済、3 axioms 全 allowlist)。新 leaf `S12_Proposition1215.lean`、commit `6d696a0a`。
全 5 結論 (a)-(e)。Thm 12.13 (前 session) と並ぶ §12 keystone で、§13-14 を gate していた。

**🔑 d.2 (τ₁-transfer) の素数限定決定 (重要・Lane G / 後続は再検討不要)**:
- 結論 `tau1 M⋆ ⊆ tau1 M ∪ α M` を `∀ r, r.Prime → r∈tau1 M⋆ → r∈tau1 M ∪ α M` に**素数限定**した。
- 理由: BG 原文 (local-analysis.mmd L3059, L2647) で **τᵢ(M) も α/β/σ も `{p∈π(M)|…}` = 素数の集合**
  (「π(M) は σ⊔τ₁⊔τ₂⊔τ₃ の disjoint union」)。BG の `r_p` は素数のみ定義 (L1363)。
- repo の `tau1` 定義は BG の `p∈π(M)` 条件を落とし `pRank`-based で **ℕ 上を走る**ため、合成数 r
  (例 9: `IsElementaryAbelian 9` は素数性不要ゆえ ℤ/9 が該当、pRank=1 可) も τ₁(M⋆) に入りうる
  (formalization artifact)。その合成数 r では r∉α(M) (α⊆素数) かつ shared-Sylow 論法 (Sylow=素数専用)
  が効かず、**文字通りの集合包含は破れうる (偽の可能性)**。素数限定は **BG 忠実かつ lossless**。
- ⚠ 12.15 は他から未 cite だったので statement 変更は安全 (S12_E 旧 decl は sorry のまま放置されていた)。

**証明の 3 段** (r 素数, r∉α(M) の場合に r∈τ₁(M) を示す):
- **P5** `r∉π(M')`: `commutator_le_commutator_sup_normal` (K=A·N, N⊴K ⟹ K'≤A'·N) を ↥M で適用
  + (M∩M⋆)≤M⋆ の derived-mono + `card_HK_mul_card_inf` 割り算 + `Mbeta_isPiGroup`。
- **P6** `r∉σM`: `mem_sigma_iff` の Sylow-r → `IsPiGroup σM` → `sigma_subgroup_le_Msigma_of_isHall`
  → M_σ ≤ M' (`Msigma_le_derived`)、P5 と矛盾。
- **pRank M r=1**: shared Sylow `R=Syl_r(M∩M⋆)=Syl_r(M)=Syl_r(M⋆)`。`r∤[M:M∩M⋆]`/`r∤[M⋆:M∩M⋆]`
  を M_β/M⋆_β diamond (`not_dvd_index_of_sup_top_normal`) で出し、`pRank_eq_of_le_of_not_dvd_index`
  (`Sylow.ofCard` で R を両 Sylow に realize) で `pRank M r = pRank(M∩M⋆) r = pRank M⋆ r = 1`。

**再利用可能な汎用 helper (§13+ で有用)**:
- `commutator_le_commutator_sup_normal {K}(A N)[N.Normal](A⊔N=⊤) : commutator K ≤ ⁅A,A⁆⊔N`
- `not_dvd_index_of_sup_top_normal {K'}(A N)[N.Normal](A⊔N=⊤)(r∤|N|) : r∤A.index`
- `pRank_eq_of_le_of_not_dvd_index {H K}(H≤K)(r∤[K:H])[Fact r.Prime] : pRank H r = pRank K r`

**§12 残 frontier** (S12_E に 5 sorry): 12.14 (`maximalContaining_centralizer_eq_singleton`),
12.16 = `sigma_subgroup_conj_into_Msigma` (Y を M_σ へ共役) / `sigma_subgroup_pRank_normalizer_le_one`
(r_p(N_H(Y))≤1) / `sigma_subgroup_not_mem_primeFactors_derived_of_tau1` (p∈τ₁(M)⟹p∉π(N_H(Y)'))。
**12.16 が Lane G を gate** ⟹ 次の優先。完了で §12 STOP。

---

## session 22 (2026-06-13, Lane F): Cor 12.16 COMPLETE (新 leaf S12_Corollary1216)

**✅✅✅ BG Cor 12.16(a)(b) 完全証明** — sorry-free・axiom-clean (AxiomsCheck 登録、各 3 axioms
全 allowlist; full build 3802 jobs / AxiomsCheck 3787 jobs green)。**新 downstream leaf
`S12_Corollary1216`** (namespace `S12.Cor1216`)、commits `6ddd4646`(leaf 完成)/`58045d80`(配線)。

**🔑 なぜ downstream leaf か (architecture)**: 12.16 の証明は Prop 12.15 (`S12_Proposition1215`)
を要するが、後者は S12_E を推移 import (Theorem125→ExceptionalBridge→…→Lemma1218→S12_E) ゆえ
S12_E から 12.15 を import 不可 (循環)。Thm 12.13 / Prop 12.15 と同じく downstream leaf 化で解決
(ユーザー裁可 Option 1, 2026-06-13)。

**🔑 q-group 特化決定 (HUB / Lane G 要対応)**: BG の Y は一般 σ(M)-部分群だが、**Lane G の
S13_Lemma131 は Y を q-群 (`IsPGroup q Y`) として供給** (S13:416)。よって leaf の 2 補題は
`(hYq : IsPGroup q Y) (hqσ : q∈σM)` 引数 (旧 S12_E の `hYpi : IsPiSubgroup (σM) Y` でなく) で q-群
特化形を証明 ⟹ char-subgroup 抽出 (Fitting) を回避し簡潔。一般形 (hYpi) は char q-subgroup
wrapper として将来追加可 (deferred)。**HUB は merge 時に Lane G の cite を S12_E sorry'd →
`S12.Cor1216.pRank_normalizer_le_one` / `…not_mem_primeFactors_derived_of_tau1` へ re-point;
引数を hYpi → hYq + hqσ へ差替 (G は hYq を保持済ゆえ供給可)。byte-identical でない点に注意**。

**証明構造** (両補題共通): conjugation `Y` を `M_σ` へ G-共役 (rank/deriv 共役不変で transport) →
core (`Y⊆M_σ` 仮定) で case split:
- Case 1 (`N_G(Y)⊆M`): direct (rank-2 A≤M / deriv N≤M')。
- Case 2 (`N_G(Y)⊄M`): 共有 helper `exists_Mstar_factorization` (M*∈ℳ(N_G(Y)), M*=(M∩M*)K,
  K=M*_β/σ p'-群 [Prop 12.15(d)/(e) + (12.3)]) → (a) 新 rank-2 B∈ℰ_p²(M∩M*) [pRank coprime-index]
  + Thm 12.5(e); (b) `deriv N ≤ deriv M* ≤ (M∩M*)'⊔K` p' [crux `commutator_le_commutator_sup_normal`]。
replicate helper: rank-2 抽出 / not_dvd_index / pRank_eq / pRank_eq_of_mulEquiv / crux /
derivedInG_mono / card_derivedInG_conj (|deriv(g•K)|=|deriv K| via pointwise_smul_def+map_commutator)。

**§12 残 frontier**: S12_E に **12.14** (`maximalContaining_centralizer_eq_singleton`) 1 件のみ
(NOT G-cited; BG 証明 ~10 行で Thm 12.13 + §5 narrow + §10 使用)。12.14 完了で **§12 STOP**。
(S12_E の sorry'd 12.16 forward-decl 3 件は HUB re-point 後に削除可; conj_into_Msigma は実証明済。)


---

## session 23 (2026-06-13, Lane F): main 同期 + Cor 12.14 recon (downstream-leaf 化決定)

**main 取込**: `git merge main` クリーン (Peterfalvi のみ、衝突0)、full build 3802 jobs green、
AxiomsCheck OK (Cor1216.* 含む)。bg-s12 先行3コミット (6ddd4646 leaf 完成 / 58045d80 配線 /
b9827f69 notes) は未マージ (HUB が次 merge で回収)。

**🔑 Cor 12.14 architecture 決定 (12.13/12.16 と同型)**: S12_E:58 `maximalContaining_centralizer_eq_singleton`
は **どこからも未引用** (dead forward-decl scaffold)。証明は **Thm 12.13** (`nonabelian_pgroup_isUniquelyMaximal`,
S12_Theorem1213) を要するが S12_E はそれを循環で import 不可 ⟹ **新 downstream leaf
`S12_Corollary1214.lean`** に実証明を置き、S12_E:58 を削除 (comment pointer 化)。leaf は
S12_Corollary1216 と同様 S12_Proposition1215 (→ S12_Theorem1213) を import すれば Thm 12.13 に到達。

**🔑 WLOG 不要を確認**: X は σ(M)-部分群 (p∈σ(M), X≤M, IsPGroup p X) ⟹ `sigma_subgroup_le_Msigma_of_isHall`
(+ `Msigma_isHall`) で **X ⊆ M_σ 直接**。M_σ の Sylow p `P` が X を含む (Sylow `exists_le`)。共役 transport 不要。
p∈σ(M) ⟹ Sylow p of M_σ = Sylow p of M = Sylow p of G (`isSylow_sylowMap_of_mem_sigma` 経由で G の Sylow に realize)。

**証明計画 (統一エンジン + 2 branch)**:
- **統一エンジン** `eq_singleton_of_uniquelyMaximal_le` (高信頼, ~25行): `IsUniquelyMaximal U ∧ U≤C_G(X) ∧
  U≤M (M coatom) ∧ C_G(X)<⊤ ⟹ ℳ(C_G(X))={M}`。`IsUniquelyMaximal.of_le_of_lt_top` で C_G(X) も
  uniquely-maximal 化 → `eq_of_isCoatom_of_le` で unique maximal = M → `Set.eq_singleton_iff_unique_mem`。
  [Finite (Subgroup G) 要 (of_le_of_lt_top)、G Finite から instance]。
- **C_G(X)<⊤** (中信頼): X≠⊥ + Z(G)=⊥ (minimal simple) ⟹ X⊄Z(G) ⟹ C_G(X)≠⊤。
- **branch r(C_P(X)) ≥ 3** (witness = rank-3 elem-ab A ⊆ C_P(X)): A は X を centralize (A⊆C_P(X)) ⟹ A≤C_G(X);
  A≤M (A⊆P⊆M_σ⊆M); `uniquenessTheorem hG (A<⊤) (2≤rank A) (3≤rank A ∨ _)` で IsUniquelyMaximal A。
  要: pRank≥3 ⟹ elem-ab rank-3 抽出 (S12_Corollary1216 の rank-2 helper を rank-3 へ一般化 or `exists_*`) +
  rank vs pRank 変換 (elem-ab order p³ ⟹ rank=3)。中信頼。
- **branch r(C_P(X)) ≤ 2** (witness = P nonabelian, X≤Z(P)) — **hard, 3 sub-args**:
  1. `p∉idealPrime G` (β(G)): r(P)≤2 なら自明 (ideal は r_p(G)≥3 要); r(P)≥3 なら Cor 5.4
     (`narrow_iff_exists_card_prime_centralizer_pRank_le_two`) で P narrow ⟹ not ideal。
     ⟹ `p∉beta M` (beta は ideal 要) ⟹ hcase の β disjunct 消えて **X⊆M_σ' 確定**。
  2. **X⊆P'** via Lemma 10.8(c) (`derived_msigma_hasNormalPComplement_of_not_mem_beta`): M_σ=N⋊P
     (N=O_{p'} normal p-complement) ⟹ M_σ'∩P=P' の射影論法 (HasNormalPComplement API 要)。**fiddly**。
  3. **r(P)≤2**: 背理法 r(P)≥3 ⟹ P narrow (Cor 5.4) ⟹ Thm 5.3(d) (`narrow_centralizer_decomp`) の
     conjunct `S⊓commutator R=⊥` を S=X で適用 ⟹ X∩P'=⊥、但し X⊆P'≠⊥ ⟹ X=⊥ 矛盾。⟹ r(P)≤2。
     その後 `sylow_structure` (b) (公開, `(S10.sylow_structure hG P).2.1 hrank`) で P abelian (⟹P'=⊥⟹X=⊥矛盾)
     or 中心積 P₁*P₂ (P₁ exp-p extraspecial p³, P₂ cyclic, Ω₁P₂=Z(P₁))。後者で **P'=P₁'=Z(P₁)≤Z(P)**
     (IsCentralProduct/IsExpPExtraspecial API で derived=center 抽出) ⟹ X⊆P'≤Z(P) ⟹ P≤C_G(X), P nonabelian。
     ⟹ Thm 12.13 で IsUniquelyMaximal P。**中心積→P'≤Z(P) 抽出が最 fiddly**。

**規模/risk**: ~350-450 行。r≤2 branch の (2) normal-p-complement 射影 + (3) 中心積 center 抽出が
API-fit 未検証で最大 risk。`narrow_centralizer_decomp` の S⊓R'=⊥ conjunct で r(P)≤2 が出る点は確認済。
**12.14 完成 + S12_E:58 削除で §12 STOP** (S12_E 残 sorry: L83/L96 = 12.16 forward-decl のみ → HUB/Lane G 調整事項)。

---

## session 23 cont. (2026-06-14, Lane F): Cor 12.14 — engine+r≥3 完成、r≤2 を精密 plan 化

**ユーザー裁可**: 12.14 完全実装 (推奨) を選択 → 新 leaf `S12_Corollary1214.lean` 着手。

**✅ 完成・ビルド green (leaf build OK; ただし root/AxiomsCheck 未配線 = 意図的)**:
- `eq_singleton_of_uniquelyMaximal_le` (統一エンジン): `IsUniquelyMaximal U ∧ U≤C_G(X) ∧ U≤M ∧ C_G(X)<⊤
  ⟹ ℳ(C_G(X))={M}` (`of_le_of_lt_top` + `eq_of_isCoatom_of_le` + `Set.eq_singleton_iff_unique_mem`)。
- 本体 setup: `|X|=p`/`X≠⊥`/`IsPGroup p X` (`mem_elemAbelianOfRank`+`IsElementaryAbelian.isPGroup`);
  Sylow `S:Sylow p G` with `X≤S≤M` (`isSylow_sylowMap_of_mem_sigma` + `X.subgroupOf M ≤ PM`)。
- `center G = ⊥` (simple+notSolvable idiom) → `C_G(X)<⊤` (`centralizer_eq_top_iff_subset`)。
- **r(C_P(X))≥3 branch** (`CPX:=C_G(X)⊓S`, `3 ≤ pRank ↥CPX p`): witness=CPX 自身。
  `pRank_le_rank` で `3≤rank ↥CPX`、`CPX<⊤` (≤M<⊤)、`Ch2.S09.uniquenessTheorem` で `IsUniquelyMaximal CPX`。

**⚠ WIP: r≤2 branch (`pRank ↥CPX p ≤ 2`) = 残 1 sorry**。leaf は**未コミット**で worktree に保持
(hub auto-merge への sorry 波及回避; 完成時に net -1 sorry [leaf 0 + S12_E:58 削除] で commit)。

**r≤2 branch 精密 plan (6 step, テンプレ+補題すべて特定済)**:
1. `p ∉ idealPrime G`: case `pRank ↥S p`。≤2 ⟹ `pRank G p ≤2` (`pRank_sylow_eq S`) ⟹ ¬ideal。
   ≥3 ⟹ `narrow_iff_exists_card_prime_centralizer_pRank_le_two` で S narrow (X' 経由)
   ⟹ `narrow_iff_exists_maximalElementaryAbelian_card_prime_sq` で ∃ maximal-elem-ab-p² ⟹ ¬ideal。
2. `p ∉ beta M` (beta=ideal 要求ゆえ 1 から)。
3. hcase + 2 ⟹ `X ≤ derivedInG (Msigma M)` (β disjunct 消滅)。
4. **[from-scratch ~50-70行]** `X ≤ derivedInG S` (=P'): 10.8(c)
   `derived_msigma_hasNormalPComplement_of_not_mem_beta hG hM hpπ hpβ` の Msigma 側 ⟹
   `oPiCore_isComplement_of_hasNormalPComplement` (S04g_Thm418, ↥(Msigma M) 内) の quotient 射影で
   `derivedInG(Msigma M)∩S = S'` (Dedekind: `M_σ'·O = S'·O` mod O_{p'}=O_{p'}(Msigma M))。
5. `rank ↥S ≤ 2`: 背理法 `pRank ↥S p ≥3` ⟹ S narrow (Cor 5.4) ⟹ `narrow_centralizer_decomp`
   (X' order p, `centralizer_subgroupOf_inf_eq hXS`+`pRank` iso で hSrank=hle) の conjunct
   `X' ⊓ commutator ↥S = ⊥`、但し X⊆P'⟹X'≤commutator ↥S (`derivedInG_eq_commutator`)⟹X'≠⊥ 矛盾。
6. Cor 10.7(b) `(S10.sylow_structure hG S).2.1 (rank≤2)`: abelian (⟹S'=⊥⟹X=⊥矛盾) or 中心積 P₁*P₂。
   **[from-scratch ~50-80行]** witness=P₁ (extraspecial, nonabelian via `IsExtraspecial` center_card=p<p³):
   `X ⊆ derivedInG S` + 中心積 class-2 (`⁅S,S⁆ ⊆ centralizer P₁`、`IsExtraspecial.commutator_eq_center`
   `⁅P₁,P₁⁆=Z(P₁)` + `IsCentralProduct.commutator_eq_bot`/`le_centralizer_*`) ⟹ X⊆centralizer P₁
   ⟹ P₁≤C_G(X)。Thm 12.13 `nonabelian_pgroup_isUniquelyMaximal` で `IsUniquelyMaximal P₁`。

**from-scratch 2 件の注意**: (4) `CentralProduct.lean` に commutator 補題無し / mathlib に commutator-of-sup
分配律無し (`commutator_le` の ∀-形のみ) ⟹ 中心積の `⁅S,S⁆⊆⁅P₁,P₁⁆` は P₂≤Z(S) 経由 quotient or
element 計算で自作。(4) の 10.8c 射影も `HasNormalPComplement` の quotient iso から組立。
S04f_Blackburn に中心積-derived 既製補題が無いか先に確認推奨。テンプレ: narrow 適用 = `S10_LocalLemmas.lean:430-590`。

**進捗更新 (session 23 cont., r≤2 steps 1-3 着地)**: leaf に bridge helper `centralizer_subgroupOf_inf_eq` +
r≤2 の **steps 1-3 (narrow scaffolding) 実装済・ビルド green** (`hnotideal`/`hpβ`/`hXMσ'`)。残 1 sorry =
**steps 4-6 のみ** (2 from-scratch proof)。step 4 の `S ⊓ Mσ' = S'` は商 `↥Mσ/K` 経由が確定:
`MonoidHom.map_commutator` で `commutator(↥Mσ/K) = (commutator ↥Mσ).map q = (⁅S,S⁆).map q`
(S が ↥Mσ/K に全射, K=ker)、`comap_map = ⊔ ker` で `⁅Mσ,Mσ⁆ ≤ ⁅S,S⁆⊔K`、Dedekind + K∩S=⊥ で
`(⁅S,S⁆⊔K)⊓S = ⁅S,S⁆`。あるいは `focalSubgroupTheorem`(Ch05:1369) + focal=P' under
`controlsOwnFusion_of_hasNormalPComplement`(Ch05:1684) 経由も可。step 6 中心積 class-2 は
S=P₁⊔P₂ を `Subgroup.coe_mul_of_left_le_normalizer_right` で積に分解→commutator element 計算
(`⁅ab,cd⁆=⁅a,c⁆` for b,d∈P₂ central)→`⁅S,S⁆=⁅P₁,P₁⁆=Z(P₁)`(`IsExtraspecial.commutator_eq_center`)。
leaf は引き続き未コミット保持。

**✅✅✅ COMPLETE (session 23 cont., 2026-06-14)**: **BG Cor 12.14 完全証明** — `S12_Corollary1214.lean`
の `S12.Cor1214.maximalContaining_centralizer_eq_singleton` が **sorry-free・axiom-clean**
(full build 3803 jobs green / AxiomsCheck OK = 3 axioms 全 allowlist)。root + AxiomsCheck 配線済、
S12_E:53 forward-decl 削除(comment pointer 化)⟹ **§12 実 sorry 3→2**(残 = S12_E:78/91 の
Cor 12.16(a)(b) 一般 hYpi forward-decl のみ = HUB/Lane G re-point 調整事項、Lane F の証明作業外)。

全 6 step が予定通り着地:統一エンジン `eq_singleton_of_uniquelyMaximal_le`(`of_le_of_lt_top`+
`eq_of_isCoatom_of_le`)+ setup(X⊆M_σ⊆Sylow S、共役不要)+ `C_G(X)<⊤`(center=⊥)+
**r(C_P(X))≥3**: witness=C_P(X) 自身(`pRank_le_rank`+Uniqueness Thm)+
**r(C_P(X))≤2**: ¬ideal(Cor 5.4 narrow)→ p∉β(M)→ X⊆M_σ'→ **X⊆S'**(10.8c: 商 ↥M_σ/K で
`MonoidHom.map_commutator`+手動 Dedekind `mem_sup_of_normal_right`)→ rank S≤2(narrow+Thm 5.3(d)
の `S⊓R'=⊥` × X⊆S'≠⊥ 矛盾)→ 中心積 Cor 10.7(b)(公開 `sylow_structure.2.1`)→ witness=P₁
(extraspecial nonabelian、`⁅S,S⁆=⁅P₁,P₁⁆=Z(P₁)⊆C_G(P₁)` を中心積分解 `coe_mul_of_left_le_normalizer_right`
+ central-commutator 簡約 keyA/keyB で、`IsExtraspecial.commutator_eq_center`)→ Thm 12.13。

**再利用知見**: (1) narrow を実 Sylow に適用するテンプレ = `S10_LocalLemmas:430-590` + bridge
`centralizer_subgroupOf_inf_eq`(leaf に複製)。(2) `pRank_eq_zero_of_isPGroup_of_ne_prime` /
`derivedInG_eq_commutator` は S09/S10 で private → leaf に複製。(3) 中心積 commutator 分配律は
mathlib/CentralProduct に無く、`Subgroup.coe_mul_of_left_le_normalizer_right` で `↑S=↑P₁*↑P₂` 分解
→ `⁅ab,cd⁆=⁅a,b⁆`(central a₂,b₂ を keyA/keyB で落とす)で自作。(4) `⁅H,K⁆≤K` は K 正規要 →
自己交換子 `⁅S,S⁆≤S` は `commutator_le.mpr` で。(5) 要素 commutator は `open scoped commutatorElement`。

**▶ Lane F §12 = 完了(STOP)**。次任務(§14 想定)はユーザー/HUB が再判断。leaf は本 commit で tracked 化。

---

## session 23 cont.² (2026-06-14, Lane F): Cor 12.16 一般形 → §13 de-axiom 完了 (2 sorry discharge)

**HUB 指示の訂正対応**: §12 残 2 sorry (S12_E の Cor 12.16(a)(b) 一般 hYpi forward-decl) は
「HUB/Lane G 調整事項」でなく **Lane F の配線タスク**だった。`S13_Lemma131:424/560`
(bg-s12 tree 内、main merge 経由で存在) が `S12.sigma_subgroup_pRank_normalizer_le_one` /
`…not_mem_primeFactors_derived_of_tau1` を一般形で cite しており、bg-s12 build で load-bearing。

**✅✅✅ 2 sorry discharge 完了** (full build 3803 green, AxiomsCheck OK 両一般形 3 axioms 全 allowlist):
- **一般 σ(M)-subgroup 形を `S12_Corollary1216` の `namespace …S12` に PROVEN 実装** —
  `sigma_subgroup_pRank_normalizer_le_one` / `sigma_subgroup_not_mem_primeFactors_derived_of_tau1`。
  q-group 形 (`Cor1216.pRank_normalizer_le_one` 等) へ **characteristic `q`-subgroup `O_q(Y)`** で reduce:
  helper `exists_char_qSubgroup` (Y solvable [< ⊤] nontrivial ⟹ `F(Y)≠⊥` [`Ch01.fitting_ne_bot_of_solvable_nontrivial`]
  ⟹ ∃ q∈primeFactors|F(Y)|, `O_q(F(Y))≠⊥` [`opiCoreInG_singleton_fittingInG_ne_bot_of_mem_primeFactors`]
  `≤ O_q(Y)` [`opiCoreInG_fittingInG_le_opiCoreInG`]; `O_q(↥Y)` characteristic [`oPiCore.characteristic` instance]
  ⟹ `N_G(Y) ≤ N_G(O_q(Y))` [`AppB.normalizer_le_normalizer_map_of_characteristic`]; q∈σM [hYpi q | |F(Y)| | |Y|])。
  (a) は q-group 形を `O_q(Y)` に適用 + `pRank_le_of_injective` で `H⊓N(Y)≤H⊓N(O_q(Y))` lift;
  (b) は `derivedInG_mono` + `card_dvd` で primeFactors 包含 lift。
- **S12_E の forward-decl 2件削除** (comment pointer 化) ⟹ §12 **完全 sorry-free**。
- **`S13_Lemma131` の import を `S12_E`→`S12_Corollary1216` に差替** ⟹ cite (`open …S12` で unqualified)
  が新一般形 (proven) に解決 ⟹ §13 Lemma 13.1 / Cor 13.2 の Cor 12.16 依存が **unconditional 化**
  (S13_Lemma131/S13_Corollary132 build green; §13 の残 sorry は S13_PrimeAction/S13_Theorem134 の
  Lane G 別件で本件無関係)。AxiomsCheck の §13 de-axiom コメント更新 + 一般形2件 assert 追加。

**▶ Lane F §12 = 完全完了** (12.1-12.18 + Thm 12.12 + 12.13/12.14/12.15/12.16 すべて sorry-free)。
次任務 (§14 想定) はユーザー/HUB 再判断。再利用知見: solvable subgroup の char q-subgroup = `O_q(Y)`
(F(Y) 経由で nontrivial 化, `oPiCore.characteristic` instance, `normalizer_le_normalizer_map_of_characteristic`)。
