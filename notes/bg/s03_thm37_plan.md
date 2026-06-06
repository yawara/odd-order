# BG Thm 3.7 形式化プラン (Frobenius kernel nilpotency, prime complement)

**目的**: BG Thm 11.3 (`Msigma_isNilpotent`) を unblock する。Thm 3.7 = 「solvable odd `G=KR`,
`K⊲G`, `R` = prime order `p` complement, `C_K(R)=1` ⇒ `K` nilpotent」(mmd L1199)。
配置 = `OddOrder/BG/Ch1_Preliminary/S03_FrobeniusActions.lean` (§3, 既存 429 行に追記)。

## 既存インフラ (調査済 2026-06-01)

- **Frobenius API** (`Isaacs/Ch06_FrobeniusActions/`):
  - `IsFrobeniusGroup G N A` (FrobeniusGroup.lean:240): `isNormal`/`isComplement` (`IsComplement' N A`)/
    `ne_bot_*`/`conj_frobenius` (∀a∈A≠1, ∀n∈N≠1, ana⁻¹≠n)。
  - `kernel_eq_notConjugateSet` (471): `K = notConjugateSet A` (= G ∖ ⋃ conjugate(A)∖1)。
  - `trivialIntersection` (357), `disjoint_kernel_conjugate_complement` (553)。
  - **partition (Wielandt の核)**: `FrobeniusActionTI.lean` の `notConjugateSet`/`TI_conjugate`/
    `nonidentitySigmaTo` (787, 非単位元 ↔ (conjugate-part, 非単位元) の bijection)/
    `parts_card_mul_sub_one_eq_card_sub_one` (845)/`card_notConjugateSet_eq_index` (532)。
  - `coprime_card_kernel_complement` (287): odd order ⇒ `(|K|,|R|)=1` 自動。
- **chief factor engine** (`GroupTheory/ChiefFactor.lean`):
  - `isNilpotent_of_chief_factor_centralization` (430): `(∀i, ⁅K, chiefSeriesInside K i⁆ ≤ chiefSeriesInside K (i+1)) ⇒ IsNilpotent ↥K` = **BG Prop 1.2 逆**。
  - `chiefSeriesInside`/`maxProperNormalOrBot`/`isChiefFactor_chiefSeriesInside`/
    `IsChiefFactor.commutator_le_of_isSolvable` (370, solvable chief factor ⇒ elementary abelian)/
    `chiefFactorCentralizer` + `le_iff_commutator_le`。
- **rep theory** (mathlib `RepresentationTheory.Basic`/`.Maschke` + repo `RepresentationTheory/PGroupFixedVector.lean`, `EigenspaceUnderCyclicAction.lean`, `OperatorMaschke.lean`)。

## 欠落 (これから建てる)

### 進捗 (2026-06-01, `S03b_Lemma33.lean`, build-green)
- ✅ `groupSumMap ρ H = ∑_{h:H} ρ ↑h` (averaging endomorphism)
- ✅ `fixed_apply_groupSumMap`: `(∑_{h∈H} ρ h) v` は `H`-不動 (左乗 `Equiv.mulLeft` で reindex)
- ✅ `trivial_of_groupSumMap_eq_card_smul`: `groupSumMap ρ K = |K|•id ⇒ K 自明` (`smul_right_injective`)
- ✅ `groupSumMap_conjugate_eq_zero`: `C_V(R)=0 ⇒ groupSumMap ρ (conj x•R) v = 0` (+`rep_apply_apply`/`mulAut_smul_eq_map`)
- ✅✅ **`centralizer_ne_bot_of_nontrivial_kernel` (Lemma 3.3 本体) 完成・sorry-free** (commit e529f11)。
  partition 組立 = `frobeniusGroup hFrob` の `nonidentitySigmaTo` bijection + `Fintype.sum_sigma` で
  `∑_{g≠1} ρ g v` を parts 上に reindex → kernel part = `groupSumMap ρ K v − v`、各 conjugate part = `−v`
  (計 |K| 個) → `∑_{g:G} ρ g v = 0` (G-fixed⊆R-fixed=0) で `groupSumMap ρ K v = |K|•v` → endgame。
  **必要だった API 追加**: `Ch06.SubgroupPartition.mem_frobeniusGroup_parts` (commit 08df6a6, 非kernel part=Rの共役を public 化)。

**✅ Lemma 3.3 (§3B) DONE。残り BG Thm 3.7 = (2) same-prime case + (3) |K|-induction。**
- (2) same-prime: infra 確認済 (`PGroupFixedVector.lean` `IsPGroup.invariants_ne_bot`/`exists_fixed_vector_ne_zero`)。
  **最難の未整備ピース = chief factor を irreducible `𝔽_q[Ḡ]`-module へ橋渡し** (elementary abelian ≃ 𝔽_q ベクトル空間 + 共役作用 ≃ Representation + minimal normal ≃ irreducible)。explore 済 (S04e/同探索ログ参照)。
- (3) induction: Lemma 3.1/3.2 (S03 済) + Lemma 3.3 (済) + Prop 1.2 (`ChiefFactor.isNilpotent_of_chief_factor_centralization` 済) + chief factor 機構で組立。

### chief-factor-as-module bridge — 詳細ロードマップ (2026-06-01 探索済, 配置案 = 新 `OddOrder/GroupTheory/RepresentationTheory/ChiefFactorModule.lean`)

**既存 infra (proven, sorry-free)**:
- `IsElementaryAbelian.zmodModule` (`GroupTheory/PRank.lean:86`): elem-abelian `q`-群 → `Module (ZMod q) (Additive G)`。
- mathlib `AddCommGroup.zmodModule` (`Algebra/Module/ZMod.lean:44`, `n•x=0 ∀x → Module (ZMod n)`) + `QuotientAddGroup.zmodModule` (:53)。
- `IsChiefFactor.isMinimalNormal_map_quotient` (`ChiefFactor.lean:318`): chief factor → `Ch02.IsMinimalNormal (U.map (mk' V))`。
- `IsChiefFactor.commutator_le_of_isSolvable` (`ChiefFactor.lean:370`): solvable chief factor `⁅U,U⁆≤V` (⇒ abelian)。
- `invariantQuotientMulDistribMulAction` (`Ch06/FrobeniusActionTI.lean:136`): 不変正規部分群上の商に `MulDistribMulAction` を lift。
- mathlib `Representation.ofModule` (`RepresentationTheory/Basic.lean`) + `Subrepresentation` (`Subrepresentation.lean`) + `IsIrreducible` = `IsSimpleModule k[G] ρ.asModule` (`Irreducible.lean`)。

**未整備 (build, 依存順)**:
1. (短) chief factor 商を `ZMod q`-module 化: `commutator_le_of_isSolvable` で abelian + `isPGroup`/exponent q → `zmodModule`。
2. (中) 共役作用 → `(ZMod q)[Ḡ]`-module (ConjAct/`invariantQuotientMulDistribMulAction` 経由) → `Representation.ofModule`。`Representation.ofDistribMulAction` は **無い** ので `k[G]`-module を経由して `ofModule`。
3. (**最難 ~50-70行**) **irreducible**: 不変部分 module ↔ `V` と `U` の間の正規部分群 の lattice duality (`map`/`comap` via `mk' V`)。`isMinimalNormal_map_quotient` で proper 無 → `IsIrreducible`。**最も load-bearing**。
4. (短) Lemma 3.3 へ wire: `S03b.centralizer_ne_bot_of_nontrivial_kernel` に食わせる wrapper。

**注意**: 探索 agent の signature は近似 (要 build 検証)。`Representation.ofModule` の `[Module k[G] M]` 構築が gate#2 の核。

### 🆕 2026-06-06: bridge は大幅に簡素化 (gate#3 irreducibility 不要)

旧ロードマップの「gate#3 = irreducible (最難 ~50-70行)」は **coprime case には不要**。Lemma 3.3
(`centralizer_ne_bot_of_nontrivial_kernel`) は `V` の既約性を要求せず、任意の `Representation F G V`
で動く。さらに **`Representation.ofDistribMulAction` は mathlib に存在する** (旧注記「無い」は誤り、
`RepresentationTheory/Basic.lean:429`)。よって bridge は ~2 instance に縮小:
- `OddOrder/GroupTheory/RepresentationTheory/ElementaryAbelianRepresentation.lean` (新規, build-green):
  - `Additive.instDistribMulActionOfMulDistribMulAction`: `MulDistribMulAction G M` (CommGroup M) ⟹
    `DistribMulAction G (Additive M)` (mathlib は acting-side Additive のみ transport するので acted-on
    側を補う)。
  - `instSMulCommClassZModOfDistribMulAction`: 任意の `ZMod n`-module + `DistribMulAction G` で
    `SMulCommClass G (ZMod n) A` (additive 写像は `ZMod.map_smul` で自動 ZMod-線形)。
  - これで `Representation.ofDistribMulAction (ZMod p) G (Additive M)` が elem-abelian chief factor で
    elaborate する (example で検証済)。
- **残 coprime case** = (a) Lemma 3.3 の対偶 (`C_V(R)=0 ⟹ K acts trivially`, S03b に追加), (b) chief factor
  X/Y に `MulDistribMulAction G` を `invariantQuotientMulDistribMulAction` 等で載せる, (c) `C_V(R̄)=1`
  (coprime FPF, `C_K(R)=1` から) を供給して結線。→ その後 |K|-induction。

### 進捗 (2026-06-01, `S03c_Thm37.lean`)
- ✅✅ **same-prime case 完成・sorry-free** (commit b0acb75): `commutator_eq_bot_of_normal_pgroup_minimalNormal`
  (正規 q-部分群 K が minimal-normal q-部分群 V を中心化)。`K⊔V` の中心と V の交わり
  (`GroupTheory.exists_mem_center_of_normal_ne_bot`, private→public 化) + minimality。
  **module/irreducibility を完全回避** (BG の O_q ルートより簡潔, 群論のみ)。
- ⏳ **coprime case** = Representation bridge + Lemma 3.3。**bridge の核 API 判明**:
  `AddMonoidHom.toZModLinearMap n (f : M →+ M₁) : M →ₗ[ZMod n] M₁` (`Algebra/Module/ZMod.lean:81`,
  ZMod-module 間の加法 hom は自動で ZMod-線形)。よって bridge =
  「chief factor (elem-abelian s-群) の `Additive` を `zmodModule` で ZMod s-module 化 →
  共役 `MulDistribMulAction G` から各 g の `AddMonoidHom` を `toZModLinearMap` で線形化 →
  `G →* Module.End (ZMod s) (Additive ·)` を MonoidHom として組む (map_one/map_mul)」。
  chief factor の群モデル (`↥U⧸V.subgroupOf U` or `U.map(mk' V)`) + G-共役作用 setup が残る fiddly 部分。
  → 構成後 `S03b.centralizer_ne_bot_of_nontrivial_kernel` に C_V(R̄)=0 と共に食わせる。
- ⏳ **|K|-induction** (Thm 3.7 本体): L=maxProperNormalOrBot K で K̄=K/L を elem-abelian 化 →
  各 chief factor V (X⊆K) に same-prime/coprime dichotomy → Prop 1.2 で nilpotent。

**残 partition の具体ルート (vector-level, MonoidAlgebra 係数計算を回避)**:
`frobeniusGroup h : SubgroupPartition G` の `.parts = insert N (conjugatesFinset A)` (=K ∪ Rの共役;
`frobeniusGroup` def @FrobeniusGroup.lean:619, `parts_card = |K|+1`)。
`nonidentitySigmaTo_injective/_surjective` (FrobeniusActionTI:794/816) から `Equiv`:
`{g:G//g≠1} ≃ Σ (X∈parts) {x∈X//x≠1}`。これで
`groupSumMap ρ ⊤ v = ∑_{g:G} ρ g v = v + ∑_{g≠1} ρ g v = v + ∑_{X∈parts}(groupSumMap ρ X v − v)
 = (∑_{X∈parts} groupSumMap ρ X v) − |K|•v` (parts 数 |K|+1)。
仮定 `C_V(R)=0` ⇒ `groupSumMap ρ ⊤ v = 0` (⊤-不動⊆R-不動=0) かつ各共役部分 `C=conj g•R` で
`groupSumMap ρ C v = 0` (C_V(C)=ρ(g)(C_V(R))=0)。ゆえ `0 = groupSumMap ρ K v − |K|•v`、
`groupSumMap ρ K v = |K|•v` → `trivial_of_groupSumMap_eq_card_smul` で K 自明、`hKnt` と矛盾。
最重 step = `∑_{g≠1} f g = ∑_{X∈parts}∑_{x∈X,x≠1} f x` の Σ-type reindex (Equiv.sum_comp/Fintype.sum_bijective)。

### (1) Lemma 3.3 (mmd L845, Wielandt) — **crux**
「`G=KR` Frobenius, `V` over `F` with `char F ∤ |K|`, `K` が `V` に非自明作用 ⇒ `C_V(R)≠0`」。
証明: `Representation F G V` → `ρ.asAlgebraHom : MonoidAlgebra F G →ₐ Module.End F V`。
- helper: 有限部分群 `H` で `σ_H := ∑_{h∈H} single h 1`、`ρ(σ_H) v ∈ fixedPoints H` (reindex `g•∑=∑`)。
- 仮定 `C_V(R)=0` ⇒ `ρ(σ_{R^g})=0` 全 g (conjugate) かつ `ρ(σ_G)=0` (`C_V(G)⊆C_V(R)=0`)。
- Frobenius partition: `σ_G = σ_K + ∑_{x∈K} σ_{R^x} − |K|•1` (kernel_eq_notConjugateSet + nonidentitySigmaTo)。
- ⇒ `0 = ρ(σ_K)v − |K|•v` ⇒ `|K|v = ρ(σ_K)v ∈ C_V(K)`; `|K|≠0 in F` ⇒ `V=C_V(K)` ⇒ K trivial。対偶。
- ~200 行。MonoidAlgebra の partition identity が最重。

### (2) same-prime case
「正規 `q`-部分群 `K̄ ⊴ Ḡ` が irreducible `F_q[Ḡ]`-module `V` (同標数) に自明作用」
(= G Thm 3.1.3 substitute)。`PGroupFixedVector.lean` の `IsPGroup` 不動点 (≠0) + irreducible ⇒ 全体。

### (3) Thm 3.7 本体 (induction on `Nat.card K`)
`L = maxProperNormalOrBot K` (G-normal, ⊂ K) → `C_L(R)⊆C_K(R)=1` → IH (`LR`, |L|<|K|) で `L` nilpotent →
`L⊆F(K)`。`Ḡ=G/L`: Lem 3.1/3.2 で Frobenius。各 chief factor `V=X/Y` (X⊆K): L が centralize (Prop 1.2)
⇒ G,Ḡ irreducible on V; G solvable ⇒ K̄,V elementary abelian; 同素数 q ⇒ (2); coprime ⇒ `C_V(R̄)=1`+Lem 3.3。
最後に Prop 1.2 (`isNilpotent_of_chief_factor_centralization`) で `K` nilpotent。

## 🆕 2026-06-06 (続): Thm 3.7 本体 induction — 精密 roadmap (BG mmd L1199-1219 再読、全 leaf dep 確認済)

BG 原文を再読し proof 構造を確定。**重要訂正: Lemma 3.3 の "kernel" は K̄=K/L (K でない)**。coprime case は
|K̄| と |V| が互いに素な場合で、そこで `s ∤ |K̄|` が成立 (chief factor V が K に s-部分群で入る ⟹ s∣|K| とは無矛盾;
Lemma 3.3 が要求するのは s∤|K̄|=|K/L|)。よって既存 `kernel_acts_trivially_of_coprime_fixedPointFree` は正しく、
適用時の kernel を K̄ にすればよい。

**leaf dep 全確認済 (build 済・命名確定)**:
- (3.39) `(|K|,|R|)=1` = **`OddOrder.Isaacs.Ch06.coprime_card_kernel_complement hFrob`** (Frobenius なら自動、Sylow 論証不要)。
- Lemmas 3.1/3.2 (Ḡ=G/L Frobenius) = **`S03.quotient_isFrobeniusGroup_of_le_kernel_of_{centralizer,fixedPoint_lift,coprime_zpowers}`**。
- Prop 1.2 = **`ChiefFactor.isNilpotent_of_chief_factor_centralization`** (`∀i ⁅K, chiefSeriesInside K i⁆ ≤ chiefSeriesInside K (i+1)` ⟹ K nilpotent; chiefSeriesInside は **G-chief-factor** の系列、確認済)。
- same-prime = **`S03c.commutator_eq_bot_of_normal_pgroup_minimalNormal`** (G/Y で X/Y minimal normal に適用)。
- coprime = **`S03c.kernel_acts_trivially_of_coprime_fixedPointFree`** (kernel=K̄)。
- chief factor abelian = **`IsChiefFactor.commutator_le_of_isSolvable`**; "K centralizes V" ⟹ ⁅K,X⁆≤Y = **`chiefFactorCentralizer.commutator_le_of_le`** (K ≤ `chiefFactorCentralizer X Y`)。
- chief factor 商作用 infra = **`Ch06.invariantQuotientMulDistribMulAction (M) (hM : ∀a m∈M, a•m∈M) : MulDistribMulAction A (N⧸M)`**。

**残 GLUE sub-lemma (次イテレーションで1つずつ)**:
- **(A) normal-nilpotent-centralizes-G-chief-factor** = 「L⊴G nilpotent (⊆F(G)) は G の chief factor を centralize」。BG の "By (3.40) and Prop 1.2, L centralizes V"。solvable 群の標準事実 (F(G)=∩ chief factor centralizer) だが **repo に無さそう → 要実装** (最重 glue)。
- **(B) chief-factor MulDistribMulAction plumbing** = Ḡ (or ConjAct) を V=X/Y に `invariantQuotientMulDistribMulAction` で載せ、`hM.zmodModule` で `[Module (ZMod s) (Additive V)]` を供給 → coprime case 適用可能に。
- **(C) induction skeleton** = `Nat.card K` 上の強帰納 (L=maxProperNormalOrBot K, LR への restriction で C_L(R)=1+Frobenius, IH→L nilpotent→L⊆F(G)); 各 chief factor で same-prime/coprime dichotomy (G solvable から elem-abelian 抽出 + 素数比較) → Prop 1.2。

## ✅ 2026-06-06 RESOLVED → coprime-branch conclusion landed (778c464)

**解決**: CommGroup-on-quotient diamond は **小修正**で解消 — 適用側で標準 `Group` を再利用して
`letI : CommGroup (↥X ⧸ Y.subgroupOf X) := { (inferInstance : Group _) with mul_comm := hVelem.comm }`
と注入(defeq-clean、diamond 無し)。`inferInstance` 単体合成が失敗していたのが原因で、refactor は不要だった。
descent smul の rw は subtype 強制で構文不一致 → goal 側を `rw [← mulDistribMulActionQuotientOfTrivial_smul_mk hL g v]`
で書き換えて defeq close。結果 **`coprime_kernel_le_chiefFactorCentralizer` (S03c, 778c464) build-green**。

**残り = (C) induction のみ**: (i) ~~coprime conclusion~~ ✅DONE, (ii) **FPF 導出 `C_V(R̄)=1`**(C_K(R)=1+coprime-action),
(iii) **G/L Frobenius 構成**(`quotient_isFrobeniusGroup_of_le_kernel_of_*`), (iv) **elem-abelian 抽出**(chief factor),
(v) **|K|-強帰納 + LR restriction + same-prime/coprime dichotomy + Prop1.2 組立**, (vi) **Thm 11.3** `Msigma_isNilpotent`。
same-prime 分岐も (C) 内で `commutator_eq_bot_of_normal_pgroup_minimalNormal` を同様 model 経由で結線要。

### (旧 BLOCKER 記録, 参考)

glue(A)+(B) は全 landed・build-green (commits a39c26f..ee9afa4, 10 本; model-bridge `chiefFactorConjAction_smul_eq_self_iff_mem` 7dd0166 が最後)。次の **coprime-branch conclusion** (`coprime_kernel_le_chiefFactorCentralizer`) を組もうとして **instance 設計の壁**:

- coprime case `kernel_acts_trivially_of_coprime_fixedPointFree` は `[CommGroup M]` を要求。
- chief factor `↥X ⧸ Y.subgroupOf X` は標準では **`Group` のみ** (可換性は `hVelem.comm` = Prop)。`letI : CommGroup := inferInstance` は **synthesize 失敗** + 仮に入れても標準 `Group` instance との **One/DivisionMonoid diamond** (`Group.toDivisionMonoid` vs `CommGroup.toDivisionCommMonoid.toDivisionMonoid`) で `1`・action が型不一致 (実測 3 error: 208 synth fail, 218/222 One mismatch)。
- PRank `IsElementaryAbelian.zmodModule` は abstract `{G}[Group G]` で `letI:CommGroup:=inferInstance` が通るが、**具体 quotient 型では通らない** (再現済)。

**解決オプション (次セッションが選ぶ)**:
- **(a) 推奨**: coprime case `kernel_acts_trivially_of_coprime_fixedPointFree` (S03c) + bridge instances (`Additive.instDistribMulActionOfMulDistribMulAction`, `instSMulCommClassZModOfDistribMulAction`, ElementaryAbelianRepresentation.lean) を **`[CommGroup M]` → `[Group M] [IsMulCommutative M]`** に refactor。`AddCommGroup (Additive M)` を IsMulCommutative から導く必要 (`Additive.addCommGroup` は CommGroup 要 → IsMulCommutative 経由の導出 or 別 instance)。committed lemma を触るので慎重に。
- **(b)** 標準 `Group` と defeq な CommGroup instance を明示構成 (canonical Group を再利用する `{ ‹Group› with mul_comm }` 形)。`IsMulCommutative → CommGroup` の正しい instance 名を特定し quotient で通るか検証。

**この壁の先の残り (C)** (未着手, 大きい): (i) coprime conclusion (上記解決後), (ii) **FPF 導出 `C_V(R̄)=1`** (C_K(R)=1 + coprime-action の固定点-in-quotient; CoprimeAction.lean 要確認), (iii) **G/L Frobenius 構成** (`quotient_isFrobeniusGroup_of_le_kernel_of_*` に正しい入力), (iv) **elem-abelian 抽出** (chief factor が elem-abelian: G solvable + `IsChiefFactor.commutator_le_of_isSolvable`), (v) **|K|-強帰納 + LR restriction + dichotomy + Prop1.2 組立**, (vi) **Thm 11.3** `Msigma_isNilpotent`。

## 🟡 2026-06-06 進捗: (C) prerequisites 3/4 landed、残 = (ii-b) FPF + (v) induction + (vi) Thm 11.3

**landed (build-green)**: coprime conclusion `coprime_kernel_le_chiefFactorCentralizer`(778c464); (iii) `frobenius_quotient_of_normal_lt_kernel`(b463229); (iv) `chiefFactor_isElementaryAbelian`(3045cca); (ii-a) `frobenius_kernel_conj_fixed_eq_one`(98dc377)。

**(ii-b) full FPF — 精密手順 (全 API 確認済、未実装)**: lemma `chiefFactor_fixedPointFree` (h:Frobenius G K R, hXK:X≤K, coprime|R||X|, solvable) ⟹ `letI := chiefFactorConjAction X Y; ∀ v, (∀r:R,(r:G)•v=v)→v=1`。
- φ := `MulAut.conjNormal.comp R.subtype : ↥R →* MulAut ↥X` (X.Normal); `(φ a) x = conj (a:G) on ↥X` (`MulAut.conjNormal_apply`: ↑= (a:G)·(x:G)·(a:G)⁻¹)。
- N := `Y.subgroupOf X` (↥X の normal subgroup)。hN_inv : `IsAInvariant φ N` — `IsAInvariant.subgroupOf` (Ch03:3106) で。
- hCop : `Coprime |↥R| |↥(Y.subgroupOf X)|` ← coprime|R||X| + `Subgroup.card_dvd_of_le`。hSolv : `IsSolvable ↥R`。
- hg_fix : `∀a:↥R, ∃n∈N, φ a x = x*n` ← v=⟦x⟧ R-fixed を `chiefFactorConjAction_smul_mk` + `QuotientGroup.eq` で。
- `coprime_fixedPoints_quotient_of_coprime_normal` (Ch04 ForwardFromCh03) → ∃c, (∀a, φ a c=c) ∧ ∃n∈N, c=x*n。
- c R-fixed (∀a:↥R, φ a c=c) ⟹ ∀r∈R, r·(c:G)·r⁻¹=(c:G) ⟹ (ii-a) `frobenius_kernel_conj_fixed_eq_one h (hXK c.2) _` で (c:G)=1 ⟹ c=1 ⟹ x=n⁻¹∈N ⟹ ⟦x⟧=1。
- **friction**: framework bridge (φ:A→MulAut vs chiefFactorConjAction MulDistribMulAction), 要素順序 (QuotientGroup.eq の a⁻¹b)、IsAInvariant.subgroupOf の引数。~9 step、複数 build cycle 見込み。

**(v) induction skeleton**: Nat.card K 強帰納 (WellFoundedLT or Nat.strong_induction), L=maxProperNormalOrBot K; L=⊥ なら K=⊥ or K自身が chief factor; L≠⊥ なら LR への restriction で C_L(R)=1 + Frobenius → IH(|L|<|K|)で L nilpotent → `nilpotent_normal_le_fitting`(L⊴G)→ L⊆F(G); Prop1.2 のため `∀i, ⁅K, chiefSeriesInside K i⁆ ≤ chiefSeriesInside K (i+1)`: chiefSeriesInside K i ≠⊥ なら chief factor V_i/V_{i+1}, elem-abelian(iv), |K̄|=|K/L| vs |V_i/V_{i+1}| 素数で same-prime[`commutator_eq_bot_of_normal_pgroup_minimalNormal`, model 経由]/coprime[`coprime_kernel_le_chiefFactorCentralizer` + (ii-b) FPF] dichotomy → `chiefFactorCentralizer.commutator_le_of_le` → ⁅K,V_i⁆≤V_{i+1} → Prop1.2 `isNilpotent_of_chief_factor_centralization`。**注: dichotomy の prime 比較 + same-prime の model 経由結線 が残課題**。

## §11 適用 (Thm 11.3)
`M_σ ⋊ ⟨a₀^g⟩` (a₀^g prime order p, C_{M_σ}(a₀^g)=1, M_σ solvable=M の部分群)。
`IsFrobeniusGroup` を構成 (`of_centralizer_kernel_le` 等) → Thm 3.7 → `M_σ` nilpotent。

## 注意
- `S04e_GorThm37` の Thm 3.7 は **Gorenstein 本** の別物 (special p-group)。本件は **BG** Thm 3.7。
- 多 commit 想定: (1) Lemma 3.3 → (2) same-prime → (3) Thm 3.7 → (4) Thm 11.3。各 build-green 単位 commit。
