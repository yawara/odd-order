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
- ⏳ `centralizer_ne_bot_of_nontrivial_kernel` (Lemma 3.3 本体, sorry) — **残 = partition identity のみ**

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

## §11 適用 (Thm 11.3)
`M_σ ⋊ ⟨a₀^g⟩` (a₀^g prime order p, C_{M_σ}(a₀^g)=1, M_σ solvable=M の部分群)。
`IsFrobeniusGroup` を構成 (`of_centralizer_kernel_le` 等) → Thm 3.7 → `M_σ` nilpotent。

## 注意
- `S04e_GorThm37` の Thm 3.7 は **Gorenstein 本** の別物 (special p-group)。本件は **BG** Thm 3.7。
- 多 commit 想定: (1) Lemma 3.3 → (2) same-prime → (3) Thm 3.7 → (4) Thm 11.3。各 build-green 単位 commit。
