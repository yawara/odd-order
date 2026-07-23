---
id: 1055
slug: isaacs-problems-campaign
title: "Isaacs 演習問題 (Problems) 形式化 campaign (scope 拡大 2026-07-22)"
created: 2026-07-22
---

# Isaacs 演習問題 (Problems) 形式化 campaign (scope 拡大 2026-07-22)

## 背景

**scope 拡大 (ユーザー裁定 2026-07-22、issue 9205 ③)**: lane a の割当 territory
(Isaacs 番号付き結果 + Pf 本文 + FeitSibley/NearFields Prop2) が全完済し、hub が
再配分をユーザーに escalate → **(E) Isaacs 演習問題 (Problems) を in-scope 化**して
lane a が形式化することに決定。従来の被覆測定 (`notes/isaacs/frontier_measured_2026_07_19.md`)
は「番号付き結果のみ」で演習を対象外にしていた ⟹ 本 campaign で演習も形式化対象に加える。

## 構造 (実測)

Isaacs FGT は各章を section (1A, 1B, ...) に分け、各 section 末に "Problems NX" として
演習を `NX.M` 形式で番号付け (例: 1A.1–1A.10, 1B.1–…, 1C.1–1C.8, 1D.1–1D.18,
1E.1–1E.8, 1F.1–…, 1G.1–…)。全 10 章で数百問。⚠ pdftotext は OCR ノイズあり
(記号・式散乱) → **statement は PDF ページ画像で確定** (Isaacs は PDF ページ = 書籍ページ + 13)。

## やること (上流優先 + 文書順)

各章の演習を section 順・番号順に形式化。置き場 = `OddOrder/Isaacs/ChNN_.../Problems*.lean`
(章ディレクトリ内の新 leaf、mathlib 互換記述名、`OddOrder.lean` 配線)。

- [ ] **Ch.1 Sylow** — 1A / 1B / 1C / 1D / 1E / 1F / 1G Problems
- [ ] Ch.2 Subnormality
- [ ] Ch.3 Split Extensions
- [ ] Ch.4 Commutators
- [ ] Ch.5 Transfer
- [ ] Ch.6 Frobenius Actions
- [ ] Ch.7 Thompson Subgroup
- [ ] Ch.8 Permutation Groups
- [ ] Ch.9 More Subnormality
- [ ] Ch.10 More Transfer

## 方針

- **番号付き結果と同じ強度**で形式化 (statement を PDF で確定 → theorem 化 → 実証明)。
- 演習が **mathlib 既存**または **repo 既存定理**で即従うものは、docstring で対応を記録
  (ラッパー方針: 純粋リネームは書かない)。
- 演習が**定義の導入のみ**のもの (例: 1A.5 が transitive action を定義) は、mathlib に既存概念が
  あれば docstring 記録、無ければ必要な範囲で定義。
- 前提インフラが repo/mathlib に無い演習は **honest な sorry-cite skeleton** を置かず、
  必要なら shared infra を先に build (claim-first)。真に blocked なら注記して次へ (文書順は維持)。
- **難易度・quick-win は着手基準でない** — 文書順で正面から。ただし 1 問で堂々巡りせず、
  genuine に blocked なら記録して先へ進み後で戻る。

## 進捗

**Ch.1 §1A** (`Ch01_Sylow/Problems.lean`、2026-07-22 着手):
- ✅ 実証明: **1A.1** (素数指数+最小性→正規) / **1A.4** (H·K=G⟹H·K^z=G + 帰結 H·H^x=G⟹H=⊤) /
  **1A.9** (|G|=pm,p>m→位数p部分群一意) / **1A.10(b)** (p群H, p∣[G:H]→p∣[N_G(H):H])。
- ✅ mathlib 対応 docstring 記録: **1A.6** (Burnside 軌道計数) / **1A.8** (Cauchy) / **1A.10(a)**
  (`fixedPointsMulLeftCosetsEquivQuotient`)。
- ✅ 実証明: **1A.2** (`card_doubleCoset_mul_card_inf_conj`: 二重剰余類 |HgK|·|K∩H^g|=|H||K|、
  H×K の両側作用 (h,k)•x=hxk⁻¹ の orbit-stabilizer)。
- ✅ 実証明: **1A.3** (`card_mul_card_inf` helper = |HK|·|H∩K|=|H||K| (1A.2 g=1) /
  `card_mul_le_card_mul_card_inf` (a)≤ / `card_mul_eq_iff_mul_eq_univ` (a)等号⟺HK=G /
  `mul_eq_univ_of_coprime_index` (b) coprime index⟹HK=G)。
- ✅ 実証明: **1A.5** (`isPretransitive_prod_iff`: G が α,β に推移的作用のとき積作用が推移的
  ⟺ G_a·G_b=univ、両方向とも安定化群と剰余類の交わり)。
- ✅ 実証明: **1A.7** (`card_not_mem_conj_ge`: 真部分群 H の共役に入らない元 ≥|H|) +
  再利用 helper **`sum_card_fixedBy_nat`** (Nat.card 版 Burnside)。⚠ 前 iteration の Fintype
  合成の壁の真因 = **`∑ m : M` 記法が statement で `[Fintype M]` を要求**していただけ (proof でなく
  型付け)。論法: χ=|Fix_{G⧸H}| に Burnside を G/H 適用 (∑_{G}χ=|G| 推移的 + ∑_{H}χ=|H|·#軌道≥2|H|)、
  χ(g)=0⟺g⁻¹∉共役、Finset counting + g↦g⁻¹ 双射。

**🎉 §1A 完了 (全 8 問: 1A.1/1A.2/1A.3/1A.4/1A.5/1A.7/1A.9/1A.10 実証明 + 1A.6/1A.8/1A.10a mathlib 記録)。**

**§1B** (`Ch01_Sylow/Problems.lean`、2026-07-23、Ch03 Hall/π 理論を import):
- ✅ 実証明 **1B.1(a)** `mul_isSubgroup_iff_le_sylow` (PS 部分群 ⟺ P≤S、Sylow 極大性)。
- ✅ 記録 **1B.1(b)** (mathlib `Sylow.unique_of_normal`/`characteristic_of_normal`)。
- ✅ 記録 **1B.2** (repo `normal_pgroup_le_opCore` = O_p 最大正規 p-部分群)。
- ✅ 記録 **1B.3** (mathlib `Sylow.normalizer_normalizer` = Sylow 正規化群自己正規化)。
- ✅ 実証明 **1B.4** `exists_le_card_eq_prime_mul_of_prime_dvd_index` (p∣|G:P|⟹∃Q⊇P |Q|=p|P|、
  一般 helper `exists_subgroup_card_eq_prime_mul_ker` = N_G(P)/P で Cauchy) +
  系 `not_dvd_index_of_maximal_pGroup` (極大 p-部分群 = Sylow、Sylow E の Cauchy 別証明)。
- ✅ 実証明 **1B.5(a)** `IsHallSubgroup.map_of_surjective` (π-Hall の全射像は π-Hall)。
- ✅ 実証明 **1B.5(b)** `exists_sylow_map_eq` (Sylow の像は Sylow) + **1B.5(c)**
  `card_sylow_le_of_surjective` (|Syl K| ≤ |Syl G|)。基盤: Sylow↔{p}-Hall 橋渡し 2 補題
  (`sylow_isHallSubgroup_singleton` / `exists_sylow_coe_eq_of_isHallSubgroup_singleton`) +
  `map_conj_smul` (θ(gHg⁻¹)=θ(g)θ(H)θ(g)⁻¹)。
- ✅ 実証明 **1B.6** `isHallSubgroup_inf_of_mul_isSubgroup` (HK 部分群 ⟹ H∩K は K の π-Hall)。
- ✅ 記録 **1B.7(a)** (repo `Subgroup.IsPiGroup.le_oPiCore` = O_π 最大正規 π-部分群)。
- ✅ 実証明 **1B.7(b)** `oPiCore_le_of_isHallSubgroup` (O_π ≤ 任意 π-Hall) + **1B.7(c)**
  `oPiCore_eq_iInf_isHallSubgroup` (O_π = 全 π-Hall の共通部分)。
- ✅ 実証明 **1B.8** (新 leaf `Ch03_SplitExtensions/PiResidual.lean`、O^p `pResidual` の π 一般化):
  `oPiResidual π G := sInf {N | N◁G ∧ IsPiGroup π (G/N)}`。**(a)** `isPiGroup_quotient_oPiResidual`
  (G/O^π が π-群、π-商正規が ⊓ で閉じ最小元) + `oPiResidual_le_of_isPiGroup_quotient` (普遍性) +
  一意性。**(b)** `oPiResidual_eq_closure_piPrimeElements` (O^π = π'-元で生成、W◁G は共役不変 +
  Cauchy で G/W が π-群、`Nat.exists_eq_pow_mul_and_not_dvd` で q-部分冪抽出)。OddOrder.lean 配線済。

**🎉 §1B 完了 (全 8 問: 1B.1a/1B.4/1B.5abc/1B.6/1B.7bc/1B.8ab 実証明 + 1B.1b/1B.2/1B.3/1B.7a 記録)。**

**§1C** (`Ch01_Sylow/Problems.lean` section 1C、2026-07-23):
- ✅ 実証明 **1C.1** `eq_normalizer_of_sylow_normalizer_le` (N_G(P)≤H ⟹ H=N_G(H)、Frattini、1B.3 一般化。
  ↥H の Sylow C + `map_conj_smul` で G に降ろす + `Sylow.smul_eq_iff_mem_normalizer`)。
- ✅ 実証明 **1C.2(a)** `exists_sylow_subgroupOf_eq_of_sylow` (H の Sylow P = H∩S、Sylow.subtype +
  極大性) + **1C.2(b)** `card_sylow_subgroup_le` (n_p(H)≤n_p(G)、1C.2a 対応が単射)。
- ✅ 実証明 **1C.3(a)** `powerOrder_eq_iUnion_sylow` (位数 p 冪の元 = ⋃ Sylow)。
- ✅ 実証明 **1C.3(b)** `prime_dvd_card_orderOf_prime_pow` (p∣\|G\| ⟹ p∣\|X\|)。Sylow `P` を `X` に
  共役作用させ `\|X\|≡\|X^P\| (mod p)` (`card_modEq_card_fixedPoints`)、固定点 `X^P`=`Z(P)`
  (可換 p-元は `P` に入る = helper `mem_sylow_of_orderOf_prime_pow_of_forall_commute`
  = `⟨x⟩≤N_G(P)` + Sylow 極大性)、`P` 非自明 p-群ゆえ `p∣\|Z(P)\|`。↥P の `X` への共役
  `MulAction` を letI 構成 + 固定点 ≃ `Z(P)` 全単射 (`card_eq_of_bijective`)。
- ✅ 実証明 **1C.7** `sylow_normal_of_maximal_subgroup_prime_index` (極大部分群 (coatom) が全て
  素数指数 + `p` = 最大素因数 ⟹ Sylow `p`-部分群正規)。背理法: `N_G(P)≠⊤` ⟹ `N_G(P)` を含む極大
  `M` (`eq_top_or_exists_le_coatom`、有限束 coatomic)、`q:=|G:M|` 素数。`P` は `M` の Sylow でもあり
  `N_M(P)=N_G(P)` (`subgroupOf_normalizer_eq`) ゆえ `n_p(G)=q·n_p(M)` (`relIndex_mul_index`)、
  Sylow 第三定理 (`card_sylow_modEq_one`) で両者 ≡1 (mod p) ⟹ `q≡1 (mod p)` ⟹ `q>p`、しかし
  `q ∣ |G|` ゆえ `q≤p`、矛盾。⚠ coercion `↑↑P` (Sylow→Subgroup→Set) vs `↑P` (Sylow→Set 直接) を
  `Sylow.coe_coe` で橋渡し。
- ✅ 実証明 **1C.6(a)** `exists_sylow_inf_sylow_of_mul_eq_univ` (`G=HK` ⟹ ∃P∈Syl(G),
  `P∩H`=H の Sylow 位数 ∧ `P∩K`=K の Sylow 位数)。helper `exists_sylow_inf_card_eq` (1C.2a の帰結) +
  Sylow 共役 `c•Q=Q'` の `c⁻¹=h·k` 分解、`P:=h⁻¹•Q`、`conj_smul_eq_self_of_mem`+`smul_inf`+`equivSMul`
  (共役の位数保存)。mathlib 既製 `conj_smul_eq_self_of_mem`/`smul_inf`/`equivSMul` を活用。
- ✅ 実証明 **1C.6(b)** `sylow_inf_mul_sylow_inf_eq` (`P=(P∩H)(P∩K)` 集合積)。`(P∩H)(P∩K)⊆P` +
  位数計数 `|(P∩H)(P∩K)|·|P∩H∩K|=|P∩H|·|P∩K|` (`card_mul_card_inf`)、`|G||H∩K|=|H||K|` (`G=HK`) の
  `p`-部分 (`factorization_mul`) で `|P|·pPart(H∩K)=|P∩H|·|P∩K|`、`|P∩H∩K|≤pPart(H∩K)` ゆえ
  `|(P∩H)(P∩K)|≥|P|`、`Set.eq_of_subset_of_ncard_le` で一致。**🎉 1C.6 完了 (a+b)**。
- ✅ 実証明 **1C.8** `card_subgroup_card_eq_modEq` (位数 p^a 部分群の個数が P と G で mod p 合同)。
  helper `le_sylow_of_isPGroup_of_le_normalizer` (`P≤N_G(D)` の p-群 D は `D≤P`)。↥P を `S_a(G)`・
  `S_a(P)` に共役 `MulAction` (letI, `equivSMul` で位数保存)、`card_modEq_card_fixedPoints` で
  `|S_a(G)|≡|Fix_G|`・`|S_a(P)|≡|Fix_P|`、`Fix_G ≃ Fix_P` を `D↦D.subgroupOf P` で全単射
  (`conj_smul_subgroupOf` で正規性移送、`map_subgroupOf_eq_of_le`/`comap_map_eq_self_of_injective`
  で往復、`subgroupOfEquivOfLe` で位数保存)。**🎉 §1C の一般 Sylow 問題 (1C.6/1C.7/1C.8) 全完了**。
- ⏸ **§1C 残り = 1C.4 / 1C.5 のみ** (上記「後回し」、重い/特殊)。次は **§1D** に進む
  (1C.4/1C.5 は §1D 以降の合間に再訪)。
- ⏸ **後回し (重い/特殊、後で戻る)**: **1C.4** (\|G\|=120 index 3 or 5)。n_2∈{1,3,5} は清潔
  (正規化群 index or 商 order 15)、但し **n_2=15 の場合が構造的に重い** (S_5 型、index-5 部分群 S_4 の
  存在は列挙でなく構造 — 計数だけでは矛盾を出せないことを確認済)。**1C.5** (A_{p+1} で
  \|N_G(P)\|=p(p-1)/2)。p-cycle の計数 (C(p+1,p)·(p-1)! 個、全て偶置換) が要で、mathlib の対称群
  cycle-type API 依存の特殊問題。

**§1D** (`Ch01_Sylow/Problems.lean` section 1D、2026-07-23 着手):
- ✅ 実証明 **1D.1** `not_dvd_index_of_sylow_normalizer_le` (`P∈Syl_p(H)`, `H◁G`, `N_G(P)⊆H` ⟹
  `p∤|G:H|`)。Frattini 論法 (`Sylow.normalizer_sup_eq_top`) で `N_G(P)⊔H=⊤`、`N_G(P)≤H` から
  `H=⊤`、`|G:H|=1`。
- ✅ 実証明 **1D.6** `isCoatom_iff_index_prime` (冪零群で `H` 極大 (coatom) ⟺ `|G:H|` 素数)。
  `⟹`: 冪零⟹正規化条件 (`Group.normalizerCondition_of_isNilpotent`) で極大は正規、対応定理で `G⧸H`
  単純 (`comap_injective` で `IsSimpleGroup` 構成)、単純+冪零⟹可換 (mathlib instance)、可換単純は素数
  位数 (`IsSimpleGroup.prime_card`)。`⟸`: 素数指数 ⟹ `H≠⊤` かつ `H<K` で `K.index∣H.index` 素数ゆえ
  `K=⊤`。⚠ import 追加 (Nilpotent/Cyclic)、namespace 罠: `MonoidHom.comap_bot`・
  `Subgroup.NormalizerCondition.normal_of_coatom` (Subgroup namespace 内)。
- ✅ 実証明 **1D.2** `not_dvd_card_and_index_of_centralizer_le` (`C_G(x)⊆H` (order-p `x∈H`) ⟹
  `p` は `|H|` と `|G:H|` を同時に割らない)。背理法: helper `exists_sylow_inf_card_eq` で `Q∈Syl_p(G)`,
  `P=Q∩H` (`|P|=pPart(H)`)、`p∣|G:H|` で `pPart(H)<pPart(G)=|Q|` (`factorization_mul`) ゆえ `P<Q`。
  `Q` は p-群 (冪零, `IsPGroup.isNilpotent`) で正規化条件、`subgroupOf_normalizer_eq` で
  `N(P.subgroupOf Q)=(N_G P).subgroupOf Q`、`SetLike.exists_of_lt` で `g∈N_G(P)∩Q`, `g∉P`。
  `⟨g⟩` の `P` への共役 `MulAction` (letI) + `exists_fixed_point_of_prime_dvd_card_of_fixed_point` で
  非単位固定点 `b` (g と可換)、`x=b^(p^(k-1))` は位数 p (`orderOf_pow`)、`g∈C_G(x)⊆H` ⟹ `g∈Q∩H=P`
  矛盾。**3度延期を克服して完遂。**
- ✅ 実証明 **1D.7** `mem_frattini_iff_forall_closure` (`g∈Φ(G)` ⟺ 非生成元: 任意の `X` で
  `⟨X∪{g}⟩=⊤ → ⟨X⟩=⊤`)。`⟹` は `frattini_nongenerating` (mathlib) + `⟨{g}⟩≤Φ`、`⟸` は
  `Φ=⨅極大` から `g∉M` なる極大 `M` を取り `X=M` で反例。
- ✅ 実証明 **1D.13** `isNilpotent_of_center_le` (`Z≤Z(G)` かつ `G⧸Z` 冪零 ⟹ `G` 冪零)。mathlib
  `Subgroup.isNilpotent_of_ker_le_center` を `mk' Z` (核=Z) に適用した特殊化。
- ✅ 記録 **1D.14** (`Φ(G)` 冪零): mathlib `frattini_nilpotent` 直対応 (`frattini G=Order.radical
  =⨅極大=Isaacs Φ(G)`)、ラッパー方針で記録のみ。
- ✅ 実証明 **1D.3(a)** `normalizer_le_of_disjoint_conj` (`H⊓H^g=1` (∀`g∉H`, Frobenius complement) ⟹
  `1<K≤H` で `N_G(K)⊆H`)。`n∈N_G(K), n∉H` なら `K=n·K·n⁻¹≤H^n` かつ `K≤H` で `K≤H⊓H^n=1` 矛盾。
  (`mem_normalizer_iff_map_conj_eq` + `pointwise_smul_le_pointwise_smul_iff`)
- ✅ 実証明 **1D.3(b)** `coprime_card_index_of_disjoint_conj` (同 `H` は Hall)。素数 `p∣gcd(|H|,|G:H|)`
  を仮定、`P=Q∩H` (`Q∈Syl_p(G)`, `|P|=pPart(H)>1`)、(a) で `N_G(P)⊆H`。`P<Q` なら 1D.2 と同じ
  g-抽出 (正規化条件+`subgroupOf_normalizer_eq`) で `g∈N_G(P)∩Q⊆H∩Q=P`, `g∉P` 矛盾 (fixed-point 不要)、
  ∴ `P=Q`、`pPart(H)=pPart(G)`、しかし `p∣index` で `pPart(H)<pPart(G)` 矛盾。
- ✅ **分割完了 (2026-07-23)**: `Problems.lean` (1682→1363 行, §1A–§1C) と新 leaf
  `Ch01_Sylow/ProblemsFrobeniusFrattini.lean` (341 行, §1D 全 7 定理) に flat suffix-split。
  新 leaf は `Problems` を import (§1A–§1C helper 利用) + Nilpotent/Cyclic/Frattini (§1D 専用)。
  `OddOrder.lean` 配線済、両 leaf build green (2209 jobs)。module 名不変で下流無影響。**以降 §1D の
  追記は新 leaf へ**。
- ✅ 実証明 **1D.4** `frobenius_complement_iff_centralizer_eq_bot` (`G=NH`, `1<N◁G`, `N∩H=1` で
  `H` Frobenius complement ⟺ 全非単位 `h∈H` で `C_N(h)=1`)。`⟹`: `n∈C_N(h), n≠1` なら `n∉H` かつ
  `h=n·h·n⁻¹∈H^n` で `h∈H⊓H^n` (Frobenius に反する)。`⟸`: `g=n·h'` 分解で `H^g=H^n`
  (`conj_smul_eq_self_of_mem`) から `n∈N,n≠1` に帰着、`x∈H⊓H^n, x≠1` で `x⁻¹n⁻¹xn∈N∩H=1` (N 正規)、
  `x,n` 可換 (`group` tactic) ゆえ `n∈C_N(x)=1` 矛盾。(新 leaf ProblemsFrobeniusFrattini.lean)
- ✅ 実証明 **1D.16** `frattini_map_subtype_le_frattini` (`N◁G` ⟹ `Φ(N)⊆Φ(G)`)。helper
  `characteristic_map_subtype_normal` (特性部分群を正規 N に沿って G へ押し出すと G で正規、
  `MulAut.conjNormal`+char)。各極大 `M` で `Φ(N)⊄M` なら `M⊔Φ(N)=⊤`、`Φ(N)◁G` ゆえ
  `M⊔Φ(N)=M·Φ(N)` (`mul_normal`)、`x=m·φ` から `m∈N⊓M`、`N≤(N⊓M)⊔Φ(N)`、`frattini_nongenerating`
  で `N⊆M`、矛盾。⚠ 一般群の部分群束は modular でない (mathlib `IsModularLattice (Subgroup C)` は
  CommGroup 限定、`mem_sup` 積形も同様) → `Φ(N)` 正規性 + `mul_normal` で Dedekind を回避。
- ⏸ **1D.5 後回し (intricate)**: `N_G(P)⊆H` (全 p-部分群) ⟹ Frobenius complement。`D=H∩H^g` の
  Sylow `Q` の共役論法が clean な計画立たず (Isaacs/Coq 再読が要)。
- ✅ 実証明 **1D.8 (可換部分)** `commutator_le_frattini` (冪零有限群で `[G,G]⊆Φ(G)`、`G/Φ(G)` 可換)。
  各極大 `M` は素数指数 (1D.6) ゆえ `G⧸M` は素数位数=巡回、`isMulCommutative_of_isCyclic_of_ker_le_center`
  (⚠ `IsCyclic.commGroup` は既存 Group instance と diamond を作るので `IsMulCommutative` 経由で回避)、
  `commutatorElement_eq_one_iff_mul_comm` で `⁅g₁,g₂⁆∈M`。
- ✅ 実証明 **1D.8 (基本アーベル部分)** `pow_mem_frattini_of_isPGroup` (p-群で `∀g, g^p∈Φ(P)`) +
  `pow_eq_one_frattiniQuotient_of_isPGroup` (商 `P/Φ(P)` の exponent が p を割る)。核は Burnside 基底定理
  **不要**: 各極大 `M` は p-群 coatom ゆえ指数素数 (1D.6) かつ `∣|P|=p^n` で `=p`、`Subgroup.pow_index_mem`
  で `g^(M.index)=g^p∈M`、全極大の共通部分で `g^p∈Φ(P)`。`commutator_le_frattini` (可換) とあわせ
  `P/Φ(P)` 基本アーベル。→ **1D.8 完了**。
- ✅ 実証明 **1D.15 (`N=G` 版)** `isNilpotent_of_quotient_frattini_isNilpotent` (`G/Φ(G)` 冪零⟹`G`
  冪零)。各 Sylow `P` の像 `θ(P)` は `G/Φ(G)` の Sylow (1B.5(b) `exists_sylow_coe_eq_of_isHallSubgroup_singleton`
  + `IsHallSubgroup.map_of_surjective`)、冪零性で正規、逆像 `P⊔Φ(G)=comap(map P)` (`comap_map_eq`+`ker_mk'`)
  が正規、Frattini 論法 `normalizer_sup_eq_top'` + 非生成性 `frattini_nongenerating` で `N_G(P)=⊤` ⟹ `P◁G`、
  全 Sylow 正規で `G` 冪零 (`isNilpotent_of_finite_tfae.out 3 0`)。mathlib `frattini_nilpotent` と平行構造。
  ⚠ coe 罠: `(P:Subgroup G)` は `↑↑P` (二重) を作り補題の `↑P` (単一) と非一致 → hfr 再文言せず `top_le_iff`+`sup_le`
  で項構成 (`sup_eq_left` の rw パターンは coe で不発)。**一般 `N` 版 (Φ(G)⊆N◁G, N/Φ(G)冪零⟹N冪零) は残**。
- ✅ 実証明 **1D.17** `isNilpotent_of_quotient_commutator_isNilpotent` (`N◁G` 冪零 + `G/N'` 冪零 ⟹ `G`
  冪零)。導来 `N'=⁅N,N⁆` は 1D.8 で `Φ(N)`、1D.16 で像 `⊆Φ(G)`、`Subgroup.map_subtype_commutator`
  (`(commutator ↥N).map N.subtype=⁅N,N⁆`) で `N'⊆Φ(G)`。全射 `G/N'↠G/Φ(G)` (`QuotientGroup.map`
  + `map_surjective_of_surjective`、⚠ section 変数 `N` が explicit 先頭ゆえ計 5 引数) で `G/Φ(G)` 冪零
  (`Group.nilpotent_of_surjective`)、1D.15 で `G` 冪零。→ **§1D Frattini 冪零クラスタ 1D.13–1D.17 完結**
  (1D.15 一般 N 版のみ残)。
- ✅ 実証明 **1D.9 (前半+核)** `isCyclic_of_frattiniQuotient_isCyclic` (`P/Φ(P)` 巡回⟹`P` 巡回、
  生成元を非生成性 `frattini_nongenerating` で持ち上げ) + `sq_le_card_frattiniQuotient_of_isPGroup_of_not_isCyclic`
  (非巡回 p-群 ⟹ `p²≤|P:Φ(P)|`、商 p-群位数 `p^n` で `n≥2`: 位数 `1`(自明)/`p`(`isCyclic_of_prime_card`) 排除)。
  ⚠ `x̄` 等結合文字は識別子不可 (`gbar`)、`MonoidHom.map_zpowers` (Subgroup 側でない)、`Subgroup.eq_top_iff'`
  は解決せず `eq_top_iff`+intro。
- ✅ 実証明 **1D.9 (後半)** `isCyclic_or_elementaryAbelian_of_card_eq_prime_sq` (位数 p² ⟹ 巡回 or
  基本アーベル)。非巡回なら前半で `p²≤|P:Φ(P)|`、Lagrange `index_mul_card` で `|Φ(P)|=1` ⟹ `Φ(P)=⊥`、
  `pow_mem_frattini` で exponent p、`commutator_le_frattini`+`commutator_eq_bot_iff` (=`IsMulCommutative`)
  で可換。⚠ 元の交換子 `⁅a,b⁆` の `Bracket P P` は **scoped instance** (`commutatorElement`) ゆえ自分で
  書くと未合成 → `commutator_eq_bot_iff` 経由で回避。→ **1D.9 完了**。
- ✅ 実証明 **1D.10 (前半)** `centralizer_eq_self_of_maximal_abelian_normal` (p-群の極大可換正規部分群 `A`
  は `C_P(A)=A`)。`A≤C_P(A)` は可換ゆえ自明。`A<C_P(A)` なら **Lemma 1.23** (`IsPGroup.exists_normal_index_eq_prime`,
  repo `Ch01_Sylow/Basic.lean`) で `A<L≤C_P(A)`, `|L:A|=p`, `L◁P` を得、`L⊆C_P(A)` で `A⊆Z(L)`、
  `L/A` 位数 p 巡回で `L` 可換 (`isMulCommutative_of_isCyclic_of_ker_le_center`) — 極大性に矛盾。
  ⚠ `Subgroup.le_centralizer` は H explicit / repo 補題は `OddOrder.Isaacs.Ch01.IsPGroup.*` で dot notation
  不発 (`_root_.IsPGroup` を見る) → 明示適用 + `import Basic`。
- ✅ 実証明 **1D.10 (後半)** `index_dvd_factorial_of_maximal_abelian_normal` (`|P:A| ∣ (|A|-1)!`)。
  `P` の `A∖{1}={a:↥A//a≠1}` への共役 MulAction (`MulAut.conjNormal`) を letI 定義、`MulAction.toPermHom`
  の核 = `C_P(A) = A` (前半)、`Subgroup.index_ker` + `Nat.card_perm` で `|P:A|=|range|∣|Perm(A∖{1})|
  =(|A|-1)!`。⚠ 罠: `rw [←hCA]` は `A` を `centralizer A` 内まで書換え motive 破綻 → `f.ker=centralizer A`
  を先証して `.trans hCA` / `hane:a≠1`(P) ≠ `⟨a,ha⟩≠1`(↥A) → Subtype.ext_iff で導出 / MulAction proof の
  `show`→`change` / `MulAut.conjNormal_apply` + `mul_inv_eq_iff_eq_mul` で commute / card は
  `Fintype.card_subtype_compl`+`card_subtype_eq`。→ **1D.10 完了**。
- ✅ 実証明 **1D.11** `card_dvd_factorial_of_abelian_bound` (`n` が可換部分群位数の上界 ⟹ `|G| ∣ n!`) +
  helper `exists_maximal_abelian_normal` (有限順序の極大元 `Finite.exists_le_maximal`、witness=`center P`)。
  各 `P∈Syl_p(G)` の極大可換正規 `A` に 1D.10 後半 ⟹ `|P:A|∣(|A|-1)!`、`A.map subtype` の可換性
  (`equivMapOfInjective` 経由) で `|A|≤n`、`|P|=|A|·|P:A| ∣ |A|! ∣ n!` (`mul_factorial_pred`)。
  `|P|=p^{v_p|G|}` (`Sylow.card_eq_multiplicity`) で全素数冪 ⟹ `|G|∣n!` (`Nat.dvd_iff_prime_pow_dvd_dvd`)。
  ⚠ `dvd_iff_prime_pow_dvd_dvd` の `intro` は `Nat.Prime` を与える (変換不要) / `card_eq_multiplicity` は
  `↥↑P` coe ゆえ明示型 `have hmult : Nat.card ↥P = …` で橋渡し。`n` を最大値でなく上界に一般化。
  → **1D.11 完了**。
- ✅ 実証明 **1D.12** `card_orderOf_eq_prime_add_one_modEq_zero` (`p∣|G|` ⟹ 位数 p 元数 `+1 ≡ 0 mod p`)
  + McKay helper `card_pow_eq_one_modEq_zero` (`#{x^p=1} ≡ 0`)。mathlib は Cauchy **存在**のみ露出・count
  無しゆえ McKay を自前構築: `vectorsProdEqOne G p` (`Perm/Cycle/Type.lean`) に `Multiplicative (ZMod p)` を
  巡回シフト作用 (`rotate`、mul_smul は p-周期性 `hper: rotate w m=rotate w (m%p)`)、
  `IsPGroup.card_modEq_card_fixedPoints` で `|G|^(p-1)≡|fixed|`、固定点 ≃ `{x//x^p=1}` (定数ベクトル、
  `.get ⟨0,pos⟩`+`get_replicate`+`rotate_one_eq_self_iff_eq_replicate`)、`|G|^(p-1)≡0`。減算は
  `{x//x^p=1} ≃ Option {x//orderOf=p}` (1↔none) で `Fintype.card_option`。⚠ `toAdd_one/mul/ofAdd` は bare、
  `List.Vector.head` は長さ p が succ 形でなく型不一致 → `.get ⟨0,hp.out.pos⟩`。→ **1D.12 完了**。
- ✅ 実証明 **1D.15 (一般 `N` 版)** `isNilpotent_of_frattini_le_of_quotient_isNilpotent` (`Φ(G)⊆N◁G`,
  `N/Φ(G)` 冪零⟹`N` 冪零) + 再利用 helper `sylow_normalizer_sup_eq_top_of_quotient_nilpotent` (`K/M` 冪零
  ⟹ 各 Sylow で `N_K(P)⊔M=⊤`、N=G 版の核を M 一般化)。**二段 Frattini** (Fitting 経由は循環): 各
  `P∈Syl_p(↥N)` に (内) helper で `N_↥N(P)⊔Φ(G)ᴺ=⊤`、`N.subtype` で押し出し (`map_sup`+`subgroupOf_map_subtype`
  +`le_normalizer_map`) `N≤N_G(P.map)⊔Φ(G)`、(外) `Sylow.normalizer_sup_eq_top` で `N_G(P.map)⊔N=⊤`、
  合わせ `N_G(P.map)⊔Φ(G)=⊤`、`frattini_nongenerating`⟹`P.map◁G`、`subgroupOf`+`Normal.subgroupOf`+
  `comap_map_eq`+`ker_subtype` で `P◁↥N`。⚠ 罠: `(↑P:Subgroup)` 明示は二重 coe→bare `↑P`+absorb は
  `le_antisymm`+`sup_le` / `rw[←hmapeq]` は `N` が `P:Sylow p ↥N` の型に現れ motive 破綻→`.le.trans` の項 /
  `Subgroup.map_top` は無く `←MonoidHom.range_eq_map`。→ **1D.15 完了 (N=G + 一般 N)**。
- ⬜ **残り §1D (1 問)**: **1D.5** (Isaacs 明記の難問)。統陳: `H≤G` で「全素数 p・全 p-部分群 `P⊆H` に
  `N_G(P)⊆H`」ならば `H` は Frobenius complement (`∀g∉H, H∩H^g=1`, cf. 1D.3)。**closing 論法は判明**:
  `D:=H∩H^g≠1` と仮定、`Q∈Syl_q(D)` (nontrivial) をとる。`Q⊆H`、`Q⊆H^g`。もし `Q` と `Q^g` (Isaacs 慣用
  `H^g=g⁻¹Hg` で `Q^g=gQg⁻¹⊆H`) が `H` で共役 `Q^g=Q^h` (h∈H) なら `h⁻¹g∈N_G(Q)⊆H` (条件) ゆえ `g∈H`、
  矛盾。**難所 = 「Q と Q^g が H で共役」の justification** (Isaacs hint だが subtle、Sylow of H への埋め込み
  だけでは同位数 q-部分群の共役は従わず、maximality/counting 論法を要すると思われる)。→ **専用 session で
  精査**。他の §1D は全完 (**17/18**)。
  ⚠ namespace 罠: `Subgroup.isNilpotent_of_ker_le_center` (Subgroup 内)、`closure_le` は
  module system で露出せず → `mem_closure_singleton`+`zpow_mem` で回避。

## Ch.2 (Subnormality) §2A — 着手 (2026-07-23)

新 leaf `OddOrder/Isaacs/Ch02_Subnormality/Problems.lean` (namespace `OddOrder.Isaacs.Ch02`、import
`Mathlib.GroupTheory.IsSubnormal`+`Ch01_Sylow.Main`、`OddOrder.lean` 配線済)。`Subgroup.IsSubnormal` は
mathlib inductive (`top`/`step`)。

- ✅ 実証明 **2A.3(a)** `le_of_isSubnormal_of_coprime_index` (`H` 部分正規, `|G:H|` と `|K|` 互いに素
  ⟹ `K≤H`)。`IsSubnormal` 帰納法 (`| top => le_top | @step H' K' hle _ hN ih`): step で `K'.index∣H'.index`
  (`index_dvd_of_le`) から `ih` で `K≤K'`、核 = 商 `mk'(H'.subgroupOf K')` の像 `(K.subgroupOf K').map` の
  card が `|K|` (`card_map_dvd`+`subgroupOfEquivOfLe`) と `(H'.subgroupOf K').index` (`card_subgroup_dvd_card`,
  `index_eq_card`) 双方を割り、後者は `|G:H'|` を割り (`relIndex_dvd_index_of_le`) `|K|` と互いに素
  (`eq_one_of_dvd_coprimes`) ⟹ 像 `⊥` ⟹ `K.subgroupOf K'≤H'.subgroupOf K'` ⟹ `K≤H'`
  (`subgroupOf_map_subtype`+`inf_eq_left`)。
- ✅ 実証明 **2A.1** `le_oPiCore_of_isSubnormal_of_isPiGroup` (subnormal π-subgroup `K ⊆ O_π(G)`) +
  helper `oPiCore_map_subtype_le_of_isSubnormal` (`(oPiCore π ↥H).map H.subtype ≤ oPiCore π G` for H 部分正規)。
  char-motive の IsSubnormal 構造帰納が動いた: top=`oPiCore.map_le_of_surjective`、step=`subgroupOfEquivOfLe`
  の iso で `oPiCore.map_eq_of_mulEquiv` 移送 + `characteristic_map_subtype_normal` (Ch01 1D.16) で ↥K' 正規
  + `IsPiGroup.le_oPiCore` + `H.subtype=K'.subtype∘subtype∘e.symm` 合成 (`map_map`) + IH。2A.1 本体は
  `↥K` π-群で `oPiCore π ↥K=⊤` (`card_top`), `(⊤).map K.subtype=range=K`。import 追加 = Ch03 Theorem315 +
  Ch01 ProblemsFrobeniusFrattini (cycle 無し)。→ **2A.1 完了、2A.3(b) unblock**。
- ⬜ **残り §2A** (要 machinery):
  - **旧 2A.1 メモ** (参考): **正しい帰納 motive の発見過程**: 素朴な
    `P K := IsPiGroup π K → K≤oPiCore` は IsSubnormal 構造帰納に **不適** (step の IH は大きい `K'` について
    で、π-group 性は小さい `K` について ⟹ 使えない)。正解は **`P H := (oPiCore π ↥H).map H.subtype ≤
    oPiCore π G`** (H を IsSubnormal で帰納): top は `↥⊤≅G` の iso、step (`H◁K'`, IH: `(oPiCore π ↥K').map
    K'.subtype ≤ oPiCore π G`) は `(oPiCore π ↥H).map (Subgroup.inclusion hle)` が ↥K' で正規 (oPiCore char
    in ↥H + `H.subgroupOf K'◁↥K'` で char-in-normal) かつ π-group (`oPiCore.isPiGroup`+`IsPiGroup.map`) ⟹
    `≤ oPiCore π ↥K'` (`IsPiGroup.le_oPiCore`)、`H.subtype=K'.subtype∘inclusion` で `.map K'.subtype` して IH。
    素材確認済: `IsPiGroup.le_oPiCore`[Normal] / `oPiCore.characteristic`/`isPiGroup` / `IsPiGroup.map_equiv`
    / `normal_of_characteristic` / 1D.16 の `characteristic_map_subtype_normal` パターン。~60 行 fiddly
    (subgroup-as-group + inclusion + char + π-group 配管)。
    **★ 全ツールチェーン確認済 (2026-07-23)、step の具体手順**: iso `e := (Subgroup.subgroupOfEquivOfLe hle).symm
    : ↥H ≃* ↥(H.subgroupOf K')` で `(oPiCore π ↥H).map e = oPiCore π ↥(H.subgroupOf K')`
    (**`oPiCore.map_eq_of_mulEquiv` は public**、Ch03 Theorem315.lean — private の `map_le_of_mulEquiv` を
    懸念したが equality 版が公開されている)。`inclusion hle = (H.subgroupOf K').subtype ∘ e` ゆえ
    `(oPiCore π ↥H).map (inclusion hle) = (oPiCore π ↥(H.subgroupOf K')).map (H.subgroupOf K').subtype`、
    これは `characteristic_map_subtype_normal` (oPiCore char + `H.subgroupOf K'◁↥K'`=hN) で ↥K' 正規 +
    π-group (`oPiCore.isPiGroup`) ⟹ `≤ oPiCore π ↥K'` (`IsPiGroup.le_oPiCore`)、`.map K'.subtype` して IH。
    top は `oPiCore.map_le_of_surjective π (⊤).subtype`。**import 追加要**: `Ch03_SplitExtensions.Theorem315`
    (oPiCore) + `Ch01_Sylow.ProblemsFrobeniusFrattini` (characteristic_map_subtype_normal)。cycle 無し。
  - ✅ 実証明 **2A.3(b)** `le_of_isSubnormal_of_coprime_index'` (`K` 部分正規, `|G:H|` と `|K|` 互いに素
    ⟹ `K≤H`) + helper `coprime_normal_le` (`N◁G`, `coprime(|N|,|G:H|)` ⟹ `N≤H`)。π=`↑(Nat.card K).primeFactors`、
    2A.1 で `K⊆O_π(G)`、`coprime_normal_le` を `O_π(G)` に適用。coprime_normal_le: `|H⊔N:H|=relIndex` が
    `card_mul_card_inf`(正規積公式)で `|N|` を割り `relIndex_dvd_index_of_le` で `|G:H|` も割り互いに素で `=1`
    ⟹ `H⊔N=H`⟹`N≤H`。coprimality は `oPiCore.isPiGroup` の primes⊆ + `Coprime.disjoint_primeFactors` +
    `Finset.disjoint_of_subset_left`。一発 green。→ **2A.3 完全完成 (a+b)**。
  - ✅ 実証明 **2A.2** `oPiResidual_le_of_isSubnormal_of_index_isPiNumber` (`K` 部分正規, `|G:K|` が π-数
    ⟹ `O^π(G) ≤ K`)。`O^π=⟨π'-元⟩` (`oPiResidual_eq_closure_piPrimeElements`=1B.8) + `closure_le` で各 π'-元
    `g` に帰着、`⟨g⟩` の位数 `orderOf g` (π'-数) は `|G:K|` (π-数) と互いに素 (`disjoint_primeFactors`)、
    2A.3(a) で `⟨g⟩≤K` ⟹ `g∈K`。import 追加 = Ch03 PiResidual。一発 green (import のみ)。→ **2A.2 完了**。
  - ✅ 記録 **2A.7** (`S◁◁G` 非可換単純 ⟹ `S^G` minimal normal): repo `Ch09.isMinimalNormal_normalClosure_of_isSubnormal`
    (Isaacs Lemma 9.17) がまさにこれ、docstring 記録 (ラッパー方針)。
  - ✅ 実証明 **2A.8** `commutator_eq_bot_of_ne_of_isSubnormal_of_simple` (異なる非可換単純な部分正規 `S,T`
    ⟹ `⁅S,T⁆=⊥`)。非可換単純部分正規は component (`isQuasisimple_of_isSimpleGroup_not_isMulCommutative`)、
    異なる component は可換 (`IsComponent.commutator_eq_bot_of_ne`、Ch09)。import 追加 = Ch09 SubnormalSocle。
  - ⏸ **残り §2A (deferred-hard、repo 直接対応薄い)**: 2A.4 (Wielandt: S 単純が全 subnormal と permute
    ⟹ 全 subnormal を正規化) / 2A.5 (minimal normal = 単純直積、socle 分解が必要) / 2A.6 / 2A.9
    (H◁◁G π-perfect ⟹ O^π(G) が H を正規化)。**2A.9 メモ**: `H≤O^π(G)` は導ける (H/(H∩O^π(G)) は
    π-群商ゆえ π-perfect の H で自明) が、正規化は subtle。いずれも ~40-60 行 machinery ゆえ専用 session。

## Ch.3 (Split Extensions) §3A — 着手 (2026-07-23、§2A hard tail deferred 中の breadth 展開)

新 leaf `OddOrder/Isaacs/Ch03_SplitExtensions/Problems.lean` (namespace `OddOrder.Isaacs.Ch03`、
import `Mathlib.GroupTheory.SemidirectProduct`+`Tactic.Group`、`OddOrder.lean` 配線済)。

- 🔨 **3A.3** (位数 pm 群) 部分完成 (2026-07-23): σ (位数 m, `AddAut.mulLeft`+`MulAutMultiplicative`)
  / `affineGroup u = Mult(ZMod p) ⋊ ⟨σ⟩` / `affineGroup_card` (|G|=p·orderOf u) / `affineGroup_card_ker`
  (P=ker rightHom 位数 p) / `affineGroup_quotient_isCyclic` (G/P 巡回) / `exists_group_card_eq_center_trivial`
  (位数 m 元存在) を実証明。⚠ **Z(G)=⊥ (中心自明) は未完** — center 計算で `Multiplicative (ZMod p)` の
  ring Mul (`instDistribOfSemiring`) と group Mul (`Multiplicative.group`) の instance 衝突。
  回避法: step1 の cancel を `mul_left_cancel` (Multiplicative) でなく **toAdd で ZMod p 加法に落として
  `add_left_cancel`**、g.right=1 の結論も MulAut equation の simp を避ける。次イテレーションで完了。
- ✅ 実証明 **3A.1(a)** semidihedral の特徴的自己同型 (2026-07-23)。`ZMod n` (8∣n) 上、生成元条件
  `c^a = c⁻¹z` (加法的 `-c+z`, `z=n/2`) を満たす唯一の自己同型 `a` = 乗数 `w=z-1` (`w²=1` ∵ 4∣n)
  による乗法、位数 2。`semidihedralAut` (concrete `AddEquiv`, 自身が逆) / `_apply` / `_apply_isUnit`
  (存在=生成元条件、odd fact `z·c=z` 経由) / `_unique` (自己同型は `1` での値で定まる, `map_nsmul`) /
  `_add_self`+`_ne_zero`+`_addOrderOf`=2 (`AddAut` は加法群ゆえ位数 = `addOrderOf`)。全実証明・sorry 無。
- ✅ 実証明 **3A.1(b)** semidihedral 群内の位数分布 (2026-07-23)。`σ = semidihedralMulAut` (=`a` の
  `MulAut (Multiplicative (ZMod n))` 版、`MulAutMultiplicative` bridge; apply=rfl、`σ²=1`)、
  `SemidihedralGroup = Multiplicative (ZMod n) ⋊ ⟨σ⟩` (φ=部分群包含 `H.subtype`、ZMod.lift 不要)、
  reflection `(x,σ)` (=S−C の元)。`_sq`: `(x,σ)²=inl(z·x)`、`_pow_four`: `(x,σ)⁴=1`、
  `_ne_one`/`_sq_eq_one_iff`。位数特徴づけ `_orderOf_eq_two_iff` (⟺`z·x=0`=偶)・`_eq_four_iff`
  (⟺`z·x≠0`=奇、`orderOf_eq_prime_pow`)・`_two_or_four`。半々: `semidihedral_invol_mul_dichotomy`
  (`z·a∈{0,z}`、induction) + `_invol_ne_zero` + **`semidihedralOrderFlip`** (位数2集合 ≃ 位数4集合、
  parity flip `x↦x·ofAdd 1`)。全実証明・sorry 無・axiom-clean。
- ✅ 実証明 **3A.1(c)** 位数 2・位数 4 の元はそれぞれ単一共役類 (2026-07-23)。`_conj`: `inl y` で
  reflection を共役すると `refl(y·x·σ(y⁻¹))` (加法的に `toAdd x` が `(2-z)·toAdd y` シフト)。
  `semidihedral_shift_surj`: `z·d=0` (d 偶) なら `∃t, (2-z)·t=d` (`u=1+n/4` が `(2-z)·u=2` ∵
  `(2-4k)(1+2k)=2-8k²≡2`、d=2s→t=u·s)。`_isConj` (差が偶なら共役) + 系 `_isConj_of_two` (両偶)
  ・`_isConj_of_four` (両奇、dichotomy で `z·x=z` 確定)。全実証明・sorry 無・axiom-clean。
  **3A.1 完全完成 (a/b/c)**。
- ✅ 実証明 **3A.2** 一般化四元数群 `Q_n` (位数 n) — 2026-07-23 完成 (ker(ψ) 構成):
  B = C の index-2 部分群 = `Subgroup.zpowers (Multiplicative.ofAdd (2:ZMod n))` (位数 n/2、
  偶元 = squares)。位数 4 の元 {(x,σ): x 奇} は inl(B) の coset `(ofAdd x₀, σ)·inl(B)` をなす
  (x₀ 奇; σ(ofAdd 2k)=ofAdd(-2k) ゆえ shift で {奇}=coset)。Q = coset ∪ inl(B) は位数 n の部分群
  (= Q_n)。**★ clean 構成発見 (2026-07-23)**: `ψ : S →* Multiplicative (ℤ/2)`,
  `ψ(x,h) = (h の parity ∈{0,1}) + (toAdd x の parity)` は**準同型** — σ twist で左 parity が保存
  (`w = z-1 = 4k-1` 奇ゆえ `parity(w·m) = parity(m)`)、H-part も加法的。ψ 全射 (`ψ(ofAdd 1,1)=1`)
  ゆえ **Q := ψ.ker、`|Q| = |S|/2 = n`** が自動 (`Subgroup.card_eq_card_quotient_mul_card_subgroup`
  や index=2)。B ≤ Q (偶元は ker)、位数 4 元 (x 奇, σ) ⊆ Q (parity 1+1=0)、Q = {(x,1):x偶}∪{(x,σ):x奇}
  = coset ∪ B。~50 行 (ψ の map_mul' 計算が主)。閉性を手で示すより ker(ψ) が圧倒的に clean。
  既存 semidihedral インフラ (reflection/σ/dichotomy/parity) を再利用。
  ⚠ 次イテレーション注意: ψ の H-part parity は `SemidirectProduct.rightHom : S →* H` +
  `H = ⟨σ⟩ ≃* Multiplicative (ℤ/2)` iso が要 (σ 位数2)。iso が clean に取れない場合は、ψ を toFun 直書き
  (g.right の 1/σ 判定 + 左 parity) + map_mul' 手計算、または Q を carrier set 直接定義
  ({(x,1):x偶}∪{(x,σ):x奇}) + closure 手証明 (既証明の位数2/4 characterization を活用) にフォールバック。
- ✅ 実証明 **3A.5** `semidirectConjEquivProd` (`G ⋊ G ≅ G × G`、共役作用の半直積は直積)。同型
  `(n,g)↦(n·g,g)` (逆 `(a,g)↦⟨a·g⁻¹,g⟩`)、map_mul' は `mul_left`/`mul_right`/`conj_apply` 展開 + `group`。
- ⬜ **3A.3** (位数 pm 群、Z(G)=1) — 構成計画 (2026-07-23、order-m 元は scratch 検証済):
  G = `Multiplicative (ZMod p) ⋊ Subgroup.zpowers σ` (p 素数, m∣p-1, m>1)。
  **(1) order-m 元 u : (ZMod p)ˣ [検証済]**: `haveI := ZMod.isCyclic_units_prime Fact.out`;
  `obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard`; `Nat.card (ZMod p)ˣ = p-1`
  (`card_units_eq_totient`+`totient_prime`); `u := g^((p-1)/m)`;
  `orderOf u = m` via `orderOf_pow_of_dvd hne hdvd` + `Nat.div_div_self hm`
  (hdvd: (p-1)/m ∣ p-1 = `Nat.div_dvd_of_dvd hm`, hne: (p-1)/m≠0)。
  **(2) σ := `(MulAutMultiplicative (ZMod p)).symm (AddAut.mulLeft u)`** : MulAut(Mult(ZMod p))。
  `orderOf σ = orderOf u = m` via `orderOf_injective (MulAutMultiplicative _).symm.toMonoidHom
  (.symm.injective)` ∘ `orderOf_injective AddAut.mulLeft hinj`。⚠ hinj (mulLeft 単射) は
  `AddAut.mulLeft = DistribMulAction.toAddAut` (`@[simps! +simpRhs]`) の apply で `(toAdd(mulLeft a)) 1
  = ↑a·1 = ↑a`; `congrArg Multiplicative.toAdd h` + `DFunLike.congr_fun _ 1` + `simpa [Units.smul_def,
  Units.ext_iff]` (前回 simp が toAdd wrapper を剥がせず未完 — apply 補題名の特定が要)。
  **(3) |G| = p·m**: `SemidirectProduct.card` (=|N|·|H|) + `Nat.card_zpowers`+orderOf σ=m +
  `Nat.card (Mult(ZMod p)) = p` (`Nat.card_congr Multiplicative.toAdd`+`Nat.card_zmod`)。
  **(4) P := inl 像 = ker rightHom, 正規, |P|=p; G/P ≅ zpowers σ 巡回 (rightHom 全射)**。
  `SemidirectProduct.rightHom`/`range_inl`/`inl_injective`。
  **(5) Z(G)=⊥ [核心・未検証, SemidirectProduct center API 無し]**: (a,h)∈center →
  ∀(b,k) 可換。k=1: a·φ(h)(b)=b·a ⟹ φ(h)(b)=b ∀b (N 可換) ⟹ φ(h)=id ⟹ h=1 (φ=subtype 単射)。
  h=1,b=1,k=σ: a=σ(a)=×u(a) ⟹ (u-1)·toAdd a=0 ⟹ toAdd a=0 (u≠1 ⟹ u-1 は体 ZMod p の unit)
  ⟹ a=1。~50 行。`Subgroup.mem_center_iff`/`SemidirectProduct.ext`/`SemidirectProduct.mul_left,right`。
- ⬜ 残り §3A (いずれも substantial ~50-60 行): **3A.6** (p-群 P が p∤|G| の G に faithful ⟹ ある
  P-orbit で faithful) — repo に **Thm 1.38 (Generalized Brodkey)** あり (`Ch01_Sylow/Main.lean:756`、
  Sylow 交叉極小で S∩T 内の両正規部分群 ⊆ O_p)。application は `G⋊P` 構成で P を Sylow とみて Brodkey +
  orbit-stabilizer。**3A.3** (order pm, m|p-1, 正規 P 位数 p, G/P 巡回, Z(G)=1) — construction:
  `(ZMod p)⋊C`, C≤Aut(ZMod p)=(ZMod p)ˣ 位数 m (巡回ゆえ存在)、加法/乗法 bridging + Z=1 検証。
  **3A.4** (order q(q-1), 基本アーベル正規, 位数 p 元共役) — 体 F_q の F_q⋊F_qˣ。3A.1/3A.2 (SD/Q_n 構成) /
  3A.7 (regular orbit) / 3A.8 (cyclic pqr auto)。次イテレーションで 3A.6 or 3A.3 を新鮮に構築推奨。
  **★ 3A.3 の材料確定 (2026-07-23、de-risked)**: bridge は **`IsCyclic.mulAutMulEquiv : MulAut G ≃*
  (ZMod (Nat.card G))ˣ`** (Cyclic.lean:593) がまさにこれ (先の「bridge 無し」は誤り)。手順:
  `N := Multiplicative (ZMod p)` (cyclic card p)、`(ZMod p)ˣ` の位数 m 元 `u` (m|p-1, 巡回ゆえ存在) →
  `σ := mulAutMulEquiv.symm u : MulAut N` 位数 m、`φ : Multiplicative (ZMod m) →* MulAut N` を generator
  ↦ σ で (injective)、`G := SemidirectProduct N (Multiplicative (ZMod m)) φ`。性質: |G|=pm (`SemidirectProduct`
  card)、P=inl 像 正規 位数 p、G/P≅Mult(ZMod m) 巡回、Z(G)=1 (φ faithful + 非自明作用の共通固定点=0)。
  ~50-60 行だが全ピース確定。次イテレーションで構築。残り (§1D 1D.5 / §2A 2A.4-6,9 / §3A 他) も
  各 ~50-60 行の construction/application。

- ⬜ **次: §3A 続き or §2A hard tail 再訪。§1D 残り = 1D.5 (Isaacs-noted-hardest)。**

## 完了条件

Isaacs Ch.1–10 の全演習問題が形式化 (実証明 or mathlib/repo 対応の docstring 記録)、
build green、AxiomsCheck OK。章単位で commit・issue checkbox 更新。

## 参照

- issue 9205 (scope 拡大の裁定元)、`notes/isaacs/frontier_measured_2026_07_19.md` (番号付き結果の完済正本)
- `references/isaacs/finite-group-theory.pdf` (statement 確定用、PDF ページ = 書籍ページ + 13)
- CLAUDE.md「トレーサビリティ」「ファイル粒度」「ラッパー方針」
