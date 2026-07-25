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
- ✅ 実証明 **1C.4** (2026-07-25 解凍後 1 発目、新 leaf `Ch01_Sylow/ProblemsOrder120.lean` ~420 行):
  `exists_subgroup_index_eq_three_or_five_of_card_onetwenty` (|G|=120 ⟹ 指数 3 か 5 の部分群)。
  n₂∈{1,3,5,15}: 3/5 は `Sylow.card_eq_index_normalizer`、1 は P⊔F 位数 40、**15 は Thm 1.16**
  (`card_sylow_modEq_one_of_max_inter`、repo Basic.lean) で交わり最大対の relIndex d∣14 ∧ d∣8 ∧ d≠1
  ⟹ d=2 ⟹ |S∩T|=4、指数 2 ⟹ 正規 (`normal_of_index_eq_two`) ⟹ S,T ≤ N:=N_G(S∩T)、
  |N|∈{24,40,120}。120 case は S∩T◁G → G/(S∩T) 位数 30 → **補題** (位数 30 群は指数 3 or 5
  部分群を持つ: n₅=6∧n₃=10 は計数矛盾 24+20>29 → 正規 Sylow5/3 ⊔ Sylow2) → `comap` 引き戻し
  (`index_comap_of_surjective`)。再利用 helper: `card_sup_of_normal_of_coprime` (正規×coprime join
  の位数積) / `exists_finset_orderOf_eq_card_sylow_mul` (素数位数 Sylow 非単位元 = n_q(q−1) 個) /
  `card_sylow_mul_add_card_sylow_mul_le` (2 素数計数 ≤ |G|−1)。全実証明・axiom-clean。
  ⚠ 教訓: `set` の let 変数は補題適用時に値へ展開され omega が別 atom 視 → `rw [← hDdef]` で
  畳み直す / minimal import では `norm_num` の `Nat.Prime` 拡張が無い → `Mathlib.Tactic.NormNum.Prime`
  を明示 import / `Finset.card_sdiff` は現 mathlib で仮定無し形 (`card_sdiff_of_subset` を使う)。
- ✅ 実証明 **1C.5** (2026-07-25、新 leaf `Ch01_Sylow/ProblemsAlternating.lean`):
  `two_mul_card_normalizer_sylow_alternating` (`2|N_{A_{p+1}}(P)| = p(p−1)`, p 奇素数) +
  除算形 `card_normalizer_sylow_alternating` (`= p(p−1)/2`)。hint 通り位数 p 元 = p-cycle
  (`cycleType_prime_order` + 台 `(n+1)p ≤ p+1` → n=0、p 奇数で偶置換 `IsCycle.sign`) を計数:
  `card_of_cycleType_mul_eq` (mathlib Perm/Centralizer) で `c·p = (p+1)!`、強化した
  `natCard_orderOf_eq_of_sylow_card_eq` (ProblemsOrder120 の計数補題を iff/Nat.card 版に格上げ:
  素数位数 Sylow ⟹ 位数 q 元ちょうど n_q(q−1) 個) で `c = n_p(p−1)`、`|N|·n_p = |A|`・
  `2|A| = (p+1)!` (`two_mul_nat_card_alternatingGroup`+`Nat.card_perm`) を掛け合わせ cancel。
  ⚠ p = 2 (A₃) では不成立 (|N|=3≠1) ゆえ `3 ≤ p` を仮定 (Isaacs 暗黙、docstring 注記)。
  全実証明・axiom-clean。⚠ 教訓: factorial `!` 記法は `open scoped Nat` が要 (minimal import)。
- 🎉 **§1C 完了 (全 8 問)**: 1C.1/1C.2ab/1C.3ab/1C.4/1C.5/1C.6ab/1C.7/1C.8 全て実証明。
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
- ✅ 実証明 **1D.5** (2026-07-25、Isaacs 明記の難問を解決): `disjoint_conj_of_forall_normalizer_le`
  (「全素数 q・全非自明 q-部分群 `P⊆H` に `N_G(P)⊆H`」⟹ `H` は Frobenius complement)。
  **難所だった「Q と Q^g の H-共役」の正体 = Q が実は H の Sylow になること**。論法:
  `D:=H∩H^g≠⊥`, `q∣|D|`, `Q∈Syl_q(D)`。(1) **仮説は D に遺伝** (hint): `N_G(Q)≤H` (仮説) +
  `Q^{g⁻¹}≤H` 非自明 → `N_G(Q^{g⁻¹})≤H` を共役 (`le_normalizer_map` + `pointwise_smul_def`) して
  `N_G(Q)≤H^g` ⟹ `N_G(Q)≤D`。(2) **Q は Syl_q(H)**: `Q⊆S∈Syl_q(H)` で `Q≠S` なら q-群の
  正規化群成長 (Thm 1.22) で `Q<N_S(Q)≤N_G(Q)⊓H≤D` の q-部分群 — Q の D-Sylow 極大性 (`Q₀.3`)
  に矛盾。(3) `Q':=Q^{g⁻¹}` も同位数ゆえ `Sylow.ofCard` で Syl_q(H)、Sylow C (1C.1 の
  `map_conj_smul` transport パターン) で `k∈H`, `(Q')^k=Q` ⟹ `k·g⁻¹∈N_G(Q)≤D≤H` ⟹ `g∈H` 矛盾。
  計数不要・~130 行・axiom-clean。仮定の `P≠⊥` は Isaacs 暗黙 (⊥ を許すと H=G に退化)、`H<G`
  properness は不要 (docstring 注記)。⚠ 教訓: `MulAut.conj g⁻¹ = (MulAut.conj g)⁻¹` は
  defeq でない (`map_inv` で明示 rw) / `subgroupOf`↔`comap subtype` は defeq だが rw は不可
  (`exact` の defeq check で橋渡し)。
- 🎉 **§1D 完了 (全 18 問)**: 1D.1–1D.18 全て実証明/記録。
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
  - ✅ 実証明 **2A.4** (2026-07-25、Wielandt 部分群): `le_normalizer_of_isSubnormal_of_forall_mul_comm`
    (S 単純が全 subnormal J と `SJ = JS` ⟹ S は全 subnormal を正規化)。**|G| 強帰納法 +
    IsSubnormal 構造帰納**。step (H⊴K'◁◁G, IH: S≤N(K')): K'=⊤ 自明 / **S≤K'** は ↥K' に降下
    (仮説移送: `IsSubnormal.trans'` (mathlib) で subnormal を G へ戻し permutability を
    elementwise transport、単純性は `MulEquiv.isSimpleGroup`+`subgroupOfEquivOfLe`、結論は
    `subgroupOf_normalizer_eq`) / **S⊄K'** は S⊓K'⊴S (S≤N(K')) + 単純性で S⊓K'=⊥ →
    K:=S⊔H は台集合 S·H (helper `coe_sup_of_mul_comm` 新設 = SH=HS→部分群構成) →
    M:=normalClosure(H) in ↥K が ≤K' (k=s·h の共役が K' に残る、`normalClosure_le_normal`) →
    S⊓M=⊥ → 計数 |S||M| ≤ |K| = |S||H| (`card_mul_card_inf`) → M=H → H⊴K
    (`normal_subgroupOf_iff_le_normalizer`) → S≤K≤N(H)。~180 行・axiom-clean。
    ⚠ 教訓: 型を跨ぐ強帰納法は `∀ (n) (G : Type*) (_ : Group G) (_ : Finite G), card ≤ n → …` の
    explicit binder 形で書き、適用時は `inferInstance` 明示 / `Set.mem_mul` の obtain した eq は
    β-未簡約 (`show a*b = c*d from heq` で reduce してから rw)。
  - ✅ 実証明 **2A.5(a)(b)(c) + 2A.6** (2026-07-25、deferred-hard tail 完遂)。`X` = minimal normal
    の任意族、`N := sSup X`。
    - **2A.5(a)** `exists_subfamily_indep_sSup_eq` (**種付き強化形**): 独立な部分族 `Y₀ ⊆ X` を与えると
      `Y₀ ⊆ Y ⊆ X` で独立かつ `sSup Y = sSup X` なる `Y` が存在 (= `N` は `X` のいくつかのメンバーの
      直積; 「独立性 + join」が内部直積の定式化)。`Finite.exists_le_maximal` で独立性を保つ極大部分族
      `Y` を取り、`M ⊄ sSup Y` なる `M ∈ X` があれば `M ⊓ sSup Y ⊴ G` が minimality で `⊥` ゆえ
      `insert M Y` も独立 (`T ∈ Y` 側は `x ∈ T ⊓ (sSup (Y∖{T}) ⊔ M)` を `x = w·m` に分解、
      `M` 正規で `mul_normal`) → 極大性に矛盾。**種 `Y₀` が (b) の鍵** (`Y₀ = ∅` が Isaacs の原題)。
    - **hint** `socle_eq_top_of_forall_isMinimalNormal` (`Soc(N) = N`): 各 `M ∈ X` で
      `M.subgroupOf N` 内の minimal normal `W` を取り (`exists_isMinimalNormal_le`)、`G`-正規閉包
      `= M` (minimality)。各 `G`-共役は `MulAut.conjNormal` による `↥N` の自己同型像ゆえ minimal
      normal のまま (`IsMinimalNormal.map_equiv`) → `(socle ↥N).map N.subtype` は `G`-正規で
      `normalClosure W` を含む。helper `apply_mem_socle` (socle は自己同型不変、`iSup_induction`)。
    - **2A.5(b)** `isSimpleGroup_of_isMinimalNormal_of_forall_isMinimalNormal`: `Soc(N) = N` の下で
      (a) を**種 `{V}`** で `↥N` に適用し `N = V ⊔ rest` (独立)。`rest` は `V` と disjoint な正規の
      join ゆえ `V` を中心化 → 任意の `K ⊴ ↥V` の押し出しは `V`-共役 (正規性) と `rest`-共役 (中心化)
      で不変 → `↥N`-正規 → `V` の minimality で `⊥` か `V`。
    - **2A.5(c)** `exists_indep_isSimpleGroup_sSup_eq_top`: (a) を全 minimal normal の族に適用
      (join = socle = `⊤`)、各メンバーの単純性は (b)。
    - **2A.6** `exists_mem_le_of_normal_le_sSup_of_not_isMulCommutative`: 対偶で全 `M ∈ X` に
      `U ⊓ M = ⊥` (minimality) → `Subgroup.commute_of_normal_of_disjoint` で `M ≤ C_G(U)` →
      `U ≤ N ≤ C_G(U)` で `U` 可換、矛盾。
    - ~294 行・sorry 0・`--strict` lint clean。あわせて 2A.4 の帰納核と主定理の間に挟まっていた
      本ブロックを主定理の後ろへ移し文書順・凝集を回復。
  - ✅ 実証明 **2A.9** (2026-07-25) `oPiCore_le_normalizer_of_isSubnormal_of_oPiResidual_eq_top`:
    `H ◁◁ G` が π-perfect (`H = O^π(H)`、形式化は `oPiResidual π ↥H = ⊤`) ⟹ `O_π(G)` が `H` を正規化。
    Isaacs の hint「`G = H·O_π(G)` と仮定してよい」を **`K := H ⊔ O_π(G)` への降下**として実装:
    `P := O_π(G)` 正規ゆえ `↑K = ↑H·↑P`、`Ch01.card_mul_card_inf` + Lagrange で
    `|K:H|·|H⊓P| = |P|` ⟹ `|K:H| ∣ |P|` は π-数 (`oPiCore.isPiGroup`) ⟹ 2A.2 を `↥K` に適用して
    `O^π(K) ≤ H.subgroupOf K`。逆向きは π-perfect 性を `Subgroup.inclusion : ↥H →* ↥K` で押し出す。
    ⟹ `H.subgroupOf K = O^π(K)` は `↥K` で正規 ⟹ `P ≤ K ≤ N_G(H)`。
    **支持 API 新設 (Ch03 `PiResidual.lean`、mathlib 流の関手性)**: `oPiResidual_map_le`
    (任意の `f : A →* B` で `O^π(A)^f ≤ O^π(B)`; 1B.8(b) の π'-元生成 + `orderOf_map_dvd`、
    全射性も単射性も不要) / `subgroupOf_le_oPiResidual_of_eq_top`。
  - ✅ 実証明 **2A.10** (2026-07-25) `isSubnormal_iff_forall_isStronglyConjugate_eq`:
    `H ◁◁ G ⟺ H に強共役な部分群は H 自身だけ`。⚠ **repo に既に Bartels (Thm 9.28) が完備**
    (`Ch09/SubnormalClosure.lean` の `strongClosure_isSubnormal`、sorry 0) で、書籍 p.290 が
    「2A.10 は Bartels の直接の帰結」と明記する通りに導出できた: `⟸` は `H^{(G)} = H` + Bartels、
    `⟹` は Lem 9.29(a) (`strongClosure_le_of_isSubnormal`) で `K ≤ H^{(G)} ≤ H` かつ `|K|=|H|`。
    強共役の定義 `Ch09.IsStronglyConjugate` も既存 (再定義しない)。Ch09 は Ch02 **Basic** しか
    import しないので Ch02 Problems → Ch09 の import に cycle 無し。
  - 🎉 **§2A 完済** (2A.1-2A.10 全 10 問)。

## Ch.2 (Subnormality) §2B — 着手 (2026-07-25)

- ✅ 実証明 **2B.1** `isSubnormal_of_forall_nilpotent_or_permutable` (`Basic.lean` 置き):
  各 `g` ごとに「`⟨H,H^g⟩` 冪零」**or**「`HH^g = H^gH`」⟹ `H ◁◁ G`。**Thm 2.8
  (permutability ⇒ subnormality) の disjunctive 強化**で、`|G|`-induction + Zipper の骨格が
  完全に共通 ⟹ 既存 `isSubnormal_of_permutable_aux` を
  `isSubnormal_of_nilpotent_or_permutable_aux` に一般化して**両者で核を共有**
  (重複コード ~100 行を作らない)。仮説が使われる 2 箇所だけ冪零分岐を追加:
  (i) 真部分群への降下 = `subgroupOf_sup` + `subgroupOfEquivOfLe` で冪零性移送、
  (ii) `S ⊔ S^x = ⊤` 排除 = `topEquiv` で `G` 冪零 ⟹ Lemma 2.1 で全部分群部分正規 ⟹ 仮定に矛盾。
  Thm 2.8 の signature は不変 (`fun x => Or.inr (hperm x)`) ゆえ下流無影響。
  `Problems.lean` 側は §2B section を起こしてポインタのみ記録 (ラッパー方針)。
- ✅ 新 leaf `OddOrder/Isaacs/Ch02_Subnormality/ProblemsInvolutions.lean` (`OddOrder.lean` 配線済)。
  ⚠ repo の `DihedralBasics.lean` は「巡回部分群を反転する involution」型の**抽象**補題群
  (Lemma 2.14 / Matsuyama 用) で mathlib の具体 `DihedralGroup n` は扱っていない — 別物なので
  本 leaf は mathlib `DihedralGroup n` (`r i` / `sr i`, `i : ZMod n`) の上で議論する。
- ✅ 実証明 **2B.2(a)** (2026-07-25、`n` 奇): involution の分類 (`orderOf_r_eq_two_iff`:
  `orderOf (r i) = 2 ⟺ i ≠ 0 ∧ 2i = 0`) から `2` が `ZMod n` の単元ゆえ involution = 鏡映全体
  (`orderOf_eq_two_iff_of_odd`)、個数 `n` (`card_involutions_of_odd`)、単一共役類
  (`isConj_sr_of_odd`: `k + k = i - j` を解いて `r k` で共役)。共役計算 `r_conj_sr`
  (`sr i ↦ sr (i - 2j)`) / `sr_conj_sr` (`sr i ↦ sr (2j - i)`) を helper に。
- ✅ 実証明 **2B.2(b)** (`n = m + m` 偶): `add_self_eq_zero_iff_of_even` (`2i = 0` の解は `0` と `m`
  のみ; `i.val` に降りて `(m+m) ∣ 2·i.val` から `c < 2` 場合分け) ⟹ involution = 全鏡映 + `r m`
  で `n + 1` 個 (`card_involutions_of_even`)。共役類はちょうど 3 つ・サイズ `1, m, m`:
  * `r m` は中心的 (`r_natCast_half_mem_center`、`-m = m` から) ⟹ 類 `{r m}` サイズ 1。
  * **鏡映の類は添字の「偶奇」で決まる**: `parityHom m : ZMod (m+m) →+* ZMod 2` (`2 ∣ n` の
    `ZMod.castHom`) を導入し `parityHom_eq_zero_iff` (`= 0 ⟺` 二倍元) →
    `isConj_sr_sr_iff_of_even`。fiber の個数は `k ↦ k + 1` が 2 fiber 間の全単射 + 互いに補集合
    (`Set.ncard_add_ncard_compl`) から `m` (`ncard_parityHom_fiber`) ⟹ `ncard_conjClass_sr = m`。
  * 3 類の非共役性 = `not_isConj_sr_zero_sr_one` / `not_isConj_sr_r` (後者は
    `exists_sr_of_isConj_sr` = 「鏡映の共役元は鏡映」から)。
- ✅ 実証明 **2B.3** `exists_involution_commuting_of_not_isConj` (有限群で非共役な involution
  `s, t` ⟹ 両方と可換で両者と異なる involution が存在)。**二面体群の構造定理を経由しない**:
  `u := s*t` を `s`,`t` が反転することだけ使い、`|u|` 奇なら `u^{(|u|+1)/2}` 共役で
  `s ↦ u s = s t s⁻¹` ゆえ `s ~ t` (仮定に反する) ⟹ `|u| = 2q` 偶、`z := u^q` が求めるもの。
  ⚠ 有限性は本質的 (`D∞` が反例) — docstring 明記。
- ✅ 実証明 **2B.4** `isConj_of_orderOf_eq_two_of_sylow_ti` (Sylow 2 が複数 + 互いに自明交叉 (TI)
  ⟹ involution はちょうど 1 つの共役類)。計画どおり:
  * `exists_sylow_two_mem` (involution はある Sylow 2 に入る) /
    `exists_sylow_two_mem_of_commute` (**可換な 2 つの involution は共通の Sylow 2 に入る** —
    `closure {s,z}` の可換性は `Subgroup.closure_le_centralizer_centralizer` から出し、
    `closure_induction` で全元 `g*g = 1` ⟹ `IsPGroup 2`) / `sylow_two_eq_of_ti` (一意性)。
  * 核 `isConj_of_sylow_two_ne`: 相異なる Sylow 2 の involution は共役 (対偶で 2B.3 の `z` を
    取ると両方が同じ Sylow に落ちて矛盾)。
  * 同じ Sylow の場合は Sylow の共役性 (`MulAction.exists_smul_eq` + `Sylow.coe_subgroup_smul`)
    で別 Sylow 内に `g s g⁻¹` を作って経由。
  * `exists_orderOf_eq_two_of_exists_sylow_two_ne` で involution の実在も示し「ちょうど 1 つ」
    が空でないことを保証。
- ✅ 実証明 **2B.5** `generalizedDihedral_tfae` (`List.TFAE`) + `isMulCommutative_of_generalizedDihedral`。
  指数 2 の `B ≤ G` について (1) `G∖B` に `B` を反転する involution が在る / (2) `G∖B` が
  involution だけ / (3) `G∖B` の全元が `B` を反転する involution、の同値と `B` の可換性。
  支持: `inv_mul_mem_of_notMem_of_index_eq_two` (`Subgroup.index_eq_two_iff'` から) /
  `mul_notMem_of_mem_of_notMem` / `exists_notMem_of_index_eq_two`。**有限性不要**。
- ✅ 実証明 **2B.6** `exists_normal_sylow_iff_forall_conj_pair` (正規 Sylow p ⟺ `p`-冪位数の
  共役元対 `⟨x, x^g⟩` が全て正規 Sylow p をもつ)。核は repo 既存の **Baer-Suzuki**
  (Thm 2.15 = `Theorem211Wielandt.lean` の `baerSuzuki_pCore`)。橋渡し 2 補題を新設:
  `coe_eq_opCore_of_normal` (正規 Sylow = `O_p(G)`) と `exists_normal_sylow_iff_isPGroup`
  (`p`-冪位数の元で生成される群では「正規 Sylow をもつ」=「`p`-群」)。後者で右辺が
  Baer-Suzuki の右辺そのものになる。生成元を部分群型へ移す配線は
  `Subgroup.map_injective H.subtype_injective` + `MonoidHom.map_closure`。
- 🎉 **§2B 完済** (2B.1-2B.6)。

## Ch.2 (Subnormality) §2C — 着手 (2026-07-25)

新 leaf `OddOrder/Isaacs/Ch02_Subnormality/ProblemsNGroups.lean` (`OddOrder.lean` 配線済)。
§2C の演習は **2C.1 のみ** ((a)(b) の 2 パート)。`IsLocal` (local 部分群) は §2C 本文の
`Theorem211Wielandt.lean` に既存、本 leaf で `IsNGroup` (全 local 部分群が可解) を定義。

- ✅ 実証明 **2C.1(a)** `isSolvable_quotient_of_isNGroup` (N-群の真の準同型像 `G ⧸ N`
  (`N ≠ ⊥`) は可解)。`p ∣ |N|` の Sylow `P ∈ Syl_p(N)` を `G` 側に写した `Q ≠ ⊥` について
  Frattini (`Sylow.normalizer_sup_eq_top`) で `N_G(Q) ⊔ N = ⊤`、`N_G(Q)` は local ゆえ可解、
  `N` 正規で `↑(N_G(Q) ⊔ N) = ↑N_G(Q)·↑N` だから `N_G(Q) → G ⧸ N` 全射 ⟹
  `solvable_of_surjective`。
- ✅ 実証明 **2C.1(b)** (2026-07-25)。4 定理に分割:
  * `exists_isMinimalNormal_of_not_isSolvable` (存在) / `isMinimalNormal_unique_of_isNGroup`
    (一意性: `S₁ ⊓ S₂ = ⊥` から `G ↪ (G⧸S₁)×(G⧸S₂)`、(a) で両因子可解 ⟹ `G` 可解で矛盾) /
    `not_isSolvable_of_isMinimalNormal_of_isNGroup` / `isSimpleGroup_of_isMinimalNormal_of_isNGroup` /
    `not_isMulCommutative_of_isMinimalNormal_of_isNGroup`。
  * 単純性は計画どおり: `↥S` の minimal normal `T` が `⊤` でなければ、`T` を動かす `g` が
    存在し (さもなくば押し出しが `G`-正規で `S` の minimality に反する)、`V := T^g` と
    `T ⊓ V = ⊥` から元ごと可換 ⟹ `T` の素数位数元の `⟨x⟩` について `V ≤ C_G(⟨x⟩) ≤ N_G(⟨x⟩)`
    が可解 ⟹ `T` 可解 ⟹ `⁅T,T⁆ = ⊥` (minimality + `commutator_lt_top_of_nontrivial`) ⟹
    `T` 冪零 ⟹ `T ≤ F(↥S)` (Thm 2.2) ⟹ `F(↥S)` の押し出しが `G`-正規非自明 ⟹
    `F(↥S) = ⊤` ⟹ `↥S` 冪零 ⟹ 可解で矛盾。
  * ⚠ `IsSolvable.commutator_lt_of_ne_bot` は**周囲の群**の可解性を要求するので使えず、
    `commutator ↥T = ⊤` に落として `IsSolvable.commutator_lt_top_of_nontrivial` を使う。
- 🎉 **§2C 完済** (2C.1(a)(b))。

## Ch.2 numbered results の被覆 — 陳腐化 docstring を訂正 (2026-07-25)

§2D の演習を見に行く過程で `Ch02_Subnormality/Basic.lean` の章被覆表が FT 経路時代のまま
**実測と食い違っている**ことが判明し訂正 (commit 済): 2A「着手中」/ 2C・2D「TODO」は
すべて誤りで、**2.1-2.20 は全部実在**する (2.18 = `zenkov_minimal_le_fitting`,
2.19 = `inf_fitting_ne_bot_of_abelian_card_ge_index`, 2.20 本体 =
`Ch04/ForwardFromCh02.lean` の `lucchini_index_normalCore_lt_index`)。`Main.lean` の
「`lucchini_K_bot_aux` axiom」注記も誤り (実際は private theorem) で訂正済。
Ch.2 は全ファイル sorry-free。

## Ch.2 (Subnormality) §2D — 次の frontier

§2D の演習は 2 問。**Zenkov (Thm 2.18) と Cor 2.19 が repo に既存**なので素材は揃っている。

- ✅ 新 leaf `OddOrder/Isaacs/Ch02_Subnormality/Problems2D.lean` (`OddOrder.lean` 配線済)。
  素材は repo 既存の Cor 2.19 (`inf_fitting_ne_bot_of_abelian_card_ge_index`) と
  Lucchini (`Ch04.lucchini_index_normalCore_lt_index`)。共通の位数補題
  `index_mul_card_inf_eq_card_of_sup_eq_top` (`|G:A|·|N ∩ A| = |N|`) /
  `index_le_card_of_card_le` / `le_centralizer_of_inf_eq_bot` を先に用意。
- ✅ 実証明 **2D.1(a)** `card_lt_card_of_fitting_eq_bot`: `|A| ≥ |N|` を仮定すると Cor 2.19 で
  `A ⊓ F(G) ≠ 1`、`F(N) = 1` から `F(G) ⊓ N = ⊥` (新補題
  `fitting_inf_eq_bot_of_fitting_eq_bot`、Thm 2.2 経由) ⟹ `F(G) ≤ C_G(N)` ⟹
  `A ⊓ F(G) ≤ A ⊓ C_G(N) = 1` で矛盾。
- ✅ 実証明 **2D.1(b)** `card_lt_card_of_coprime`: 同じ骨格で、`F(N) = 1` の代わりに
  `π := {q | q ∤ |N|}` を使う。`A ⊓ F(G)` は π-群、`F(G)` 冪零ゆえ `↥F(G)` 内で部分正規、
  **自分で証明した 2A.1** (`le_oPiCore_of_isSubnormal_of_isPiGroup`) で `O_π(↥F(G))` に落ち、
  `O_π` 特性的ゆえ押し出し `Q` は `G`-正規な π-群 ⟹ `Q ⊓ N = ⊥` ⟹ `Q ≤ C_G(N)` ⟹ 矛盾。
- ✅ 実証明 **2D.2** `card_lt_card_of_isCyclic`: `core_G(A) ⊓ N ≤ A ⊓ N = 1` かつ両者正規で
  `core_G(A) ≤ A ⊓ C_G(N) = 1`、**Lucchini** の `|A : core_G(A)| < |G:A|` に `|G:A| = |N|`
  を代入。
- ⚠ **2D.1 は書籍が書いていない `N ≠ 1` を要する** (`N = 1` なら `C_A(N) = A` ゆえ `A = 1` で
  `|A| = |N| = 1`、結論 `|A| < |N|` が偽)。2D.2 では書籍自身が `N` 非自明を明示しているので
  2D.1 でも同じ暗黙の仮定を置くのが原意と解し docstring に明記。
- 🎉 **§2D 完済** ⟹ **Isaacs Ch.2 の章末演習 (§2A-§2D) 全問完済**。

### 3A.8 のメモ (2026-07-25)

**核は landing 済** (`exists_unique_fixes_inverts`)。`n = s·m` (`gcd(s,m)=1`, `n` 奇, `1 < m`)
で「`s`-捩れの生成元 `m` を固定し `m`-捩れの生成元 `s` を反転する」`u : ZMod n` の一意存在 +
`u² = 1` + `u ≠ 1`。**CRT の一般論は不要で Bezout だけで閉じる**のがポイント:
`sA + mB = 1` から `e := mB` が `e·m = m`, `e·s = 0`, `e² = e` をみたし `u := -1 + 2e`。

**landing 済 (2026-07-25)**:
- `exists_unique_fixes_inverts` (核: 一意存在 + involution)。
- Bezout 系の再利用可能な支持補題: `exists_bezout_zmod` / `eq_of_fixes_inverts` (一意性のみを
  切り出したもの、奇数性不要) / `inverts_mul` / `fixes_mul` / `inverts_of_inverts_coprime` /
  `fixes_of_fixes_coprime`。
- (a) の捩れ表現 `fixes_inverts_iff_torsion` (生成元での条件 ⟺ 「`s`-捩れを全部固定し
  `m`-捩れを全部反転」)。書籍の言い回しに一致。
- (b) `mul_eq_of_fixes_inverts_pqr` (`u_p · u_q = u_r`) ⟹ `{1,u_p,u_q,u_r}` は Klein 四元群。

**(c) も landing 済 (2026-07-25)** ⟹ **3A.8 完了**。
基盤: `zmodUnitsAction` / `zmodSemidirect n K` / `conj_inl_apply` / `inl_ofAdd_one_pow` /
`conj_pow_fixes_iff` (`α^j` が `⟨x,k⟩` を固定 ⟺ `j·(1-k) = 0`)。
本体: `kleinSubgroup` (3 involution が張る位数 4 の部分群) / `mem_kleinSubgroup` /
`two_mul_ne_zero_of_odd_prime_factor` / `conj_pow_ne_one` / **`no_regular_orbit_klein`**。

⚠ **実装上の罠 3 件** (同種の作業で再発しうる):
1. `ZMod (p*q*r)` は**法が型に現れる**ので `rw [mul_assoc]` が型内の `p * q * r` にマッチして
   motive 破綻する。`mul_assoc up uq` と引数を固定すること。
2. 構造体フィールドの証明で `rcases ha with rfl|…` を使うと、**定義の束縛変数** (`up` 等) が
   substitution で消える。`rw [ha]` を使うこと。
3. `eq_inv_of_mul_eq_one_left h : up = up⁻¹` を simp 補題にすると `up → up⁻¹ → up⁻¹⁻¹ → …` で
   無限ループ (maxRecDepth 到達)。`inv_eq_of_mul_eq_one_left` (`up⁻¹ = up`) を使うこと。

### §3A leaf の分割 (2026-07-25)

`Ch03/Problems.lean` が 1363 行になり上限 1500 に近づいたため、先頭の 3A.1 (semidihedral) /
3A.2 (一般化四元数群) クラスタを sibling leaf `ProblemsSemidihedral.lean` へ **prefix-split**
(元 `Problems.lean` がそれを import、module 名不変で下流無影響)。
分割後: `ProblemsSemidihedral.lean` 588 行 / `Problems.lean` 801 行。宣言数 93 が一致すること
を確認済。`OddOrder.lean` 配線も同 commit。

### 3A.10 のメモ

`G := Multiplicative (ZMod p) ≀[H] H` (正則 wreath product)、`A := base group` で全部出る。

**landing 済 (2026-07-25)**: `conj_inl_of_comm` (`D` 可換なら任意の `x` による base 元の共役は
座標置換のみ — `WreathProduct.ext` + `mul_left`/`inv_left` から直接計算) /
`eq_inl_of_right_eq_one` / **`centralizer_range_inl_eq`** (= `A = C_G(A)`、指示関数の技)。

**束ね上げも landing 済 (2026-07-25)** ⟹ **3A.10 完了**。`zpWreath` / `zpWreathBase` /
`zpWreathBase_spec` (可換・`p` 乗して 1・分裂 (`A ⊓ inr.range = ⊥`, `A ⊔ inr.range = ⊤`)・
`G/A ≅ H`・`A = C_G(A)`)。`A ⊴ G` は `range_inl_normal` を instance 化。
あわせて `WreathProduct` の一般 API を補完: `inl_left_mul_inr_right` (`SemidirectProduct` 側に
あって wreath 版に無かった分解補題) / `range_inl_normal` / `rightHom_surjective`。


⚠ 実装上の罠 (今回): `WreathProduct` の補題を `rw`/`congrArg` で使うとき、`Ω` が
metavariable のままだと `MulAction ?m ?m` で instance 解決が詰まる。`conj_inl_of_comm hD x` の
ように**引数を明示**するか、`rw [← map_mul]; congr 1` のように `inl` を露出させない形にする。

### 3A.7 の証明 (2026-07-25 landing)

`exists_regular_orbit_of_primeFactors_card_le_two`。骨格は 2 段:
1. 「`g` の安定化群が非自明 ⟹ ある素因子 `r ∣ n := o(α)` で `α^{n/r}` が `g` を固定」。
   `α^j ≠ 1` が `g` を固定するとき `m := gcd(n,j)` について **Bezout** で `α^m = (α^j)^b`
   (`α^n = 1` を使う) ゆえ `α^m` も固定、`orderOf (α^j) = n/m ≠ 1` の素因子 `r` を取ると
   `m·r ∣ n` すなわち `m ∣ n/r` で `α^{n/r} = (α^m)^c` も固定。安定化群は
   `MulAction.stabilizer (MulAut G) g` として扱うと冪の処理が部分群の閉性で済む。
2. よって regular orbit が無いと `G` は固定部分群 `F r = eqLocus (α^{n/r}) id` (高々 2 個) の
   合併。各 `F r` は真部分群 (`orderOf (α^{n/r}) = r > 1`) で、**群は 2 つの真部分群の合併に
   ならない** (`not_forall_mem_or_mem_of_ne_top`) から矛盾。

⚠ この「2 つの真部分群の合併にならない」は 3A.6 には**そのままでは効かない**: 3A.6 の
`G = ⋃_{1≠z∈V} C_G(z)` は `V` の階数が 2 以上だと 3 個以上の合併になり、群は 3 個以上の
真部分群の合併になりうる (階数 1 のときだけこの筋で閉じる)。

## Ch.3 §3B — 次の frontier (演習 3B.1-3B.15)

`§3B` は Schur-Zassenhaus と可解群の節で、演習が 15 問ある:
3B.1 (可解群の極大部分群は素冪指数) / 3B.2 (可換因子の subnormal 列 ⟹ 可解) /
3B.3 (合成因子が全て素数位数 ⟺ 可解) / 3B.4 (`|N|` と `|G:N|` 互いに素、`|U| ∣ |G:N|` ⟹
`U` はある補群に含まれる) / 3B.5 (`P ∈ Syl_p(G)` が中心に含まれる ⟹ `G = X × P`) /
3B.6 (剰余類の代表の位数) / 3B.7 (supersolvable) / … / 3B.14 (`C = C_G(F(G))`) /
3B.15 (Berkovich)。文書順に 3B.1 から。

### 3A.6 の解析 (2026-07-25、deferred-hard として記録)

**確立できた部分** (次に着手する人はここから始めてよい):
- `Γ := G ⋊ P` を作ると `p ∤ |G|` ゆえ `P ∈ Syl_p(Γ)`、Sylow p-部分群は `{P^g : g ∈ G}`。
- **`P ∩ P^g = P_g` (= `g` の `P`-安定化群)**: `u ∈ P` に対し `g⁻¹ u g = (g⁻¹ · u(g)) u` なので
  `g⁻¹ u g ∈ P ⟺ u(g) = g`。すなわち **Sylow 交叉 = 点安定化群**。
- **`O_p(Γ) = 1`**: `O_p(Γ) ∩ G = 1` (位数) ゆえ `[O_p(Γ), G] = 1` で `O_p(Γ) ≤ C_Γ(G)`、
  かつ `O_p(Γ) ≤ P`、`P` の作用が faithful なので `P ∩ C_Γ(G) = 1`。
- **軌道 `Δ = P·h` 上の核は `core_P(P_h)`** (`P_{u(h)} = (P ∩ P^h)^{u⁻¹}` から)。
- **`core_P(P_h) = 1 ⟺ P_h ∩ Z(P) = 1`** (`p`-群の非自明正規部分群は中心と非自明に交わる;
  逆に `Z(P)` の位数 `p` の元は `P`-正規)。⟹ **目標は「`C_{Z(P)}(h) = 1` なる `h ∈ G` の存在」**、
  さらに `V := Ω_1(Z(P))` として「`G ≠ ⋃_{1≠z∈V} C_G(z)`」と同値。
- Brodkey (Thm 1.38) + `O_p(Γ) = 1` から、交わり極小な Sylow 対 `(S,T)` について
  **`Z(S) ∩ Z(T) = 1`** は出る (`Z(S) ∩ Z(T)` は `Z(S)` の部分群ゆえ `S`-正規、同様に `T`-正規)。

**詰まっている一手**: 必要なのは `Z(P) ∩ P^h = 1` (より強い) であって `Z(P) ∩ Z(P^h) = 1` では
足りない。`core_P(D)` が `P^h` でも正規になる (⟹ Brodkey が直接使える) ことが示せれば閉じるが、
交わり極小性からそれを出す一手が未確定。**次に試すこと**: (i) Isaacs p.76 前後の本文/他の演習で
1.38 の使い方を確認、(ii) 極小 Sylow 交叉の古典補題 (`N_S(D) ∩ N_T(D)` 系) を当たる、
(iii) [[feedback-ask-chatgpt-for-elided-gaps]] に従い最強モデルに再構成を依頼。

## Ch.3 (Split Extensions) §3A — 着手 (2026-07-23、§2A hard tail deferred 中の breadth 展開)

新 leaf `OddOrder/Isaacs/Ch03_SplitExtensions/Problems.lean` (namespace `OddOrder.Isaacs.Ch03`、
import `Mathlib.GroupTheory.SemidirectProduct`+`Tactic.Group`、`OddOrder.lean` 配線済)。

- ✅ 実証明 **3A.3** 位数 pm 群 (正規 P 位数 p, G/P 巡回, Z(G)=1) — 2026-07-23 **完全完成**:
  σ=×u (位数 m, `AddAut.mulLeft`+`MulAutMultiplicative`) / `affineGroup u = Mult(ZMod p) ⋊ ⟨σ⟩` /
  `affineGroup_card` (|G|=p·orderOf u) / `affineGroup_card_ker` (P=ker rightHom 位数 p, 正規) /
  `affineGroup_quotient_isCyclic` (G/P 巡回) / **`affineGroup_center_eq_bot`** (Z(G)=⊥、u≠1) /
  `exists_group_card_eq_normal_cyclic_center_trivial` (存在まとめ)。center は (a,h)∈Z → φ(h)=id⟹h=1、
  a=σ(a)⟹(u-1)·toAdd a=0⟹a=1 (体 ZMod p で u-1 可逆)。⚠ `Multiplicative (ZMod p)` の ring/group Mul
  instance 衝突は **cancel を toAdd で ZMod p 加法に落として `add_left_cancel`** で回避 (教訓記録)。
  全実証明・sorry 無・axiom-clean。
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
- ✅ 実証明 **3A.4** (2026-07-25) `affineGroupOfField` 系: 有限体 `F` の `Fˣ` が `(F,+)` に作用する
  半直積 `G = Multiplicative F ⋊ Fˣ` (3A.3 の `affineGroup` と同じ `MulAutMultiplicative` +
  `AddAut.mulLeft` idiom)。`|G| = q(q-1)` / `|ker rightHom| = q` / `ker` は基本アーベル `p`-群 /
  位数 `p` の元は `right = 1` (`orderOf right` が `p` と `q-1` を割るが互いに素) で
  `inl x` (`x ≠ 0`) の形、`Fˣ` が `F ∖ {0}` に推移的だから単一共役類
  (`SemidirectProduct.inl_aut`)。まとめ `exists_group_card_eq_elementaryAbelian_isConj` は
  `GaloisField p k` を代入 (⚠ `GaloisField.card` は **`Nat.card` で述べられている**ので
  `Fintype` 経由は不要)。

### ⚠ §3A の被覆は実測で更新 (2026-07-25)

本 issue の §3A 記載は古く、**3A.3 と 3A.5 は既に完成済み**だった (実測で確認)。現状:

| 問題 | 状態 |
|---|---|
| 3A.1(a)(b)(c) | ✅ (semidihedral) |
| 3A.2 | ✅ (一般化四元数群) |
| 3A.3 | ✅ (位数 pm, Z(G)=1) |
| 3A.4 | ✅ (2026-07-25) |
| 3A.5 | ✅ (`G ⋊ G ≅ G × G`) |
| 3A.6 | ⏸ **deferred-hard** (2026-07-25 に解析; 下記) |
| 3A.7 | ✅ **完了** (2026-07-25) |
| 3A.8 | ✅ **完了** ((a)(b)(c) すべて) |
| 3A.9 | ✅ **完了** ((a)(b)) |
| 3A.10 | ✅ **完了** (`zpWreathBase_spec`) |

- ⬜ **次: §3A 続き or §2A hard tail 再訪。§1D 残り = 1D.5 (Isaacs-noted-hardest)。**

## 完了条件

Isaacs Ch.1–10 の全演習問題が形式化 (実証明 or mathlib/repo 対応の docstring 記録)、
build green、AxiomsCheck OK。章単位で commit・issue checkbox 更新。

## 参照

- issue 9205 (scope 拡大の裁定元)、`notes/isaacs/frontier_measured_2026_07_19.md` (番号付き結果の完済正本)
- `references/isaacs/finite-group-theory.pdf` (statement 確定用、PDF ページ = 書籍ページ + 13)
- CLAUDE.md「トレーサビリティ」「ファイル粒度」「ラッパー方針」

---

## ❄ 2026-07-24 FROZEN (ユーザー裁定) — pending へ

Isaacs Problems campaign (lane a の現 frontier) はユーザー裁定で凍結。再開時は本文の
文書順 (Ch.1 §A から) と置き場規約 (ChNN/Problems*.lean) をそのまま引き継ぐ。
lane a の次 frontier は hub 裁定 (9500 番台) で再割当。

## ☀ 2026-07-25 UNFROZEN (ユーザー指示) — open へ復帰

ユーザー指示「凍結してた問題を解くやつをやります」で campaign 再開。文書順で最古の未完
= **§1C の 1C.4 / 1C.5** (deferred-heavy) から再訪 → 以降 1D.5 / §2A hard tail
(2A.4/5/6/9) / §3A 残り (3A.4/6/7/8) / §3B〜 の順。

**2026-07-25 の消化**: 1C.4 ✅ / 1C.5 ✅ / 1D.5 ✅ / 2A.4 ✅ / 2A.5(a)(b)(c) ✅ / 2A.6 ✅ /
2A.9 ✅ / 2A.10 ✅ (**§2A 完済**) / 2B.1 ✅。
さらに 2B.2(a)(b) ✅ / 2B.3 ✅ (新 leaf `Ch02_Subnormality/ProblemsInvolutions.lean`)。
さらに 2B.4 ✅ / 2B.5 ✅ / 2B.6 ✅ で **§2B も完済**。
さらに **2C.1(a) ✅ / 2C.1(b) ✅ で §2C も完済**。あわせて Ch.2 の陳腐化した被覆表
(2A/2C/2D を誤って TODO と記載) も実測に合わせて訂正。
さらに **§2D も完済 (2D.1(a)(b) / 2D.2)** ⟹ **Isaacs Ch.2 の章末演習は全問完済**。
さらに **3A.4 ✅** (3A.3 / 3A.5 は既済と実測判明)。
さらに **3A.9(a) ✅**。**3A.6 は deferred-hard** (解析は §3A 節に記録; Brodkey の適用の一手が
未確定)。さらに **3A.8(a) の核 ✅**。さらに **3A.8(a)(b) ✅**。さらに **3A.8(a)(b) のまとめ ✅**。さらに **3A.8(c) の基盤 ✅**。さらに **3A.8(c) ✅ ⟹ 3A.8 完了**。
⚠ `Ch03/Problems.lean` は **1363 行** (上限 1500) — **次の追加の前に §3A leaf を分割する**
(CLAUDE.md のファイル粒度規約: 3A.1/3A.2 の semidihedral・一般化四元数クラスタ (~550 行) を
別 leaf へ出すのが自然)。
さらに **§3A leaf 分割 ✅ / 3A.9(b) ✅ (3A.9 完了)**。
さらに **3A.10 の核 ✅** (`A = C_G(A)`)。
さらに **3A.10 ✅** ⟹ **§3A は 3A.6 / 3A.7 を除いて完了**。
さらに **3A.7 ✅** ⟹ **§3A は 3A.6 のみ残り** (deferred-hard)。
さらに **3B.1 ✅ / 3B.2 ✅ / 3B.3 ✅** (新 leaf `Ch03_SplitExtensions/Problems3B.lean`)。
さらに **3B.4 ✅ / 3B.5 ✅**。
**次 frontier = 3B.8 から文書順**。3A.6 は §3B を進めた後に再訪する。

### §3B の記録 (2026-07-25)

| # | 状態 | Lean 名 (`OddOrder.Isaacs.Ch03`) |
|---|---|---|
| 3B.1 | ✅ | `index_isPrimePow_of_isCoatom` (+ 対応定理 `isCoatom_map_mk'_of_isCoatom`) |
| 3B.2 | ✅ | `isSolvable_of_commutator_series` (+ 教科書形との往復 3 補題) |
| 3B.3 | ✅ | `isSolvable_iff_forall_prime_card_of_simple_factors` |
| 3B.4 | ✅ | `exists_isComplement'_le_of_coprime` (+ `isComplement'_conj`) |
| 3B.5 | ✅ | `exists_subgroup_orderOf_not_dvd_isComplement'` |
| 3B.6(a) | ✅ | `exists_mem_coset_primeFactors_orderOf_dvd` |
| 3B.6(b) | ✅ | `orderOf_eq_of_primeFactors_orderOf_dvd_of_coprime` |
| 3B.6(c) | ✅ | `isConj_inv_of_quotient_isConj_inv` (+ `isComplement'_subgroupOf_of_coprime`) |
| 3B.6 まとめ | ✅ | `exists_mem_coset_orderOf_eq_and_isConj_inv` |
| 3B.7(a) | ✅ | `card_prime_of_isMinimalNormal_of_isSupersolvable` (新 leaf `ProblemsSupersolvable.lean`) |
| 3B.7(b) | ✅ | `index_prime_of_isCoatom_of_isSupersolvable` |

**設計メモ**:

- **3B.2/3B.3 の「列」の表し方**: 因子が abelian という仮説は交換子形
  `⁅Nᵢ₊₁, Nᵢ₊₁⁆ ≤ Nᵢ` で表した。これなら包含も正規性も有限性も要らず (すべて従属)、
  教科書形 (`Nᵢ ⊴ Nᵢ₊₁` + 商 abelian) との往復は 3 補題
  (`commutator_le_of_quotient_isMulCommutative` / `normal_subgroupOf_of_commutator_le` /
  `quotient_isMulCommutative_of_commutator_le`) が与える。
  3B.3 の**単純因子**は商群を直接書くと仮説内で `Normal` instance を捏ねる必要が出るので、
  「抽象群 `Qᵢ` + 全射 `Nᵢ₊₁ ↠ Qᵢ` (核 = `Nᵢ`)」の形で与えた (`Qᵢ ≅ Nᵢ₊₁/Nᵢ` と同値)。

- **3B.4 のために Basic.lean の SZ D-part を一般化した**:
  `exists_conj_le_of_isComplement'_of_coprime` は `IsSolvable ↥M` を要求していたが、
  教科書 3B.4 は「`N` **または** `U` が可解」で足りる。そこで一般版
  `exists_conj_le_of_isComplement'_of_coprime'` (`IsSolvable ↥M ∨ IsSolvable ↥U`) を新設し、
  既存名はその `Or.inl` 特殊化として残した (BG/Peterfalvi 側 5 箇所の呼び出しは無変更)。
  `U` 可解の側は `IsComplement'.QuotientMulEquiv` で `↥P ⧸ M.subgroupOf P ≃* ↥(U.subgroupOf P)`
  を作り、SZ 共役性の「商が可解」枝に流す。
  さらに 3B.6(c) のために結論も強化した (`∃ x ∈ M, U ≤ K^x` — 共役元が `M` の中にあることは
  証明中で既に得ていた情報)。既存名の側で `⟨x, _, hx⟩` に落とすので下流は無変更。

- **3B.6(a) の π-分解は Hall E-定理で得る**: `⟨g⟩` は可換ゆえ可解なので `hall_E_exists` が
  π-Hall 部分群 `C` を与え、`|⟨g⟩| = |C| · [⟨g⟩:C]` が求める π/π'-分解になる (自然数の
  π-part を factorization で作る必要がない)。あとは中国剰余定理で `t ≡ 1 (mod m)`,
  `[⟨g⟩:C] ∣ t` なる `t` を取り `h := g^t`。教科書 hint の「`NC = N⟨g⟩` なる巡回 π-部分群 `C`」
  と同じ道具立て。

- **3B.7 で超可解群を定義した** (`ProblemsSupersolvable.lean`, repo/mathlib いずれにも無かった):
  `IsSupersolvable G := ∃ r N, (∀ i, (N i).Normal) ∧ N 0 = ⊥ ∧ N r = ⊤ ∧
  ∀ i < r, ∃ x ∈ N (i+1), N (i+1) = N i ⊔ ⟨x⟩`。因子の巡回性を `Nᵢ₊₁ = Nᵢ ⊔ ⟨x⟩` で表すと
  商の `Normal` instance を仮説内で作らずに済み、`Nᵢ ≤ Nᵢ₊₁` も自動。
  `IsSupersolvable.isSolvable` は 3B.2 経由、`IsSupersolvable.quotient` も証明済 (3B.7(b) の
  帰納で使う)。3B.9 / 3B.10 も同じ定義を使う予定。

- **3B.6(c)**: `H := N⟨h⟩` の中で `⟨h⟩` は `N` の補群 (`isComplement'_subgroupOf_of_coprime`
  を新規に証明)。`h₂ := x h x⁻¹` の生成する `⟨h₂⟩` は位数 `o(h)` で `|N|` と互いに素なので
  D-part の **`U` 可解枝** (`⟨h₂⟩` は巡回) が使え、`⟨h₂⟩ ≤ ⟨h⟩^y` (`y ∈ N`) を得る。
  `⟨h⟩ ⊓ N = 1` より `G ⧸ N` での像を比べて `k = h⁻¹`, すなわち `h ~ h⁻¹`。
