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
- [x] Ch.5 Transfer — **着手 (2026-07-26)**、下記 §5A 節参照
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
足りない。

#### 2026-07-25 の再攻略で得た**より鋭い定式化** (次に着手する人はここから)

`V := Ω₁(Z(P))` とおく。**「どの軌道も faithful でない」⟺ 全ての `g ∈ G` で `V ∩ P^g ≠ 1`**
(∵ 軌道核 `core_P(P_g) ≠ 1 ⟺ P_g ∩ Z(P) ≠ 1 ⟺ P_g ∩ V ≠ 1`、かつ `P_g = P ∩ P^g`)。
すなわち **`V` が `Γ = G ⋊ P` の全ての Sylow `p`-部分群と非自明に交わる**という仮定。

交わり極小な Sylow 対を `(S, T) = (P, P^g)` に取ると (共役で `S = P` としてよい):
- Brodkey (Thm 1.38) + `O_p(Γ) = 1` ⟹ **`Z(S) ∩ Z(T) = 1`** (両者に正規な `D` の部分群だから)。
- `V ≤ Z(S)`、`V^g ≤ Z(T)` ⟹ **`V ∩ V^g = 1`**。
- 仮定から **`V ∩ T ≠ 1`** かつ **`V^g ∩ S ≠ 1`**。

⟹ **残る一手は「`V ∩ T ≠ 1` を `V ∩ Z(T) ≠ 1` に格上げする」だけ** (格上げできれば
`1 ≠ w ∈ V ∩ Z(T) ≤ Z(S) ∩ Z(T) = 1` で即座に矛盾し、問題が閉じる)。
同値な言い換え: 「`V ∩ T` の非自明な部分群で `T`-正規なものを見つける」。
`p`-群の非自明部分群は一般に中心と交わらない (交わるのは**正規**部分群) ので、
`V ∩ T` の `T`-正規性を出す構造 (極小交叉の古典補題 or 別の Sylow 対の選び方) が要る。

#### 🎉 2026-07-26: **3A.6 の欠けていた一手が見つかった (数学的には解決)**

**statement** (PDF で確認): `P` が `p`-群で位数が `p` で割れない群 `G` に **faithful** に
自己同型で作用するなら, ある `P`-軌道 `Δ ⊆ G` 上で `P` は faithful に作用する。
hint = Thm 1.38 (generalized Brodkey)。

これまでの停滞は `V := Ω₁(Z(P))` を経由する被覆論法 (`G = ⋃ C_G(v)` の否定) に固執した
ことが原因で, **`V` は不要**。正しい鍵は次の**正規性**:

> **軌道 `Δ_g = {u(g) : u ∈ P}` の各点固定部分群 `N := core_P(P_g)` は `P` だけでなく
> `P^g` でも正規。**

これで Thm 1.38 が直接効く。証明の全体:

1. `Γ := G ⋊ P`。`p ∤ |G|` ゆえ `P ∈ Syl_p(Γ)`, かつ Sylow `p`-部分群は
   `{P^g : g ∈ G}` (共役元の `P`-成分は `P` を動かさない)。
2. `P` の作用が faithful ⟹ **`O_p(Γ) = 1`** (既記録: `O_p(Γ) ⊓ G = 1` (位数) ⟹
   `⁅O_p(Γ), G⁆ = 1` ⟹ `O_p(Γ) ≤ C_Γ(G) ⊓ P = 1`)。
3. **`P ∩ P^g = P_g`** (点安定化群)。∵ `g⁻¹ u g = inl(g⁻¹ · u(g)) · u` なので
   `g⁻¹ u g ∈ P ⟺ u(g) = g`, さらにそのとき `g⁻¹ u g = u`。
4. `Δ_g` 上の核は `N = ⋂_{u∈P} P_{u(g)} = core_P(P_g)` (`P_{u(g)} = u P_g u⁻¹`)。
5. **⭐ 核 `N` は `P^g` でも正規** — これが欠けていた一手:
   `t ∈ P^g` を `t = inl(w) · u` (`w := g⁻¹ · u(g) ∈ G`, `u ∈ P`) と書き, `n ∈ N` に対し
   `t n t⁻¹ = inl(w) · (u n u⁻¹) · inl(w)⁻¹`。`m := u n u⁻¹ ∈ N` (`N ⊴ P`) で
   `inl(w) · m · inl(w)⁻¹ = inl(w · m(w)⁻¹) · m`。
   ここで **`m` は `Δ_g` を各点固定するので `g` と `u(g)` を固定 ⟹ 自己同型ゆえ
   `w = g⁻¹ · u(g)` も固定** (`m(w) = m(g)⁻¹ · m(u(g)) = w`)。よって `t n t⁻¹ = m ∈ N`。
6. `|P ∩ P^g|` を最小にする `g` を取る (Sylow が全て `P^g` の形なので **これが Γ での
   極小 Sylow 交叉**)。`N ≤ P ∩ P^g` は `P` でも `P^g` でも正規だから **Thm 1.38** より
   `N ≤ O_p(Γ) = 1` ⟹ `P` は `Δ_g` に faithful に作用する ∎

⚠ 被覆論法 (`V` 経由) は**筋が悪い**ので追わない (階数 ≥ 2 で被覆数が増え閉じない)。

#### 🎉 Lean 実装完了 (2026-07-26) — 新 leaf `Ch03_SplitExtensions/ProblemsFaithfulOrbit.lean`

| 部品 | Lean 名 |
|---|---|
| `(inl g)⁻¹·inr u·inl g = inl(g⁻¹·(φ u)g)·inr u` | `inl_inv_mul_inr_mul_inl` |
| Sylow 交叉 = 点安定化群 (元の形) | `conj_inr_mem_inr_range_iff` |
| `inr(P)` は `Γ` の Sylow | `sylowInrRange` (+ `card_inr_range_eq_pow_factorization`) |
| `O_p(Γ) = 1` | `opCore_semidirectProduct_eq_bot` (+ `inr_range_inf_centralizer_eq_bot`) |
| 点安定化群 / 軌道核 (P で正規) | `fixSubgroup` / `orbitKernel` / `orbitKernel_normal` |
| `inr(P) ⊓ inr(P)^{inl g} = inr(P_g)` | `inr_range_inf_conjInrRange_eq` |
| ⭐ 軌道核は共役 Sylow でも正規 | `conjInrRange_le_normalizer_orbitKernel_map` |
| `Γ` の Sylow はすべて `conjInrRange a` | `exists_eq_conjInrRange` |
| 交叉位数の共役不変性 | `exists_card_inf_eq` |
| **本体** | `exists_faithful_orbit` |

⚠ 実装知見:
- `simp` は `φ (v m₀ v⁻¹)` を `(φ v)∘(φ m₀)∘(φ v).symm` に展開するので、軌道核条件を
  `u = 1` と `u = v⁻¹` で使った 2 式を simp に渡す。
- `γ.left`/`γ.right` のまま `rw` すると自己参照で潰れる → `obtain ⟨a, b⟩ := γ` で先に分解。
- `Ch03` は `Ch04` を import できないので `le_normalizer_of_forall_conj_mem` は局所 private 版。
- 極小性は `Function.argmin` + `Subgroup.eq_of_le_of_card_ge`、
  共役不変性は `Subgroup.smul_inf` + `Subgroup.equivSMul`。


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
| 3A.6 | ✅ **完了** (2026-07-26) `exists_faithful_orbit` (新 leaf `ProblemsFaithfulOrbit.lean`) |
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
**次 frontier = (1) 3A.6 再訪 (1 iteration 時間箱) → (2) Isaacs Ch.4 §4A から文書順**。

⚠ **実測 (2026-07-25)**: `Problem NX.Y` docstring を Ch.4-Ch.10 で grep すると **0 件** —
**Ch.4 以降の章末演習は 1 問も形式化されていない**。Ch.1-Ch.3 (+ Ch.2 全問, §3A/§3B) が
済んだので、campaign の残りは Ch.4 以降が主戦場。

prefix-split 済 (2026-07-25): `Problems3B.lean` (1300 行) → `Problems3BSolvability.lean`
(3B.1-3B.3, 239 行) + `Problems3B.lean` (3B.4-3B.15, 1093 行)。

3B.15 (Berkovich) の証明: 最小指数の `H` は極大。極小正規 `N` について `N ≤ H` なら
`G ⧸ N` へ落として帰納法。`N ≰ H` なら `G = N ⋊ H` で `N` への `H` の共役作用を見る —
`C_N(H) = N` なら `N` が `H` を正規化して `H ⊴ G`、`C_N(H) = 1` なら `v ∈ N \ {1}` の
安定化群 `H_v < H` から `N ⊔ H_v` が真部分群になり、その指数 = 軌道の大きさ `≤ |N| - 1`
`< |N| = [G:H]` で最小性に矛盾 (`MulAction.index_stabilizer` を使用)。

## Ch.4 (Commutators) §4A — 着手 (2026-07-25)

新 leaf `OddOrder/Isaacs/Ch04_Commutators/Problems.lean` (namespace `OddOrder.Isaacs.Ch04`、
`OddOrder.lean` 配線済)。§4A は 11 問 (4A.1-4A.11)。

| # | 状態 | Lean 名 |
|---|---|---|
| 4A.1 | ✅ | `commutator_eq_commutator_of_mul_eq_top` |
| 4A.2 | ✅ | `exists_closure_commutatorTriple_eq_zpowers` (前半) / `exists_card_two_subgroups_commutator_triple_eq_top` (後半 = A₅ 実例 + Note) |
| 4A.3 | ✅ | `IsQuasiquaternion` (定義) / `eq_bot_of_isQuasiquaternion_quotient` |
| 4A.5 | ✅ | (a) `index_centralizer_eq_of_not_mem_center` / (b) `card_closure_pair_eq` / (c) `index_centralizer_closure_pair_eq` / (d) `map_center_centralizer_eq_center` + `isExtraspecial_centralizer_closure_pair` / (e) `exists_index_center_eq_prime_pow_two_mul` (新 leaf `ProblemsExtraspecial.lean`) |
| 4A.6 | ✅ | `IsMaximalClassPGroup` (定義) / `exists_eq_lowerCentralSeries_of_isMaximalClass` (+ 一意性 `eq_of_normal_of_card_eq_of_isMaximalClass`、新 leaf `ProblemsMaximalClass.lean`) |
| 4A.7 | ✅ | `exists_orderOf_eq_and_forall_orderOf_dvd` (+ 冪公式 `pow_mk` / 上界 `pow_prime_pow_succ_eq_one`、新 leaf `ProblemsWreath.lean`) |
| 4A.8(d) | 🔨 進行中 | 位数・下降中心列の翻訳 (`lowerCentralSeries_eq_map_shiftSubSeq`) 完了、残りは linchpin `Δ^{p-1} = T_p` 1 本 — 下記 |
| 4A.8(c) | ✅ 訂正版 | `forall_commute_ker_augHom_iff` + 位数 `card_center_ker_augHom` (`|Z(P'U)| = p`)。書籍の主張は `p=2, n=1` で偽 — 下記 |
| 4A.8(b) | ✅ | `commutator_range_inl_range_inr_eq` (`⁅A,U⁆ = ker(座標積)` の像) + `commutator_eq_commutator_range_inl_range_inr` (4A.1 経由 `P' = ⁅A,U⁆`) + まとめ `commutator_eq_coordProdHom_ker_map` |
| 4A.8(a) | ✅ | `mem_center_iff_exists_const` / `center_eq_inf_centralizer_range_inr` (`ProblemsWreath.lean`) |
| 4A.4 | ✅ | `isElementaryAbelian_quotient_center_of_commutator_eq_center` (+ 同値形 `frattini_eq_center_of_commutator_eq_center` + 橋 `isExtraspecial_of_commutator_eq_center`) |

- **4A.1** (`G = AB`, `A`,`B` abelian ⟹ `G' = ⁅A,B⁆`): `⁅A,B⁆` の正規性は既存の
  `commutator_normal_of_sup_eq_top` (Ch.4 Main の Lem 4.1 系) をそのまま使える。
  商で `A` の像と `B` の像が可換 + 各々 abelian ⟹ 商 abelian ⟹ `G' ≤ ⁅A,B⁆`。
- **4A.4**: repo の `IsExtraspecial` は `frattini_eq_center` を**フィールドとして仮定**して
  いるので、本問 (`P' = Z(P)`, `|Z(P)| = p` ⟹ `P/Z(P)` elementary abelian) は新規内容。
  類 2 の恒等式 `⁅x^n, y⁆ = ⁅x,y⁆^n` を証明して `x^p ∈ Z(P)` を出す。
  **書籍併記の `Z = P' = Φ` 形も完了 (2026-07-25)**: 「repo に `Φ ⊆` 方向が無い」という
  当初の注記は**誤り**で、Lem 4.5 forward `frattini_le_of_isElementaryAbelian_quotient_of_pgroup`
  (Ch04 Main/CommutatorIdentities) がちょうど `P/N` elementary abelian ⟹ `Φ(P) ≤ N` を与える。
  ⟹ `frattini_eq_center_of_commutator_eq_center`、さらに repo の
  `OddOrder.GroupTheory.IsExtraspecial` (Φ = Z を field に持つ) への橋
  `isExtraspecial_of_commutator_eq_center` を追加。以後 4A.5 以降は Isaacs の定義
  (`P' = Z(P)` 位数 `p`) から repo 構造の API をそのまま使える。

- **4A.2** (`⁅H,K,L⁆` は `⁅h,k,l⁆` たちで生成されるとは限らない): 前半 (位数 2 の `H,K,L` なら
  三重交換子の**元**は高々 1 個の非単位元 ⟹ 生成するのは巡回群) は
  `exists_closure_commutatorTriple_eq_zpowers` で `closure {…} = ⟨⁅⁅h,k⁆,m⁆⟩` と**等式**まで出す
  (生成元自身が集合の元なので場合分け不要)。汎用補題
  `commutator_zpowers_eq_zpowers_commutatorElement` (`a² = b² = 1` ⟹ `⁅⟨a⟩,⟨b⟩⁆ = ⟨⁅a,b⁆⟩`) を分離。
  後半の `A₅` 実例は書籍 Hint どおり `P = ⟨(0 1 2 3 4)⟩`, `H = ⟨(1 4)(2 3)⟩`, `K = ⟨(0 2)(3 4)⟩`
  (どちらも `N_{A₅}(P) ≅ D₁₀` の折り返し ⟹ `⁅H,K⁆ = P`)、`L = ⟨(0 1)(2 3)⟩` (`P` を正規化しない)。
  **`⁅P,L⁆ = ⊤` は「`⟨P,L⟩ = A₅` + 単純性」でなく位数で出した**: `⁅rot5,l⁆` (位数 5)、
  `⁅rot5²,l⁆` (位数 3)、その積 (位数 2) が `⁅P,L⁆` に居る ⟹ `30 ∣ |N| ∣ 60` ⟹ `|N| ∈ {30,60}`、
  `30` なら指数 2 = `(60).minFac` で `N ⊴ A₅` となり単純性に反する ⟹ `|N| = 60`。
  具体置換の計算は `Equiv.Perm (Fin 5)` 上の `decide` (冪は `maxRecDepth 8000` が要る)、
  `↥(alternatingGroup (Fin 5))` へは `Subtype.ext` + `change` で降ろす。
  Note (「`⁅H,K,L⁆` は `⁅h,k,l⁆` で生成されない」) は前半の巡回性 +
  `alternatingGroup.isCyclic_iff_card_le_three` で主定理の最後の連言肢に含めた。

- **4A.3** (quasiquaternion 群の Schur 乗数は自明): `Q = CU` (`C,U` 巡回、`C ⊴ Q`、
  `C ∩ U = Z(Q)`) を `IsQuasiquaternion` として定義し、`Z ≤ G' ⊓ Z(G)` かつ `G ⧸ Z` が
  quasiquaternion なら `Z = ⊥` を証明。書籍 Hint どおり `C, U` の引き戻し `A, B` を取り、
  (i) `A = Z⟨a₀⟩` ゆえ `A` abelian (`Z ≤ Z(G)` を使う)、(ii) `G = AB`、
  (iii) `A ⊓ B = Z(G)`、(iv) `G ⧸ A` 巡回 ⟹ **Lem 4.6 cardinality**
  (`card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient`) を
  `G` と `Ḡ = G ⧸ Z` の両方に適用。引き戻しの位数が `|Z|` 倍になること
  (`card_comap_mk'_eq_mul`、`index_comap_of_surjective` + Lagrange) と `Ḡ' = G'/Z`
  (`map_commutator_eq` + `comap_map_eq` + `Z ≤ G'`) から `|C||Z| = |C||Z|²` ⟹ `|Z| = 1`。
  ⚠ counting なので `[Finite G]` を仮定 (書籍も有限群の文脈)。

- **4A.5** (extraspecial の構造 (a)-(e)、新 leaf `Ch04_Commutators/ProblemsExtraspecial.lean`):
  中心道具は**類 2 の左交換子準同型** `commutatorLeftHom` (`g ↦ ⁅x,g⁆`、核 = `C_P(x)`) と
  そこから出る恒等式 3 本 (`⁅a,bc⁆ = ⁅a,b⁆⁅a,c⁆` / `⁅a,b⁻¹⁆` / `⁅a,b^n⁆`)。
  (a) は核・像の Lagrange (`index_ker` + 像が位数 `p` の `Z(P)` の非自明部分群)。
  (b) は `P/Z(P)` が elementary abelian (4A.4) で `⟨x̄⟩ ⊓ ⟨ȳ⟩ = 1` を示し
  `|U| = |U の像| · |Z| = p²·p`。
  **(c)(d)(e) の要は中心積分解 `P = V·U`** (`exists_mem_centralizer_mul_mem_closure_pair`):
  `⁅x,g⁆ = c^i` から `g(y^i)⁻¹ ∈ C_P(x)`、さらに `⁅y,·⁆` を潰して `V` に落とす。
  これで (d) の `Z(V) = Z(P)` は**位数勘定なしで**出る (書籍の `P > U` すら不要 —
  `P > U` は `V` の非可換性、すなわち extraspecial 性の側でだけ要る)。
  (c) は `|VU|·|V ⊓ U| = |V||U|` に `VU = P`, `V ⊓ U = Z(P)`, `|U| = p³` を代入。
  (e) は `|Q|` の強帰納法 (書籍 Hint)、基底は `Q = U` (`|Q| = p³`)、段は `V` extraspecial +
  `[Q:V] = p²` + `Z(V) = Z(Q)`。

- **4A.6** (maximal class、新 leaf `Ch04_Commutators/ProblemsMaximalClass.lean`):
  ⚠ **mathlib の下降中心列は古典的 `γ_k` から 1 ずれる** (`lowerCentralSeries ⊤ 0 = P`) —
  古典 `γ_k` = `lowerCentralSeries ⊤ (k-1)`。汎用部品を 4 つ整備:
  (i) `p`-群で真の部分群は位数が `p` 倍以上違う (`prime_mul_card_dvd_card_of_lt`)、
  (ii) 下降中心列は類の下で真減少 (`lowerCentralSeries_lt_of_lt_nilpotencyClass`)、
  (iii) 下方 `p^j ∣ |L_{c-j}|` / 上方 `p^i·|L_i| ∣ |P|`、
  (iv) **非可換 `p`-群では `p² ∣ |P:P'|`** (`P/P'` 巡回 ⟹ `P/Φ(P)` 巡回 ⟹ Ch01 の
  `isCyclic_of_frattiniQuotient_isCyclic` で `P` 巡回 ⟹ 可換)。
  (iii)+(iv) から **`|G| = p^k` (`k ≥ 2`) の `p`-群の類 ≤ `k-1`**
  (`nilpotencyClass_le_of_card_eq_prime_pow`; BG S04 の同型 lemma とは独立に Isaacs 層で証明 —
  BG を import すると層が逆流するため) と maximal class での `|L_i| = p^{n-1-i}` が出る。
  本題は `|P⧸N| = p^k` の類 ≤ `k-1` ⟹ `L_{k-1}(P) ≤ N`、位数一致で `N = L_{k-1}(P)`。
  ⚠ 書籍の `|N : P| ≥ p²` は誤植で `|P : N| ≥ p²` (指数が `p` 冪なので `p² ∣ |P:N|` と同値)。

- **4A.7** (正則 wreath product `C ≀ U` の元の位数の最大値 = `p^{n+1}`、新 leaf
  `Ch04_Commutators/ProblemsWreath.lean`): §3A の一般 wreath product `D ≀[Q] Q`
  (`Q` の左正則作用) で実現。**上界は冪公式を使わない**のがポイント —
  `rightHom (x^p) = (rightHom x)^p = 1` ⟹ `x^p ∈ range inl` (base 群)、base は指数 `p^n`
  ⟹ `x^{p^{n+1}} = 1` (`pow_prime_pow_succ_eq_one`)。
  下界には冪公式 `pow_mk` (`⟨f,q⟩^k` の base 成分 = `∏_{j<k} f((q^j)⁻¹ ω)`、`D` 可換で証明) と
  `prod_range_card_eq_prod_univ` (生成元の冪で捻った積 = 群全体の積; `Finset.prod_image` +
  `pow_injOn_Iio_orderOf`) を使い、証人 `x = ⟨δ₁ c, q⟩` に対し `x^p = ⟨const c, 1⟩` (位数 `p^n`)。

- **4A.8(a)** (`Z(P) = C_A(U)` = 定数 tuple 全体): §3A の既存部品がほぼそのまま効く —
  `centralizer_range_inl_eq` (`C_W(base) = base`) で中心の元が base に入り、
  `forall_conj_inr_eq_iff_const` (`inr` との可換性 ⟺ 軌道上定数) で定数性が出る。
  逆向きは定数 tuple が base とも `inr q` とも可換という直接計算。

### 4A.8(b) 完了 (2026-07-25) — 実装知見

`⁅A,U⁆ = P'` = 「成分の積が `1`」の tuple 全体。実装で効いた点:

1. `coordProdHom : (Q → D) →* D`, `f ↦ ∏ ω, f ω` (`D` 可換ゆえ準同型)。
2. `prod_smul_eq`: `∏ ω, f (q⁻¹ ω) = ∏ ω, f ω` (`Fintype.prod_equiv (Equiv.mulLeft q⁻¹)`)。
3. **交換子公式** `⁅inl f, inr q⁆ = inl (fun ω => f ω * (f (q⁻¹ ω))⁻¹)`。
   ⚠ **pointwise (`fun ω => …`) で書くこと** — Pi の `f * g⁻¹` 形で書くと
   `HMul (Q → D) D` の instance 解決に失敗する (撤退の原因)。証明は `ext ω` +
   構造 simp 補題 (`mul_left`/`inv_left`/`one_left` …) で、`change` は右成分で通らない。
4. `⊆`: 上の公式の座標積 = `(∏f)(∏f)⁻¹ = 1` (2 を使う)。
5. `⊇`: `⁅inl (δ_x d), inr (y x⁻¹)⁆ = inl (δ_x d · (δ_y d)⁻¹)` (shift が `δ_x ↦ δ_{qx}`) と
   δ-分解 `f = ∏_x (δ_x (f x) · (δ_1 (f x))⁻¹)` (`Finset.univ_prod_mulSingle` +
   `Finset.prod_apply` で `∏_x (δ_1 (f x))⁻¹ = 1` を `∏ f = 1` から出す)。
6. `P' = ⁅A,U⁆` 自体は **4A.1** (`commutator_eq_commutator_of_mul_eq_top`) —
   `P = A·U` は §3A の既存 simp 補題 `inl_left_mul_inr_right`、`A`/`U` の
   `IsMulCommutative` instance はその場で構成 (`U` 側は `Q` 可換の仮定が要る)。
7. ⚠ **最後の積は base 群 (可換) の中で取る**: `map_prod` は codomain に `CommMonoid` を
   要求するので wreath product では使えない。`Subgroup.comap inl ⁅A,U⁆` の中で
   `Subgroup.prod_mem` を使う。
8. ⚠ `Subgroup.map` の存在形が与える membership は `x ∈ ↑K` (Set 強制) なので
   `rw [MonoidHom.mem_ker]` は当たらない — `change` で `∏ ω, … = 1` に落とす。

### ⚠ 4A.8(c) は `p = 2, n = 1` で偽の疑い (2026-07-25、要 PDF 再確認)

書籍 (p. 124): 「(c) Show `|Z(P'U)| = p`.」 だが **`p = 2, n = 1` は反例に見える**:

- `C = C₂`, `A = C₂ × C₂`, `U = C₂` (成分交換) ⟹ `P = C₂ ≀ C₂ = D₈` (位数 8)
- `P' = ⁅A,U⁆ = {(a,b) : ab = 1} = {(1,1), (d,d)} = Z(P)` (位数 2、`D₈` は extraspecial)
- `P'` は中心なので `P'U = Z(P) × ⟨u⟩ ≅ C₂ × C₂` は **abelian**、ゆえに `|Z(P'U)| = 4 ≠ 2`

`p = 2, n = 2` (`C = C₄`) では `P' = {(a,a⁻¹)} ≅ C₄` で `u` 共役が `(a,a⁻¹) ↦ (a⁻¹,a)` ゆえ
`P'U` は非可換、`Z(P'U) = {(a,a⁻¹) : a² = 1}` は位数 2 = `p` ✅。奇素数でも同様。
⟹ **正しい主張は「`p` が奇 または `n ≥ 2`」の条件付き**と思われる。3B.12 と同型の書籍の穴。
次 iteration で PDF ページ画像を再確認し、条件付きの形で形式化する。

### 4A.8(c) の Lean 実装知見 (2026-07-25、3 回目で完成)

**解決策 = `Pi.mulSingle` を使わず `if ω = x then d else 1` を直接書く**。指示関数は自前で
定義してしまえば型推論の問題は起きず、`Finset.prod_eq_single x` + `simp +contextual` で
`∏ ω, (if ω = x then c else 1) = c` も通る。以下は 2 回目の着手で判明した詰まり:

- ⚠ `Pi.mulSingle_eq_of_ne h d` / `Pi.mulSingle_eq_same x d` のように**値を位置引数で渡すと
  依存族 `f` がメタ変数のまま残り** application type mismatch になる (非依存族
  `fun _ : Q => D` でも同じ)。`(f := …)` という名前付き指定も**不可** (implicit 名が `f` でない)。
  ⟹ **`simp [Pi.mulSingle_apply, hb]` で潰す**のが確実 (`Pi.mulSingle_apply` が `if` 形に開く)。
- ⚠ 証明中の `classical` と、補助補題の statement にある `[DecidableEq Q]` は**別 instance**に
  なり mismatch する。補助は `classical` の後に `have` でインライン定義する。
- `∏ ω, Pi.mulSingle x d ω = d` は `Finset.prod_eq_single x` + 上記 simp で通る (確認済)。

### 4A.8(d) の分析 (2026-07-25、次 iteration の出発点)

書籍: 「`n = 1` なら `P` は maximal class、一般に `P'U` は maximal class」。

**位数は本 commit で確定** (`card_ker_augHom_eq` / §3A `WreathProduct.card`):
`|P| = |C|^{|Q|}·|Q| = p^{np+1}`、`|P'U| = p^{n(p-1)+1}` (`augHom` が全射ゆえ
`|ker| = |P|/|C|`)。⟹ maximal class の主張は
「`class(P) = np`」(`n = 1` のとき `= p`) と「`class(P'U) = n(p-1)`」。

**第一歩は本 commit で設置**: `shiftSubHom q : (Q → D) →* (Q → D)`,
`Δ_q f = f · (f ∘ shift_q)⁻¹` (= 群環の `(1-q)·` 作用) と
`commutatorElement_inl_inr_eq_shiftSubHom` (`⁅inl f, inr q⁆ = inl (Δ_q f)`)、
`range_shiftSubHom_le_ker_coordProdHom` (`(1-q)R ⊆ I`)。
次は **`γ_{i+1}(P) = (Δ_q)^i(A) の像`** を帰納で立てる。
⚠ `⁅H, K ⊔ L⁆` の分配は**偽**なので (memory: lean-subgroup-commutator-api-traps)、
`⁅L_i, ⊤⁆` を `⁅·, A⁆` と `⁅·, U⁆` に割るには good-elements 法が要る。

#### 4A.8(d) の完全な設計 (2026-07-25 に手計算で確定、数値検証済み)

**(i) 下降中心列の帰納形**: `S ≤ (Q → D)` が shift 安定なら
`⁅S.map inl, ⊤⁆ = (S.map (shiftSubHom q)).map inl`。理由:
`⁅inl f, inl g * inr q'⁆ = inl (Δ_{q'} f)` (base 可換で `⁅inl f, inl g⁆ = 1`、
`⁅a, bc⁆ = ⁅a,b⁆ · b⁅a,c⁆b⁻¹` の第 2 項の共役も base 可換で消える)。
`Q = ⟨q⟩` が位数 `p` なら `Δ_{q^k} f = Δ_q (∏_{j<k} f∘shift^j)` (群環の
`1 - x^k = (1-x)(1 + x + … + x^{k-1})`) なので、生成元 `q` の分だけで足りる。
⟹ **`lowerCentralSeries ⊤ i = (Δ^i(⊤)).map inl`** (`i ≥ 1`; 基底は 4A.8(b) の
`P' = ker(coordProd).map inl` と `range Δ_q = ker coordProd`)。
**元レベルの式 `⁅inl f, y⁆ = inl (Δ_{y.right} f)` は
`commutatorElement_inl_eq_shiftSubHom` として設置済**。さらに
**`Δ_{q^k} = Δ_q ∘ T_k`** (`shiftSubHom_pow_eq_comp`、`T_k = shiftSumHom q k` は
群環の `1 + x + ⋯ + x^{k-1}`; 証明は `Finset.prod_range_div` の telescoping) も設置済で、
これにより「生成元 `q` の `Δ` だけで `⁅A, U⁆` の全生成元が捉えられる」。
**帰納段も設置済**: `commutator_map_inl_top_eq`
(`S` が shift 安定 = `S.map (shiftHom q) ≤ S` なら
`⁅S.map inl, ⊤⁆ = (S.map (shiftSubHom q)).map inl`)。
補助は `shiftHom` (平行移動)・`shift_pow_mem_of_shift_stable`・
`shiftSumHom_mem_of_shift_stable`。
**(α) も完了**: `lowerCentralSeries_eq_map_shiftSubSeq`
(`lowerCentralSeries ⊤ (i+1) = (shiftSubSeq q (i+1)).map inl`、
`shiftSubSeq q i = Δ^i(⊤)`)。基底は 4A.8(b)、shift 安定性の保存は
`shiftSubHom_comp_shiftHom` (`Δ` と `shift` の可換性) + `Subgroup.map_map`。
**(β) の第一歩も設置**: `shiftSumHom_card_eq_const` (`T_{|Q|} f` は定数 = ノルム) と
`shiftSubHom_shiftSumHom_card` (**`Δ_q ∘ T_{|Q|} = 1`**, 群環の `(1-x)·N = 0`)。
⟹ **残るのは (β) `(1-x)` の冪零指数 `n(p-1)+1` の算術だけ**:
`shiftSubSeq q i = ⊥ ⟺ i ≥ n(p-1)+1` を示せば `class(P) = n(p-1)+1` が出る
(`lowerCentralSeries_eq_bot_iff_nilpotencyClass_le` 経由)。`P'U` 側も同様に
`Δ` の反復を `ker coordProd` から始めればよい。

#### (β) の linchpin = **`Δ^{p-1} = T_p` (作用素として)**

`D` が指数 `p` のとき、群環 `F_p[x]/(x^p-1)` の恒等式 `(1-x)^{p-1} = 1 + x + ⋯ + x^{p-1} = N`
が成り立つ。これさえ Lean で言えれば
`Δ^p = Δ ∘ Δ^{p-1} = Δ ∘ T_p = 1` (**既証の `shiftSubHom_shiftSumHom_card`**) で上界が出て、
下界も `Δ^{p-1}(δ₁ c) = T_p(δ₁ c) = const c ≠ 1` (`shiftSumHom_card_eq_const`) で即出る。
⟹ **`class(P) = p` (n=1 で maximal class) は linchpin 1 本に還元済み**。

**mathlib の部品は調査済み (2026-07-25)**:
- `sub_pow_char_of_commute (h : Commute x y) : (x - y)^p = x^p - y^p`
  (`Mathlib/Algebra/CharP/Lemmas.lean` L223) — **可換とは限らない環でも可換な元同士なら使える**
  ので、**自己準同型環 `AddMonoid.End V` の中で `1` と `σ` に直接適用できる**。
  ただし `[ExpChar R p]` インスタンスが要る。
- インスタンスを避けるなら `Commute.add_pow` (二項定理) + `Nat.Prime.dvd_choose_self`
  (`0 < k < p` で `p ∣ C(p,k)`) + 「`V` の指数が `p` ⟹ `End V` で `p • x = 0`」で
  `(1-σ)^p = 1 + (-σ)^p = 1 + (-1)^p·1 = 0` (`p` 奇なら `1 - 1`、`p = 2` なら `1 + 1 = 2 = 0`)。
- `(p-1).choose j ≡ (-1)^j [ZMOD p]` は mathlib に無いが **自前で証明済**
  (`cast_choose_prime_sub_one`; Pascal + `Nat.Prime.dvd_choose_self` の帰納、13 行)。
  ⚠ `Nat.Prime` は `Irreducible` の別名なので **dot 記法 `hr.dvd_choose_self` は
  `Irreducible.dvd_choose_self` に解決されて失敗する** — 完全名で書くこと。

⚠ なお `Δ^p = 0` だけでは `class(P) ≤ p` (上界) しか出ない。maximal class には
`Δ^{p-1} ≠ 0` (下界) が要り、そこは linchpin `Δ^{p-1} = T_p` が最短。

**多項式側は landing 済 (2026-07-25)**: `one_sub_X_pow_prime_sub_one`
(`(1 - X)^{p-1} = ∑_{j<p} X^j` in `(ZMod p)[X]`; `sub_pow_char` + `mul_neg_geom_sum` +
整域での約分)。⟹ 残るのは**作用素への移送**だけ:
`V = Additive (Q → D)` (指数 `p` ⟹ `ZMod p`-加群) 上で `Polynomial.aeval σ` を使い、
`aeval σ (1 - X) = Δ`, `aeval σ (∑_{j<p} X^j) = T_p` を確認すれば `Δ^{p-1} = T_p` が出る。
必要 import は `Mathlib.Algebra.{Field.ZMod, Polynomial.Coeff, Polynomial.Div, Ring.GeomSum}`
(本 commit で追加済)。

**位数側も `n=1` 特殊形を landing**: `card_wreath_of_card_eq_prime`
(`|C| = |Q| = p` ⟹ `|C ≀ Q| = p^{p+1}`) — maximal class の判定 `class = p` と対になる。

**二項展開 `shiftSubHom_iterate_apply` は landing 済 (2026-07-25)**:
`Δ^k f ω = ∏_{j ≤ k} f((q^j)⁻¹ω)^{(-1)^j C(k,j)}`。実装知見:
- `Function.iterate_succ_apply'` で `Δ^[k+1] = Δ ∘ Δ^[k]` に開く
- 添字ずらし `(q^j)⁻¹(q⁻¹ω) = (q^{j+1})⁻¹ω` は `group`
- ⚠ **`rw [Finset.prod_congr …]` / `rw [Finset.prod_range_succ]` は積が 2 つあると
  どちらに当たるか不定** — 対象を `have` で等式化するか `conv_rhs` で明示する
- Pascal は `Nat.choose_succ_succ' k i` + `push_cast` + `ring`

**🎉 linchpin 完成 (2026-07-25)**: `shiftSubHom_iterate_prime_sub_one`
(`Δ_q^{p-1} f = T_p f`、指数 `p` の可換 base `D` に対する作用素等式)。仕上げは
ルート A (pointwise 二項展開) で、部品 2 本:
- `zpow_eq_self_of_pow_eq_one` (`d^r = 1` ∧ `(m : ZMod r) = 1` ⟹ `d ^ m = d`。
  `ZMod.intCast_zmod_eq_zero_iff_dvd` で `m = 1 + r·c` に分解し `zpow_add`/`zpow_mul`)
- `cast_neg_one_pow_mul_choose_prime_sub_one` (`(-1)^j·C(r-1,j) ≡ 1 (mod r)`
  = `cast_choose_prime_sub_one` の系、`(-1)^j·(-1)^j = 1`)

**⟹ 4A.8(d) の `P` 側 (`n = 1`) 完了**:
- `shiftSubHom_iterate_prime_eq_one` (上界 `Δ^p = Δ ∘ T_p = 1`)
- `mem_shiftSubSeq_iff` (`g ∈ Δ^i(⊤) ⟺ ∃ f, Δ^[i] f = g`) →
  `shiftSubSeq_prime_eq_bot` / `shiftSubSeq_prime_sub_one_ne_bot`
  (下界の witness = 指示関数 `δ₁ c`、`Δ^{p-1}(δ₁ c) = T_p(δ₁ c) = const c ≠ 1`)
- `nilpotencyClass_wreath_eq_of_exponent_prime` (**`class(D ≀ Q) = p`**、
  `lowerCentralSeries_eq_map_shiftSubSeq` + `lowerCentralSeries_eq_bot_iff_nilpotencyClass_le`;
  `IsNilpotent` 自体も `Subgroup.nilpotent_iff_lowerCentralSeries` で上界から得る)
- **`isMaximalClassPGroup_wreath`** (`|C| = |Q| = p` ⟹ `C ≀ Q` は maximal class;
  `|P| = p^{p+1}` = `card_wreath_of_card_eq_prime`、`class + 1 = p + 1`)。axiom-clean。

⚠ 教訓: `orderOf_eq_card_of_forall_mem_zpowers` の結論は `Nat.card` (`Fintype.card` でない) /
`Subgroup.map_eq_bot_iff_of_injective` は `H` が**明示引数** (`_ inl_injective`) /
`⟨(k:ℤ), _⟩ : q^k ∈ zpowers q` の証明義務は β-未簡約 (`rw [zpow_natCast]` 不可、`simp`)。

linchpin の証明ルート 2 つ:
1. **pointwise 二項展開**: `Δ^k f ω = ∏_{j≤k} f((q^j)⁻¹ω)^{(-1)^j C(k,j)}` を `k` の帰納
   (Pascal) で示し、`k = p-1` で `C(p-1,j) ≡ (-1)^j (mod p)` を使うと指数が全部 `1` になる。
   要調査: mathlib に `(p-1).choose j ≡ (-1)^j [ZMOD p]` があるか。
2. **多項式環経由**: `F_p[x]` は整域なので `(1-x)^p = 1 - x^p = N·(1-x)` から `(1-x)` を約して
   `(1-x)^{p-1} = N`。`V ≅ F_p[x]/(x^p-1)` (n=1 なので `D ≅ F_p`) の同型を作る手間がかかる。

**(β) の当面の目標は `n = 1` の場合** (書籍の「`n = 1` なら `P` は maximal class」):
`D` が指数 `p` なら `V = Q → D` は `ZMod p`-加群で `Δ = 1 - σ` (`σ` = 平行移動, `σ^p = 1`)、
標数 `p` の可換環 `ZMod p[σ]` で **freshman's dream** `(1-σ)^p = 1 - σ^p = 0`
(mathlib `add_pow_char`) ⟹ `class(P) ≤ p`。下界は `Δ^{p-1}(δ₁ c) = const c ≠ 1`
(ノルム関係式の相棒: `(1-x)^{p-1} = N` mod `p`) ⟹ `class(P) = p = np` で maximal class。
一般 `n` の sharp 値 `n(p-1)+1` は `(1-x)^p = p·(1-x)s` の filtration が要る。

**(ii) 残る算術 = `Δ = (1-x)` の冪零指数**。`ZMod(p^n)[x]/(x^p-1)` で
`(1-x)^{n(p-1)+1} = 0` かつ `(1-x)^{n(p-1)} ≠ 0` ⟹ **`class(P) = n(p-1)+1`**。
- `p=2, n=1`: `(1-x)² = 0` ⟹ class 2。`|P| = 8` (`D₈`) で maximal class ✓
- `p=3, n=1`: class 3、`|P| = 3⁴` で maximal class ✓
- `p=2, n=2`: `(1-x)² = 2(1-x)`, `(1-x)³ = 0` ⟹ class 3。`|P| = 2⁵` なので
  maximal class には class 4 が要る ⟹ **`P` は maximal class でない** ✓
  (書籍が `n = 1` に限定しているのと整合)
- 一般に `class(P) = n(p-1)+1` と maximal class の要求 `np` が一致するのは **`n = 1` のときだけ** ✓

**(iii) `P'U` 側**: `class(P'U) = n(p-1)`、`|P'U| = p^{n(p-1)+1}` なので**常に maximal class** ✓
(`p=2,n=2` で検算: `P' = (1-x)R ≅ C₄`, `Δ(P') = (1-x)²R ≅ C₂`, `(1-x)³R = 0`
⟹ class 2、`|P'U| = 8` ⟹ maximal class ✓)。

**残りの下降中心列の計算**は群環のフィルトレーションに落ちる:
`A = C^Q` を `ZMod(p^n)[Q] = ZMod(p^n)[x]/(x^p - 1)` (`x = u`) と見ると
`⁅A, U⁆` は `(x-1)A`、以降 `γ_{i+1}(P) = (x-1)^i A` (`i ≥ 1`)。
`(x-1)^p ≡ x^p - 1 = 0 (mod p)` なので `(x-1)` 冪の減少列が `p`-進的に落ちる速さが
class を決める。⟹ **群環の `(x-1)`-filtration を Lean で立てるのが本体** (規模大)。
`ProblemsMaximalClass.lean` の下降中心列部品 (真減少・`p` 冪の上下界) は再利用できる。

⚠ 4A.8(c) と違い `p = 2, n = 1` でも成立する (`D₈` は位数 8・class 2 = 3-1 で maximal class、
`P'U ≅ C₂×C₂` は位数 4・class 1 = 2-1 でやはり maximal class)。

### 4A.8(c) 完了 (位数まで)

`card_center_ker_augHom : |Z(P'U)| = p` (仮説 `hd` の下)。部品は
`card_ker_powMonoidHom_prime` (位数 `p^n` の巡回群で `x^p = 1` の解は `p` 個 —
像 `⟨c^p⟩` の位数が `p^{n-1}` であることと Lagrange) と `d ↦ inl (const d)` の全単射。

### 🎉 4A.8(d) 完了 (2026-07-25、一般 `n`) — 新 leaf `ProblemsWreathClass.lean`

**主結果** (すべて実証明・axiom-clean):
- `nilpotencyClass_wreath_eq`: **`class(C ≀ Q) = n(p-1)+1`** (`C` の指数がちょうど `p^n`)
- `isMaximalClassPGroup_wreath_iff`: **`P` が maximal class ⟺ `n = 1`**
  (`|P| = p^{np+1}` ゆえ maximal class は `class = np` を要求、一致は `n=1` のみ)
- `nilpotencyClass_ker_augHom_eq`: **`class(P'U) = n(p-1)`**
- `isMaximalClassPGroup_ker_augHom`: **`P'U` は常に maximal class** (`|P'U| = p^{n(p-1)+1}`)

**手法 = 群環 `ℤ/p^n[x]/(x^p-1)` の `(1-x)`-filtration を「作用素の言葉だけ」で実行**
(加群も多項式環も構成しない — ここが実装上の要):
- **基底** `exists_witness_shiftSubHom_iterate_prime_sub_one`:
  `Δ^{p-1} f = T_p f · g^p` **かつ** `T_p g = (T_p f)⁻¹`。前者は二項展開の係数を
  `(-1)^j C(p-1,j) = 1 + p·e_j` と分解 (`e_j = ((-1)^j C(p-1,j) - 1)/p`、割り切れは
  `cast_choose_prime_sub_one`)、後者は `∑_j e_j = -1` (交代和
  `Int.alternating_sum_range_choose_of_ne` = `0`) で、群環の `y^{p-1} = N + p·s` と
  `N·s = s(1)·N = -N` (`s(1) = -1`) にちょうど対応。**`D` の指数に仮定は要らない**。
- **帰納** `exists_shiftSubHom_iterate_mul_prime_sub_one`:
  `Δ^{(m+1)(p-1)} f = (T_p f)^{(-1)^m p^m} · g^{p^{m+1}}` かつ
  `T_p g = (T_p f)^{(-1)^{m+1}}`。段では `Δ^{p-1}(T_p f) = 1` (定数を消す = `y·N = 0`) で
  第 1 因子が落ち、`(T_p h)^{p^m}` が新しい第 1 因子になる。
- 指数 `p^n` なら第 2 因子が消えて **`Δ^{n(p-1)} f = (T_p f)^{(-1)^{n-1}p^{n-1}}`**。
  上界は `Δ ∘ T_p = 1`、下界は `f = δ₁ c` で `T_p f = const c` と `c^{p^{n-1}} ≠ 1`。
- **`P'U` 側**: `commutator_map_inl_eq` を「`inr q ∈ K` なる任意の `K`」へ一般化 (`⊤` 版は
  その特殊化) し、基底 `commutator_ker_augHom_self` (`⁅P'U,P'U⁆ = Δ²(A) の像`) を
  `x = inl x.left · inr x.right` 分解 + `⁅inr a, inr b⁆ = 1` (Q 可換) + 正規性による共役吸収で
  出す。以降 `lowerCentralSeries_ker_augHom_eq` は同じ帰納。部分群の類は
  `nilpotencyClass_le_iff_lowerCentralSeries_eq_bot` (`top_subtype_lowerCentralSeries` 経由) で
  環境群の下降中心列に翻訳。

⚠ **一般版が n=1 版を包含**するので、`ProblemsWreath.lean` 側の n=1 専用系
(`shiftSubHom_iterate_prime_eq_one` / `shiftSubSeq_prime_eq_bot` /
`shiftSubSeq_prime_sub_one_ne_bot` / `nilpotencyClass_wreath_eq_of_exponent_prime` /
`isMaximalClassPGroup_wreath`) は削除した (同事実 2 本立ては証明分裂の元)。
linchpin `shiftSubHom_iterate_prime_sub_one` (`Δ^{p-1} = T_p` の**等式**、標数 `p` 限定) と
多項式版 `one_sub_X_pow_prime_sub_one` は書籍の論法そのものなので残す。

⚠ 教訓: `Subgroup.isNilpotent_iff_lowerCentralSeries` は `S` が**明示引数** (`(… _).mpr`) /
`Div Int` = `Int.ediv` ゆえ `Int.mul_ediv_cancel'` が使える / `conv_lhs` は `∈` の左辺 =
**部分群側**を拾う (元側を書換えたいなら `have` で等式化) / `prod_smul_eq` は
`∏ ω, f (q⁻¹ * ω)` の形にしか rw できない (`f y ^ e j` を噛ませたら `exact` で defeq 渡し)。

#### 🎉 4A.10 完了 (2026-07-25) — 新 leaf `ProblemsCenterIndex.lean`

**主結果** (実証明・axiom-clean): `card_commutator_le_of_index_center_le`
= 書籍そのままの **`p`-群 `P` で `|P : Z(P)| ≤ p^n` ⟹ `|P'| ≤ p^{n(n-1)/2}`**。

- 中核 `card_commutator_le_of_normal_cyclic_quotient`:
  **`Q ⊴ G`, `G/Q` cyclic, `Z(G) ≤ Q` ⟹ `|G'| ≤ |⁅Q,Q⁆| · |Q : Z(G)|`**。
  `Ḡ = G/⁅Q,Q⁆` で `Ā = Q/⁅Q,Q⁆` は可換正規 (`⁅q₁,q₂⁆ ∈ ⁅Q,Q⁆`)、`Ḡ/Ā ≅ G/Q`
  (`QuotientGroup.quotientQuotientEquivQuotient`) が cyclic なので **repo の Lemma 4.6 位数形**
  `card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient` が
  `|Ḡ'|·|Ā ⊓ Z(Ḡ)| = |Ā|` を与える。`Z(G)` の像 ⊆ `Ā ⊓ Z(Ḡ)` と像・核の位数関係で
  `|G'|·|Z(G) の像| ≤ |Z(G) の像|·|⁅Q,Q⁆|·|Q:Z(G)|`、約せば結論。
- 支持補題 `card_map_mul_card_inf_ker` (`|f(H)|·|H ⊓ ker f| = |H|`; `MonoidHom.restrict` +
  `Subgroup.index_ker`)。
- 帰納 `card_commutator_le_pow_choose_two` は **`n.choose 2` で述べる**のが要点
  (Pascal `(n+1).choose 2 = n.choose 2 + n` がそのまま指数の勘定)。書籍形への変換は
  `Nat.choose_two_right`。`Z(P)` を含む極大部分群は `IsCoatomic.eq_top_or_exists_le_coatom`
  + `NormalizerCondition.normal_of_coatom` (冪零) + 1D.6 `isCoatom_iff_index_prime`。

⚠ 教訓: `commutator_eq_bot_iff_center_eq_top` / `NormalizerCondition.normal_of_coatom` /
`Subgroup.isNilpotent_iff_lowerCentralSeries` はいずれも **section 変数が明示引数**ゆえ
`X.mpr` 形が「Unknown constant X.mpr」になる (`(X _).mpr` と書く) /
`by` ブロックを入れ子にした改行継続は parse error になりやすい (`have` に切り出す)。

#### 🎉 4A.12 (a)(b)(c 一般部分) 完了 (2026-07-25) — 新 leaf `ProblemsWreathNonCommutator.lean`

**主結果** (実証明・axiom-clean):
- `IsAbelianTwoGen T` (可換かつ 2 元生成)、`𝒯(H)` = その性質の極大元 (`Maximal IsAbelianTwoGen`)
- `commutatorElement_eq_of_right_commute` : `x.right`, `y.right` 可換なら
  **`⁅x,y⁆ = inl(Δ_{x.right} y.left)⁻¹ · inl(Δ_{y.right} x.left)`**
- `exists_maximal_commutator_mem` = **(a)** (`⁅x,y⁆ ∈ B` ⟹ ある極大 `T` で `⁅x,y⁆ ∈ ⁅B,T⁆`)
- `exists_mem_not_isCommutator` = **(b)** (`∑_T |A|^{|H|−|H:T|} < |A|^{|H|−1}` ⟹
  `⁅B,U⁆` は交換子でない元を含む; 書籍の `1/|A| > ∑(1/|A|)^{|H:T|}` に `|A|^{|H|}` を掛けた形)
- `sum_lt_of_card_lt` = **(c) 一般部分** (`H` が可換 2 元生成でなければ `|A| > |𝒯(H)|` で成立)

(a) の鍵は `⁅x,y⁆ ∈ B ⟺ x.right, y.right` が可換で、そのとき交換子が base 側の 2 つの `Δ` に
分解すること (`⁅inr h, inr k⁆ = inr ⁅h,k⁆ = 1` が効く)。可換 2 元生成部分群を含む極大元は
`Finite.exists_le_maximal`、`⟨u,v⟩` の可換性は中心化群の二段論法。
(b) は (a) + 4A.11 の位数 + `Finset.card_biUnion_le` の鳩の巣。

⬜ **残: (c) の `H = D₈` で `m = 3` が取れる部分** (= `|𝒯(D₈)| ≤ 3`)。`D₈` の部分群を
具体的に列挙する計算なので別途。

⬜ **4A.13 も未着手** (pdftotext が切れていて見落としていた; PDF p.138 で確認):
`G` 冪零で class `m > 1`, `a ∈ G` ⟹ `H = G'⟨a⟩` の冪零類は `m` 未満。

#### 🎉 4A.13 完了 (2026-07-25) — 新 leaf `ProblemsNilpotencyClass.lean`

`nilpotencyClass_commutator_sup_zpowers_lt` : **`G` 冪零・class `m > 1` ⟹
`class(G'⟨a⟩) < m`** (実証明・axiom-clean、有限性の仮定は不要)。

- `commutatorMemLeft N y` = `{x | ⁅x,y⁆ ∈ N}` (`N ⊴ G` で部分群)
- `commutator_self_le_lowerCentralSeries_two` = 基底 `⁅H,H⁆ ≤ γ₃(G)`
  (good-elements 二段: `⁅a, H⁆ ≤ γ₃` を先に出し、それを使って `H ≤ commutatorMemLeft γ₃ y`)
- `lowerCentralSeries_commutator_sup_zpowers_le` = `γ_i(H) ≤ γ_{i+1}(G)` の帰納
- 部分群の類への翻訳は `nilpotencyClass_le_iff_lowerCentralSeries_eq_bot`
  (4A.8(d) で作ったもの。汎用なので `ProblemsWreathClass` → **`ProblemsMaximalClass`** へ移設)

以下は着手前の設計メモ (実装は概ねこの通り):

#### 4A.13 の設計 (2026-07-25、着手前メモ)

書籍 (p.125): `G` 冪零で class `m > 1`, `a ∈ G` ⟹ **`H = G'⟨a⟩` の冪零類は `m` 未満**。

- 添字: mathlib の `lowerCentralSeries X i` = 古典的 `γ_{i+1}(X)`。示すべきは
  `Subgroup.lowerCentralSeries H (m-1) = ⊥` (⟹ `class(↥H) ≤ m-1 < m`)。
  部分群の類への翻訳は **`nilpotencyClass_le_iff_lowerCentralSeries_eq_bot`**
  (4A.10 の `ProblemsCenterIndex.lean` に既設) が使える。
- **鍵の主張**: `k ≥ 1` で `H.lowerCentralSeries k ≤ (⊤ : Subgroup G).lowerCentralSeries (k+1)`
  (古典形 `γ_i(H) ≤ γ_{i+1}(G)`, `i ≥ 2`)。`k = m-1` で右辺 `= γ_{m+1}(G) = ⊥`。
- **帰納段**は易しい: `⁅L, H⁆ ≤ ⁅γ_{k+2}, ⊤⁆ = γ_{k+3}`。
- **基底 `⁅H,H⁆ ≤ γ_3(G) = ⁅G', ⊤⁆` が本体**。`G/γ_3` で `Ḡ'` は中心的なので
  `H̄ = Ḡ'⟨ā⟩` は可換、という筋。⁅H ⊔ K, ·⁆ の分配は使えないので **good-elements 二段**で:
  * `N := γ_3` は正規。`{x | ⁅x,y⁆ ∈ N}` と `{y | ⁅x,y⁆ ∈ N}` はそれぞれ部分群
    (`⁅x₁x₂,y⁆ = x₁⁅x₂,y⁆x₁⁻¹·⁅x₁,y⁆` と `N` 正規; 逆元は `commutatorElement_inv_left`)。
  * 第 1 段: `{y | ⁅a,y⁆ ∈ N}` は `G'` (∵ `⁅G,G'⁆ = γ_3`) と `a` を含む ⟹ `H` を含む
    ⟹ `⁅a, H⁆ ≤ N`。
  * 第 2 段: `{x | ∀ y ∈ H, ⁅x,y⁆ ∈ N}` は `G'` (∵ `⁅G',G⁆ = γ_3`) と `a` (第 1 段) を含む
    ⟹ `H` を含む ⟹ `⁅H,H⁆ ≤ N`。
- `H := commutator G ⊔ Subgroup.zpowers a`。`Subgroup.closure_le` で generator に落とす。

#### 🎉 4A.12(c) の `D₈` 部分 完了 (2026-07-25) — 新 leaf `ProblemsDihedralEight.lean`

`sum_lt_of_three_lt_card_dihedralFour` : **`H = D₈` なら `|A| > 3` で (b) の不等式が成立**
(= 書籍の「`m = 3` が取れる」)。核は `card_le_three_of_maximal_dihedralFour` (`|𝒯(D₈)| ≤ 3`)。

`D₈ = DihedralGroup 4` の可換部分群は 3 つの指数 2 部分群
`⟨r⟩ = closure {r 1}` / `closure {r 2, sr 0}` / `closure {r 2, sr 1}` のいずれかに含まれる:
- 鏡映 `sr i ∈ T` があれば, `r k` との可換性から `2k = 0` (⟹ `k ∈ {0,2}`)、
  `sr j` との可換性から `2(i-j) = 0` (⟹ `j ∈ {i, i+2}`) ⟹ `T ≤ closure {r 2, sr i}`。
- 鏡映が無ければ `T ≤ ⟨r⟩` (`r_one_pow`)。
- `closure {r 2, sr (i+2)} = closure {r 2, sr i}` (`sr (i+2) = r 2 · sr i`) なので候補は 3 つ。

⚠ 教訓: `ZMod 4` の算術は `decide` で済むが、**文脈に自由変数があると `revert; decide` は
「Expected type must not contain free variables」で落ちる** — `∀ i k : ZMod 4, …` の
**閉じた補題として切り出してから `decide`** する。

### 🎉 §4A 完済 (4A.1–4A.13 全問)。

## Ch.4 §4B (書籍 p.131 の Problems 4B) — 着手 (2026-07-25)

新 leaf `OddOrder/Isaacs/Ch04_Commutators/ProblemsHallWitt.lean` (`OddOrder.lean` 配線済)。
§4B は Hall–Witt 恒等式 / three subgroups lemma の節で, repo には既に
`commutator_commutator_le_of_rotate` (Cor 4.10, mod `N` 版) がある。

- ✅ **4B.1** `exists_characteristic_abelian_not_le_center` (class > 2 ⟹ 中心的でない
  特性可換部分群が存在)。**答えは `γ_{c-1} = lowerCentralSeries ⊤ (c-2)`**:
  `⁅γ_{c-1},γ_{c-1}⁆ ≤ γ_{2(c-1)} = 1` (`c ≥ 3` ゆえ `2(c-1) ≥ c+1`; Thm 4.11
  `commutator_lowerCentralSeries_le`) で可換、`⁅γ_{c-1}, G⁆ = γ_c ≠ 1` で非中心。
  特性性は mathlib の `lowerCentralSeries_characteristic` instance。
- ✅ **4B.3** `commutator_lowerCentralSeries_upperCentralSeries_le`
  (`⁅G^i, Z_j⁆ ≤ Z_{j-i}`) + 系 `…_eq_bot` (`⁅G^i, Z_i⁆ = 1`)。`k` の帰納 + three
  subgroups lemma。⚠ 添字対応: mathlib の `lowerCentralSeries ⊤ k` = 古典 `G^{k+1}`、
  `Subgroup.upperCentralSeries G j` = 古典 `Z_j` (`Z_0 = 1`)。
- ✅ **4B.4(a)(b)** `commutator_le_centralizer_of_centralizes` /
  `commutator_isCommutative_of_centralizes`。どちらも three subgroups lemma 直接適用。
  ⚠ **(b) は書籍が `X ⊴ G` を仮定するが不要** — `⁅X,Y⁆` が `X` で正規化されること
  (`le_normalizer_commutator_left`, 4A.9 で作った) だけで足りる。

⚠ 教訓: root の `upperCentralSeries` は **deprecated** で `Subgroup.upperCentralSeries` と
**別定数**として扱われ、instance 検索 (Normal) や型が合わない — 新規コードは必ず
`Subgroup.` 付きで書く。

- ✅ **4B.2** `exists_characteristic_selfCentralizing_class_le_two`
  (`G` 冪零 ⟹ 特性部分群 `K` で `C_G(K) ⊆ K` かつ class ≤ 2)。
  `K` を「特性かつ class ≤ 2」の極大元に取り、`C := C_G(K)` として:
  * **吸収補題**: `A ≤ C` が特性 class ≤2 なら `A ⊔ K` も特性 class ≤2 ⟹ 極大性で `A ≤ K`。
    join の class ≤ 2 は新補題 `lowerCentralSeries_sup_eq_bot`
    (`⁅A,K⁆ = 1` + 両方 class ≤2 ⟹ `A ⊔ K` も class ≤2; `commutatorMemLeft` の good-elements
    二段を 2 回) と `characteristic_sup` (`characteristic_iff_map_eq` + `map_sup`)。
  * `C` 自身が class ≤2 なら吸収で終わり。そうでなければ **4B.1 と同じ `A := γ_{c-1}(C)`**
    (`c = class(↥C) ≥ 3`) が特性可換 ⟹ 吸収で `A ≤ K` ⟹ `C = C_G(K) ≤ C_G(A)` から
    `⁅A,C⁆ = γ_c(C) = 1` で `c` の最小性に矛盾。
  * 相対下降中心列の交換子評価 `commutator_lowerCentralSeries_le'` (Thm 4.11 の相対版) は
    `↥S` の ⊤ 版を `S.subtype` で押し出して得た (`top_subtype_lowerCentralSeries` +
    `map_commutator`)。
  ⚠ 教訓: `x ∈ commutatorMemLeft N y` は `⁅x,y⁆ ∈ N` と defeq だが**構文的に違う**ので
  `commutatorElement_mem_comm` に渡すには `show ⁅x,y⁆ ∈ N from …` の型註釈が要る。
- ✅ **4B.5 完了 (2026-07-25)** — 新 leaf `Ch04_Commutators/ProblemsSupersolvableMann.lean`
  (167 行、`OddOrder.lean` 配線済、全実証明・axiom-clean)。
  `exists_normal_centralizer_eq_self_of_isSupersolvable` (超可解群は自己中心化する正規部分群を
  持つ) + `nilpotencyClass_mannSubgroup_le_of_isSupersolvable` (`class M(G) ≤ 3`) +
  `isNilpotent_mannSubgroup_of_isSupersolvable`。下記の設計どおり。
  ⚠ 実装で判明した追加の API 注意:
  * `isCyclic_of_prime_card` は `[Fact p.Prime]` を要求 → `haveI : Fact (Nat.card ↥M).Prime := ⟨h⟩`
    を置いてから `isCyclic_of_prime_card (p := Nat.card ↥M) rfl`。
  * `QuotientGroup.eq_one_iff.mpr ha` は項として書くと "Unknown constant" になる
    (`rw` の中で使うときは `have h1 : mk' A a = 1 := by rw [...]; exact ha` に分解する)。
  * 最後の `Mbar = ⊥` からの矛盾は `simp at hprime` では閉じない
    (`simp only [Subgroup.card_bot]` + `Nat.not_prime_one`)。

  **`M(G)` と Thm 4.15 は repo に既にある** (`Ch04_Commutators/Mann.lean`):
  `mannSubgroup G` / `nilpotencyClass_mannSubgroup_le_of_centralizer_eq_self [Finite G]
  {K} [K.Normal] (hself : Subgroup.centralizer ↑K = K) : nilpotencyClass ↥(mannSubgroup G) ≤ 3`。
  ⟹ **4B.5 は「超可解群は自己中心化する正規部分群を持つ」に完全に帰着する**。

  **証明 (確定)**: `A` を**可換正規**部分群のうち極大に取る (`Finite.exists_le_maximal`,
  base `⊥`)。`C := C_G(A) ⊇ A`。`A < C` と仮定すると `C/A ≠ 1` なので `G ⧸ A` の中で
  `C.map (mk' A)` に含まれる minimal normal 部分群 `M̄` が取れ
  (`Ch02.exists_isMinimalNormal_le_of_normal`)、**超可解性から `|M̄|` は素数**
  (`Ch03.card_prime_of_isMinimalNormal_of_isSupersolvable` + `IsSupersolvable.quotient`)
  ゆえ `M̄` は巡回。引き戻し `B := M̄.comap (mk' A)` は `A < B ⊴ G`, `B ≤ C` で、
  `A ≤ Z(B)` (∵ `B ≤ C_G(A)`) と `B/A` 巡回から
  `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` で**可換** ⟹ `A` の極大性に矛盾。

  **中断時点の draft** (~150 行、あと数個の名前解決だけ) は
  `scratchpad/wip/ProblemsSupersolvableMann.lean` に退避。実測した API の注意点:
  * `Ch03.IsSupersolvable` / `Ch03.card_prime_of_isMinimalNormal_of_isSupersolvable` は
    `namespace OddOrder.Isaacs.Ch04` の中で `open OddOrder.Isaacs.Ch03` しても解決しなかった。
    **`Ch03.` 前置で書く** (同じファイルで `Ch02.exists_isMinimalNormal_le_of_normal` は
    `Ch02.` 前置で解決している)。
  * centralizer の正規性は `Subgroup.normal_centralizer` (instance、`[H.Normal]` 付き)。
    `Subgroup.centralizer_normal_of_normal` は**存在しない**。
  * `isCyclic_of_prime_card` は `Nat.card ↥M = p` の形を要求する
    (`(Nat.card ↥M).Prime` からは `⟨_, rfl⟩` 等で渡す)。

### 🎉 §4B 完済 (4B.1–4B.5 全 5 問)。

## Ch.4 §4C (書籍 p. 137 の Problems 4C) — 🎉 完済 (2026-07-25)

新 leaf `OddOrder/Isaacs/Ch04_Commutators/ProblemsStabilityGroup.lean` (331 行、
`OddOrder.lean` 配線済、全実証明・axiom-clean)。§4C は「`A` が `G` に自己同型で作用する」
節で, Isaacs 自身が「`A` と `G` をともに半直積 `Γ = G ⋊ A` の部分群とみなす」と宣言している
(p. 131) ので, **周囲群 `Γ` の部分群 `G`, `A`** に対する形で述べた (半直積はその特別な場合)。

「`A` が鎖 `1 = H₀ ⊆ ⋯ ⊆ H_m = G` を stabilize する」(= `H_{i-1}` の `H_i` における各右剰余類が
`A`-不変) は交換子で `⁅H i, A⁆ ≤ H (i-1)` と同値 ⟹ 構造体 `StabilizesChain` (`base` + `step`)。
書籍の有限鎖 (条件は `0 < i ≤ m` のみ) との橋渡しは `stabilizesChain_min`
(`H (min i m)` で上端 `G` に延長; `G ⊴ Γ` ゆえ `⁅G,A⁆ ≤ G` で延長部分は自動)。

| # | 状態 | Lean 名 (`OddOrder.Isaacs.Ch04`) |
|---|---|---|
| 4C.1 | ✅ | `exists_stabilizes_isSubnormal_chain` (+ 有限鎖版 `..._of_finite`) |
| 4C.2 | ✅ | `StabilizesChain.nilpotencyClass_le` / `.isNilpotent` (+ 有限鎖版 `nilpotencyClass_le_of_stabilizes_finite_normal_chain`) |
| 4C.3 | ✅ | `commutator_commutator_eq_bot_of_trivial_on_normal` (+ `le_centralizer_commutator_of_trivial_on_normal`) |

**設計メモ**:

- **4C.1 の「部分正規部分群の鎖」= 反復交換子列**: `M i := ⁅G, A; m - i⁆` (4A.9 の
  `commIterate`)。`⁅L, A⁆` が `L` に正規化される (`le_normalizer_commutator_left`, 4A.9) ので
  各段 `⁅G,A;j+1⁆ ⊴ ⁅G,A;j⁆` が部分正規段になり, `⁅G,A;0⁆ = G ⊴ Γ` からの帰納で
  `IsSubnormal` (Γ 内)。`↥G` 内の部分正規は `IsSubnormal.comap G.subtype` で即出る
  (`subgroupOf = comap subtype`)。停止 `M 0 = ⊥` は `⁅G,A;j⁆ ≤ H (m-j)` の帰納。
  再利用 helper: `commIterate_le_commIterate_of_le` (添字一般の単調減少) /
  `isSubnormal_commIterate` / `normal_subgroupOf_commIterate_succ` /
  `commIterate_le_of_stabilizesChain` / `le_normalizer_of_normal`。
- **4C.2 の核 = `commutator_lowerCentralSeries_le`**: `⁅H i, γ_{j+1}(A)⁆ ≤ H (i - (j+1))` を
  `j` の帰納で示す。各段は Isaacs **Cor 4.10** (three subgroups lemma の mod `N` 形
  `commutator_commutator_le_of_rotate`) を `H₁ = γ_{j+1}(A)`, `H₂ = A`, `H₃ = H i`,
  `N = H (i-(j+2))` に適用: `⁅⁅A, H i⁆, γ⁆ ≤ ⁅H(i-1), γ⁆ ≤ N` と
  `⁅⁅H i, γ⁆, A⁆ ≤ ⁅H(i-(j+1)), A⁆ ≤ N`。**`H i` の `Γ` 内正規性**が `N.Normal` として
  ここで要る = 4C.2 が「正規部分群の鎖」を要求する理由。仕上げは `i = m`, `j = m-1` で
  `⁅H m, γ_m(A)⁆ ≤ H 0 = ⊥` ⟹ `γ_m(A) ≤ A ⊓ C_Γ(G) = ⊥` (faithfulness) ⟹
  `nilpotencyClass_le_of_lowerCentralSeries_eq_bot` (Mann.lean)。
  ⚠ ℕ の切り捨て減算のおかげで `i ≤ j` の縮退段も `H 0 = ⊥` に落ちて自動的に正しい
  (`commutator_le_pred` の `i = 0` 場合が `⁅⊥, A⁆ = ⊥`)。
  ⚠ **書籍の `m ≥ 1` は不要** (`m = 0` なら `G = H 0 = 1` で faithfulness が `A = 1` を
  強いる) — 仮定から落として docstring に注記。
- **4C.3** は three subgroups lemma (`Subgroup.commutator_commutator_eq_bot_of_rotate`) の
  `(G, A, N)` への直接適用: `⁅⁅A,N⁆,G⁆ = 1` は仮定, `⁅⁅N,G⁆,A⁆ ≤ ⁅N,A⁆ = 1` は `N ⊴ G`。

## Ch.5 §5A (書籍 pp. 152-153 の Problems 5A) — 着手 (2026-07-26)

新 leaf `OddOrder/Isaacs/Ch05_Transfer/Problems.lean` (namespace `OddOrder.Isaacs.Ch05`、
`OddOrder.lean` 配線済)。mathlib の transfer は
`MonoidHom.transfer (ϕ : ↥H →* A) : G →* A` (`A` 可換) で、Isaacs の `v : G → H/H'` は
`A = H/H'`, `ϕ` = 自然な射影の場合。

| # | 状態 | Lean 名 / メモ |
|---|---|---|
| 5A.1 | ✅ | `transfer_id_eq_pow_index_of_commGroup` / `coe_transfer_id_of_commGroup` |

⚠ **余域を `↥H` に取る版は避ける**: `H ≤ Z(G)` の一般形で `CommGroup ↥H` を statement 内
`letI` で供給すると, その instance の `toGroup` が `Subgroup.toGroup` と構文的に一致せず
`MonoidHom.id ↥H` の型が合わない (diamond)。**一般の `ϕ : ↥H →* A` 版で述べる**のが正解
(Isaacs の `v : G → H/H'` はまさにこの形)。
| 5A.2 | ⬜ | `v : G → G/G'` は自然な射影 (= `H = ⊤` の場合)。`transfer_eq_pow` は使えない (key 仮説が偽) ので `diff` の定義を展開する必要あり |
| 5A.3 | ⬜ | 推移律 (transversal の積 `ST`、pretransfer の合成)。mathlib は `diff` 経由の定義なので要検討 |
| 5A.4 | ✅ | (a) `transfer_eq_pow_index_of_le_center` / (b) `inf_ker_transfer_eq_bot_of_le_center` + `sup_ker_transfer_eq_top_of_le_center` (+ `normal_of_le_center`) |
| 5A.5–5A.8 | ⬜ | **Schur 乗数 `M(G)`** が要る (5A.5 巡回-by-巡回 / 5A.6 二面体群 / 5A.7 / 5A.8 直積)。repo の Schur 乗数まわりの資産を先に実測すること |

## Ch.4 §4D (書籍 p. 145 の Problems 4D) — 進行中 (2026-07-25)

7 問 (4D.1–4D.7)。coprime action の節。

| # | 状態 | Lean 名 (`OddOrder.Isaacs.Ch04`) / leaf |
|---|---|---|
| 4D.1(a)(b) | ✅ | `commutator_eq_bot_of_centralizer_le_of_coprime` / `inf_centralizer_eq_bot_of_centralizer_le_of_coprime` (`ProblemsCoprimeAction.lean`) |
| 4D.2 | ✅ | `baerAdd_mul_inv_of_commutator_le_center` / `baerMul_div_eq_commutator` (`ProblemsBaerAddition.lean`) |
| 4D.3 | ✅ 全 7 小問 | `IsIrreducibleCoprimeAction.*` (`ProblemsIrreducibleAction.lean`): (a) `exists_isPGroup` / (b) `commutator_le_center` / (c) `fixedPoints_eq_commutator` + `eq_commutator_or_eq_top_of_isAInvariant` / (d) `pow_mem_commutator` + `pow_eq_one_quotient_commutator` / (e) `pow_eq_one_of_mem_commutator` / (f) `pow_eq_one_of_ne_two` / (g) `pow_four_eq_one_of_two` |
| 4D.4 | ✅ | `actionCommutator_eq_bot_of_isPGroup_two_of_fixes_pow_four` (`ProblemsIrreducibleAction.lean`) |
| 4D.5 主張本体 | ✅ | `derivedSeries_semidirectProduct_eq_bot_and_ne_bot` (上界 `..._eq_bot` / 下界 `..._ne_bot` / Lemma 4.29 部分群版 `commutator_commutator_inl_inr_map_eq`、新 leaf `ProblemsDerivedLength.lean`) |
| 4D.5 系 | ✅ | `exists_finite_group_derivedSeries_ne_bot` + `regularPermAut` / `regularPermAut_injective` (同 leaf) |
| 4D.6 | ✅ | `range_fittingProductHom_eq_fixedPoints` / `ker_fittingProductHom_eq_actionCommutator` (新 leaf `ProblemsFittingMap.lean`) |
| 4D.7 | ✅ | `le_oPiCore_compl_of_sylow_isCyclic` (新 leaf `ProblemsCyclicSylow.lean`) |

### 🎉 §4D 完済 (4D.1–4D.7 全 7 問) ⟹ **Isaacs Ch.4 の章末演習 (§4A–§4D) 全完**

### 4D.1 の設計 (実装済)

周囲群 `Γ` の部分群として述べる。鍵は `mem_of_pow_card_eq_one_of_mem_centralizer`
(`C_Γ(N)` の元で `|A|` 乗が 1 のものは `A` に入る) — `x = a·g` 分解 + `C_Γ(N) ⊓ G ≤ N` +
互いに素性。これで `G ≤ N_Γ(A)` が出て `⁅G,A⁆ ≤ G ⊓ A = 1`。(b) は `A₀ := A ⊓ C_Γ(N)` に (a)。

### 4D.4 の設計 (実装済)

`|H|` の強い帰納法。`A`-不変部分群 `H` への制限作用 (`Ch03.IsAInvariant.toMulAutHom`) が
非自明なら、帰納法の仮定で `H` の真の `A`-不変部分群すべてに自明作用 ⟹
`IsIrreducibleCoprimeAction` 成立 ⟹ **4D.3(g)** で `H` の全元が `y⁴ = 1` ⟹ 仮定で固定。
補助 `isAInvariant_map_subtype_of_isAInvariant`。
⚠ `Ch03.IsAInvariant.toMulAutHom` は `ThreeSubgroups.lean` で `_root_.` 無しに宣言されており
実名が `OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom` — namespace Ch04 の
中では `OddOrder.Isaacs.Ch03.…` とフルに書く (`Ch03.…` では解決しない)。

### 4D.5 の設計 (下界 + 系が残り)

**上界 (実装済)**: `rightHom : B ⋊ A ↠ A` で `(B ⋊ A)^{(n)} ≤ ker rightHom = inl(B)`、
`inl(B)` 可換ゆえ `(B ⋊ A)^{(n+1)} = 1`。coprime も faithful も不要。

**下界 (実装済)**: `V := A^{(n-1)} ≠ 1` (導来長がちょうど `n`)。`(|B|, |V|) = 1` と `B` 可換から
Lemma 4.29 (`⁅B, V, V⁆ = ⁅B, V⁆`; repo は `actionCommutator` 形) が使える。
半直積 `Γ = B ⋊ A` の中で `W := ⁅inl(B), inr(V)⁆` とおくと:
- `inr(V) ≤ Γ^{(k)}` (∀ `k ≤ n-1`; `inr` は導来列を保つ + `V = A^{(n-1)} ≤ A^{(k)}`)
- `W ≤ Γ^{(k)}` を `k ≤ n-1` について帰納: `k → k+1` は `W = ⁅W, inr V⁆` (4.29) と
  `W, inr V ≤ Γ^{(k)}` から `W ≤ ⁅Γ^{(k)}, Γ^{(k)}⁆ = Γ^{(k+1)}`。
- 仕上げ: `k = n-1` で `W = ⁅W, inr V⁆ ≤ Γ^{(n)}`、`W ≠ 1` は faithful から
  (`⁅B, V⁆ = 1` なら `V` が `B` に自明作用 ⟹ `V = 1` に矛盾)。
⟹ `Γ^{(n)} ≠ 1` かつ `Γ^{(n+1)} = 1` で導来長ちょうど `n+1`。
⚠ 実装知見: **BG に同型の subgroup 版 4.29 (`commutator_commutator_right_eq`) があるが
BG は Isaacs を import するので Ch04 からは使えない** (import cycle)。Ch04 内では
制限作用の半直積 `Δ = B ⋊[φ∘V.subtype] ↥V` で Γ 形 4.29 を使い、
`F = SemidirectProduct.map (id B) V.subtype : Δ →* Γ` で `Subgroup.map_commutator` により
押し出すのが正しい経路 (`commutator_commutator_inl_inr_map_eq`)。
⚠ `derivedSeries_antitone` は群を**明示引数**で取る (`derivedSeries_antitone A hk`)。

**系 (実装済)**: `C ≀ A` (regular wreath product)。⚠ repo の `WreathProduct` (Ch03,
`D ≀[Ω] Q`) は独立 structure で `SemidirectProduct` ではないため 4D.5 本体に載らない —
同型な半直積 `(A → C) ⋊ A` を `regularPermAut` (座標を `f ↦ fun ω => f (a⁻¹ * ω)` で置換)
として直接構成した。`C` = 位数 `p` 巡回 (`p ∤ |A^{(n-1)}|`, `Nat.exists_infinite_primes`)
とすると `B := (A → C)` は基本アーベル `p`-群 (各座標の位数が `p` を割る) ゆえ
`Nat.card B = p^k` で coprime、正則作用は忠実 (1 の指示関数を `a` で評価)。
⚠ 「導来長」の述語は導入せず `derivedSeries G n ≠ ⊥ ∧ derivedSeries G (n+1) = ⊥` で述べた。
⚠ `Nat.card (Multiplicative (ZMod p)) = p` を使う `rw` は `Fact p.Prime` が `p` に依存して
motive 破綻 — 仮説側で `rw [hcardD] at hpow` と書き換える。

### 4D.6 の設計 (実装済)

`θ = fittingProductHom φ` (`ThreeSubgroupsCoprime.lean`)。像は添字付け替え `a ↦ b*a` で
`A`-固定、逆は `θ(c) = c^{|A|}` と「coprime ⟹ `x ↦ x^{|A|}` が `C_G(A)` 上単射 ⟹
有限性で全射」。核は Lemma 4.28 の `G = C_G(A)·⁅G,A⁆` で `g = c*x` と分解し
`1 = θ(g) = c^{|A|}` から `c = 1` — **位数の数え上げを経由しない**。

### 4D.7 の設計 (2026-07-26 に確定、未実装)

**statement** (PDF p.159 = 書籍 p.146 で確認済): `G` `p`-可解, Sylow `p`-部分群が巡回,
`K ≤ G` が `p'`-部分群で `p ∣ |N_G(K)|` ⟹ `K ⊆ O_{p'}(G)`。

**repo での "p-可解"** = `Ch03.IsPiSeparable ({p} : Set ℕ) G` (π = 単元集合では
π-separable = p-solvable; S7B2 等の既存用法と同じ)。`O_{p'}(G) = oPiCore {p}ᶜ G`,
`O_p(G) = oPiCore {p} G`。

**証明 (|G| の帰納法、hint どおり 2 ケース)**:

- **Case 1: `O_{p'}(G) ≠ 1`**。`Ḡ := G/O_{p'}(G)` に帰納法。仮説は全部遺伝する
  (Sylow の像は巡回、`K̄` は `p'`-群、`p ∣ |N_G(K)|` の位数 `p` の元 `x` は
  `O_{p'}(G)` に入らないので像も位数 `p` で `N_Ḡ(K̄)` に入る)。結論 `K̄ ≤ O_{p'}(Ḡ) = 1`
  (**`O_{p'}(G/O_{p'}(G)) = 1`** — 引き戻しが `p'`-群の正規部分群になるから) ⟹ `K ≤ O_{p'}(G)`。
- **Case 2: `O_{p'}(G) = 1`**。まず **`O_p(G)` が正規 Sylow `p`-部分群**であることを示す:
  1. **Hall–Higman 1.2.3** (repo `Ch03.hall_higman_1_2_3 {p}`, `O_{p'}(G) = ⊥` を仮定) で
     `C_G(O_p(G)) ≤ O_p(G)`。`O_p(G)` は巡回 Sylow の部分群ゆえ巡回=可換なので逆包含も成立し
     **`C_G(O_p(G)) = O_p(G)`**。
  2. `MulAut ↥(O_p(G))` は**可換** (mathlib `IsCyclic.mulAutMulEquiv : MulAut G ≃* (ZMod |G|)ˣ`
     を `injective` で引き戻す; ZGroup.lean:169 と同じイディオム)。`MulAut.conjNormal` の核が
     `C_G(O_p(G)) = O_p(G)` なので **`commutator G ≤ O_p(G)`**。
  3. `O_p(G)` を含む Sylow `p`-部分群 `Q` は `⁅⊤, Q⁆ ≤ commutator G ≤ Q` から正規
     (`le_normalizer_of_commutator_le`)、正規 `p`-部分群ゆえ `Q ≤ O_p(G)`
     (`Subgroup.IsPiGroup.le_oPiCore`) ⟹ `Q = O_p(G)` = 正規 Sylow。
  4. `p ∣ |N_G(K)|` の位数 `p` の元 `x` は Sylow が唯一なので `x ∈ P := O_p(G)`。
     `⟨x⟩ = Ω₁(P)` は巡回 `p`-群の唯一の位数 `p` 部分群ゆえ **char `P` ⟹ `⊴ G`**。
  5. `K` は `⟨x⟩` を正規化 (正規)、`x` は `K` を正規化 ⟹ `⁅K, ⟨x⟩⁆ ≤ K ⊓ ⟨x⟩ = 1`
     (位数互いに素) ⟹ **`x ∈ C_P(K)`, すなわち `C_P(K) ≠ 1`**。
  6. `K` の `P` への coprime 作用 + `P` 可換で **Thm 4.34** (`fixedPoints ⊓ actionCommutator = ⊥`)。
     `P` は巡回 `p`-群なので**非自明な部分群 2 つは必ず非自明に交わる** ⟹ `C_P(K) ≠ 1` から
     `⁅P, K⁆ = 1` ⟹ `K ≤ C_G(P) = P`。`K` は `p'`-群で `P` は `p`-群 ⟹ **`K = 1 = O_{p'}(G)`** ∎

**実装状況 (2026-07-26)** — 新 leaf `Ch04_Commutators/ProblemsCyclicSylow.lean`:

| 部品 | 状態 |
|---|---|
| Hall–Higman 1.2.3 | ✅ 既存 `Ch03.hall_higman_1_2_3` |
| `IsCyclic.mulAutMulEquiv` | ✅ mathlib |
| Thm 4.34 | ✅ 既存 `fixedPoints_inf_actionCommutator_eq_bot_of_abelian` |
| (a) 巡回群の `MulAut` は可換 | ✅ `mulAut_mul_comm_of_isCyclic` |
| (b) `ker (MulAut.conjNormal) = C_G(N)` | ✅ `ker_conjNormal_eq_centralizer` |
| `C_G(O_p(G)) = O_p(G)` | ✅ `centralizer_oPiCore_eq` |
| `G' ≤ O_p(G)` | ✅ `commutator_le_oPiCore_of_isCyclic` |
| `IsPiGroup {p} ↔ IsPGroup p` | ✅ `Ch03.Subgroup.isPiGroup_singleton_iff_isPGroup` (Theorem315.lean に新設) |
| **`O_p(G)` は正規 Sylow** | ✅ `exists_sylow_coe_eq_oPiCore_of_isCyclic` |
| (d) 巡回 `p`-群の非自明部分群は非自明に交わる | ✅ `inf_ne_bot_of_isCyclic_of_isPGroup` (+ `exists_orderOf_eq_prime_of_ne_bot`) |
| (c) `O_{p'}(G/O_{p'}(G)) = 1` | ✅ 既存 `Ch03.oPiCore_quotient_self_eq_bot` |
| `Ω₁(P) ⊴ G` (一般形: 正規巡回部分群の部分群は正規) | ✅ `normal_of_le_of_isCyclic` |
| coprime 作用で `C_P(K) ≠ 1 ⟹ ⁅P,K⁆ = 1` | ✅ `le_centralizer_of_isCyclic_of_exists_fixed` |
| **Case 2 本体** (`O_{p'}(G) = ⊥` ⟹ `K = ⊥`) | ✅ `eq_bot_of_oPiCore_compl_eq_bot` |
| **本体** | ✅ `le_oPiCore_compl_of_sylow_isCyclic` |

⭐ **書籍の hint (`|G|` の帰納法) は不要だった**: `O_{p'}(G/O_{p'}(G)) = 1` が常に成り立つ
(`Ch03.oPiCore_quotient_self_eq_bot`) ので, 商 `G/O_{p'}(G)` に Case 2 を **1 回適用する
だけ**で済む。商への遺伝に要ったのは `Ch01.exists_sylow_map_eq` (自作 1B.5(b)) +
`isCyclic_map_of_isCyclic` + `map_normalizer_le_normalizer_map` の 3 点のみ。

**残りの組み立て手順** (次 iteration):

- **Case 2 (`O_{p'}(G) = ⊥`)**: ✅ 実装済 (`eq_bot_of_oPiCore_compl_eq_bot`)。
- **Case 1 (`O_{p'}(G) ≠ ⊥`)**: `Ḡ = G/O_{p'}(G)` への遺伝に要るもの —
  `Ch03.quotient_isPiSeparable` ✅ / Sylow の像が Sylow = 自作 **1B.5(b)**
  `exists_sylow_map_eq` ✅ (+ Sylow 共役性で「商の任意の Sylow は像」) / `K̄` の位数は `|K|` を
  割る / `mk' x` の位数は `p` (`x ∉ O_{p'}(G)` は位数から) / 結論は
  `Ch03.oPiCore_quotient_self_eq_bot` ✅ で `K̄ = ⊥` ⟹ `K ≤ ker (mk') = O_{p'}(G)`。
- **仮説の形 (2026-07-26 に再検討、こちらを推奨)**: 「Sylow `p` が巡回」は帰納法では
  **`∀ H : Subgroup G, IsPGroup p ↥H → IsCyclic ↥H`** (「すべての `p`-部分群が巡回」) の形で
  持つのがよい。Sylow 版とは同値 (各 `p`-部分群は Sylow に含まれ, 巡回群の部分群は巡回) で,
  Case 2 (`eq_bot_of_oPiCore_compl_eq_bot` は `∀ Q : Sylow p G, IsCyclic` を取る) へは即座に
  渡せる。**商への遺伝**は: `H̄ ≤ G/O` が `p`-群なら `H := comap (mk' O) H̄` の Sylow
  `p`-部分群 `S` が `mk'` で `H̄` へ**同型に**写る (`S ⊓ O = 1` は位数互いに素から,
  `|S| = |H| の p-部分 = |H̄|`) ので `H̄ ≅ S` 巡回。これが Case 1 の唯一の非自明な plumbing。

⚠ **BG 側に重複**: `isPiGroup_singleton_of_isPGroup` / `isPGroup_of_isPiGroup_singleton`
(`BG/Ch1_Preliminary/S04g_Thm418Core.lean`, `PLengthTransfer.lean`) は今回 Isaacs Ch03 に
新設した iff 版と同内容。BG は Isaacs を import するので **BG 側を上流版へ redirect** できる
(hub 案件、lane a の territory 外なので今回は触らない)。

### 4D.3 の設計 (残り (c)–(g))

`IsIrreducibleCoprimeAction φ` (coprime + (A or G 可解) + 真の `A`-不変部分群に自明作用 +
`G` に非自明作用) の下で、既に得ているもの:
`actionCommutator_eq_top` (`⁅G,A⁆ = G`) / `le_fixedPoints_of_ne_top` + `fixedPoints_ne_top`
(**`C_G(A)` が唯一の極大 `A`-不変部分群**) / (a) `p`-群 / (b) `G' ≤ Z(G)`。

- **(c)** `G' < H < G` なる `A`-不変 `H` は無い。Thm 4.34 (Fitting,
  `fixedPoints_inf_actionCommutator_eq_bot_of_abelian`) を `G/G'` (可換) への作用に適用:
  `⁅G/G', A⁆ = ⁅G,A⁆G'/G' = G/G'` なので `C_{G/G'}(A) = 1`。`H` が真の `A`-不変なら `A` は
  `H` 上で自明 ⟹ `H/G' ≤ C_{G/G'}(A) = 1` ⟹ `H = G'`。
  ⚠ 商への作用は `Ch03.IsAInvariant.quotientMulAutHom` (`ThreeSubgroups.lean` に
  `fixedPointsOfMulAut_quotientMulAutHom_eq_map` あり)。
- **(d)** `G/G'` は基本アーベル。`℧₁(G/G')` の引き戻しは `G'` を含む `A`-不変部分群ゆえ (c) で
  `G'` か `G`。`G` なら `G/G' = (G/G')^p` で有限 `p`-群ゆえ `G/G' = 1` = `G = G'`, `G` が
  非自明 `p`-群であることに矛盾。よって `(G/G')^p = 1`。
- **(e)** `G'` は基本アーベル。(b) で `G' ≤ Z(G)` ゆえ可換。class ≤2 なので交換子は双線形で
  `⁅x,y⁆^p = ⁅x^p, y⁆`、(d) より `x^p ∈ G' ≤ Z(G)` ゆえ `= 1`。`G'` は交換子で生成。
- **(f)** `p > 2` ⟹ `x^p = 1`。class ≤2 + `G'` の exponent `p` (e) + `p` 奇 ⟹
  `x ↦ x^p` は準同型 `φ_p : G →* G`。像は `G'` に入り (d)、`G'` 上では自明 (e) なので
  `G/G' →* G'` を誘導し, これは `A`-同変。`A` は `G'` (target) に自明作用するので
  誘導写像は `⁅G/G', A⁆ = G/G'` 上で自明 ⟹ 恒等的に 1 ⟹ `x^p = 1`。
- **(g)** `p = 2` ⟹ `x⁴ = 1`。(d) で `x² ∈ G'`、(e) で `G'` の exponent は 2 ⟹ `x⁴ = 1`。

⚠ 実装知見 (2026-07-25、全 7 小問完了):
- `G ⧸ commutator G` に **`CommGroup` instance は無い** (mathlib は `Abelianization` を別 def に
  している)。repo 既存パターン `letI : CommGroup X := { (inferInstance : Group X) with
  mul_comm := … }` で供給する (`Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl`
  から `IsMulCommutative` を得て `.is_comm.comm`)。この letI の下で
  `fixedPoints_inf_actionCommutator_eq_bot_of_abelian` (Thm 4.34) がそのまま適用できた
  (Group instance は structure eta で defeq)。
- 副産物 `frattini_eq_commutator` (`Φ(G) = G'`)。`frattini G ≠ ⊤` は mathlib
  `frattini_nongenerating` を `K = ⊥` で使う (`⊥ ⊔ Φ = ⊤ → ⊥ = ⊤` の矛盾)。
- class ≤2 の道具は Ch04 Main に既存: `mul_pow_of_class_le_two` ((x*y)^n の collection 公式) /
  `commutatorElement_pow_left_of_class_le_two` (⁅x^n,z⁆ = ⁅x,z⁆^n) /
  `commutatorElement_mem_commutator_top`。
- `omit [Finite A] [Finite G] in` は **docstring より前**に書く (後ろだと構文エラー)。

#### 🎉 4A.11 完了 (2026-07-25) — `ProblemsWreath.lean` に追加

**主結果** (実証明・axiom-clean):
- `commutator_range_inl_map_inr_eq` : **`⁅B, K⁆ = (cosetProdKer K).map inl`**
  (`cosetProdKer K` = 各右剰余類 `Kω` 上で座標積が `1` な tuple 全体)
- `card_commutator_range_inl_map_inr` : **`|⁅B,K⁆| = |A|^{|H| − |H:K|}`** (書籍の形)
- 積の形 `card_cosetProdKer_mul` (`|⁅B,K⁆| · |A|^{|H:K|} = |A|^{|H|}`; ℕ の切り捨て減算を避ける)

支持部品: `rightCosetSetoid` / `cosetRep` (`Quotient.out` による代表元) + 3 補題 /
`filter_mem_cosetRep` / `cosetProdRepHom` (各代表元での剰余類積、核 = `cosetProdKer`、全射) /
`card_cosetRepFixed` (代表元の個数 = `K.index`; `K × T ≃ Q`, `(k,t) ↦ kt` の全単射から)。

⚠ **4A.8(b) は `K = ⊤` の特殊化**なので従来の独立証明 (~70 行) を削除し
`cosetProdKer_top` 経由の系に置換した (同事実の二重管理を解消)。

⚠ 教訓: `open scoped Classical in` は **docstring より前**に置く (後ろだと parse error) /
`Nat.card ⁅A,B⁆` は `(… : Subgroup G)` の型註釈が要る (`Bracket … Type` に取られる) /
`Fintype ↥K` は `[Fintype Q]` だけでは合成されない (classical か `DecidablePred` が要る)。

以下は着手前の設計メモ (実装は概ねこの通り):

#### 4A.11 の設計 (2026-07-25、着手前メモ)

書籍 (p.125): `G = A ≀ H` 正則 wreath (`A` 可換, `H` 有限), base `B = {f : H → A}`, `K ⊆ H`。
**`⁅B,K⁆` = 「`H` の各**左**剰余類上で値の積が単位元」な `f` 全体**、したがって
**`|⁅B,K⁆| = |A|^{|H| − |H:K|}`**。hint の作用は `f^h(x) = f(x h⁻¹)`。

⚠ **repo の wreath は左移動** (`shiftHom q f ω = f (q⁻¹ω)`, `commutatorElement_inl_inr`) なので、
`Δ_q` が触る位置は `{ω, q⁻¹ω}`、`q ∈ K` を動かすと **右剰余類 `Kω`**。剰余類の**個数**は
左右で同じなので位数の主張は不変。docstring に convention 差を明記すること。

- 定義: `cosetProdKer K : Subgroup (Q → D)` = `{f | ∀ ω, ∏ k : K, f (k * ω) = 1}`
  (`∏ k : K` と書けば Finset の剰余類を扱わずに済むのが要点)。
- **⊆**: `Subgroup.commutator_le` で生成元 `⁅inl f, inr q⁆ = inl (Δ_q f)` (`q ∈ K`) に帰着。
  `∏_k (Δ_q f)(kω) = ∏_k f(kω) · (∏_k f(q⁻¹kω))⁻¹` で `k ↦ q⁻¹k` は `K` の全単射ゆえ 1。
- **⊇**: 既存 4A.8(b) (`commutator_range_inl_range_inr_eq`) の証明を一般化。
  * `hgen`: `⁅inl (δ_x d), inr (y·x⁻¹)⁆ = inl (δ_x d · (δ_y d)⁻¹)` は **`y·x⁻¹ ∈ K`**
    (⟺ `y ∈ Kx` 同一右剰余類) のときに `⁅B, K.map inr⁆` の元。
  * 分解: 代表元関数 `ρ` (各右剰余類から 1 点、クラス上定数) を取り
    `f = ∏_{x:Q} (δ_x (f x) · (δ_{ρ x}(f x))⁻¹)`。評価すると
    `f ω · (∏_{x : ρ x = ω} f x)⁻¹` で、`ρ ω ≠ ω` なら空積、`ρ ω = ω` なら剰余類上の積 = 1。
  * `ρ` は `MulAction.orbitRel` (K の左移動作用、軌道 = 右剰余類) の `Quotient.out`、
    または `QuotientGroup.rightRel K` の `Quotient.out` で作る。
- **位数**: `cosetProdKer K = ker Φ`, `Φ : (Q→D) →* (剰余類 → D)`, `Φ f C = ∏_{y∈C} f y` は全射
  ⟹ `|ker| = |D|^{|Q|} / |D|^{|Q:K|} = |D|^{|Q| − |Q:K|}`。

⚠ **4A.8(b) は `K = ⊤` の特殊化**なので、一般版が landing したら
`ProblemsWreath.lean` の `commutator_range_inl_range_inr_eq` を一般版の系に置換して
重複を消す (単一右剰余類 `Q` 上の積 = `coordProdHom`)。一般版は ProblemsWreath 内に置くのが
import 方向的に自然 (現 1033 行 + ~250 行で 1500 上限内)。

#### 🎉 4A.9 完了 (2026-07-25) — 新 leaf `ProblemsIteratedCommutator.lean`

**主結果** (実証明・axiom-clean):
- `isSubnormal_iff_commIterate_le` = **(a)** (`N ⊴ G`, `N ⊔ A = ⊤`, `M` 安定 ⟹ `A ◁◁ G ⟺ M ≤ A`)
- `commIterate_le_nilpotentResidual` = **(b)** (`M ≤ A` ⟹ `M ≤ A^∞`; `N` 正規も `G = NA` も不要)
- `exists_commIterate_stable` (有限群で最終項 `M` が存在 = 系列の安定化)

再利用可能な副産物: `commIterate` (始点と交換相手が別の反復交換子列) と単調性・加法性 /
`le_normalizer_of_forall_conj_mem` / **`le_normalizer_commutator_left`・`_right`**
(`⁅H,K⁆` は両因子で正規化される) / `exists_commIterate_top_le_of_isSubnormal`
(部分正規性の **defect 形** `∃ d, ⁅⊤,A;d⁆ ≤ A`)。

以下は着手前の設計メモ (実装は概ねこの通り):

#### 4A.9 の設計 (2026-07-25、PDF p.137 = 書籍 p.124 で statement 確定)

`G = NA` (`N ⊴ G`, `A ≤ G`)、`M` = 系列 `N ⊇ ⁅N,A⁆ ⊇ ⁅N,A,A⁆ ⊇ ⋯` の最終項。
**(a) `A ◁◁ G` (⚠ subnormal、PDF 画像で `⊲⊲` を確認) ⟺ `M ⊆ A`** / **(b) `M ⊆ A` なら `M ⊆ A^∞`**。

- 定義: `commIterate N A 0 = N`, `commIterate N A (i+1) = ⁅commIterate N A i, A⁆`
  (新 leaf `Ch04_Commutators/ProblemsIteratedCommutator.lean`)。
- **(a) ⟸**: 部分正規鎖は `A = L_k A ≤ ⋯ ≤ L_1 A ≤ L_0 A = N ⊔ A = ⊤` (`L_i := commIterate`)。
  各段 `W := L_{i+1} ⊔ A ⊴ L_i ⊔ A` は `Subgroup.normal_subgroupOf_iff_le_normalizer` +
  `sup_le` で 2 本に分ける:
  * `A ≤ N_G(W)`: `A ≤ W` ゆえ `⁅A,W⁆ ≤ ⁅W,W⁆ ≤ W` (`le_normalizer_of_commutator_le`)。
  * `L_i ≤ N_G(W)`: 共役 `f = MulAut.conj x` (`x ∈ L_i`) で `W.map f = L_{i+1}.map f ⊔ A.map f`
    (`Subgroup.map_sup`)。`L_{i+1}.map f = L_{i+1}` は「**`⁅H,K⁆` は `H` で正規化される**」
    (`⁅hx,y⁆ = h⁅x,y⁆h⁻¹⁅h,y⁆` = `commutatorElement_mul_left_eq_conj_mul` から)、
    `A.map f ≤ W` は `xax⁻¹ = ⁅x,a⁆·a ∈ L_{i+1}A`。`x⁻¹` にも適用して両包含。
  ⚠ `⁅H, K ⊔ L⁆` の分配は偽なので使わない (`sup_le` を **normalizer 側**で使うのが要点)。
- **(a) ⟹**: `IsSubnormal A` の構造帰納で **`∃ d, commIterate ⊤ A d ≤ A`** (defect 版):
  `top` は `d = 0`、`step (A ≤ K) (K subnormal) (A ⊴ K)` は IH の `d` に対し
  `commIterate ⊤ A d ≤ commIterate ⊤ K d ≤ K` (第 2 引数単調) から
  `commIterate ⊤ A (d+1) = ⁅…, A⁆ ≤ ⁅K,A⁆ ≤ A`。あとは `M = ⁅M,A⁆` を `d` 回反復して
  `M = commIterate M A d ≤ commIterate ⊤ A d ≤ A`。
- **(b)**: `M = ⁅M,A⁆` と `M ≤ A` から `M = commIterate M A i ≤ Subgroup.lowerCentralSeries A i`
  (∀ i) ⟹ `M ≤ ⨅ i, … = nilpotentResidual A` (= `A^∞`)。
  ⚠ `nilpotentResidual` は `Ch09_MoreSubnormality/NilpotentResidual.lean` だが、そこは
  **Ch01 しか import しない**ので Ch04 から import しても cycle 無し (実測済)。
- `M` は「最終項」= 有限性で `L k = L (k+1)` となる `k` の値。仮説として
  `hM : commIterate N A k = commIterate N A (k+1)` を取る形が扱いやすい
  (存在は減少列の安定性から別途)。

### §1D の欠落 (2026-07-25 に発見・補充)

§1D は **1D.17 までしか形式化されていなかった** (1D.18 / 1D.19 が欠落)。3B.14 が 1D.19 を
使うので先に補充した。1D.18 = `F(G/Z(G)) = F(G)/Z(G)`、1D.19 = 「`C = C_G(F)` として
`C/(C ⊓ F)` は非自明な abelian 正規部分群を持たない」(対応定理の形
「`A ⊴ ↥C` かつ `⁅A,A⁆ ≤ F.subgroupOf C` ⟹ `A ≤ F.subgroupOf C`」で述べた)。
⟹ **章末問題の「済」ラベルは番号ごとに実測で確認すること** (§1D は 1D.5 だけが欠落と
思われていたが実際は 1D.18/1D.19 も欠けていた)。

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
| 3B.8 | ✅ | `sylow_normal_of_forall_isCoatom_index_prime` / `isSolvable_of_forall_isCoatom_index_prime` / `exists_normal_qComplement` |
| 3B.9 | ✅ | `exists_subgroup_card_eq_of_isSupersolvable` |
| 3B.10 | ✅ | `sylow_normal_of_isSupersolvable` (3B.7(b) + 3B.8 の核の系) |
| 3B.11 | ✅ | `prime_dvd_index_frattini_of_dvd_card_frattini` |
| 3B.12 | ⚠ 訂正版 | `index_sup_eq_relIndex_of_isMinimalNormal_of_not_le` (書籍の主張は偽 — 下記) |
| 3B.13 | ✅ | `exists_greatest_isSolvable_normal` (+ `isSolvable_sup_of_normal`) |
| 3B.14 | ✅ | `center_fitting_greatest_isSolvable_normal_centralizer` (1D.19 + `|S|` 帰納) |
| 1D.18 | ✅ | `Ch01.fitting_quotient_center` (§1D の欠落を補充) |
| 1D.19 | ✅ | `Ch01.le_fitting_subgroupOf_of_commutator_le` (+ `center_fitting_map_eq_inf_centralizer`) |
| 3B.15 | ✅ | `normal_of_index_minimal` (Berkovich) |

⟹ **§3B は 3B.1-3B.15 全完** (3B.12 のみ訂正版)。**2026-07-26 に 3A.6 も完了したので
Isaacs Ch.3 の章末演習は全問完済** ⟹ あわせて **Isaacs Ch.1–Ch.4 の章末演習が全問完済**。

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

- **3B.8 の核 = Sylow 個数の合同式**: 「極大部分群の指数がすべて素数」⟹ 最大素因数 `p` の
  Sylow `p`-部分群は正規。`P` が非正規なら `N_G(P) ≤ M` (極大) が取れ、`P ∈ Syl_p(M)` かつ
  `N_M(P) = N_G(P)` なので `n_p(G) = n_p(M)·[G:M]`。両者 `≡ 1 (mod p)` から `[G:M] ≡ 1 (mod p)`
  ⟹ `[G:M] > p` で `p` の最大性に矛盾。可解性と正規 `q`-補群 (最小素因数 `q`) はこの核 +
  `G ⧸ P` への帰納法で従う。**正規 `q`-補群は「`|H|` が `q` で割れない正規部分群で `[G:H]` が
  `q`-冪」**という指数形で述べた (存在量化の中で `G ⧸ H` を書くと `H.Normal` instance が
  statement 内で取れないため; 書籍の定義「指数が Sylow `q`-部分群の位数に等しい部分群」と同値)。

### ⚠ 3B.12 は書籍の主張のままでは**偽** (2026-07-25 に反例を確認)

書籍 (p. 85): 「`G` 可解, `Φ(G) = 1`, `M` 極大, `H ⊆ M` ⟹ `G` は指数 `|M : H|` の部分群を持つ」。
**反例 = `G = A₄`**:

- `A₄` は可解、`Φ(A₄) = 1` (極大部分群は `V₄` と 4 個の `C₃`、共通部分は 1)
- `M = V₄` は極大 (指数 3; 位数 6 の部分群が無いので極大)
- `H = ⟨(12)(34)⟩ ≤ M` で `|M : H| = 2`
- しかし `A₄` は指数 2 (= 位数 6) の部分群を持たない (古典的事実)

原文は PDF ページ画像 (書籍 p.85 = PDF p.98) で確認済 — OCR の読み違いではなく確かに `H ⊆ M`。
書籍の議論が通るのは「**`M` に含まれない極小正規部分群 `N` がある**」場合で、そのとき
`G = N ⋊ M` から `N ⊔ H` がちょうど指数 `|M : H|` を与える。`A₄` の `M = V₄` は唯一の極小正規
部分群 `V₄` 自身を含むので、この条件が破れている。⟹ 訂正版
`index_sup_eq_relIndex_of_isMinimalNormal_of_not_le` を形式化し、docstring に反例を明記した。

- **3B.6(c)**: `H := N⟨h⟩` の中で `⟨h⟩` は `N` の補群 (`isComplement'_subgroupOf_of_coprime`
  を新規に証明)。`h₂ := x h x⁻¹` の生成する `⟨h₂⟩` は位数 `o(h)` で `|N|` と互いに素なので
  D-part の **`U` 可解枝** (`⟨h₂⟩` は巡回) が使え、`⟨h₂⟩ ≤ ⟨h⟩^y` (`y ∈ N`) を得る。
  `⟨h⟩ ⊓ N = 1` より `G ⧸ N` での像を比べて `k = h⁻¹`, すなわち `h ~ h⁻¹`。
