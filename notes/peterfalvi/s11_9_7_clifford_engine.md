# Pf §11 (9.7) Clifford decomposition engine — design (lane-c, 2026-06-22)

> Goal: prove `clifford_dichotomy` (Pf 9.7) `Nonempty (CliffordCaseAData chars) ∨ Nonempty
> (CliffordCaseBData chars)` by building the Clifford decomposition of the chief factor `H̄ = H/H₀`
> as an `F_p[U]`-module.  Deep, multi-session.  User-chosen (2026-06-22) over de-opacify-only /
> wait-for-hub.  正本 = this note.  Owner = lane-c (`S11_MaximalII_III_IV.lean`).

## 教科書 (9.7) 証明 (mmd 04.11 L53-69)

`H̄` は (9.6) で `UW₁`-既約 `F_p`-加群 (dim `q`、`|H̄|=p^q`)。`U` に制限し Clifford:
`H̄ = H₁ ⊕ ⋯ ⊕ H_k`、`H_i` は既約 `F_p[U]`-加群で `W₁` 共役。`q = dim H̄ = k·dim H₁`。`q` 素数ゆえ
**k=q (CaseA, dim H₁=1)** か **k=1 (CaseB, U 既約)**。

- **CaseA (k=q)**: `H_i` 位数 `p`、`a=|U:C_U(H₁)| ∣ p-1`、`U/C_U(H_i)` 巡回位数 `a`、
  `Ū ↪ (位数 a の巡回群)^{q-1}`。
- **CaseB (k=1)**: (8.5.b) で `U'` が `H` を中心化 ⟹ `Ū` abelian。`F=End_{F_p[U]}(H̄)` は体
  (Schur+有限可除環=体 Wedderburn)。`Ū≅U*⊆F*`、`H̄` は `F` 上 1 次元、`Ū` 巡回、`W₁` が `Ū` 上 FPF
  ⟹ `U*∩F_p=1` ⟹ `u` は `p-1` と互いに素・`(p^q-1)/(p-1)` を割る。

## 前提: ChiefFactorData の de-opacify (step 0、ungated)

`ChiefFactorData` の `quotient_elementaryAbelian` / `quotient_chiefFactor` /
`U_noncentral_on_quotient` は現状 **opaque `True`** (`exists_chiefFactorData` が捨てている)。engine は
`H̄` の**実**構造 (el-ab + 既約 + 非中心) を要する。`exists_chiefFactor_seed` (S11:1091) /
`exists_chiefFactor_kernel` (897) が**実証明を保持**しているので、それを field に通す:
- `quotient_elementaryAbelian` → `IsElementaryAbelian p (↥data.H ⧸ (H0.subgroupOf data.H))`
- `quotient_chiefFactor` → 既約性 (∀ A-inv 部分群 = ⊥ or ⊤、`coprimeFrobeniusChiefFactor_card` の `hirr` 形)
- `U_noncentral_on_quotient` → `C_H̄(U) ≠ ⊤` (action form)
chiefFactor_basic (済) は `_holds` / `quotient_order` 経由ゆえ互換 (field 値を返すだけ)。

## 進捗

- **steps 3–5 DONE (2026-06-22, commits `f90a435f` / `87395477` / `bd78654b`)** — Clifford 算術核心 **完成**
  (全 sorry-free + axiom-clean、AxiomsCheck 登録、full build 緑、FT sorry 130 不変):
  - **step 3 `card_eq_pow_of_iSup_aInvariant_irreducible`** (order step): 有限・要素可換な `K` が
    φ-不変・φ-既約・共通位数 `n` の部分群族の join `⨆ S i = ⊤` なら `∃ k, |K| = n^k`。証明 = 非零ピースの
    極大 `SupIndep` 部分族を抽出 (既約性で span 維持: ピースと partial join の交わりが φ-不変 ⟹ ⊥ or 全体、
    ⊥ なら族を拡大できて極大性に矛盾) → `Subgroup.noncommPiCoprod` で内部直積 (独立性で単射・span で全射) ⟹
    `|K| = ∏ n = n^k`。**罠**: `Finset.SupIndep.insert` は `IsModularLattice (Subgroup K)` 要 →
    `hcomm` から `letI : CommGroup K` を合成 (基底 Group 継承で `Subgroup K` 型同一性保持)。
    `smul_smul : a•b•x = (a*b)•x` (結合は forward)。
  - **step 4 軌道 3 補題** (`isAInvariant_comp_subtype_pointwise_smul` / `forall_aInvariant_le_pointwise_smul`
    / `card_pointwise_smul`): `U ◁ A` 作用で、A-軌道 `φ a • S₀` の各並進が U-不変・U-既約・同位数。
    不変性 = `φu•(φa•S₀)=φa•(φ(a⁻¹ua)•S₀)=φa•S₀` (`a⁻¹ua∈U`); 既約性 = `J≤φa•S₀` を `φa⁻¹•J≤S₀` に
    引き戻す; 位数 = automorphism は位数保存 (`pointwise_smul_def` + `equivMapOfInjective`)。
  - **step 5 `chiefFactor_clifford_dim_dvd_q`** (組み立て): 極小 U-不変 `S₀≠⊥` (有限性) で
    `0<d ∧ d∣q ∧ |S₀|=p^d`。step2 span (full action) + step3 order (restricted U-action) ⟹ `|H̄|=|S₀|^k`、
    `|H̄|=p^q` (`chiefFactor_quotient_card`) ⟹ `p^q=(p^d)^k` ⟹ `q=d·k` (`Nat.pow_right_injective`)。
    **q 素数 ⟹ d∈{1,q}** = (9.7) 二分の算術的核心。**インフラ罠**: `data.H`(`TypesIIIIIIVSetup.H`) vs
    `data.typeP.H` の defeq をインスタンス探索が展開せず action の `[N.Normal]` が見つからない →
    `@[reducible] TypesIIIIIIVSetup.H` で透過化 + `attribute [instance] ChiefFactorData.N_normal`
    (文中で `Subgroup (↥H⧸N)` を使うため; instance-field は自動でグローバル instance にならない)。
- **step 6 DONE (2026-06-23, commit `deab3074`)** — **構造的 U-二分** (sorry-free + axiom-clean):
  - `chiefFactor_clifford_dim_dvd_q` を enrich (S₀ の U-不変性 `hS₀inv` + U-既約性 `hirr₀` も返す)。
  - **`chiefFactor_clifford_U_dichotomy`**: `(∀ J U-inv, J=⊥∨⊤)` (case b: U-既約) `∨` `(∃ S₀≠⊥ U-inv,
    |S₀|=p)` (case a)。証明 = `d∈{1,q}` を q 素数 (`data.nontrivial.2.1`) で読み、`d=q ⟹ |S₀|=p^q=|H̄| ⟹
    S₀=⊤` (`Subgroup.eq_top_of_card_eq`) + 極小性で U-既約、`d=1 ⟹ |S₀|=p`。**これが (9.7) の case 分け本体**。

- **step 7a DONE (2026-06-23, commit `e2a673bd`)** — **subgroup-level Singer 機構** (CaseB 体モデル核心、
  sorry-free + axiom-clean):
  - **`isCyclic_card_dvd_of_aInvariant_irreducible_faithful_comm`**: 有限**可換** A が有限 el-ab `p`-群 K に
    **忠実・既約** (∀ φ-inv J, J=⊥∨⊤) 作用 ⟹ **A 巡回 ∧ |A| ∣ |K|-1**。= (9.7) case (b) の構造核心
    (`U`-既約 chief factor ⟹ `Ū` 巡回・位数 ∣ p^q-1)。`elabRepresentation`→`Representation.asModule`→
    `SingerField.isCyclic_and_card_dvd_of_faithful_irreducible_comm` を配線。
  - **`elabRepresentation_isIrreducible`** (支持 bridge): `elabRepresentation p φ` の `Subrepresentation`
    束が `IsSimpleOrder` ⟺ subgroup-level 既約。`Submodule (ZMod p)(Additive K) ≃o Subgroup K`
    (`AddSubgroup.toZModSubmodule`/`toSubgroup'`) + `elabRepresentation_apply` で対応。
  - **module-instance hell 突破 (重要知見)**: ① `set_option backward.isDefEq.respectTransparency false`
    = `asModule` が ρ を無視する def ゆえ `Module k[G] asModule` の instance 探索が ρ を型から推論できない問題を
    解消 (mathlib も同設定)。② 結論を `IsSimpleOrder (Subrepresentation …)` で直接述べる (`IsIrreducible`
    abbrev は `[Field (ZMod p)]` 要 → `MonoidAlgebra` の ZMod Field/CommSemiring diamond)。③ module は
    **instance arg** で渡す (ambient `CommGroup K` 上で構築; `IsElementaryAbelian.zmodModule` は
    `IsMulCommutative` 経由で diamond)。

- **step 7c DONE (2026-06-23, commit `4b4666de`)** — **CaseA bound `a∣p-1`**:
  `card_range_dvd_card_sub_one_of_prime_card`: A が素数位数 p の K に作用 ⟹ `|φ.range| ∣ p-1`
  (K 巡回 ⟹ `MulAut K≅(ZMod p)ˣ` 位数 p-1 [`IsCyclic.card_mulAut`+`Nat.totient_prime`]、`φ.range≤MulAut K`)。
  sorry-free + axiom-clean。CaseA の `a=|U:C_U(H₁)|∣p-1`。

- **(8.5.b) DONE (2026-06-23, commit `f4a49642`)** — **`typeP_commutator_U_centralizes_H`**:
  `⁅data.U, data.U⁆ ≤ C_M(H)` (Ū=U/C_U(H) 可換)。sorry-free + axiom-clean。証明 = `⁅U,U⁆⊆M''=⁅M',M'⁆`
  (`commutator_mono`+`derivedInG J=⁅J,J⁆` [`map_commutator`+`← MonoidHom.range_eq_map`+`range_subtype`]) +
  `M''⊆F(M)=H⊔(U⊓C_M(H))` (`secondDerived_le_fitting` carrier field) + `K=U⊓C_M(H)≤C_M(H)≤N(H)` で
  `↑(H⊔K)=↑H·↑K` (`coe_mul_of_right_le_normalizer_left`, `centralizer_le_normalizer (↑H:Set)`;
  `Subgroup.normalizer` は Set 引数) + element-wise (x=h·c, h=x·c⁻¹∈U⊓H=⊥, x=c∈K)。
  **(8.5.b) の "U' が H 中心化" は H 全体 (H̄ でなく) ゆえ H̄=H/N 上でも自動で中心化** (N≤H)。

- **step 7b DONE (2026-06-23, commit `e40c98f6`)** — **`chiefFactor_caseB_image_cyclic`** (chief-factor
  Singer 適用, sorry-free + axiom-clean): case (b) (U-既約 chief factor) で **`Ū=φU.range` 巡回 ∧
  `|Ū|∣p^q-1`**。7a Singer (`isCyclic_card_dvd_of_aInvariant_irreducible_faithful_comm`) を H̄ に適用。
  A=`φU.range` (忠実像 Ū)、φ=`A.subtype` (subtype 単射=faithful)、irreducible=case(b) hyp から range 経由
  transfer、**可換=(8.5.b)**: 任意 `⁅a,b⁆∈[U,U]⊆C(H)` ⟹ H̄ 上自明作用 (`hcentral_triv`) ⟹
  `φU ⁅a,b⁆=1` ⟹ `Commute (φU a)(φU b)`。**instance 知見 (再利用大)**: ① `[Group][IsMulCommutative]→
  CommGroup` は **scoped** (`open scoped IsMulCommutative`、zmodModule と一致させる)、② `Fact p.Prime` を
  足すと `ZMod p` が Field 化し zmodModule の CommRing 経路と semiring diamond ⟹ **NeZero p のみ**使う、
  ③ element commutator `⁅,⁆` も scoped (`open scoped commutatorElement`)。
- **dvd_norm DONE (2026-06-23, commit `fa766efc`)** — **`chiefFactor_caseB_image_dvd_norm`**: FPF 入力
  `Coprime |Ū| (p-1)` を仮定すれば step 7b の `|Ū|∣p^q-1` が **`|Ū|∣(p^q-1)/(p-1)`** に昇格 (sorry-free +
  axiom-clean)。= (9.7)(b) mmd L69 の初等数論最終段 (`(p-1)∣(p^q-1)` via `p≡1 [MOD p-1]` + coprime ⟹
  `|Ū|·(p-1)∣p^q-1` ⟹ 商整除)。**∴ case-(b) 整除条件 (`u_coprime`/`u_dvd_norm`) の残ハード入力は
  `Coprime |Ū| (p-1)` 一点に縮約**。

- **frontier = case-(b) FPF coprime (`Coprime |Ū| (p-1)`) = 体モデル同型 (9.7)(b) L51 — 重・multi-session**:
  textbook (9.7)(b) L69 は `W₁ が Ū 上 FPF ⟹ U*∩𝔽ₚ=1 ⟹ coprime(u,p-1)`。これには **体 F=p^q と同型
  `(H̄⋊Ū)⋊W₁ ≅ (F⋊U*)⋊Aut F`** (L51) を構築し W₁ を `Aut F`・`𝔽ₚ` を W₁-不変部分体と同定する必要。
  Singer 機構 (7a) の体は `MonoidAlgebra(ZMod p)Ū⧸I` で W₁-作用を持たない ⟹ `End_{𝔽ₚ[U]}(H̄)` を体化
  (Schur+Wedderburn) し W₁-Galois 作用を載せる新インフラ (~150-250+ 行) が要る。**これが case-(b) の真の長物**
  (step 7b/dvd_norm で他は片付いた)。
  **carrier 構成 (clifford_dichotomy 閉鎖) — 体モデル後に GATED**: `CliffordCaseBData` は `chars.u` を参照
  (`u_coprime_p_sub_one : Coprime chars.u (p-1)`, `u_dvd_norm_quotient : chars.u ∣ (p^q-1)/(p-1)`) が
  `Section11CharacterData.u` は **free field** (`u_eq_card_quotient` opaque)。**`chars.u=|Ū|` pin が要る**
  (lane-b S12 は tau/S/support のみ消費・u 未使用ゆえ安全寄りだが **carrier signature 変更 = cross-lane、
  hub 判断推奨** [[cross-lane-sync-via-notes]])。pin 後、上の `chiefFactor_caseB_image_*` (|Ū| 版) を
  `chars.u` 版に乗せれば CaseB carrier が組める。
  - **CaseA (case a) = 型問題 + 構成 (別 gate)**: `Hpart : Fin q → Subgroup G` 各位数 `p` だが H̄ の
    order-p ピースは G 引き戻しで位数 `p|H₀|` ⟹ **`Subgroup G` で位数ちょうど p は不整合** (構造体 `Hpart`
    型を `Subgroup (↥H⧸N)` に直す carrier 変更要、consumer は `caseA.a` のみ使用)。`a∣p-1` は **7c で済**
    (`card_range_dvd_card_sub_one_of_prime_card`)。
  - **∴ clifford_dichotomy は honest には閉じられない**: case-(b) は体モデル FPF + chars.u pin、case-(a) は
    Hpart 型変更。いずれも単一 session 増分でない。**step 7b/dvd_norm で (9.7) の Singer 算術核心は完了**、
    残りは体モデル建設 (大物) + carrier 設計判断 (hub)。

- **step 0 DONE (2026-06-22, commit `f69557a5`)**: `ChiefFactorData` の 3 opaque field を実構造に
  置換。`exists_chiefFactor_kernel` を強化し、kernel `N = W.comap (mk' N₀)` について
  `IsElementaryAbelian p (↥H ⧸ N)` + `UW₁`-既約 (`∀ J, IsAInvariant (quotientMulAutHom hN) J → J=⊥∨⊤`)
  + `U`-非中心 (`fixedSubgroup (quotientMulAutHom hN) U ≠ ⊤`) を追加で返す。**sorry-free + axiom-clean**
  (AxiomsCheck 登録)。`exists_chiefFactorData` が wire、`chiefFactor_basic` から再 launder 削除。
  - **技法 (設計より単純化)**: 当初案の equivariant-iso transport (`H/N ≅ S`) は **不要**だった。
    既約性は correspondence で: `J ≤ H̄` invariant を `J̃=J.comap(mk' N) ◁ H` に引き戻し
    (`N≤J̃`)、`J̄=J̃.map(mk' N₀) ≤ V` に押し出し (`W≤J̄`)、`J̄⊓S ∈{⊥,S}` を Maschke summand の
    `hirr` で分岐。非中心は `C_V(U) ≤ W` (U-fixed `a·b` は両成分 fixed、`C_S(U)=⊥`) → `C_H(U)≤N`
    → `C_{H̄}(U)=⊥`。**element-wise + `map_fixedSubgroup_eq_fixedSubgroup_quotient` のみ**で iso 不要。
  - **設計上の罠 (記録)**: ① `ChiefFactorData` は `[Finite G]` を**付けられない** (S13 `Hypothesis`
    が `variable {G} [Group G]` のみで `chief : ChiefFactorData` を持つ → 壊れる)。よって action は
    `typeP_quotientCoprimeAction` (要 Finite) でなく `quotientMulAutHom` (Finite 不要) で phrase。
    ② 構造体は `typeP_quotientCoprimeAction`/`IsAInvariant`/`quotientMulAutHom` の定義・open より
    **後ろ**に置く必要 (元 426 行→`exists_chiefFactorData` 直前へ移動)。③ `[N_normal : N.Normal]`
    instance-field + `quotientMulAutHom (N := N) ...` で N を pin しないと instance 検索が N 未確定で失敗。
  - **残依存**: `exists_chiefFactorData`/`chiefFactor_basic` は `typeIII_IV_p_eq_W2` フィールド経由で
    §12 sorry (`theorem88_caseB_prime_orders` = lane-b (10.11)) に依存ゆえ axiom-clean でない (de-opacify
    した 3 構造 field 自体は kernel 由来で clean)。

## ⚑ 方針修正 (2026-06-22, step 1 着手で判明) — subgroup-level + cardinality

**finrank/Representation で組むより subgroup-level (`IsAInvariant`/`fixedSubgroup` + cardinality) が圧倒的に楽。**
理由: ① counting は全部 cardinality で済む — `|H̄|=p^q`、各 U-既約成分 `|S_i|=p^d`、半単純で
`|H̄|=∏|S_i|=(p^d)^k=p^{dk}` ⟹ `q=dk` ⟹ `q` 素数で `d∈{1,q}`。**`finrank` 不要**。② repo の
Maschke = `exists_aInvariant_irreducible_summand_disjoint` (OperatorMaschke.lean:368) は **subgroup-level**
で module instance を内部隠蔽 — これを使えば下の instance 地獄を回避。
- **finrank-instance 地獄 (記録、回避せよ)**: `chiefFactor_finrank` を `card_eq_pow_finrank` 経由で
  作ろうとして放棄。`letI : CommGroup (↥H⧸N) := inferInstance` が量子化群 Group instance と噛み合わず
  `CommGroup`/`Module`/`AddCommMonoid (Additive (↥H⧸N))` 合成が連鎖失敗。**el-ab → Additive module は
  `↥H⧸N` のような quotient carrier では instance が通らない**。必要になったら module instance は
  `exists_aInvariant_*` のように内部に閉じ込めるか、`Additive` を避け cardinality で回す。
- **step 1 着地分 (DONE)**: `chiefFactor_quotient_card : Nat.card (↥H ⧸ chief.N) = chief.p ^ data.q`
  (`quotient_order`+`H0_eq` から、instance 不要、sorry-free)。= dichotomy が読む「dim H̄ = q」基礎。

**subgroup-level dichotomy 証明スケッチ** (実装中):
1. `S₀` := H̄ の極小 nonzero U-不変部分群 (`(Set.toFinite _).exists_minimal`, U-既約)。`d:=Nat.log p |S₀|`。
2. **✅ DONE (span step, commit 次)**: `iSup_smul_eq_top_of_irreducible` = **完全一般補題**
   「既約 A-作用 (`∀ J, IsAInvariant φ J → J=⊥∨⊤`) で任意 nonzero `S₀` は軌道で全体を張る:
   `⨆_{a:A} φ(a)•S₀ = ⊤`」。証明 = orbit join `T` は φ-不変 (reindex `a↦h·a`、`pointwise_mulAut_smul_eq_map`
   +`Subgroup.map_iSup`+`smul_smul`) ∧ `S₀≤T` (a=1) ⟹ `T≠⊥` ⟹ 既約で `T=⊤`。**当初の「W₁-共役だけの join +
   U◁UW₁」より簡単** — L=U⊔W1 全体の軌道 join で十分 (reindex が trivial)。`chief.quotient_chiefFactor` を
   `H:=↥H⧸N`, `φ:=quotientMulAutHom N_aInvariant`, `S₀` で apply ⟹ H̄ は S₀ の (U⊔W1)-軌道で張られる。
   (後で「W₁-共役で十分」= U◁ ゆえ各 `φ(uw)•S₀=φ(w)•S₀` は count 段で必要なら別途。)
3. 各 `φ(g)•S₀` は U-既約・`|·|=|S₀|=p^d` (共役は位数保存)。半単純 (Maschke,
   `exists_aInvariant_irreducible_summand_disjoint` 反復) で H̄ は dim-d U-既約の直和 ⟹ `|H̄|=(p^d)^k` ⟹
   `q=dk` ⟹ `d∣q`。(「全 U-既約成分が dim d」: 成分は `⨆` の被加数の iso ⟹ 同 dim)。**← 次の実装対象**。
4. `q` 素数: `d=q` (S₀=H̄=U-既約 ⟹ **CaseB**) か `d=1` (q 個の位数-p 成分 ⟹ **CaseA**)。
   `chiefFactor_quotient_card` で `|H̄|=p^q`。

## アーキテクチャ (steps) — 旧 module-route (参考、上の subgroup-route を優先)

0. **de-opacify ChiefFactorData** — **DONE**。実 H̄ 構造を露出。
1. **dim H̄ = q** — **DONE (card 版)** `chiefFactor_quotient_card`。finrank 版は instance 地獄ゆえ不要化。
2. **Maschke/半単純**: repo `exists_aInvariant_irreducible_summand_disjoint` (subgroup-level) を反復で
   `H̄|_U = ⊕ 既約` に。mathlib `Representation` Maschke は instance 重く非推奨。
3. **Clifford permutation (新規, mathlib 不在)**: 上スケッチ step 2-3 (`⨆ W₁-共役 = ⊤` + 同 dim)。**核心**。
4. **dichotomy**: 上スケッチ step 4 (`q=dk`, `q` 素数 ⟹ `d∈{1,q}`)。
5. **CaseA 構成 (k=q)**: `q` 成分を G-部分群 (`Hpart`, H̄→H→G 対応) に、位数 `p`、`a ∣ p-1`。
6. **CaseB 構成 (k=1)**: Schur (End 体) + Wedderburn (有限可除環=体)、`Ū` 巡回、整除性。

## 再利用する infra

- **repo**: `IsElementaryAbelian.zmodModule`/`card_eq_pow_finrank`/`mulAutEquivGeneralLinearGroup`
  (PRank.lean); `coprimeFrobeniusChiefFactor_card` (S11:722, Wielandt on H̄); `S03c_Thm37` /
  `S03g_Thm310Module` / `WielandtElabBridge` (coprime FPF action on el-ab を module 形で扱う**前例**、
  mirror 推奨); `typeP_quotientCoprimeAction` (S11:683, H̄ の action)。
- **mathlib**: `RepresentationTheory/{Maschke,Semisimple,Irreducible,Subrepresentation,Submodule}`;
  `RingTheory/SimpleModule/{Isotypic,WedderburnArtin,Basic}`。

## 新規に書く部分 (mathlib/repo 不在)

- **step 3 Clifford permutation** (W₁ が isotypic 成分を推移的に置換) ← 最重要・最難。
- **step 6 field model assembly** (CaseB の End 体 + 巡回 + 整除)。

## 進め方 (上流順)

step 0 (de-opacify) → 1 (bridge+dim) → 2 (Maschke 分解) → 3 (Clifford perm) → 4 (dichotomy) →
5/6 (CaseA/CaseB)。各 step を build-green で commit。step 3 が crux、難航時は ChatGPT 相談可
([[feedback-ask-chatgpt-for-elided-gaps]])。CaseA/CaseB carrier の opaque Prop field は
`True`+`trivial` で可、**実 field** (Hpart/a/u-整除) が本体。

## 注意

- `H̄ ⧸ N` の dependent quotient は `[N.Normal]` 依存 ⟹ `quotientMulEquivOfEq` で iso bridge
  (S11 既存知見、design note s11_wielandt_91)。`zmodModule` の `IsMulCommutative` diamond 注意
  (`WielandtPerFactorDischarge` の `subgroupZmodModule` 参照)。
- これは深い build。完了で (9.7) のみ解禁、(9.8)-(9.11) は別途指標論を要する。
