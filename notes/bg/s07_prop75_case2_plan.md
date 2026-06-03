# BG Prop 7.5 case (2) (= brick 3) 実装プラン — living note

> 2026-06-03。`hypothesis71_of_scn2_or_pLengthOne` (S07:~1075) の case (2) を埋める。
> brick 2b (Prop 1.15(b) 一般形) 完了で前提が揃った。case (1) は Thm 6.7 待ちで明示 sorry。
> mmd 出典: `references/bg/local-analysis.mmd` L2252-2307。

## 完了済み (このセッション)

- **✅ 還元補題 `generated_eq_of_forall_le_opiCoreInG`** (S07, private, build-green, axiom-clean):
  `A ≤ X` かつ `∀ Y ∈ hInvariant X A π, Y ≤ opiCoreInG π X` ⟹ `sSup (hInvariant X A π) = opiCoreInG π X`。
  逆向きは `opiCoreInG π X ∈ hInvariant X A π` (自身が A-不変 π-部分群) から自動。**case 1/2 双方で使う**。
  これで Hypothesis71 の `generated_eq` は「**core claim**: 各 `Y ∈ ℋ_X(A;π')` が `O_{π'}(X)` に入る」に還元済。
- **✅ ne_bot / proper 実証明 + core-claim helper 2 種** (S07, build-green):
  - `primesOf_eq_singleton` (`IsPGroup p A` + `A≠⊥` ⟹ `primesOf A={p}`): `(primesOf A)ᶜ={p}ᶜ` 変換用。core claim で {p}-固有補題(Thm 6.1 等)を呼ぶ際に必要。
  - `le_opiCoreInG_of_normal_of_isPiSubgroup` (`N≤H` + `(N.subgroupOf H).Normal` + `IsPiSubgroup π N` ⟹ `N≤opiCoreInG π H`): `subgroupOf→oPiCore→map subtype` 連鎖の packaging。general case の `O_{p'}(C_G(b))⊓C_X(b) ≤ O_{p'}(C_X(b))` 等で再利用。

## ゴール構造 (`hypothesis71_of_scn2_or_pLengthOne`)

`Hypothesis71 A = ⟨ne_bot, proper, generated_eq⟩`。`rcases hcase with hcase1 | hcase2`:
- **case 1** (p-length one): 全体 `sorry` (Thm 6.7 未形式化; BG 「follows easily from Theorem 6.7」)。
- **case 2** (`A ∈ SCN₂(P)`): `obtain ⟨P, hAP, hAscn2⟩ := hcase2`; `refine ⟨ne_bot, proper, generated_eq⟩`。

### ne_bot (`A ≠ ⊥`) — provable, ~12 LOC
`hAscn2.le_pRank : 2 ≤ pRank ↥(A.subgroupOf P) p`。
`exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (by norm_num) this`
⟹ `∃ B, B.IsElementaryAbelian p ∧ 2 ≤ Nat.log p (card B)`。
`Nat.pow_le_of_le_log (card_pos.ne') hBlog : p^2 ≤ card B`; `card B ∣ card ↥(A.subgroupOf P)` (Lagrange);
`card ↥(A.subgroupOf P) = card ↥A` (`Subgroup.subgroupOfEquivOfLe hAP` の `Nat.card_congr`);
`p ≥ 2` ⟹ `card A ≥ 4 > 1` ⟹ `Nontrivial ↥A` ⟹ `A ≠ ⊥` (`Subgroup.nontrivial_iff_ne_bot` 系)。
別ルート: SCN `selfCentralizing` で `A=⊥ ⟹ C_↥P(⊥)=⊤=⊥ ⟹ ↥P trivial`, P Sylow nontrivial と矛盾。

### proper (`A < ⊤`) — provable, ~8 LOC
`P : Sylow p G`。`P < ⊤` を示す: `P=⊤ ⟹ IsPGroup p G ⟹ IsNilpotent ⟹ IsSolvable`, `hG.notSolvable` と矛盾。
`P.isPGroup' : IsPGroup p ↥↑P`; `hPtop ▸ this : IsPGroup p ↥(⊤:Subgroup G)`;
`.of_surjective Subgroup.topEquiv.toMonoidHom topEquiv.surjective : IsPGroup p G`;
`haveI := this.isNilpotent` (要 `[Finite G]`); `IsNilpotent.to_isSolvable` (instance) で `IsSolvable G`。
最後 `lt_of_le_of_lt hAP hP_lt : A < ⊤`。

### generated_eq — 還元補題適用 + core claim
```
intro X hAX hXlt
apply generated_eq_of_forall_le_opiCoreInG hAX
intro Y hY            -- hY : Y ∈ hInvariant X A (primesOf A)ᶜ
-- core claim: Y ≤ opiCoreInG (primesOf A)ᶜ X
```
`primesOf A = {p}` (A は p-群, nontrivial): `primesOf A = {q | q ∈ (card A).primeFactors}`,
`IsPGroup p A` + `A≠⊥` ⟹ `(card A).primeFactors = {p}`。よって `(primesOf A)ᶜ = {p}ᶜ`。

## core claim 本体 (mmd L2273-2307) = 最重部分

設定: `π={p}`, `Z = Ω₁(Z(P))` (= `Omega ↥(center P) p 1` を G に戻す or `omega1OfAbelian`)。
`Y ∈ ℋ_X(A;p')` = `Y ≤ X ∧ A ≤ N_G(Y) ∧ IsPiSubgroup {p}ᶜ Y`。目標 `Y ≤ O_{p'}(X)`。

### B 構成 (7.4): `B ∈ E_p²(A)` かつ `B ⊴ P` — 要新規補題
`A ⊴ P` (SCN), `Z(P) ⊆ A` (SCN selfCentralizing ⟹ center P ≤ C_P(A)=A)。2 分岐:
- **Z(P) 非 cyclic**: `B ∈ E_p²(Z)`, `Z = Ω₁(Z(P))`。`ElementaryAbelian.of_card_prime_sq_of_not_isCyclic` 系。
- **Z(P) cyclic**: `|Z|=p`。`(Ω₁(A)/Z) ∩ Z(P/Z) ≠ 1` を **G 2.6.4** (`IsPGroup.normal_inf_center_nontrivial`,
  P/Z の p-群性 + Ω₁(A)/Z 正規 nontrivial) で。`B/Z` 位数 p を取り `B ⊴ P`。
  **罠**: P/Z 商 + Ω₁(A)/Z の正規性 + pullback。要 bar-quotient 補助。
共通: `B ≤ A`, `B` elementary abelian 位数 p², `B ⊴ P`, `Nat.Coprime (card B) (card Y)` (B p-群, Y p'-群)。

### special case 1 (mmd L2275-2285): `X = C_G(b)`, `b ∈ B^# ∩ Z`
- `P` は `X = C_G(b)` の Sylow p (b ∈ Z(P) ⟹ P ≤ C_G(b)=X, かつ |X|_p = |P|)。**要補題: P ∈ Sylow p X**。
- `A` abelian normal in P ⟹ **Thm 6.1** (`thmA4b`, X solvable/odd を `hG.solvable_of_lt_top`+`hodd.of_dvd_nat`):
  `A ≤ O_{p',p}(X) = oPiPrimePiCore {p} ↥X`。
- bar = mod `O_{p'}(X)`: `X̄ = X/O_{p'}(X)`, `O_p(X̄) = O_{p',p}(X)/O_{p'}(X)`。**要 bar-quotient bridge**:
  `oPiPrimePiCore {p} X` の像 = `oPiCore {p} X̄ = opCore p X̄` (`oPiPrimePiCore` 定義が comap mk' なので
  `map mk'` で像 = `oPiCore {p} X̄`; `oPiCore_singleton_eq_opCore` で `opCore`)。
- `[Ā,Ȳ] ⊆ O_p(X̄) ∩ Ȳ = 1` (Ȳ は O_p(X̄) を正規化, A normalizes Y; Ȳ p'-群, O_p p-群 ⟹ 交わり 1)
  ⟹ `Ā ⊆ C_{O_p(X̄)}(Ȳ)`。
- `C_P(A) ⊆ A` (SCN) ⟹ `C_{O_p(X̄)}(Ā) ⊆ Ā` ⟹ **Prop 1.10** (Ȳ, O_p(X̄) を A,G に置く;
  `coprime_nilpotent_acts_trivially_of_centralizer_self`, φ = Ȳ の O_p(X̄) 共役作用):
  Ȳ が O_p(X̄) を中心化。
- **Prop 1.15(a)** (`hall_higman_solvable_specialization` @ X̄, `O_{p'}(X̄)=1` は `oPiCore_quotient_self_eq_bot`):
  `C_X̄(O_p(X̄)) ⊆ O_p(X̄)` ⟹ `Ȳ ⊆ O_p(X̄)`。Ȳ p'-群 ∩ p-群 ⟹ `Ȳ=1` ⟹ `Y ⊆ O_{p'}(X)`。

### special case 2 (mmd L2287-2297): `X = C_G(b)`, 任意 `b ∈ B^#`
case 1 から `|Z|=p`, `B = ⟨b⟩ × Z` と仮定可。`P₁ = C_P(b)`, `P₂` Sylow p of X ⊇ P₁。
`P/P₁ = P/C_P(B) ≅ Z_p` (7.4) ⟹ `|P₂:P₁| ≤ p`, `P₁ ⊴ P₂` ⟹ `Z ⊆ Z(P₁)`, `Z(P₁) ⊴ P₂`。
**Thm 6.1**: `Z ⊆ Z(P₁) ⊆ O_{p',p}(X)`。`[Y,Z] ⊆ Y ∩ O_{p',p}(X) ⊆ O_{p'}(X)`。
`A normalizes C_Y(Z)`, special case 1 (Z に適用) ⟹ `C_Y(Z) ⊆ O_{p'}(C_G(Z))`
⟹ `C_Y(Z) ⊆ O_{p'}(C_X(Z))` ⟹ **Prop 1.15(b)** (`oPiPrimeCore_centralizer_le_oPiPrimeCore`):
`C_Y(Z) ⊆ O_{p'}(X)`。`Y = C_Y(Z)·[Y,Z] ⊆ O_{p'}(X)`。

### general case (mmd L2299-2307): 任意 `X`
**Prop 1.16** (`cocyclicFixedByClosure_eq_top_of_not_isCyclic` or `exists_..` 系): `Y = ⟨C_Y(b) | b ∈ B^#⟩` (7.5)。
各 b: A normalizes C_Y(b); special 1/2 ⟹ `C_Y(b) ⊆ O_{p'}(C_G(b))`
⟹ `C_Y(b) ⊆ O_{p'}(C_X(b)) ⊆ O_{p'}(X)` (**Prop 1.15(b)**)。closure で `Y ⊆ O_{p'}(X)`。

## 要新規補題 (core claim 前に build)
1. **✅ `primesOf` = {p}** = `primesOf_eq_singleton` (done)。
2. **✅ normal p'-subgroup → opiCoreInG** = `le_opiCoreInG_of_normal_of_isPiSubgroup` (done)。
3. **Sylow-of-centralizer**: `b ∈ center P` (or `b ∈ Z(P_1)`) ⟹ `P ∈ Sylow p ↥(C_G(b))` (P ≤ C_G(b), index coprime p)。**型注意**: `Sylow p ↥(C_G(b))` は ↥(C_G(b)) 上, P を `.subgroupOf (C_G(b))` で持ち上げ。Thm 6.1 (`thmA4b`) が要求。
4. **bar-quotient bridge**: `(oPiPrimePiCore {p} X).map (mk' (oPiCore {p}ᶜ X)) = opCore p (X/O_{p'}(X))`
   (`oPiPrimePiCore` 定義 unfold + `map_comap` + `oPiCore_singleton_eq_opCore`)。
   `[Ā,Ȳ]⊆O_p(X̄)∩Ȳ` の commutator-in-quotient 計算も。
5. **🔴 relativized Prop 1.15(b)** (general case 律速・最大の型juggling): 絶対形
   `oPiPrimeCore_centralizer_le_oPiPrimeCore` は「群 G'」版。general case の `O_{p'}(C_X(b)) ≤ O_{p'}(X)`
   は **G' := ↥X** で適用 → 結論は ↥X 上の subgroup。これを ambient G の `opiCoreInG {p}ᶜ (C_X(b))`
   (C_X(b) = centralizer b ⊓ X) ↔ `opiCoreInG {p}ᶜ X` に翻訳する transport 補題が要 (↥X ≃ X 経由,
   `oPiCore`・`opiCoreInG` と `.subgroupOf X`/`.map X.subtype` の往復)。**~50-100 LOC, G/↥X/↥(C_X(b)) 三層**。
   special2 の `C_Y(Z) ⊆ O_{p'}(C_X(Z)) ⟹ O_{p'}(X)` も同型。
6. **B-construction** (E_p² in A normal in P) helper (cyclic/noncyclic Z(P) 2 分岐 + G 2.6.4)。

### general case の精密分解 (helper 3/5 + 確認済 lemma で組める, 2026-06-03 設計)
`Y ≤ X`, `A ≤ N_G(Y)`, `IsPiSubgroup {p}ᶜ Y`, B(E_p² ≤ A) 与え, special property
`hspec : ∀ b∈B^#, ∀ W≤C_G(b) A-inv p', W ≤ opiCoreInG {p}ᶜ (C_G(b))` を仮定:
1. Prop 1.16 (B↷Y 共役, coprime, noncyclic) で `Y = ⟨C_Y(b)|b∈B^#⟩`。
2. 各 b∈B^#: `C_Y(b):=Y⊓C_G(b)`。A-inv (A≤N_G(Y) ∧ A≤C_G(b) (b∈A abelian) ⟹ A≤N_G(C_Y(b)))。p' (≤Y)。
   `hspec` ⟹ `C_Y(b) ≤ opiCoreInG {p}ᶜ (C_G(b))`。
3. `opiCoreInG {p}ᶜ (C_G(b)) ⊴ C_G(b)` (oPiCore characteristic の像) ⟹ `(それ)⊓C_X(b) ⊴ C_X(b)` (N⊴H,K≤H)
   ⟹ **helper 2** で `≤ opiCoreInG {p}ᶜ (C_X(b))`。`C_Y(b) ≤ それ⊓C_X(b)` (C_Y(b)≤両方)。
4. **helper 5** (relativized 1.15b) で `opiCoreInG {p}ᶜ (C_X(b)) ≤ opiCoreInG {p}ᶜ X`。
5. closure (Prop 1.16 の sup) で `Y ≤ opiCoreInG {p}ᶜ X`。

## 確認済 lemma インベントリ (file:line, signature)
- `Hypothesis71` = ⟨ne_bot:A≠⊥, proper:A<⊤, generated_eq:∀X,A≤X→X<⊤→sSup(hInvariant X A (primesOf A)ᶜ)=opiCoreInG (primesOf A)ᶜ X⟩ (S07:119)
- `hInvariant H A π = {Q | Q≤H ∧ A≤N_G(Q) ∧ IsPiSubgroup π Q}` (`GroupTheory/AInvariantPiSubgroups.lean:41`); `mem_hInvariant` (:51)
- `IsSCN` = ⟨isNormal, isMulCommutative, selfCentralizing: C_G(A)=A⟩ (`GroupTheory/SCN.lean:75`);
  `IsSCN_n p n A = IsSCN A ∧ n ≤ pRank A p` (:221); `.isSCN`(:228) `.le_pRank`(:230)
- `thmA4b` (Thm 6.1): `[Finite G](hp_odd:p≠2)(hsolv:IsSolvable G)(hodd:Odd(card G))(P:Sylow p G){A}(hA_le:A≤↑P)(hA_norm:↑P≤N_G(A))[IsMulCommutative A] : A ≤ oPiPrimePiCore {p} G` (`BG/AppA_PStability.lean:1915`)
- `IsMinimalSimpleOdd`: `.odd`, `.simple`, `.notSolvable`, `.properSolvable`/`.solvable_of_lt_top M (hM:M<⊤):IsSolvable ↥M` (`BG/Ch2_Uniqueness/Setup.lean:47,68`)
- Odd 伝播: `hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)`
- Prop 1.10 `coprime_nilpotent_acts_trivially_of_centralizer_self {A G}[…][IsNilpotent G]{φ:A→*MulAut G}(hCop)(hCC:C_G(Fix φ)≤Fix φ):∀a g,(φ a)g=g` (S01:1777)
- Prop 1.15(a) `hall_higman_solvable_specialization [IsSolvable G](hp':oPiCore {q|q∉{p}} G=⊥):C_G(oPiCore{p}G)≤oPiCore{p}G` (S01:2297)
- Prop 1.15(b)特殊 `oPiPrimeCore_centralizer_eq_bot_of_oPiPrimeCore_eq_bot` (S01:2438); 一般 `oPiPrimeCore_centralizer_le_oPiPrimeCore` (S01:2483)
- Prop 1.16: `cocyclicFixedByClosure_eq_top_of_not_isCyclic (φ)(hCop)(hNC:¬IsCyclic A):cocyclicFixedByClosure φ=⊤` (S01b_Prop116:138);
  S07 specialization `exists_cocyclic_inf_centralizer_ne_bot_of_not_isCyclic` (S07:700)
- G 2.6.4 `IsPGroup.normal_inf_center_nontrivial (hP:IsPGroup p P){N}[N.Normal](hN:Nontrivial N):Nontrivial ↥(N⊓center P)` (Isaacs/Ch01_Sylow/Main:355)
- Ω: `Omega (p n) := closure {g|g^(p^n)=1}` (`GroupTheory/OmegaSubgroup.lean:55`); `omega1OfAbelian` (:185)
- ElementaryAbelian `IsElementaryAbelian` (type:41 / Subgroup:514); `of_card_prime_sq_of_not_isCyclic` (:84)
- pRank `pRank (p) := ⨆ A elem-ab, log p (card A)` (`GroupTheory/PRank.lean:373`);
  `exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (0<n)(n≤pRank G p):∃A elem-ab,n≤log p(card A)` (:446)
- `oPiPrimePiCore π G = comap (mk'(oPiCore πᶜ G)) (oPiCore π (G/oPiCore πᶜ G))` (Ch03:2812);
  `oPiCore_quotient_self_eq_bot` (Ch03:1793); `oPiCore_singleton_eq_opCore` (Ch04)
- 還元補題 `generated_eq_of_forall_le_opiCoreInG (hAX:A≤X)(hY:∀Y∈hInvariant X A π,Y≤opiCoreInG π X):sSup(hInvariant X A π)=opiCoreInG π X` (S07, このセッション)

## 罠メモ
- bar-quotient は §4 (AppA/S04e/S04g) の商引き戻しパターン流用。`O_p(X̄)` の identification が最 fiddly。
- `Subgroup.IsPiGroup` / `.subgroupOf` / `.le_oPiCore` は **`OddOrder.Isaacs.Ch03` namespace 配下** (full-qualify)。
- 変数名に結合マクロン `X̄` 等 (U+0304) 不可 → `Xbar` 等にリネーム (brick 2b 実測)。
- core claim は special1 → special2 → general の 3 段。special1 を `private` 補題に切り出し special2/general から呼ぶのが楽
  (special2 は special1 を Z に, general は special1/2 を b に適用)。incremental skeleton 推奨 (sorry で型通し→1 個ずつ)。
