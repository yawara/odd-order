# Bender–Glauberman Lemma 13.8 — GAP 3 (steps 5–6, 最終矛盾) の展開

> ChatGPT (Pro, odd-order project, thread "F lane") の回答 (思考 11m1s) を Lane F が厳密検証したもの。
> 検証日 2026-06-14。**結論: (3a)/(3b)/(3c) すべて健全・完全**。Lean kernel 2 本の埋め方が確定。
> GAP 1+2 は `bg-lemma-13-8-elided-steps.md`。

記号: `H := N_M(Q)`, `K := H ∩ M_α`, `D := M_α ∩ M*`, `X := C_{M_α}(P)`。

---

## (3a) ∃ R ≤ N_M(Q), |R|=r, [R,P]=1  ← Lean kernel `gap3_centralizer_…` の前半

**Step 1 (商 H/K ≅ M/M_α).** `M_α ⊴ M` ⟹ `K = H∩M_α ⊴ H`。`P ≤ H` ゆえ P は H に共役作用、
K は P-不変。`M = H·M_α` ⟹ 第二同型 `H/K ≅ M/M_α` (P-equivariant、P≤H・M_α⊴M)。

**Step 2 (coprimeness).** `p∈τ₁(M) ⟹ p∉σ(M) ⟹ p∉α(M)`、M_α は α(M)-群 ⟹ `p∤|K|` (K≤M_α)。
同様に `r∉σ(M) ⟹ r∉α(M) ⟹ r∤|K|`。

**Step 3 (r-part が商で生存).** `π:M→M/M_α`。`r∣|C_M(P)|`, `r∤|M_α|` ⟹ `r∣|π(C_M(P))|`
(kernel = C_M(P)∩M_α ≤ M_α は r と互素)。`π(C_M(P)) ≤ C_{M/M_α}(P)`、同型移送で
`r ∣ |C_{H/K}(P)|`。

**Step 4 (coprime-action centralizer COVER).** 標準補題:
> A が有限群 H に作用, `K⊴H` A-不変, `(|A|,|K|)=1` ⟹ `C_{H/K}(A) = C_H(A)·K/K`。

A=P, H=N_M(Q), K=H∩M_α で適用 (仮定: K⊴H, P-不変, (|P|,|K|)=1)。⟹ `C_{H/K}(P)=C_H(P)K/K`。
`r∣|C_{H/K}(P)| = [C_H(P):C_H(P)∩K]`、`C_H(P)∩K≤K` で `r∤|K|` ⟹ `r∣|C_H(P)|`。
**🔑 repo handle = `Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal`** (Cor 3.28;
A-fixed coset が C_H(A) の元へ lift = cover の片側、逆は自明)。これは事前に特定済の私のプラン通り。

**Step 5 (Cauchy).** `r∣|C_H(P)|` ⟹ ∃R≤C_H(P), |R|=r。R≤N_M(Q), [R,P]=1。∎

## (3b) X = C_{M_α}(P) ⊆ M*  ← Lean kernel `gap3_centralizer_…` の後半

**Step 1.** R≤N_M(Q)≤N_G(Q)≤M* (hNQ)。
**Step 2.** r∈β(M*), |R|=r ⟹ R 非自明 β(M*)-部分群; [R,P]=1 ⟹ R≤C_{M*}(P)。Prop 10.14(d) を M* に
(Y=R) ⟹ `N_G(R)≤M*`。
**Step 3.** PR≤M, [P,R]=1 ⟹ PR 可換。p∉σ(M), r∉σ(M) ⟹ **PR は σ(M)'-部分群**。
**Step 4 (Hall 共役で E へ).** `M = M_σ⋊E` (E = Hall σ(M)'-補群)。M 可解ゆえ Hall の定理:
任意の σ(M)'-部分群は E の M-共役に含まれる ⟹ ∃m∈M, `(PR)^m ≤ E`。
`P^m∈ℰ_p¹(E)`, `R^m∈ℰ_r¹(C_E(P^m))` ([P^m,R^m]=1)。
**Step 5 (Thm 13.4).** `centralizer_le_centralizer_of_tau1` を P^m,R^m に ⟹
`C_{M_σ}(P^m)≤C_{M_σ}(R^m)`。M_σ⊴M で m⁻¹ 共役戻し ⟹ `C_{M_σ}(P)≤C_{M_σ}(R)`
(C_{M_σ}(P^m)=C_{M_σ}(P)^m 等、M_σ^m=M_σ より)。
**Step 6 (鎖).** `X=C_{M_α}(P)≤C_{M_σ}(P)≤C_{M_σ}(R)≤C_G(R)≤N_G(R)≤M*`。X≤M_α ⟹ `X ⊆ M_α∩M*`。∎

## (3c) ⁅M_α∩M*, Q⁆ ⊆ M*_α  ← Lean kernel `gap3_commutator_inf_le_Malpha_star`

> **私が最も不安だった step。ChatGPT が `L:=[D,Q]` を経由する refinement で綺麗に解決。**
> 私の当初の素朴な「D̄ が q'、Q̄ が q」では D⊄M*' ゆえ直接 D̄ が取れない問題を、L=[D,Q] が回避。

**Step 1.** D=M_α∩M*≤M_α、M_α は α(M)-群、`q∉α(M)` ⟹ `q∤|D|` (D は q'-群)。
**Step 2.** Q≤M normalizes M_α (⊴M)、Q≤M* normalizes M* ⟹ Q normalizes `D=M_α∩M*` (Q-不変)。
**Step 3.** D Q-不変 ⟹ `[D,Q]≤D`。`L:=[D,Q]` は q'-群。
**Step 4.** Q≤M*' (head: Q=[Q,P]⊆M'∩M*')、D≤M*、M*'⊴M* ⟹ ∀d∈D,u∈Q: [d,u]=(d⁻¹u⁻¹d)u∈M*'
⟹ `L=[D,Q]≤M*'`。∴ L≤D, L≤M*', L は q'-群。
**Step 5 (nilpotent で q'⊥q).** Thm 10.2 を M* に: `M*'/M*_α nilpotent`。bar = mod M*_α。
`L̄≤M*'/M*_α` は q'-部分群、`Q̄≤M*'/M*_α` は q-部分群 (Q≤M*')。**有限 nilpotent 群では相異なる
Sylow 因子は可換** ⟹ q-部分群と q'-部分群は可換 ⟹ `[L̄,Q̄]=1` ⟹ `[L,Q]≤M*_α`。
**Step 6 (coprime commutator 恒等式 — 🔑 punchline).** Q は q-群、D は q'-群、作用は coprime。
標準恒等式 **`[D,Q,Q]=[D,Q]`** (coprime action; BG Prop 1.6(b))。L=[D,Q] ⟹
`L = [D,Q] = [D,Q,Q] = [L,Q] ≤ M*_α` (Step 5)。∴ `[D,Q]=L⊆M*_α`。∎

## 最終矛盾 (assembly = repo `gap3_assembly` 既済)

X⊆D=M_α∩M* (3b) ⟹ [X,Q]⊆[D,Q]⊆M*_α (3c)。X≤M_α, Q≤M, M_α⊴M ⟹ [X,Q]⊆M_α。
∴ [X,Q]⊆M_α∩M*_α=1 (Lem 10.12)。⟹ [X,Q]=1, X⊆C_M(Q); X=C_{M_α}(P)⊆C_M(P) ⟹
X⊆C_{M_α}(PQ)=1 (Lem 12.18)。X=C_{M_α}(P)≠1 と矛盾。∎

---

## Lean 形式化 handle (検証で確定)

| 数学的事実 | repo/mathlib handle | 備考 |
|---|---|---|
| coprime quotient cover (3a-4) | `Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal` | inner-action φ=conj∘P.subtype, IsAInvariant 設定要 (S03c_Thm37 が例) |
| 第二同型 H/K≅M/M_α (3a-1) | `QuotientGroup.quotientInfEquivProdNormalQuotient` 等 | or 直接 element 経由 (y=h·a) で iso 回避可 |
| Cauchy (3a-5) | `exists_prime_orderOf_dvd_card` / `Cauchy` | r∣|C_H(P)| |
| Hall σ'-subgroup へ共役 (3b-4) | `Ch03.hall_D` (∃H Hall ⊇ U) + `hall_C` (共役) | PR を Hall σ' へ → E へ。SubgroupESetup の E に合わせ込む |
| Thm 13.4 (3b-5) | `S13.centralizer_le_centralizer_of_tau1` | P^m,R^m∈E 要 |
| 中心化子の共役移送 (3b-5) | `C_N(P^m)=C_N(P)^m` (N⊴, m∈M) | 手書き or `Subgroup.centralizer` conj lemma |
| [D,Q]≤D (D Q-不変) (3c-3) | `Subgroup.commutator_le` + normalizer | |
| nilpotent で q⊥q' 可換 (3c-5) | ✅ **`S10.commute_of_coprime_orderOf_of_isNilpotent`** (S10_LocalLemmasCore:679) | element-level (位数互素 ⟹ commute)。⁅L̄,Q̄⁆=⊥ は element-wise。**使用例 = S12_Lemma1218:349/970** (同パターン: nilpotent 商で coprime 像が可換) を mirror |
| coprime commutator [D,Q,Q]=[D,Q] (3c-6) | ✅ **`OperatorQuotientAction.commutator_commutator_right_eq`** (:308; BG Prop 1.6(b)) | ⚠ `H.Normal` (ambient) 要 ⟹ **ambient を DQ にして H=D⊴DQ で適用**し G へ移送 (commutator は intrinsic) |

### ✅✅ (3c) 完全形式化済 (2026-06-14, commit b3dcd9c1)
2 reusable helper + kernel すべて sorry-free・full build 緑:
- `commutator_commutator_right_eq_of_le_normalizer` (Q-invariant coprime 恒等式; ambient D⊔Q)。
- `commutator_le_Malpha_of_coprime_le_derived` (nilpotent 商で ⁅A,B⁆≤M*_α; A,B≤M*' coprime)。
- `gap3_commutator_inf_le_Malpha_star` (iv 本体)。
知見: element commutator `⁅,⁆` は `open scoped commutatorElement` 必須; `orderOf_mk`=`Subgroup.orderOf_mk`;
quotient には `haveI : N.Normal := S10.Malpha_subgroupOf_normal Mstar` が要 (Group instance synthesis)。
**残り 13.8 = (3a)+(3b) `gap3_centralizer_Malpha_P_le_Mstar` の 1 kernel のみ**。

✅ **全 handle 確定 — 13.8 は完全に formalize 可能**。
- (3a): `coprime_fixedPoints_quotient_of_coprime_normal` (事前プラン通り)。inner-action setup は S03c_Thm37 が例。
- (3b): `centralizer_le_centralizer_of_tau1` + `hall_D`/`hall_C` (PR→E 共役) + SubgroupESetup の E。
- (3c): `commute_of_coprime_orderOf_of_isNilpotent` (S12_Lemma1218 に使用例) + `commutator_commutator_right_eq` (ambient DQ)。

次イテレーション標的: 形式化を開始。難所 (3c) は handle が揃い使用例もある。
(3b) の SubgroupESetup の E への P,R 同時共役 (PR≤E) が最も組立工数大か。

### ✅✅✅ Lemma 13.8 COMPLETE (2026-06-14, Lane F)
GAP 3 (3a)/(3b)/(3c) 全形式化完了 ⟹ `forbidden_config_impossible` (Lemma 13.8 本体) +
`gap3_false_from_r` (assembly) すべて sorry-free・**axiom-clean** (`#print axioms` =
`[propext, Classical.choice, Quot.sound]` のみ; `forbidden_config_impossible` を
AxiomsCheck に登録)。full build 3807 jobs 緑。

- **(3a)** `exists_order_r_le_normalizer_centralizer` (commit `68d490b9`): coprime quotient cover
  で得た P-fixed 代表 `c∈C_{N_M(Q)}(P)` を商 `↥M ⧸ (M_β).subgroupOf M` で `c≡y (mod M_β)` ⟹
  `r∣orderOf c` (`orderOf_map_dvd` + `r∤|M_β|` で r-part 生存)、Cauchy で `R=⟨order-r power⟩`。
- **(3b)** `gap3_centralizer_Malpha_P_le_Mstar`: (3a) で `R` → Prop 10.14(d) で `N_G(R)⊆M*`
  → 新 helper **`centralizer_msigma_le_of_commute_tau1`** (= "Thm 13.4 の E 外への共役拡張")
  → chain `M_α⊓C(P)≤M_σ⊓C(P)≤M_σ⊓C(R)≤C(R)≤N_G(R)≤M*`。
- **共役拡張 helper の核**: `exists_conj_smul_le_hallPiece` (PR を Hall σ'-補群 E へ M-共役;
  π=σ(M)ᶜ, F=E, hF=`IsHallSubgroup σᶜ (E.subgroupOf E=⊤)` を `SubgroupESetup.isPiGroup_sigma_compl`
  から構成) → 共役対に `centralizer_le_centralizer_of_tau1` → `M_σ⊴M` の共役同変性
  (`centralizer_conj_smul` + `Subgroup.smul_inf` + `conj_smul_eq_self_of_mem_normalizer`) で戻す。
- **`isPiGroup_sup_of_le_centralizer`** (private): 可換 σ'-対 P,R の join も σ'-群
  (`↥(P⊔R)` 内で両者正規 ⟹ `IsPiGroup.sup_of_normal`)。p≠r 不要。
- 🔑 知見: `isPiGroup_sigma_compl` は `SubgroupESetup` namespace 内 (`SubgroupESetup.` 接頭辞要)。
  subtype 元 `⟨y,h⟩` の `orderOf_injective` は `.symm` 要 (goal LHS が subtype 側)。

⟹ **§13 下流 leaf の 13.7 + 13.8 完了**。残 = 13.9/13.10/13.11 (Lane G の 13.6 landing 待ち)。
