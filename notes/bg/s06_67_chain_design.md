# BG §6→§7 close-out 設計ノート (2026-06-04)

goal: §7 を 100% sorry-free にする。鎖 = **Lem 6.5(c) → Lem 6.6 → Cor 1.12 → E*(S) char → Thm 6.7 → §7 Prop 7.5 case1**。
全 build-green・axiom-clean・AxiomsCheck 登録が完了条件。

すべての deep 外部定理は形式化済 (Isaacs Thm 4.36, BG Prop 1.10, Prop 1.15(a), hall_C)。残りは
**組み立て + 数本の self-contained 新補題**。mathlib に genuinely-missing な深い定理は無い。

## ⚠️ 重大訂正: E*_p(G) は「包含で極大」(max-by-inclusion)

BG mmd L352 定義: `E*_p(G)` = **maximal** elementary abelian p-subgroups (包含で極大、
max-**order** ではない)。repo の `Subgroup.maxElemAbelianIn P p` は max-**order** で **別物**。

- handoff note の「E*_p = maxElemAbelianIn ⊤ p 流用」は**誤り**。新述語が要る:
  ```lean
  def IsMaximalElementaryAbelian (p : ℕ) (E : Subgroup G) : Prop :=
    E.IsElementaryAbelian p ∧ ∀ F : Subgroup G, E ≤ F → F.IsElementaryAbelian p → F = E
  ```
- 局所性: `E max-by-incl in G ∧ E ≤ S ⟹ E max-by-incl in S` (∵ S 内 larger は G 内 larger)。
- **Prop 7.5 case1 接続の鍵**: `A = {x∈C_G(A)|x^p=1} = Ω₁(C_G(A))` ⟹ A は任意 X⊇A で
  包含極大 elem ab。証明: A<F elem ab, x∈F\A は order p, F abelian ⟹ x∈C_X(A)≤C_G(A),
  x^p=1 ⟹ x∈A 矛盾。**max-order 版ではこの含意は成り立たない** → max-by-incl 必須。

## 規約 (Lem 6.5(c), 検証済)

- `H.comap (MulAut.conj g).toMonoidHom = g⁻¹Hg` (集合 `{y | g*y*g⁻¹ ∈ H}`)。`hg : g⁻¹Hg ≤ U`。
- engine `exists_conj_eq_of_isHall_subgroupOf` の出力 `MulAut.conj w • H = wHw⁻¹` (pointwise)。
- BG `H^g := g⁻¹Hg` (= comap)。

## Lem 6.6 (4 parts) — mmd L2090-2103

`M := O_{p'}(G) = oPiCore {q|q≠p} G`, `U := N_G(S)`, `O_{p',p}(G) = oPiPrimePiCore {p} G`。
`hasPLengthOne p G := ¬ p ∣ card (G ⧸ oPiPrimePiCore {p} G)` (G/O_{p',p} が p'-群)。

**foundation (1)**: p-length one ⟹ `S ≤ O_{p',p}(G)` (S は p-群, 商 G/O_{p',p} は p'-群 ⟹ S の像自明);
`S` は `O_{p',p}(G)` の Sylow p (S∈Syl_p(G)⊇O_{p',p}); `O_{p',p}(G) = M·S` (O_{p',p}/M = O_p(G/M)
は p-群 ⟹ = M·Sylow); Frattini `Sylow.normalizer_sup_eq_top` (S Sylow of O_{p',p}⊴G) ⟹
`G = O_{p',p}·U = MSU = MU` (S≤U)。結論: `G = M ⊔ U` (= O_{p'}·N_G(S)) ∧ `O_{p',p} = M⊔S`。

- (2): Lem 6.5(a) を H=S, K=M, U=N_G(S) で。S⊆G' ⟹ S=S∩G'=S∩U'⊆U'=(N_G(S))'。
- (3): Y:Set G nonempty ⊆S, Y^x⊆S. Lem 6.5(c) を K=M, H=closure Y で。`closure Y`^x⊆S≤U;
  c∈C_M(closure Y)⊆C_G(Y), g∈U=N_G(S), x=cg。comap 規約: `(closure Y).comap(conj x)≤U`。
- (4): Q p-subgroup ⟹ Q≤O_{p',p}=MS (商 p'); S Sylow of MS; Sylow 共役で ∃x∈M,y∈S, Q^{xy}⊆S
  ⟹ Q^x⊆S (y∈S 正規化); z∈Q∩S: z^x z⁻¹∈S∩M=1 (x∈M) ⟹ x∈C_G(Q∩S)。

mathlib: `Sylow.normalizer_sup_eq_top [N.Normal] (P≤N) : N_G(P)⊔N=⊤`, `Sylow.subtype`,
`Sylow.exists_comap_subtype_eq`, `oPiCore_quotient_self_eq_bot`, `oPiCore_compl_le_oPiPrimePiCore`。

## Cor 1.12 (NEW) — derive from Thm 4.36 + Prop 1.10. mmd L457-459

statement: p odd, G p-群, E elem ab ≤G, A p'-operators (φ:A→*MulAut G),
A が C_G(E) の全 order-p 元を fix ⟹ A は G 上自明 (∀a g, φ a g = g)。

proof: C:=C_G(A)=`fixedPointsOfMulAut φ`. (i) E⊆C (e∈E は order|p かつ ∈C_G(E) ⟹ fix);
(ii) C_G(C)⊆C_G(E); (iii) A は C_G(C) の order-p 元 fix (⊆C_G(E)); (iv) **Thm 4.36**
(`isaacs_thm_4_36`, p odd) を A↷C_G(C) (p-群, A-invariant) restrict で ⟹ A trivial on C_G(C)
⟹ C_G(C)⊆C; (v) **Prop 1.10** (`coprime_nilpotent_acts_trivially_of_centralizer_self`,
G nilpotent ∵ p-群) で C_G(C)≤C ⟹ A trivial on G。
plumbing: `restrictAction` (S01 内, Prop 1.10 証明で使用例), `IsAInvariant.normalizer`/centralizer。

interfaces (全確認済):
- `isaacs_thm_4_36 (hp_odd:p≠2) (φ:A→*MulAut G) (hG:IsPGroup p G) (hA_p':¬p∣card A)
   (h_fix:∀g,g^p=1→∀a,φ a g=g) : actionCommutator φ = ⊥` (Ch04:4161)
- `coprime_nilpotent_acts_trivially_of_centralizer_self [IsNilpotent G] (hCop) 
   (hCC: centralizer (fixedPointsOfMulAut φ) ≤ fixedPointsOfMulAut φ) : ∀a g, φ a g = g` (S01:1770)
- bridge: `actionCommutator_eq_bot_iff_acts_trivially φ : actionCommutator φ = ⊥ ↔ ∀a g, φ a g = g` (Ch04:2184)
- `restrictAction (hH:IsAInvariant φ H) : A →* MulAut ↥H` + `restrictAction_apply` (S01:1750); `IsAInvariant`
- `fixedPointsOfMulAut φ` (Mathlib/Subgroup.lean:149) + `mem_fixedPointsOfMulAut`
- conj plumbing: `S.normalizerMonoidHom.comp (Subgroup.inclusion hL_le_norm) : ↥L →* MulAut ↥S`
- p-群⟹nilpotent: `IsPGroup.isNilpotent`; G p-群 ⟹ G nilpotent (Cor 1.12 の Prop 1.10 適用に必要)

**Thm 6.7 で要る conjugation 形**: L,S≤G, S p-群(p odd), E≤S elem ab, L p'-subgroup,
L≤N_G(S) (conj 作用), L が C_S(E) の order-p 元中心化 ⟹ L が S 中心化 (⁅L,S⁆=1)。
= 上記 MulAut Cor 1.12 を φ=(↥L→*MulAut↥S, conj) で instantiate。conj-action plumbing 要
(L↷S, S は ↥L-MulAut; 既存例: S01 `mem_centralizer_opCore_of_mem_oPiPrimeCore_centralizer`
が ⟨u⟩↷RT を setup、参照)。

## E*(S) char (NEW): E max-by-incl elem ab in S ⟹ E = Ω₁(C_S(E))

⊇: E≤C_S(E) (E abelian), E exp p ⟹ E⊆{g|g^p=1} ⟹ E≤Ω₁(C_S(E))。
⊆: gen g∈C_S(E), g^p=1, g∉E ⟹ ⟨E,g⟩=E⊔⟨g⟩ elem ab (E exp p, g order p, g∈C_S(E) ⟹ abelian,
exp p), ≤S, E<⟨E,g⟩ ⟹ max-by-incl 矛盾 ⟹ g∈E。closure⊆E (E subgroup)。
Ω₁ = `OddOrder.GroupTheory.Omega p 1 ↥(C_S(E))` 形 (要 OmegaSubgroup API 確認; ambient
subgroup 版の往復に注意)。Thm 6.7 では「C_S(E) の order-p 元は E 内」だけ使う (Ω₁ 等式の ⊆ 方向)。

## Thm 6.7 組み立て — mmd L2105-2127

K=O_{p'}(G), S Sylow⊇E. **reduction mod K**: G/K で O_{p'}=1 (`oPiCore_quotient_self_eq_bot`),
EK/K∈E*_p(G/K), LK/K p', p-length one 保存 ⟹ G/K で示せば L⊆K。assume K=1。
Lem 6.6(1) ⟹ O_{p',p}=S ⟹ S⊴G。L↷S (S⊴G), [L,E]⊆L∩S=1 (E≤S, L p'∩S=1 via coprime) ⟹
L 中心化 E ⟹ (Cor 1.12 conj 形 + E=Ω₁(C_S(E))) L 中心化 S。Prop 1.15(a)
(`hall_higman_solvable_specialization`, O_{p'}=⊥) ⟹ L⊆C_G(S)⊆O_p(G)=O_{p',p}=S。L p'∩S ⟹ L=1。
(K=1 で O_{p',p}=O_p; `opCore_le_oPiPrimePiCore` / 逆。)

## §7 Prop 7.5 case1 — S07:~3503 sorry. mmd L2261

case1 仮定: `A=Ω₁(C_G(A))` ∧ 全真部分群 p-length one。Hyp 7.1(2): A≤X<⊤ ⟹
⟨ℋ_X(A;p')⟩=O_{p'}(X)。各 Y∈ℋ_X(A;p') に **Thm 6.7** (G→X solvable, E→A∈E*_p(X)
[A=Ω₁⟹max-by-incl], L→Y p' normalized by A, X p-length one) ⟹ Y⊆O_{p'}(X)。
generated = O_{p'}(X) は `generated_eq_of_forall_le_opiCoreInG` 系 (S07 既存 helper) で。

## 進め方

逐次 build-green (同一 main tree)。重い証明 (6.5c[進行中], 6.6, Cor1.12, Thm6.7) は
fresh-context subagent に詳細プラン付き委譲 → 独立監査 (#print axioms=[propext,choice,
Quot.sound], statement 不変, no new sorry/axiom, AxiomsCheck)。S06 同時編集回避 (逐次)。

## conjugation-action plumbing (Cor 1.12 conj 形 + Thm 6.7 で必須)

先例 = S01 `mem_centralizer_opCore_of_mem_oPiPrimeCore_centralizer` (L2350 付近):
```lean
-- L ≤ normalizer S のとき L↷S の MulAut 作用:
set φ : ↥L →* MulAut ↥S := S.normalizerMonoidHom.comp (Subgroup.inclusion hL_le_norm) with hφ
-- φ a g の coe: ((φ a) g : G) = (a:G) * (g:G) * (a:G)⁻¹  (rfl で出る; hφcoe パターン)
```
`Subgroup.fixedPointsOfMulAut φ` = C_S(L) (の subgroupOf 形)。`IsAInvariant`, `restrictAction`
は S01 §1D / Prop1.10 証明に既存例。

## Thm 6.7 statement (intrinsic, 群 G について) — Phase D が群 ↥X に適用

```lean
theorem ... [Finite G] [IsSolvable G] {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    {E : Subgroup G} (hE : IsMaximalElementaryAbelian p E)
    {L : Subgroup G} (hLp' : ¬ p ∣ Nat.card L) (hEL : E ≤ Subgroup.normalizer L)
    (hpl1 : Ch1.hasPLengthOne p G) :
    L ≤ Ch03.oPiCore {q | q ≠ p} G
```
- L hypothesis は `IsPiSubgroup {p}ᶜ L` 形でも可 (Phase D の ℋ と直結) — どちらか実装時決定。
- 結論 `oPiCore {q|q≠p} G` = O_{p'}(G)。

**Phase D ambient/intrinsic 翻訳** (S07 case1, X<⊤ proper):
Thm 6.7 を群 `↥X` に適用。A, Y (≤X, ≤G) を `A.subgroupOf X`, `Y.subgroupOf X` に翻訳;
`IsMaximalElementaryAbelian p (A.subgroupOf X)` ← A=Ω₁(C_G(A)) で各 F:↥X 翻訳; `↥X` solvable
= `hG.solvable_of_lt_top X hXlt`; `↥X` p-length one = case1 仮説; 結論
`Y.subgroupOf X ≤ oPiCore {q≠p} ↥X` を `.map X.subtype` で `Y ≤ opiCoreInG {p}ᶜ X` に戻す
(`opiCoreInG π X := (oPiCore π ↥X).map X.subtype`; `Y = (Y.subgroupOf X).map X.subtype` ∵ Y≤X)。
この翻訳層が Phase D の主作業。`generated_eq_of_forall_le_opiCoreInG hAX` で
generated_eq に落とす (case2 `hypothesis71_of_scn2` と同パターン, S07:~3511)。
ℋ membership: `Q∈hInvariant X A π' ↔ Q≤X ∧ A≤N(Q) ∧ IsPiSubgroup π' Q` (π'=(primesOf A)ᶜ;
A p-群 ⟹ primesOf A={p} via `primesOf_eq_singleton hAp hAne`)。

case1 A≠⊥: A=Ω₁(C_G(A)), A=⊥⟹C_G(A)=⊤⟹{x|x^p=1}=⊥⟹p∤|G|, hp_mem(p∣|G|)+Cauchy 矛盾。
case1 A<⊤: A p-群, A=⊤⟹G p-群 nilpotent solvable, hG.notSolvable 矛盾。

## Thm 6.7 実装分割 (確定プラン, 最重)

S06 に `import OddOrder.GroupTheory.NarrowPGroup` (IsMaximalElementaryAbelian) +
`import OddOrder.BG.Ch1_Preliminary.S01_Solvable` (Cor 1.12 + Prop 1.15(a)) 追加。

**(B1) reduced-case lemma** `thm67_reduced` (O_{p'}=⊥ case, 数学的核心):
仮定 `hK : oPiCore {q∉{p}} G = ⊥`, hpl1, `hE : IsMaximalElementaryAbelian p E`,
`hLp' : ¬p∣|L|`, `hEL : E ≤ normalizer L` ⟹ `L = ⊥`。
- S:Sylow p G, E≤S (`IsPGroup.exists_le_sylow` 系)。
- 6.6 foundation + hK ⟹ `oPiPrimePiCore {p} G = S` ⟹ S⊴G (oPiPrimePiCore.normal)。
- `S = oPiCore {p} G`: S≤O_p (`IsPiGroup.le_oPiCore`, S normal {p}-群); O_p≤O_{p',p}=S
  (補題 `oPiCore {p} G ≤ oPiPrimePiCore {p} G`: O_p image≤O_p(G/M), pull back; or opCore 経由)。
- `⁅L,E⁆ ≤ L⊓S = ⊥`: ⁅L,E⁆≤L (E≤N(L), `commutator_le_left`系/⁅E,L⁆≤L); ⁅L,E⁆≤S (E≤S⊴G);
  L⊓S=⊥ (L p', S p-群)。⟹ L,E 各元可換 (L 中心化 E)。
- E*(S) char: hE ⟹ E max-incl in S (E≤S) ⟹ ∀ x∈C_S(E), x^p=1 → x∈E
  (`IsMaximalElementaryAbelian.le_of_le_centralizer` を F=⟨x⟩ で)。
- **Cor 1.12 conj 適用**: φ := `S.normalizerMonoidHom.comp (inclusion (L≤N(S)=⊤))` : ↥L→*MulAut↥S;
  `corollary_1_12 hp_odd (IsPGroup p ↥S = S.isPGroup') (¬p∣|↥L|) φ (E.subgroupOf S elem ab)
   (h_fix: C_{↥S}(E.subgroupOf S) の order-p 元は E 内 ⟹ L 固定)` ⟹ ∀l∈L,s∈S, lsl⁻¹=s
   (L 中心化 S, i.e. L≤C_G(S))。plumbing 先例 = S01 `mem_centralizer_opCore_of_mem_oPiPrimeCore_centralizer` (~L2350)。
- Prop 1.15(a) `hall_higman_solvable_specialization hK : centralizer(oPiCore {p} G)≤oPiCore {p} G`。
  S=oPiCore {p} ⟹ L≤C_G(S)≤S。L p'∩S p-群 ⟹ L≤L⊓S=⊥。`L=⊥`。

**(B2) reduction + Thm 6.7** `thm67` (一般形): 結論 `L ≤ oPiCore {q∉{p}} G` (=O_{p'}(G))。
K:=oPiCore {q∉{p}} G, q:=mk' K。
- `oPiCore {q∉{p}} (G/K) = ⊥` (`oPiCore_quotient_self_eq_bot`)。
- **Ē=E.map q ∈ IsMaximalElementaryAbelian p (G/K)** (lift, ~50 行): Ē elem ab (E∩K=1, ≅E);
  max-incl: F̄⊇Ē elem ab, lift F̄=F/K (K≤F), P_F:Syl_p F ⊇E, P_F K=F (P_F surjects F/K),
  ⁅P_F,P_F⁆≤K∩P_F=1 ∧ P_F^p≤K∩P_F=1 ⟹ P_F elem ab ≤G, E≤P_F, hE max-incl ⟹ P_F=E ⟹ F̄=Ē。
- L̄=L.map q, ¬p∣|L̄| (image of p'); Ē≤normalizer L̄ (image normalizes image)。
- **hasPLengthOne(G/K)**: `oPiPrimePiCore {p} G = comap q (oPiCore {p}(G/K))` (定義, K=M) ⟹
  `(oPiPrimePiCore {p} G).map q = oPiCore {p}(G/K)` (map∘comap, q surj); O_{p',p}(G/K)=O_p(G/K)
  (∵O_{p'}(G/K)=⊥) = O_{p',p}(G)/K; 第三同型 `quotientQuotientEquivQuotient`:
  (G/K)/(O_{p',p}(G)/K) ≅ G/O_{p',p}(G) ⟹ card 一致, hpl1(G) ⟹ hasPLengthOne(G/K)。
- `thm67_reduced` @G/K ⟹ L̄=L.map q=⊥ ⟹ L≤q.ker=K。∎

**E*_p の述語**: `OddOrder.GroupTheory.IsMaximalElementaryAbelian p E`
(= E.IsElementaryAbelian p ∧ ∀F elem ab, E≤F→F=E)。`.le_of_le_centralizer`,`.eq_of_le` helper 既存。

## E*(S) char (membership 形, Ω₁ 回避)

```lean
-- IsMaximalElementaryAbelian p E, x ∈ C_S(E) [≤ centralizer (E:Set)], x^p=1 ⟹ x ∈ E
-- pf: ⟨x⟩ elem ab; E ⊔ ⟨x⟩ elem ab (IsElementaryAbelian.sup_of_le_centralizer, ⟨x⟩≤C(E));
--     E ≤ E⊔⟨x⟩, max-by-incl ⟹ E⊔⟨x⟩=E ⟹ x∈E.
```
`IsElementaryAbelian.sup_of_le_centralizer` (ElementaryAbelian.lean:535): H,K elem ab,
K≤centralizer H ⟹ H⊔K elem ab。Thm 6.7 では C_S(E) の order-p 元 ∈ E だけ要る (Cor 1.12 入力)。
