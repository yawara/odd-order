# BG Lem 4.13/4.14 → Thm 4.16 の最終ゲート: Gorenstein Thm 4.15 chain ロードマップ

> 2026-05-31 作成。`bg-prove` workflow (#9 Lem4.13) の **BLOCKED_DESIGN** (run wf_aa5d5280-3ff,
> 357k tokens, 4 agent) が暴いた precursor tree を永続化。**§4 Thm 4.16 (Blackburn apex) の唯一残ゲート**。
> cold-start でこのノートから着手可能。
>
> ## ✅✅ 状態更新 (2026-05-31): precursor(1) も precursor(2) も完成
> - **precursor(1)** `pRank_le_two_of_scn3_empty` ✅ (commit c1d23e8, S04d) = G Thm 4.15(i)。
> - **precursor(2)** `exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction` ✅ (commit 4caebe5, S04e)
>   = minimal ψ-inv ⇒ special exp p (Thm 3.7+3.8 経由、**full Thm 3.10 帰納は回避** — minimal special D で
>   minimality が ψ-trivial-on-D′ を供給。下記 tree の「precursor(2) …【大】」「G Thm 3.10」は不要に)。
> ⇒ **Lem 4.13 = 残るは G Thm 4.15(ii) の assembly のみ** (precursor1+2 + GL数論)。
> G Thm 4.15(ii) proof = `finite-groups.mmd` L4225-4231: D=precursor(2) の minimal special exp-p Q、
> (a) D abelian ⇒ elem ab, ψ∈GL(≤2,p) order q ⇒ q∣p²-1; (b) D nonabelian ⇒ |D|=p³ extraspecial,
> ψ on D/Φ(D)=elem ab rank2 ⇒ 同様。
>
> ## ✅✅ 数論層 完成 (2026-05-31, commits 9c34e48 + 2795e0c)
> - `prime_dvd_prime_sq_sub_one_of_orderOf_mulAut`@PRank: E elem ab |E|≤p², σ:MulAut E prime
>   order q≠p ⇒ q∣p²-1。
> - `lt_of_prime_dvd_prime_sq_sub_one`@PRank: p,q prime, p odd, q≠p, q∣p²-1 ⇒ q<p。
> 両者で G Thm 4.15(ii) の数論結論 (q∣p²-1 ∧ q<p) を rank≤2 elem ab 作用から供給。sorry-free。
> **⇒ 残る Lem 4.13 ピースは構造論 (extraspecial reduction) + 配線のみ** (数論は完了)。
>
> ## 🔁 残る Lem 4.13 ピース (2 個):
> **(I) abelian 分岐**: D=precursor(2) Q が abelian ⇒ special abelian = elem ab。d(D)≤2
> (precursor(1) 由来, D≤P) ⇒ |D|≤p²。ψ (order q, =q∣|Aut R| を Cauchy で実体化) を D に作用、
> GL kernel ⇒ q∣p²-1。**容易** (GL kernel 直適用 + |D|≤p² の rank 翻訳)。
> **(II) nonabelian 分岐 = extraspecial reduction (構造論, 本体)**: nonabelian special D + pRank(D)≤2 (=d≤2)
> ⇒ |D|=p³。Gorenstein 初等論法 (L4229, structure theorem 不要):
>   1. m(Z(D))=1 ⇒ |Z(D)|=p ⇒ D extraspecial。 (m(Z)≥2 なら x∉Z + rank2 central で rank3 elem ab、
>      pRank≤2 矛盾)。
>   2. E := Z₂(D) 内の |E:Z(D)|=p subgroup (Z₂(D)/Z(D)=Z(D/Z(D))≠1, nilpotent)。E◁D, |E|=p²,
>      E elem ab rank2 (exp p)。
>   3. C_D(E)=E: C⊋E なら y∈C∖E で ⟨E,y⟩ abelian exp p rank3、pRank≤2 矛盾。
>   4. D/E=D/C_D(E) ↪ MulAut(E) faithful, p-群 ⇒ **既存 `card_pSubgroup_mulAut_le_prime_of_card_le_prime_sq`**
>      @PRank で |D/E|≤p。⇒ |D|=|E||D/E|≤p³。nonabelian⇒|D|≥p³。∴|D|=p³。⇒ D/Φ(D)=D/D' elem ab rank2、
>      ψ 作用、GL kernel ⇒ q∣p²-1。
> **規模**: (II) ~120-180行 (Z₂存在 / rank3 構成 / D/E↪MulAut(E) 共役同変埋込 / Sylux bound 既存)。
> **配線**: + q<p の数論 (q∣p²-1 ∧ q≠p ∧ p odd ⇒ q<p, ~15行 ℕ lemma) + SCN₃=∅⟺pRank≤2 (precursor(1)) +
> q∣|Aut R| を ψ order q に (Cauchy)。→ Lem 4.13 完成 → Lem 4.14 (q∣½(p±1)) → Thm 4.16 apex。

## 発見 (設計note の誤りを訂正)

`notes/bg/s04_prop411_thm416_design.md` の「**Lem 4.13 gate = GL橋 (I-0d) のみ**」は **誤り**。
BG Lem 4.13 = **Gorenstein Thm 4.15(ii)** で, その証明は **Thm 4.15(i) を消費**する。
Thm 4.15(i) = **BG Lem 4.7 の hard (⇒) 方向 = SCN₃(R)=∅ ⇒ pRank(R)≤2** で, repo は **easy ⇐ のみ**
(`scn3_empty_of_pRank_le_two`@S04:1076)。repo docstring @S04:1060 も "hard converse … deferred" と明記。

## 依存ツリー (BG Lem 4.13/4.14 → Thm 4.16)

```
Thm 4.16 (Blackburn apex)
 └─ BG Lem 4.13/4.14  (q∣|Aut R|, q≠p, SCN₃=∅ ⇒ q∣p²-1 ∧ q<p; 4.14: q∣½(p±1))   ← mmd L1624-1628
     ├─ precursor(1) pRank_le_two_of_scn3_empty  (SCN₃=∅ ⇒ pRank≤2 = G Thm4.15(i))  【§5/§7/§10 共有ゲート】
     │   ├─ G Thm 4.15(i)  (d_n(P)≤2 ⇒ d(P)≤2, p odd)                        ← G mmd L4219-4227
     │   │   ├─ G Lemma 4.14  (A max ab normal, m(A)=d_n(P) ⇒ Ω₁(C_P(Ω₁(A)))=Ω₁(A))  ← G L4203-4215 【大・engine】
     │   │   │   ├─ G Lem 4.12  (⟨x,y⟩ noncyclic ⇒ ⟨y,y^x⟩⊊⟨x,y⟩)            ← G L4185 【新規・小】
     │   │   │   ├─ G Lem 4.13  (stab(G⊇H⊇1, H ab) ⇒ [φ,ψ] が G 上自明 ⇒ A abelian) ← G L4195 【新規・小】
     │   │   │   ├─ G Lem 3.9(i)  (cl≤2, p odd ⇒ Ω₁ exp p)  ✅ `Omega.exponent_eq_of_class_le_two`
     │   │   │   ├─ G Lem 3.12  (M max ab normal ⇒ C_P(M)=M) ✅≈ `isSCN_iff_isMaximalAbelianNormal`@SCN:169 (⟸)
     │   │   │   └─ G Lem 1.3.4  (G/Z cyclic ⇒ G abelian)   ✅ `commutative_of_cyclic_center_quotient` (mathlib)
     │   │   └─ GL橋 (E_{p³} 排除, |E/E₁|≤p)  ✅ `IsElementaryAbelian.mulAutEquivGeneralLinearGroup`@PRank:188
     │   └─ SCN₃=∅ ⟺ d_n≤2 翻訳  ✅≈ isSCN_iff_isMaximalAbelianNormal (max ab normal=IsSCN, rank で SCN₃)
     ├─ precursor(2) isSpecial_expP_of_minimal_pprime_action  (minimal ψ-inv ⇒ special exp p = G Thm3.7+3.10) 【大】
     │   ├─ G Thm 3.7   (ψ-inv 部分群の構造)            ← G mmd L3847
     │   ├─ G Thm 3.10  (p odd, ψ p'-aut が Ω₁(P) 上自明 ⇒ ψ=1)  ← G L3897
     │   │   依存: Maschke ✅(Thm1.20), three-subgroups lemma, Burnside Thm1.4
     │   └─ ⚠ `thompson_critical_omega`@S01:845 は **別物** (G 5.3.9/5.3.10 characteristic critical, NOT minimal-ψ-inv)
     └─ GL橋 + card_mulAut  ✅ (q∣p(p²-1)(p-1), q≠p で p 因子除去 ⇒ q∣p²-1)
```

⚠ **番号注意**: BG は 1st-ed 番号 "**G** 5.4.15" を引くが, `references/gorenstein/finite-groups.mmd` は 2nd-ed
番号で **"Theorem 4.15"** (L4219-4231)。`grep 5.4.15` は forward-ref しか当たらない → 内容捏造リスク。
本体 = L4221-4230, engine の Lemma 4.14 = L4203-4215。

## 実装順 (推奨, 下層から)

1. **G Lem 4.12** + **G Lem 4.13** (新規小, Lemma 4.14 の前提) — bundle 可。4.12=Frattini/Burnside basis (`Corollary 1.2`=G/Φ cyclic⇒cyclic, repo に `frattini` 系あり), 4.13=[φ,ψ] 自明の純計算 (AppA stability は coprime⇒trivial で別物, ここは abelian 結論の commutator 計算)。
2. **G Lemma 4.14** `omega1_centralizer_omega1_eq_omega1` (大, engine)。証明 = G L4203-4215 の B_i-chain 帰納 (B_1=⟨Ω₁(A),x⟩ ◁ ⟨A,x⟩ を class≤2 経由) + D=Ω₁(C_P(Ω₁(A))) exp p の minimal-counterexample (Lem4.12/4.13/3.9(i)/3.12) + Ω₁(A)=D の rank squeeze (Lem1.3.4 + d_n 最大性)。
3. **G Thm 4.15(i)** (d_n≤2 ⇒ d≤2): Lemma 4.14 + GL橋で E_{p³} 排除。
4. **precursor(1)** `pRank_le_two_of_scn3_empty` (SCN₃=∅ ⇒ pRank≤2): 4.15(i) + SCN₃⟺d_n。**§5 Lem5.1(a)/5.1(b)/Thm5.3/Cor5.4 も一斉に開く** (s05_design_2026_05_30.md L33/L360-370/L448)。**独立 leaf 推奨** (S04d でなく §5 共有)。
5. **precursor(2)** `isSpecial_expP_of_minimal_pprime_action` (G Thm 3.7+3.10)。
6. **BG Lem 4.13** `dvd_prime_sq_sub_one_and_lt_of_scn3_empty` + **Lem 4.14** (bundle, 純算術) — precursor 1,2 で genuine assembly に。
7. **Thm 4.16 (Blackburn)** apex。

## 目標署名 (#9 設計 synth より, faithful)

```lean
-- precursor(1) — §5共有ゲート, 独立 leaf
theorem pRank_le_two_of_scn3_empty {R} [Group R] [Finite R] {p} [Fact p.Prime]
    (hp : Odd p) (hpg : IsPGroup p R) (hSCN : ∀ A : Subgroup R, ¬ IsSCN₃ p A) :
    pRank R p ≤ 2

-- BG Lem 4.13 (= G Thm 4.15(ii))
theorem dvd_prime_sq_sub_one_and_lt_of_scn3_empty {R} [Group R] [Finite R] {p q}
    (hp : Odd p) (hpp : p.Prime) (hpg : IsPGroup p R)
    (hSCN : ∀ A : Subgroup R, ¬ IsSCN₃ p A)
    (hq : q.Prime) (hqp : q ≠ p) (hqdvd : q ∣ Nat.card (MulAut R)) :
    q ∣ (p ^ 2 - 1) ∧ q < p
-- Lem 4.14: 上の結論を feed (fresh 仮説 hoist 禁止), q odd ⇒ q∣(p+1)/2 ∨ q∣(p-1)/2
```

## anti-scaffold (設計 7 trap, 厳守)

- **TRAP 1 (主)**: `(hSCN : ∀A,¬IsSCN₃)` を `(hrank : pRank≤2)` に **置換しない** — それが G4.15(i) の hoist。
  Thm4.16 caller は SCN₃=∅ を持つ (mmd L1640 "Clearly SCN₃(R) is empty"), pRank≤2 は持たない。
  `¬∃E_{p³}` / teeth 付き ¬IsSCN₃ / Omega-finrank 言い換え も同じ hoist。
- **TRAP 2**: order-q reduction を `(E, |E|=p², ψ:MulAut E, orderOf ψ=q)` 仮説に積まない (minimal-special-D 構成が payload)。ψ は `q∣Nat.card (MulAut R)` 経由でのみ登場。
- **TRAP 3**: descent instance を Classical.choice/sorry で埋めない。ψ∈MulAut R order q (Cauchy) → char D → D/Φ(D) → GL橋 を explicit 構成 (template = S7A2_NormalPThm75.lean:276-340 が sorry-free 実例)。
- **TRAP 4**: 結論 `q∣(p²-1) ∧ q<p` を弱めない (q<p は Lem4.14 の ½(p±1) split から genuine, `q∣p+1` 手抜き不可)。
- **TRAP 6**: `IsSCN₃` verbatim 使用, `pRank≤2` alias 定義で二方向を defeq 崩壊させない。

## 参照パス

- BG: `references/bg/local-analysis.mmd` L1624-1628 (Lem4.13/4.14), L1636+ (Thm4.16)
- Gorenstein: `references/gorenstein/finite-groups.mmd` — Thm4.15 L4219-4231, Lemma4.14 L4203-4215,
  Lem4.12 L4185, Lem4.13 L4195, Lem3.9 L3878, Thm3.10 L3897, Thm3.7 L3847, Lem3.12 L3921
- repo present: `Omega.exponent_eq_of_class_le_two` / `commutative_of_cyclic_center_quotient` /
  `isSCN_iff_isMaximalAbelianNormal`@SCN:169 / `IsElementaryAbelian.mulAutEquivGeneralLinearGroup`@PRank:188 +
  `card_mulAut`@:206 / `autCentralizer.eq_bot_of_not_dvd_card`@CriticalSubgroup:1224 (Burnside, Φ形 要追加かも) /
  GL descent template `mulAutGLTwoEquivOfIsElementaryAbelianCard`@S7A2:94 + `gl2_pSubgroup_card_le_prime`@S7A1:313
- §5 共有: `notes/bg/s05_design_2026_05_30.md` L33/L360-370/L448
- 設計note 訂正対象: `notes/bg/s04_prop411_thm416_design.md` (「gate=GL橋のみ」)
- 完全な blocker = #9 run wf_aa5d5280-3ff の design 出力 (skeleton STEP0-3b + 7 traps + ready_lemmas)
