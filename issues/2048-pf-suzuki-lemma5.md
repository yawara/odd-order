---
id: 2048
slug: pf-suzuki-lemma5
title: "Peterfalvi I.3 Lemma 5: cyclic W and Suzuki type B"
created: 2026-07-18
---

# Peterfalvi I.3 Lemma 5: cyclic W and Suzuki type B

## 背景

Peterfalvi Part II, Ch. I §3 Lemma 5 (p. 107) の形式化。`|st| = 3`、
`Q` が位数 `q^3` (`q = |Q₀|`) の Suzuki 2-group であるとき、`W` が
巡回、`|W| ∣ q + 1`、さらに `W ≠ 1` なら `Q` が Appendix III
Definition 3 の type B であることを示す。

既存 `Suzuki2Groups.SuzukiTypeData.typeB` と `higman_classification` は
任意の `Prop` carrier を持つ scaffold であり、この補題には引用しない。原文が使う
Appendix III Theorem (d),(e) の `K`-module 分解・type-B 同値・有限体座標と、
2 次元有限体表現の結論を具体的データとして構成する。

## やること

- [x] `w ∈ W#` に対して §3 Proposition 1(c) と忠実性から
      `Q ∩ C_G(w) = Q₀` を証明する
- [x] Appendix III Lemma 1(b) の quadratic central extension を実体化する
- [x] Definition 3 の具体的 `TypeBData` を実体化する
- [ ] Peterfalvi Appendix III Theorem (d),(e) (Higman) の Lemma 5 用 payload を構成する
  - [x] `OrderQModuleSplit` / `IsomorphicOrderQModuleSplit` という結論データ型と、
        位数 `q²` の inverse-image API を定義する
  - [x] ambient `K` action の忠実性・固定点自由性、`Q₀`-不変性、actual actor の
        involution 上の正則性と `|K| = q - 1` を証明する
  - [x] quotient の固定点自由性から summand 上の推移性・単純性・
        distinct summands の complementarity を得る一般 bridge を証明する
  - [x] actual `K` action を `Q/Q₀` へ降ろし、固定点自由性と
        order-`q` invariant summand の推移性・単純性を証明する
  - [x] Higman p. 79 の easy direction: 有限 Suzuki `2`-groupの全 involution が
        中心に入り、involution と単位元からなる具体的 elementary-abelian
        `2`-subgroupを構成する
  - [x] Higman Lemma 1 (p. 83): 中心を homocyclic とし、actual `K`-不変部分群を
        Agemo 層として分類する。具体的 `Q₀` は最終非自明層であり、残る中心逆包含を
        `Agemo Z(Q) 2 1 = ⊥` と正確に同値化する
  - [x] Higman Lemma 2 (p. 83): 非自明 normal abelian `K`-subgroup `A` と
        `u ∉ A` に対する `u² ∈ A²` と `[u,A] ≤ A⁴` の同時成立を排除する
  - [x] Higman Lemma 3 (pp. 83--84): normal invariant subgroup `C` が `A` を
        cover し `Φ(C) = Φ(A)` なら `exp(A) ≤ 4` を証明する
    - [x] normal actor-invariant subgroup の subtype 上で honest な cover を定義し、
          `Φ(C) ≤ A` と原文 p. 83 の `Φ(C) = A ∨ Φ(C) = Φ(A)` を証明する
    - [x] `Φ(C) = Φ(A)` から `[C,A] ≤ A²`、`C² ≤ A²`、
          `[C,A²] ≤ A⁴` を ambient subgroup として証明する
    - [x] homocyclic `ZMod` 座標の基底上で平方値 endomorphism を半分にし、
          線形延長して `α ≡ 1 mod A²` から honest に `α = 1 - 2ν` を構成する
    - [x] 実際の共役自己同型を `α = 1 - 2ν` と `α² = 1` に接続し、
          `4(ν² - ν) = 0` を導く
    - [x] homocyclic `ZMod` 座標で `ν mod 2` の冪等性を証明し、有限可換
          idempotent 族の common `0`/`1` eigenvector と推移作用の一般帰結を証明する
    - [x] 実際の `A/A²` 上で `u ↦ ν̄(u)` を加法準同型として構成し、
          その像が pairwise commuting な冪等作用素族であることを証明する
    - [x] ambient `X`-作用から `ν̄` の共変性を導き、common-eigenvector 論と
          involution 推移性から各 `ν̄(u)` が `0` または `1` であることを証明する
    - [x] Lemma 2 により `ker ν̄ = A` を示す
    - [x] `0`/`1` dichotomy と第一同型定理から像の位数 `2`、
          従って `C/A` の位数 `2` を証明する
    - [x] 原文 p. 84 の二場合分けを接続し、
          `NormalInvariantCover.pow_four_eq_one_of_frattini_map_eq` として
          `∀ a : A, a ^ 4 = 1` を結論する
  - [x] Higman Lemmas 4--9 を形式化し、Lemma 12 冒頭で用いる
        maximal abelian subgroup の指数境界 `exp(A) ≤ 4` と `Φ(G) ≤ A` を構成する
    - [x] 原文の `Lᵢ = Hᵢ / (Hᵢ² Hᵢ₊₁)` を actual lower-central quotient として
          構成し、ambient denominator、elementary-abelian 性、標準 `F₂`-module、
          誘導作用・表現を `HigmanLowerCentralGraded` に実装する
    - [x] commutator から alternating・作用同変な `L₁ × L₁ → L₂` を構成し、
          その値が `L₂` を span することを証明する
      - [x] 二重の `QuotientGroup.lift` で代表元公式を持つ commutator pairing を構成する
      - [x] `ZMod 2`-双線形化と degree-2 alternating linearization を構成する
      - [x] commutator closure から pairing の値の span が `L₂` に等しいことを証明する
      - [x] 誘導自己同型作用に関する commutator pairing の equivariance を証明する
    - [x] 非零 `L₂` 上の推移性から source-facing な Higman Lemma 4 を証明する
      - [x] Singer finite field への base change と Frobenius eigenbasis
            `λ^(2^i)` を構成する
      - [x] bracket weights `λ^(2^i+2^j)` と full span を接続し、
            `L₁ ≃ L₂` から primitive-root contradiction を導く
      - [x] `not_exists_equivariant_linearEquiv_of_higman_bracket`
            (`17a033729`) として landing
    - [x] Lemma 4 直後の scalar-extension corollary: 任意の拡大体上で
          `L₁` と同型な `F₂`-linear invariant subspace が `L₂` に存在しないことを
          `not_exists_injective_intertwiner_to_baseChange_of_higman_bracket` として示す
    - [x] Higman Lemma 5: `H² = H₂` の下で平方写像 `L₁ → L₂` の
          scalar-extension 公式と一意性を構成する
      - [x] source仮定 `Agemo H 2 1 = H₂` を構成用包含へ接続し、代表元の平方を
            actual quotient map `L₁ → L₂` に降ろす
      - [x] quadratic add law、`QuadraticMap (ZMod 2)` bundle、polar = actual
            commutator bracket を証明する
      - [x] ambient automorphism作用に関する equivariance と、余域だけを拡大した
            `L₁ → K ⊗ L₂` の add law / equivariance を証明する
      - [x] ordered basis上の upper-triangular quadratic candidate、そのpolar、
            Frobenius-power座標の pairwise-exponent 公式を証明する
      - [x] Lemma 4 Corollaryから uniqueness principleを導き、actual
            `lowerCentralSquareMapBaseChange` に source-facing に instantiate する
      - [x] 一般の faithful irreducible cyclic `L₁` actionから、full Singer-orderを
            仮定せず normalized Frobenius-conjugate eigenbasisを構成する
            (`FrobeniusCoordinates.lean`, issue 9300)
      - [x] candidateの actor-equivarianceを証明してactual uniquenessを適用し、
            `exists_lowerCentralSquareMap_eq_frobeniusSum` として actual square mapの
            表示公式を結論する
    - [x] Higman Lemma 6: `H² = H₂` の下で `L₃` が `L₂` と
          `ξ`-同型でないことを actual lower-central layers 上で証明する
      - [x] §4 の actor を有限 2 群 `H` 上の faithful な奇数位数 cyclic
            automorphism group として明示し、`H² = H₂ = Φ(H)` と Burnside の
            operator theorem から `L₁` 作用の faithfulness を導出する
      - [x] 代表元 `[x,y]` から actual `L₂ × L₁ → L₃` を二重 quotient descent で
            構成し、`F₂`-双線形性、full span、ambient automorphism equivariance を証明する
      - [x] `L₁ × L₁ → L₂` と合成した actual triple commutator
            `[[x,y],z]` を三重線形化し、その値が `L₃` を span することを証明する
            (`HigmanLowerCentralDegreeThree.lean`)
      - [x] `L₂ ≃ξ L₃` から各 layer 上の actor kernel/order の一致と
            `finrank L₁ = finrank L₂` を原文 p. 85 の議論どおり導く
        - [x] actual mixed bracket の full span と `L₁` の既約性から
              `ker ρ₂ ∩ ker ρ₃ ≤ ker ρ₁` を証明する
        - [x] `L₂ ≃ξ L₃` と `L₁` 作用の忠実性から `L₂` 作用の忠実性を導く
              (`L₃` への移送は既存の equivariant-equivalence API)
        - [x] actor order と Singer field の Frobenius period を接続し、
              `finrank L₁ = finrank L₂` を仮定せず導く
      - [x] Neumann の位数 3 fixed-point-free automorphism theorem を形式化し、
            `finrank L₂` が奇数であることを導く
        - [x] `H² = H₂` から平方包含を `H₂,H₃` へ伝播し、各 layer の
              fixed-point-free 性を `H/H₄` へ直接降ろす
        - [x] 偶数次元なら faithful transitive Singer actor に位数 3 の元が存在する
              ことを Cauchy で示し、商作用の位数も 3 であることを証明する
        - [x] Neumann の class-two 結論と `L₃ ≠ 0` を矛盾させ、
              `lowerCentralLayerOne_finrank_odd_of_equivariant_linearEquiv` を得る
      - [x] pair/triple Frobenius weight の指数算術と
            `[u²,u] = 1` の actual square-map 接続から triple bracket を消去する
        - [x] 相異なる `i,j,k` の三項 weight は modulo `2^n-1` でどの pair
              weight とも一致しないことを示し、対応 eigenspace を `⊥` にする
        - [x] actual `[u^(2),u] = 0` を平方写像へ接続し、Lemma 5 の Frobenius
              basis 展開式を仮定する bridge から triple-bracket sum をゼロにする
        - [x] repeated weight が原典の二候補
              `[[u_i,u_{j-1}],u_{j-1}]`, `[[u_j,u_{i-1}],u_{i-1}]` に限ることを
              binary exponent 算術で示し、odd `n` では両方の inner pair が同時に
              permitted gap `±r` を持てないことを `ZMod n` 上で証明する
        - [x] actual `L₂` の Frobenius eigenbasis と bracket の full span を接続し、
              全ての非零 basis bracket が一つの cyclic gap `±r` に支えられることを示す
        - [x] actual triple-bracket の零和を固有値 fiber ごとに分離する
        - [x] distinct-index 項の消滅を仮定した各 pair-weight fiber を二つの
              repeated 候補へ縮約し、odd-gap 排他と零和から全項を消去する
        - [x] `L₃` の pair-weight eigenspace span を使い、distinct-index の actual
              triple-bracket 項をゼロにする
        - [x] 非零項の固有値を pair-weight range に戻して対応 fiber を適用し、
              actual basis triple-bracket の全項をゼロにする
      - [x] triple full span と `L₂ ≃ξ L₃` の非自明性を接続し、source-facing な
            Lemma 6 の否定定理を組み立てる
    - [x] Higman Lemma 7 (p. 86): `A = Φ(C)` かつ `C' ≤ A²` なら `C` は可換
      - [x] 平方写像 `c ↦ c²` を actual `L₁(C) → A/A²` に降ろし、全射性と
            actor-equivariance を証明する
      - [x] cover 既約性から平方写像を
            `lowerCentralLayerZeroToAgemoZeroLinearEquiv` に上げる
      - [x] actual `L₂(C)` を分類で得る successive Agemo factor へ同変同型し、
            非可換 `C` なら `L₂(C)` が非自明であることを証明する
      - [x] involution 推移性、actor の奇数位数・忠実性、Agemo power equivalence を
            `LemmaSevenSpectralCertificate.false` に接続する
      - [x] 同型仮定を内部構成した source-facing endpoint
            `higmanLemmaSeven_isMulCommutative` として landing (`01b037909`)
    - [x] Higman Lemma 8 (p. 87):
          `C' = A` なら `exp(A) ≤ 2`
      - [x] cover と `C' = A` から `C² = C'`
            (`Agemo C 2 1 = commutator C`) を証明する
      - [x] actual lower-central terms を `C₂ = A`, `C₃ = A²`, `C₄ = A⁴` と同定する
      - [x] actual `L₂ ≃ A/A²`, `L₃ ≃ A²/A⁴` と actor-equivariance を構成する
      - [x] `exp(A) > 2` のとき power map `L₂ ≃ξ L₃` を構成し、Lemma 6 と矛盾させる
            (`higmanLemmaEight_pow_two_eq_one`, `cd97f2d75`)
    - [x] Higman Lemma 9 (p. 87): Lemmas 3, 7, 8 の三分岐から maximal abelian normal
          invariant subgroup `A` に対する `exp(A) ≤ 4` と `Φ(G) ≤ A` を証明する
      - [x] `[P,A] ≤ A²` から shared Agemo commutator API で
            `[Φ(P),A] ≤ A⁴` を導き、`A ⊔ Φ(P)` 内の cover と Lemma 2 witness を構成する
      - [x] cover の Frattini subgroup を `A` と同定し、Lemma 7 branch を最大性で排除、
            Lemma 8 branch から `exp(A) ≤ 2` を得る
      - [x] `A = Z(P)` と nilpotency class `≤ 2` を実証明して `Φ(P) ≤ A` を閉じ、
            両結論を公開 endpoint `higmanLemmaNine` にまとめる (`844d2d5f1`)
  - [ ] Higman Lemmas 10--12 (pp. 87--92) の分類終端から
        `Agemo Z(Q) 2 1 = ⊥`、従って `Z(Q) = Q₀` を証明し、同時に
        actual two-summand split を構成する
    - [x] B/C/D model の中心 exponent 2 (`ModelCenters.lean`, `37b78e57b`):
          twisted product の mem_center_iff + polarization radical 自明性
          (B/C は初等、D は Dedekind 自己同型独立 3 項) + equivModel transport
    - [x] `center_sq_eq_one_of_xiLengthThree` (`08fb9d018`):
          分類と接続し ξ-length 3 で ∀ z ∈ Z(P), z² = 1
    - [x] `center_eq_frattini_of_xiLengthThree` / `agemo_center_eq_bot_of_
          xiLengthThree` (`e88893f9a`): Z(P) = Φ(P)、℧₁(Z(P)) = ⊥
    - [x] `exists_orderQModuleSplit_of_xiLengthThree`
          (新 leaf TwoSummandSplit.lean, `a51ff24ca`): P/Z(P) の
          two-summand split (OrderQModuleSplit) を factor 像で実構成
          (card は A(n,θ) model count、P/Z の EA 性込み)
    - [ ] 残り: Lemma 5 側で ξ-length-3 仮定 (IsXiActor + HasXiLengthThree)
          を IsSuzuki2Group + |Q| = q³ から供給する橋渡し
      - [x] 計数半分 (新 leaf XiLengthFromCard.lean, `f3cb7c6ce`):
            regular actor は fpf / |K| ∣ |T|−1 (自由軌道計数、
            card_dvd_of_no_nontrivial_fixed 使用) / 2^n−1∣2^k−1→n∣k /
            不変部分群位数は q 冪 / no_four_chain_of_card_eq_cube
      - [x] 3-chain 存在の field 側 core (`3f7d0caaa`):
            `le_of_adjoin_frobeniusFixed_eq_top` — Singer 生成元が
            Frob^n 固定なら次数 m ≤ n (X^{2^n}−X の根の個数制限)
      - [x] 既約 middle quotient の排除 (`d1d113b24`):
            `exists_proper_invariant_subgroup_of_card_sq` — EA 位数 (2^n)² +
            cyclic 位数 2^n−1 fpf → proper 非自明不変部分群存在 (sorry 0)
      - [x] 最終 assembly `hasXiLengthThree_of_card_eq_cube` (`9400087bd`):
            IsSuzuki2Group + |P| = q³ + cyclic regular actor (|K| = q−1) →
            HasXiLengthThree K.subtype (sorry 0)。**ξ-length-3 橋渡し完成** —
            higmanLemmaTwelve / center_eq_frattini / two-summand split の
            全 Higman payload が Lemma 5 設定から供給可能に
      - [-] (旧計画メモ; 完了済につき参照のみ)
            (i) 非自明不変正規部分群は involutionSubgroup を含む
            (2 群の正規部分群は中心と交わる + 位数 2 元 + K 推移性)、
            |involutionSubgroup| = q; (ii) P/Ω₁ (位数 q²) の
            proper 非自明不変正規部分群の存在: Z(P/Ω₁) proper なら採用;
            abelian なら ℧₁(P/Ω₁) proper 非自明なら採用; どちらも潰れると
            P/Ω₁ は faithful 既約 F₂[K]-module (fpf は coprime lifting
            quotient_fixedPointFree_of_fixedPoints_le で降ろす) →
            exists_galoisFieldLinearModel_of_faithful_irreducible
            (FrobeniusCoordinates.lean:747) + adjoin_generator_eq_top_of_
            irreducible_linearModel で F₂(λ) = 全体 → 次数 = ord_2(2^n−1) = n
            ≠ 2n 矛盾; (iii) preimage で chain ⊥ < Ω₁ < B < ⊤ を組み、
            HasXiLengthThree を結論; (iv) IsXiActor は Def 1 の K
            (cyclic + regular→transitive) から直接
    - [x] Higman Lemma 10: characteristic `2` の proper odd-degree
          finite field extensionで、任意の `r : ℤ`, `ε` に対する非零 `α` と
          `Tr(α · Frob^r(α) · ε) = 0` を構成する
      - [x] 原文冒頭の `gcd(1+2^r,2^m-1)` の奇偶二分法と power-map 全射 branch を証明する
      - [x] 標数 `2` の twisted quadratic map に対する Chevalley--Warning の
            source-neutral bridge を `OddOrder.Algebra` に構成する (issue 9308)
      - [x] 負の整数 Frobenius 反復も含む exact endpoint `higmanLemmaTen` を証明する
            (`42e744a4f`)
    - [x] Higman Lemma 11: `K`-length `2` の Suzuki `2`-group を
          原文の有限体座標群 `A(n, θ)` と同型にする
      - [x] 原典 p. 79 の actor 仮定を regular でなく cyclic-transitive として分離し、
            `P' = Φ(P) = Z(P) = Ω₁(P)` と lower-central length two を構成する
      - [x] actor の prime-supported reduction と、第一層体次数 `m` が第二層次数 `n` の
            odd multiple になる有限体 bridge を構成する (issues 9310--9311)
      - [x] 非忠実でもよい第二層作用を effective image 上で faithful にし、任意の共通
            splitting field `L` 上に `Fin n` の Singer--Frobenius eigenbasis を構成する
      - [x] common overfield の canonical 共役基底を構成し、ground-vector の exact
            Frobenius 展開、actor 対角化、scalar Frobenius による cyclic successor を
            同一基底上で証明する (issue 9314)
      - [x] `m` と `n` を同一視せず、非零 bracket が単一 gap `±r (mod m)` に
            支えられることを証明する
        - [x] `λ` は第一層体を生成するだけ、第二層固有値 `ν` は位数 `2^n-1` の
              primitive root という原文の unequal-degree 条件のまま、pair-weight equality
              から `±r (mod m)` を導く指数算術を証明する
              (`higmanLemmaEleven_pairGap_of_pairWeight_eq_frobeniusShift`)
        - [x] canonical common-field 共役基底上で actual bracket の非零係数を actor の
              pair-weight equality に接続し、全 nonzero bracket の `±r` support を得る
              (`lowerCentralPairGapSupport_of_commonConjugateBases`)
        - [x] bracket span から canonical 第一層 basis の非零 bracket と第二層 basis の
              非零座標を選び、actual pair-weight equality を得る
              (`exists_lowerCentralConjugateBasisBracketCoordinate`)
        - [x] 選んだ三つの Frobenius index を循環再添字化し、field model・generator・
              canonical basis を保ったまま `ι(ν) = λ^(1+2^r)`、非零 `(0,r,0)` seed、
              全 `±r` support を actual data から構成する
              (`exists_normalizedLowerCentralConjugateBasisBracketCoordinate`)
      - [x] gap-supported bracket を正規化し、Lemma 5 の平方和を
            `Tr[L/K](α^(1+2^r) ε)` に再添字化する
        - [x] normalized seed bracket が第二層 canonical basis の 0 番固有線上にあることを
              示し、`[b₀,b_r] = ε • v₀` (`ε ≠ 0`) を構成する
              (`exists_ne_zero_smul_secondConjugateBasis_zero_of_bracket`)
        - [x] alternating bracket から `r ≠ 0` を得て、primitive second-layer
              eigenvalue と odd extension degree から原典の `m ≠ 2r`
              (`r + r ≠ 0`) を証明する
              (`gap_ne_zero_of_alternating`,
              `twice_gap_ne_zero_of_odd_degree`)
        - [x] Frobenius orbit で全 cyclic edge の係数を復元し、upper-triangular sum を
              relative trace に畳み込む。normalized basis 版に加えて、Lemma 5 の元 basis
              上の任意 anchor `(a, a+r, s₀)` を直接消費する版も構成する
              (`square_frobeniusSum_eq_trace_of_normalized_singleGap`,
              `squareMap_eq_trace_of_normalized_singleGap`,
              `square_frobeniusSum_eq_trace_of_anchored_singleGap`)
      - [x] Lemma 10 と xi-length-two 構造から proper `L/K` を排除する。
            length-two 群の actual square map が非零入力上で非零であることを quotient
            kernel から証明し、anchored trace formula と結合して `finrank K L = 1`
            を得る
            (`lowerCentralSquareMapAdditive_ne_zero_of_xiLengthTwo`,
            `finrank_eq_one_of_anchoredTrace_lowerCentralSquareMap_of_xiLengthTwo`)
      - [x] actual central extension を平方写像で分類し、Peterfalvi の honest
            `TypeAData` へ接続する shared adapter を構成する (issue 9309)
      - [x] proper extension 排除から `m = n` を導き、degree-one algebra map と
            relative trace を同定して原典 p. 89 の “the trace is superfluous” を証明する
            (`absoluteDegrees_eq_of_relativeFinrank_eq_one`,
            `anchoredTraceFormula_trace_superfluous`)
      - [x] trace-free 平方写像を `a ↦ a * θ(a)` と lower-central extension 座標へ
            接続し、source-facing `higmanLemmaEleven` を組み立てる
        - [x] degree-one anchored trace 式の anchor を Frobenius 座標変更へ吸収し、
              `ε * (a * θ(a))` の actual lower-central square normal formを得る
              (`exists_lowerCentralCoordinates_typeANormalForm_of_anchoredTrace_finrankOne`)
        - [x] 二つの actual lower-central layer から kernel/quotient `MulEquiv` を構成し、
              `ε` を kernel 座標へ吸収して honest `TypeAData` を得る
              (`typeADataOfLowerCentralSquareNormalForm`)
        - [x] actor から得た元の Singer basis 上で actual anchored trace 式を構成し、
              上記 endgame と合成して source-facing theorem `higmanLemmaEleven` を閉じる
    - [ ] Higman Lemma 12 (pp. 89--92): ξ-length `3` の Suzuki `2`-group を
          `B(n, θ, ε)`, `C(n, ε)`, `D(n, θ, ε)` のいずれかに分類する
      - [x] ξ-length `3` を `HasXiLengthThree` (3 strict steps が存在し、4 steps は不存在)
            として normal actor-invariant poset 上に定義し、任意の 3-step chain が
            actual covers になることを導出する
      - [x] Lemma 9 と cover dichotomy / Lemmas 7--8 を接続し、公開 endpoint
            `frattini_isElementaryAbelian_of_xiLengthThree` で `Φ(P)` が elementary abelian
            であることを証明する
      - [x] `P / Φ(P)` の二つの ξ-composition steps を actual invariant summands に持ち上げ、
            ξ-length `2` の部分群 `X, Y` と `P = XY` を構成する
        - [x] `Φ(P)` を三段組成列の第一項と同定し、商の induced actor が
              `HasXiLengthTwo` を満たすことを証明する
        - [x] Maschke により商の complementary invariant summands を構成し、
              preimage が normal / invariant、`X ∩ Y = Φ(P)`、`X ⊔ Y = P` を証明する
        - [x] `Φ(P) < S < P` である各 preimage `S` の restricted actor range が
              `HasXiLengthTwo` を満たすことを証明する
      - [x] 可換な ξ-length-two summand `A(n,1) = C₄ⁿ` も含む honest data carrier を
            構成し、二つの summand を共通 parameter `n ≥ 2` の `A(n,θ)`,
            `A(n,φ)` と同定する
        - [x] `XiLengthTwoTypeAData` を構成し、非可換 branch は Lemma 11、
              可換 branch は homocyclic exponent-four 分類と actual
              `A/A² ≃ A²` square coordinates から `A(n,1)` へ接続する
        - [x] 任意の proper invariant preimage `S` を、可換性の分岐を残さず
              `IsXiLengthTwoTypeA S` と同定する
        - [x] complementary preimages `X, Y` の二つの model parameter が一致し、
              共通値が `2 ≤ n` を満たすことを証明する
      - [x] concrete `A(n,θ)` model の canonical square root を actor の
            involution 推移性で任意の `g ∈ Inv(P)` へ輸送し、左右いずれの
            invariant factor 内にも `x² = g` の解が存在することを証明する
      - [x] `X ∩ Y = Φ(P)` と `Φ(P)` の exponent two を用いて、`X`, `Y` が
            elementwise commute すれば `xy⁻¹` が `Φ(P)` 外の involution になる
            矛盾を導き、公開 endpoint
            `xiLengthThreeTypeAFactorData_exists_with_nontrivial_mixed_commutator`
            で actual `⁅x,y⁆ ≠ 1` witness を得る
      - [x] ambient group を class-two central extension と同定する
        - [x] involution transitivity と elementary-abelian `Φ(P)` から
              `[P,P] = Φ(P) ≤ Z(P)` を証明する
        - [x] `lowerCentralTerm P 1 = Φ(P)`, `lowerCentralTerm P 2 = ⊥` と
              `lowerCentralLayerKernel P 1 = ⊥` を証明する
        - [x] `Agemo P 2 1 = Φ(P)` を証明し、零次 lower-central layer を
              actual quotient `P / Φ(P)` と同定する
      - [x] 二つの type-A factor の group-level central-extension 座標を
            ambient `Φ(P)` に接続する
        - [x] concrete type-A model の short exact sequence を factor へ輸送し、
              quotient projection の核が `(Φ(P)).subgroupOf S` であることを証明する
        - [x] `Φ(P) ≤ X,Y` を使い、左右 kernel field を同一の ambient
              `Φ(P)` へ移す additive group equivalence とその transition を構成する
        - [x] noncommuting mixed-factor witness を、左右因子の provenance を保つ
              actual lower-central bilinear pairing の非零値へ接続する
        - [x] 左右 factor の座標より先に、ambient actor の実際の `Φ(P)` 制限作用を
              primitive scalar multiplication へ共役する共通 Singer 座標と Frobenius
              eigenbasis を構成し、その次数が factor parameter に等しいことを証明する
        - [x] 上記の共通 `Φ(P)` 座標を prescribed kernel coordinate として、左右各
              factor の quotient 座標を actor-compatible に構成し、
              `ν = λ·θ(λ) = μ·φ(μ)` を導く
          - [x] Lemma 11 の field model を caller-prescribed actor generator 版へ
                強化し、同じ ambient generator が invariant factor の faithful range
                でも generator のまま残ることを証明する
          - [x] noncommutative factor について `Φ(S) = Φ(P).subgroupOf S` を証明し、
                factor の第2 lower-central layer と ambient `Φ(P)` の canonical な
                `ZMod 2` 線形同値が restricted actor action と可換することを証明する
          - [x] commutative `A(n,1)` factor について square equivalence から
                prescribed ambient kernel coordinate に従属する quotient coordinate
                と actor compatibility を構成する
          - [x] odd-order `θ` に対する unit twisted norm
                `u ↦ u·θ(u)` の全単射性を証明し、任意の非零 kernel scaling を
                quotient-basis scaling で実現する
          - [x] normal-form の Frobenius renormalization を quotient coordinate 側へ
                counter-shift して prescribed kernel coordinate を固定し、square map の
                actor-equivariance から `ν = λ·θ(λ)` を導く一般補題を証明する
          - [x] `PairGap` normalization が第2層へ加える最初の Frobenius shift と
                original kernel coordinate との exact equality を strong sibling API で返す
          - [x] `ProperExtension` の anchored-trace construction が第2層へ加える次の
                Frobenius shift も同様に返し、上記 counter-shift 補題へ接続する
          - [x] 二つの shift を一つの Frobenius automorphism に合成し、type-A
                automorphism との可換性を証明して original kernel coordinate へ戻す
          - [x] relative degree 1 の anchored trace normal form を kernel field 側へ戻し、
                prescribed kernel coordinate を変えず quotient coordinate だけを構成する
          - [x] nonzero coefficient を twisted-norm surjectivity で quotient coordinate
                だけに吸収し、prescribed kernel coordinate のまま係数 1 にする
          - [x] shift 復元と係数 1 化を一つの公開 endpoint に束ね、quotient actor
                compatibility と `ν = λ·θ(λ)` を同時に保持する
          - [x] caller-prescribed generator 版 Lemma 11 の actual field model と二つの
                tracked shift を上記 endpoint へ接続し、noncommutative factor の
                quotient coordinate を共通 `Φ(P)` 座標から構成する
          - [x] 同じ ambient Singer datum を左右の非可換因子へ一度ずつ適用し、両方の
                quotient coordinate と `ν = λ·θ(λ) = μ·φ(μ)` を一つの endpoint で返す
          - [x] commutative `A(n,1)` と noncommutative factor の座標 data を共通の
                inclusive bundle に包み、実際の complementary pair の全組合せを返す
          - [x] actual mixed commutator pairing の actor covariance を左右の tagged
                coordinates で表示し、原典 p. 90 の固有値制約
                `λ^(2^i) μ^(2^j) = ν^(2^k)` を導いて B/C/D case split の直前まで到達する
                (`exists_mixedFrobeniusWeightEquation_of_xiLengthThree`,
                新 leaf `HigmanLemmaTwelve/MixedEigenweights.lean`, 2026-07-21)
            - [x] shared `BilinearEigenweight.lean`: 等変双線形写像の非零値から
                  target eigenbasis の weight 一致を導く (Lemma 11 の private 版 dedup、issue 9317)
            - [x] ambient `L₁ ≃ Φ(P)` 同定 + Singer 中心座標 + factor quotient を
                  `P/Φ(P)` へ落とす actor-equivariant な inclusion を構成
            - [x] 両 branch (Agemo 商 / lower-central layer) から共通 `F ⊗ P/Φ(P)` 内の
                  Frobenius eigenvector 族を抽出 (`exists_factorFamily`)
            - [x] 非零 mixed bracket を base change して weight equation を読み取る
          - [x] `θ = 1` / `φ = 1` / 両方非自明の固有値制約から原典 pp. 90--92 の
                B/C/D case split を実行し、`B(n,θ,ε)` / `C(n,ε)` / `D(n,θ,ε)` を確定する
                — **`higmanLemmaTwelve` 完成 (`fe298b348`, AxiomsCheck 登録
                `8e69a8a32`)**: IsTypeB ∨ IsTypeC ∨ IsTypeD、sorry 0・axiom-clean。
                4 case lemma = isTypeB_of_mixedTerm_theta_one (`d1e3da617`) /
                isTypeB_of_mixedTerm_theta_eq (`5d5e28e48`) /
                isTypeC_of_mixedTerm_right_theta_one (`9879a1fbe`) /
                isTypeD_of_mixedTerm_monomial (`ea85296bf`)、
                転置対称性 (`e783303bf`)、dispatch は flip 正規化 + factor swap
            - [x] piece 4 の純算術を完備化 (`TwoPowerCongruence.lean`): 冪和衝突の
                  完全記述 + multiset carry collapse + B case 消去 (`a≡b∧c≡a+1`,
                  `s≡±r`) + C case 一意性 (`2r+1=n ∧ s≡r+1 ∧ t≡1`) + D case
                  一意性 (partition 解析、survivor + mirror) + 固有値方程式からの
                  bridge 5 本 (pow_eq_pow_iff_modEq 経由、離散対数不要)
            - [x] support pinning 算術 (`SupportPinning.lean`, `0c5905902`):
                  ν=λ^{1+2^r} primitive から orderOf λ / coprime 回収、θ=φ の μ=λ、
                  B: (i,j)∈{(0,r),(r,0)} / C: 2r+1=n ∧ (n−1,r+1) / D: (3r,r)∨mirror
            - [x] flip 正規化 (`CaseDispatch.lean`, `f17e2b279`):
                  `NoncommutativeFactorCoordinateData.flip` (A(n,θ)≅A(n,θ⁻¹)、
                  ePhi 不動で θ↦θ⁻¹, λ↦θλ) + `exists_flip_frobenius_le_half`
                  (0<r≤n/2 の WLOG)
            - [x] M 単項化 (`CaseDispatch.lean`, `0e0a86396`): 二重和 collapse +
                  support 抽出 + case 別単項定理 — θ=φ=1: M=c₀αβ / θ=φ≠1:
                  M=c₁αβ^{2^r}+c₂α^{2^r}β / C: 2r+1=n ∧ M=c₀α^{2^{n−1}}β^{2^{r+1}} /
                  D: (s≡2r∧5r≡0∧M=c₀α^{2^{3r}}β^{2^r})∨mirror
            - [x] B case の shear 正規化 (`exists_typeB_shear_normalization`,
                  `65b4efd8f`): (α,β)↦(α+c₂tβ,tβ) で θ(α)β 単項消去、
                  1+c₁c₂≠0 と生存係数≠0 は anisotropy から、奇数位数 twisted norm
                  で再スケール、IsTypeBEpsilon まで返す
            - [x] group-side assembly の hL/hR 供給: packaged inclusion の
                  actor-eigenvalue 法則 3 定理
                  (`FactorCoordinateData.toInclusionData_incl_representation` ほか、
                  `ba9ac88da`)
            - [x] ε 正規化 (`241971692`): B は shear 補題が IsTypeBEpsilon まで
                  返す; C/D は `isTypeC/DEpsilon_of_decomposed_aniso` で
                  decomposed anisotropy + monomial から IsType*Epsilon
                  (monomial 指数 ↔ θ 冪の Frobenius 同定込み)
            - [x] group-side assembly: 実際の mixed 項
                  (ambientCenterCoordinate ∘ lowerCentralCommutatorBilinear) を
                  mixedTerm_lambda_equivariance で equivariance に接続 → 上記単項化
                  → engine (isTypeB/C/D_of_mixedTerm) の hM → higmanLemmaTwelve
                  (完了 — 上記 case split 項に詳細)
              - [x] `mixedTermBilinear` bundle + `_lambda_equivariance` +
                    `FactorInclusionData.exists_incl_eq` (`1b4f0c413`,
                    CaseSplitBCD.lean 末尾; 同 file は 1380 行 — 以後の追記禁止)
              - [x] `shearRescaleLinearEquiv` (α,β)↦(α+ρβ,tβ) +
                    座標 parametrized engine `isTypeB_of_squareCoordinate`
                    (`356819071`; B case θ=φ≠1 は sheared 座標
                    `(shearRescale…).trans e` で進入、
                    `ambientProductExtension_hsq_of_coordinate` は e 一般で既に OK、
                    `ambientProductExtension_inl_range = frattini P` も e 非依存)
              - [x] 新 leaf `HigmanLemmaTwelve/Assembly.lean` (hub 配線済) +
                    `exists_mixedTermBilinear_ne_zero` (`2e05ad8e5`)
              - [x] case dispatch 本体 (Assembly.lean, `fe298b348` で完了):
                    exists_mixedFrobeniusWeightEquation_of_xiLenghThree の状態
                    (factors/c/ePhi/ν primitive/left/right FactorCoordinateData/
                    ν=λθλ=μφμ) から θL/θR の Frobenius 冪
                    (exists_frobenius_pow_eq_of_ringAut) で 4 分岐:
                    (i) θ=φ=1: λ=μ は char2 平方単射、hord は
                    orderOf_eq_and_coprime_of_pow_eq_orderOf、
                    mixedTerm_monomial_of_theta_one → isTypeB_of_mixedTerm
                    (phi:=1, IsTypeBEpsilon は decomposed anisotropy 直接);
                    (ii) θ=φ≠1: μ=λ は eq_of_pow_eq_pow_orderOf、
                    mixedTerm_two_monomials_of_theta_eq →
                    exists_typeB_shear_normalization →
                    isTypeB_of_squareCoordinate (hq は ambientProductSquare_eq
                    + shear 結論);
                    (iii) 片方 =1: 必要なら因子 swap (commutator 反対称 char2)、
                    noncomm 側 flip で 0<r≤n/2、mixedTerm_monomial_typeC
                    (2r+1=n が出力) → isTypeCEpsilon_of_decomposed_aniso →
                    isTypeC_of_mixedTerm (theta_two_sq は Frob^{1+2r}=Frob^n=1);
                    (iv) 両方 ≠1 かつ θ≠φ: mixedTerm_monomial_typeD
                    (survivor/mirror は swap) → isTypeDEpsilon_of_decomposed_aniso
                    → isTypeD_of_mixedTerm (θ^5=1 は 5r≡0, φ=θ² は s≡2r)。
                    hcentral は commutator_eq_frattini_and_frattini_le_center_
                    of_xiLengthThree + inl_range。anisotropy 入力は
                    ambientProductSquare_decomposed_ne_zero (hinv は
                    involutions_subset_of_nontrivial_invariant 経由)
  - [x] Higman payload 一括供給 `center_payload_of_card_eq_cube`
        (`f2165d373`): IsSuzuki2Group + cyclic regular actor + |P| = q³ →
        Z(P) = Φ(P) ∧ 中心 exponent 2 ∧ OrderQModuleSplit。
        Lemma 5 側は actualKActor (ActualKActor.lean:117, cyclic instance +
        actsRegularly 済) + card_K_eq_card_Q0_sub_one で instantiate 可能
  - [ ] summands が同型 iff type B を証明し、type-B 有限体座標を
        actual `Q/Q₀`, `K` action に接続する
    - **設計 (2026-07-21 確定)**: Lemma 5 の消費は ⟸ 方向
      (IsomorphicOrderQModuleSplit → IsTypeB) が critical path。
      経路 = higmanLemmaTwelve の分類 + C/D 排除:
      - **Lemma U (split 一意性)**: P/Z が非同型既約 2 成分 U₁ ≇ U₂ の
        半単純分解を持つとき、任意の complementary invariant order-q 対は
        {U₁, U₂} に一致 (第 3 の既約部分加群は Schur 射影で U₁ ≅ U₂ を強制)。
        Maschke は OperatorMaschke.lean の bridge 流用。
      - [x] **Lemma I 完了** (SummandIsomorphism.lean):
        exists_frobenius_conjugate_of_semiconj +
        _of_equivariant_linearEquiv (μ = λ^{2^i})
      - **Lemma I (module iso → eigenvalue Frobenius 共役)** (設計原文): 2 つの faithful
        既約 F₂[K]-module 間の K-equivariant 同型は Singer 固有値の
        μ = λ^{2^j} を強制 (exists_galoisFieldLinearModel + 生成元 orderOf、
        既存 equivariant-linearEquiv 系 (HigmanLemmaSix 587 等) 参照)。
      - **Lemma NI (C/D の非同型)**: pre-case-split state の (λ, μ, ν) で
        C case: λ^{1+2^r} = ν = μ² と μ = λ^{2^j} → 1 + 2^r ≡ 2^{j+1}
        (mod 2^n−1) → TwoPowerCongruence の subset-sum 衝突分析で r = 0 矛盾;
        D case: 1 + 2^r ≡ 2^j + 2^{j+2r} → 5r ≡ 0・r ≢ 0 と衝突。
      - **⟸ 組み立て**: split V₁ ≅ V₂ 所与; rcases 分類; C/D なら
        Lemma U で {V₁,V₂} = 正準 factor 像、Lemma I+NI で矛盾 → B。
      - **⟹ (優先度低; Lemma 5 は不使用)**: TypeBModel の F×0 / 0×F summand
        + swap 同値。actor 側の座標同一視 ((e) 後半) は別項。
      - 注意: OrderQModuleSplit の actor は K.subtype (Suzuki actor)、
        Z = center P。分類側 factor との突き合わせは
        exists_complementaryFactorCoordinates_of_xiLengthThree の
        factors.left/right 像 (TwoSummandSplit の構成) を経由。
- [x] invariant `Q₀`-coset の coprime fixed-point lifting から
      自由作用と位数整除を得る一般補題を証明する
- [ ] `K`-不変な位数 `q²` 部分群 `X` と `X^w ≠ X` を証明する
- [ ] `W` の projective-line 上の自由作用から `|W| ∣ q+1` を証明する
- [ ] 一般有限体上の 2 次元表現 API から `W` の巡回性を証明する
  - [x] projective FPF から cyclicity と `|E| ∣ |F| + 1` を得る一般定理を証明する
- [ ] type-B 結論を含む Lemma 5 の最終定理を組み立てる

## 完了条件

- `W` の巡回性、位数の割り切り、`W ≠ 1 → TypeBData Q` を一つの
  source-facing theorem として証明する
- 新規 `sorry` / `axiom` / opaque-Prop carrier を導入しない
- 変更した leaf が build-green。`OddOrder` / `OddOrder.AxiomsCheck` の統合 gate は
  main / hub 側で実行する

## 参照

- `references/peterfalvi/pdftotext/05.3_pp_100_107_General_Properties_of_G.txt`
- `references/peterfalvi/pdf/05.3_pp_100_107_General_Properties_of_G.pdf`
- `references/peterfalvi/pdftotext/08.0_pp_139_143_On_Suzuki_2-Groups.txt`
- `references/peterfalvi/pdf/08.0_pp_139_143_On_Suzuki_2-Groups.pdf`
- `references/higman/suzuki-2-groups.pdftotext.txt`
- `references/higman/p83_84_lemmas_1_3.layout.txt`
- `references/higman/p84_85_lemmas_3_6.layout.txt`
- `references/higman/p85_lemmas_4_6.raw.txt`
- `references/higman/pages/suzuki-2-groups-p085.png`
- `references/higman/p86_87_lemmas_6_10.layout.txt`
- `references/higman/p86_87_lemmas_6_10.raw.txt`
- `references/higman/p88_92_lemmas_10_12.layout.txt`
- `references/higman/p88_92_lemmas_10_12.raw.txt`
- `references/higman/pages/suzuki-2-groups-p086.png`
- `references/higman/pages/suzuki-2-groups-p087.png`
- `references/higman/pages/suzuki-2-groups-p088.png`
- `references/higman/pages/suzuki-2-groups-p089.png`
- `references/higman/pages/suzuki-2-groups-p090.png`
- `references/higman/pages/suzuki-2-groups-p091.png`
- `references/higman/pages/suzuki-2-groups-p092.png`
- `references/higman/suzuki-2-groups.pdf`
- `references/higman/SOURCE.md`
- `OddOrder/Higman/Suzuki2Groups/HigmanSquareMap.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanTripleBracketContradiction.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanLowerCentralGraded.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanCoverAbelian.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanCoverPowerOverlap.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanFiniteFieldTrace.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanLemmaTwelve/LengthThreeReduction.lean`
- `OddOrder/Algebra/ChevalleyWarning.lean`
- `OddOrder/Peterfalvi/Appendices/Suzuki/OrderThreeSuzukiCentralizer.lean`
- `OddOrder/Peterfalvi/Appendices/Suzuki2Groups/QuadraticExtensions.lean`

## 🔍 hub 内容監査 (2026-07-20 21:40 tick, merge 9a2d27ec1) — **健全。STOP なし**

合流時に merge 9a2d27ec1 (`d5a1c543a`/`d5145a9af`/`2fa607a0f`) の内容を独立監査した
(sorry 数でなく「hard content が実証明されたか / 構成不能な仮説へ hoist されていないか」で判定)。

**判定: genuine・sorry 0・axiom 0・unsound carrier 無し・既存 API の暗黙の弱化なし。**

### 確認できた事実

- **`_with_secondShift` 3 本は真に strong**。旧版と**仮説リストが byte-identical** で、
  結論に conjunct が増えているだけ (`∃ s, eTwo' = eTwo.trans (Frob^s).toLinearEquiv ∧ …`)。
  互換射影 3 本の statement も旧版と **byte-identical** — 下流を黙って弱めていない。
- ⚠ ただし**新しい数学ではない**。追加された結論は `rfl` で閉じており (PairGap:1206,
  TraceFormula:844)、witness は元々この Frobenius shift だった。**`∃` に隠れていた witness を
  露出させた de-opacification** であって、hub はこの 3 commit を「新定理」と読まないこと。
  (プロジェクト方針上これは正当な作業 — 下流の counter-shift に必要。)
- **`LengthTwoModels` の 7 宣言はすべて実証明**。`homocyclicFourSquareEquiv` は抽象的な
  濃度同型でなく `((… (mk x) : ℧₁(A)) : A) = x^2` が `rfl` で成立する二乗写像なので、
  `Frob⁻¹` 正規化は**強制されている** (等式を成り立たせるために選んだのではない)。
- **導入された仮説はすべて in-repo の producer に辿れた** — `ε` ← `exists_homocyclic_four_of_
  commutative_xiLengthTwo` / `hinvPhi` ← `involutions_subset_of_nontrivial_invariant` /
  `hEA` ← `frattini_isElementaryAbelian_of_xiLengthThree` / `he` ← `exists_ambientFrattini
  SingerCoordinates_of_xiLengthThree`。**構成不能な posited data は無い**。
  (`he` のみ `conj` 形 → pointwise `≃+` 形の glue が未記述。機械的、`PairGap.lean:106` に前例。)
- `XiLengthTwoTypeAData` は `TypeAData` から `phi_ne_one` を 1 つ落としたもので、
  `equivModel` は具体的な `QuadraticExtension` に着地し、可換/非可換の両分岐から実際に inhabited。
  `HasXiLengthTwo/Three` も「長さ n の狭義鎖の存在 **+ より長い鎖の非存在**」で honest。

### 残課題 (STOP でない・b の判断で)

1. ~~新規 7 宣言に consumer が無く、可換分岐の endpoint は依然 actor-blind な
   `LinearEquiv.ofFinrankEq` (LengthTwoModels:345) 経由~~ → **`55c15a749`
   「restore prescribed kernels after normalization」で解消中と見られる** (TypeAConclusion +
   LengthTwoModels に +248 行)。次 tick で再確認する。
2. **重複**: `xiLengthTwoTypeAData_of_homocyclic_four_prescribedKernel` (399-401) が
   `squareEquiv.toAdditive.trans kernelCoord |>.trans (frobeniusEquiv F 2).symm.toAddEquiv` を
   inline しているが、これは 90 行上で自ら追加した `homocyclicFourQuotientCoordinate` そのもの。
   後者に差し替えるのが素直。
3. **API が二重化**: strong/projection のペアで statement が 3 組。うち
   `exists_shiftedSecondLinearEquiv_expansion` (TraceFormula:883) は**既に consumer 0 の dead shim**。
   移行期としては妥当だが、shift が消費され切った時点で畳むこと (放置すると溜まる)。
4. **第 1 層の shift は未露出**: PairGap の強化は第 2 層座標 `eTwo'` のみを pin する。
   `eOne'` も証明中は `frobeniusShiftLinearEquivForNormalization eOne i.val` (PairGap:1077) だが
   export されていない。prescribed-coordinate が商/第 1 層の counter-shift も要求するなら
   3 本目の sibling が要る。

## 🔍 hub 内容監査 (2026-07-21 00:54 tick) — Lemma 12 mixed weight equation は genuine ✅

merge 015768c0a の ⭐ `d8b97df76` (+ feeders `ecf55f86a`/`3dc3f4c37`) を独立監査。
**判定: genuine・sorry 0・axiom-clean、book 強度の進捗。**

- `exists_mixedFrobeniusWeightEquation_of_xiLengthThree`
  (`HigmanLemmaTwelve/MixedEigenweights.lean:634`) は実証明 (0-sorry、AxiomsCheck:8452 登録)。
  honest な Lemma 12 仮説 (`IsPGroup 2 P`・`¬IsMulCommutative P`・2 involutions・`IsXiActor`・
  `HasXiLengthThree`・prime 条件) から `λ^(2^i)·λ'^(2^j) = ν^(2^k)` + `ν = λθ(λ) = μφ(μ)` を導出
  = Higman p.90 の pre-case-split state ちょうど。
- 存在量化の data は**構成済** (free field でない): factors ← `xiLengthThreeTypeAFactorData_exists`
  (`LengthTwoModels.lean:1278`、実 subgroup 分解 `left⊓right=Φ(P)`/`left⊔right=⊤`)、
  nonzero mixed commutator ← `exists_mixed_lowerCentralCommutatorBilinear_ne_zero`
  (`AmbientCentralExtension.lean:777`)、weight 抽出 ← `BilinearEigenweight.lean:150` (honest 線形代数)。
- red flag 無し (vacuous/矛盾仮説/unsound carrier いずれも無し)。次は B/C/D の case split。
