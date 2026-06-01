# `prove` workflow — 教科書定理証明の汎用パイプライン (book 非依存)

**確定**: 2026-05-31 (worktree `gracious-hermann`)。`bg-prove` を generalize したもの。

## 何 / なぜ

教科書定理を 1 つ **design → implement(逐次 build-green, anti-scaffold) → adversarial verify** で
証明し、緑なら commit する 3-phase workflow。従来 BG 専用だった `bg-prove.js` を **book 非依存**に
一般化し、`args.book` (`bg`|`peterfalvi`|`isaacs`) で原典 mmd・namespace・note・引用名を切り替える。
`bg-prove` は `prove({book:'bg', ...})` を呼ぶ薄い alias に変更 (証明ロジックの single source of
truth = `prove.js`)。

**位置づけ**: `prove` = per-theorem prover (1 定理を緑に)。**cross-target の自走 orchestration は
workflow の外** (main-loop + 依存順キュー note が「1 ターゲットずつ launch → 完了通知で監査
(PASS は commit 維持 / VERIFY_FAILED は `git reset --hard HEAD~1` / BLOCKED は skip) → 次を launch」
を回す)。BG の実例 = `notes/bg/autonomous_prove_queue.md`。

**適否** (memory `autonomous-proof-workflows` / issue 0046 HANDOFF の学び):
- ✅ **well-scoped な単一定理 + 依存ほぼ ready** に効く (BG §4 Blackburn 群が多数 PASS、Peterfalvi の
  [Is]Thm 6.34 / (1.9) Galois / (6.8.x) sub-lemma もこの型)。`tractable` gate が前提不足を弾く。
- ❌ **深い依存チェーン** (例: §4-§6 coherence engine) は単一集中セッション (直接編集 + leaf build)
  の方が速い (再読込/decompose-report オーバーヘッドが無い)。workflow に載せない。

## book プリセット

| book | cite | mmd 既定 | namespace | note glob |
|---|---|---|---|---|
| `bg` | BG | `references/bg/local-analysis.mmd` | `OddOrder.BG.ChN.SNN` | `notes/bg/*.md` |
| `peterfalvi` | Peterfalvi | `references/peterfalvi/*.mmd` (章別; `args.mmdFile` で指定) | `OddOrder.Peterfalvi.SNN` (汎用は `OddOrder.GroupTheory.RepresentationTheory.*`) | `notes/peterfalvi/*.md` |
| `isaacs` | Isaacs | `references/isaacs/finite-group-theory.mmd` | `OddOrder.Isaacs.ChNN_*` | `notes/isaacs/*.md` |

- `bg` の `extra`: "**G**, Thm X.Y.Z" 省略箇所は `references/gorenstein/finite-groups.mmd` 参照 (まず Isaacs に読み替え)。
- `peterfalvi` の `extra`: [Is] (Isaacs Character Theory) 引用は repo の `RepresentationTheory.*`/`S03` に既存か確認、無ければ genuine に建てる。

## args API

最低限 `{book, name, decl}`。任意 override:

| key | 意味 |
|---|---|
| `book` | プリセット選択 (既定 `bg`) |
| `name` | ターゲットの人間可読名 (例 `"Peterfalvi [Is]Thm 6.34 (Frobenius induced irreducibility)"`) |
| `decl` | 目標 Lean decl 候補名 |
| `mmdFile` | 原典ファイルパス override (Peterfalvi の章別 mmd で必須。例 `references/peterfalvi/04.8_*.mmd`) |
| `mmd` | mmd 内の該当箇所 (例 `"(6.8) の証明 L136-243"`) |
| `namespace` / `design_note` / `ready_deps` | namespace / 参照ノート / grep 確認すべき ready 前提 の override |
| `mode` | `full` (既定, 3-phase) / `fast` (軽量, 下記) |
| `verify` | fast mode で `false` にすると objective build/axiom 検証も省略 (= implementer 自己申告のみ、最速) |
| `skeleton` / `target_file` | (任意) 設計済み target を fast に流すときの skeleton ヒント / 置き場所 |

返り status: `PASS` / `VERIFY_FAILED` / `BLOCKED_DESIGN` / `BLOCKED_IMPL` (返り値に `book`, fast 時 `mode:'fast'` フィールド付き)。

## mode: full / fast — 精度 vs 速度

| | `full` (既定) | `fast` |
|---|---|---|
| Design | 3並列調査 (mmd/API/scaffold) + synth (4 agent) | **implement に畳み込み (0 agent)** |
| Implement | 逐次 1–2 | 逐次 1–2 |
| Verify | 3並列 adversarial (build / scaffold-trap / faithfulness) | **objective build/axiom 1 つのみ** (`verify:false` で 0) |
| agent 数 | ~8–9 | **~2–3** |
| 適 | 重要 / 偽署名リスク高 / scaffold 誘惑大 な target | well-scoped で素早く数を稼ぎたい target、設計既知の target |

**fast が犠牲にするもの**: ①独立 scaffold-trap 監査 ②statement 忠実性クロスチェック ③`tractable` 事前 gate
(無理筋は実装中に判明 → revert)。**anti-scaffold 原則は implementer prompt に残し自衛** (外すと偽進捗量産)。
判断系を落とすので、稀に Nougat 落ち署名や hoist が滑り込む — 重要 target は `full` に戻すか後で `full` 監査をかける運用。

## 起動例

```jsonc
// Peterfalvi [Is]Thm 6.34 (Frobenius induced irreducibility)
Workflow({ name: 'prove', args: {
  book: 'peterfalvi',
  name: '[Is]Thm 6.34 (Frobenius L=H⋊W₁, θ∈Irr H, θ≠1 ⇒ Ind_H^L θ∈Irr L, deg=|W₁|θ(1))',
  decl: 'OddOrder.RepresentationTheory.induce_irreducible_of_frobenius',
  mmdFile: 'references/peterfalvi/04.8_pp_30_37_Some_Coherence_Theorems.mmd',
  ready_deps: 'inner_induce_eq_inner_restrict, inertia, brauer_permutation_lemma\', induceTerm_of_mem_normal, conjBy',
  design_note: 'issues/0046-peterfalvi-s08-6-8-coherence.md (進捗節の Thm 6.34 roadmap)',
} })

// BG (従来通り; bg-prove alias 経由でも prove 直でも可)
Workflow({ name: 'bg-prove', args: { name: 'Thm 4.16 ...', decl: '...', mmd: 'Thm 4.16 の証明' } })
```

## 3-phase 内部 (要約)

- **Design**: 3 並列 agent (①原典精読 ②repo API マッパー ③scaffold-trap 監査) → 1 synth が
  `DESIGN_SCHEMA` (signature/target_file/imports/skeleton/ready_lemmas/scaffold_risks/`tractable`) を確定。
  `tractable=false` → `BLOCKED_DESIGN` で即返す。
- **Implement**: 逐次 build-green 実装 (最大 2 attempt)、hoist 禁止 / sorry-free / exact 署名 /
  AxiomsCheck 登録 / 失敗時 `git checkout` でツリーを HEAD に戻す。未達 → `BLOCKED_IMPL`。
- **Verify**: 3 並列 adversarial (①build/axiom = 唯一の builder ②scaffold-trap read-only
  ③statement 忠実性 vs mmd) → 全 OK で `PASS`、逸脱は `VERIFY_FAILED`。

## 検証結果 (2026-05-31, Peterfalvi で実測)

同一クラスの character-theory lemma で full / fast を実走比較:

| run | mode | target | agent | tokens | 所要 | 結果 |
|---|---|---|---|---|---|---|
| 1 | full (誤発火※) | `induce_apply_one` (Ind θ(1)=[G:H]θ(1)) | 8 | 441k | ~9.5分 | PASS, 独立監査で faithful/緑/axiom-clean 確認 |
| 2 | **fast** | `conjBy_eq_self_of_mem` (g∈H⇒θ^g=θ) | **2** | **83k** | **~4.4分** | PASS, 独立監査で faithful/緑/axiom-clean + load-bearing refactor 確認 |

**fast は約 5× 安・約 2× 速**。well-scoped target では judgment verify を落としても健全な結果(implementer が anti-thin-wrapper を守り `subgroup_le_inertia` を新 lemma 呼び出しに refactor するなど)。

**※ args 文字列化の footgun**: run 1 で `args` が JSON 文字列として届き `T=args||{}` が文字列に → `T.book`/`T.mode` が undefined → 既定 bg/full に落ちた(`book:"BG"`, verify 3, agent 8 が証拠。設計 agent は「追加情報」の JSON 文字列から target を読めたので結果的に landed)。→ **`prove.js` を string-robust 化済**(`typeof T==='string'` なら `JSON.parse`)。

**運用モデルの確証**: fast mode が落とす精度次元(scaffold-trap / faithfulness / thin-wrapper)は **main loop が独立監査**(diff 精読 + `lake build OddOrder OddOrder.AxiomsCheck` + sorry数 + `#assert_only_allowed_axioms`)で補う。result の `book`/`mode`/`agent_count`/`verify` フィールドで「意図したモードで走ったか」を必ず確認(self-reported status を鵜呑みにしない)。重要 / scaffold 誘惑大 / 偽署名リスク高な target は full mode に上げる。

## durability (重要)

`/.claude/` は `.gitignore` で丸ごと除外 = **workflow スクリプトは git versioned されない**。さらに
`.claude/workflows/` は **worktree ごとに独立** (symlink でなくコピー)。したがって:

- 本 note (tracked) が `prove`/`bg-prove` の **設計の正本**。スクリプト実体は各 worktree の
  `.claude/workflows/{prove,bg-prove}.js` (untracked)。
- 別 worktree / main で `prove` を使うには、そこの `.claude/workflows/prove.js` を用意する必要がある
  (本 note の Appendix から復元可)。main の `bg-prove.js` は従来の self-contained 版のままで動く
  (本一般化は worktree `gracious-hermann` ローカル)。
- 構文検証: `node` の `--check` は top-level `return`/`await` を弾く (runtime は body を async 関数で
  wrap して実行するので合法)。検証は AsyncFunction constructor wrap で行う:
  `new (Object.getPrototypeOf(async function(){}).constructor)('args','phase','log','parallel','agent','workflow', src)`。
- **推奨 (ユーザー判断待ち)**: workflow スクリプトは価値ある IP で worktree 間共有も望ましいので、
  `.gitignore` の `/.claude/` を `/.claude/*` + `!/.claude/workflows/` 等に緩めて `.claude/workflows/`
  だけ track するのが durability の正攻法 (本 note への全文複製による drift を回避できる)。未決。
  それまでは本 note + 各 worktree の untracked スクリプトが実体。`prove.js` の現行版は ~180 行、
  構成は本節の「3-phase 内部」+「book プリセット」+「args API」で full spec を与えており、
  失われても再構成可能 (bg-prove.js は 12 行の `return await workflow('prove', {...args, book:'bg'})` alias)。
