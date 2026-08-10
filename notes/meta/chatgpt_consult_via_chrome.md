# ChatGPT 相談を Chrome MCP で自分で回す手順 (全レーン共通)

**確定**: 2026-06-15 (lane-b で実証)

## これは何か

教科書の行間で詰まったとき、強い外部モデル (ChatGPT Pro 等) に再構成を依頼できる。
**いつ・なぜ聞くか**の判断と自己完結プロンプトの書き方は memory
`feedback-ask-chatgpt-for-elided-gaps.md` + 既存プロンプト例 (`notes/bg/s13_8_chatgpt_prompt.md`,
`s13_10_chatgpt_prompt.md`, `notes/peterfalvi/*_chatgpt_prompt.md`) を見ること。

このファイルは**機械的な how-to** = ユーザー relay なしで、エージェント自身が Chrome 拡張 MCP
(`mcp__Claude_in_Chrome__*`) を使って既に開いている ChatGPT タブにプロンプトを投入・送信し、
回答を読み取る手順。2026-06-15 にユーザーが「これからは自分で Chrome をいじって勝手に投げて」と明示。

## 前提

- Chrome に **Claude in Chrome 拡張**がインストール済み・接続済み (ユーザーが用意)。未接続なら
  `list_connected_browsers` → `select_browser`、またはユーザーに Chrome 内で接続してもらう
  (`switch_browser`)。
- ChatGPT のタブ (該当プロジェクト・該当チャット) が**既に開いている**のが通常。lane ごとに
  別チャットを使う運用 (例: lane-b は project "odd-order" / chat "Formalizing Peterfalvi's Proof")。

## 手順

### 0. ツールを読み込む (deferred)

`mcp__Claude_in_Chrome__*` は deferred。**ToolSearch のクエリに注意**:

- ❌ `ToolSearch{query:"Claude_in_Chrome"}` は **0 件**で返る (サーバ名そのままは効かない)。
- ✅ `ToolSearch{query:"chrome browser tab navigate page", max_results:30}` で全 toolkit が一括で載る。
  記述的キーワードで引く。

### 1. タブを特定

`tabs_context_mcp{createIfEmpty:false}` → 開いている tab の `tabId` と title/url が返る。ChatGPT の
tabId を控える。新規に開くなら `tabs_create_mcp` → `navigate{url:"https://chatgpt.com/..."}`。

### 2. プロンプトを入力欄に投入 ★ここが肝★

ChatGPT の composer は **`#prompt-textarea` という ProseMirror の contenteditable `<div>`** であって、
plain な `<textarea>` ではない。よって:

- ❌ `computer{action:"type"}` で改行入りの長文を打つのは危険 — **ChatGPT は Enter で送信**するので、
  本文中の改行で途中送信され得る (Shift+Enter が改行)。
- ❌ `form_input` は contenteditable には素直に効かない。
- ✅ **`javascript_tool` で合成 paste イベントを dispatch する**のが最も確実。複数段落・unicode
  (μ σ χ τ → ⊥ ⋊ ◁ ∑ 等) を 1 回の paste として忠実に入れられ、送信もされない:

```js
const text = `...プロンプト全文 (テンプレートリテラル; 本文にバッククォートと ${'$'}{ を含めない)...`;
const el = document.querySelector('#prompt-textarea') || document.querySelector('div[contenteditable="true"]');
if (!el) { throw new Error('input element not found'); }
el.focus();
const dt = new DataTransfer();
dt.setData('text/plain', text);
el.dispatchEvent(new ClipboardEvent('paste', { clipboardData: dt, bubbles: true, cancelable: true }));
// 検証用に返す:
({ targetLen: text.length, editorLen: el.innerText.length, head: el.innerText.slice(0,90), tail: el.innerText.slice(-90) })
```

- **`await` 落とし穴**: `javascript_tool` の REPL は tool 説明に反して**トップレベル `await` 非対応**
  (`SyntaxError: await is only valid in async functions`)。`setTimeout`+`await` を使わず同期で書くか、
  `(async()=>{...})()` で包む。paste は同期反映されるので普通は await 不要。
- 戻り値の `editorLen`/`head`/`tail` で全文が入ったか検証する (ProseMirror が段落区切りを足すので
  editorLen は targetLen より少し大きくなるのが正常; head/tail 一致を確認)。

### 3. 送信前に目視 → 送信 ★座標は paste 後に取り直す★

**重要 (lane-f 2026-06-15 実測)**: 長文 paste 後は composer が縦に伸びて**送信ボタンが下へ動く**。
paste **前**の screenshot 座標を使い回すと空白をクリックして送信されない。手順:
1. paste 後に `computer{action:"screenshot", tabId}` を**取り直す**。
2. 右下の上矢印 (送信ボタン、`Pro 拡張` の右隣) を `computer{action:"left_click", coordinate:[…], tabId}` でクリック
   (1456×840 window で実測 `[1137, 789]`。window/composer 高さ依存ゆえ毎回 screenshot から読む)。
3. **送信できたか必ず JS で検証** (クリック成功 ≠ 送信成功): `msgCount` が +1、`composerEmpty===true`、
   `isGenerating===true` を確認 (下記スニペット)。未送信なら座標を直して再クリック。
```js
(() => { const t=[...document.querySelectorAll('[data-message-author-role]')];
  const el=document.querySelector('#prompt-textarea')||document.querySelector('div[contenteditable="true"]');
  return { msgCount:t.length, composerEmpty: el? el.innerText.trim().length===0 : 'no-el',
    isGenerating: !!document.querySelector('button[data-testid="stop-button"]')||!!document.querySelector('[data-testid="stop-streaming-button"]'),
    lastRole: t.at(-1)?.getAttribute('data-message-author-role') }; })()
```
Enter キー送信でも可だが、ボタンクリック + JS 検証の方が誤爆しにくい。

### 4. 回答を待つ → ★text で読む★ (screenshot で読まない)

- ChatGPT **Pro の推論は遅い** (実測 **12〜19分**)。外部生成はハーネスが完了を検知できないので
  `ScheduleWakeup` で自分でポーリング (/loop 文脈なら prompt に `/loop <指示>` を渡して再入)。13.10 が
  18m42s だった例から、初回 ~900s → まだ `isGenerating` なら ~300s 刻みで再ポーリングが効率的。
- **回答は必ず `get_page_text{tabId}` の text で読む** (ユーザー明示 2026-06-15)。screenshot は冒頭しか
  見えず長文回答に不適。`get_page_text` は article 本文を優先抽出するので最新 assistant turn を全文取れる。
  完了判定は §3 の JS (`isGenerating===false` かつ最後が assistant) で先に確認してから読む。
- **回答は鵜呑みにせず全 step 厳密検証**してから形式化 (memory の方針通り)。

## tier の注意 (なぜ拡張 MCP を使うか)

OS レベルの `mcp__computer-use__*` では Chrome は tier **"read"** (クリック・タイプがブロック) になる。
一方 **Chrome 拡張 MCP (`mcp__Claude_in_Chrome__*`) は拡張経由なのでこの制約を受けず**、クリック・JS
実行・入力ができる。よって Chrome 操作は必ず拡張 MCP 側を使う。

## 落とし穴まとめ (再掲)

1. ToolSearch はサーバ名 "Claude_in_Chrome" だと 0 件 → 記述的キーワードで引く。
2. composer は textarea でなく ProseMirror contenteditable → 長文は JS 合成 paste で入れる。
3. `type` で改行入り長文は途中送信の危険 (Enter=送信)。
4. `javascript_tool` はトップレベル await 非対応 → 同期 or async IIFE。
5. 送信ボタン座標は window/composer 高さ依存 + **paste 後にボタンが下へ動く** → paste **後**に
   screenshot を取り直してから click。送信は JS (`msgCount`/`composerEmpty`/`isGenerating`) で検証。
6. Pro は思考 12〜19分 → ScheduleWakeup でポーリング、**回答は `get_page_text` の text で読む** (screenshot 不可)。
7. **`javascript_tool` / `computer` は `tabId` 必須** (忘れると `InputValidationError: tabId Required`)。
8. **base64 にしない** (lane-f 2026-06-15 のミス)。本文は template literal に**直接**入れる — ただし
   本文から **backtick / `${` / `\`** を除いておく (プロンプトは最初から backtick-free で書く; markdown の
   `\*` escape も外す)。これで unicode (σ τ ℰ ◁ 等) もそのまま忠実に paste される。

## ✅ 確認済レシピ (2026-06-15 lane-f が B method を再現・skill 化候補)

ToolSearch (記述キーワード) → `tabs_context_mcp{createIfEmpty:false}` で ChatGPT tab の tabId 取得 →
プロンプトを backtick-free で用意 (`notes/.../*_chatgpt_prompt.md` 保存) → §2 の合成 paste JS (tabId 付き、
template literal 直接) → JS で `editorLen≈targetLen`+head/tail 検証 → §3 で paste 後 screenshot → 送信ボタン
click → JS で送信検証 → `ScheduleWakeup`(~900s) ポーリング → §4 `get_page_text` で text 回収 → 厳密検証 → Lean 化。

---

## 2026-08-09 更新 (UI 変更 + 長考の実測)

### モデル選択の UI が変わった — 「Pro 拡張」はもう無い

旧記載の「モデルドロップダウン → 知能メニュー (最速/標準/高/最高/**Pro 拡張**/GPT-5.5)」は**現存しない**。
現在 (2026-08-09 実測) の手順:

1. composer 右の **`Pro ⌄`** バッジをクリック → 小さいポップオーバー (スライダー + `詳細設定 ›`)
2. **`詳細設定`** をクリック → 2 行が出る
   - **モデル**: `GPT-5.6 Sol` / `GPT-5.5` / `o3` (既定は `GPT-5.6 Sol` = 最強)
   - **推論レベル**: `Pro` (最上位)
3. 送信前に composer のバッジが `Pro` であることを目視確認する。

⟹ **既定のままで最強** (`GPT-5.6 Sol` + 推論レベル `Pro`)。旧 UI を探して迷わないこと。

### 長文投入は `execCommand('insertText')` でも通る (合成 paste より簡単)

§2 の ClipboardEvent 合成 paste は今も有効だが、**次の 4 行でも同じ結果**が得られた (2026-08-09、4738 字):

```js
const TEXT = `…本文 (backtick / ${…} / \ を含めない)…`;
const ed = document.querySelector('#prompt-textarea') || document.querySelector('div[contenteditable="true"]');
ed.focus();
document.execCommand('insertText', false, TEXT);
ed.textContent.length;   // 検証用
```

⚠ `type` アクションで改行入り文字列を渡すと**改行の時点で送信される**ことを実測で再確認した
(「TEST line one / TEST line two」で 1 行目だけが送信された)。落とし穴 3 は健在。

⚠ 送信ボタンの座標は paste 後に取り直すこと (落とし穴 5) — 加えて **composer 右上の「展開」アイコンを
誤クリックしやすい**。展開すると composer が縦に伸びて送信ボタンがさらに下へ動くので、screenshot を
取り直してから押し直す。

### Pro の思考時間は「12〜19 分」では収まらない

落とし穴 6 の「12〜19分」は**過小**。2026-08-09 の実測 (BG App.C Problem 1 = 未解決問題を投入):

- **1 回目**: 約 2.5 時間走ったのち **`A network error occurred.`** で落ちた。
  落ちる直前は「PDF をダウンロード → サイト検索 → 交互語の最短自明関係を探索」まで到達していた。
- **`再試行` ボタン**を押すと**最初からやり直し**になる (途中経過は保持されない)。
- **2 回目**: さらに 4 時間以上走ってなお未完了 (進捗表示は 2.5 時間動かず)。

⟹ **未解決問題級を投げるときの運用**:
- ポーリング間隔は `ScheduleWakeup(1800)` (30 分) で十分。60〜900s は無駄。
- **ネットワークエラーで落ちる前提**で監視する (落ちていたら `再試行` を押す)。
- 進捗表示 (`Pro が思考中です` の上の要約行) は**内部推論の断片が出る**ので、完走しなくても
  中間結果 (簡約・排除された場合分け) は回収できる。screenshot で読める。
- 何時間で見切るかは**ユーザーに決めさせる** (`AskUserQuestion`)。こちらで勝手に「今すぐ回答」を
  押さない — 深い探索が打ち切られる。

---

## 2026-08-10 更新 (Work モード + 思考レベル「ウルトラ」)

### UI がまた変わった — 上部に `Chat` / `Work` トグル

`https://chatgpt.com/` を開くと画面上部中央に **`Chat` | `Work`** のトグルがある。
**`Work`** 側は別サーフェス (プレースホルダが「何に取り組みますか?」、下にプロジェクト選択・
プラグイン (GitHub/Google 等)・デスクトップアプリ導線が並ぶ)。長時間の調査タスクはこちら。

### モデルと思考レベルの選び方 (2026-08-09 の「Pro ⌄ → 詳細設定」からさらに変わった)

1. composer 右下の **`✦ 5.6 Sol <レベル> ⌄`** バッジをクリック → 詳細設定ポップオーバー
2. 3 行: **モデル** (`GPT-5.6 Sol`) / **思考レベル** / **速度** (`高速`)
3. **思考レベル**行をクリック → サブメニューが右に開く:
   **軽 / 中程度 / 高い / 非常に高い / 最大 / ウルトラ**
   (`ウルトラ` には「利用枠の消費が速くなります」の注記)
4. 選ぶとバッジが `✦ 5.6 Sol ウルトラ` に変わる。**送信前にバッジで目視確認**する
   (Work 既定は `軽` なので、放っておくと最弱で走る)。

⚠ `Chat` 側の既定は `非常に高い` で、`Work` 側の既定は `軽` と**別々に持たれている**。

### 投入・送信は従来どおり

`#prompt-textarea` への `document.execCommand('insertText', …)` (§「長文投入」) がそのまま効く。
2026-08-10 実測: 10,728 字を 1 発で投入 (`editorLen` 10,826 = ProseMirror の段落区切り分だけ増える)。
送信ボタンは composer 右下の丸い上矢印で、**paste 後に screenshot を取り直して座標を読む**
(落とし穴 5 は健在)。送信検証 JS (`msgCount`/`composerEmpty`/`isGenerating`) も同じものが使える。
