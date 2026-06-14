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

### 3. 送信前に目視 → 送信

`computer{action:"screenshot"}` で composer に全文が入り送信ボタン (右下の上矢印) が有効なのを確認 →
そのボタンを `computer{action:"left_click", coordinate:[…]}` でクリック。座標は screenshot から読む
(lane-b 実測では 1502×818 window で概ね `[1172, 765]`、ただし window サイズ依存なので毎回確認)。
Enter キー送信でも可だが、ボタンクリックの方が誤爆しにくい。

### 4. 回答を待つ → 読む

- ChatGPT **Pro の推論は遅い** (lane-b 実測で思考 **12分超**)。外部生成はハーネスが完了を検知できない
  ので、`ScheduleWakeup{delaySeconds:~720}` で自分でポーリングする (/loop 文脈なら prompt に
  `/loop <元の指示>` を渡して再入)。
- 完了後 `get_page_text{tabId}` で回答全文を取得 (article 本文を優先抽出してくれる)。screenshot より
  テキスト取得の方が長文回答に向く。
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
5. 送信ボタン座標は window サイズ依存 → 毎回 screenshot で確認。
6. Pro は思考 10分超もある → ScheduleWakeup でポーリング、get_page_text で回収。
