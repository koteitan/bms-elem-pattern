[← Back](README.md) | [English](en/03-patterns.md) | [Japanese](03-patterns.md)

# R_N（elementary patterns of resemblance）

前提: [01 順序数と ω₁](01-ordinals.md)、[02 構造と初等部分構造](02-elementary-substructure.md)

## 1. 定義

**定義（Carlson）.** $`N \ge 1`$ とする。順序数の上の関係 $`\le_1, \dots, \le_N`$ を、次の式で同時に定める。

```math
\alpha \le_j \beta \iff \alpha \le \beta \wedge (\alpha; \le, \le_1, \dots, \le_N) \preceq_{\Sigma_j} (\beta; \le, \le_1, \dots, \le_N) \qquad (1 \le j \le N)
```

```math
\mathcal{R}_N = (\mathrm{Ord}; \le, \le_1, \dots, \le_N), \qquad \alpha \lt_j \beta \iff \alpha \lt \beta \wedge \alpha \le_j \beta
```

Wilken の論文の $`\mathcal{R}_2`$、$`\mathcal{R}_3`$ は、$`N = 2, 3`$ の場合である。

**読み方.** $`\alpha \le_j \beta`$ は、$`\alpha`$ 未満の順序数の「形」が、$`\beta`$ 未満まで広げても $`\Sigma_j`$ 論理式では見分けられない、ということである。ここで形とは、大小関係と、関係 $`\le_1, \dots, \le_N`$ 自身のことである。

## 2. なぜ定義できるか

右辺は、左辺で定義しようとしている関係 $`\le_1, \dots, \le_N`$ を使っている。循環しているように見えるが、$`\beta`$ についての帰納法で定まる。

右辺の 2 つの構造に現れる関係は、$`\beta`$ 未満の 2 元 $`a, b`$ の間の $`a \le_i b`$ だけである。$`b \lt \beta`$ なので、これは帰納法のそれより前の段階 $`b`$ で決まっている。したがって、段階 $`\beta`$ では、すでに決まった関係を使って、すべての $`\alpha \le \beta`$ について $`\alpha \le_j \beta`$ を決めればよい。

この決め方から、$`a \le_i b`$ の真偽は、$`a, b`$ を含むどの構造 $`(\gamma; \ldots)`$ で見ても同じである。構造の関係は全体の関係の制限だからである。

Lean では、$`\beta`$ についての整礎再帰でこの関係を定義し、定義の式を補題として取り出す。そのとき、「$`\beta`$ 未満で評価する論理式は $`\beta`$ 未満の組の関係しか見ない」という補題が要になる。

## 3. 基本性質

**命題.** $`1 \le j \le N`$ とする。

1. $`\alpha \le_j \alpha`$
2. $`\alpha \le_j \beta`$ かつ $`\beta \le_j \gamma`$ なら $`\alpha \le_j \gamma`$
3. $`j \lt N`$ のとき、$`\alpha \le_{j+1} \beta`$ なら $`\alpha \le_j \beta`$

**証明.** 1 は同じ構造どうしなので明らか。2 は [02](02-elementary-substructure.md) §4 の推移性。3 は $`\Sigma_{j+1}`$ 初等部分構造なら $`\Sigma_j`$ 初等部分構造であることから出る。$`\square`$

3 から、$`\alpha \lt_{j+1} \beta`$ なら $`\alpha \lt_j \beta`$ である。

## 4. 小さい例

以下 $`N \ge 1`$ は任意とする。

**例 1.** 自然数 $`n \lt m`$ について、$`n \le_1 m`$ でない。同様に $`n \le_1 \omega`$ でない。

- $`n \ge 1`$ のとき：パラメータ $`n - 1`$ を持つ $`\Sigma_1`$ 論理式 $`\exists x\ (n - 1 \lt x)`$ は、$`m`$ で真（$`x = n`$）、$`n`$ で偽である
- $`n = 0`$ のとき：$`\exists x\ (x \le x)`$ は $`m`$ で真、空の構造 $`0`$ で偽である

**例 2.** $`\omega \lt_1 \omega + 1`$ である。

例 1 と §3 の 3 から、$`\omega + 1`$ 未満の異なる 2 元の間では、どの $`\le_j`$ も成り立たない。したがって $`(\omega; \ldots)`$ と $`(\omega + 1; \ldots)`$ では、原子式 $`x \le_j y`$ は $`x = y`$ と同じ意味になる。すると $`\Sigma_1`$ 初等部分構造であるかは、関係 $`\le`$ だけの構造の場合と同じになり、[02](02-elementary-substructure.md) §4.2 の例から成り立つ。

**例 3.** $`\omega \le_2 \omega + 1`$ でない。$`\Sigma_2`$ 論理式「最大元がある」が $`\omega + 1`$ で真、$`\omega`$ で偽だからである。

**例 4.** $`\omega \le_1 \omega + 2`$ でない。$`\Sigma_1`$ 論理式 $`\exists x\ \exists y\ (x \lt y \wedge x \le_1 y)`$ は、例 2 から $`\omega + 2`$ で真（$`x = \omega`$、$`y = \omega + 1`$）、例 1 から $`\omega`$ で偽だからである。

以上から $`\{\beta : \omega \le_1 \beta\} = \{\omega, \omega + 1\}`$ である。

## 5. 文献で分かっていること

証明には使わない。ラベルの大きさを論じるときに使う。

- $`\mathcal{R}_2`$ で最小の $`\lt_2`$ の組は $`\varepsilon_0 \cdot \omega \lt_2 \varepsilon_0 \cdot (\omega + 1)`$ である
- 列 $`\upsilon_0 = 0`$、$`\upsilon_{\xi + 1} = \upsilon_\xi^\infty`$、$`\upsilon_\lambda = \sup_{\iota \lt \lambda} \upsilon_\iota`$ を考える。$`\upsilon_\xi^\infty`$ は $`\upsilon_\xi`$ を材料にした相対化 Buchholz 型表記系の可算部分で、$`\upsilon_1 = \psi_0(\Omega_\omega)`$ である
- $`\mathcal{R}_2`$ で、$`\iota \gt 1`$ が「極限 + 1」の形でない添字全体 $`I`$ について、$`(\upsilon_\iota)_{\iota \in I}`$ は極大の $`\lt_2`$ 鎖である
- $`\psi_0(\Omega_\omega)`$ は、その下に有限の $`\le_2`$ 鎖がいくらでも長くとれる最小の順序数である
- $`\mathcal{R}_3`$ で最小の $`\lt_3`$ の組は $`\upsilon_{\omega^2} \lt_3 \upsilon_{\omega^2 + 2}`$ である
- 始切片 $`\upsilon_{\omega^2 + 2}`$ の上では、$`\mathcal{R}_2`$ と $`\mathcal{R}_3`$ の関係は一致する

出典：

- G. Wilken, Pure Σ2-elementarity beyond the core, Annals of Pure and Applied Logic 172 (2021). https://doi.org/10.1016/j.apal.2021.103001
- G. Wilken, Tracking chains revisited. https://arxiv.org/abs/1611.04348
- G. Wilken, Pure Σ2-Elementarity beyond the Core, arXiv 版 v1 の第 4 節. https://arxiv.org/abs/1710.01870v1

## 6. 証明での使われ方

| 事実 | 使う場所 |
|---|---|
| 定義 | ラベルの関係 $`\lhd_k = \lt_{k+1}`$（[06](06-finite-reflection.md)） |
| 反射律、推移律、段の単調性 | [04](04-pattern-properties.md)、[06](06-finite-reflection.md)、[08](08-termination.md) |

## 7. Lean での対応

Lean では段の番号が 1 つずれる。`lev N j a b` が $`a \le_{j+1} b`$、`lab N j a b` が $`a \lt_{j+1} b`$ である。

| 概念 | Lean | ファイル |
|---|---|---|
| 定義の再帰 | `stage`, `RFix`, `RN` | [`Pattern/Basic.lean`](../../lean/Pattern/Basic.lean) |
| $`\le_{j+1}`$、$`\lt_{j+1}`$ | `lev N j`, `lab N j` | 同上 |
| 定義の式 | `rel_iff`, `lev_iff` | 同上 |
| $`\beta`$ 未満の組しか見ない | `sig_congr`, `stage_agree`, `elem_congr` | 同上 |
| §3 の 1、2、3 | `lev_refl`, `lev_trans`, `lev_mono` | 同上 |
| $`\lt`$ についての推移律と単調性 | `lab_trans`, `lab_mono` | 同上 |
