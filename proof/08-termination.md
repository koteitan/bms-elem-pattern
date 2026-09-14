[← Back](README.md) | [English](en/08-termination.md) | [Japanese](08-termination.md)

# 停止性と整礎性

前提: [01 順序数と ω₁](01-ordinals.md)、[05 配列、展開、安定ラベル](05-arrays-labels.md)、[06 有限反映](06-finite-reflection.md)、[07 ω₁ の中の閉包と鎖](07-closure-chains.md)

## 1. ラベルの体系

$`r \le 3`$ とする。$`\mathrm{Lab}`$ を順序数全体とし、$`\mathcal{R}_r`$ の関係で $`\lhd_k = \lt_{k+1}`$（$`k \lt r`$）と置く。

- 狭義、推移：[03](03-patterns.md) §3
- 有限反映：[06](06-finite-reflection.md)

したがってこれは行数 $`r`$ のラベルの体系（[05](05-arrays-labels.md) §5）である。

## 2. 初期列のラベル

**補題.** $`S^r_n`$ は安定ラベルを持つ。

**証明.** [07](07-closure-chains.md) §4 の鎖 $`c_0 \lt c_1 \lt \cdots \lt c_n`$ を取り、$`f(i) = c_i`$ と置く。

1. $`i \lt j`$ なら $`c_i \lt c_j`$
2. $`j \prec_k i`$ なら $`j \lt i`$ なので、$`c_j \lt_{k+1} c_i`$、すなわち $`f(j) \lhd_k f(i)`$

$`\square`$

## 3. 標準列はラベルを持つ

**補題.** 空でない標準列は安定ラベルを持つ。

**証明.** 展開の回数についての帰納法で示す。初期列は §2 による。$`A`$ から $`A[N]`$ を得たとき、$`A`$ が空なら $`A[N] = A`$ も空なので、仮定に反する。$`A`$ が空でなければ帰納法の仮定から安定ラベルがあり、命題 19.1 から $`A[N]`$ にも安定ラベルがある。$`\square`$

## 4. 停止性

**定理.** $`r \le 3`$、$`A`$ を $`r`$ 行の標準列、$`n : \mathbb{N} \to \mathbb{N}`$ とし、$`A_0 = A`$、$`A_{t+1} = A_t[n(t)]`$ と置く。このとき、ある $`T`$ で $`A_T`$ は空である。

**証明.** どの $`A_t`$ も空でないとする。

1. §3 から $`A_0`$ は安定ラベル $`f_0`$ を持つ
2. $`f_t`$ が $`A_t`$ の安定ラベルなら、命題 19.1 から、$`A_{t+1}`$ の安定ラベル $`f_{t+1}`$ で $`\mathrm{ht}(f_{t+1}) \lt \mathrm{ht}(f_t)`$ となるものが取れる。選択公理で $`t`$ ごとに 1 つ選んで列にする
3. $`\mathrm{ht}(f_0) \gt \mathrm{ht}(f_1) \gt \cdots`$ は順序数の無限降下列で、[01](01-ordinals.md) §1 に反する

$`\square`$

## 5. 整礎性

**定理.** $`r \le 3`$ のとき、$`r`$ 行の標準列の上の関係

```math
A \mathrel{R} B \iff B \ne \emptyset \wedge \exists n\ \bigl(A = B[n]\bigr)
```

は整礎である。

**証明.** $`R`$ の無限降下列 $`B_0, B_1, \dots`$（$`B_{t+1} \mathrel{R} B_t`$）があるとする。$`B_{t+1} = B_t[n(t)]`$ となる $`n(t)`$ を選ぶと、これは $`B_0`$ から始まる展開列で、どの項も空でない。§4 に反する。$`\square`$

## 6. ラベルの大きさ（形式化していない）

**下限.** 空の配列の高さを $`0`$、空でない配列 $`A`$ の展開木での高さを $`\mathrm{rank}(A) = \sup_N (\mathrm{rank}(A[N]) + 1)`$ と置く。

```math
\mathrm{rank}(A) \le \mathrm{ht}(f)
```

が、安定ラベル $`f`$ についての $`\mathrm{ht}(f)`$ の帰納法で示せる。$`A[N]`$ のラベル $`g`$ は $`\mathrm{ht}(g) \lt \mathrm{ht}(f)`$ を満たし、帰納法の仮定から $`\mathrm{rank}(A[N]) \le \mathrm{ht}(g)`$ だからである。したがって $`S^r_n`$ の最後のラベルは、$`S^r_n`$ の展開木での高さ以上でなければならない。

**上限.**

| 場合 | ラベルの範囲 |
|---|---|
| Lean で作ったラベル | $`\omega_1`$ 未満。どこにあるかは分からない |
| ペア数列（文献） | $`\psi_0(\Omega_\omega)`$ 未満に取れる |
| $`(0,0,0)(1,1,1)`$（文献） | $`(\upsilon_{\omega^2}, \upsilon_{\omega^2 + 2})`$ が使える |
| それより先のトリオ数列 | 分からない |

## 7. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| ラベルの体系 | `labelSystem` | [`Pattern/Reflect.lean`](../lean/Pattern/Reflect.lean) |
| §2 | `stable_stair` | [`Pattern/Main.lean`](../lean/Pattern/Main.lean) |
| §3 | `std_stable` | 同上 |
| §4 | `terminates`, `pss_terminates`, `tss_terminates` | 同上 |
| §5 | `StdElt`, `StdR`, `StdR_wf` | 同上 |
