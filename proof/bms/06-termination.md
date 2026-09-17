[← Back](README.md) | [English](en/06-termination.md) | [Japanese](06-termination.md)

# すべての行数の停止性と整礎性

前提: [pss 05 配列、展開、安定ラベル](../pss/05-arrays-labels.md)、[pss 07 ω₁ の中の閉包と鎖](../pss/07-closure-chains.md)、[pss 08 停止性と整礎性](../pss/08-termination.md)、[05 すべての段の有限反映](05-finite-reflection.md)

## 1. ラベルの体系

$`r \ge 1`$ を行数とする。$`\mathrm{Lab}`$ を順序数全体とし、$`\mathcal{R}_r`$ の関係で $`\lhd_k = \lt_{k+1}`$（$`k \lt r`$）と置く。[05](05-finite-reflection.md) §5 から、これは行数 $`r`$ のラベルの体系である。

$`r = 0`$ のときは、有限反映の条件 $`n \lt 0`$ が空なので、どんな狭義で推移的な関係でもラベルの体系になる。Lean では $`r = 0`$ も同じ定義で扱う。

## 2. 初期列のラベル

**補題.** $`S^r_n = (0, \dots, 0)(1, \dots, 1) \cdots (n, \dots, n)`$ は安定ラベルを持つ。

**証明.** [pss 08](../pss/08-termination.md) §2 と同じである。[pss 07](../pss/07-closure-chains.md) §4 の鎖 $`c_0 \lt c_1 \lt \cdots \lt c_n`$ は、どの 2 つもすべての段 $`j \le r`$ で $`c_i \lt_j c_{i'}`$ なので、$`f(i) = c_i`$ と置けばよい。$`\square`$

## 3. 標準列はラベルを持つ

**補題.** 空でない $`r`$ 行の標準列は安定ラベルを持つ。

**証明.** 展開の回数についての帰納法。初期列は §2、展開は命題 19.1（[pss 05](../pss/05-arrays-labels.md) §7）による。[pss 08](../pss/08-termination.md) §3 と同じである。$`\square`$

## 4. 停止性

**定理.** $`r`$ を任意の自然数、$`A`$ を $`r`$ 行の標準列、$`n : \mathbb{N} \to \mathbb{N}`$ とし、次のように置く。

```math
A_0 = A, \qquad A_{t+1} = A_t[n(t)]
```

このとき、ある $`T`$ で $`A_T`$ は空である。

**証明.** どの $`A_t`$ も空でないとする。§3 と命題 19.1 から、安定ラベル $`f_t`$ で次を満たすものが選べる。

```math
\mathrm{ht}(f_0) \gt \mathrm{ht}(f_1) \gt \mathrm{ht}(f_2) \gt \cdots
```

これは順序数の無限降下列で、[pss 01](../pss/01-ordinals.md) §1 に反する。$`\square`$

## 5. 整礎性

**定理.** $`r`$ 行の標準列の上の関係

```math
A \mathrel{R} B \iff B \ne \emptyset \wedge \exists n\ \bigl(A = B[n]\bigr)
```

は整礎である。

**証明.** $`R`$ の無限降下列は、どの項も空でない展開列になり、§4 に反する。$`\square`$

## 6. BM4 との関係

- BM4 の初期列 $`E_r = (0, \dots, 0)(1, \dots, 1)`$ は $`S^r_1`$ である。したがって、$`E_r`$ から展開で得られる行列は $`r`$ 行の標準列で、§4 からその展開は止まる
- 展開規則は BM4 のものだけを扱う。他の版のバシク行列との一致は扱っていない
- DH の論文は、同じ命題 19.1 に、構成可能階層の初等部分構造のラベルを渡して停止性を示した。ここでは $`\mathcal{R}_r`$ の関係を渡している

## 7. ラベルの大きさ（形式化していない）

- Lean のラベルは、[pss 07](../pss/07-closure-chains.md) の閉包で作るので、$`\omega_1`$ 未満であることしか分からない
- [pss 08](../pss/08-termination.md) §6 の下限 $`\mathrm{rank}(A) \le \mathrm{ht}(f)`$ は、行数によらず成り立つ
- 4 行以上で、$`\mathcal{R}_r`$ の中のどこにラベルが取れるかは調べていない

## 8. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| §1 | `labelSystemGen` | [`Pattern/General.lean`](../../lean/Pattern/General.lean) |
| $`S^r_n`$、標準列 | `stair`, `Std` | [`Pattern/Main.lean`](../../lean/Pattern/Main.lean) |
| §2 | `stable_stair` | 同上 |
| §3 | `std_stable` | 同上 |
| §4 | `terminates` | 同上 |
| §5 | `StdElt`, `StdR`, `StdR_wf` | 同上 |
| 鎖 | `lamChain`, `lab_lam` | [`Pattern/Chain.lean`](../../lean/Pattern/Chain.lean) |
| 命題 19.1 | `descent` | [`Bm4/Label.lean`](../../lean/Bm4/Label.lean) |
