[← Back](README.md) | [English](en/04-cofinal-predecessors.md) | [Japanese](04-cofinal-predecessors.md)

# P7′：下端では前者が非有界

前提: [pss 04 R_N の性質 P1〜P7](../pss/04-pattern-properties.md)、[02 論理式 Φₘ](02-phi.md)、[03 成分ごとの条件をブロックの形に書く](03-block-form.md)

## 1. 主張

**命題（P7′）.** $`1 \le m \lt N`$、$`\alpha \lt_{m+1} \beta`$ とする。このとき、$`1 \le i \le m`$ のすべてで $`\mathrm{Cof}_i(\alpha)`$ である。

```math
\forall z \lt \alpha\ \exists s\ \bigl(z \lt s \lt \alpha \wedge s \le_i \alpha\bigr)
```

$`m = 1`$ が P7 である。3 行の有限反映では P7 だけを使った。すべての段の有限反映では、[02](02-phi.md) の補題 B を $`\alpha`$ で使うためにこの命題が要る。

**補足.** $`\alpha \lt_j \beta`$ なら $`\alpha \gt 0`$ である。$`\Sigma_1`$ 文 $`\exists x\ (x \le x)`$ は $`\beta`$ で真（$`x = \alpha`$）なので、$`\alpha`$ でも真だからである。[03](03-block-form.md) の補題はこれを使う。

## 2. 証明

$`m`$ についての帰納法。$`m = 1`$ は P7 である。

$`m + 1 \lt N`$、$`\alpha \lt_{m+2} \beta`$ とする。$`\alpha \lt_{m+1} \beta`$ なので、帰納法の仮定から $`i \le m`$ のすべてで $`\mathrm{Cof}_i(\alpha)`$ である。$`\mathrm{Cof}_{m+1}(\alpha)`$ を示す。

使う事実：

- $`\alpha \lt_1 \beta`$ なので、P5 から $`\alpha`$ は後続で閉じる
- $`\alpha \lt_2 \beta`$ なので、P6 から $`\beta`$ は後続で閉じる
- 次の $`\tau`$ はパラメータ無しの $`\Pi_{m+2}`$ 文で、その否定は [03](03-block-form.md) §4 (2) の $`\Sigma_{m+2}`$ 文である

```math
\tau = \forall z\ \exists u\ \bigl(z \lt u \wedge \Phi_m(u)\bigr)
```

**段階 A：α で τ.** $`z \lt \alpha`$ を取る。$`\mathrm{Cof}_m(\alpha)`$ から、$`z \lt u \lt \alpha`$ で $`u \le_m \alpha`$ となる $`u`$ がある。$`i \lt m`$ の $`\mathrm{Cof}_i(\alpha)`$ があるので、補題 B から $`\alpha \models \Phi_m(u)`$。

**段階 B：β で τ.** $`\alpha \le_{m+2} \beta`$ で、$`\neg\, \tau`$ はパラメータ無しの $`\Sigma_{m+2}`$ 文なので、$`\alpha`$ と $`\beta`$ で真偽が一致する。段階 A から $`\beta \models \tau`$。

**段階 C：Cof_m(β).** $`z \lt \beta`$ を取る。段階 B から、$`z \lt u \lt \beta`$ で $`\beta \models \Phi_m(u)`$ となる $`u`$ がある。$`\beta`$ は後続で閉じるので、補題 A から $`u \le_m \beta`$。

**段階 D：β で Φ_{m+1}(α).** $`\alpha \lt \beta`$、$`\alpha \le_{m+1} \beta`$ である。段階 C から $`i \le m`$ のすべてで $`\mathrm{Cof}_i(\beta)`$ なので、補題 B から $`\beta \models \Phi_{m+1}(\alpha)`$。

**段階 E：α へ戻す.** $`z \lt \alpha`$ を取る。パラメータ $`z`$ を持つ $`\Sigma_{m+2}`$ 文（[03](03-block-form.md) §4 (1)）

```math
\exists u\ \bigl(z \lt u \wedge \Phi_{m+1}(u)\bigr)
```

は、段階 D から $`\beta`$ で真（$`u = \alpha`$）。$`\alpha \le_{m+2} \beta`$ から $`\alpha`$ でも真で、証人 $`u`$ は $`z \lt u \lt \alpha`$、$`\alpha \models \Phi_{m+1}(u)`$ を満たす。$`\alpha`$ は後続で閉じるので、補題 A から $`u \le_{m+1} \alpha`$。

$`\square`$

**読み方.** 「$`\alpha`$ の $`\le_{m+1}`$-前者が非有界」は $`\alpha`$ の中の論理式では言えない。そこで次の順に進む。

1. $`\alpha`$ の中で言える「$`\Phi_m`$ を満たす点が非有界」を $`\beta`$ へ上げる
2. $`\beta`$ の側で $`\mathrm{Cof}_m(\beta)`$ を得て、$`\alpha`$ 自身が $`\beta`$ で $`\Phi_{m+1}`$ を満たすことを示す
3. 「$`z`$ より上に $`\Phi_{m+1}`$ を満たす点がある」を $`\alpha`$ へ戻す

## 3. 証明での使われ方

| 事実 | 使う場所 |
|---|---|
| P7′ | [05](05-finite-reflection.md) の「α で (d)」で、$`\Phi_{n-1}`$ を満たす点を $`\alpha`$ の中に非有界に取る |

## 4. Lean での対応

`cof_of_lab j h` の仮定 `lab N (j + 1) α β` は $`\alpha \lt_{j+2} \beta`$、結論 `Cof N i α` は $`\mathrm{Cof}_{i+1}(\alpha)`$ である。

| 概念 | Lean | ファイル |
|---|---|---|
| $`\alpha \gt 0`$ | `pos_of_lab` | [`Pattern/General.lean`](../../lean/Pattern/General.lean) |
| P7′ | `cof_of_lab` | 同上 |
| $`\tau`$ の否定、段階 E の文 | `sig_forall_exists_phi`, `sig_exists_phi` | 同上 |
| P5、P6、P7 | `succ_lt_of_lab0`, `succ_lt_of_lab1_top`, `exists_lev0_below` | [`Pattern/Basic.lean`](../../lean/Pattern/Basic.lean) |
