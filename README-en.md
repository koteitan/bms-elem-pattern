[English](README-en.md) | [Japanese](README.md)

# Termination Proof of the Pair Sequence System via Σ₂-Elementary Substructures

We prove in Lean 4 that every expansion of the pair sequence system eventually terminates.
The labels are related by Carlson's structure R2 (the relations of Σ₁- and Σ₂-elementary substructure between ordinals).
Using R3 (up to Σ₃), the proof is extended to the trio sequence system.

- Overview of the pair sequence proof: [proof/README-en.md](proof/README-en.md)
- Extension to trio sequences: [proof/en/TSS.md](proof/en/TSS.md)
- Lean sources: [lean/](lean/)

## References

### The Bashicu matrix system and its termination

1. Bashicu, 「BASIC言語による巨大数のまとめ」 (A summary of large numbers in BASIC), Googology Wiki (Japanese). [page](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0%3ABashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81#%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E6%95%B0%28Bashicu_matrix_number%29)
2. P進大好きbot, 「ペア数列の停止性」 (Termination of the pair sequence system), Googology Wiki (Japanese) (2018). [page](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0%3AP%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7)
3. R. Hunter, "Well-Orderedness of the Bashicu Matrix System", arXiv:2307.04606 (2023). [arXiv](https://arxiv.org/abs/2307.04606)
4. DH, 「Bashicu Matrix System ver. 4 の停止性と展開関係の整礎性」 (Termination of Bashicu Matrix System ver. 4 and well-foundedness of its expansion relation), Googology Wiki (Japanese) (2026). [paper PDF](https://googology.fandom.com/ja/wiki/%E3%83%95%E3%82%A1%E3%82%A4%E3%83%AB%3ABM4%28%E4%BD%9C%E6%88%90%E8%80%85%E6%83%85%E5%A0%B1%E4%BB%98%E3%81%8D%29.pdf), [announcement blog post](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0%3ADeltaEta22223/BM4%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7%E8%A8%BC%E6%98%8E)
5. koteitan, dh-bms-wf-formal (a Lean 4 formalization of 4). [GitHub](https://github.com/koteitan/dh-bms-wf-formal). The directory `lean/Bm4/` of this repository is copied from it.

### Well-ordering of Y sequences

6. Phyrion, 「0-Y 与 BMS：可逆性、序同构及良序性」 (0-Y and BMS: invertibility, order isomorphism and well-ordering; well-ordering of 0-Y with a Lean 4 formalization). [GitHub](https://github.com/Phyrion1343/0Y-Well-Ordering-Lean)
7. Phyrion, "Well-Ordering of the 1-Y Sequence System" (well-ordering of 1-Y with a Lean 4 formalization). [GitHub](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean)

### Elementary patterns of resemblance

8. T. J. Carlson, "Elementary Patterns of Resemblance", Annals of Pure and Applied Logic 108 (2001) 19–77. [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0168007200000403)
9. T. J. Carlson and G. Wilken, "Tracking Chains of Σ2-elementarity", Annals of Pure and Applied Logic 163 (2012) 23–67. [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0168007211001199)
10. G. Wilken, "Tracking chains revisited", Sets and Computations, World Scientific (2017) 183–220. [arXiv](https://arxiv.org/abs/1611.04348)
11. G. Wilken, "Pure patterns of order 2", Annals of Pure and Applied Logic 169 (2018) 54–82. [arXiv](https://arxiv.org/abs/1608.08421)
12. G. Wilken, "A Glimpse of Σ3-elementarity", The Legacy of Kurt Schütte, Springer (2020) 415–441. [Springer](https://link.springer.com/chapter/10.1007/978-3-030-49424-7_21)
13. G. Wilken, "Pure Σ2-elementarity beyond the core", Annals of Pure and Applied Logic 172 (2021) 103001. [DOI](https://doi.org/10.1016/j.apal.2021.103001), [arXiv](https://arxiv.org/abs/1710.01870)

### Lean

14. The mathlib Community, Mathlib. [GitHub](https://github.com/leanprover-community/mathlib4)

## License

[CC BY-SA 4.0](LICENSE)
