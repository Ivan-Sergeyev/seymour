# Matroid Decomposition Theorem Verification

The goal of this project is to formally verify Seymour's decomposition theorem for regular matroids in Lean 4.

## Blueprint

- You can find the blueprint on the [GitHub Pages site](https://ivan-sergeyev.github.io/seymour/)
- Quick link to the [dependency graph](https://ivan-sergeyev.github.io/seymour/blueprint/dep_graph_document.html)

## Timeline

- 2024-10-15 project announced
- 2025-03-24 finished proof that every vector matroid is a matroid
- 2025-05-17 finished proof that the 1-sum of regular matroids is a regular matroid, dtto 2-sum
- 2025-07-05 finished proof that the 3-sum of regular matroids is a regular matroid

## References

- [K. Truemper – Matroid Decomposition](https://www2.math.ethz.ch/EMIS/monographs/md/)
- [J. Oxley – Matroid Theory](https://doi.org/10.1093/acprof:oso/9780198566946.001.0001)
- [J. Geelen, B. Gerards – Regular matroid decomposition via signed graphs](https://www.math.uwaterloo.ca/~jfgeelen/Publications/regular.pdf)
- S. R. Kingan - On Seymour's decomposition theorem ([arxiv](https://arxiv.org/abs/1403.7757), [paper](https://doi.org/10.1007/s00026-015-0261-1))
- H. Bruhn et al. - Axioms for infinite matroids ([arxiv](https://arxiv.org/abs/1003.3919), [paper](https://doi.org/10.1016/j.aim.2013.01.011))

## Used tools and projects

- Imports [Mathlib](https://github.com/leanprover-community/mathlib4) library
- Uses [LeanProject](https://github.com/pitmonticone/LeanProject) template
- Uses [Leanblueprint](https://github.com/PatrickMassot/leanblueprint) tool
- Uses [doc-gen4](https://github.com/leanprover/doc-gen4) library
