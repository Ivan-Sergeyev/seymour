# Matroid Decomposition Theorem Verification

The goal of this project is to formally verify Seymour's decomposition theorem for regular matroids in Lean 4.

## Abstract

Seymour's theorem is an important chapter of matroid theory. We aim to formally verify Seymour's theorem in Lean 4.
[First, we build a library for working with totally unimodular matrices.](https://github.com/Ivan-Sergeyev/seymour/blob/main/Seymour/Matrix/TotalUnimodularity.lean)
We define
[binary matroids](https://github.com/Ivan-Sergeyev/seymour/blob/019dc97f8ee0641c031dc5df01afca603b2f915e/Seymour/Matroid/FromMatrix.lean#L20)
and their
[standard representation](https://github.com/Ivan-Sergeyev/seymour/blob/019dc97f8ee0641c031dc5df01afca603b2f915e/Seymour/Matroid/StandardRepresentation.lean#L64)
and we
[prove that they form a matroid](https://github.com/Ivan-Sergeyev/seymour/blob/019dc97f8ee0641c031dc5df01afca603b2f915e/Seymour/Matroid/FromMatrix.lean#L206)
in the sense that
[Mathlib 4 defines matroids](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Data/Matroid).
[We define regular matroids to be matroids for which there exists a full representation rational matrix that is totally unimodular](https://github.com/Ivan-Sergeyev/seymour/blob/019dc97f8ee0641c031dc5df01afca603b2f915e/Seymour/Matroid/Regularity.lean#L15)
and
[we prove that all regular matroids are binary](https://github.com/Ivan-Sergeyev/seymour/blob/019dc97f8ee0641c031dc5df01afca603b2f915e/Seymour/Matroid/Regularity.lean#L294).
We define
[1-sum](https://github.com/Ivan-Sergeyev/seymour/blob/019dc97f8ee0641c031dc5df01afca603b2f915e/Seymour/Matroid/Sum1.lean#L44),
[2-sum](https://github.com/Ivan-Sergeyev/seymour/blob/019dc97f8ee0641c031dc5df01afca603b2f915e/Seymour/Matroid/Sum2.lean#L141),
and
[3-sum](https://github.com/Ivan-Sergeyev/seymour/blob/019dc97f8ee0641c031dc5df01afca603b2f915e/Seymour/Matroid/Sum3.lean#L3433)
of binary matroids as specific ways to compose their standard representation matrices. We prove that the
[1-sum](https://github.com/Ivan-Sergeyev/seymour/blob/019dc97f8ee0641c031dc5df01afca603b2f915e/Seymour/Matroid/Sum1.lean#L213), 
the
[2-sum](https://github.com/Ivan-Sergeyev/seymour/blob/019dc97f8ee0641c031dc5df01afca603b2f915e/Seymour/Matroid/Sum2.lean#L394),
and the
[3-sum](https://github.com/Ivan-Sergeyev/seymour/blob/019dc97f8ee0641c031dc5df01afca603b2f915e/Seymour/Matroid/Sum3.lean#L3457)
of regular matroids are a regular matroid.
[This concludes the composition direction of the Seymour's theorem.](https://github.com/Ivan-Sergeyev/seymour/blob/main/Seymour.lean)

## Timeline

- 2024-10-15 project announced
- 2025-03-24 finished proof that every vector matroid is a matroid
- 2025-05-17 finished proof that the 2-sum of regular matroids is a regular matroid
- 2025-07-05 finished proof that the 3-sum of regular matroids is a regular matroid

## Blueprint

- You can find the blueprint on the [GitHub Pages site](https://ivan-sergeyev.github.io/seymour/)
- Quick link to the [dependency graph](https://ivan-sergeyev.github.io/seymour/blueprint/dep_graph_document.html)

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
