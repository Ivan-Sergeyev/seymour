# Seymour's Matroid Decomposition Theorem Verification

Seymour's decomposition theorem is a hallmark result in matroid theory that gives a structural characterization of the class of regular matroids. The aim of this project is to formally verify the proof of this theorem in Lean 4. [This file](Seymour.lean) contains a formally verified summary of our main results together with the key definitions they depend on. Currently, we formalized the statement of the theorem and the proof of its forward (composition) direction for matroids of finite rank and with potentially infinite ground sets. In the future, we would like to also formalize the proof of the backward (decomposition) direction, which we stated in [this file](Seymour/Results/HardDirection.lean).

## Blueprint

You can find the blueprint of our formalization on the [GitHub Pages site](https://ivan-sergeyev.github.io/seymour/). The blueprint serves as an overview of the theoretical results underpinning the formalization, as well as the documentation of our implementation. The blueprint is also presented visually in the [dependency graph](https://ivan-sergeyev.github.io/seymour/blueprint/dep_graph_document.html).

## How to Get Involved

In case you want to contribute to our project, you can read the [contribution guidelines](CONTRIBUTING.md). We use [GitHub Issues](https://github.com/Ivan-Sergeyev/seymour/issues) for tracking tasks, and the issues we think could be a good fit for newcomers are labeled with `good first issue`. Feel free to reach out on [Zulip](https://leanprover.zulipchat.com/#narrow/channel/498634-Seymour) in case you have questions.

## Timeline

- 2024-10-15 project announced
- 2025-03-24 finished proof that every vector matroid is a matroid
- 2025-05-17 finished proof that the 2-sum of regular matroids is a regular matroid
- 2025-07-05 finished proof that the 3-sum of regular matroids is a regular matroid

## References

- [K. Truemper – Matroid Decomposition](https://www2.math.ethz.ch/EMIS/monographs/md/)
- [J. Oxley – Matroid Theory](https://doi.org/10.1093/acprof:oso/9780198566946.001.0001)
- H. Bruhn, R. Diestel, M. Kriesell, R. Pendavingh, P. Wollan – Axioms for infinite matroids ([arxiv](https://arxiv.org/abs/1003.3919), [paper](https://doi.org/10.1016/j.aim.2013.01.011))

## Used Tools and Projects

- [Mathlib](https://github.com/leanprover-community/mathlib4)
- [LeanProject](https://github.com/pitmonticone/LeanProject)
- [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
- [doc-gen4](https://github.com/leanprover/doc-gen4)
