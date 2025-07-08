import Seymour.EasyDirection


variable {α : Type} [DecidableEq α]

/-!

# Looking into low-hanging fruit for hard direction of Seymour's theorem

## Main conclusions:

* 90% chance not viable to do in the remaining time; if feasible, then most likely only for finite matroids
* even finite case would require several weeks of work: ~2 full-focus, 3-4 more realistically

## Technical details

* Requires newer version of MathLib to work with matroid minors
* Depends on the notion of k-connectivity
  * Needs to be handled formally differently for infinite matroids, without using rank
* Depends on the notion of k-separation
  * Needs to be handled formally differently for infinite matroids, without using rank
* Depends on the splitter theorem
* Depends on Kuratowski's theorem
* Depends on Menger's theorem

## Infinite matroids

Here is what "Axioms for infinite matroids" says about generalization of Seymour's theorem to infinte matroids:

"Since our paper was first made available in preprint form [17], various authors have built
on it to extend some of the classical results of finite matroid theory to infinite matroids, or to
relate such infinite extensions to well-known conjectures outside matroid theory. Such extensions
include [...] the decomposition theorem of Cunningham–Edmonds and Seymour [19,44,4,11], [...]."

References:

[17] H. Bruhn, R. Diestel, M. Kriesell, R. Pendavingh, P. Wollan, Axioms for infinite matroids (2010). arXiv:1003.3919.

[19] W.H. Cunningham, J. Edmonds, A combinatorial decomposition theory, Canad. J. Math. 32 (3) (1980) 734–765.
[44] P.D. Seymour, Decomposition of regular matroids, J. Combin. Theory Ser. B 28 (3) (1980) 305–359.
[4] E. Aigner-Horev, R. Diestel, L. Postle, The structure of 2-separations of infinite matroids (2012). arXiv:1201.1135.
[11] N. Bowler, J. Carmesin, Ubiquity of Ψ-matroids (in preparation).

From a quick glance:
* [19] and [44] are classical book references, only [4] and [11] came out after the paper
* [4] deals with Cunningham–Edmonds theorem, looks like a partial result, slightly different focus (full decomposition tree)
* [11] seems relevant, but it says "it's complicated" and is more difficult to parse in terms of notation

-/

/-!

## Old blueprint about hard direction of Seymour's decomposition theorem

\subsection{Chapter 11.3}

The goal of the chapter is to prove the ``hard'' direction of the regular matroid decomposition theorem.

\begin{proposition}[11.3.3]
  \label{prop:11.3.3}
  \uses{prop:10.2.8}
  Graph plus $T$ set representing $R_{10}$
\end{proposition}

\begin{proposition}[11.3.5]
  \label{prop:11.3.5}
  \uses{prop:10.2.4}
  Graph plus $T$ set representing $F_{7}$.
\end{proposition}

\begin{proposition}[11.3.11]
  \label{prop:11.3.11}
  \uses{prop:9.2.14}
  The binary representation matrix $B^{12}$ for $R_{12}$.
\end{proposition}

\begin{theorem}[11.3.2]
  \label{thm:11.3.2}
  \uses{def:regular_matroid,def:R10,def:splitter}
  $R_{10}$ is a splitter of the class of regular matroids.

  In short: up to isomorphism, the only $3$-connected regular matroid with $R_{10}$ minor is $R_{10}$.
\end{theorem}

\begin{proof}[Proof sketch]
  \uses{thm:7.2.1.a,prop:11.3.3,def:isomorphism,def:1_elem_ext,prop:11.3.5,def:F7,def:contraction} % thm:11.3.1 = thm:7.2.1
  \begin{itemize}
    \item Splitter theorem case (a)
    \item $R_{10}$ is self-dual, so it suffices to consider $1$-element additions.
    \item Represent $R_{10}$ by (11.3.3)
    \item Up to isomorphism, there are only $3$ distinct $3$-connected $1$-element extensions.
    \item Case 1 (graphic): contract a certain edge, the resulting graph contains a subdivision of (11.3.5), which represents $F_{7}$. Thus, this extension is nonregular.
    \item Cases 2, 3 (nongraphic): reduce instances to (11.3.5), same conclusion.
  \end{itemize}
\end{proof}

\begin{theorem}[11.3.10]
  \label{thm:11.3.10}
  \uses{cor:6.3.24,def:R12}
  In short: Restatement of \ref{cor:6.3.24} for $R_{12}$.
  Replacements: $\M$ is the class of regular matroids, $N$ is $R_{12}$, (6.3.12) is (11.3.6), (6.3.21-23) are (11.3.7-9).
\end{theorem}

\begin{theorem}[11.3.12]
  \label{thm:11.3.12}
  \uses{def:regular_matroid,def:R12,def:minor,def:k_sep,prop:11.3.11,def:isomorphism}
  Let $M$ be a regular matroid with $R_{12}$ minor. Then any $3$-separation of that minor corresponding to the $3$-separation $(X_{1} \cup Y_{1}, X_{2} \cup Y_{2})$ of $R_{12}$ (see (11.3.11) -- matrix $B^{12}$ for $R_{12}$ defining the $3$-separation) under one of the isomorphisms induces a $3$-separation of $M$.

  In short: every regular matroid with $R_{12}$ minor is a $3$-sum of two proper minors.
\end{theorem}

\begin{proof}[Proof sketch]
  \uses{def:1_elem_ext,prop:10.2.9,thm:11.3.10}
  \begin{itemize}
    \item Preparation: calculate all $3$-connected regular $1$-element additions of $R_{12}$. This involves somewhat tedious case checking. (Representation of $R_{12}$ in (10.2.9) helps a lot.) By the symmetry of $B^{12}$ and thus by duality, this effectively gives all $3$-connected $1$-element extensions as well.
    \item Verify conditions of theorem 11.3.10 (which implies the result).
    \item (11.3.7) and (11.3.9) are ruled out immediately from preparatory calculations.
    \item The rest is case checking ((c.1) and (c.2)), simpified by preparatory calculations.
  \end{itemize}
\end{proof}

\begin{theorem}[11.3.14 regular matroid decomposition, easy direction]
  \label{thm:11.3.14.seymour_easy}
  \uses{def:regular_matroid,def:graphic_matroid,def:cographic_matroid,def:isomorphism,def:R10,def:1_sum,def:2_sum,def:3_sum}
  Every binary matroid produced from graphic, cographic, and matroids isomorphic to $R_{10}$ by repeated $1$-, $2$-, and $3$-sum compositions is regular.
\end{theorem}

\begin{proof}[Proof sketch]
  \uses{thm:11.2.10}
  Follows from theorem 11.2.10.
\end{proof}

\begin{theorem}[11.3.14 regular matroid decomposition, hard direction]
  \label{thm:11.3.14.seymour_hard}
  \uses{def:regular_matroid,def:graphic_matroid,def:cographic_matroid,def:isomorphism,def:R10,def:R12,def:1_sum,def:2_sum,def:3_sum,def:k_conn,def:k_sep,prop:11.3.11}
  Every regular matroid $M$ can be decomposed into graphic and cographic matroids and matroids isomorphic to $R_{10}$ by repeated $1$-, $2$-, and $3$- sum decompositions.
  Specifically: If $M$ is a regular $3$-connected matroid that is not graphic and not cographic, then $M$ is isomorphic to $R_{10}$ or has an $R_{12}$ minor. In the latter case, any $3$-separation of that minor corresponding to the 3-separation $(X_{1} \cup Y_{1}, X_{2} \cup Y_{2})$ of $R_{12}$ ((11.3.11)) under one of the isomorphisms induces a $3$-separation of $M$.
\end{theorem}

\begin{proof}[Proof sketch]
  \uses{thm:10.4.1.if,thm:11.3.2,thm:11.3.12,lem:8.3.12}
  \begin{itemize}
    \item Let $M$ be a regular matroid. Assume $M$ is not graphic and not cographic.
    \item If $M$ is $1$-separable, then it is a $1$-sum. If $M$ is $2$-separable, then it is a $2$-sum. Thus assume $M$ is $3$-connected.
    \item By theorem 10.4.1, $M$ has an $R_{10}$ or an $R_{12}$ minor.
    \item $R_{10}$ case: by theorem 11.3.2, $M$ is isomorphic to $R_{10}$.
    \item $R_{12}$ case: by theorem 11.3.12, $M$ has an induced by $3$-separation, so by lemma 8.3.12, $M$ is a $3$-sum.
  \end{itemize}
\end{proof}

-/

def Matroid.IsMinor (M N : Matroid α) : Prop := sorry
  -- issue: need to `import Mathlib.Data.Matroid.Minor.Order`, which is only available in newer version of mathlib
  -- does not exist in `import Mathlib.Data.Matroid.Minor.Basic`, which is available in current version of mathlib

/-- A matroid is $k$-connected iff ... . -/
def Matroid.IsConnectedK (M : Matroid α) (k : ℕ) : Prop := sorry

def Set.union_map_left {Z Zₗ Zᵣ : Set α} (hZ : Z = Zₗ ∪ Zᵣ) : Zₗ → Z := fun z => ⟨z.val, hZ ▸ Set.mem_union_left Zᵣ z.property⟩
def Set.union_map_right {Z Zₗ Zᵣ : Set α} (hZ : Z = Zₗ ∪ Zᵣ) : Zᵣ → Z := fun z => ⟨z.val, hZ ▸ Set.mem_union_right Zₗ z.property⟩

def Matrix.IsSeparationK {X Y : Set α} (B : Matrix X Y Z2) {Xₗ Xᵣ Yₗ Yᵣ : Set α}
    [Fintype Xₗ] [Fintype Xᵣ] [Fintype Yₗ] [Fintype Yᵣ]  -- issue: need to avoid this
    (k : ℕ) (hX : X = Xₗ ∪ Xᵣ) (hY : Y = Yₗ ∪ Yᵣ) : Prop :=
  (Xₗ ∪ Yₗ).encard ≥ k ∧ (Xᵣ ∪ Yᵣ).encard ≥ k ∧
    ((B.submatrix (Set.union_map_right hX) (Set.union_map_left hY)).rank +
     (B.submatrix (Set.union_map_left hX) (Set.union_map_right hY)).rank ≤ k - 1)

/-- Up to isomorphism, the only $3$-connected regular matroid with $R_{10}$ minor is $R_{10}$. -/
lemma splitterR10 {M : Matroid α} {f : Fin 10 → α} (hf : f.Injective)
    (hMR10 : (matroidR10.toMatroid.map f (by tauto)).IsMinor M) (hM3 : M.IsConnectedK 3) :
    ∃ e : α ≃ Fin 10, M.mapEquiv e = matroidR10.toMatroid :=
  sorry


/-! # Current version -/

/-- The hard direction of the Seymour's theorem. -/
theorem Matroid.IsRegular.isGood {M : Matroid α} (hM : M.IsRegular) : M.IsGood := by
  sorry

/-- Matroid is regular iff it can be decomposed into graphic matroids & cographics matroids & matroids isomorphic to R10
    using 1-sums & 2-sums & 3-sums. -/
theorem Matroid.isRegular_iff_isGood (M : Matroid α) : M.IsRegular ↔ M.IsGood :=
  ⟨Matroid.IsRegular.isGood, Matroid.IsGood.isRegular⟩
