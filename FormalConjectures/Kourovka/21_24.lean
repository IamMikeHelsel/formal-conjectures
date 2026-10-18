/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Problem 21.24

by D. Bubboloni, F. Fumagalli, C. E. Praeger

A graph is a *cograph* if it has no induced path on four vertices. It is *chordal* if it has no
induced cycle of length at least four.

The answer is yes, by Rundström [Ru] and independently by van Doorn, Judin, Monticone and
Morrison [vDJMM, Section 7].

*References:*
- [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v48), Problem 21.24.
- [Ru] M. Rundström, *Kourovka Notebook Problem 21.24*, solution note (2026),
  [PDF](https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/04/21.24-runds.pdf).
- [vDJMM] W. van Doorn, E. Judin, P. Monticone and D. Morrison, *On some problems from the
  Kourovka Notebook*, [arXiv:2607.17477](https://arxiv.org/abs/2607.17477).
-/

@[expose] public section

open SimpleGraph

namespace Kourovka.«21.24»

/--
The power graph $\mathcal{P}(G)$ of a group $G$: its vertex set is $G$, and distinct $x, y$ are
adjacent if $x \in \langle y \rangle$ or $y \in \langle x \rangle$.
-/
def powerGraph (G : Type*) [Group G] : SimpleGraph G :=
  SimpleGraph.fromRel fun x y ↦ x ∈ Subgroup.zpowers y

/-- A graph is a *cograph* if it has no induced path on four vertices. -/
def IsCograph {V : Type*} (Γ : SimpleGraph V) : Prop :=
  ¬ (pathGraph 4).IsIndContained Γ

/--
For a finite group $G$, the power graph $\mathcal{P}(G)$ is the graph with vertex set $G$ and
edges $\{x, y\}$ for all $x \ne y \in G$ such that either $x \in \langle y \rangle$ or
$y \in \langle x \rangle$. Is it true that, for every finite group $G$, if $\mathcal{P}(G)$ is a
cograph, then $\mathcal{P}(G)$ is chordal?
-/
@[category research solved, question, AMS 5 20,
  formal_proof using lean4 at
    "https://github.com/pitmonticone/Kourovka/blob/dcfdbdad8c434e30f6151fb3b4343364d70eeed4/Kourovka/Problem_21_24.lean#L241"]
theorem kourovka_21_24 :
    ∀ (G : Type) [Group G] [Finite G], IsCograph (powerGraph G) → (powerGraph G).IsChordal := by
  sorry

end Kourovka.«21.24»
