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
# Wormald's conjecture on isomorphic linear forests

A *linear forest* is a forest in which every component is a path. Akiyama, Exoo and Harary
showed that the edges of every cubic graph can be partitioned into two linear forests. Wormald
conjectured that for cubic graphs whose order is divisible by $4$ the two linear forests can be
taken isomorphic [Wo].

Schreib [Sc] disproved the conjecture with a disconnected cubic graph on $16$ vertices: the
disjoint union of $K_{3,3}$ with a $10$-vertex graph built from two copies of $K_4$, each with one
edge subdivided, joined by a bridge between the two subdivision vertices. Adding $t$ disjoint
copies of $K_4$ gives counterexamples of order $16 + 4t$ for every $t \ge 0$.

The conjecture remains open for connected cubic graphs. Kronenberg, Letzter, Pokrovskiy and
Yepremyan [KLPY] proved it for all sufficiently large connected cubic graphs.

*References:*
- [Wo] N. Wormald, *Problem 13*, Ars Combinatoria 23(A) (1987), 332–334.
- [Sc] J. A. Schreib, *A counterexample to Wormald's conjecture*,
  [arXiv:2610.00086](https://arxiv.org/abs/2610.00086).
- [KLPY] G. Kronenberg, S. Letzter, A. Pokrovskiy and L. Yepremyan, *Decomposing cubic graphs into
  isomorphic linear forests*, [arXiv:2210.11458](https://arxiv.org/abs/2210.11458).
-/

@[expose] public section

open SimpleGraph

namespace WormaldConjecture

/-- $F$ is a *linear forest*: it is acyclic and every vertex has degree at most $2$. -/
def IsLinearForest {V : Type*} (F : SimpleGraph V) : Prop :=
  F.IsAcyclic ∧ ∀ v, (F.neighborSet v).encard ≤ 2

/-- The edges of $G$ can be partitioned into two isomorphic spanning linear forests. -/
def HasIsomorphicLinearForestPartition {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ R B : SimpleGraph V, R ⊔ B = G ∧ Disjoint R B ∧ IsLinearForest R ∧ IsLinearForest B ∧
    Nonempty (R ≃g B)

/-- The empty graph is a linear forest. -/
@[category test, AMS 5]
theorem isLinearForest_bot (V : Type*) : IsLinearForest (⊥ : SimpleGraph V) :=
  ⟨isAcyclic_bot, fun v ↦ by simp⟩

/--
Wormald's conjecture: the edges of every cubic graph whose order is divisible by $4$ can be
partitioned into two isomorphic linear forests. This is false [Sc].
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/jamesschreib/wormald-conjecture/blob/8c099877a6a232e5877db9d91ee358a3a01d8139/formalization.lean#L83-L85"]
theorem wormald_conjecture :
    ¬ ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree 3 → 4 ∣ Fintype.card V → HasIsomorphicLinearForestPartition G := by
  sorry

/--
For every $t \ge 0$ there is a cubic graph on $16 + 4t$ vertices whose edges cannot be partitioned
into two isomorphic linear forests [Sc, Corollary 6.1].
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/jamesschreib/wormald-conjecture/blob/8c099877a6a232e5877db9d91ee358a3a01d8139/Family.lean#L224-L230"]
theorem wormald_conjecture.variants.family (t : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      Fintype.card V = 16 + 4 * t ∧ G.IsRegularOfDegree 3 ∧
        ¬ HasIsomorphicLinearForestPartition G := by
  sorry

/--
The connected case of Wormald's conjecture: the edges of every connected cubic graph whose order
is divisible by $4$ can be partitioned into two isomorphic linear forests.
-/
@[category research open, AMS 5]
theorem wormald_conjecture.variants.connected :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → G.IsRegularOfDegree 3 → 4 ∣ Fintype.card V →
        HasIsomorphicLinearForestPartition G := by
  sorry

end WormaldConjecture
