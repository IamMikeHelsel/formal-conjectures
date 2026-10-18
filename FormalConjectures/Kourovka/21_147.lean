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
# Problem 21.147

by V. M. Kopytov, N. Ya. Medvedev; communicated by A. V. Zenkov

A *right ordering* of a group $G$ is a total order $\le$ on $G$ such that $a \le b$ implies
$ac \le bc$ for all $a, b, c \in G$. A group is *right-orderable* if it has a right ordering.

The answer is no. The integer Heisenberg group has two right-relatively convex subgroups whose
join is not right-relatively convex [vDJMM, Theorem 8.1].

*References:*
- [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v48), Problem 21.147.
- [vDJMM] W. van Doorn, E. Judin, P. Monticone and D. Morrison, *On some problems from the
  Kourovka Notebook*, [arXiv:2607.17477](https://arxiv.org/abs/2607.17477).
-/

@[expose] public section

namespace Kourovka.«21.147»

/-- The linear order `o` on the group $G$ is a right ordering. -/
def IsRightOrdering {G : Type*} [Group G] (o : LinearOrder G) : Prop :=
  ∀ a b c : G, o.le a b → o.le (a * c) (b * c)

/-- The group $G$ is right-orderable. -/
def IsRightOrderable (G : Type*) [Group G] : Prop :=
  ∃ o : LinearOrder G, IsRightOrdering o

/--
A subgroup $H$ of a group $G$ is *right-relatively convex* if it is convex under some right
ordering of $G$.
-/
def IsRightRelativelyConvex {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ o : LinearOrder G, IsRightOrdering o ∧
    ∀ a ∈ H, ∀ b ∈ H, ∀ c : G, o.le a c → o.le c b → c ∈ H

/-- The trivial subgroup of a right-orderable group is right-relatively convex. -/
@[category test, AMS 6 20]
theorem isRightRelativelyConvex_bot {G : Type*} [Group G] (hG : IsRightOrderable G) :
    IsRightRelativelyConvex (⊥ : Subgroup G) := by
  obtain ⟨o, ho⟩ := hG
  refine ⟨o, ho, fun a ha b hb c hac hcb ↦ ?_⟩
  rw [Subgroup.mem_bot] at ha hb ⊢
  subst ha hb
  exact o.le_antisymm _ _ hcb hac

/--
A subgroup $H$ of a right-orderable group $G$ is said to be right-relatively convex if it is
convex under some right ordering on $G$. Is the lattice of right-relatively convex subgroups of a
right-orderable group always a sublattice of the lattice of its subgroups?
-/
@[category research solved, question, AMS 6 20,
  formal_proof using lean4 at
    "https://github.com/pitmonticone/Kourovka/blob/dcfdbdad8c434e30f6151fb3b4343364d70eeed4/Kourovka/Problem_21_147.lean#L437-L441"]
theorem kourovka_21_147 :
    ¬ ∀ (G : Type) [Group G], IsRightOrderable G →
      ∀ H K : Subgroup G, IsRightRelativelyConvex H → IsRightRelativelyConvex K →
        IsRightRelativelyConvex (H ⊓ K) ∧ IsRightRelativelyConvex (H ⊔ K) := by
  sorry

end Kourovka.«21.147»
