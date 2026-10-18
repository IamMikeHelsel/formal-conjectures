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
# Conjecture 19.25

by B. Curtin, G. R. Pourgholi

The answer is no. The simple group $\mathrm{PSU}(3, 3)$ and a non-simple group of the same order
$6048$ both have totient sum $23984$ [vDJMM, Theorem 4.1].

*References:*
- [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v48), Problem 19.25.
- [vDJMM] W. van Doorn, E. Judin, P. Monticone and D. Morrison, *On some problems from the
  Kourovka Notebook*, [arXiv:2607.17477](https://arxiv.org/abs/2607.17477).
-/

@[expose] public section

open scoped Nat Group

namespace Kourovka.«19.25»

/--
Let $G$ and $H$ be finite groups of the same order with
$\sum_{g \in G} \phi(|g|) = \sum_{h \in H} \phi(|h|)$,
where $\phi$ is the Euler totient function. Suppose that $G$ is simple. Is
$H$ necessarily simple?
-/
@[category research solved, question, AMS 20,
  formal_proof using lean4 at
    "https://github.com/pitmonticone/Kourovka/blob/dcfdbdad8c434e30f6151fb3b4343364d70eeed4/Kourovka/Problem_19_25.lean#L57-L62"]
theorem kourovka_19_25 :
    ¬ ∀ (G H : Type) [Group G] [Group H] [Fintype G] [Fintype H],
        Fintype.card G = Fintype.card H →
        ∑ g : G, φ (orderOf g) = ∑ h : H, φ (orderOf h) →
        IsSimpleGroup G → IsSimpleGroup H := by
  sorry

end Kourovka.«19.25»
