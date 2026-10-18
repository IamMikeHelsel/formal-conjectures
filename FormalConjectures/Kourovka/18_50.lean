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
# Problem 18.50

by S. Kohl

The answer is yes [vDJMM, Theorem 3.1].

*References:*
- [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v48), Problem 18.50.
- S. Kohl, [MathOverflow question 123890](https://mathoverflow.net/q/123890).
- [vDJMM] W. van Doorn, E. Judin, P. Monticone and D. Morrison, *On some problems from the
  Kourovka Notebook*, [arXiv:2607.17477](https://arxiv.org/abs/2607.17477).
-/

@[expose] public section

open scoped Nat

namespace Kourovka.«18.50»

/--
Let $n \in \mathbb{N}$. Is it true that for every $k \in \{1, \dots, n!\}$ there is some group $G$
and pairwise distinct elements $g_1, \dots, g_n \in G$ such that the set
$\{g_{\sigma(1)} \cdots g_{\sigma(n)} \mid \sigma \in S_n\}$ of all products of the $g_i$ obtained
by permuting the factors has cardinality $k$?
-/
@[category research solved, question, AMS 20,
  formal_proof using lean4 at
    "https://github.com/pitmonticone/Kourovka/blob/dcfdbdad8c434e30f6151fb3b4343364d70eeed4/Kourovka/Problem_18_50.lean#L329-L332"]
theorem kourovka_18_50 :
    ∀ n k : ℕ, 1 ≤ k → k ≤ n ! →
      ∃ (G : Type) (_ : Group G) (g : Fin n → G), g.Injective ∧
        (Set.range fun σ : Equiv.Perm (Fin n) ↦ (List.ofFn fun i ↦ g (σ i)).prod).ncard = k := by
  sorry

end Kourovka.«18.50»
