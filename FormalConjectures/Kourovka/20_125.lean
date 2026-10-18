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
# Problem 20.125

by V. G. Bardakov

A *Rota–Baxter operator* (of weight $1$) on a group $G$ is a map $B : G \to G$ such that
$B(g) B(h) = B(g B(g) h B(g)^{-1})$ for all $g, h \in G$ [BG].

The answer is yes. The map $(\sigma, f) \mapsto (\sigma^{-1}, s(f))$ on
$S_3 \times \mathbb{Z}^{\mathbb{N}}$, where $s$ is the left shift, is such an operator
[vDJMM, Theorem 5.1].

*References:*
- [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v48), Problem 20.125.
- [BG] V. G. Bardakov and V. Gubarev, *Rota–Baxter operators on groups*, Proc. Indian Acad. Sci.
  Math. Sci. 133 (2023), Art. No. 4.
- [vDJMM] W. van Doorn, E. Judin, P. Monticone and D. Morrison, *On some problems from the
  Kourovka Notebook*, [arXiv:2607.17477](https://arxiv.org/abs/2607.17477).
-/

@[expose] public section

namespace Kourovka.«20.125»

/-- $B$ is a Rota–Baxter operator of weight $1$ on the group $G$. -/
def IsRotaBaxter {G : Type*} [Group G] (B : G → G) : Prop :=
  ∀ g h : G, B g * B h = B (g * B g * h * (B g)⁻¹)

/-- The constant map at $1$ is a Rota–Baxter operator. -/
@[category test, AMS 20]
theorem isRotaBaxter_one (G : Type*) [Group G] : IsRotaBaxter fun _ : G ↦ (1 : G) := by
  simp [IsRotaBaxter]

/--
Does there exist a non-abelian group $G$ and a Rota–Baxter operator $B : G \to G$ such that $B$
is surjective but not injective?
-/
@[category research solved, question, AMS 20,
  formal_proof using lean4 at
    "https://github.com/pitmonticone/Kourovka/blob/dcfdbdad8c434e30f6151fb3b4343364d70eeed4/Kourovka/Problem_20_125.lean#L80-L82"]
theorem kourovka_20_125 :
    ∃ (G : Type) (_ : Group G) (B : G → G),
      (∃ a b : G, a * b ≠ b * a) ∧ IsRotaBaxter B ∧ B.Surjective ∧ ¬ B.Injective := by
  sorry

end Kourovka.«20.125»
