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
# Problem 3.46

by B. I. Plotkin

A group is *locally soluble* if every finitely generated subgroup is soluble. A normal subgroup
is *maximal locally soluble* if it is locally soluble and is not properly contained in another
locally soluble normal subgroup. Every group has such a subgroup, by Zorn's lemma.

The answer is yes. van Doorn, Judin, Monticone and Morrison [vDJMM, Theorem 2.1] construct a
group with exactly two maximal locally soluble normal subgroups.

*References:*
- [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v48), Problem 3.46.
- [vDJMM] W. van Doorn, E. Judin, P. Monticone and D. Morrison, *On some problems from the
  Kourovka Notebook*, [arXiv:2607.17477](https://arxiv.org/abs/2607.17477).
-/

@[expose] public section

namespace Kourovka.«3.46»

/-- A group is *locally soluble* if every finitely generated subgroup is soluble. -/
def IsLocallySoluble (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG → Group.IsSolvable H

/-- Every soluble group is locally soluble. -/
@[category test, AMS 20]
theorem isLocallySoluble_of_isSolvable (G : Type*) [Group G] [Group.IsSolvable G] :
    IsLocallySoluble G :=
  fun _ _ ↦ inferInstance

/--
Does there exist a group having more than one, but finitely many maximal locally soluble normal
subgroups?
-/
@[category research solved, question, AMS 20,
  formal_proof using lean4 at
    "https://github.com/pitmonticone/Kourovka/blob/dcfdbdad8c434e30f6151fb3b4343364d70eeed4/Kourovka/Problem_3_46.lean#L2720-L2725"]
theorem kourovka_3_46 :
    ∃ (G : Type) (_ : Group G),
      {M : Subgroup G | Maximal (fun N : Subgroup G ↦ N.Normal ∧ IsLocallySoluble N) M}.Finite ∧
      1 < {M : Subgroup G | Maximal (fun N : Subgroup G ↦ N.Normal ∧ IsLocallySoluble N) M}.ncard := by
  sorry

end Kourovka.«3.46»
