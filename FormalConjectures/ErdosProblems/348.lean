/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 348

*References:*
- [erdosproblems.com/348](https://www.erdosproblems.com/348)
- [Ge26] Geneson, J., *Deletion thresholds and exponential examples for complete sequences*.
  [arXiv:2609.25107](https://arxiv.org/abs/2609.25107) (2026).
-/

@[expose] public section

namespace Erdos348

open Erdos348

def erdos_348.answer : Set (ℕ × ℕ) := {(m, n) : ℕ × ℕ | m < n ∧ m ≤ 1}

/--
For what values of $0 \leq m < n$ is there a complete sequence
$A = \{a_1 \leq a_2 \leq \cdots\}$ of integers such that
 1. $A$ remains complete after removing any $m$ elements, but
 2. $A$ is not complete after removing any $n$ elements.

Geneson [Ge26, Theorem 1] proved that the pairs are exactly those with $m \leq 1$.
Completeness allows finitely many exceptions, and deletions remove indexed occurrences.

A formal proof of this exact statement (formalizing Geneson's argument, including the
central-interval theorem and the extension of complete finite deletions) is linked below.
-/
@[category research solved, question value, AMS 11, formal_proof using lean4 at
  "https://github.com/IamMikeHelsel/erdos-348-lean/blob/3c73026398eeed70eb623159bfee953c965fd5c3/Solution.lean#L1114"]
theorem erdos_348 :
    { (m, n) | (m) (n) (_ : m < n) (a : ℕ → ℕ) (_ : Monotone a)
      (_ : ∀ s, s.card = m → IsAddCompleteNatSeq' (Function.updateFinset a s 0))
        (_ : ∀ t, t.card = n → ¬IsAddCompleteNatSeq' (Function.updateFinset a t 0)) } =
    erdos_348.answer := by
  sorry

end Erdos348
