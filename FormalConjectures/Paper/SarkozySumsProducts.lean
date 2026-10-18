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
# Sárközy's conjecture on sums and products modulo a prime

For a prime $p$ and $A \subseteq \mathbb{F}_p$, let $A^* = (A + A) \cup (AA)$ be the set of residues
that are a sum or a product of two elements of $A$. Sárközy conjectured that there are constants
$c > 0$ and $p_0$ such that $\mathbb{F}_p^\times \subseteq A^*$ for every prime $p > p_0$ and every
$A \subseteq \mathbb{F}_p$ with $|A| > (\frac{1}{2} - c) p$ [Sá, Conjecture 65]. He also asked
whether one can take $c = \frac{1}{4} - \varepsilon$ for every $\varepsilon > 0$.

Tang [Ta] disproved the conjecture. For every prime $p \ge 5$ there is a set
$A \subseteq \mathbb{F}_p$ with $|A| = \frac{p - 1}{2}$ such that $1 \notin A^*$. Conversely,
$A + A = \mathbb{F}_p$ whenever $|A| > \frac{p}{2}$, so the threshold $\frac{1}{2}$ is sharp.

*References:*
- [Sá] A. Sárközy, *Unsolved problems in number theory*, Period. Math. Hungar. 42 (2001), 17–35.
- [Ta] Q. Tang, *A counterexample to a conjecture of Sárközy on sums and products modulo a prime*,
  [arXiv:2603.29992](https://arxiv.org/abs/2603.29992).
-/

@[expose] public section

open scoped Pointwise

namespace SarkozySumsProducts

/--
Sárközy's conjecture: there exist constants $c > 0$ and $p_0$ such that, if $p > p_0$ is prime and
$A \subseteq \mathbb{F}_p$ satisfies $|A| > (\frac{1}{2} - c) p$, then
$\mathbb{F}_p^\times \subseteq (A + A) \cup (AA)$. This is false [Ta, Corollary 2.3].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/QuanyuTang/Lean-files/blob/be948aee673b520254534f45098adf09a0fa0eb7/UPNT65.lean#L686-L691"]
theorem sarkozy_conjecture :
    ¬ ∃ c > (0 : ℝ), ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ < p → ∀ A : Finset (ZMod p),
      (1 / 2 - c) * p < A.card → ∀ x : ZMod p, x ≠ 0 → x ∈ A + A ∨ x ∈ A * A := by
  sorry

/--
Sárközy asked whether, for every $\varepsilon > 0$, the conjecture holds with
$c = \frac{1}{4} - \varepsilon$. The answer is no [Ta].
-/
@[category research solved, question, AMS 11,
  formal_proof using lean4 at
    "https://github.com/QuanyuTang/Lean-files/blob/be948aee673b520254534f45098adf09a0fa0eb7/UPNT65.lean#L686-L691"]
theorem sarkozy_conjecture.variants.quarter :
    ¬ ∀ ε > (0 : ℝ), ε < 1 / 4 → ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ < p → ∀ A : Finset (ZMod p),
      (1 / 4 + ε) * p < A.card → ∀ x : ZMod p, x ≠ 0 → x ∈ A + A ∨ x ∈ A * A := by
  sorry

/--
For every prime $p \ge 5$ there is a set $A \subseteq \mathbb{F}_p$ with $|A| = \frac{p - 1}{2}$
such that $1 \notin A + A$ and $1 \notin AA$ [Ta, Theorem 2.2].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/QuanyuTang/Lean-files/blob/be948aee673b520254534f45098adf09a0fa0eb7/UPNT65.lean#L554-L555"]
theorem sarkozy_conjecture.variants.half (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ A : Finset (ZMod p), A.card = (p - 1) / 2 ∧ (1 : ZMod p) ∉ A + A ∧ (1 : ZMod p) ∉ A * A := by
  sorry

end SarkozySumsProducts
