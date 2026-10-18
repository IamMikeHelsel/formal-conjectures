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
# Erdős Problem 790

Let $l(n)$ be the largest size of a sum-free subset guaranteed in every set of $n$ integers.
Erdős observed that $l(n) \geq (n/2)^{1/2}$. Choi, Komlós and Szemerédi [CKS75] proved
$(n \log n / \log\log n)^{1/2} \ll l(n) \ll n / \log n$, which answers the first question, and
conjectured $l(n) \geq n^{1-o(1)}$. Korsky [Ko26] proved $l(n) \gg n / (\log n)^2$, which
answers both questions: the first with yes and the second with no.

*References:*
- [erdosproblems.com/790](https://www.erdosproblems.com/790)
- [Er65] Erdős, P., *Extremal problems in number theory*. Proc. Sympos. Pure Math., Vol. VIII
  (1965), 181--189.
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
  combinatorial theory (1973), 117--138.
- [CKS75] Choi, S. L. G., Komlós, J. and Szemerédi, E., *On sum-free subsequences*. Trans. Amer.
  Math. Soc. (1975), 307--313.
- [Ko26] Korsky, S., *Large Sum-Free Subsets of Sets of Integers* (2026).
  [Proof claim](https://www.erdosproblems.com/forum/thread/790/proof-claims).
-/

@[expose] public section

open Filter

open scoped Asymptotics Finset

namespace Erdos790

/-- A finite set $B$ of integers is sum-free (in the sense of this problem) if there is no
solution to $a_1 = a_2 + \cdots + a_r$ with all $a_i \in B$ distinct. That is, no element of $B$
is the sum of two or more other distinct elements of $B$. -/
def IsSumFree (B : Finset ℤ) : Prop :=
  ∀ b ∈ B, ∀ S ⊆ B.erase b, 2 ≤ #S → ∑ x ∈ S, x ≠ b

/-- $l(n)$ is maximal such that every set $A \subseteq \mathbb{Z}$ with $\lvert A\rvert = n$
contains a sum-free subset $B$ with $\lvert B\rvert \geq l(n)$. -/
noncomputable def l (n : ℕ) : ℕ :=
  sSup {m | ∀ A : Finset ℤ, #A = n → ∃ B ⊆ A, IsSumFree B ∧ m ≤ #B}

/--
Let $l(n)$ be maximal such that if $A\subset\mathbb{Z}$ with $\lvert A\rvert=n$ then there
exists a sum-free $B\subseteq A$ with $\lvert B\rvert \geq l(n)$. Is it true that
$l(n)n^{-1/2}\to \infty$? Is it true that $l(n)< n^{1-c}$ for some $c>0$?

The answers are yes and no, by Korsky [Ko26].
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/JENW1N/erdos790-lean/blob/ca7ef62267bb255b709fb4b67caa7d8db4d9f248/Erdos790/Main.lean#L300"]
theorem erdos_790 :
    Tendsto (fun n ↦ (l n : ℝ) / √n) atTop atTop ∧
      ¬ ∃ c > (0 : ℝ), ∀ᶠ n in atTop, (l n : ℝ) < (n : ℝ) ^ (1 - c) := by
  sorry

/-- Is it true that $l(n)n^{-1/2}\to \infty$? The answer is yes. This was first proved by Choi,
Komlós and Szemerédi [CKS75]. -/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/JENW1N/erdos790-lean/blob/ca7ef62267bb255b709fb4b67caa7d8db4d9f248/Erdos790/Main.lean#L254"]
theorem erdos_790.parts.i :
    Tendsto (fun n ↦ (l n : ℝ) / √n) atTop atTop := by
  sorry

/-- Is it true that $l(n)< n^{1-c}$ for some $c>0$? The answer is no, by Korsky [Ko26]. -/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/JENW1N/erdos790-lean/blob/ca7ef62267bb255b709fb4b67caa7d8db4d9f248/Erdos790/Main.lean#L269"]
theorem erdos_790.parts.ii :
    ¬ ∃ c > (0 : ℝ), ∀ᶠ n in atTop, (l n : ℝ) < (n : ℝ) ^ (1 - c) := by
  sorry

/-- Estimate $l(n)$. The order of growth of $l(n)$ is not known. -/
def erdos_790.variants.estimate.answer : ℕ → ℝ := sorry

/-- Estimate $l(n)$. This is interpreted here as asking for $\Theta(l(n))$. -/
@[category research open, question value, AMS 5]
theorem erdos_790.variants.estimate :
    (fun n ↦ (l n : ℝ)) =Θ[atTop] erdos_790.variants.estimate.answer := by
  sorry

/-- Choi, Komlós and Szemerédi [CKS75] proved $l(n) \ll n / \log n$. -/
@[category research solved, AMS 5]
theorem erdos_790.variants.isBigO_div_log :
    (fun n ↦ (l n : ℝ)) =O[atTop] fun n ↦ n / Real.log n := by
  sorry

/-- Korsky [Ko26] proved that $l(n) \geq c n / (\log n)^2$ for some $c > 0$ and all
$n \geq 2$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/JENW1N/erdos790-lean/blob/ca7ef62267bb255b709fb4b67caa7d8db4d9f248/Erdos790/Main.lean#L181"]
theorem erdos_790.variants.korsky :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 2 ≤ n → c * n / Real.log n ^ 2 ≤ l n := by
  sorry

/-- Choi, Komlós and Szemerédi [CKS75] conjectured that $l(n) \geq n^{1-o(1)}$. This follows
from `erdos_790.variants.korsky`. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/JENW1N/erdos790-lean/blob/ca7ef62267bb255b709fb4b67caa7d8db4d9f248/Erdos790/Main.lean#L229"]
theorem erdos_790.variants.cks_conjecture (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 - ε) ≤ l n := by
  sorry

end Erdos790
