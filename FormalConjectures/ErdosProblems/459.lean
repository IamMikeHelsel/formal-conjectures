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
# Erdős Problem 459

*References:*
- [erdosproblems.com/459](https://www.erdosproblems.com/459)
- [ErGr80] P. Erdős and R. L. Graham, *Old and new problems and results in combinatorial number
  theory*, Monographies de L'Enseignement Mathématique 28 (1980), p.91.
- [OEIS A289280](https://oeis.org/A289280)
-/

@[expose] public section

namespace Erdos459

/--
The function from the problem, in its equivalent form: `f u` is the smallest `v > u` all of whose
prime factors divide `u`. (Equivalently, `f u` is the largest `v` such that no `m ∈ (u, v)` is
composed entirely of primes dividing `u * v`.)
-/
noncomputable def f (u : ℕ) : ℕ := sInf {v | u < v ∧ v.primeFactors ⊆ u.primeFactors}

/--
Let $f(u)$ be the largest $v$ such that no $m\in (u,v)$ is composed entirely of primes dividing
$uv$. Estimate $f(u)$.

The estimate $u + 2 \le f(u) \le u^2$ holds for every $u \ge 2$. The upper bound is attained
when $u$ is prime, and the lower bound when $u = 2^k - 2$ with $k \ge 2$; Cambie further showed
that $f(n) = (1 + o(1))n$ for almost all $n$.
-/
@[category research solved, AMS 11]
theorem erdos_459 {u : ℕ} (hu : 2 ≤ u) : u + 2 ≤ f u ∧ f u ≤ u ^ 2 := by
  have hmem : u ^ 2 ∈ {v | u < v ∧ v.primeFactors ⊆ u.primeFactors} :=
    ⟨by nlinarith, by rw [Nat.primeFactors_pow _ two_ne_zero]⟩
  refine ⟨le_csInf ⟨_, hmem⟩ ?_, Nat.sInf_le hmem⟩
  rintro v ⟨hv, hsub⟩
  by_contra! h
  obtain rfl : v = u + 1 := by omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show u + 1 ≠ 1 by omega)
  have hpu : p ∣ u :=
    Nat.dvd_of_mem_primeFactors (hsub (Nat.mem_primeFactors.2 ⟨hp, hpd, by omega⟩))
  have : p ∣ 1 := (Nat.dvd_add_right hpu).1 hpd
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

/--
The upper bound $f u ≤ u ^ 2$ is attained exactly when `u` is prime: $f p = p ^ 2$.
-/
@[category research solved, AMS 11]
theorem erdos_459.variants.upper_tight {p : ℕ} (hp : p.Prime) : f p = p ^ 2 := by
  have hmem : p ^ 2 ∈ {v | p < v ∧ v.primeFactors ⊆ p.primeFactors} :=
    ⟨by nlinarith [hp.two_le], by rw [Nat.primeFactors_pow _ two_ne_zero]⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
  rintro v ⟨hv, hsub⟩
  have hv0 : v ≠ 0 := by omega
  rw [hp.primeFactors] at hsub
  have hvp := Nat.eq_prime_pow_of_unique_prime_dvd hv0
    fun {d} hd hdv => by simpa using hsub (Nat.mem_primeFactors.2 ⟨hd, hdv, hv0⟩)
  obtain ⟨k, rfl⟩ : ∃ k, v = p ^ k := ⟨_, hvp⟩
  have : 1 < k := by
    by_contra! h
    interval_cases k <;> simp at hv
    exact hp.ne_zero hv
  exact Nat.pow_le_pow_right hp.pos this

end Erdos459
