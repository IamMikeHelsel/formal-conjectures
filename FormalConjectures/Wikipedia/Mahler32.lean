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
# Mahler's 3/2 Problem

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Mahler%27s_3/2_problem)
-/

@[expose] public section

namespace Mahler32

/-- For a real number `α`, define `Ω(α)` as
$$
\Omega (\alpha )=\inf _{\theta > 0}\left({\limsup _{n\rightarrow \infty }\left\lbrace
{\theta \alpha ^{n}}\right\rbrace -\liminf _{n\rightarrow \infty }\left\lbrace {\theta \alpha ^{n}}\right\rbrace }\right).
$$
-/
noncomputable def Ω (α : ℝ) : ℝ :=
  sInf {Filter.atTop.limsup (fun n ↦ Int.fract (θ * α ^ n))
    - Filter.atTop.liminf (fun n ↦ Int.fract (θ * α ^ n)) | (θ : ℝ) (_ : 0 < θ)}

/-- The **Mahler Conjecture** states that there are no Z-numbers. -/
@[category research open, AMS 11]
theorem mahler_conjecture (x : ℝ) (hx : IsZNumber x) : False := by
  sorry

open Filter in
/-- Mahler's conjecture would follow if `Ω(3/2)` exceeded `1/2`: a Z-number `x` has all
fractional parts `{x (3/2)^n}` below `1/2`, so `Ω(3/2) ≤ 1/2`. -/
@[category textbook, AMS 11]
theorem mahler_conjecture.variants.consequence (H : 1 / 2 < Ω (3 / 2)) :
    type_of% mahler_conjecture := by
  intro x hx
  obtain ⟨hx0, hxn⟩ := hx
  have hbdd : ∀ θ : ℝ, IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ ↦ Int.fract (θ * (3 / 2 : ℝ) ^ n)) ∧
      IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ ↦ Int.fract (θ * (3 / 2 : ℝ) ^ n)) := fun θ =>
    ⟨isBoundedUnder_of ⟨1, fun n => (Int.fract_lt_one _).le⟩,
      isBoundedUnder_of ⟨0, fun n => Int.fract_nonneg _⟩⟩
  have hΩ : Ω (3 / 2) ≤ atTop.limsup (fun n ↦ Int.fract (x * (3 / 2 : ℝ) ^ n))
      - atTop.liminf (fun n ↦ Int.fract (x * (3 / 2 : ℝ) ^ n)) := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro _ ⟨θ, -, rfl⟩
      exact sub_nonneg.2 (liminf_le_limsup (hbdd θ).1 (hbdd θ).2)
    · exact ⟨x, hx0, rfl⟩
  have h1 : atTop.limsup (fun n ↦ Int.fract (x * (3 / 2 : ℝ) ^ n)) ≤ 1 / 2 := by
    apply limsup_le_of_le (hbdd x).2.isCoboundedUnder_le
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hxn n hn).le
  have h2 : 0 ≤ atTop.liminf (fun n ↦ Int.fract (x * (3 / 2 : ℝ) ^ n)) := by
    apply le_liminf_of_le (hbdd x).1.isCoboundedUnder_ge
    exact Eventually.of_forall fun n => Int.fract_nonneg _
  linarith

/-- Flatto, Lagarias and Pollington proved that for all rational `p/q > 1` in lowest terms with
`q ≥ 2`, we have `Ω(p/q) ≥ 1/p`: for every `θ > 0`, the limit points of `{θ (p/q)^n}` are not
contained in any interval of length less than `1/p`. -/
@[category research solved, AMS 11]
theorem mahler_conjecture.variants.flatto_lagarias_pollington (p q : ℕ) (hq : 1 < q)
    (hpq : p.Coprime q) (hpq' : q < p) : 1 / p ≤ Ω (p / q) := by
  sorry

end Mahler32
