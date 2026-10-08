import Mathlib

/-!
# Lean certificate for `Collatz_cotree_density` (self-contained)

## What is certified

1. **Notebook form** (Jan's Mathematica notebook, `In[52]`), at the Collatz root `c = 4`:
   with `a = c - 1`, `v = log₂ c - 1`, `A⁻ = a² - a - 1`,
   ```
   lhs = (a³ v² + A⁻ v²) / (v · (c³/2) · (c-1)²)
   rhs = ((a-1) v) / ((c/2) · (c-1)²)
   ```
   `v = 1` at `c = 4` (`vLog_four`), `lhs = rhs = 2/18` (`notebook_lhs_four`,
   `notebook_rhs_four`), and `lhs / rhs = 1` (`cotree_collatz`).

2. **Series form** (Table 7, Eq. 3.55–3.57): the three geometric series
   * leftward:    first term 81/4608,   ratio 13/16 → 27/288
   * upward odd:  first term 1/64,      ratio 1/64  → 1/63
   * upward even: first term 27/18432,  ratio 1/64  → 1/672

   converge (as genuine infinite sums in `ℝ`) to these values, and
   27/288 + 1/63 + 1/672 = 27/288 + 5/288 = 2/18 (`hasSum_collatz_cotree`).

`collatz_cotree_density` packages both.

## Scope

This is **Lean-checked arithmetic**. Nothing here mentions the map `n ↦ 3n+1` or its
iteration: the first terms and ratios are copied from Table 7, and the notebook identity
`lhs = rhs` holds for every real `c ≠ 0, 1` and `v ≠ 0` (`cotree_lhs_eq_rhs`), because
`a³ + (a² - a - 1) = (a+1)²(a-1)` (`numerator_factor`). In particular it does not prove
that every branching number lies in the tree from `c`.

Uses only the standard axioms (`#print axioms` at the end).

Check with: `lake env lean self-contained/collatz_cotree_density.lean`
-/

namespace CollatzCotreeDensity

open Real

noncomputable section

/-! ## 1. Notebook form at c = 4 -/

/-- Jan's `lhs`, with `a = c - 1`, `A⁻ = a² - a - 1`, and `v` a parameter. -/
def lhs (c v : ℝ) : ℝ :=
  ((c - 1) ^ 3 * v ^ 2 + ((c - 1) ^ 2 - (c - 1) - 1) * v ^ 2) /
    (v * (c ^ 3 / 2) * (c - 1) ^ 2)

/-- Jan's `rhs = ((a-1) v) / ((c/2)(c-1)²)` with `a = c - 1`. -/
def rhs (c v : ℝ) : ℝ :=
  ((c - 1 - 1) * v) / (c / 2 * (c - 1) ^ 2)

/-- Jan's `v = log₂ c - 1`. -/
def vLog (c : ℝ) : ℝ := logb 2 c - 1

/-- The polynomial identity behind `lhs = rhs`: `a³ + (a² - a - 1) = (a+1)²(a-1)`. -/
theorem numerator_factor (a : ℝ) : a ^ 3 + (a ^ 2 - a - 1) = (a + 1) ^ 2 * (a - 1) := by
  ring

/-- `lhs = rhs` for every real `c ≠ 0, 1` and `v ≠ 0`: an algebraic identity. -/
theorem cotree_lhs_eq_rhs {c v : ℝ} (hv : v ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    lhs c v = rhs c v := by
  have hc1' : c - 1 ≠ 0 := sub_ne_zero.2 hc1
  unfold lhs rhs
  field_simp
  ring

/-- `v = log₂ 4 - 1 = 1`. -/
theorem vLog_four : vLog 4 = 1 := by
  unfold vLog
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, logb_pow, logb_self_eq_one (by norm_num)]
  norm_num

/-- At `c = 4`: `rhs = 2/18`, the density of the Collatz branching classes `[4, 16]₁₈`. -/
theorem notebook_rhs_four : rhs 4 (vLog 4) = 2 / 18 := by
  rw [vLog_four]; unfold rhs; norm_num

/-- At `c = 4`: `lhs = 2/18`. -/
theorem notebook_lhs_four : lhs 4 (vLog 4) = 2 / 18 := by
  rw [vLog_four]; unfold lhs; norm_num

/-- **Notebook certificate:** `lhs / rhs = 1` at `c = 4`. -/
theorem cotree_collatz : lhs 4 (vLog 4) / rhs 4 (vLog 4) = 1 := by
  rw [notebook_lhs_four, notebook_rhs_four]; norm_num

/-! ## 2. Series form (Table 7) -/

/-- Closed form `a / (1 - r)` of the geometric series `∑ a rⁿ`. -/
def geomSeriesSum (a r : ℚ) : ℚ := a / (1 - r)

/-- `∑ a rⁿ` converges to `geomSeriesSum a r` in `ℝ` when `0 ≤ r < 1`. -/
theorem hasSum_geomSeriesSum (a r : ℚ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ ↦ (a : ℝ) * (r : ℝ) ^ n) (geomSeriesSum a r : ℝ) := by
  have h := (hasSum_geometric_of_lt_one
    (by exact_mod_cast hr0 : (0 : ℝ) ≤ r)
    (by exact_mod_cast hr1 : (r : ℝ) < 1)).mul_left (a : ℝ)
  convert h using 1
  simp [geomSeriesSum]
  ring

/-- Leftward cotree series: `81/4608 / (1 - 13/16) = 27/288`. -/
theorem collatz_leftward_geom_series :
    geomSeriesSum (81 / 4608) (13 / 16) = 27 / 288 := by
  simp only [geomSeriesSum]; norm_num

/-- Upward odd cotree series: `1/64 / (1 - 1/64) = 1/63`. -/
theorem collatz_upward_odd_geom_series :
    geomSeriesSum (1 / 64) (1 / 64) = 1 / 63 := by
  simp only [geomSeriesSum]; norm_num

/-- Upward even cotree series: `27/18432 / (1 - 1/64) = 1/672`. -/
theorem collatz_upward_even_geom_series :
    geomSeriesSum (27 / 18432) (1 / 64) = 1 / 672 := by
  simp only [geomSeriesSum]; norm_num

/-- Upward total: `1/63 + 1/672 = 5/288`. -/
theorem collatz_upward_total : (1 : ℚ) / 63 + 1 / 672 = 5 / 288 := by norm_num

/-- Eq. 3.57: `27/288 + 5/288 = 2/18`. -/
theorem collatz_cotree_density_via_geom :
    geomSeriesSum (81 / 4608) (13 / 16) +
    geomSeriesSum (1 / 64) (1 / 64) +
    geomSeriesSum (27 / 18432) (1 / 64) = 2 / 18 := by
  simp only [geomSeriesSum]; norm_num

theorem hasSum_collatz_leftward :
    HasSum (fun n : ℕ ↦ (81 / 4608 : ℝ) * (13 / 16) ^ n) (27 / 288) := by
  have h := hasSum_geomSeriesSum (81 / 4608) (13 / 16) (by norm_num) (by norm_num)
  simp only [geomSeriesSum] at h
  convert h using 1 <;> push_cast <;> norm_num

theorem hasSum_collatz_upward_odd :
    HasSum (fun n : ℕ ↦ (1 / 64 : ℝ) * (1 / 64) ^ n) (1 / 63) := by
  have h := hasSum_geomSeriesSum (1 / 64) (1 / 64) (by norm_num) (by norm_num)
  simp only [geomSeriesSum] at h
  convert h using 1 <;> push_cast <;> norm_num

theorem hasSum_collatz_upward_even :
    HasSum (fun n : ℕ ↦ (27 / 18432 : ℝ) * (1 / 64) ^ n) (1 / 672) := by
  have h := hasSum_geomSeriesSum (27 / 18432) (1 / 64) (by norm_num) (by norm_num)
  simp only [geomSeriesSum] at h
  convert h using 1 <;> push_cast <;> norm_num

/-- **Series certificate:** the sum of the three Table 7 series, as an infinite sum in `ℝ`,
is `2/18`. -/
theorem hasSum_collatz_cotree :
    HasSum (fun n : ℕ ↦ (81 / 4608 : ℝ) * (13 / 16) ^ n + (1 / 64 : ℝ) * (1 / 64) ^ n +
      (27 / 18432 : ℝ) * (1 / 64) ^ n) (2 / 18) := by
  have h := (hasSum_collatz_leftward.add hasSum_collatz_upward_odd).add
    hasSum_collatz_upward_even
  convert h using 1
  norm_num

/-! ## 3. The packaged certificate -/

/-- **`Collatz_cotree_density`.** At the Collatz root `c = 4`:
* the notebook's `lhs` and `rhs` both equal `2/18`, and `lhs / rhs = 1`;
* the three Table 7 cotree series sum (in `ℝ`) to `27/288 + 1/63 + 1/672 = 2/18`. -/
theorem collatz_cotree_density :
    vLog 4 = 1 ∧
    lhs 4 (vLog 4) = 2 / 18 ∧ rhs 4 (vLog 4) = 2 / 18 ∧
    lhs 4 (vLog 4) / rhs 4 (vLog 4) = 1 ∧
    HasSum (fun n : ℕ ↦ (81 / 4608 : ℝ) * (13 / 16) ^ n) (27 / 288) ∧
    HasSum (fun n : ℕ ↦ (1 / 64 : ℝ) * (1 / 64) ^ n) (1 / 63) ∧
    HasSum (fun n : ℕ ↦ (27 / 18432 : ℝ) * (1 / 64) ^ n) (1 / 672) ∧
    (27 : ℝ) / 288 + 1 / 63 + 1 / 672 = 2 / 18 :=
  ⟨vLog_four, notebook_lhs_four, notebook_rhs_four, cotree_collatz,
    hasSum_collatz_leftward, hasSum_collatz_upward_odd, hasSum_collatz_upward_even,
    by norm_num⟩

end

end CollatzCotreeDensity

#print axioms CollatzCotreeDensity.collatz_cotree_density
#print axioms CollatzCotreeDensity.cotree_lhs_eq_rhs
#print axioms CollatzCotreeDensity.hasSum_collatz_cotree
