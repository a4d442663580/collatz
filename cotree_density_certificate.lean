import Mathlib

/-!
# Lean certificate for `cotree_density_definitions.tex`

Certifies the three-line derivation of the cotree density test
`d(tT) = d(S_{≥0})`, with every quantity expressed in terms of `c ≥ 4`:

* `a = c - 1`, `v = log₂ c - 1`, `A⁻ = a² - a - 1`,
* `lcm_LU = v · (c³/2) · (c-1)²`, `lcm_pq = (c/2) · (c-1)²`.

## Certificates

* `line2` : `(a³v² + A⁻v²) / lcm_LU = (a-1)v / lcm_pq`.
* `line2_lhs_eq_line3_lhs`, `line2_rhs_eq_line3_rhs` : each side of line 2 rewrites to the
  corresponding side of line 3 (this is the step that cancels `v` from `lcm_LU` and uses
  `a³ + a² - a - 1 = c²(c-2)`).
* `line3` : `2(c-2) log₂(c/2) / ((c-1)² c log₂ 2) = 2(c-2)(log₂ c / log₂ 2 - 1) / ((c-1)² c)`.
* `derivation` : all three facts together.

The hypothesis `c ≥ 4` is used only to get `v ≥ 1 > 0` (so `v` cancels in `lcm_LU`) and
`c > 0` (so `log₂(c/2) = log₂ c - 1`). Uses only the standard axioms
(`#print axioms derivation` at the end).

Check with: `lake env lean cotree_density_definitions.lean`
-/

namespace CotreeDensityDefinitions

open Real

noncomputable section

/-- `a = c - 1` -/
def a (c : ℝ) : ℝ := c - 1

/-- `v = log₂(c) - 1` -/
def v (c : ℝ) : ℝ := logb 2 c - 1

/-- `A⁻ = a² - a - 1` -/
def Aminus (c : ℝ) : ℝ := a c ^ 2 - a c - 1

/-- `lcm_LU = v · c³/2 · (c-1)²` -/
def lcmLU (c : ℝ) : ℝ := v c * (c ^ 3 / 2) * (c - 1) ^ 2

/-- `lcm_pq = (c/2)(c-1)²` -/
def lcmpq (c : ℝ) : ℝ := c / 2 * (c - 1) ^ 2

/-- `A⁻ = (c-1)² - (c-1) - 1`, the second form in the definitions. -/
theorem Aminus_eq (c : ℝ) : Aminus c = (c - 1) ^ 2 - (c - 1) - 1 := rfl

/-- The key polynomial identity: `a³ + a² - a - 1 = c²(c-2)`. -/
theorem numerator_factor (c : ℝ) : a c ^ 3 + Aminus c = c ^ 2 * (c - 2) := by
  unfold Aminus a; ring

/-- `log₂(c/2) = log₂ c - 1` for `c > 0`. -/
theorem logb_half {c : ℝ} (hc : 0 < c) : logb 2 (c / 2) = logb 2 c - 1 := by
  rw [logb_div hc.ne' two_ne_zero, logb_self_eq_one one_lt_two]

/-- `v ≥ 1` when `c ≥ 4`. -/
theorem one_le_v {c : ℝ} (hc : 4 ≤ c) : 1 ≤ v c := by
  unfold v
  have h4 : logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, logb_rpow two_pos (by norm_num)]
  have : logb 2 4 ≤ logb 2 c := logb_le_logb_of_le one_lt_two (by norm_num) hc
  linarith

/-- Line 2: `(a³v² + A⁻v²) / lcm_LU = (a-1)v / lcm_pq`. -/
theorem line2 {c : ℝ} (hc : 4 ≤ c) :
    (a c ^ 3 * v c ^ 2 + Aminus c * v c ^ 2) / lcmLU c = (a c - 1) * v c / lcmpq c := by
  have hv : v c ≠ 0 := (lt_of_lt_of_le one_pos (one_le_v hc)).ne'
  have hc0 : c ≠ 0 := by linarith
  have hc1 : c - 1 ≠ 0 := by linarith
  unfold lcmLU lcmpq Aminus a
  field_simp
  ring

/-- Left side of line 2 equals left side of line 3. -/
theorem line2_lhs_eq_line3_lhs {c : ℝ} (hc : 4 ≤ c) :
    (a c ^ 3 * v c ^ 2 + Aminus c * v c ^ 2) / lcmLU c =
      2 * (c - 2) * logb 2 (c / 2) / ((c - 1) ^ 2 * c * logb 2 2) := by
  have hv : v c ≠ 0 := (lt_of_lt_of_le one_pos (one_le_v hc)).ne'
  have hc0 : c ≠ 0 := by linarith
  have hc1 : c - 1 ≠ 0 := by linarith
  rw [logb_half (by linarith), logb_self_eq_one one_lt_two]
  have hv' : logb 2 c - 1 = v c := rfl
  rw [hv']
  unfold lcmLU Aminus a
  field_simp
  ring

/-- Right side of line 2 equals right side of line 3. -/
theorem line2_rhs_eq_line3_rhs {c : ℝ} (hc : 4 ≤ c) :
    (a c - 1) * v c / lcmpq c =
      2 * (c - 2) * (logb 2 c / logb 2 2 - 1) / ((c - 1) ^ 2 * c) := by
  have hc0 : c ≠ 0 := by linarith
  have hc1 : c - 1 ≠ 0 := by linarith
  rw [logb_self_eq_one one_lt_two, div_one]
  unfold lcmpq a v
  field_simp
  ring

/-- Line 3: `2(c-2) log₂(c/2) / ((c-1)² c log₂ 2) = 2(c-2)(log₂ c / log₂ 2 - 1) / ((c-1)² c)`. -/
theorem line3 {c : ℝ} (hc : 4 ≤ c) :
    2 * (c - 2) * logb 2 (c / 2) / ((c - 1) ^ 2 * c * logb 2 2) =
      2 * (c - 2) * (logb 2 c / logb 2 2 - 1) / ((c - 1) ^ 2 * c) := by
  rw [← line2_lhs_eq_line3_lhs hc, ← line2_rhs_eq_line3_rhs hc]
  exact line2 hc

/-- The whole derivation `d(tT) = d(S_{≥0})` for every real `c ≥ 4`. -/
theorem derivation {c : ℝ} (hc : 4 ≤ c) :
    (a c ^ 3 * v c ^ 2 + Aminus c * v c ^ 2) / lcmLU c = (a c - 1) * v c / lcmpq c ∧
    (a c ^ 3 * v c ^ 2 + Aminus c * v c ^ 2) / lcmLU c =
      2 * (c - 2) * logb 2 (c / 2) / ((c - 1) ^ 2 * c * logb 2 2) ∧
    (a c - 1) * v c / lcmpq c =
      2 * (c - 2) * (logb 2 c / logb 2 2 - 1) / ((c - 1) ^ 2 * c) ∧
    2 * (c - 2) * logb 2 (c / 2) / ((c - 1) ^ 2 * c * logb 2 2) =
      2 * (c - 2) * (logb 2 c / logb 2 2 - 1) / ((c - 1) ^ 2 * c) :=
  ⟨line2 hc, line2_lhs_eq_line3_lhs hc, line2_rhs_eq_line3_rhs hc, line3 hc⟩

end

end CotreeDensityDefinitions

#print axioms CotreeDensityDefinitions.derivation
