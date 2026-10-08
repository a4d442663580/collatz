import Mathlib

/-!
# Lean certificate for `Barina_cotree_density` (self-contained)

## What is certified

1. **Closed form**, at the Bařina `7n±1` root `c = 8`:
   with `a = c - 1`, `v = log₂ c - 1`, `A⁻ = a² - a - 1`,
   ```
   lhs = (a³ v² + A⁻ v²) / (v · (c³/2) · (c-1)²)
   rhs = ((a-1) v) / ((c/2) · (c-1)²)
   ```
   `v = 2` at `c = 8` (`vLog_eight`), `lhs = rhs = 12/196` (`lhs_eight`, `rhs_eight`),
   and `lhs / rhs = 1` (`cotree_barina`).

2. **Series form**: the seven cotree geometric series
   * leftward:     first term 49/8192,      ratio 57/64     → 1372/25088
   * upward T₁:    first term 3/512,        ratio 1/2²¹     → 12288/2097151
   * upward T₂:    first term 5/8192,       ratio 1/2²¹     → 1280/2097151
   * upward T₃:    first term 1/16384,      ratio 1/2²¹     → 128/2097151
   * upward T₄:    first term 3/524288,     ratio 1/2²¹     → 12/2097151
   * upward T₅:    first term 1/2097152,    ratio 1/2²¹     → 1/2097151
   * upward T₆:    first term 7/268435456,  ratio 1/2²¹     → 7/268435328

   converge (as genuine infinite sums in `ℝ`) to these values; the six upward sums add up
   to 164/25088, and 1372/25088 + 164/25088 = 12/196 (`hasSum_barina_cotree`).

`barina_cotree_density` packages both.

## Scope

This is **Lean-checked arithmetic**. Nothing here mentions the map `n ↦ 7n±1` or its
iteration: the first terms and ratios are input data, and the identity `lhs = rhs` holds
for every real `c ≠ 0, 1` and `v ≠ 0` (`cotree_lhs_eq_rhs`), because
`a³ + (a² - a - 1) = (a+1)²(a-1)` (`numerator_factor`). In particular it does not prove
that every branching number lies in the tree from `c`.

Uses only the standard axioms (`#print axioms` at the end).

Check with: `lake env lean barina_cotree_density.lean` (any project depending on Mathlib).
-/

namespace BarinaCotreeDensity

open Real

noncomputable section

/-! ## 1. Closed form at c = 8 -/

/-- `lhs`, with `a = c - 1`, `A⁻ = a² - a - 1`, and `v` a parameter. -/
def lhs (c v : ℝ) : ℝ :=
  ((c - 1) ^ 3 * v ^ 2 + ((c - 1) ^ 2 - (c - 1) - 1) * v ^ 2) /
    (v * (c ^ 3 / 2) * (c - 1) ^ 2)

/-- `rhs = ((a-1) v) / ((c/2)(c-1)²)` with `a = c - 1`. -/
def rhs (c v : ℝ) : ℝ :=
  ((c - 1 - 1) * v) / (c / 2 * (c - 1) ^ 2)

/-- `v = log₂ c - 1`. -/
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

/-- `v = log₂ 8 - 1 = 2`. -/
theorem vLog_eight : vLog 8 = 2 := by
  unfold vLog
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, logb_pow, logb_self_eq_one (by norm_num)]
  norm_num

/-- At `c = 8`: `rhs = 12/196`, the density of the twelve Bařina branching classes mod 196. -/
theorem rhs_eight : rhs 8 (vLog 8) = 12 / 196 := by
  rw [vLog_eight]; unfold rhs; norm_num

/-- At `c = 8`: `lhs = 12/196`. -/
theorem lhs_eight : lhs 8 (vLog 8) = 12 / 196 := by
  rw [vLog_eight]; unfold lhs; norm_num

/-- **Closed-form certificate:** `lhs / rhs = 1` at `c = 8`. -/
theorem cotree_barina : lhs 8 (vLog 8) / rhs 8 (vLog 8) = 1 := by
  rw [lhs_eight, rhs_eight]; norm_num

/-! ## 2. Series form -/

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

/-- Leftward cotree series: `49/8192 / (1 - 57/64) = 7/128 = 1372/25088`. -/
theorem barina_leftward_geom_series :
    geomSeriesSum (49 / 8192) (57 / 64) = 1372 / 25088 := by
  simp only [geomSeriesSum]; norm_num

/-- Upward T₁: `3/512 / (1 - 1/2²¹) = 12288/2097151`. -/
theorem barina_upward_T1_geom_series :
    geomSeriesSum (3 / 512) (1 / 2097152) = 12288 / 2097151 := by
  simp only [geomSeriesSum]; norm_num

/-- Upward T₂: `5/8192 / (1 - 1/2²¹) = 1280/2097151`. -/
theorem barina_upward_T2_geom_series :
    geomSeriesSum (5 / 8192) (1 / 2097152) = 1280 / 2097151 := by
  simp only [geomSeriesSum]; norm_num

/-- Upward T₃: `1/16384 / (1 - 1/2²¹) = 128/2097151`. -/
theorem barina_upward_T3_geom_series :
    geomSeriesSum (1 / 16384) (1 / 2097152) = 128 / 2097151 := by
  simp only [geomSeriesSum]; norm_num

/-- Upward T₄: `3/524288 / (1 - 1/2²¹) = 12/2097151`. -/
theorem barina_upward_T4_geom_series :
    geomSeriesSum (3 / 524288) (1 / 2097152) = 12 / 2097151 := by
  simp only [geomSeriesSum]; norm_num

/-- Upward T₅: `1/2097152 / (1 - 1/2²¹) = 1/2097151`. -/
theorem barina_upward_T5_geom_series :
    geomSeriesSum (1 / 2097152) (1 / 2097152) = 1 / 2097151 := by
  simp only [geomSeriesSum]; norm_num

/-- Upward T₆: `7/268435456 / (1 - 1/2²¹) = 7/268435328`. -/
theorem barina_upward_T6_geom_series :
    geomSeriesSum (7 / 268435456) (1 / 2097152) = 7 / 268435328 := by
  simp only [geomSeriesSum]; norm_num

/-- Upward total: the six upward sums add up to `164/25088`. -/
theorem barina_upward_total :
    (12288 : ℚ) / 2097151 + 1280 / 2097151 + 128 / 2097151 +
    12 / 2097151 + 1 / 2097151 + 7 / 268435328 = 164 / 25088 := by norm_num

/-- `1372/25088 + 164/25088 = 12/196`. -/
theorem barina_cotree_density_via_geom :
    geomSeriesSum (49 / 8192) (57 / 64) +
    geomSeriesSum (3 / 512) (1 / 2097152) +
    geomSeriesSum (5 / 8192) (1 / 2097152) +
    geomSeriesSum (1 / 16384) (1 / 2097152) +
    geomSeriesSum (3 / 524288) (1 / 2097152) +
    geomSeriesSum (1 / 2097152) (1 / 2097152) +
    geomSeriesSum (7 / 268435456) (1 / 2097152) = 12 / 196 := by
  simp only [geomSeriesSum]; norm_num

theorem hasSum_barina_leftward :
    HasSum (fun n : ℕ ↦ (49 / 8192 : ℝ) * (57 / 64) ^ n) (1372 / 25088) := by
  have h := hasSum_geomSeriesSum (49 / 8192) (57 / 64) (by norm_num) (by norm_num)
  simp only [geomSeriesSum] at h
  convert h using 1 <;> push_cast <;> norm_num

theorem hasSum_barina_upward_T1 :
    HasSum (fun n : ℕ ↦ (3 / 512 : ℝ) * (1 / 2097152) ^ n) (12288 / 2097151) := by
  have h := hasSum_geomSeriesSum (3 / 512) (1 / 2097152) (by norm_num) (by norm_num)
  simp only [geomSeriesSum] at h
  convert h using 1 <;> push_cast <;> norm_num

theorem hasSum_barina_upward_T2 :
    HasSum (fun n : ℕ ↦ (5 / 8192 : ℝ) * (1 / 2097152) ^ n) (1280 / 2097151) := by
  have h := hasSum_geomSeriesSum (5 / 8192) (1 / 2097152) (by norm_num) (by norm_num)
  simp only [geomSeriesSum] at h
  convert h using 1 <;> push_cast <;> norm_num

theorem hasSum_barina_upward_T3 :
    HasSum (fun n : ℕ ↦ (1 / 16384 : ℝ) * (1 / 2097152) ^ n) (128 / 2097151) := by
  have h := hasSum_geomSeriesSum (1 / 16384) (1 / 2097152) (by norm_num) (by norm_num)
  simp only [geomSeriesSum] at h
  convert h using 1 <;> push_cast <;> norm_num

theorem hasSum_barina_upward_T4 :
    HasSum (fun n : ℕ ↦ (3 / 524288 : ℝ) * (1 / 2097152) ^ n) (12 / 2097151) := by
  have h := hasSum_geomSeriesSum (3 / 524288) (1 / 2097152) (by norm_num) (by norm_num)
  simp only [geomSeriesSum] at h
  convert h using 1 <;> push_cast <;> norm_num

theorem hasSum_barina_upward_T5 :
    HasSum (fun n : ℕ ↦ (1 / 2097152 : ℝ) * (1 / 2097152) ^ n) (1 / 2097151) := by
  have h := hasSum_geomSeriesSum (1 / 2097152) (1 / 2097152) (by norm_num) (by norm_num)
  simp only [geomSeriesSum] at h
  convert h using 1 <;> push_cast <;> norm_num

theorem hasSum_barina_upward_T6 :
    HasSum (fun n : ℕ ↦ (7 / 268435456 : ℝ) * (1 / 2097152) ^ n) (7 / 268435328) := by
  have h := hasSum_geomSeriesSum (7 / 268435456) (1 / 2097152) (by norm_num) (by norm_num)
  simp only [geomSeriesSum] at h
  convert h using 1 <;> push_cast <;> norm_num

/-- **Series certificate:** the sum of the seven cotree series, as an infinite sum in `ℝ`,
is `12/196`. -/
theorem hasSum_barina_cotree :
    HasSum (fun n : ℕ ↦ (49 / 8192 : ℝ) * (57 / 64) ^ n +
      (3 / 512 : ℝ) * (1 / 2097152) ^ n + (5 / 8192 : ℝ) * (1 / 2097152) ^ n +
      (1 / 16384 : ℝ) * (1 / 2097152) ^ n + (3 / 524288 : ℝ) * (1 / 2097152) ^ n +
      (1 / 2097152 : ℝ) * (1 / 2097152) ^ n + (7 / 268435456 : ℝ) * (1 / 2097152) ^ n)
      (12 / 196) := by
  have h := ((((((hasSum_barina_leftward.add hasSum_barina_upward_T1).add
    hasSum_barina_upward_T2).add hasSum_barina_upward_T3).add hasSum_barina_upward_T4).add
    hasSum_barina_upward_T5).add hasSum_barina_upward_T6)
  convert h using 1
  norm_num

/-! ## 3. The packaged certificate -/

/-- **`Barina_cotree_density`.** At the Bařina root `c = 8`:
* `lhs` and `rhs` both equal `12/196`, and `lhs / rhs = 1`;
* the leftward series sums (in `ℝ`) to `1372/25088`, the six upward series to
  `164/25088`, and `1372/25088 + 164/25088 = 12/196`. -/
theorem barina_cotree_density :
    vLog 8 = 2 ∧
    lhs 8 (vLog 8) = 12 / 196 ∧ rhs 8 (vLog 8) = 12 / 196 ∧
    lhs 8 (vLog 8) / rhs 8 (vLog 8) = 1 ∧
    HasSum (fun n : ℕ ↦ (49 / 8192 : ℝ) * (57 / 64) ^ n) (1372 / 25088) ∧
    HasSum (fun n : ℕ ↦ (3 / 512 : ℝ) * (1 / 2097152) ^ n) (12288 / 2097151) ∧
    HasSum (fun n : ℕ ↦ (5 / 8192 : ℝ) * (1 / 2097152) ^ n) (1280 / 2097151) ∧
    HasSum (fun n : ℕ ↦ (1 / 16384 : ℝ) * (1 / 2097152) ^ n) (128 / 2097151) ∧
    HasSum (fun n : ℕ ↦ (3 / 524288 : ℝ) * (1 / 2097152) ^ n) (12 / 2097151) ∧
    HasSum (fun n : ℕ ↦ (1 / 2097152 : ℝ) * (1 / 2097152) ^ n) (1 / 2097151) ∧
    HasSum (fun n : ℕ ↦ (7 / 268435456 : ℝ) * (1 / 2097152) ^ n) (7 / 268435328) ∧
    (12288 : ℝ) / 2097151 + 1280 / 2097151 + 128 / 2097151 +
      12 / 2097151 + 1 / 2097151 + 7 / 268435328 = 164 / 25088 ∧
    (1372 : ℝ) / 25088 + 164 / 25088 = 12 / 196 :=
  ⟨vLog_eight, lhs_eight, rhs_eight, cotree_barina,
    hasSum_barina_leftward, hasSum_barina_upward_T1, hasSum_barina_upward_T2,
    hasSum_barina_upward_T3, hasSum_barina_upward_T4, hasSum_barina_upward_T5,
    hasSum_barina_upward_T6, by norm_num, by norm_num⟩

end

end BarinaCotreeDensity

#print axioms BarinaCotreeDensity.barina_cotree_density
#print axioms BarinaCotreeDensity.cotree_lhs_eq_rhs
#print axioms BarinaCotreeDensity.hasSum_barina_cotree
