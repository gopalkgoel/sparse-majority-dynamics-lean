import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Error propagation through a covariance-corrected expansion -/

namespace MajorityDynamics.Analysis

/-- Transfer a first-order expansion between approximate and exact moments.
No limit or probabilistic hypothesis is hidden in this scalar inequality. -/
theorem covariance_expansion_transfer (A' A B u I' I J v H b e eNew eOld eCross eMean : ℝ)
    (_hH : 0 ≤ H) (hb : 0 ≤ b)
    (hA : |A| ≤ H) (hv : |v| ≤ b)
    (hwindow : |I' - (I + J - v * I)| ≤ e)
    (hnew : |A' - I'| ≤ eNew) (hold : |A - I| ≤ eOld)
    (hcross : |B - J| ≤ eCross) (hmean : |u - v| ≤ eMean) :
    |A' - (A + B - u * A)| ≤ e + eNew + (1 + b) * eOld + eCross + H * eMean := by
  have heMean : 0 ≤ eMean := (abs_nonneg _).trans hmean
  have hprod : |v * I - u * A| ≤ b * eOld + eMean * H := by
    have heq : v * I - u * A = v * (I - A) + (v - u) * A := by ring
    rw [heq]
    calc
      _ ≤ |v * (I - A)| + |(v - u) * A| := abs_add_le _ _
      _ ≤ b * eOld + eMean * H := by
        apply add_le_add
        · rw [abs_mul, abs_sub_comm I A]
          exact mul_le_mul hv hold (abs_nonneg _) hb
        · rw [abs_mul, abs_sub_comm v u]
          exact mul_le_mul hmean hA (abs_nonneg _) heMean
  have htarget : |(I + J - v * I) - (A + B - u * A)| ≤ eOld + eCross + b * eOld + eMean * H := by
    have heq : (I + J - v * I) - (A + B - u * A) = (I - A) + (J - B) - (v * I - u * A) := by ring
    rw [heq]
    calc
      _ ≤ |I - A| + |J - B| + |v * I - u * A| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ eOld + eCross + (b * eOld + eMean * H) := by
        rw [abs_sub_comm I A, abs_sub_comm J B]
        exact add_le_add (add_le_add hold hcross) hprod
      _ = _ := by ring
  calc
    _ ≤ |A' - I'| + |I' - (A + B - u * A)| := abs_sub_le _ _ _
    _ ≤ eNew + (|I' - (I + J - v * I)| + |(I + J - v * I) - (A + B - u * A)|) :=
      add_le_add hnew (abs_sub_le _ _ _)
    _ ≤ eNew + (e + (eOld + eCross + b * eOld + eMean * H)) :=
      add_le_add le_rfl (add_le_add hwindow htarget)
    _ = _ := by ring

end MajorityDynamics.Analysis
