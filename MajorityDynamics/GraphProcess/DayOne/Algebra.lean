import MajorityDynamics.GraphProcess.FaithfulStep.Basic

noncomputable section
set_option maxHeartbeats 1000000
namespace MajorityDynamics.GraphProcess.DayOne

/-- Uniform algebraic centering error, including the missing diagonal trial
and the possible odd vertex count. -/
theorem centering_error {N A r τ T s t d x y : ℝ}
    (hN : 1 ≤ N) (hr : 1 ≤ r) (hr2 : r^2 = N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hodd : |N-2*A| ≤ 1)
    (hτ0 : 0 ≤ τ) (hτT : τ ≤ T) (hT : 1 ≤ T)
    (hs : |s| = 1) (ht : |t| = 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hx0 : 0 ≤ x) (hxN : x ≤ N)
    (hx : |x-A-τ*r*s| ≤ 2) (hy : |y-A-τ*r*t| ≤ 2) :
    |x*(y-d)-A*(A-d)*(1+τ/r*(2*s+2*t))| ≤ 20*(T+1)^2*N := by
  have hr0 : 0 < r := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hratio : 0 ≤ τ/r := div_nonneg hτ0 hr0.le
  have hratioT : τ/r ≤ T := by
    rw [div_le_iff₀ hr0]
    nlinarith
  let u := 2*τ/r
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have huT : u ≤ 2*T := by
    dsimp [u]
    rw [mul_div_assoc]
    linarith
  have hx' : |x-A*(1+u*s)| ≤ 2+T := by
    have hid : x-A*(1+u*s) = (x-A-τ*r*s)+(τ/r*(N-2*A)*s) := by
      dsimp [u]
      rw [← hr2]
      field_simp
      ring
    rw [hid]
    calc
      _ ≤ |x-A-τ*r*s|+|τ/r*(N-2*A)*s| := abs_add_le _ _
      _ ≤ 2+T := by
        rw [abs_mul, abs_mul, hs, abs_of_nonneg hratio, mul_one]
        nlinarith [mul_le_mul hratioT hodd (abs_nonneg (N-2*A)) hT0]
  have hAd : |A-d| ≤ 2*N := by
    rw [abs_le]
    constructor <;> linarith
  have hy' : |(y-d)-(A-d)*(1+u*t)| ≤ 2+3*T := by
    have hid : (y-d)-(A-d)*(1+u*t) = (y-A-τ*r*t)+(τ/r*(N-2*A+2*d)*t) := by
      dsimp [u]
      rw [← hr2]
      field_simp
      ring
    have hod : |N-2*A+2*d| ≤ 3 := by
      calc
        _ ≤ |N-2*A|+|2*d| := abs_add_le _ _
        _ ≤ 3 := by rw [abs_of_nonneg (by positivity : 0 ≤ 2*d)]; linarith
    rw [hid]
    calc
      _ ≤ |y-A-τ*r*t|+|τ/r*(N-2*A+2*d)*t| := abs_add_le _ _
      _ ≤ 2+3*T := by
        rw [abs_mul, abs_mul, ht, abs_of_nonneg hratio, mul_one]
        nlinarith [mul_le_mul hratioT hod (abs_nonneg (N-2*A+2*d)) hT0]
  have hbt : |(A-d)*(1+u*t)| ≤ 2*N*(1+2*T) := by
    rw [abs_mul]
    have h : |1+u*t| ≤ 1+2*T := by
      calc
        _ ≤ |(1:ℝ)|+|u*t| := abs_add_le _ _
        _ = 1+u := by rw [abs_one,abs_mul,abs_of_nonneg hu0,ht,mul_one]
        _ ≤ 1+2*T := by linarith
    exact mul_le_mul hAd h (abs_nonneg _) (by positivity)
  have hprod : |x*(y-d)-A*(1+u*s)*((A-d)*(1+u*t))| ≤
      N*(2+3*T)+(2+T)*(2*N*(1+2*T)) := by
    have hid : x*(y-d)-A*(1+u*s)*((A-d)*(1+u*t)) =
        x*((y-d)-(A-d)*(1+u*t))+(x-A*(1+u*s))*((A-d)*(1+u*t)) := by ring
    rw [hid]
    calc
      _ ≤ |x*((y-d)-(A-d)*(1+u*t))|+|(x-A*(1+u*s))*((A-d)*(1+u*t))| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul,abs_mul,abs_of_nonneg hx0]
        exact add_le_add (mul_le_mul hxN hy' (abs_nonneg _) hN0)
          (mul_le_mul hx' hbt (abs_nonneg _) (by positivity))
  have hu2 : u^2*N = 4*τ^2 := by
    dsimp [u]
    rw [← hr2]
    field_simp
    ring
  have hcross : |A*(1+u*s)*((A-d)*(1+u*t))-A*(A-d)*(1+τ/r*(2*s+2*t))| ≤
      8*T^2*N := by
    have hid : A*(1+u*s)*((A-d)*(1+u*t))-A*(A-d)*(1+τ/r*(2*s+2*t)) =
      A*(A-d)*u^2*s*t := by dsimp [u]; ring
    rw [hid,abs_mul,abs_mul,abs_mul,abs_mul,hs,ht,mul_one,mul_one,
      abs_of_nonneg hA0,abs_of_nonneg (sq_nonneg u)]
    calc
      _ ≤ N*(2*N)*u^2 := mul_le_mul_of_nonneg_right
        (mul_le_mul hAN hAd (abs_nonneg _) hN0) (sq_nonneg _)
      _ = 8*τ^2*N := by calc
        _ = 2*(u^2*N)*N := by ring
        _ = _ := by rw [hu2]; ring
      _ ≤ 8*T^2*N := by
        apply mul_le_mul_of_nonneg_right _ hN0
        nlinarith
  have hab := abs_sub_le (x*(y-d)) (A*(1+u*s)*((A-d)*(1+u*t)))
    (A*(A-d)*(1+τ/r*(2*s+2*t)))
  have hh := hab.trans (add_le_add hprod hcross)
  apply hh.trans
  nlinarith [mul_nonneg hN0 hT0, mul_nonneg hN0 (sq_nonneg T)]

end MajorityDynamics.GraphProcess.DayOne
